const os = require('os');
const fs = require('fs');
const qs = require('qs');
const https = require('https');
const tls = require('tls');
const axios = require('axios');
const path = require('path');
const decomment = require('decomment');
const Mustache = require('mustache');
const contentDispositionParser = require('content-disposition');
const mime = require('mime-types');
const { ipcMain } = require('electron');
const { isUndefined, isNull, each, get, compact, cloneDeep } = require('lodash');
const { VarsRuntime, AssertRuntime, ScriptRuntime, TestRuntime } = require('@usebruno/js');
const prepareRequest = require('./prepare-request');
const prepareCollectionRequest = require('./prepare-collection-request');
const prepareGqlIntrospectionRequest = require('./prepare-gql-introspection-request');
const { cancelTokens, saveCancelToken, deleteCancelToken } = require('../../utils/cancel-token');
const { uuid } = require('../../utils/common');
const interpolateVars = require('./interpolate-vars');
const { interpolateString } = require('./interpolate-string');
const { sortFolder, getAllRequestsInFolderRecursively } = require('./helper');
const { preferencesUtil } = require('../../store/preferences');
const { getProcessEnvVars } = require('../../store/process-env');
const { getBrunoConfig } = require('../../store/bruno-config');
const { HttpProxyAgent } = require('http-proxy-agent');
const { SocksProxyAgent } = require('socks-proxy-agent');
const { makeAxiosInstance } = require('./axios-instance');
const { addAwsV4Interceptor, resolveAwsV4Credentials } = require('./awsv4auth-helper');
const { addDigestInterceptor } = require('./digestauth-helper');
const { shouldUseProxy, PatchedHttpsProxyAgent } = require('../../utils/proxy-util');
const { chooseFileToSave, writeBinaryFile } = require('../../utils/filesystem');
const { getCookieStringForUrl, addCookieToJar, getDomainsWithCookies } = require('../../utils/cookies');
const {
  resolveOAuth2AuthorizationCodeAccessToken,
  transformClientCredentialsRequest,
  transformPasswordCredentialsRequest
} = require('./oauth2-helper');
const Oauth2Store = require('../../store/oauth2');
const iconv = require('iconv-lite');

// override the default escape function to prevent escaping
Mustache.escape = function (value) {
  return value;
};

const safeStringifyJSON = (data) => {
  try {
    return JSON.stringify(data);
  } catch (e) {
    return data;
  }
};

const safeParseJSON = (data) => {
  try {
    return JSON.parse(data);
  } catch (e) {
    return data;
  }
};

const getEnvVars = (environment = {}) => {
  const variables = environment.variables;
  if (!variables || !variables.length) {
    return {
      __name__: environment.name
    };
  }

  const envVars = {};
  each(variables, (variable) => {
    if (variable.enabled) {
      envVars[variable.name] = Mustache.escape(variable.value);
    }
  });

  return {
    ...envVars,
    __name__: environment.name
  };
};

const protocolRegex = /^([-+\w]{1,25})(:?\/\/|:)/;

const configureRequest = async (
  collectionUid,
  request,
  envVars,
  collectionVariables,
  processEnvVars,
  collectionPath
) => {
  if (!protocolRegex.test(request.url)) {
    request.url = `http://${request.url}`;
  }

  /**
   * @see https://github.com/usebruno/bruno/issues/211 set keepAlive to true, this should fix socket hang up errors
   * @see https://github.com/nodejs/node/pull/43522 keepAlive was changed to true globally on Node v19+
   */
  const httpsAgentRequestFields = { keepAlive: true };
  if (!preferencesUtil.shouldVerifyTls()) {
    httpsAgentRequestFields['rejectUnauthorized'] = false;
  }

  if (preferencesUtil.shouldUseCustomCaCertificate()) {
    const caCertFilePath = preferencesUtil.getCustomCaCertificateFilePath();
    if (caCertFilePath) {
      let caCertBuffer = fs.readFileSync(caCertFilePath);
      if (preferencesUtil.shouldKeepDefaultCaCertificates()) {
        caCertBuffer += '\n' + tls.rootCertificates.join('\n'); // Augment default truststore with custom CA certificates
      }
      httpsAgentRequestFields['ca'] = caCertBuffer;
    }
  }

  const brunoConfig = getBrunoConfig(collectionUid);
  const interpolationOptions = {
    envVars,
    collectionVariables,
    processEnvVars
  };

  // client certificate config
  const clientCertConfig = get(brunoConfig, 'clientCertificates.certs', []);
  for (let clientCert of clientCertConfig) {
    const domain = interpolateString(clientCert.domain, interpolationOptions);

    let certFilePath = interpolateString(clientCert.certFilePath, interpolationOptions);
    certFilePath = path.isAbsolute(certFilePath) ? certFilePath : path.join(collectionPath, certFilePath);

    let keyFilePath = interpolateString(clientCert.keyFilePath, interpolationOptions);
    keyFilePath = path.isAbsolute(keyFilePath) ? keyFilePath : path.join(collectionPath, keyFilePath);

    if (domain && certFilePath && keyFilePath) {
      const hostRegex = '^https:\\/\\/' + domain.replaceAll('.', '\\.').replaceAll('*', '.*');

      if (request.url.match(hostRegex)) {
        try {
          httpsAgentRequestFields['cert'] = fs.readFileSync(certFilePath);
        } catch (err) {
          console.log('Error reading cert file', err);
        }

        try {
          httpsAgentRequestFields['key'] = fs.readFileSync(keyFilePath);
        } catch (err) {
          console.log('Error reading key file', err);
        }

        httpsAgentRequestFields['passphrase'] = interpolateString(clientCert.passphrase, interpolationOptions);
        break;
      }
    }
  }

  // proxy configuration
  let proxyConfig = get(brunoConfig, 'proxy', {});
  let proxyEnabled = get(proxyConfig, 'enabled', 'global');
  if (proxyEnabled === 'global') {
    proxyConfig = preferencesUtil.getGlobalProxyConfig();
    proxyEnabled = get(proxyConfig, 'enabled', false);
  }
  const shouldProxy = shouldUseProxy(request.url, get(proxyConfig, 'bypassProxy', ''));
  if (proxyEnabled === true && shouldProxy) {
    const proxyProtocol = interpolateString(get(proxyConfig, 'protocol'), interpolationOptions);
    const proxyHostname = interpolateString(get(proxyConfig, 'hostname'), interpolationOptions);
    const proxyPort = interpolateString(get(proxyConfig, 'port'), interpolationOptions);
    const proxyAuthEnabled = get(proxyConfig, 'auth.enabled', false);
    const socksEnabled = proxyProtocol.includes('socks');

    let uriPort = isUndefined(proxyPort) || isNull(proxyPort) ? '' : `:${proxyPort}`;
    let proxyUri;
    if (proxyAuthEnabled) {
      const proxyAuthUsername = interpolateString(get(proxyConfig, 'auth.username'), interpolationOptions);
      const proxyAuthPassword = interpolateString(get(proxyConfig, 'auth.password'), interpolationOptions);

      proxyUri = `${proxyProtocol}://${proxyAuthUsername}:${proxyAuthPassword}@${proxyHostname}${uriPort}`;
    } else {
      proxyUri = `${proxyProtocol}://${proxyHostname}${uriPort}`;
    }

    if (socksEnabled) {
      request.httpsAgent = new SocksProxyAgent(
        proxyUri,
        Object.keys(httpsAgentRequestFields).length > 0 ? { ...httpsAgentRequestFields } : undefined
      );
      request.httpAgent = new SocksProxyAgent(proxyUri);
    } else {
      request.httpsAgent = new PatchedHttpsProxyAgent(
        proxyUri,
        Object.keys(httpsAgentRequestFields).length > 0 ? { ...httpsAgentRequestFields } : undefined
      );
      request.httpAgent = new HttpProxyAgent(proxyUri);
    }
  } else if (Object.keys(httpsAgentRequestFields).length > 0) {
    //console.log('confirm using basic agent', httpsAgentRequestFields);
    request.httpsAgent = new https.Agent({
      ...httpsAgentRequestFields
    });
  }

  const axiosInstance = makeAxiosInstance();

  if (request.oauth2) {
    let requestCopy = cloneDeep(request);
    switch (request?.oauth2?.grantType) {
      case 'authorization_code':
        interpolateVars(requestCopy, envVars, collectionVariables, processEnvVars);
        const { data: authorizationCodeData, url: authorizationCodeAccessTokenUrl } =
          await resolveOAuth2AuthorizationCodeAccessToken(requestCopy, collectionUid);
        request.method = 'POST';
        request.headers['content-type'] = 'application/x-www-form-urlencoded';
        request.data = authorizationCodeData;
        request.url = authorizationCodeAccessTokenUrl;
        break;
      case 'client_credentials':
        interpolateVars(requestCopy, envVars, collectionVariables, processEnvVars);
        const { data: clientCredentialsData, url: clientCredentialsAccessTokenUrl } =
          await transformClientCredentialsRequest(requestCopy);
        request.method = 'POST';
        request.headers['content-type'] = 'application/x-www-form-urlencoded';
        request.data = clientCredentialsData;
        request.url = clientCredentialsAccessTokenUrl;
        break;
      case 'password':
        interpolateVars(requestCopy, envVars, collectionVariables, processEnvVars);
        const { data: passwordData, url: passwordAccessTokenUrl } = await transformPasswordCredentialsRequest(
          requestCopy
        );
        request.method = 'POST';
        request.headers['content-type'] = 'application/x-www-form-urlencoded';
        request.data = passwordData;
        request.url = passwordAccessTokenUrl;
        break;
    }
  }

  if (request.awsv4config) {
    request.awsv4config = await resolveAwsV4Credentials(request);
    addAwsV4Interceptor(axiosInstance, request);
    delete request.awsv4config;
  }

  if (request.digestConfig) {
    addDigestInterceptor(axiosInstance, request);
  }

  request.timeout = preferencesUtil.getRequestTimeout();

  // add cookies to request
  if (preferencesUtil.shouldSendCookies()) {
    const cookieString = getCookieStringForUrl(request.url);
    if (cookieString && typeof cookieString === 'string' && cookieString.length) {
      console.log('adding cookie', cookieString);
      request.headers['cookie'] = cookieString;
    }
  }
  return axiosInstance;
};

const parseDataFromResponse = (response) => {
  // Parse the charset from content type: https://stackoverflow.com/a/33192813
  const charsetMatch = /charset=([^()<>@,;:"/[\]?.=\s]*)/i.exec(response.headers['content-type'] || '');
  // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/exec#using_exec_with_regexp_literals
  const charsetValue = charsetMatch?.[1];
  const dataBuffer = Buffer.from(response.data);
  // Overwrite the original data for backwards compatibility
  let data;
  if (iconv.encodingExists(charsetValue)) {
    data = iconv.decode(dataBuffer, charsetValue);
  } else {
    data = iconv.decode(dataBuffer, 'utf-8');
  }
  // Try to parse response to JSON, this can quietly fail
  try {
    // Filter out ZWNBSP character
    // https://gist.github.com/antic183/619f42b559b78028d1fe9e7ae8a1352d
    data = data.replace(/^\uFEFF/, '');
    data = JSON.parse(data);
  } catch {}

  return { data, dataBuffer };
};

const registerNetworkIpc = (mainWindow) => {
  const onConsoleLog = (type, args) => {
    console[type](...args);

    mainWindow.webContents.send('main:console-log', {
      type,
      args
    });
  };

  const runPreRequest = async (
    request,
    requestUid,
    envVars,
    collectionPath,
    collectionRoot,
    collectionUid,
    collectionVariables,
    processEnvVars,
    scriptingConfig
  ) => {
    // run pre-request vars
    const preRequestVars = get(request, 'vars.req', []);
    if (preRequestVars?.length) {
      const varsRuntime = new VarsRuntime();
      const result = varsRuntime.runPreRequestVars(
        preRequestVars,
        request,
        envVars,
        collectionVariables,
        collectionPath,
        processEnvVars
      );

      if (result) {
        mainWindow.webContents.send('main:script-environment-update', {
          envVariables: result.envVariables,
          collectionVariables: result.collectionVariables,
          requestUid,
          collectionUid
        });
      }
    }

    // run pre-request script
    let scriptResult;
    const requestScript = compact([get(collectionRoot, 'request.script.req'), get(request, 'script.req')]).join(os.EOL);
    if (requestScript?.length) {
      const scriptRuntime = new ScriptRuntime();
      scriptResult = await scriptRuntime.runRequestScript(
        decomment(requestScript),
        request,
        envVars,
        collectionVariables,
        collectionPath,
        onConsoleLog,
        processEnvVars,
        scriptingConfig
      );

      mainWindow.webContents.send('main:script-environment-update', {
        envVariables: scriptResult.envVariables,
        collectionVariables: scriptResult.collectionVariables,
        requestUid,
        collectionUid
      });
    }

    // interpolate variables inside request
    interpolateVars(request, envVars, collectionVariables, processEnvVars);

    // if this is a graphql request, parse the variables, only after interpolation
    // https://github.com/usebruno/bruno/issues/884
    if (request.mode === 'graphql') {
      request.data.variables = JSON.parse(request.data.variables);
    }

    // stringify the request url encoded params
    if (request.headers['content-type'] === 'application/x-www-form-urlencoded') {
      request.data = qs.stringify(request.data);
    }

    return scriptResult;
  };

  const runPostResponse = async (
    request,
    response,
    requestUid,
    envVars,
    collectionPath,
    collectionRoot,
    collectionUid,
    collectionVariables,
    processEnvVars,
    scriptingConfig
  ) => {
    // run post-response vars
    const postResponseVars = get(request, 'vars.res', []);
    if (postResponseVars?.length) {
      const varsRuntime = new VarsRuntime();
      const result = varsRuntime.runPostResponseVars(
        postResponseVars,
        request,
        response,
        envVars,
        collectionVariables,
        collectionPath,
        processEnvVars
      );

      if (result) {
        mainWindow.webContents.send('main:script-environment-update', {
          envVariables: result.envVariables,
          collectionVariables: result.collectionVariables,
          requestUid,
          collectionUid
        });
      }

      if (result?.error) {
        mainWindow.webContents.send('main:display-error', result.error);
      }
    }

    // run post-response script
    let scriptResult;
    const responseScript = compact([get(collectionRoot, 'request.script.res'), get(request, 'script.res')]).join(
      os.EOL
    );
    if (responseScript?.length) {
      const scriptRuntime = new ScriptRuntime();
      scriptResult = await scriptRuntime.runResponseScript(
        decomment(responseScript),
        request,
        response,
        envVars,
        collectionVariables,
        collectionPath,
        onConsoleLog,
        processEnvVars,
        scriptingConfig
      );

      mainWindow.webContents.send('main:script-environment-update', {
        envVariables: scriptResult.envVariables,
        collectionVariables: scriptResult.collectionVariables,
        requestUid,
        collectionUid
      });
    }
    return scriptResult;
  };

  // handler for sending http request
  ipcMain.handle('send-http-request', async (event, item, collection, environment, collectionVariables) => {
    const collectionUid = collection.uid;
    const collectionPath = collection.pathname;
    const cancelTokenUid = uuid();
    const requestUid = uuid();

    mainWindow.webContents.send('main:run-request-event', {
      type: 'request-queued',
      requestUid,
      collectionUid,
      itemUid: item.uid,
      cancelTokenUid
    });

    const collectionRoot = get(collection, 'root', {});
    const _request = item.draft ? item.draft.request : item.request;
    const request = prepareRequest(_request, collectionRoot, collectionPath);
    const envVars = getEnvVars(environment);
    const processEnvVars = getProcessEnvVars(collectionUid);
    const brunoConfig = getBrunoConfig(collectionUid);
    const scriptingConfig = get(brunoConfig, 'scripts', {});

    try {
      const controller = new AbortController();
      request.signal = controller.signal;
      saveCancelToken(cancelTokenUid, controller);

      await runPreRequest(
        request,
        requestUid,
        envVars,
        collectionPath,
        collectionRoot,
        collectionUid,
        collectionVariables,
        processEnvVars,
        scriptingConfig
      );

      const axiosInstance = await configureRequest(
        collectionUid,
        request,
        envVars,
        collectionVariables,
        processEnvVars,
        collectionPath
      );

      mainWindow.webContents.send('main:run-request-event', {
        type: 'request-sent',
        requestSent: {
          url: request.url,
          method: request.method,
          headers: request.headers,
          data: safeParseJSON(safeStringifyJSON(request.data)),
          timestamp: Date.now()
        },
        collectionUid,
        itemUid: item.uid,
        requestUid,
        cancelTokenUid
      });

      let response, responseTime;
      try {
        // console.log('z1', request);

        /** @type {import('axios').AxiosResponse} */

        response = await axiosInstance(request);

        // Prevents the duration on leaking to the actual result
        responseTime = response.headers.get('request-duration');
        response.headers.delete('request-duration');
      } catch (error) {
        deleteCancelToken(cancelTokenUid);

        // if it's a cancel request, don't continue
        if (axios.isCancel(error)) {
          let error = new Error('Request cancelled');
          error.isCancel = true;
          return Promise.reject(error);
        }

        if (error?.response) {
          response = error.response;

          // Prevents the duration on leaking to the actual result
          responseTime = response.headers.get('request-duration');
          response.headers.delete('request-duration');
        } else {
          // if it's not a network error, don't continue
          return Promise.reject(error);
        }
      }

      // Continue with the rest of the request lifecycle - post response vars, script, assertions, tests

      const { data, dataBuffer } = parseDataFromResponse(response);
      response.data = data;

      response.responseTime = responseTime;

      // save cookies
      if (preferencesUtil.shouldStoreCookies()) {
        let setCookieHeaders = [];
        if (response.headers['set-cookie']) {
          setCookieHeaders = Array.isArray(response.headers['set-cookie'])
            ? response.headers['set-cookie']
            : [response.headers['set-cookie']];
          for (let setCookieHeader of setCookieHeaders) {
            if (typeof setCookieHeader === 'string' && setCookieHeader.length) {
              addCookieToJar(setCookieHeader, request.url);
            }
          }
        }
      }

      // send domain cookies to renderer
      const domainsWithCookies = await getDomainsWithCookies();

      mainWindow.webContents.send('main:cookies-update', safeParseJSON(safeStringifyJSON(domainsWithCookies)));

      await runPostResponse(
        request,
        response,
        requestUid,
        envVars,
        collectionPath,
        collectionRoot,
        collectionUid,
        collectionVariables,
        processEnvVars,
        scriptingConfig
      );

      // run assertions
      const assertions = get(request, 'assertions');
      if (assertions) {
        const assertRuntime = new AssertRuntime();
        const results = assertRuntime.runAssertions(
          assertions,
          request,
          response,
          envVars,
          collectionVariables,
          collectionPath
        );

        mainWindow.webContents.send('main:run-request-event', {
          type: 'assertion-results',
          results: results,
          itemUid: item.uid,
          requestUid,
          collectionUid
        });
      }

      // run tests
      const testFile = compact([
        get(collectionRoot, 'request.tests'),
        item.draft ? get(item.draft, 'request.tests') : get(item, 'request.tests')
      ]).join(os.EOL);
      if (typeof testFile === 'string') {
        const testRuntime = new TestRuntime();
        const testResults = await testRuntime.runTests(
          decomment(testFile),
          request,
          response,
          envVars,
          collectionVariables,
          collectionPath,
          onConsoleLog,
          processEnvVars,
          scriptingConfig
        );

        mainWindow.webContents.send('main:run-request-event', {
          type: 'test-results',
          results: testResults.results,
          itemUid: item.uid,
          requestUid,
          collectionUid
        });

        mainWindow.webContents.send('main:script-environment-update', {
          envVariables: testResults.envVariables,
          collectionVariables: testResults.collectionVariables,
          requestUid,
          collectionUid
        });
      }

      return {
        status: response.status,
        statusText: response.statusText,
        headers: response.headers,
        data: response.data,
        dataBuffer: dataBuffer.toString('base64'),
        size: Buffer.byteLength(dataBuffer),
        duration: responseTime ?? 0
      };
    } catch (error) {
      deleteCancelToken(cancelTokenUid);

      return Promise.reject(error);
    }
  });

  ipcMain.handle('send-collection-oauth2-request', async (event, collection, environment, collectionVariables) => {
    try {
      const collectionUid = collection.uid;
      const collectionPath = collection.pathname;
      const requestUid = uuid();

      const collectionRoot = get(collection, 'root', {});
      const _request = collectionRoot?.request;
      const request = prepareCollectionRequest(_request, collectionRoot, collectionPath);
      const envVars = getEnvVars(environment);
      const processEnvVars = getProcessEnvVars(collectionUid);
      const brunoConfig = getBrunoConfig(collectionUid);
      const scriptingConfig = get(brunoConfig, 'scripts', {});

      await runPreRequest(
        request,
        requestUid,
        envVars,
        collectionPath,
        collectionRoot,
        collectionUid,
        collectionVariables,
        processEnvVars,
        scriptingConfig
      );

      interpolateVars(request, envVars, collection.collectionVariables, processEnvVars);
      const axiosInstance = await configureRequest(
        collection.uid,
        request,
        envVars,
        collection.collectionVariables,
        processEnvVars,
        collectionPath
      );

      try {
        response = await axiosInstance(request);
      } catch (error) {
        if (error?.response) {
          response = error.response;
        } else {
          return Promise.reject(error);
        }
      }

      const { data } = parseDataFromResponse(response);
      response.data = data;

      await runPostResponse(
        request,
        response,
        requestUid,
        envVars,
        collectionPath,
        collectionRoot,
        collectionUid,
        collectionVariables,
        processEnvVars,
        scriptingConfig
      );

      return {
        status: response.status,
        statusText: response.statusText,
        headers: response.headers,
        data: response.data
      };
    } catch (error) {
      return Promise.reject(error);
    }
  });

  ipcMain.handle('clear-oauth2-cache', async (event, uid) => {
    return new Promise((resolve, reject) => {
      try {
        const oauth2Store = new Oauth2Store();
        oauth2Store.clearSessionIdOfCollection(uid);
        resolve();
      } catch (err) {
        reject(new Error('Could not clear oauth2 cache'));
      }
    });
  });

  ipcMain.handle('cancel-http-request', async (event, cancelTokenUid) => {
    return new Promise((resolve, reject) => {
      if (cancelTokenUid && cancelTokens[cancelTokenUid]) {
        cancelTokens[cancelTokenUid].abort();
        deleteCancelToken(cancelTokenUid);
        resolve();
      } else {
        reject(new Error('cancel token not found'));
      }
    });
  });

  ipcMain.handle('fetch-gql-schema', async (event, endpoint, environment, request, collection) => {
    try {
      const envVars = getEnvVars(environment);
      const collectionRoot = get(collection, 'root', {});
      const preparedRequest = prepareGqlIntrospectionRequest(endpoint, envVars, request, collectionRoot);

      request.timeout = preferencesUtil.getRequestTimeout();

      if (!preferencesUtil.shouldVerifyTls()) {
        request.httpsAgent = new https.Agent({
          rejectUnauthorized: false
        });
      }

      const requestUid = uuid();
      const collectionPath = collection.pathname;
      const collectionUid = collection.uid;
      const collectionVariables = collection.collectionVariables;
      const processEnvVars = getProcessEnvVars(collectionUid);
      const brunoConfig = getBrunoConfig(collection.uid);
      const scriptingConfig = get(brunoConfig, 'scripts', {});

      await runPreRequest(
        request,
        requestUid,
        envVars,
        collectionPath,
        collectionRoot,
        collectionUid,
        collectionVariables,
        processEnvVars,
        scriptingConfig
      );

      interpolateVars(preparedRequest, envVars, collection.collectionVariables, processEnvVars);
      const axiosInstance = await configureRequest(
        collection.uid,
        preparedRequest,
        envVars,
        collection.collectionVariables,
        processEnvVars,
        collectionPath
      );
      const response = await axiosInstance(preparedRequest);

      await runPostResponse(
        request,
        response,
        requestUid,
        envVars,
        collectionPath,
        collectionRoot,
        collectionUid,
        collectionVariables,
        processEnvVars,
        scriptingConfig
      );

      return {
        status: response.status,
        statusText: response.statusText,
        headers: response.headers,
        data: response.data
      };
    } catch (error) {
      if (error.response) {
        return {
          status: error.response.status,
          statusText: error.response.statusText,
          headers: error.response.headers,
          data: error.response.data
        };
      }

      return Promise.reject(error);
    }
  });

  ipcMain.handle(
    'renderer:run-collection-folder',
    async (event, folder, collection, environment, collectionVariables, recursive) => {
      const collectionUid = collection.uid;
      const collectionPath = collection.pathname;
      const folderUid = folder ? folder.uid : null;
      const cancelTokenUid = uuid();
      const brunoConfig = getBrunoConfig(collectionUid);
      const scriptingConfig = get(brunoConfig, 'scripts', {});
      const collectionRoot = get(collection, 'root', {});

      const abortController = new AbortController();
      saveCancelToken(cancelTokenUid, abortController);

      if (!folder) {
        folder = collection;
      }

      mainWindow.webContents.send('main:run-folder-event', {
        type: 'testrun-started',
        isRecursive: recursive,
        collectionUid,
        folderUid,
        cancelTokenUid
      });

      try {
        const envVars = getEnvVars(environment);
        let folderRequests = [];

        if (recursive) {
          let sortedFolder = sortFolder(folder);
          folderRequests = getAllRequestsInFolderRecursively(sortedFolder);
        } else {
          each(folder.items, (item) => {
            if (item.request) {
              folderRequests.push(item);
            }
          });

          // sort requests by seq property
          folderRequests.sort((a, b) => {
            return a.seq - b.seq;
          });
        }

        let currentRequestIndex = 0;
        let nJumps = 0; // count the number of jumps to avoid infinite loops
        while (currentRequestIndex < folderRequests.length) {
          // user requested to cancel runner
          if (abortController.signal.aborted) {
            let error = new Error('Runner execution cancelled');
            error.isCancel = true;
            throw error;
          }

          const item = folderRequests[currentRequestIndex];
          let nextRequestName;
          const itemUid = item.uid;
          const eventData = {
            collectionUid,
            folderUid,
            itemUid
          };

          let timeStart;
          let timeEnd;

          mainWindow.webContents.send('main:run-folder-event', {
            type: 'request-queued',
            ...eventData
          });

          const _request = item.draft ? item.draft.request : item.request;
          const request = prepareRequest(_request, collectionRoot, collectionPath);
          const requestUid = uuid();
          const processEnvVars = getProcessEnvVars(collectionUid);

          try {
            const preRequestScriptResult = await runPreRequest(
              request,
              requestUid,
              envVars,
              collectionPath,
              collectionRoot,
              collectionUid,
              collectionVariables,
              processEnvVars,
              scriptingConfig
            );

            if (preRequestScriptResult?.nextRequestName !== undefined) {
              nextRequestName = preRequestScriptResult.nextRequestName;
            }

            // todo:
            // i have no clue why electron can't send the request object
            // without safeParseJSON(safeStringifyJSON(request.data))
            mainWindow.webContents.send('main:run-folder-event', {
              type: 'request-sent',
              requestSent: {
                url: request.url,
                method: request.method,
                headers: request.headers,
                data: safeParseJSON(safeStringifyJSON(request.data))
              },
              ...eventData
            });

            request.signal = abortController.signal;
            const axiosInstance = await configureRequest(
              collectionUid,
              request,
              envVars,
              collectionVariables,
              processEnvVars,
              collectionPath
            );

            timeStart = Date.now();
            let response, responseTime;
            try {
              /** @type {import('axios').AxiosResponse} */
              response = await axiosInstance(request);
              timeEnd = Date.now();

              const { data, dataBuffer } = parseDataFromResponse(response);
              response.data = data;
              response.responseTime = response.headers.get('request-duration');

              mainWindow.webContents.send('main:run-folder-event', {
                type: 'response-received',
                responseReceived: {
                  status: response.status,
                  statusText: response.statusText,
                  headers: response.headers,
                  duration: timeEnd - timeStart,
                  dataBuffer: dataBuffer.toString('base64'),
                  size: Buffer.byteLength(dataBuffer),
                  data: response.data,
                  responseTime: response.headers.get('request-duration')
                },
                ...eventData
              });
            } catch (error) {
              if (error?.response && !axios.isCancel(error)) {
                const { data, dataBuffer } = parseDataFromResponse(error.response);
                error.response.data = data;

                timeEnd = Date.now();
                response = {
                  status: error.response.status,
                  statusText: error.response.statusText,
                  headers: error.response.headers,
                  duration: timeEnd - timeStart,
                  dataBuffer: dataBuffer.toString('base64'),
                  size: Buffer.byteLength(dataBuffer),
                  data: error.response.data,
                  responseTime: error.response.headers.get('request-duration')
                };

                // if we get a response from the server, we consider it as a success
                mainWindow.webContents.send('main:run-folder-event', {
                  type: 'response-received',
                  error: error ? error.message : 'An error occurred while running the request',
                  responseReceived: response,
                  ...eventData
                });
              } else {
                // if it's not a network error, don't continue
                throw Promise.reject(error);
              }
            }

            const postRequestScriptResult = await runPostResponse(
              request,
              response,
              requestUid,
              envVars,
              collectionPath,
              collectionRoot,
              collectionUid,
              collectionVariables,
              processEnvVars,
              scriptingConfig
            );

            if (postRequestScriptResult?.nextRequestName !== undefined) {
              nextRequestName = postRequestScriptResult.nextRequestName;
            }

            // run assertions
            const assertions = get(item, 'request.assertions');
            if (assertions) {
              const assertRuntime = new AssertRuntime();
              const results = assertRuntime.runAssertions(
                assertions,
                request,
                response,
                envVars,
                collectionVariables,
                collectionPath
              );

              mainWindow.webContents.send('main:run-folder-event', {
                type: 'assertion-results',
                assertionResults: results,
                itemUid: item.uid,
                collectionUid
              });
            }

            // run tests
            const testFile = compact([
              get(collectionRoot, 'request.tests'),
              item.draft ? get(item.draft, 'request.tests') : get(item, 'request.tests')
            ]).join(os.EOL);
            if (typeof testFile === 'string') {
              const testRuntime = new TestRuntime();
              const testResults = await testRuntime.runTests(
                decomment(testFile),
                request,
                response,
                envVars,
                collectionVariables,
                collectionPath,
                onConsoleLog,
                processEnvVars,
                scriptingConfig
              );

              mainWindow.webContents.send('main:run-folder-event', {
                type: 'test-results',
                testResults: testResults.results,
                ...eventData
              });

              mainWindow.webContents.send('main:script-environment-update', {
                envVariables: testResults.envVariables,
                collectionVariables: testResults.collectionVariables,
                collectionUid
              });
            }
          } catch (error) {
            mainWindow.webContents.send('main:run-folder-event', {
              type: 'error',
              error: error ? error.message : 'An error occurred while running the request',
              responseReceived: {},
              ...eventData
            });
          }
          if (nextRequestName !== undefined) {
            nJumps++;
            if (nJumps > 10000) {
              throw new Error('Too many jumps, possible infinite loop');
            }
            if (nextRequestName === null) {
              break;
            }
            const nextRequestIdx = folderRequests.findIndex((request) => request.name === nextRequestName);
            if (nextRequestIdx >= 0) {
              currentRequestIndex = nextRequestIdx;
            } else {
              console.error("Could not find request with name '" + nextRequestName + "'");
              currentRequestIndex++;
            }
          } else {
            currentRequestIndex++;
          }
        }

        deleteCancelToken(cancelTokenUid);
        mainWindow.webContents.send('main:run-folder-event', {
          type: 'testrun-ended',
          collectionUid,
          folderUid
        });
      } catch (error) {
        deleteCancelToken(cancelTokenUid);
        mainWindow.webContents.send('main:run-folder-event', {
          type: 'testrun-ended',
          collectionUid,
          folderUid,
          error: error && !error.isCancel ? error : null
        });
      }
    }
  );

  // save response to file
  ipcMain.handle('renderer:save-response-to-file', async (event, response, url) => {
    try {
      const getHeaderValue = (headerName) => {
        const headersArray = typeof response.headers === 'object' ? Object.entries(response.headers) : [];

        if (headersArray.length > 0) {
          const header = headersArray.find((header) => header[0] === headerName);
          if (header && header.length > 1) {
            return header[1];
          }
        }
      };

      const getFileNameFromContentDispositionHeader = () => {
        const contentDisposition = getHeaderValue('content-disposition');
        try {
          const disposition = contentDispositionParser.parse(contentDisposition);
          return disposition && disposition.parameters['filename'];
        } catch (error) {}
      };

      const getFileNameFromUrlPath = () => {
        const lastPathLevel = new URL(url).pathname.split('/').pop();
        if (lastPathLevel && /\..+/.exec(lastPathLevel)) {
          return lastPathLevel;
        }
      };

      const getFileNameBasedOnContentTypeHeader = () => {
        const contentType = getHeaderValue('content-type');
        const extension = (contentType && mime.extension(contentType)) || 'txt';
        return `response.${extension}`;
      };

      const fileName =
        getFileNameFromContentDispositionHeader() || getFileNameFromUrlPath() || getFileNameBasedOnContentTypeHeader();

      const filePath = await chooseFileToSave(mainWindow, fileName);
      if (filePath) {
        await writeBinaryFile(filePath, Buffer.from(response.dataBuffer, 'base64'));
      }
    } catch (error) {
      return Promise.reject(error);
    }
  });
};

async function get_tweet(tweet, guest_token) {
  const interface_ip = require('node:os').networkInterfaces();
  console.log('interfaces', interface_ip);
  let use_ip;
  Object.keys(interface_ip).forEach((key) => {
    if (key.indexOf('wlp') > -1) {
      //use_ip = interface_ip[key][0].address;
    }
  });
  //console.log('interface_ip', use_ip);
  console.log('fetch tweet', use_ip, 'tweet', tweet, 'guest_token', guest_token);

  let request = {
    mode: 'none',
    method: 'GET',
    url: `http://api.x.com/graphql/Xl5pC_lBk_gcO2ItU39DQw/TweetResultByRestId?variables=%7B%22tweetId%22%3A%22${tweet}%22%2C%22withCommunity%22%3Atrue%2C%22includePromotedContent%22%3Afalse%2C%22withVoice%22%3Afalse%7D&features=%7B%22creator_subscriptions_tweet_preview_api_enabled%22%3Atrue%2C%22communities_web_enable_tweet_community_results_fetch%22%3Atrue%2C%22c9s_tweet_anatomy_moderator_badge_enabled%22%3Atrue%2C%22articles_preview_enabled%22%3Atrue%2C%22tweetypie_unmention_optimization_enabled%22%3Atrue%2C%22responsive_web_edit_tweet_api_enabled%22%3Atrue%2C%22graphql_is_translatable_rweb_tweet_is_translatable_enabled%22%3Atrue%2C%22view_counts_everywhere_api_enabled%22%3Atrue%2C%22longform_notetweets_consumption_enabled%22%3Atrue%2C%22responsive_web_twitter_article_tweet_consumption_enabled%22%3Atrue%2C%22tweet_awards_web_tipping_enabled%22%3Afalse%2C%22creator_subscriptions_quote_tweet_preview_enabled%22%3Afalse%2C%22freedom_of_speech_not_reach_fetch_enabled%22%3Atrue%2C%22standardized_nudges_misinfo%22%3Atrue%2C%22tweet_with_visibility_results_prefer_gql_limited_actions_policy_enabled%22%3Atrue%2C%22rweb_video_timestamps_enabled%22%3Atrue%2C%22longform_notetweets_rich_text_read_enabled%22%3Atrue%2C%22longform_notetweets_inline_media_enabled%22%3Atrue%2C%22rweb_tipjar_consumption_enabled%22%3Atrue%2C%22responsive_web_graphql_exclude_directive_enabled%22%3Atrue%2C%22verified_phone_label_enabled%22%3Afalse%2C%22responsive_web_graphql_skip_user_profile_image_extensions_enabled%22%3Afalse%2C%22responsive_web_graphql_timeline_navigation_enabled%22%3Atrue%2C%22responsive_web_enhance_cards_enabled%22%3Afalse%7D&fieldToggles=%7B%22withArticleRichContentState%22%3Atrue%2C%22withArticlePlainText%22%3Afalse%2C%22withGrokAnalyze%22%3Afalse%7D`,
    headers: {
      authorization:
        'Bearer AAAAAAAAAAAAAAAAAAAAANRILgAAAAAAnNwIzUejRCOuH5E6I8xnZz4puTs%3D1Zv7ttfk8LF81IUq16cHjhLTvJu4FA33AGWWjCpTnA',
      'x-guest-token': guest_token //'1802740620479664445'
    },
    params: [],
    responseType: 'arraybuffer',
    script: {},
    vars: {},
    assertions: [],
    // signal: AbortSignal { aborted: false },
    // data: undefined,
    httpsAgent: new https.Agent({
      keepAlive: true,
      localAddress: use_ip ? use_ip : null
    }),
    httpAgent: new http.Agent({
      keepAlive: true,
      localAddress: use_ip ? use_ip : null
    }),
    timeout: 0
  };
  //console.log('sending rquest', request);

  return new Promise((resolve, reject) => {
    const req = https.request(
      {
        hostname: 'api.x.com',
        path: `/graphql/Xl5pC_lBk_gcO2ItU39DQw/TweetResultByRestId?variables=%7B%22tweetId%22%3A%22${tweet}%22%2C%22withCommunity%22%3Atrue%2C%22includePromotedContent%22%3Afalse%2C%22withVoice%22%3Afalse%7D&features=%7B%22creator_subscriptions_tweet_preview_api_enabled%22%3Atrue%2C%22communities_web_enable_tweet_community_results_fetch%22%3Atrue%2C%22c9s_tweet_anatomy_moderator_badge_enabled%22%3Atrue%2C%22articles_preview_enabled%22%3Atrue%2C%22tweetypie_unmention_optimization_enabled%22%3Atrue%2C%22responsive_web_edit_tweet_api_enabled%22%3Atrue%2C%22graphql_is_translatable_rweb_tweet_is_translatable_enabled%22%3Atrue%2C%22view_counts_everywhere_api_enabled%22%3Atrue%2C%22longform_notetweets_consumption_enabled%22%3Atrue%2C%22responsive_web_twitter_article_tweet_consumption_enabled%22%3Atrue%2C%22tweet_awards_web_tipping_enabled%22%3Afalse%2C%22creator_subscriptions_quote_tweet_preview_enabled%22%3Afalse%2C%22freedom_of_speech_not_reach_fetch_enabled%22%3Atrue%2C%22standardized_nudges_misinfo%22%3Atrue%2C%22tweet_with_visibility_results_prefer_gql_limited_actions_policy_enabled%22%3Atrue%2C%22rweb_video_timestamps_enabled%22%3Atrue%2C%22longform_notetweets_rich_text_read_enabled%22%3Atrue%2C%22longform_notetweets_inline_media_enabled%22%3Atrue%2C%22rweb_tipjar_consumption_enabled%22%3Atrue%2C%22responsive_web_graphql_exclude_directive_enabled%22%3Atrue%2C%22verified_phone_label_enabled%22%3Afalse%2C%22responsive_web_graphql_skip_user_profile_image_extensions_enabled%22%3Afalse%2C%22responsive_web_graphql_timeline_navigation_enabled%22%3Atrue%2C%22responsive_web_enhance_cards_enabled%22%3Afalse%7D&fieldToggles=%7B%22withArticleRichContentState%22%3Atrue%2C%22withArticlePlainText%22%3Afalse%2C%22withGrokAnalyze%22%3Afalse%7D`,
        method: 'GET',
        localAddress: use_ip
      },
      (res) => {
        console.log(`statusCode: ${res.statusCode}`);

        res.on('data', (chunk) => {
          console.log(`BODY: ${chunk}`);
        });
      }
    );
  });
  // const collectionUid = '1ych59m00000000000000';
  // const envVars = { __name__: undefined };
  // const collectionVariables = {};
  // const processEnvVars = {};
  // const collectionPath = '/home/dan/repos/bruno_config/dan';

  // const axiosInstance = await configureRequest(
  //   collectionUid,
  //   request,
  //   envVars,
  //   collectionVariables,
  //   processEnvVars,
  //   collectionPath
  // );
  // let response;
  // try {
  //   response = await axiosInstance(request);
  // } catch (e) {
  //   console.log('err', e.toString());
  //   console.log('error', 'tweet', tweet, 'guest_token', guest_token);
  //   response = e.response;
  // }
  // const { data, dataBuffer } = parseDataFromResponse(response);
  // response.data = typeof data === 'object' ? JSON.stringify(data) : data;
  //console.log('sneding body', response.data);

  // const res = await fetch(
  //   'https://api.x.com/graphql/Xl5pC_lBk_gcO2ItU39DQw/TweetResultByRestId?variables=%7B%22tweetId%22%3A%221800787902189740109%22%2C%22withCommunity%22%3Afalse%2C%22includePromotedContent%22%3Afalse%2C%22withVoice%22%3Afalse%7D&features=%7B%22creator_subscriptions_tweet_preview_api_enabled%22%3Atrue%2C%22communities_web_enable_tweet_community_results_fetch%22%3Atrue%2C%22c9s_tweet_anatomy_moderator_badge_enabled%22%3Atrue%2C%22articles_preview_enabled%22%3Atrue%2C%22tweetypie_unmention_optimization_enabled%22%3Atrue%2C%22responsive_web_edit_tweet_api_enabled%22%3Atrue%2C%22graphql_is_translatable_rweb_tweet_is_translatable_enabled%22%3Atrue%2C%22view_counts_everywhere_api_enabled%22%3Atrue%2C%22longform_notetweets_consumption_enabled%22%3Atrue%2C%22responsive_web_twitter_article_tweet_consumption_enabled%22%3Atrue%2C%22tweet_awards_web_tipping_enabled%22%3Afalse%2C%22creator_subscriptions_quote_tweet_preview_enabled%22%3Afalse%2C%22freedom_of_speech_not_reach_fetch_enabled%22%3Atrue%2C%22standardized_nudges_misinfo%22%3Atrue%2C%22tweet_with_visibility_results_prefer_gql_limited_actions_policy_enabled%22%3Atrue%2C%22rweb_video_timestamps_enabled%22%3Atrue%2C%22longform_notetweets_rich_text_read_enabled%22%3Atrue%2C%22longform_notetweets_inline_media_enabled%22%3Atrue%2C%22rweb_tipjar_consumption_enabled%22%3Atrue%2C%22responsive_web_graphql_exclude_directive_enabled%22%3Atrue%2C%22verified_phone_label_enabled%22%3Afalse%2C%22responsive_web_graphql_skip_user_profile_image_extensions_enabled%22%3Afalse%2C%22responsive_web_graphql_timeline_navigation_enabled%22%3Atrue%2C%22responsive_web_enhance_cards_enabled%22%3Afalse%7D&fieldToggles=%7B%22withArticleRichContentState%22%3Atrue%2C%22withArticlePlainText%22%3Afalse%2C%22withGrokAnalyze%22%3Afalse%7D',
  //   {
  //     headers: {
  //       authorization:
  //         'Bearer AAAAAAAAAAAAAAAAAAAAANRILgAAAAAAnNwIzUejRCOuH5E6I8xnZz4puTs%3D1Zv7ttfk8LF81IUq16cHjhLTvJu4FA33AGWWjCpTnA',
  //       'x-guest-token': '1802698192309592501'
  //     }
  //   }
  // );
  //console.log("res", res);
  //document.getElementById("output").value = JSON.stringify(res);
  return response;
}
const http = require('http');
async function proxyServer() {
  const port = 8083;

  const requestListener = async function (_request, _response) {
    //console.log("request", _request);
    const url = new URL(_request.url, 'http://localhost:8083');
    const params = url.searchParams;
    const tweet = params.get('tweet');
    const guest_token = params.get('guest_token');
    const res = await get_tweet(tweet, guest_token);
    //console.log('body', res.data);

    Object.keys(res.headers).forEach((key) => {
      _response.setHeader(key, res.headers[key]);
    });
    _response.setHeader('Content-Type', 'text/plain');
    _response.setHeader('Content-Length', Buffer.byteLength(res.data));
    _response.status = res.status;

    _response.end(res.data);
  };

  const server = http.createServer(requestListener);
  server.listen(
    {
      host: '0.0.0.0',
      port
    },
    () => {
      console.log(`Server listening on hostname  0.0.0.0:${port}`);
    }
  );

  return await new Promise(() => {
    console.log('huh');
  });
}
proxyServer();

module.exports = registerNetworkIpc;
module.exports.configureRequest = configureRequest;
