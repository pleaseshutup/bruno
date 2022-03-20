import each from 'lodash/each';
import { rawRequest, gql } from 'graphql-request';

const sendNetworkRequest = async (item) => {
  return new Promise((resolve, reject) => {
    if(item.type === 'http-request') {
      const timeStart = Date.now();
      sendHttpRequest(item.draft ? item.draft.request : item.request)
        .then((response) => {
          const timeEnd = Date.now();
          resolve({
            state: 'success',
            data: response.data,
            headers: Object.entries(response.headers),
            size: response.headers["content-length"],
            status: response.status,
            duration: timeEnd - timeStart
          });
        })
        .catch((err) => reject(err));
    }
  });
};

const sendHttpRequest = async (request) => {
  return new Promise((resolve, reject) => {
    const { ipcRenderer } = window.require("electron");

    console.log(request);
    const headers = {};
    each(request.headers, (h) => {
      if(h.enabled) {
        headers[h.name] = h.value;
      }
    });

    let options = {
      method: request.method,
      url: request.url,
      headers: headers
    };

    if(request.body && request.body.mode === 'json' && request.body.content) {
      options.data = request.body.content;
    }

    ipcRenderer
      .invoke('send-http-request', options)
      .then(resolve)
      .catch(reject);
  });
};

const sendGraphqlRequest = async (request,) => {
  const query = gql`${request.request.body.graphql.query}`;

  const { data, errors, extensions, headers, status } = await rawRequest(request.request.url, query);

  return {
    data,
    headers,
    data,
    errors
  }
};

export {
  sendNetworkRequest
};