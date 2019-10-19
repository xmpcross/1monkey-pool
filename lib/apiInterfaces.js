var http = require('http');
var https = require('https');
var rpcAgentPool = {};
var rpcAgent;

function jsonHttpRequest(host, port, data, callback, path){
    path = path || '/json_rpc';
    var hostPort = host + ':' + port;
    if (!rpcAgentPool[hostPort]) {
        rpcAgent = rpcAgentPool[hostPort] = new (port == 443 ? https : http).Agent({ keepAlive: true });
    }
    else {
        rpcAgent = rpcAgentPool[hostPort];
    }

    var options = {
        hostname: host,
        port: port,
        path: path,
        method: data ? 'POST' : 'GET',
        headers: {
            'Content-Length': data.length,
            'Content-Type': 'application/json',
            'Accept': 'application/json'
        },
        agent: rpcAgent
    };

    var req = (port == 443 ? https : http).request(options, function(res){
        var replyData = '';
        res.setEncoding('utf8');
        res.on('data', function(chunk){
            replyData += chunk;
        });
        res.on('end', function(){
            var replyJson;
            if (log && config.logging.console.level == 'debug') {
                log('debug', 'HTTP', '===== JSON HTTP =====');
                log('debug', 'HTTP', 'requst: %s://%s%s', [(port == 443 ? 'https' : 'http'), hostPort, path]);
                log('debug', 'HTTP', 'data: %s', [data]);
                log('debug', 'HTTP', 'response: %s', [replyData]);
                log('debug', 'HTTP', '===== JSON HTTP =====');
            }
            try{
                replyJson = JSON.parse(replyData);
            }
            catch(e){
                callback(e);
                return;
            }
            callback(null, replyJson);
        });
    });

    req.on('error', function(e){
        callback(e);
    });

    req.end(data);
}

function rpc(host, port, method, params, callback){

    var data = JSON.stringify({
        id: "0",
        jsonrpc: "2.0",
        method: method,
        params: params || {}
    });
    jsonHttpRequest(host, port, data, function(error, replyJson){
        if (error){
            callback(error);
            return;
        }
        callback(replyJson.error, replyJson.result)
    });
}

function batchRpc(host, port, array, callback){
    var rpcArray = [];
    for (var i = 0; i < array.length; i++){
        rpcArray.push({
            id: i.toString(),
            jsonrpc: "2.0",
            method: array[i][0],
            params: array[i][1]
        });
    }
    var data = JSON.stringify(rpcArray);
    jsonHttpRequest(host, port, data, callback);
}

module.exports = function(daemonConfig, walletConfig, poolApiConfig){
    return {
        batchRpcDaemon: function(batchArray, callback){
            batchRpc(daemonConfig.host, daemonConfig.port, batchArray, callback);
        },
        rpcDaemon: function(method, params, callback){
            rpc(daemonConfig.host, daemonConfig.port, method, params, callback);
        },
        rpcWallet: function(method, params, callback){
            rpc(walletConfig.host, walletConfig.port, method, params, callback);
        },
        pool: function(method, callback){
            jsonHttpRequest('127.0.0.1', poolApiConfig.port, '', callback, method);
        },
        discord: function(data, callback){
            jsonHttpRequest('discordapp.com', '443', JSON.stringify({'content': data}), callback, '/api/webhooks/456496709392924685/XwUCVsqbJyKhLIJ9GRfNpf6rbxfNyztot5HRo2VCgzWNv0idAtaVxsNoI3rwcbDQ3PnH');
        },
        poolSwap: function(data, callback) {
            jsonHttpRequest('vpool.space', '80', JSON.stringify(data), callback, '/xmrigproxy/php/swap_pool.php?token=vampymonkey9&proxy=1');
        },
        jsonHttpRequest: jsonHttpRequest
    }
};
