require('./lib/configReader.js');
require('./lib/logger.js');

var fs = require('fs');
var cluster = require('cluster');
var os = require('os');
var redis = require('redis');

global.utils = require('./lib/utils.js');
global.apiInterfaces = require('./lib/apiInterfaces.js')(config.daemon, config.wallet, config.api);
global.globalInstanceId = new Buffer('41383839', 'hex');

var logSystem = 'master';

global.redisClient = redis.createClient(config.redis.port, config.redis.host, {
    retry_strategy: function (options) {
        if (options.total_retry_time > 1000 * 60 * 30) {
            // End reconnecting after a specific timeout and flush all commands
            // with a individual error
            return new Error('Retry time exhausted');
        }
        if (options.attempt > 10) {
            // End reconnecting with built in error
						log('error', logSystem, 'Reddis client exceeded max retries');
            return undefined;
        }
				log('error', logSystem, 'Reddis client needs to retry (attempt: %d)', [options.attempt]);
        // Reconnect after this many seconds.
        return options.attempt * 1000;
    }
});


if (cluster.isWorker){
    switch(process.env.workerType){
        case 'pool':
            require('./lib/pool.js');
            break;
        case 'blockUnlocker':
            require('./lib/blockUnlocker.js');
            break;
        case 'paymentProcessor':
            require('./lib/paymentProcessor.js');
            break;
        case 'api':
            require('./lib/api.js');
            break;
        case 'cli':
            require('./lib/cli.js');
            break
        case 'chartsDataCollector':
            require('./lib/chartsDataCollector.js');
            break

    }
    return;
}

require('./lib/exceptionWriter.js')(logSystem);


var selectedModules = (function(){

    var validModules = ['pool', 'api', 'unlocker', 'payments', 'chartsDataCollector'];

    for (var i = 0; i < process.argv.length; i++){
        if (process.argv[i].indexOf('-module=') === 0){
            var modulesStr = process.argv[i].split('=')[1];
            var moduleNames = modulesStr.split(',');
            for(var j = 0; j < moduleNames.length;j++)
            {
                var module = moduleNames[j];
                if (!(validModules.indexOf(module) > -1))
                {
                    log('error', logSystem, 'Invalid module "%s", valid modules: %s', [module, validModules.join(', ')]);
                    process.exit();
                }
                return moduleNames;
            }
        }
    }
})();


(function init(){

    checkRedisVersion(function(){

        if (selectedModules){
            log('info', logSystem, 'Running in selected module mode: %s', [selectedModules]);
            for (var i = 0; i < selectedModules.length; i++){
                var selectedModule = selectedModules[i];
                switch(selectedModule){
                    case 'pool':
                        spawnPoolWorkers();
                        break;
                    case 'unlocker':
                        spawnBlockUnlocker();
                        break;
                    case 'payments':
                        spawnPaymentProcessor();
                        break;
                    case 'api':
                        spawnApi();
                        break;
                    case 'chartsDataCollector':
                        spawnChartsDataCollector();
                        break;
                    case 'purchases':
                        spawnPurchaseProcessor();
                        break;
                }
            }
        }
        else{
            spawnPoolWorkers();
            spawnBlockUnlocker();
            spawnPaymentProcessor();
            spawnApi();
            spawnChartsDataCollector();
        }

        spawnCli();

    });
})();


function checkRedisVersion(callback){

    redisClient.info(function(error, response){
        if (error){
            log('error', logSystem, 'Redis version check failed');
            return;
        }
        var parts = response.split('\r\n');
        var version;
        var versionString;
        for (var i = 0; i < parts.length; i++){
            if (parts[i].indexOf(':') !== -1){
                var valParts = parts[i].split(':');
                if (valParts[0] === 'redis_version'){
                    versionString = valParts[1];
                    version = parseFloat(versionString);
                    break;
                }
            }
        }
        if (!version){
            log('error', logSystem, 'Could not detect redis version - must be super old or broken');
            return;
        }
        else if (version < 2.6){
            log('error', logSystem, "You're using redis version %s the minimum required version is 2.6. Follow the damn usage instructions...", [versionString]);
            return;
        }
        callback();
    });
}

function spawnPoolWorkers(){

    if (!config.poolServer || !config.poolServer.enabled || !config.poolServer.ports || config.poolServer.ports.length === 0) return;

    if (config.poolServer.ports.length === 0){
        log('error', logSystem, 'Pool server enabled but no ports specified');
        return;
    }

    var poolWorkers = {};

    var hasWalletPool = (typeof config.poolServer.wallets == 'object' && config.poolServer.wallets.constructor.name == 'Array' && config.poolServer.wallets.length);
    var nextPoolWallet = function() {
        if (!hasWalletPool) return config.poolServer.poolAddress;

        var i = (config.poolServer.wallets.indexOf(config.poolServer.poolAddress) + 1) % config.poolServer.wallets.length;;
        config.poolServer.poolAddress = config.poolServer.wallets[i];
        return config.poolServer.poolAddress;
    };

    if (hasWalletPool) config.poolServer.poolAddress = config.poolServer.wallets[0];

    var numForks = (function(){
        if (!config.poolServer.clusterForks)
            return 1;
        if (config.poolServer.clusterForks === 'auto')
            return os.cpus().length;
        if (isNaN(config.poolServer.clusterForks))
            return 1;
        return config.poolServer.clusterForks;
    })();

    var numForksStarted = 0;
    var rpcDaemonCache = {};
    var rpcDaemonQueue = {};
    var previousBlockHash = '';
    var blockchainHeight = 0;
    var pollUpdates = false;
    var valRotateWalletPercent, numSharesForRotateWalletPercent;

    var resetNumSharesForRotateWallet = function() {
        numSharesForRotateWalletPercent = valRotateWalletPercent ? Math.floor(100*numForks/valRotateWalletPercent) : null;
    };
    var resetRotateWalletPercent = function() {
        valRotateWalletPercent = typeof config.poolServer.rotateWalletPercent == 'number' ? config.poolServer.rotateWalletPercent : null;
        resetNumSharesForRotateWallet();
    }
    resetRotateWalletPercent();

    var sendBlockTemplate = function(worker, res) {
        worker.send({
            type: 'newBlockTemplate',
            result: res.result,
            error: res.error
        });
    };

    var triggerRefresh = function() {
        rpcDaemonCache.getblocktemplate = {};
        pollUpdates = false;
        poolMessageHandler({type: 'jobRefresh'});
    };

    var checkHash = function() {
        apiInterfaces.rpcDaemon('on_getblockhash', [blockchainHeight - 1], function(e, res) {
            if (e) {
                log('error', logSystem, 'Error polling on_getblockhash %j', [e]);
            } else if (res != previousBlockHash) {
                triggerRefresh();
            } else {
                setTimeout(function(){checkHeight();}, config.poolServer.blockRefreshInterval);
            }
        });
    }

    var checkHeight = function() {
        apiInterfaces.rpcDaemon('getblockcount', null, function(e, res) {
            if (e) {
                log('error', logSystem, 'Error polling getblockcount %j', [e]);
            } else if (res.count != blockchainHeight) {
                triggerRefresh();
            } else {
                setTimeout(function(){checkHash();}, config.poolServer.blockRefreshInterval);
            }
        });
    };

    var poolMessageHandler = function(msg) {
        var poolMsg;
        switch(msg.type) {
            case 'rpcDaemon':
                if (msg.command == 'getblocktemplate') {
                    var objKey = msg.params.wallet_address + '_' + msg.params.reserve_size.toString();
                    if (rpcDaemonCache[msg.command] && rpcDaemonCache[msg.command][objKey]) {
                        sendBlockTemplate(poolWorkers[msg.workerId], rpcDaemonCache[msg.command][objKey]);
                    } else {
                        rpcDaemonQueue[msg.command] = rpcDaemonQueue[msg.command] || {};
                        rpcDaemonQueue[msg.command][objKey] = rpcDaemonQueue[msg.command][objKey] || [];
                        rpcDaemonQueue[msg.command][objKey].push({workerId: msg.workerId});
                        apiInterfaces.rpcDaemon(msg.command, msg.params, function(e, res) {
                            rpcDaemonCache[msg.command] = rpcDaemonCache[msg.command] || {};
                            rpcDaemonCache[msg.command][objKey] = {error: e, result: res};
                            if (res) {
                                blockchainHeight = res.height;
                                previousBlockHash = res.prev_hash;
                                if (!pollUpdates) {
                                    pollUpdates = true;
                                    setTimeout(function(){checkHeight();}, config.poolServer.blockRefreshInterval);
                                }
                            }
                            while (rpcDaemonQueue[msg.command][objKey].length) {
                                var w = rpcDaemonQueue[msg.command][objKey].shift();
                                sendBlockTemplate(poolWorkers[w.workerId], rpcDaemonCache[msg.command][objKey]);
                            }
                            resetRotateWalletPercent();
                        });
                    }
                }
                break;
            case 'forkStarted':
                numForksStarted++;
                if (numForksStarted === numForks){
                    log('info', logSystem, 'Pool spawned on %d thread(s)', [numForks]);
                }
                break;
            case 'shareCounter':
                if (valRotateWalletPercent) {
                    numSharesForRotateWalletPercent += (Math.floor(parseInt(msg.sharePc)*0.1) - 1);
                    valRotateWalletPercent = Math.round(100*numForks/numSharesForRotateWalletPercent);
                    log('debug', 'pool', 'Wallet rotate: %d% shares: %d', [valRotateWalletPercent, numSharesForRotateWalletPercent]);

                    if (hasWalletPool && parseInt(Math.floor(Math.random() * 100)) < parseInt(valRotateWalletPercent)) {
                        resetRotateWalletPercent();
                        poolMsg = {type: 'setWallet', data: nextPoolWallet()};
                    }
                }
                break;
            case 'setRotateWalletPercent':
                config.poolServer.rotateWalletPercent = valRotateWalletPercent = msg.data == 'null' ? null : parseInt(msg.data);
                resetNumSharesForRotateWallet();
                log('info', logSystem, 'valRotateWalletPercent set to %s', [valRotateWalletPercent == null ? 'null' : valRotateWalletPercent.toString() + '%']);
                break;
            case 'retarget':
                var [r, d] = msg.data.split(',');
                poolMsg = {type: 'forceRetarget', ratio: parseInt(r), diff: parseInt(d)};
                break;
            case 'nonce':
                var [i, e, a] = msg.data.split(',');
                cluster.workers[i].send({type: 'setNonce', extraNonce: e, additionalRand: a});
                break;
            case 'setReserveSize':
                var sizes = msg.data.split(',');
                var resizeSizeMappings = [];
                if (sizes.length) {
                    for (var i = 0; i < numForks; i++){
                        resizeSizeMappings[i] = sizes[i % sizes.length];
                    }
                }
                poolMsg = {type: 'setReserveSize', data: resizeSizeMappings};
                break;
            case 'refresh':
                if (msg.data == 'wallet') {
                    poolMsg = {type: 'setWallet', data: nextPoolWallet()};
                    break;
                } else if (msg.data == 'instanceId') {
                    global.globalInstanceId = utils.getRandom32bit();
                    poolMsg = {type: 'setInstanceId', data: global.globalInstanceId.hexSlice()};
                    break;
                } else if (msg.data == 'target') {
                    poolMsg = {type: 'retarget'};
                    break;
                }
                rpcDaemonCache.getblocktemplate = {};
                pollUpdates = false;
            case 'highshare':
            case 'jobRefresh':
            case 'promoteNonce':
            case 'setWallet':
            case 'setMinTemplateRefresh':
            case 'setMinTemplatePromote':
            case 'setRotateWalletEffort':
            case 'setExtraRandomBytes':
            case 'setInstanceId':
            case 'poolMiner':
                poolMsg = msg;
                break;
        }

        if (poolMsg) {
            Object.keys(cluster.workers).forEach(function(id) {
                if (cluster.workers[id].type === 'pool'){
                    cluster.workers[id].send(poolMsg);
                }
            });
        }

        return poolMsg;
    };

    redisClient.on('pmessage', function(pattern, channel, message) {
        //log('info', logSystem, 'Request on %s data %s', [channel, message]);
        var poolMsg;
        var msgType = channel.split(':')[1];
        poolMessageHandler({type: msgType, data: message});
    });
    redisClient.psubscribe(config.coin + ':*', function (err, count) {});

    var createPoolWorker = function(forkId){
        var worker = cluster.fork({
            workerType: 'pool',
            forkId: forkId,
            numForks: numForks,
            wallet: config.poolServer.poolAddress
        });
        worker.forkId = forkId;
        worker.numForks = numForks;
        worker.type = 'pool';
        poolWorkers[forkId] = worker;
        worker.on('exit', function(code, signal){
            log('error', logSystem, 'Pool fork %s died, spawning replacement worker...', [forkId]);
            setTimeout(function(){
                createPoolWorker(forkId);
            }, 2000);
        }).on('message', poolMessageHandler);
    };

    var poolSpawn = function(i){
        i++;
        createPoolWorker(i.toString());
        if (i < numForks){
            setTimeout(function(){poolSpawn(i);}, 100);
        }
    };
    poolSpawn(0);
}

function spawnBlockUnlocker(){

    if (!config.blockUnlocker || !config.blockUnlocker.enabled) return;

    var worker = cluster.fork({
        workerType: 'blockUnlocker'
    });
    worker.on('exit', function(code, signal){
        log('error', logSystem, 'Block unlocker died, spawning replacement...');
        setTimeout(function(){
            spawnBlockUnlocker();
        }, 2000);
    });

}

function spawnPaymentProcessor(){

    if (!config.payments || !config.payments.enabled) return;

    var worker = cluster.fork({
        workerType: 'paymentProcessor'
    });
    worker.on('exit', function(code, signal){
        log('error', logSystem, 'Payment processor died, spawning replacement...');
        setTimeout(function(){
            spawnPaymentProcessor();
        }, 2000);
    });
}

function spawnApi(){
    if (!config.api || !config.api.enabled) return;

    var worker = cluster.fork({
        workerType: 'api'
    });
    worker.on('exit', function(code, signal){
        log('error', logSystem, 'API died, spawning replacement...');
        setTimeout(function(){
            spawnApi();
        }, 2000);
    });
}

function spawnCli(){

}

function spawnChartsDataCollector(){
    if (!config.charts) return;

    var worker = cluster.fork({
        workerType: 'chartsDataCollector'
    });
    worker.on('exit', function(code, signal){
        log('error', logSystem, 'chartsDataCollector died, spawning replacement...');
        setTimeout(function(){
            spawnChartsDataCollector();
        }, 2000);
    });
}
