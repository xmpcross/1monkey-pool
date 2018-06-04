var fs = require('fs');
var net = require('net');
var crypto = require('crypto');

var async = require('async');
var bignum = require('bignum');
var multiHashing = require('cryptonight-hashing');
var cnUtil = require('cryptonote-util');

// Must exactly be 8 hex chars, already lowercased before test
var noncePattern = new RegExp("^[0-9a-f]{8}$");

//SSL for claymore
var tls = require('tls');

var forkId = process.env.forkId;
var threadId = '(Thread ' + forkId + ') ';
var alternateReserveSize = (forkId % 2 == 0);

var logSystem = 'pool';
require('./exceptionWriter.js')(logSystem);

var apiInterfaces = require('./apiInterfaces.js')(config.daemon, config.wallet, config.api);
var utils = require('./utils.js');
Buffer.prototype.toByteArray = function () {
  return Array.prototype.slice.call(this, 0)
}

var log = function(severity, system, text, data){
    global.log(severity, system, threadId + text, data);
};

var cryptoNight = multiHashing['cryptonight'];

var diff1 = bignum('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF', 16);

var instanceId = crypto.randomBytes(4);

var validBlockTemplates = [];
var currentBlockTemplate;
var currentBlockHeight = 0;
var currentBlockHash = "";

var connectedMiners = {};
var connectedMinersCount = 0;

var bannedIPs = {};
var perIPStats = {};

var shareTrustEnabled = config.poolServer.shareTrust && config.poolServer.shareTrust.enabled;
var shareTrustStepFloat = shareTrustEnabled ? config.poolServer.shareTrust.stepDown / 100 : 0;
var shareTrustMinFloat = shareTrustEnabled ? config.poolServer.shareTrust.min / 100 : 0;

var banningEnabled = config.poolServer.banning && config.poolServer.banning.enabled;

// Pool Wallet Tweaks
var rotatingWallet = (typeof config.poolServer.poolAddress == 'object' && config.poolServer.poolAddress.constructor.name == 'Array' && config.poolServer.poolAddress.length);
var hasWalletPool = (typeof config.poolServer.wallets == 'object' && config.poolServer.wallets.constructor.name == 'Array' && config.poolServer.wallets.length);
var nextPoolWalletAddress = poolWalletAddress = rotatingWallet ? getRotatingPoolWalletAddress() : process.env.wallet;

/* Every 30 seconds clear out timed-out miners and old bans */
setInterval(function(){
    if (banningEnabled){
        for (ip in bannedIPs){
            var banTime = bannedIPs[ip];
            if (now - banTime > config.poolServer.banning.time * 1000) {
                delete bannedIPs[ip];
                delete perIPStats[ip];
                log('info', logSystem, 'Ban dropped for %s', [ip]);
            }
        }
    }

    setWorkerCount();

}, 30000);

process.on('message', function(message) {
    switch (message.type) {
        case 'banIP':
            bannedIPs[message.ip] = Date.now();
            break;
        case 'forceRetarget':
            log('info', logSystem, 'Force retarget: %j', [message]);
            for (var minerId in connectedMiners){
                if (Math.floor(Math.random() * 100) < message.ratio) {
                    var miner = connectedMiners[minerId];
                    miner.minDiff = message.diff;
                    miner.setNewDiff(message.diff);
                }
            }
            break;
        case 'setWallet':
            setNextPoolWalletAddress(message.data);
            break;
        case 'refresh':
            if (!message.data.match(/template/i)) {
                instanceId = crypto.randomBytes(4);
                log('info', logSystem, 'InstanceId refreshed');
            }

            log('info', logSystem, 'Refreshing block template');
            jobRefresh('get_template');

            break;
    }
});

function IsBannedIp(ip){
    if (!banningEnabled || !bannedIPs[ip]) return false;

    var bannedTime = bannedIPs[ip];
    var bannedTimeAgo = Date.now() - bannedTime;
    var timeLeft = config.poolServer.banning.time * 1000 - bannedTimeAgo;
    if (timeLeft > 0){
        return true;
    }
    else {
        delete bannedIPs[ip];
        log('info', logSystem, 'Ban dropped for %s', [ip]);
        return false;
    }
}

function BlockTemplate(template){
    /*
    Generating a block template is a simple thing.  Ask for a boatload of information, and go from there.
    Important things to consider.
    The reserved space is 13 bytes long now in the following format:
    Assuming that the extraNonce starts at byte 130:
    |130-133|134-137|138-141|142-145|
    |minerNonce/extraNonce - 4 bytes|instanceId - 4 bytes|clientPoolNonce - 4 bytes|clientNonce - 4 bytes|
    This is designed to allow a single block template to be used on up to 4 billion poolSlaves (clientPoolNonce)
    Each with 4 billion clients. (clientNonce)
    While being unique to this particular pool thread (instanceId)
    With up to 4 billion clients (minerNonce/extraNonce)
     */

    // Store pool wallet address on block template
    this.wallet = poolWalletAddress;

    // Set this.blob equal to the BT blob that we get from upstream.
    this.blob = template.blocktemplate_blob;
    this.idHash = crypto.createHash('md5').update(template.blocktemplate_blob).digest('hex');

    // Set this.diff equal to the known diff for this block.
    this.difficulty = template.difficulty;

    // Set this.height equal to the known height for this block.
    this.height = template.height;

    // Set this.reserveOffset to the byte location of the reserved offset.
    this.reserveOffset = template.reserved_offset;

    // Set this.buffer to the binary decoded version of the BT blob.
    this.buffer = new Buffer(this.blob, 'hex');

    // Copy the Instance ID to the reserve offset + 4 bytes deeper.  Copy in 4 bytes.
    instanceId.copy(this.buffer, this.reserveOffset + 4, 0, 3);

    // Generate a clean, shiny new buffer.
    this.previous_hash = new Buffer(32);

    // Copy in bytes 7 through 39 to this.previous_hash from the current BT.
    this.buffer.copy(this.previous_hash, 0, 7, 39);

    this.MAX_EXTRA_NONCE = 1677215;

    // Reset the Nonce. - This is the per-miner/pool nonce
    this.extraNonce = 0;

    // The clientNonceLocation is the location at which the client pools should set the nonces for each of their clients.
    this.clientNonceLocation = this.reserveOffset + 12;

    // The clientPoolLocation is for multi-thread/multi-server pools to handle the nonce for each of their tiers.
    this.clientPoolLocation = this.reserveOffset + 8;
}

BlockTemplate.prototype = {
    getNonce: function() {
        this.extraNonce++;

        if (this.extraNonce > this.MAX_EXTRA_NONCE) {
            this.extraNonce = this.extraNonce - this.MAX_EXTRA_NONCE;
        }
    },
    nextBlob: function(nicehash){
        this.getNonce();
        this.buffer.writeUInt32BE(this.extraNonce * (nicehash && alternateReserveSize ? 256 : 1), this.reserveOffset);
        return convertBlob(this.buffer).toString('hex');
    },
    nextBlobWithChildNonce: function(){
        this.getNonce();
        // Write a 32 bit integer, big-endian style to the 0 byte of the reserve offset.
        this.buffer.writeUInt32BE(this.extraNonce, this.reserveOffset);
        // Don't convert the blob to something hashable.
        return this.buffer.toString('hex');
    }
};

function convertBlob(blobBuffer) {
    return cnUtil.convert_blob(blobBuffer);
}

function constructNewBlob(blockTemplate, NonceBuffer) {
    return cnUtil.construct_block_blob(blockTemplate, NonceBuffer);
}

function getBlockID(blockBuffer) {
    return cnUtil.get_block_id(blockBuffer);
}

function getBlockTemplate(callback){
    apiInterfaces.rpcDaemon('getblocktemplate', {reserve_size: alternateReserveSize ? 17 : 8, wallet_address: nextPoolWalletAddress}, callback);
}

function getBlockCount(callback){
    apiInterfaces.rpcDaemon('getblockcount', null, callback);
}

function getBlockHash(callback){
    apiInterfaces.rpcDaemon('on_getblockhash', [currentBlockHeight - 1], callback);
}

function jobLoop()
{
    jobRefresh();
    setTimeout(function(){ jobLoop(); }, config.poolServer.blockRefreshInterval);
}

var jobRefreshCompleteCallback = null;
function jobRefreshError(text, error)
{
    log('error', logSystem, text, [error]);
    if(jobRefreshCompleteCallback != null)
        jobRefreshCompleteCallback(false);
}

var jobRefreshCounter = 0;
function jobRefresh(state){
    state = state || "check_force";

    switch(state){
    case "check_force":
        if(jobRefreshCounter % config.poolServer.blockRefreshForce == 0)
            jobRefresh("get_template");
        else
            jobRefresh("check_count");
        jobRefreshCounter++;
        break;

    case "check_count":
        getBlockCount(function(error, result){
            if (error){
                jobRefreshError('Error polling getblockcount %j', error);
                return;
            }

            if(result.count == currentBlockHeight) {
                jobRefresh("check_hash");
                return;
            }

            log('debug', logSystem, 'Blockchain height changed to %s, updating template.', [result.count]);
            jobRefresh("get_template");
            return;
        });
    break;

    case "check_hash":
        getBlockHash(function(error, result){
            if(error) {
                jobRefreshError('Error polling on_getblockhash %j', error);
                return;
            }

            if(result == currentBlockHash) {
                if(jobRefreshCompleteCallback != null)
                     jobRefreshCompleteCallback(true);
                return;
            }

            log('debug', logSystem, 'Blockchain hash changed to %s, updating template.', [currentBlockHash]);
            jobRefresh("get_template");
            return;
        });
        break;

    case "get_template":
        getBlockTemplate(function(error, result){
            if(error) {
                jobRefreshError('Error polling getblocktemplate %j', error);
                return;
            }

            if (!currentBlockTemplate
                || result.height > currentBlockTemplate.height
                || (result.height == currentBlockTemplate.height
                    && result.blocktemplate_blob != currentBlockTemplate.blob)) {

                currentBlockHeight = result.height;
                currentBlockHash = result.prev_hash;

                processBlockTemplate(result);
                log('info', logSystem, 'New block to mine at height %d w/ difficulty of %d wallet %s', [result.height, result.difficulty, currentBlockTemplate.wallet.substr(-6)]);
            }

            if(jobRefreshCompleteCallback != null)
                jobRefreshCompleteCallback(true);
        });
    }
}

function processBlockTemplate(template){
    if (nextPoolWalletAddress != poolWalletAddress) {
        poolWalletAddress = nextPoolWalletAddress;
    }

    currentBlockTemplate = new BlockTemplate(template);

    for (var minerId in connectedMiners){
        var miner = connectedMiners[minerId];
        miner.pushMessage('job', miner.getJob(true));
    }

    validBlockTemplates.push(currentBlockTemplate);
    if (validBlockTemplates.length > 3) validBlockTemplates.shift();

    if (rotatingWallet && Object.keys(connectedMiners).length) nextPoolWalletAddress = getRotatingPoolWalletAddress();

    if (forkId == 1) {
        redisClient.hmset(config.coin + ':network', {
            height: template.height || 0,
            difficulty: template.difficulty || 0,
            expected_reward: template.expected_reward || 0,
            timestamp: Math.round(Date.now()/1000)
        });
    }
}

/* Reset worker counts */
function setWorkerCount() {
    var c = Object.keys(connectedMiners).length;
    if (c == connectedMinersCount) return;

    connectedMinersCount = c;
    redisClient.hset(config.coin + ':workers', forkId, connectedMinersCount);
    log('info', logSystem, 'Workers connected: %d', [connectedMinersCount]);
}

function getRotatingPoolWalletAddress() {
    var i = Math.floor(config.poolServer.poolAddress.length * Math.random());
    return config.poolServer.poolAddress[i];
}

function getNextPoolWallet() {
    if (!hasWalletPool) return nextPoolWalletAddress || poolWalletAddress;

    var i = Math.floor(config.poolServer.wallets.length * Math.random());
    return config.poolServer.wallets[i];
}

function setNextPoolWalletAddress(addr) {
    nextPoolWalletAddress = addr;
    log('info', logSystem, 'Pool wallet changed to %s', [addr]);
    jobRefresh("get_template");
}

(function init(){
    jobRefreshCompleteCallback = function(sucessful){
        if (!sucessful){
            log('error', logSystem, 'Could not start pool');
            return;
        }
        startPoolServerTcp(function(successful){ });
        jobRefreshCompleteCallback = null;
    };

    jobLoop();
})();

/* Allowed Miner Address Check */
var poolAddressPrefix = cnUtil.address_decode(new Buffer(poolWalletAddress)).toString();
var allowedPrefixes = config.poolServer.allowedMinerAddressPrefixes;
if (!allowedPrefixes) allowedPrefixes = config.poolServer.allowedMinerAddressPrefixes = [];
if (allowedPrefixes.indexOf(poolAddressPrefix) == -1) allowedPrefixes.push(poolAddressPrefix);

/* Dynamic Vardiff */
var checkRetargetInterval;
var varDiffSettings = config.poolServer.varDiff;
if (!varDiffSettings.forced) varDiffSettings.forced = 'off';
if (!varDiffSettings.checkSettingsTime) varDiffSettings.checkSettingsTime = 30;
if (!varDiffSettings.enableTargetTimeVariance) varDiffSettings.enableTargetTimeVariance = 'on';
if (!varDiffSettings.targetTimeVariance) varDiffSettings.targetTimeVariance = '-2,2';
if (!varDiffSettings.jobDiffScale) varDiffSettings.jobDiffScale = 1;
redisClient.hmset(config.coin + ':vardiff', varDiffSettings);

function getTargetTimeVarianceRange() {
    config.poolServer.targetTimeRange = varDiffSettings.targetTimeVariance.split(',').map(function(v) {
        return parseInt(v) + varDiffSettings.targetTime;
    });
    return config.poolServer.targetTimeRange;
}

setInterval(function(){
    redisClient.hgetall(config.coin + ':vardiff', function(err, obj) {
        var settingsChanged = false;
        for (var dynamicVarDiffSetting in obj) {
            var dynamicVardiffValue = obj[dynamicVarDiffSetting];
            var currentSettingValue = config.poolServer.varDiff[dynamicVarDiffSetting];
            if (dynamicVardiffValue != currentSettingValue) {
                log('info', logSystem, 'Updating Vardiff setting \'%s\' from \'%s\' to \'%s\'', [dynamicVarDiffSetting, currentSettingValue, dynamicVardiffValue]);
                config.poolServer.varDiff[dynamicVarDiffSetting] = dynamicVardiffValue;
                settingsChanged = true;
                if (dynamicVarDiffSetting == 'retargetTime') {
                    clearInterval(checkRetargetInterval);
                    checkRetargetInterval = setInterval(checkRetarget, config.poolServer.varDiff.retargetTime * 1000);
                }
                else if (dynamicVarDiffSetting == 'targetTimeVariance') {
                    getTargetTimeVarianceRange();
                }
            }
        }
        if (settingsChanged) VarDiff = getVarDiff();
    });

}, config.poolServer.varDiff.checkSettingsTime * 1000);

function checkTargetTime() {
    if (!varDiffSettings.enableTargetTimeVariance || varDiffSettings.enableTargetTimeVariance == 'off') {
        return;
    }

    var tRange = config.poolServer.targetTimeRange || getTargetTimeVarianceRange();
    config.poolServer.varDiff.targetTime = tRange[0] + Math.floor(Math.random() * (tRange[1] - tRange[0] + 1));
    VarDiff = getVarDiff();

    log('info', logSystem, 'Setting VarDiff target time to %d/sec', [config.poolServer.varDiff.targetTime]);
}

function checkRetarget() {
    if (Object.keys(connectedMiners).length) checkTargetTime();
    var now = Date.now() / 1000 | 0;
    for (var minerId in connectedMiners){
        var miner = connectedMiners[minerId];
        if(!miner.noRetarget || config.poolServer.varDiff.forced == 'on') {
            miner.retarget(now);
        }
    }
}

checkRetargetInterval = setInterval(checkRetarget, config.poolServer.varDiff.retargetTime * 1000);
checkTargetTime();

function getVarDiff() {
    var variance = config.poolServer.varDiff.variancePercent / 100 * config.poolServer.varDiff.targetTime;
    return {
        variance: variance,
        bufferSize: config.poolServer.varDiff.retargetTime / config.poolServer.varDiff.targetTime * 4,
        tMin: config.poolServer.varDiff.targetTime - variance,
        tMax: config.poolServer.varDiff.targetTime + variance,
        maxJump: config.poolServer.varDiff.maxJump
    };
}

var VarDiff = getVarDiff();

function Miner(id, login, workerName, pass, remote, startingDiff, noRetarget, pushMessage, agent){
    this.id = id;
    this.login = login;
    this.pass = pass;
    this.remote = remote;
    this.ip = remote.ip;
    this.pushMessage = pushMessage;
    this.heartbeat();
    this.noRetarget = noRetarget;
    this.minDiff = parseInt(startingDiff);
    this.workerName = workerName;
    this.validJobs = [];

    // Vardiff related variables
    this.shareTimeRing = utils.ringBuffer(16);
    this.lastShareTime = Date.now() / 1000 | 0;

    this.validShares = 0;
    this.invalidShares = 0;

    if (shareTrustEnabled) {
        this.trust = {
            threshold: config.poolServer.shareTrust.threshold,
            probability: 1,
            penalty: 0
        };
    }

    this.proxy = false; this.nicehash = false;
    if (agent && agent.includes('xmr-node-proxy')) {
        this.proxy = true;
    }
    else if (agent && agent.includes('NiceHash')) {
        this.noRetarget = true;
        this.nicehash = true;
        this.minDiff = Math.max(this.minDiff, config.poolServer.nicehashDiff || 200000, config.poolServer.varDiff.minDiff);
    }

    this.difficulty = this.minDiff;
    this.cachedJob = null;
}
Miner.prototype = {
    retarget: function(now){

        var options = config.poolServer.varDiff;
        var minDiff = Math.max(options.minDiff, this.minDiff);

        var sinceLast = now - this.lastShareTime;
        var decreaser = sinceLast > VarDiff.tMax;

        var avg = this.shareTimeRing.avg(decreaser ? sinceLast : null);
        var newDiff;

        var direction;

        if (avg > VarDiff.tMax && this.difficulty > minDiff){
            newDiff = options.targetTime / avg * this.difficulty;
            newDiff = newDiff > minDiff ? newDiff : minDiff;
            direction = -1;
        }
        else if (avg < VarDiff.tMin && this.difficulty < options.maxDiff){
            newDiff = options.targetTime / avg * this.difficulty;
            newDiff = newDiff < options.maxDiff ? newDiff : options.maxDiff;
            direction = 1;
        }
        else{
            return;
        }

        if (Math.abs(newDiff - this.difficulty) / this.difficulty * 100 > options.maxJump){
            var change = options.maxJump / 100 * this.difficulty * direction;
            newDiff = this.difficulty + change;
        }

        this.setNewDiff(newDiff);
        this.shareTimeRing.clear();
        if (decreaser) this.lastShareTime = now;
    },
    setNewDiff: function(newDiff){
        newDiff = Math.round(newDiff);
        if (this.difficulty === newDiff) return;
        log('info', logSystem, 'Retargetting difficulty %d to %d for %s', [this.difficulty, newDiff, this.remote.addr]);
        this.pendingDifficulty = newDiff;
        this.pushMessage('job', this.getJob(true));
    },
    heartbeat: function(){
        this.lastBeat = Date.now();
    },
    getTargetHex: function(){
        if (this.pendingDifficulty){
            this.lastDifficulty = this.difficulty;
            this.difficulty = this.pendingDifficulty;
            this.pendingDifficulty = null;
        }

        var padded = new Buffer(32);
        padded.fill(0);

        var diffBuff = diff1.div(this.difficulty).toBuffer();
        diffBuff.copy(padded, 32 - diffBuff.length);

        var buff = padded.slice(0, 4);
        var buffArray = buff.toByteArray().reverse();
        var buffReversed = new Buffer(buffArray);
        this.target = buffReversed.readUInt32BE(0);
        var hex = buffReversed.toString('hex');
        return hex;
    },
    getJob: function(forceNew){
        if (!forceNew
            && this.lastBlockHeight === currentBlockTemplate.height
            && currentBlockTemplate.idHash === this.validJobs.slice(-1)[0].blockHash
            && !this.pendingDifficulty
            && this.cachedJob !== null) {
            return this.cachedJob;
        }

        this.lastBlockHeight = currentBlockTemplate.height;
        var target = this.getTargetHex();

        var blob = this.proxy
            ? currentBlockTemplate.nextBlobWithChildNonce()
            : currentBlockTemplate.nextBlob(this.nicehash);

        var newJob = {
            id: utils.uid(),
            extraNonce: currentBlockTemplate.extraNonce,
            height: currentBlockTemplate.height,
            difficulty: this.difficulty,
            diffHex: this.diffHex,
            submissions: []
        };

        if (this.proxy) {
            newJob.clientPoolLocation = currentBlockTemplate.clientPoolLocation;
            newJob.clientNonceLocation = currentBlockTemplate.clientNonceLocation;
        }
        else {
            if (this.nicehash && alternateReserveSize) newJob.extraNonce *= 256;
            newJob.blockHash = currentBlockTemplate.idHash;
        }

        this.validJobs.push(newJob);

        if (this.validJobs.length > 4)
            this.validJobs.shift();

        this.cachedJob = !this.proxy ? {
            blob: blob,
            target: target,
        } : {
            blocktemplate_blob: blob,
            difficulty: currentBlockTemplate.difficulty,
            height: currentBlockTemplate.height,
            reserved_offset: currentBlockTemplate.reserveOffset,
            client_nonce_offset: currentBlockTemplate.clientNonceLocation,
            client_pool_offset: currentBlockTemplate.clientPoolLocation,
            target_diff: this.difficulty,
            target_diff_hex: this.target,
        };

        this.cachedJob.job_id = newJob.id;
        this.cachedJob.id = this.id;

        return this.cachedJob;
    },
    checkBan: function(validShare){
        // Store valid/invalid shares per IP (already initialized with 0s)
        // Init global per-IP shares stats
        if (!perIPStats[this.ip]){
            perIPStats[this.ip] = { validShares: 0, invalidShares: 0 };
        }
        var stats = perIPStats[this.ip];
        validShare ? (stats.validShares++, this.validShares++) : (stats.invalidShares++, this.invalidShares++);

        if (!banningEnabled) return;

        if (stats.validShares + stats.invalidShares >= config.poolServer.banning.checkThreshold){
            if (stats.invalidShares / stats.validShares >= config.poolServer.banning.invalidPercent / 100){
                log('warn', logSystem, 'Banned %s@%s', [this.login, this.ip]);
                bannedIPs[this.ip] = Date.now();
                delete connectedMiners[this.id];
                process.send({type: 'banIP', ip: this.ip});
            }
            else{
                stats.invalidShares = 0;
                stats.validShares = 0;
            }
        }
    }
};

function recordShareData(miner, job, shareDiff, blockCandidate, hashHex, shareType, blockTemplate){

    var dateNow = Date.now();
    var dateNowSeconds = dateNow / 1000 | 0;
    // Expire the stats per unique worker after 7 days. Note that an
    // address and IP can have multiple workers (e.g. one process for CPU and
    // one for GPU).
    var uniqueWorkerTtl = 86400 * 7;
    var uniqueWorkerKey = [config.coin, 'unique_workers', miner.login, miner.ip].join(':');

    var redisCommands = [
        ['hincrby', config.coin + ':shares:roundCurrent', miner.login, job.difficulty],
        ['zadd', config.coin + ':hashrate', dateNowSeconds, [job.difficulty, miner.login, dateNow].join(':')],
        ['zadd', config.coin + ':hashrate', dateNowSeconds, [job.difficulty, miner.login + '+' + miner.workerName, dateNow].join(':')],
        ['hincrby', config.coin + ':workers:' + miner.login, 'hashes', job.difficulty],
        ['hset', config.coin + ':workers:' + miner.login, 'lastShare', dateNowSeconds],
        ['hset', uniqueWorkerKey, 'lastShare', dateNowSeconds],
        ['hset', uniqueWorkerKey, 'address', miner.login],
        ['expire', uniqueWorkerKey, uniqueWorkerTtl],
        ['zadd', config.coin + ':sharelog', dateNow, [dateNow, job.height, shareDiff, job.difficulty, blockTemplate.difficulty, miner.remote.addr, blockCandidate ? blockTemplate.wallet : ''].join(':')]
    ];

    if (blockCandidate){
        redisCommands.push(['hset', config.coin + ':stats', 'lastBlockFound', Date.now()]);
        redisCommands.push(['rename', config.coin + ':shares:roundCurrent', config.coin + ':shares:round' + job.height]);
        redisCommands.push(['hgetall', config.coin + ':shares:round' + job.height]);
    }

    redisClient.multi(redisCommands).exec(function(err, replies){
        if (err){
            log('error', logSystem, 'Failed to insert share data into redis %j \n %j', [err, redisCommands]);
            return;
        }
        if (blockCandidate){
            var workerShares = replies[replies.length - 1];
            var totalShares = Object.keys(workerShares).reduce(function(p, c){
                return p + parseInt(workerShares[c]);
            }, 0);
            redisClient.zadd(config.coin + ':blocks:candidates', job.height, [
                hashHex,
                Date.now() / 1000 | 0,
                blockTemplate.difficulty,
                totalShares
            ].join(':'), function(err, result){
                if (err){
                    log('error', logSystem, 'Failed inserting block candidate %s \n %j', [hashHex, err]);
                }
            });
        }

    });

    log('info', logSystem, 'Accepted %s share at difficulty %d/%d - %s%% job %s%% block - from %s name: %s',
        [shareType, shareDiff, job.difficulty, (shareDiff*100/job.difficulty).toFixed(2), (shareDiff*100/blockTemplate.difficulty).toFixed(2), miner.remote.addr, miner.workerName]
    );
}

function getShareBuffer(miner, job, blockTemplate, params) {
    var template = new Buffer(blockTemplate.buffer.length);
    var nonce = params.nonce;
    blockTemplate.buffer.copy(template);
    template.writeUInt32BE(job.extraNonce, blockTemplate.reserveOffset);

    if (miner.proxy) {
        template.writeUInt32BE(params.poolNonce, job.clientPoolLocation);
        template.writeUInt32BE(params.workerNonce, job.clientNonceLocation);
    }

    try {
        var shareBuffer = constructNewBlob(template, new Buffer(nonce, 'hex'));
        return shareBuffer;
    }
    catch (e) {
        log('error', logSystem, "Can't constructNewBlob with %s nonce from miner %s: %s", [nonce, miner.remote.addr, e]);
        return null;
    }
}

function processShare(miner, job, blockTemplate, params){
    var hash;
    var shareType;
    var resultHash = params.result;

    var shareBuffer = getShareBuffer(miner, job, blockTemplate, params);
    if (shareBuffer === null) {
        return false;
    }

    if (shareTrustEnabled && miner.trust.threshold <= 0 && miner.trust.penalty <= 0 && Math.random() > miner.trust.probability){
        try {
            hash = new Buffer(resultHash, 'hex');
        }
        catch (e) {
            log('warn', logSystem, 'Invalid share from trusted miner');
            return false;
        }
        shareType = 'trusted';
    }
    else {
        var convertedBlob = convertBlob(shareBuffer);
        var cn_variant = (config.cnVariantBlock && config.cnVariantBlock < job.height) ? 1 : 0;
        hash = cryptoNight(convertedBlob, cn_variant);
        shareType = 'valid';
    }

    if (hash.toString('hex') !== resultHash) {
        log('warn', logSystem, 'Bad hash from miner %s@%s', [miner.login, miner.ip]);
        return false;
    }

    var hashArray = hash.toByteArray().reverse();
    var hashNum = bignum.fromBuffer(new Buffer(hashArray));
    var hashDiff = diff1.div(hashNum);

    if (hashDiff.ge(blockTemplate.difficulty)){

        apiInterfaces.rpcDaemon('submitblock', [shareBuffer.toString('hex')], function(error, result){
            if (error){
                log('error', logSystem, 'Error submitting block at height %d from %s, share type: "%s" - %j', [job.height, miner.remote.addr, shareType, error]);
                recordShareData(miner, job, hashDiff.toString(), false, null, shareType, blockTemplate);
            }
            else{
                var blockFastHash = getBlockID(shareBuffer).toString('hex');
                log('block', logSystem,
                    '##### MONKEY FOUND BLOCK ######## Block %s found with diff %d at height %d diff %d by miner %s wallet %s ##### MONKEY FOUND BLOCK ########',
                    [blockFastHash.substr(0, 6), hashDiff, job.height, blockTemplate.difficulty, miner.remote.addr, blockTemplate.wallet.substr(-6)]
                );
                recordShareData(miner, job, hashDiff.toString(), true, blockFastHash, shareType, blockTemplate);
                handleBlockFound();
            }
        });
    }

    else if (hashDiff.lt(job.difficulty/varDiffSettings.jobDiffScale)){
        log('warn', logSystem, 'Rejected low difficulty share of %s from %s', [hashDiff.toString(), miner.remote.addr]);
        return false;
    }
    else{
        recordShareData(miner, job, hashDiff.toString(), false, null, shareType, blockTemplate);
    }

    return true;
}

function handleBlockFound() {
    if (hasWalletPool) {
        process.send({type: 'setWallet', wallet: getNextPoolWallet()});
    }
    else {
        jobRefresh("get_template");
    }
}

function handleMinerMethod(method, params, remote, portData, sendReply, pushMessage){
    var miner = connectedMiners[remote.addr];
    // Check for ban here, so preconnected attackers can't continue to screw you
    if (IsBannedIp(remote.ip)){
        sendReply('your IP is banned');
        return;
    }
    switch(method){
        case 'login':
            var login = params.login;
            if (!login){
                sendReply('missing login');
                return;
            }

            var difficulty = portData.difficulty;
            var workerName = params.pass;
            var noRetarget = false;
            // Grep the worker name.
            var workerNameCharPos = login.indexOf('+');
            if (workerNameCharPos != -1) {
              workerName = login.substr(workerNameCharPos + 1);
              login = login.substr(0, workerNameCharPos);
            }
            if(config.poolServer.fixedDiff.enabled) {
                var fixedDiffCharPos = login.indexOf(config.poolServer.fixedDiff.addressSeparator);
                if(fixedDiffCharPos != -1) {
                    noRetarget = true;
                    var workerDifficulty = login.substr(fixedDiffCharPos + 1);
                    if (workerDifficulty > difficulty) {
                        difficulty = workerDifficulty;
                    }
                    login = login.substr(0, fixedDiffCharPos);
                }
            }

            // Check that the address prefix is sane.
            var addressPrefix = cnUtil.address_decode(new Buffer(login)).toString();
            if (config.poolServer.allowedMinerAddressPrefixes.indexOf(addressPrefix) == -1) {
                log('info', logSystem, 'Invalid address prefix %s for address %s', [addressPrefix, login]);
                sendReply('invalid address used');
                return;
            }

            var minerId = utils.uid();
            miner = new Miner(minerId, login, workerName, params.pass, remote, difficulty, noRetarget, pushMessage, params.agent);
            connectedMiners[remote.addr] = miner;
            
            sendReply(null, {
                id: minerId,
                job: miner.getJob(true),
                status: 'OK'
            });
            log('warn', logSystem, 'Miner connected from %s worker name: %s diff %d (%s) addr: %s', [miner.remote.addr, workerName, miner.difficulty, (miner.noRetarget ? 'F' : 'V'), login]);
            break;
        case 'getjob':
            if (!miner){
                sendReply('Unauthenticated');
                return;
            }
            miner.heartbeat();
            sendReply(null, miner.getJob());
            break;
        case 'submit':
            if (!miner){
                sendReply('Unauthenticated');
                return;
            }
            miner.heartbeat();

            var job = miner.validJobs.filter(function(job){
                return job.id === params.job_id;
            })[0];

            if (!job){
                sendReply('Invalid job id');
                return;
            }

            params.nonce = params.nonce.substr(0, 8).toLowerCase();
            if (!noncePattern.test(params.nonce)) {
                 var minerText = miner ? (' ' + miner.login + '@' + miner.ip) : '';
                 log('warn', logSystem, 'Malformed nonce: ' + JSON.stringify(params) + ' from ' + minerText);
                 perIPStats[miner.ip] = { validShares: 0, invalidShares: 999999 };
                 miner.checkBan(false);
                 sendReply('Duplicate share');
                 return;
            }

            if (job.submissions.indexOf(params.nonce) !== -1){
                var minerText = miner ? (' ' + miner.login + '@' + miner.ip) : '';
                log('warn', logSystem, 'Duplicate share: ' + JSON.stringify(params) + ' from ' + minerText);
                perIPStats[miner.ip] = { validShares: 0, invalidShares: 999999 };
                miner.checkBan(false);
                sendReply('Duplicate share');
                return;
            }

            job.submissions.push(params.nonce);

            var blockTemplate = currentBlockTemplate.height === job.height ? currentBlockTemplate : validBlockTemplates.filter(function(t){
                return t.height === job.height;
            })[0];

            if (!blockTemplate){
                var minerText = miner ? (' ' + miner.login + '@' + miner.ip) : '';
                log('warn', logSystem, 'Block expired, Height: ' + job.height + ' from ' + minerText);
                sendReply('Block expired');
                return;
            }

            var shareAccepted = processShare(miner, job, blockTemplate, params);
            miner.checkBan(shareAccepted);
            log('debug', logSystem, "Share: %j", [{job: job, params: params, blockTemplate: {reserveOffset: blockTemplate.reserveOffset, blob: blockTemplate.buffer.toString('hex')}}]);

            if (shareTrustEnabled){
                if (shareAccepted){
                    miner.trust.probability -= shareTrustStepFloat;
                    if (miner.trust.probability < shareTrustMinFloat)
                        miner.trust.probability = shareTrustMinFloat;
                    miner.trust.penalty--;
                    miner.trust.threshold--;
                }
                else{
                    log('warn', logSystem, 'Share trust broken by %s@%s', [miner.login, miner.ip]);
                    miner.trust.probability = 1;
                    miner.trust.penalty = config.poolServer.shareTrust.penalty;
                }
            }

            if (!shareAccepted){
                sendReply('Low difficulty share');
                return;
            }

            var now = Date.now() / 1000 | 0;
            var shareTimeDiff = now - miner.lastShareTime;

            if (miner.validShares > 1) {
                log('debug', logSystem, 'Miner %s: share took %d secs, valid shares: %d', [miner.remote.addr, shareTimeDiff, miner.validShares]);
            }

            miner.shareTimeRing.append(shareTimeDiff);
            miner.lastShareTime = now;

            sendReply(null, {status: 'OK'});
            break;
        case 'keepalived' :
            miner.heartbeat()
            sendReply(null, { status:'KEEPALIVED'
            });
            break;
        default:
            sendReply("invalid method");
            var minerText = miner ? (' ' + miner.login + '@' + miner.ip) : '';
            log('warn', logSystem, 'Invalid method: %s (%j) from %s', [method, params, minerText]);
            break;
    }
}

var httpResponse = ' 200 OK\nContent-Type: text/plain\nContent-Length: 20\n\nmining server online';

function startPoolServerTcp(callback){
    async.each(config.poolServer.ports, function(portData, cback){
        var handleMessage = function(socket, jsonData, pushMessage){
            if (!jsonData.id) {
                log('warn', logSystem, 'Miner RPC request missing RPC id');
                return;
            }
            else if (!jsonData.method) {
                log('warn', logSystem, 'Miner RPC request missing RPC method');
                return;
            }
            else if (!jsonData.params) {
                log('warn', logSystem, 'Miner RPC request missing RPC params');
                return;
            }

            log('debug', logSystem, 'Received %j from %s', [jsonData, socket.remote.addr]);

            var sendReply = function(error, result){
                if(!socket.writable) return;
                var sendData = JSON.stringify({
                    id: jsonData.id,
                    jsonrpc: "2.0",
                    error: error ? {code: -1, message: error} : null,
                    result: result
                });
                socket.write(sendData + "\n");
                log('debug', logSystem, 'Sending %s to %s', [sendData, socket.remote.addr]);
            };

            handleMinerMethod(jsonData.method, jsonData.params, socket.remote, portData, sendReply, pushMessage);
        };

        var socketResponder = function(socket){
            socket.setKeepAlive(true);
            socket.setEncoding('utf8');

            var dataBuffer = '';

            var pushMessage = function(method, params){
                if(!socket.writable) return;
                var sendData = JSON.stringify({
                    jsonrpc: "2.0",
                    method: method,
                    params: params
                }) + "\n";
                socket.write(sendData);
            };

            var getRemote = function(socket) {
                var ip = socket.remoteAddress.replace(/^.*:/, '');
                return {
                    ip: ip,
                    port: socket.remotePort,
                    addr: ip + ':' + socket.remotePort
                };
            };

            socket.on('data', function(d){
                if (!socket.remote) socket.remote = getRemote(socket);
                dataBuffer += d;
                if (Buffer.byteLength(dataBuffer, 'utf8') > 10240){ //10KB
                    dataBuffer = null;
                    log('warn', logSystem, 'Socket flooding detected and prevented from %s', [socket.remoteAddress]);
                    socket.destroy();
                    return;
                }
                if (dataBuffer.indexOf('\n') !== -1){
                    var messages = dataBuffer.split('\n');
                    var incomplete = dataBuffer.slice(-1) === '\n' ? '' : messages.pop();
                    for (var i = 0; i < messages.length; i++){
                        var message = messages[i];
                        if (message.trim() === '') continue;
                        var jsonData;
                        try{
                            jsonData = JSON.parse(message);
                        }
                        catch(e){
                            if (message.indexOf('GET /') === 0) {
                                if (message.indexOf('HTTP/1.1') !== -1) {
                                    socket.end('HTTP/1.1' + httpResponse);
                                    break;
                                }
                                else if (message.indexOf('HTTP/1.0') !== -1) {
                                    socket.end('HTTP/1.0' + httpResponse);
                                    break;
                                }
                            }

                            log('warn', logSystem, 'Malformed message from %s: %s', [socket.remoteAddress, message]);
                            socket.destroy();

                            break;
                        }
                        handleMessage(socket, jsonData, pushMessage);
                    }
                    dataBuffer = incomplete;
                }
            }).on('error', function(err){
                if (err.code !== 'ECONNRESET')
                    log('warn', logSystem, 'Socket error from %s %j', [socket.remote.addr, err]);
            }).on('close', function(){
                if (socket.remote) {
                    log('warn', logSystem, 'Miner disconnected %s', [socket.remote.addr]);
                    delete connectedMiners[socket.remote.addr];
                }
                pushMessage = function(){};
            });

        };

        if(portData.type === 'SSL') {
          var options = {
            key: fs.readFileSync(config.poolServer.sslKey),
            cert: fs.readFileSync(config.poolServer.sslCert)
          };
          tls.createServer(options, socketResponder).listen(portData.port, function (error, result) {
            if (error) {
              log('error', logSystem, 'SSL Could not start server listening on port %d, error: $j', [portData.port, error]);
              cback(true);
              return;
            }
            log('info', logSystem, 'SSL Started server listening on port %d', [portData.port]);
            cback();
          });
        }
        else {
          net.createServer(socketResponder).listen(portData.port, function (error, result) {
            if (error) {
              log('error', logSystem, 'Could not start server listening on port %d, error: $j', [portData.port, error]);
              cback(true);
              return;
            }
          log('info', logSystem, 'Started server listening on port %d', [portData.port]);
          cback();
        });
      }
    }, function(err){
        if (err)
            callback(false);
        else
            callback(true);
    });
}
