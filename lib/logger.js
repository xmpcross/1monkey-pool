var fs = require('fs');
var util = require('util');

var dateFormat = require('dateformat');
var clc = require('cli-color');

var severityMap = {
    'debug': clc.cyan,
    'info': clc.green,
    'warn': clc.yellow,
    'error': clc.red,
    'block': clc.magentaBright
};

var severityLevels = ['debug', 'info', 'warn', 'error', 'block'];


var logDir = config.logging.files.directory;
var singleFile = config.logging.files.singleFile || false;

if (!fs.existsSync(logDir)){
    try {
        fs.mkdirSync(logDir);
    }
    catch(e){
        throw e;
    }
}

var pendingWrites = {};

setInterval(function(){
    for (var fileName in pendingWrites){
        var data = pendingWrites[fileName];
        fs.appendFile(fileName, data, (err) => {if(err) throw err;});
        delete pendingWrites[fileName];
    }
}, config.logging.files.flushInterval * 1000);

global.log = function(severity, system, text, data){

    var logConsole = severityLevels.indexOf(severity) >= severityLevels.indexOf(config.logging.console.level);
    var logFiles = severityLevels.indexOf(severity) >= severityLevels.indexOf(config.logging.files.level);

    if (!logConsole && !logFiles) return;

    var time = dateFormat(new Date(), 'yyyy-mm-dd HH:MM:ss');
    var formattedMessage = text;

    if (data) {
        data.unshift(text);
        formattedMessage = util.format.apply(null, data);
    }

    if (logConsole){
        if (config.logging.console.colors)
            console.log(severityMap[severity](time) + clc.white.bold(' [' + system + '] ') + formattedMessage);
        else
            console.log(time + ' [' + system + '] ' + formattedMessage);
    }


    if (logFiles) {
        var fileName = logDir + '/' + system + (singleFile ? '' : '_' + severity) + '.log';
        var fileLine = time + ' ' + formattedMessage + '\n';
        pendingWrites[fileName] = (pendingWrites[fileName] || '') + fileLine;
    }
};
