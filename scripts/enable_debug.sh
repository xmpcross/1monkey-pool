#!/bin/bash

DEBUG_COLORS=true DEBUG=*,-axm:profiling pm2 reload proxy --update-env
