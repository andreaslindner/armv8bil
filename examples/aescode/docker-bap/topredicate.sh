#!/bin/sh
ssh -X -p32768 root@localhost /root/bap-bap-0.7/utils/topredicate -il /tmp/example.il -wp -solver stp -stp-out /tmp/res.stp -validity
