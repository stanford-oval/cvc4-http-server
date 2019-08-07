#!/bin/sh

set -e
set -x

srcdir=`dirname $0`/..
prefix=/usr/local
bindir=${prefix}/bin

workdir=`mktemp -t -d almond-nlp-integration-XXXXXX`
workdir=`realpath $workdir`
on_error() {
    test -n "$serverpid" && kill $serverpid
    serverpid=

    cd $oldpwd
    rm -fr $workdir
}
trap on_error ERR INT TERM

node $bindir/cvc4-http-server &
serverpid=$!

# in interactive mode, sleep forever
# the developer will run the tests by hand
# and Ctrl+C
if test "$1" = "--interactive" ; then
    sleep 84600
else
    # sleep until the process is settled
    sleep 30

    curl -H'Content-Type: application/octet-stream' -d@$srcdir/data/test1.smt 'http://127.0.0.1:8400/solve' -o answer1.txt
    diff -u answer1.txt <<<"unsat"
fi

kill $serverpid
serverpid=

cd $oldpwd
rm -fr $workdir
