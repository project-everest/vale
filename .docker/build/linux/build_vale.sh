#!/usr/bin/env bash

#set -x

target=$1
out_file=$2
threads=$3

function export_home() {
    if command -v cygpath >/dev/null 2>&1; then
        export $1_HOME=$(cygpath -m "$2")
    else
        export $1_HOME="$2"
    fi
}

# By default, kremlin master works against F* stable. Can also be overridden.
function fetch_kremlin() {
  if [ ! -d kremlin ]; then
    git clone https://github.com/FStarLang/kremlin kremlin
  fi
  cd kremlin
  git fetch origin
  local ref=$( if [ -f ../.kremlin_version ]; then cat ../.kremlin_version | tr -d '\r\n'; else echo origin/master; fi )
  echo Switching to KreMLin $ref
  git reset --hard $ref
  cd ..
  export_home KREMLIN "$(pwd)/kremlin"
}

function exec_build () {
    cd vale

    export_home FSTAR "$(pwd)/../"
    result_file="../result.txt"
    local status_file="../status.txt"
    echo -n false > $status_file

    if ! [ -d tools/Vale ]; then
        echo "I don't seem to be in the right directory, bailing"
        echo Failure > $result_file
        return
    fi

    fetch_kremlin

    # Set up build environment
    nuget restore tools/Vale/src/packages.config -PackagesDirectory tools/FsLexYacc

    if [[ $target == "vale-ci" ]]; then
        echo target -> vale-ci
        scons -j $threads --NOVERIFY && echo -n true > $status_file;
    else
        echo "Invalid target"
        echo Failure > $result_file
        return
    fi

    if [[ $(cat $status_file) != "true" ]]; then
        echo "Build failed"
        echo Failure > $result_file
    else
        echo "Build succeeded"
        echo Success > $result_file
    fi

    cd ..
}

# Some environment variables we want
export OCAMLRUNPARAM=b
export OTHERFLAGS="--print_z3_statistics --use_hints --query_stats"
export MAKEFLAGS="$MAKEFLAGS -Otarget"

exec_build
