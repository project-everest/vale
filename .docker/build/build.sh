#!/usr/bin/env bash

#set -x

target=$1
out_file=$2
threads=$3
branchname=$4

function export_home() {
    if command -v cygpath >/dev/null 2>&1; then
        export $1_HOME=$(cygpath -m "$2")
    else
        export $1_HOME="$2"
    fi
}

function exec_build () {

    result_file="../result.txt"
    local status_file="../status.txt"
    echo -n false > $status_file

    if ! [ -d tools/Vale ]; then
        echo "I don't seem to be in the right directory, bailing"
        echo Failure > $result_file
        return
    fi

    # Set up build environment
    nuget restore tools/Vale/src/packages.config -PackagesDirectory tools/FsLexYacc

    if [[ $target == "vale-ci" ]]; then
        echo "target -> vale-ci"
        ./run_scons.sh -j $threads --DAFNY --FSTAR --FSTAR-MY-VERSION && echo -n true > $status_file;
    elif [[ $target == "vale-nightly" ]]; then
        echo "target -> vale-nightly"
        ./run_scons.sh -j $threads --DAFNY --FSTAR --FSTAR-MY-VERSION && echo -n true > $status_file;
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
}

# Some environment variables we want
export OCAMLRUNPARAM=b
export OTHERFLAGS="--print_z3_statistics --use_hints --query_stats"
export MAKEFLAGS="$MAKEFLAGS -Otarget"

export_home FSTAR "$(pwd)/FStar"
cd vale
exec_build
cd ..
