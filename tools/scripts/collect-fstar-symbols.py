#!/usr/bin/python

import argparse
import os, os.path
import sys
import subprocess
import json
import fnmatch

def find_fstar_files(directory):
    matches = []
    extensions = ["fsti", "fst"]

    # Based on: https://stackoverflow.com/a/2186565
    for root, dirnames, filenames in os.walk(directory):
        for ext in extensions:
            for filename in fnmatch.filter(filenames, '*.' + ext):
                matches.append(os.path.join(root, filename))
    return matches

def generate_export_symbols_file(f, outdir):
  fd = open(f, 'r')
  fileName = os.path.basename(f)
  moduleName, extension = os.path.splitext(fileName)
  fstar = os.path.join(os.environ['FSTAR_HOME'], "bin", "fstar.exe");
  proc = subprocess.Popen([fstar, '--ide', os.environ['FSTAR_INCLUDES'], f], stdin = subprocess.PIPE, stdout = subprocess.PIPE)
  output = json.loads(proc.stdout.readline())
  print output
  if output['kind'] == 'protocol-info':
    command1 = "{\"query-id\":\"4\",\"query\":\"exported\",\"args\":{\"name\":\"" + moduleName + "\" }}"
    print command1
    proc.stdin.write('%s\n' % command1)
    output = json.loads(proc.communicate()[0])
    print output
    if output['status'] == 'success':
		   outputfile = os.path.join(outdir, f + ".exported");
       od = open(outputfile, "w+")
       s = str(output['response'])
       od.write(s)
       od.close()

def generate_export_dir(d, outdir):
    files = find_fstar_files(d, outdir)
    for f in files:
        generate_export_symbols_file(f)

def generate_export(directories, outdir):
    for d in directories:
        generate_export_dir(d, outdir)
    
def main():
    parser = argparse.ArgumentParser(description= 'Compute exported symbols of F* files')
    parser.add_argument('--dir', action='append', required=true, help='generate exported symbols for files in this folder and its subfolders')
    parser.add_argument('--outdir', action='store', required=true, help='directory where output files are')
    
    args = parser.parse_args()
    if (not args.dir is None) and (not args.outdir is None):
        generate_export(args.dir, args.outdir)

    print("Invalid or insufficient arguments supplied.  Try running with -h")


if (__name__=="__main__"):
  main()

