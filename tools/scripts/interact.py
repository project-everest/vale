# Script for running F* in interactive mode
# Can optionally run Vale command before running F*
# Run with -h to see options
# Requires Python version >= 3.6

# Example:
#   python interact.py -f obj/MyFile.fst.checked.cmd
# Example:
#   python interact.py --fstar-args fstar.exe obj/MyFile.fst
# Example:
#   python interact.py -v obj/MyFile.fst.cmd -f obj/MyFile.fst.checked.cmd

# Notes:
# - If you're checking a file and an earlier part of the same file changes, this script will detect
#   the change and lax-check the change automatically
# - If you're checking a file and another file changes, you need to reset (r) to see the changes
#   - This includes when you're checking an fst file and the corresponding fsti file changes
#     - A change to a {:public} Vale procedure's spec causes the fsti file to change
#       (a change to a non-public Vale procedure's spec does not change the fsti file,
#       and does not need a reset)
# - We recommend running with the commandline tool rlwrap, e.g.,
#       python interact.py -f obj/MyFile.fst.checked.cmd
#   which will give you a readline-interface.  For example, it will give you arrow-based command history.

import sys
import argparse
import subprocess
import shlex
import json
import time
import typing
import os

# F* and Vale commands can either be placed directly in the python script command line, or read from files:
def add_cmd(argv, short, long, args, name, dest, req):
    if '--fstar-args' in argv:
        i = argv.index('--fstar-args')
        cmd_fstar = argv[(i + 1) : ]
        argv = argv[ : i]
        return cmd_fstar
    else:
        argparser.add_argument(short, long, action = 'store', dest = dest, required = req,
            help = f'specify file that contains command to run {name} (alternative: use {args} to specify {name} command directly)')
        return None

argv = sys.argv[1 : ]
helper_text  = "We recommend running this script using the commandline tool 'rlwrap', "
helper_text += "which will give you a readline-interface.  "
helper_text += "For example, it will give you arrow-based command history."
argparser = argparse.ArgumentParser(description=helper_text)
cmd_fstar = add_cmd(argv, '-f', '--fstar-cmd', '--fstar-args', 'F*', 'cmd_file_fstar', False)
cmd_vale = add_cmd(argv, '-v', '--vale-cmd', '--vale-args', 'Vale', 'cmd_file_vale', False)
argparser.add_argument('-a', '--auto', action = 'store', required=False,
    help='Try to automatically find cmd files given a module name')
argparser.add_argument('--fstar-file', action = 'store', dest = 'file_fstar',
    help = 'specify path of F* file (by default, the first .fst or .fsti file from the F* command is chosen)')
argparser.add_argument('--vale-file', action = 'store', dest = 'file_vale',
    help = 'specify path of Vale file (by default, the first -in argument from the Vale command is chosen)')
args = argparser.parse_args(argv)

def get_cmd(cmd, arg):
    if arg != None:
        with open(arg) as f:
            cmd = f.read()
            if '&&' in cmd:
                cmd = cmd[0 : cmd.index('&&')] # strip any trailing && ... from command
    return cmd

if not args.auto is None:
    cmd_fstar = get_cmd(cmd_fstar, 'obj/%s.fst.checked.cmd' % args.auto)
    cmd_vale = get_cmd(cmd_vale, 'obj/%s.fst.cmd' % args.auto)
else:
    cmd_fstar = get_cmd(cmd_fstar, args.cmd_file_fstar)
    cmd_vale = get_cmd(cmd_vale, args.cmd_file_vale)
cmd_fstar_ide = shlex.split(cmd_fstar) + ['--ide']

file_fstar = args.file_fstar
if file_fstar == None:
    l = [x for x in cmd_fstar.split() if x.endswith('.fst') or x.endswith('.fsti')]
    if len(l) == 0:
        print(f'could not find .fst or .fsti file in following command: {cmd_fstar}')
        exit()
    file_fstar = l[0]

file_vale = args.file_vale
if cmd_vale != None and file_vale == None:
    cmd_vale_split = shlex.split(cmd_vale)
    file_vale = cmd_vale_split[cmd_vale_split.index('-in') + 1]
file_vale_mod_time = None

try:
    pipe = subprocess.Popen(cmd_fstar_ide, stdin = subprocess.PIPE, stdout = subprocess.PIPE, stderr = subprocess.STDOUT)
except subprocess.CalledProcessError as e:
    print(f'F* error: {e.output}')
    exit()

class Block(typing.NamedTuple):
    name:str # string indicates name of named block
    lines:list # lines in the block (list of strings)
    line_number:int

class QueryError(Exception):
    pass

class ValeError(Exception):
    pass

# read file, parse into blocks, return blocks
def read_file():
    global file_vale_mod_time
    if cmd_vale != None:
        m = os.path.getmtime(file_vale)
        if m != file_vale_mod_time:
            file_vale_mod_time = m
            try:
                t = time.time()
                print(f'running Vale', end = '', flush = True)
                subprocess.check_output(cmd_vale_split, stderr = subprocess.STDOUT)
            except subprocess.CalledProcessError as e:
                file_vale_mod_time = None
                raise ValeError(e.output.decode('ascii'))
            finally:
                print(f' // {time.time() - t} seconds')
    print(f'reading from file {file_fstar}')
    with open(file_fstar) as f:
        lines = f.read().splitlines()
    blocks = []
    current = []
    name = '0'
    line_number = 0
    block_line_number = 1
    for line in lines:
        line_number = line_number + 1
        tokens = line.split()
        if len(tokens) >= 1 and tokens[0] == '//--':
            if len(current) > 0:
                blocks.append(Block(name, current, block_line_number))
            name = tokens[1] if len(tokens) >= 2 else str(len(blocks))
            current = []
            block_line_number = line_number + 1
        else:
            current.append(line)
    if len(current) > 0:
        blocks.append(Block(name, current, block_line_number))
    return blocks

def list_blocks(blocks):
    print('Found these blocks:')
    for block in blocks:
        print(f'  {block.name}')

query_id = 0
encoding = 'utf-8'

def send_query(q, args):
    global query_id
    global pipe
    query_id = query_id + 1
    query = {'query-id' : str(query_id), 'query' : q, 'args' : args}
    pipe.stdin.write((json.dumps(query) + '\n').encode(encoding))
    pipe.stdin.flush()

def recv_response():
    global pipe
    while True:
        response = json.loads(pipe.stdout.readline().decode(encoding))
        if response['kind'] == 'response':
            if response['status'] == 'success':
                break
            else:
                raise QueryError(response['response'])

def pop_block(pushed_blocks):
    pushed_blocks.pop()
    send_query('pop', {})
    recv_response()

def push_block(pushed_blocks, block, kind):
    args = {'kind' : kind, 'code' : '\n'.join(block.lines), 'line' : block.line_number, 'column' : 0}
    print(f'checking ({kind}) block {block.name}', end = '', flush = True)
    t = time.time()
    send_query('push', args)
    try:
        recv_response()
    finally:
        print(f' // {time.time() - t} seconds')
    pushed_blocks.append(block)

def check_block(pushed_blocks, blocks, name):
    # keep old blocks that match new blocks (up to named block):
    i = 0
    while i < len(pushed_blocks) and i < len(blocks):
        if blocks[i].name == name:
            break
        if blocks[i] != pushed_blocks[i]:
            break
        i = i + 1
    # pop all but matching blocks:
    while len(pushed_blocks) > i:
        pop_block(pushed_blocks)
    # push blocks until we reach named block:
    while i < len(blocks):
        block = blocks[i]
        if block.name == name:
            push_block(pushed_blocks, block, 'full')
            print('success')
            return
        else:
            push_block(pushed_blocks, block, 'lax')
        i = i + 1
    # if we reach here, name didn't exist:
    print(f'did not find block named {name}')

blocks = []
pushed_blocks = []

try:
    blocks = read_file()
except ValeError as e:
    print(e)
list_blocks(blocks)

last = None
while True:
    print()
    print('type v <blockname> to verify a block, r to reset, l to list blocks, q to quit, enter to repeat last')
    inp = sys.stdin.readline().split()
    try:
        if len(inp) == 0 and last != None:
            inp = last
            print(' '.join(inp))
        elif len(inp) != 0:
            last = inp
        if len(inp) == 1 and inp[0] == 'q':
            break
        elif len(inp) == 1 and inp[0] == 'l':
            blocks = read_file()
            list_blocks(blocks)
        elif len(inp) == 1 and inp[0] == 'r':
            while len(pushed_blocks) > 0:
                pop_block(pushed_blocks)
        elif len(inp) == 2 and inp[0] == 'v':
            blocks = read_file()
            check_block(pushed_blocks, blocks, inp[1])
        else:
            print(f'command "{" ".join(inp)}" not found')
    except ValeError as e:
        print(e)
    except QueryError as e:
        e = e.args[0][0]
        print(e['level'])
        print(f"  {e['message']}")
        for r in e['ranges']:
            print(f"  range: {r}")

