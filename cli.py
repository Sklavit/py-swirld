# coding=utf-8


import logging
logging.getLogger().setLevel(logging.DEBUG)

# bokeh serve --show viz.py --args <number of nodes>
# import atexit
#
# import sys
#
argv = ['bokeh', 'serve', '--show', 'myapp.py']
argv = ['bokeh', 'serve', '--show', 'viz.py', '--args', '3']
#
# import subprocess
# process = subprocess.Popen(args)
#
# def cleanup_process():
#     try:
#         process.terminate()
#     except OSError:
#         pass
# atexit.register(cleanup_process)
import argparse


from bokeh.command.subcommands.serve import Serve
from bokeh.command.util import die

parser = argparse.ArgumentParser(prog=argv[0])

subs = parser.add_subparsers(help="Sub-commands")

cls = Serve
subparser = subs.add_parser(cls.name, help=cls.help)
subcommand = cls(parser=subparser)
subparser.set_defaults(invoke=subcommand.invoke)

args = parser.parse_args(argv[1:])
args.invoke(args)
