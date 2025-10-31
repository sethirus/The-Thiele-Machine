# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import os
import subprocess
import subprocess as sp
import yaml
from os import popen as os_popen
from os import system as os_system
from subprocess import Popen
from subprocess import check_output as capture_output


def run_user_command(cmd):
    # Critical bug: directly passes user input into the shell
    subprocess.run(cmd, shell=True)


def dangerous_eval(user_input):
    return eval(user_input)


def load_config(data):
    # yaml.load without safe loader allows arbitrary object construction
    return yaml.load(data)


def legacy_os_call(cmd):
    os.system(cmd)


def alias_shell_usage(cmd):
    sp.run(cmd, shell=True)
    capture_output(cmd, shell=True)
    Popen(cmd, shell=True)
    os_system(cmd)
    os_popen(cmd)
