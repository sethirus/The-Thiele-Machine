# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import os
import subprocess
import yaml


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
