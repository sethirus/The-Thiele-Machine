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
