#!/usr/bin/env python3
import argparse
import sys
import thiele_verify


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        thiele_verify.verify_dir(args.directory)
    except Exception as e:
        print(f"verification failed: {e}")
        return 1
    print("verification succeeded")
    return 0


def cmd_refinement(args: argparse.Namespace) -> int:
    try:
        mu_coarse = thiele_verify.verify_dir(args.coarse)
        mu_refined = thiele_verify.verify_dir(args.refined)
    except Exception as e:
        print(f"verification failed: {e}")
        return 1
    if mu_refined >= mu_coarse:
        print("μ monotonicity holds")
        return 0
    print("μ monotonicity violated")
    return 1


p = argparse.ArgumentParser(description="Challenge harness for Thiele receipts")
sub = p.add_subparsers(dest="cmd", required=True)

p_ver = sub.add_parser("verify", help="verify receipt directory")
p_ver.add_argument("directory")
p_ver.set_defaults(func=cmd_verify)

p_ref = sub.add_parser("refinement", help="compare μ under refinement")
p_ref.add_argument("coarse")
p_ref.add_argument("refined")
p_ref.set_defaults(func=cmd_refinement)

args = p.parse_args()
code = args.func(args)
sys.exit(code)