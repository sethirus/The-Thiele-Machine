#!/usr/bin/env bash
# Wrapper for GPG to enforce --pinentry-mode loopback for non-interactive signing
exec gpg --pinentry-mode loopback "$@"
