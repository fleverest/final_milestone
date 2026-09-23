#!/bin/sh
set -e
git config --global gpg.format ssh
git config --global commit.gpgsign true

key=$(ssh-add -L 2>/dev/null | grep signing | head -n1 || true)
if [ -n "$key" ]; then
    git config --global user.signingkey "$key"
    git config --global gpg.format ssh
    git config --global commit.gpgsign true
else
    echo "warning: no signing key in agent; user.signingkey not set" >&2
fi
