#!/usr/bin/env bash

set -exo pipefail

find src archive counterexamples -name '*.lean' | xargs ./scripts/cleanup-braces.py
