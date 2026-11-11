#!/usr/bin/env bash
# Build every module with Lake and print the axiom audit.
# First run downloads Mathlib's prebuilt cache (several GB on disk).
set -e
cd "$(dirname "$0")"
lake exe cache get
lake build
lake env lean ExactFDiv/Audit.lean
