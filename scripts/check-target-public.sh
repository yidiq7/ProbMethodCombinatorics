#!/bin/sh
# Pre-publication check: a task target must be public, or comparator aborts.
# Usage: sh precheck.sh <target_file> <fully.qualified.Decl>
set -u
F="$1"; D="$2"; SHORT="${D##*.}"
if ! grep -qE "^(private +)?(theorem|lemma|def|abbrev) +${SHORT}\b" "$F"; then
  echo "NOT FOUND: $SHORT in $F"; exit 2
fi
if grep -qE "^private +(theorem|lemma|def|abbrev) +${SHORT}\b" "$F"; then
  echo "REFUSE: $SHORT is private in $F"
  echo "  comparator hands lean4export the unmangled name, it aborts (exit 2), and the PR cannot merge."
  echo "  Promote it to public and commit that BEFORE publishing the task."
  exit 1
fi
echo "OK: $SHORT is public in $F"
