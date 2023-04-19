#!/usr/bin/env bash
# usage: transform.sh [--stdout] [--stderr] transform1 transform2 ... -- [goblint args] file.c
# runs goblint with the given transformations active and outputs the transformed file to stdout

set -eu -o pipefail

function main() {
  local -a trans_args=()
  local stdout=0 stderr=0 output_file

  while [ $# -gt 0 ]; local arg="$1"; shift; do
    case $arg in
      --) break ;;
      --stdout) stdout=1 ;;
      --stderr) stderr=1 ;;
      *) trans_args+=( "--set" "trans.activated[+]" "$arg" ) ;;
    esac
  done

  output_file="$(mktemp ./transformed.c.XXXXXX)"

  # save stdout to $stdout0
  exec {stdout0}>&1
  [ $stdout -eq 1 ] || exec 1>/dev/null
  [ $stderr -eq 1 ] || exec 2>/dev/null

  export OCAMLRUNPARAM="${OCAMLRUNPARAM},b=0"  # turn off backtraces
  goblint "${trans_args[@]}" --set trans.output "$output_file" "$@" || result=$?

  # output the transformed file with the 'Generated by CIL v. X.X.X' header removed
  tail +4 "$output_file" 1>&$stdout0
  rm "$output_file"

  return "${result-0}"
}

main "$@"
