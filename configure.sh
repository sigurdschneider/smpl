#! /bin/bash

coq_ver=$(${COQBIN}coqc -v 2>/dev/null | sed -n -e 's/The Coq Proof Assistant, version \([^ ]*\).*$/\1/p')
case "$coq_ver" in
  8.6*)
		;;
	*)
    echo "Error: Need Coq 8.6*"
		exit 1
esac
echo "Found Coq version $coq_ver."

SOURCES=$(find theories -name \*.v -print | grep -v /\.# | sed -e 's%^\./%%g')
echo $(cat _CoqProject) src/smpl.ml4 $SOURCES  > Make
echo "Make generated."
