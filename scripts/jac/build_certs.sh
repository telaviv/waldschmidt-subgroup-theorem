#!/bin/bash
# Build the raw kernel-check files two at a time (each needs ~3.3 GB); log timings.
cd "$(dirname "$0")/../.."
export PATH="$HOME/.elan/bin:$PATH"
LOG=scripts/jac/build_certs.log
: > $LOG
for pair in "V1 F1j0" "F1j1 V2k1" "V2k2 V2k3" "V2k4 V2k5" "V2k6 V2k7" "V2k8"; do
  start=$(date +%s)
  targets=""
  for f in $pair; do targets="$targets LSG.Jac.Cert.$f"; done
  lake build $targets 2>&1 | grep -E "Built LSG.Jac.Cert|error" >> $LOG
  echo "pair [$pair] wall $(( $(date +%s) - start )) s" >> $LOG
done
echo DONE >> $LOG
