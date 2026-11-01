#!/bin/bash
# Build the given LSG.Jac.Cert.* modules two at a time; log wall times.
cd "$(dirname "$0")/../.."
export PATH="$HOME/.elan/bin:$PATH"
LOG=${LOG:-scripts/jac/build_e1.log}
: > $LOG
mods=("$@")
i=0
while [ $i -lt ${#mods[@]} ]; do
  a=${mods[$i]}; b=${mods[$((i+1))]:-}
  start=$(date +%s)
  if [ -n "$b" ]; then lake build LSG.Jac.Cert.$a LSG.Jac.Cert.$b 2>&1 | grep -E "Built LSG.Jac.Cert|error" >> $LOG
  else lake build LSG.Jac.Cert.$a 2>&1 | grep -E "Built LSG.Jac.Cert|error" >> $LOG; fi
  echo "[$a $b] wall $(( $(date +%s) - start )) s" >> $LOG
  i=$((i+2))
done
echo DONE >> $LOG
