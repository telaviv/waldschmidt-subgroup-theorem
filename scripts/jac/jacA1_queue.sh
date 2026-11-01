#!/bin/bash
# Checkpoint-4 build queue: P2 certificates, then the E1 certificates, two at a time.
cd "$(dirname "$0")/../.."
LOG=scripts/jac/build_p2.log bash scripts/jac/build_e1.sh P2_0 P2_1 P2_2 P2_3 P2_4 P2_5 P2_6 P2_7 P2_8
LOG=scripts/jac/build_q4.log bash scripts/jac/build_e1.sh \
  E1_E40_0 E1_E40_1 E1_F4Y_0 E1_F4Y_1 E1_E04_0 E1_F4X_0 E1_E04_1 E1_F4X_1 E1_E44_0 E1_E44_1
