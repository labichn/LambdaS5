#!/bin/bash

# Take two snapshots: one right after s5 initialization, and one right after
# ses initialization. Save them in init.heap and ses.heap.
# Regenerate the snapshots if (i) they don't exist, or (ii) they are out of date

if [ ! -f minit.heap    -o ../obj/s5.d.byte -nt minit.heap ]; then

echo "save_machine_snaps.sh: Rebuilding heap snapshots"

echo "___takeS5Snapshot()" | ./s5 stdin -eval-machine -save minit.heap
(cat ses/es-lab-tests/initSESPlus.js; echo "___takeS5Snapshot();") | ./s5 stdin -eval-machine -save mses.heap
(cat ses/es-lab-tests/initSESPlus.js; echo "cajaVM.eval(\"___takeS5Snapshot();\");") | ./s5 stdin -eval-machine -save mseseval.heap

fi
