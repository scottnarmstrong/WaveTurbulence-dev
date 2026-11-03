# VINES scratch progress

COUNT landed; `w/count` merged main at `37c6fbb` before starting M4.
Lean work is under `/home/scott/wt-scratch/vines/`, with copied MOLE source
hashes in `COPIED-SHA256.txt`; no writes to `/home/scott/wt-scratch/mole/`.
See the scratch `HANDOFF.md` for current definitions and verification status.
M4 remains in progress; this is a checkpoint, not a completion claim.

The checked scratch interface now includes expanded atom/bond/group counts,
degree profiles, sigma, group partition, template and actual-vine connectivity,
ladder length, coherence index, and boundary conservation. The 12-result axiom
probe reports only standard axioms. `subsetvc` remains in progress.

The exhaustive block/hyper-block degree-mask checks now pass for all eight
base cores. The larger cores are split by joint pair to stay within default
budgets. Applying the tables to arbitrary rung expansions remains in progress;
this checkpoint does not claim `subsetvc`.
