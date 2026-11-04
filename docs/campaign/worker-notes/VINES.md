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

The actual-atom group partition/sizes/index, lattice gap-norm conservation,
and connectivity of all drafted vine-like classes are checked. A new actual
half-edge recurrence proves matched rung membership for arbitrary full-rung
sequences of length >=3, and constant membership for connected blocks larger
than a double bond. The 24-result axiom audit passes with standard axioms only.
The final `subsetvc` classification/removal theorem remains in progress.

The pinned realization now supplies actual full-rung sequences for every
expanded slot, with exact labels and no extra incidence hypotheses. This
proves constant membership/no fresh joints for connected blocks larger than
a double bond on every slot of length >=3. The two-cut direction fact is
also derived from actual block degree balance. The expanded interface and
50-result standard-axiom audit pass; subsetvc remains open, including the
short-slot and simultaneous-removal arguments. See the scratch HANDOFF for
exact checked modules and commands.
