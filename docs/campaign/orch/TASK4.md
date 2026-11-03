# wt-orch Task 4 — independent topology review of the blueprint; then Wave B draft audits

First `git merge main` in your worktree (your Task 3 is landed; blueprint is in `docs/blueprint/`).

## 4a. Topology review of `docs/blueprint/GRAPH.md` (refute-first)

The blueprint was written by one agent from the four maps; it has not been independently reviewed. Review the
**topology**, not the proofs: for the root `T.main` and the induction gates (`T.propansatz`, `T.layergarden`,
`T.fixedpoint`), and for a sample of at least 30 other nodes chosen across §A.5–§A.13 (include every node on the
critical path §D.1), check against the TeX:
- omissions (a substantive step or external input used in the source but absent from the graph);
- wrong or reversed edges, cycles, nodes whose listed dependencies would not suffice;
- hidden external inputs (results cited as "standard", "as in DH21", "the same proof" without a node);
- false parallelism (packets in §E marked independent that share a definition or a lemma);
- route decisions §B that conjoin alternatives instead of choosing one;
- whether WAVE-B's tier-B1 statements (§4.1–§4.10) are the right gates (would a different cut be safer?).
Write `docs/campaign/orch/audits/GRAPH-topology.md`: verdict, a table of issues (node, problem, evidence, fix), and a
list of missing nodes with proposed rows. Commit on `w/orch`.

Also reconcile `docs/blueprint/WAVE-B.md` §3 (the blueprint agent's textual definitions of figure-only objects) with
your `figure-defs.md`: list every point where they differ, with the reading you recommend.

## 4b. Wave B draft audits (when announced)

wt-gauss-hc is drafting the exact Lean for Wave B tier B1 in untracked files under `/home/scott/wt-scratch/waveb/`
(brief: `docs/campaign/briefs/WAVEB-DRAFT.md`), in three stages. When the orchestrator tells you a stage is ready,
audit it refute-first in the Task 1 format (verdict table per declaration and binder, REQUIRED fixes with exact Lean
changes, OPTIONAL, author questions, non-vacuity probes), file `docs/campaign/orch/audits/WaveB-stage<k>.md`.

When 4a is done print `READY task4a` and wait for the stage announcements.
