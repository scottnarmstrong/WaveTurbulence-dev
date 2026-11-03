# wt-orch Task 7 — seal plans for the frozen `wkelwp` and `main`

`git merge main` first (your Task 6 audits will be landed by the running integration round).

For each of the two frozen theorems (`WaveTurbulence/Frozen/Theorems/{Wkelwp,Main}.lean`), write a seal plan:
1. Split the statement into its conjuncts / logical pieces (for `main`: MeasurableSet F; the probability bound; the
   expectation estimate at all t ∈ [0,T]; the selection device; the constant hierarchy θ, L₀).
2. For each piece, list the landed Lean results that discharge it (exact names, modules, and whether their statements
   match the needed form exactly — binders, carriers, the `ContDiff` pitfall F44), the still-unfrozen Wave B statements
   it will consume (propansatz, nlsAkBridge, …; drafts in /home/scott/wt-scratch/waveb-snap-2/), and the glue lemmas
   still missing (with proposed statements).
3. For `wkelwp`: conjuncts 1–2 and uniqueness are claimed by `WaveTurbulence.WKE.wkelwp_conj12` (+ `tauMax`) and
   `WKE.isWKESolution_unique`; conjunct 3 by packet WKE-L2S (in progress). Check that their statements compose to the
   frozen type exactly (draft the provider assembly `WaveTurbulence.Provider.wkelwp` as an untracked scratch file that
   elaborates with only conjunct 3 left as a clearly named hypothesis-free `sorry`-free gap marker — i.e. state what is
   missing, do not add it as a hypothesis).
Write `docs/campaign/orch/SEAL-PLAN.md`, commit on w/orch, print `READY task7`.
