# Batch-3 main verification

Verified 2026-11-06 00:07 UTC after landing `f89596c` (source commit `457893b`).

`scripts/land_check.sh` on canonical main returned exit 0:

```text
duplicate scan: OK
sorry scan: OK
Build completed successfully (14412 jobs).
FROZEN-ANCHOR GUARD OK
check_lean_modules: PASS (5366 Lean files, 0 comparator configurations)
LAND CHECK OK
```

`nice -n 5 lake env lean /home/scott/wt-scratch/port-b3a/SourceProvidersAudit.lean` on main returned exit 0. Mathlib source status and Lake pins were unchanged. Exact exported axiom results:

```text
'WaveTurbulence.Spine.leafwise_regular_asymptotics' depends on axioms: [propext, Classical.choice, Quot.sound]
'WaveTurbulence.Spine.coherent_approximation' depends on axioms: [propext, Classical.choice, Quot.sound]
'WaveTurbulence.Spine.leafwise_coherent_approximation' depends on axioms: [propext, Classical.choice, Quot.sound]
'WaveTurbulence.Spine.leafwise_incoherent_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'WaveTurbulence.Spine.ladder_fourier' depends on axioms: [propext, Classical.choice, Quot.sound]
'WaveTurbulence.Spine.ladder_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'WaveTurbulence.Spine.coarse_spliced' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No frozen bytes changed or theorem was sealed. See PORT-B3-independent.md and PORT-B3-provenance.json for the independent mapping review and source/target hashes.

DRAFT_ANCHORS: 10 (the ten paths enumerated in HQ README)
UNREGISTERED_SORRIES: 0
DRAFT_IMPORT_VIOLATIONS: 0
SEALED_THIS_TURN: 0
