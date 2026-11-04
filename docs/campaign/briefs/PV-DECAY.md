# Packet PV-DECAY (B2 freeze, REQUIRED item F-5): the principal value for decaying kernels

Read `COMMON.md` first.

## Goal

Prove `tendsto_pvResonantIntegral_of_decay`, **exactly as stated** in
`docs/campaign/orch/audits/WaveB2-handoff.md`, section "F-5 (REQUIRED): the missing characterization lemma, for a
prover". The statement is reproduced verbatim there, with its opens and namespace. It has been elaborated against
the current build, and its conclusion is checked by `rfl` to equal that of `tendsto_pvResonantIntegral`.

It is `tendsto_pvResonantIntegral` with the compact-support hypotheses replaced by the `DeltaKernel` decay of the
kernel and of its gradient. The handoff gives a two-step proof sketch:

1. **Per slice:** dominated convergence once `pvQuotient (sliceInt F ℓ)` is integrable.
2. **Outer integral:** dominated convergence in `ℓ`.

The key change is replacing `hasCompactSupport_sliceInt` in the landed 1-D truncation limit `tendsto_pvTruncation`
with integrability of `S` together with differentiability of `S` at 0.

This is the only open REQUIRED item before the Wave B2 freeze. The independent audit and its re-check are in
`docs/campaign/orch/audits/WaveB2-independent-audit.md`.

## Where

Most of the work is statement-independent analysis about the landed Resonant objects (`energyInvIntegral`,
`energyInvSliceLimit`, `pvQuotient`, `sliceInt`, `tendsto_pvTruncation`, `energyPrincipalValue_spec`).

- **Foundations part:** put it on your branch under `WaveTurbulence/Foundations/Resonant/PVDecay*.lean`, namespace
  `WaveTurbulence.Resonant`. Search for these names first and reuse them.
- **The B2-level lemma:** prove it in scratch, in `/home/scott/wt-scratch/pv-decay/`, against the current B2 build,
  importing the B2 modules. Do not edit `/home/scott/wt-scratch/waveb2`.

For how to build against `/home/scott/wt-scratch/waveb2/build` and `/home/scott/wt-scratch/waveb/build`, see the
handoff's "Checks" section: `LEAN_PATH` = dev `.lake/build/lib/lean` : `waveb/build` : `waveb2/build`.

## Worktree

`/home/scott/WaveTurbulence-worktrees/an-sob`. Merge main first.

## Done

- No sorry; standard axioms only.
- A `HANDOFF.md` in the scratch directory.
- Report `READY pv-decay`.

After that, G7 MOLEPROP4: DH23 Lemmas `ylem1`/`ylem2` and Prop 10.4. It consumes wt-nt's APPB-OPS and wt-gausssum's
VINES, which should be further along by then.
