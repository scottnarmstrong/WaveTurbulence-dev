# Packets L1+L2 PL1: TARGET Proposition 5.1 (decay for incoherent regular objects)

Read `COMMON.md` first.

## Goal

Prove TARGET Prop `proplayer1` (L953–L956), with its proof at L979–L1093, under the standing assumptions
`standing5` (L949–L951). The paragraph-level map, with every display (`incohproof1`–`incohproof28`), the terse steps
and the interpolation check, is in `~/wave-turbulence/maps/T-part1.md` L960–L1060. These are blueprint packets L1
(steps 1–2) and L2 (steps 3–4 and assembly) in `docs/blueprint/GRAPH.md` §E. This is on the critical path
(proplayer1 → Props 6.1–6.3 → vine estimates → reduction).

## Inputs already on main

| input | where |
|---|---|
| TARGET Lemma 5.2 `lemlayer1` (Poisson-dual oscillatory integral) | `Foundations/NTSP/**` (packet NT5) |
| TARGET Lemma 5.3 `lemlayer2` (lattice exponential sum, long times) | `Foundations/WeylSums/QuadExpSum2.lean`, `MinorArcSums.lean` (NT4) |
| Poisson summation, stationary phase | `Foundations/Fourier/**` (N2) |
| time-integral lemmas `timeintlem`, `timeintlem2` (DNY21 Lemma 3.1) | `Foundations/Fourier/PhaseTimeIntegralBounds.lean`, `TimeIntegral*.lean` (N3) |
| 𝔛 norms, cutoffs, Fourier-L¹ product lemma | `Foundations/Fourier/**` (N1) |
| Sobolev embedding, simplex volumes | `Foundations/Analysis/**` (N4) |

Before writing anything, survey these with `grep` and reuse them. Do not reprove them.

## Staging

1. **Analytic core first.** Work in Foundations on your branch: files `WaveTurbulence/Foundations/Incoh/*.lean`,
   namespace `WaveTurbulence.Incoh`. Prove steps 3–4 with a carrier that abstracts the couple:
   - a finite set of `n` links, each with a time box `ℬ_𝔫`;
   - an incoherence flag;
   - lattice-sum factors `𝒮_𝔫` of the form `incohproof10`;
   - the time domain `ℐ* ⊂ ∏ ℬ_𝔫`.

   The results to prove are the bounds `incohproof12`–`incohproof20` (couple case) and `incohproof22`–`incohproof28`
   (tree case, with the 𝔛^{−η} / 𝔛^{1/4} interpolation), ending in
   `‖K̃_ext‖_{𝔛^η} ≲_1 (C_0δ)^n L^{−(γ_1−100dη)g}`. Make every constant explicit in the style of the landed packets.
2. **Steps 1–2 next.**
   - The unimodular change of variables `incohproof1`–`incohproof3`.
   - The localization `incohproof4`–`incohproof8`, including the Fourier-L¹ bound of `W`.
   - `T.treelemma` (L2422) part (2).

   These need links (`T-deflink`, blueprint packet C2, not started). Until C2 exists, state the link structure you
   need as a local structure in `Incoh`, list its fields in your HANDOFF, and prove steps 1–2 from it. The C2
   packet will then build that structure from the frozen Wave B gardens.
3. **Assembly.** Prove `proplayer1` for the abstract carrier. Instantiating it with the frozen layered regular
   couples comes after the Wave B freeze and C2.

## Rules

- If a step of the source is wrong or too terse to formalize, record it in your HANDOFF with the precise reading
  you adopted. The map already flags L1060ff ("replace 𝒮_0 by a pure phase at loss L^{4d}") as terse.
- Never weaken a bound to make a proof go through without reporting it.

## Worktree

`/home/scott/WaveTurbulence-worktrees/wke-l2s`, branch `w/wke-l2s`. Merge main first. Commit as you go, since
Foundations work lands in integration rounds.

## Done

- Stage 1 done: report `READY pl1-core`, and keep going.
- Stages 2–3 done: `HANDOFF.md` in `WaveTurbulence/Foundations/Incoh/`, then report `READY pl1`.
