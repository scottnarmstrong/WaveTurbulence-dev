# Statement audit: wt-l2s's final abstract Proposition 5.1 (TARGET `proplayer1`)

Auditor: `wt-orch`, refute-first. Date: 2026-11-04 (Task 33c). Findings only; nothing was edited.

**Scope.** `Foundations/Incoh/Proposition51.lean` and `Proposition51OneClock.lean`, landed on main in `541d4c8`. The
questions:
- is P-1 of `PL1-core.md` covered (the degenerate couple with one trivial tree)?
- is the theorem what TARGET L953–L956 asserts, for the abstract carrier?

## Verdict

**PASS. P-1 is closed.**
- **The two-root case.** `exists_proposition51` is TARGET (layerregest1) for the abstract couple and tree carrier with
  two root clocks.
- **The trivial-tree case.** `exists_proposition51_oneClock` is the same estimate for TARGET L1049's case of a couple
  with a trivial tree: one live root clock, the other time passive.
- **Coverage.** Together they cover every couple with `g ≥ 1`. Both trees trivial means order 0 and `g = 0`, which is
  excluded.
- **Axioms:** standard.
- **Note C-1** (interface; not a defect).

## 1. Inputs

**Main hashes.** `Proposition51` `42a6daba60b6…`, `Proposition51OneClock` `a591a640f0ef…`, `OneClockVertexDecay`
`a2de538ea0db…`, `VertexClockPropositionRate` `693c15e67c72…`.

**Earlier audit.** `PL1-core.md` covered the analytic core at `fb174c5`: PASS, with P-1 required. The present files
assemble the final rates on it.

## 2. Against TARGET L944–L956

**TARGET.**
- L951 fixes "a layered regular couple `𝒬` and a layered regular tree `𝒯` of order `2n` and incoherency index
  `0 ≤ g ≤ n`", with inputs `F_r = φ(δr) + R_r` and `‖R_r‖_{𝔖^{40d,40d}}` bounded.
- The boxes are `ℬ = [q,q+1]×[q',q'+1]`, and `∩ {t > s}` for trees.
- (layerregest1) for `g ≥ 1`:
  `‖K*_𝒬‖_{𝔛^{η,30d,30d}(ℬ)} + ‖K*_𝒯‖_{𝔛^{η,30d,0}(ℬ)} ≲₁ (C₁δ)^n L^{−(γ₁−√η)g}`.

**`exists_proposition51`.**
- **The bound.** Same `n` and the same `incoherenceCount` for the couple and tree link data. The couple kernel
  `sourceCoupleKernel` is cut by both root clocks (`I ∩ R.rootCut t`) on `R.rootBox`. The tree kernel is on
  `rootBox ∩ {t 1 < t 0}`. The sum of the two `mixedRestrictionNorm`s is at most
  `2·(C₁δ)^n L^{−(incoherenceExponent d γ − √η)·g}`.
- **The norms.** `𝔛^{η,30d,30d}` for the couple and `𝔛^{η,30d,0}` for the tree, as in TARGET.
- **`γ₁`.** `incoherenceExponent d γ = min(2γ, 1, 2(d−1)(1−γ))` is TARGET's `γ₁` (defgamma1).
- **The factor 2** is an explicit admissible constant for `≲₁`.
- **Inputs.** `spatialNorm (40d)(40d) ≤ B`; `C₁` depends on `d, η, B`.
- **The prefix.**
  - `C₁` comes before `γ, δ, D`, so it is uniform in them, which is stronger.
  - `L₀` comes after `D`: TARGET's "`L` large depending on `𝔇`".
  - `η` is small (`η ≤ 1/100`, `(100d)²η ≤ 1`, `η < γ₁`). That is within TARGET's `η` small depending on `(d, γ)`.
- **Faithful.** The sum over a couple and a tree with a common `(n, g)` is TARGET's own formulation (L951, L955).
  This is a literal transcription.

**`exists_proposition51_oneClock` (P-1).**
- **The kernel.** `sourceVertexClockKernel ζ v a L γ δ Q I f t = sourceIntegral … (I ∩ {w | w v ≤ t_a})`. Only the
  live root clock, at link endpoint `v`, is cut, by the time coordinate `a`. The other time variable does not occur.
- **The box.** `vertexClockBox v a Q b` is the root's layer interval in coordinate `a`, and an arbitrary unit
  interval `[b, b+1]` in the other.
- **This is TARGET L1049:** "including the case when one of the trees of `𝒬` is trivial, the function `K̃(t,s)` will
  not depend on `t` (or `s`)". `a ∈ {0, 1}` covers either tree being trivial. The arbitrary `b` covers the layer `q'`
  of the trivial tree's lone leaf.
- **The tree half** is unchanged, so the summed form is the same as in `exists_proposition51`.

## 3. Checks (mine)

- **Probe** (dev's build). `#check` of `exists_proposition51`, `exists_proposition51_oneClock` and the component
  theorems; `#print` of `vertexClockBox`, `vertexClockKernel`, `sourceVertexClockKernel`, `sourceCoupleKernel` and
  `incoherenceExponent`.
- **Axioms** of `exists_proposition51`, `exists_proposition51_oneClock` and
  `exists_rawVertexClockKernel_propositionRate`: [propext, Classical.choice, Quot.sound].

## 4. Note

**C-1 (interface; not a defect).** The summed forms need a tree with the same `(n, g)` as the couple. To bound one
couple or one tree alone, as B2.2 `incoherentDecay` states them (each with its own `g`), use the component theorems.
- `exists_rawCoupleKernel_propositionRate` (two roots);
- `exists_rawVertexClockKernel_propositionRate` (one root);
- `exists_rawTreeKernel_propositionRate` (trees).

They carry the same constants structure and are landed. **Instantiation with the frozen gardens remains C2's, after
the Wave B freeze**, as the module docs say.
