# WKE-L2S handoff — incomplete

Branch: `w/wke-l2s`. No frozen file, provider, shared WKE file, root import,
manifest, or findings ledger was edited. No push or landing was performed.

## Files and proved results

- `Symmetry.lean`: absolute-value closure of `DeltaKernel`; existence of a
  nonnegative mollifier; joint absolute integrability of the mollified kernel;
  `deltaInt_swap_of_decay`; `collisionTerm_zero_reverse`;
  `collisionTerm_three_eq_one_reverse`.
- `Polar.lean`: `lintegral_polar`, for a nonnegative Borel function on any
  nontrivial finite-dimensional real normed space with Haar measure. The radial
  density remains in `Measure.volumeIoiPow`, and the sphere measure is
  `Measure.toSphere`.
- `Radial.lean`: `radial_cauchy_schwarz`, the weighted inequality of Lemma 3,
  conditional only on positivity and membership of its two factors in L².
  This does not establish their membership for the application.
- `Exponents.lean`: the two nonempty conjugate-exponent windows in Lemma 4.
- `Weight.lean`: resonance energy identity and weight transfer with exactly
  the multiplier used in frozen `weightedL2Norm` and constant `2^(s/2)`.

## Approach and unresolved proof

Use a nonnegative smooth normalized bump, apply Fubini before taking the
mollifier limit, and use the existing `DeltaKernel` convergence theorem in both
orders. This proves symmetry under genuine continuous decay hypotheses, and
the two collision-term consequences for `CollisionInputs`.

**No brief milestone is claimed complete.** In particular, the following are
not proved:

1. Lemma 1 for arbitrary nonnegative Borel kernels and Corollary 2 for the
   resonant angular measure (including symmetry of that measure).
2. Finiteness of A_k and the actual uniform M₁/M₂ estimates. Selecting their
   Hölder exponents does not prove the estimates.
3. Propositions 5–7, Theorem 7, the signed-input extension, or any of the
   three supporting lemmas in audit §3.
4. `wkelwp_blowup`, Picard existence, or identification of maximal times.

The unresolved foundational proof is the measurable nonnegative extension
over a varying hyperplane. Two routes were investigated:

- The mollifier route is proved for continuous decaying kernels; its existing
  domination hypothesis is unavailable for a general Borel kernel. Fatou
  alone does not give the needed equality or monotone extension.
- Mathlib's `HaarToSphere` gives the general polar coordinate change, and
  `lintegral_polar` packages it for a fixed space. Applying it on each
  hyperplane does not by itself establish measurability of the resulting
  family as the normal varies, nor symmetry of its angular measure.

Resolving this needs a proof of measurable dependence on the hyperplane and
a measure-extension/uniqueness argument. No estimate or symmetry assumption
was inserted to stand in for that proof. This is an unresolved formalization
step, not a counterexample to the audited mathematical result.

## Exact checks

All compiles were sequential through the worktree's `wt-throttled` override.
The final runs of these commands exited 0 without warnings:

```
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.Symmetry
# Build completed successfully (9053 jobs).
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.Weight
# Build completed successfully (9049 jobs).
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.Polar
# Build completed successfully (2837 jobs).
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.Exponents
# Build completed successfully (3137 jobs).
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.Radial
# Build completed successfully (3368 jobs).
nice -n 5 lake env lean /home/scott/wt-scratch/wke-l2s/Axioms.lean
# exit 0
git diff --check
# exit 0, no output
```

The job counts include cached prerequisites; these were targeted builds,
not full library builds. Only project compilation was reported by Lake.
Initial elaboration errors in the new modules were fixed before these final
successful runs; no failing source is retained.

`#print axioms` on all nine main public results listed below returned exactly
`[propext, Classical.choice, Quot.sound]`:

```
deltaInt_swap_of_decay
integrable_mollified_kernel
collisionTerm_zero_reverse
collisionTerm_three_eq_one_reverse
weight_transfer
lintegral_polar
exists_holder_exponent_M1
exists_holder_exponent_M2
radial_cauchy_schwarz
```

All are in namespace `WaveTurbulence.WKEL2`. No custom axioms or sorry were
reported. Banned-token search over new Lean files returned no matches; each
file has fewer than 1500 lines.

## Suspected source erratum and deviations

TARGET L2522–L2523, (schappend11): “ι ∈ {−1,0,1}” for the sum indexed by
multi-index decompositions omits Leibniz multinomial coefficients. Already
two derivatives split between different factors have coefficient 2. An
indexing by ordered differentiation histories could retain ±1 coefficients,
but the displayed sum does not have that indexing. The subsequent lower-order
constant must absorb the actual multiplicities; the existence of an a priori
bound is unaffected. This observation has not been formalized, and no source
or shared findings file was changed.

No mathematical deviation was introduced. Partial lemmas have names and
docstrings recording their scope. In particular, real-valued Bochner norms
must be accompanied by integrability/MemLp for general measurable inputs;
mere finiteness of a real expression is not a membership condition. The
frozen definition is left intact.

STOPPED wke-l2s: general Borel resonant-measure extension remains unproved; Theorem 7 and the blow-up conjunct are unfinished.
