# WKE-L2S progress ledger — active

Branch: `w/wke-l2s`. All work is confined to `Foundations/WKEL2/**`.
No frozen definition, provider, shared WKE file, root import, manifest, or
findings ledger was edited. No push or landing was performed.

## Status

- **Goal 1 complete:** research-note Lemma 1 and Corollary 2, including all
  nonnegative Borel kernels, infinite integrals, angular-first integration,
  and symmetry of the angular measure.
- **Goal 2 active:** radial weight A_k is defined, nonnegative, jointly
  measurable, and its defining integral is integrable for unit θ throughout
  `d ≥ 3`, `s > d/2-1`. Radial Cauchy–Schwarz, the two Hölder exponent windows,
  translation-uniform Hölder, and the nonsingular kernel's Lᵖ membership are
  proved. **Uniform M₁ and M₂ bounds are not yet proved.**
- **Goals 3 and 4 unproved:** Propositions 5–7, Theorem 7, the signed extension,
  audit §3's supporting lemmas, Picard existence/persistence, and
  `wkelwp_blowup`. No maximal-time name has been introduced.

There is no claimed mathematical obstruction. The orchestrator accepted the
initial partial work and directed continuation; the earlier stopped status
has been superseded.

## Files and approach

- `Symmetry.lean`: the initial continuous-decaying-kernel symmetry using a
  nonnegative mollifier, Fubini before taking its limit, and uniqueness of
  limits; gain-input reversal and equivalence of the two asymmetric loss terms.
- `HyperplaneChart.lean`: the Householder reflection perpendicular to
  `e - unitVec a`; its measurable formula, restriction to a linear isometric
  equivalence between hyperplanes, and volume preservation. The chart is
  measurable everywhere; continuity at its exceptional direction is not claimed.
- `ResonantMeasure.lean`: pushforward of weighted product measure; intrinsic
  hyperplane integration and measurability for all nonnegative Borel kernels.
  Cached reference-hyperplane measure instances avoid expensive conversion
  between the induced measurable space and its Haar-measure projection.
- `ResonantLocalFinite.lean`: local integrability of inverse norm, exact ball
  masses, and finiteness on compacts in dimension at least two.
- `ResonantIntegral.lean`: signed integral formula, with precisely the factor
  two relative to existing `deltaInt`.
- `CompactKernel.lean`: compactly supported continuous test kernels satisfy
  the existing `DeltaKernel` hypotheses.
- `ResonantSymmetry.lean`: locally finite Borel measures are determined by
  integrals of C_c test functions; the initial symmetry proves swap invariance.
  `lintegral_inv_norm_hyperplane_swap` has no reference-vector hypothesis.
- `Polar.lean`, `PolarRadial.lean`, `HyperplaneScaling.lean`,
  `ResonantPolar.lean`, `ResonantPolarFull.lean`, `ResonantPolarOrder.lean`:
  general nonnegative polar integration, lowering radial density by inverse
  radius, radial invariance of charts, and the full Corollary 2 formula with
  both radial exponents exactly `d-2`.
- `AngularMeasure.lean`, `RadialCutoff.lean`, `AngularCoordinates.lean`:
  angular measure defined using the radial cutoff and normalized by `(d-1)^2`;
  identification with the two sphere integrals and their symmetry. The two
  radial cutoff masses are each `1/(d-1)` and cancel the normalization exactly.
  Sphere coordinates use the fixed reference hyperplane's isometric chart.
- `Weight.lean`: energy identity and weight transfer with the exact frozen
  `weightedL2Norm` multiplier, constant `2^(s/2)`.
- `Radial.lean`: radial Cauchy–Schwarz for a general positive weight, assuming
  membership of its two factors in L². Membership is not hidden in a norm.
- `Exponents.lean`: the two conjugate-exponent windows from Lemma 4.
- `RadialWeight.lean`: A_k; centered integrability by polar integration in
  dimension `d-2`, shifted integrability by a scalar Peetre inequality, and
  joint measurability.
- `HolderTranslation.lean`: integrability and a translation-independent
  Hölder bound for functions in conjugate Lebesgue spaces.
- `WeightedKernelLp.lean`: Japanese-bracket decay kernel membership whenever
  `a*p > d`, with the actual membership proof, not an assumed estimate.

## Commits

- `16bd608`, `3cce822`: initial accepted partial work.
- `4abc2b6`: measurable hyperplane charts and Borel resonant measure.
- `1f17b9e`: Lemma 1 for arbitrary nonnegative Borel kernels.
- `c028a91`: polar formula and normalized angular-measure symmetry.
- Subsequent milestone: radial-weight integrability and Hölder inputs.

## Checks

All compilation commands were sequential through `wt-throttled`, with no
budget overrides. Each final targeted build below exited 0 without warnings:

```
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.Symmetry
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.Weight
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.Polar
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.Radial
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.Exponents
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.HyperplaneChart
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.ResonantMeasure
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.ResonantLocalFinite
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.ResonantIntegral
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.CompactKernel
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.ResonantSymmetry
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.ResonantPolarOrder
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.AngularCoordinates
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.RadialWeight
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.HolderTranslation
nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.WeightedKernelLp
```

The polar and angular targets also checked their focused prerequisites. No
Mathlib recompilation was reported. Earlier elaboration errors and style
warnings were repaired before the final successful builds.

Axiom probes are in `/home/scott/wt-scratch/wke-l2s/Axioms.lean` (initial
results) and `ResonantAxioms.lean` (continuation results). Exact command:

```
nice -n 5 lake env lean /home/scott/wt-scratch/wke-l2s/ResonantAxioms.lean
```

The probes check the main symmetry, polar, angular-coordinate, radial-weight,
and Hölder/kernel-membership results. All 17 continuation declarations printed exactly the axiom set
`[propext, Classical.choice, Quot.sound]` (exit 0). The initial probe returned
the same set for its nine main declarations. No custom axiom or sorry was
reported.

Banned-token search in new Lean modules and `git diff --check` returned no
matches/errors. Every new Lean module is below 1500 lines.

## Suspected source erratum and deviations

TARGET L2522–L2523, (schappend11): “ι ∈ {−1,0,1}” omits multinomial
coefficients in the displayed sum over multi-index decompositions. Already
two derivatives split between two factors produce coefficient 2. Indexing by
ordered differentiation histories could retain unit coefficients, but the
printed sum does not use that indexing. The subsequent lower-order constant
must absorb the actual multiplicities. This has not been formalized and no
source or shared findings file was changed.

No mathematical deviation was introduced. For general measurable inputs,
real-valued Bochner expressions alone do not express L² membership;
integrability/MemLp must accompany them. The frozen norm remains unchanged.

## Next proof frontier

Prove Lᵖ membership for the singular far-field kernels and the near-field
integrability bounds, then use the translation Hölder lemma for uniform M₂
and M₁. Their already-proved exponent windows cover exactly `2s > d-2`.
Continue to Propositions 5–7 and Theorem 7, then the blow-up argument.

The measurable-chart elaboration refactor was profiled with
`nice -n 5 lake env lean --profile WaveTurbulence/Foundations/WKEL2/ResonantMeasure.lean`.
Before refactoring the failing proof, tactic execution totaled 15.5s and hit
the default heartbeat budget; after factoring the ambient graph and caching
the reference measure instances, it totaled 455ms and the file exited 0.
Profiles are `resonant-profile-before.log` and `resonant-profile-after.log`
in the scratch directory. No elaboration budget was changed.

## Active continuation: uniform M₂ proved

- `2ed2b68`: near/far inverse-norm kernels, their actual Lᵖ membership,
  conjugate-exponent selection, translation-uniform spatial convolution,
  its transport to every moving hyperplane, and the polar mass identity.
- `b2cdf72`: `M2.exists_uniform_M2` proves research-note Lemma 4(a), including
  great-sphere integrability and a constant independent of the center and normal.
- `7f38e97`: scalar/transverse norm-power integrability, the exact scalar slice
  identity for M₁, cylindrical near-field integrability, cylindrical coordinate
  isometries, homogeneity, and the M₁ exponent window.

The M₂ measurable-sphere conversion initially exceeded the default budget.
The passing proof derives measurability directly from the scalar radial
integrand, rather than composing the ambient joint measurability theorem
through two nested subtype coercions. No statement or budget was changed.
The initial profile is `m2-profile-before.log` in scratch.

M₁ remains under active construction: the spatial/angular polar identity
already passed its target dependency build; the cylindrical far-field Lᵖ
proof and transport are being checked. The near/far cutoff for this proof is
an isometric cylindrical unit box rather than a Euclidean unit ball. This
only changes allowed constants depending on dimension and exponent.

`angularSineInv` uses the norm of orthogonal projection onto the normal's
perpendicular hyperplane, equal to the absolute sine for unit vectors. As
with existing inverse-norm definitions, the inverse is assigned zero at
zero. No stronger weighted exponent or additional source premise is used.

## Goal 2: both uniform bounds compiled

`e28075c` proves `M1.exists_uniform_M1` throughout `d ≥ 3`, `s > d/2-1`.
Together with `b2cdf72` (`M2.exists_uniform_M2`), this completes the two
uniform bounds of research-note Lemma 4. The actual near/far integrability,
far-field Lᵖ membership, axis transport, and polar identities are proved;
none is passed as a source-result assumption. The M₁ and M₂ targeted builds
both exited 0 without warnings. The combined axiom probe is
`/home/scott/wt-scratch/wke-l2s/Lemma4Axioms.lean`.

Goal 3 is now active: exact frozen weighted-L² membership/norm bridge,
extended nonnegative ray Cauchy–Schwarz, angular Schur bounds, and the loss
and gain estimates. Theorem 7 and the blow-up conjunct remain unproved.

The combined Lemma 4 axiom probe exited 0: all ten main declarations,
including both uniform M₁ and M₂ theorems, depend exactly on
`[propext, Classical.choice, Quot.sound]`. No custom axiom or sorry was reported.

## Goal 3 active: radial Cauchy–Schwarz and angular loss estimate

- `88d4a56`: linear isometries preserve canonical spherical surface measure.
- `ca7eb06`: exact frozen weighted norm equals the genuine weighted L² norm;
  polar radial-density powers; nonnegative ray energies; their exact angular
  integral; extended radial Cauchy–Schwarz (Lemma 3), with no finite-energy
  assumption on individual rays; M₂ in fixed reference-sphere coordinates.
- `daf9045`: angular Schur energy bound and exact second-loss polar
  factorization, valid for nonnegative extended integrals.
- `4ec7f9a`: uniform angular ray-mass estimate (the nonnegative-integral
  core of Proposition 5).

Passing focused builds: `RadialCauchyENN`, and the `AngularM2`,
`AngularCauchyAlgebra`, `AngularProduct`, `AngularSchur`, `LossTwoPolar`,
`AngularMassEstimate`, `LossTwoBound` prerequisites of `LossTwoTrilinear`.
All passing modules above built without warnings. The signed delta-integral
bridge and bounded weighted multiplication are still being checked.
Proposition 6's two-axis geometry, transverse integral, no-atom surface
lemma, and sine Schur bound are working files pending compilation.
The full Theorem 7 and supporting blow-up obligations remain active.

## Proposition 5 and the j = 2 case of Theorem 7

`fbb8c41` proves `exists_uniform_lossTwo_signed`: signed Borel weighted-L²
inputs give a genuinely integrable resonant kernel for every center and a
uniform bound for the exact `deltaInt`, with its factor one half.
`84834bc` proves `exists_collisionTerm_two_bound`: actual weighted `MemLp 2`
membership and the trilinear bound in the exact frozen norm.
`nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.LossTwoTrilinear`
exited 0 without warnings after the style cleanup.

`nice -n 5 lake env lean /home/scott/wt-scratch/wke-l2s/LossTwoAxioms.lean`
exited 0. All nine results audited (weighted norm bridge, radial energy,
radial Cauchy–Schwarz, reference M₂, angular Schur energy, angular mass,
signed Q₂, bounded multiplication, and the j = 2 trilinear estimate)
depend exactly on `[propext, Classical.choice, Quot.sound]`.

Merged `main` at `942e385`; the landed maximal-time API is
`WaveTurbulence.WKE.tauMax` (`Foundations/WKE/Lifespan.lean`), so the final
blow-up theorem will use that time, as required by the brief. The merge moved
`deltaInt_smul` into `WaveTurbulence.WKE`; `09c15d4` adapts the reference.
The same targeted j = 2 build passed again after this merge, without warnings.

Proposition 6's infrastructure is being checked in the focused
`LossOneInfrastructure` target. Its geometric route is two successive
orthogonal slices, a positive scalar shear with Jacobian inverse sine,
and the uniform affine codimension-two decay integral. Spherical averaging,
Tonelli square expansion, and full-sphere M₁ Schur pairing are explicit.
These working files are not yet certified as built; no completion claim for
Proposition 6, Proposition 7, full Theorem 7, or the blow-up theorem is made.

## Proposition 6 active: geometry and spherical representation

- `7d2e76b`: nonnegative weighted-square Tonelli expansion, orthogonality
  almost everywhere on resonant measure, and the inverse-sine pairing algebra.
- `31dd94b`: uniform affine codimension-two decay integral, nonnegative
  scalar dilation/shear identities, sine-kernel symmetry and measurability,
  and nullity of proper-subspace directions for spherical surface measure.
- `a9711ea`: positive-ray density, two-axis volume coordinates and inner-product
  identities, and the M₁ sine Schur energy bound.
- `434acb4`: positive angular slicing, full-sphere sine mass estimate,
  and identification of positive-ray samples with radial masses.
- `8789fd2`: the null exceptional second-axis set and the extended
  nonnegative codimension-two slice bound.
- `8e3bf74`: spatial weighted Cauchy–Schwarz in the exact frozen norm.

The spherical-average representation initially reached the default heartbeat
budget. Warm profiles (`loss-one-spherical-before.log`, then focused traces
and `loss-one-spherical-after5.log`, all in the scratch directory) located
the cost in composing the joint integrand measurability theorem with a
fixed-parameter embedding through the Euclidean-space/sphere coercions.
A direct measurability proof from the continuous fixed-parameter sphere
map passes. The warm `--profile -D profiler.threshold=1` source check exited
0 with no warnings. Cumulative tactic execution fell from 11.7s (failure)
to 247ms (passing); no heartbeat or other budget was changed. The complete
`LossOneBound` target is being checked next; Proposition 6 is not yet closed.

## Goal 3 complete at implementation level: Theorem 7

`420a7fb` proves the nonnegative first-loss bound; `6586e33` its signed
version; `d6e2e05` the j = 1 bound; `7cf2b43` signed resonant symmetry and
j = 3. Their axiom audit (`LossOneAxioms.lean`) exited 0, standard axioms only.

`774bdbc` proves that gain recentering preserves dk dν; `9d01328` proves the
gain Schur pairing; `073c0c4` proves the exact weighted gain pairing.
`3350ffe` and `207ed18` establish genuine real L² tests and the extended
nonnegative duality argument. `a0d684c` proves weighted squared integrability
of the absolute gain output; `04fcda0` derives the signed j = 0 bound,
actual membership, and the almost everywhere intrinsic delta reading.
`ae6eadc` combines all four terms into `exists_collisionTerm_bound`.

The final focused Trilinear build exited 0 without warnings. The six-result
`Theorem7Axioms.lean` audit exited 0: standard axioms only for every result.
The exact binders, frozen definition hashes, normalizations, source ranges,
and scope of this worker implementation check are in `THEOREM7-CHECK.md`.
No frozen anchor or manifest promotion was attempted.

Goal 4 is active. `939aa54` constructs continuous weighted Schwartz-to-L²
embeddings using the exact frozen multiplier and proves actual membership,
exact norm equality, and norm continuity on frozen Schwartz solutions.
`9e41b79` proves inverse weights, injectivity, density, and continuity of the
weighted solution curve in the Banach model. The weighted encode/decode
model and its linear algebra are being checked. The final blow-up theorem
will use the landed `WaveTurbulence.WKE.tauMax`.

## Goal 4 in progress: exact weighted Banach field and quantitative Picard

- `3735d3d`: full frozen collision decomposition almost everywhere on the
  actual Borel weighted-L² domain, and its genuine membership and norm bound.
- `9c6ce78`: norm-preserving bounds for dense linear and trilinear extensions,
  with exact agreement on the dense core.
- `e3686ea`: the actual Schwartz collision map, transported through the
  faithful weighted Schwartz image and extended to the L² Banach model.
- `b84ccca`: quantitative cubic Picard existence with lifespan
  `[8 (‖T‖ + 1) ‖u₀‖²]⁻¹` for nonzero data.
- `a8e819b`: uniqueness on a common compact interval, the global zero
  solution, differential/mild equivalence including endpoints, and local
  existence and uniqueness for the completed weighted collision field.
  The Schwartz-data lifespan uses the exact frozen weighted norm.

Checks: targeted `CollisionBanach`, `CubicPicard`, `CubicUniqueness`,
`CubicMild`, and `CollisionPicard` builds exited 0 without warnings in their
final versions. `nice -n 5 lake env lean
/home/scott/wt-scratch/wke-l2s/BanachAxioms.lean` exited 0. Its eight results
(full collision bound, Schwartz agreement, cubic existence and uniqueness,
both mild/differential directions, weighted mild existence and uniqueness)
all depend exactly on `[propext, Classical.choice, Quot.sound]`.

`4151cc6` constructs actual finite weighted Schwartz jet maps and their
Banach completions; `2fb7ad1` proves the faithful isometric realization in
finite L² coordinates, exact one-letter Leibniz/weight identities, and
first-order weighted bounds. The final targeted `JetEstimates` build exited
0 without warnings. The ordered-word convention retains all distribution
multiplicities; comparison with the source multi-index supremum norm is
still a remaining obligation, not a claimed result.

Elaboration checks: `collision-banach-before.log` located a default-budget
failure in a rewrite chain (3.29s tactic execution). Applying the dense-core
agreement theorem directly reduced tactics to about 0.20s; the final build
passed. `weighted-coordinates-before.log` located a default-budget failure
in the native isometric extension application (11.2s elaboration). An
abstract dense-isometry extension, explicit carrier arguments, and an
explicit unfolding in the agreement lemma passed at the default budget
(`weighted-coordinates-after2.log`: 0.217s elaboration, 0.243s tactics).
No budgets were changed.

Remaining: the finite-order jet trilinear bounds and their density
extensions, tame Gronwall persistence, identification with the source
weighted Sobolev spaces and equivalent Schwartz topology, equivalence with
the frozen pointwise Schwartz solution class, and the full blow-up conjunct
relative to `WKE.tauMax`. No completion or READY claim is made yet.
