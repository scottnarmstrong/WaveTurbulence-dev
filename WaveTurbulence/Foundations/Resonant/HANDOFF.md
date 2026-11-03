# N5 RESONANT handoff

## Landing repair against current main

Merged main `abd80f7d70983a11bb29c142b75a2d6390eb2810` (merge `50791f9`).
Kept the newer Resonant definitions and their packet namespace. The merged
principal-value files elaborate with `Resonant.energyInvInner`, `pvQuotient`,
`IsPVCutoff` and the explicit `energyInvInner_eq` helper. The remaining stale
reference in `SchwartzSmooth` is now explicitly `WKE.deltaInt_congr`, matching
the namespace of the landed `WKE.Multilinear` API. No WKE files were edited.

Post-merge checks, all successful:

- `nice -n 5 lake build WaveTurbulence.Foundations.Resonant.Basic`:
  `Build completed successfully (9097 jobs).`
- Every one of the 43 Resonant Lean files was then freshly elaborated,
  sequentially in dependency order, using
  `nice -n 5 lake env lean WaveTurbulence/Foundations/Resonant/<Module>.lean`.
  Result: `PASS: 43 individual Resonant module checks`; no warnings or errors.
  Exact ordered module list, per-file output, timings and exit codes are in
  `/home/scott/wt-scratch/resonant/repair-validation/` (`modules.txt`,
  `check_all.py`, `results.json`, and one log per module).
- `nice -n 5 lake env lean /home/scott/wt-scratch/resonant/FinalAxioms.lean`:
  exit 0; all sixteen main exports still have only the standard three axioms.
  Output: `repair-validation/axioms.log`. The repository axiom checker reports
  sixteen `ok` lines and `16 declarations audited`.
- `python3 scripts/check_lean_modules.py --root . --max-lines 1500 --files WaveTurbulence/Foundations/Resonant/*.lean`:
  `check_lean_modules: PASS (43 Lean files, 0 comparator configurations)`.

No mathematical changes, new premises, deviations or errata were introduced
by this repair. The source-convention notes below remain applicable.

Branch: `w/resonant`. Verified implementation snapshot: `5a7f74c`.
All declarations are in `WaveTurbulence.Resonant`; the import interface is
`WaveTurbulence.Foundations.Resonant.Basic`.

## Files and completed goals

All 43 Lean files are under `WaveTurbulence/Foundations/Resonant/`.

| Files | Contents |
|---|---|
| `Basic` | Public import interface for the complete packet. |
| `Integral` | Resonant integral in the frozen collision parametrization; collision operator and gain-term special cases; polynomial bounds; inner/outer integrability; mollified characterization in original momentum variables, including the negative energy sign. |
| `Derivatives`, `LocalDerivatives` | Scalar global/local dominated differentiation and smooth parameter families. |
| `DualCoordinates`, `FrechetIntegral` | Integrability of finite-dimensional derivative functionals and differentiation through both integration levels. |
| `SchwartzKernel`, `SchwartzDifferentiation`, `SchwartzSmooth` | Local uniform domination from Schwartz seminorms; full vector Fréchet derivative; C∞ dependence on external momentum for Schwartz three-momentum tests. |
| `PrincipalValueOneDim`, `PrincipalValueBounds`, `PrincipalValueComplex` | Symmetric cancellation, existence before choice-defined principal values, characterization, cutoff independence, support/Lipschitz bounds, complex convergence. |
| `PrincipalValueSlices`, `SliceRegularity`, `PrincipalValue`, `PrincipalValueEstimates` | Inverse collision-energy slicing, normal derivative bounds, outer convergence, proved-limit definition, characterization, bounds, cutoff independence. |
| `SineIntegral`, `SineKernel`, `CutoffSine`, `CentralFourier` | Bounded sine primitive, integration by parts and total-variation bounds uniform in scale and frequency. |
| `PrincipalValueRemainder`, `PrincipalValueFourier`, `PrincipalValueFourierLimit`, `SymmetricQuotient`, `FourierPhase` | L¹ quotient remainder, uniform one-dimensional Fourier estimate and limit, symmetric-quotient cutoff error, frequency-dependent Lipschitz estimate. |
| `LocalizedVolume`, `LocalizedSlices`, `ComplexSlicing` | Center-uniform inverse-norm volume estimates, localized tangential slices, complex disintegration and phase splitting. |
| `BilinearFourierBound`, `BilinearFourier`, `BilinearFourierLimit`, `JointFourierIntegral` | Finite joint integrability, uniform multidimensional estimate, explicit cutoff-independent limit and joint-integral characterization. |
| `BilinearSliceError`, `InverseSquareVolume`, `SmallEnergyBound`, `SmallEnergyCharacterization` | Inverse-square local integrability for d≥3, quantitative μ⁻¹ error and actual principal-value interpretation of the low-energy integral. |
| `LocalizedAmplitude`, `CutoffBounds`, `NTOmegainv`, `NTOmegainvCoordinate`, `NTOmegainvSmallEnergy`, `NTOmegainvSource` | Generic fixed cutoffs, source coordinate-derivative premises, and both conclusions of DH21 Lemma 6.3 with one constant chosen before all amplitude/center/scale/frequency data. |
| `EnergyBilinear` | Exact finite normalization bridge and localized inverse-energy convergence. |

Primary exports:

- `collisionOp_eq_resonantIntegral`, `abs_resonantIntegral_le_of_decay`,
  `tendsto_mollified_resonantIntegral_k`.
- `hasFDerivAt_schwartzResonant_integral`, `contDiff_resonantIntegral_schwartz`.
- `exists_energyInvIntegral_limit`, `energyPrincipalValue`,
  `energyPrincipalValue_spec`, `energyPrincipalValue_eq_integral`,
  `abs_energyPrincipalValue_le`, `energyPrincipalValue_cutoff_independent`.
- `dh21_lemma_6_3_square`, `tendsto_lowBilinearFourierTruncation`,
  `norm_bilinearFourier_small_energy_le`.
- `energyInvIntegral_eq_bilinearFourierTruncation`.

## Approach and precise scope

The resonant integral reuses the landed WKE hyperplane normalization. Polynomial
decay in both free momenta gives integrability and center-uniform bounds for
d≥2, with decay exponent greater than d. Smoothness of Schwartz tests is proved
in the full vector momentum: differentiate under both integrals, reconstruct
the derivative from finite basis evaluations, then induct on derivative order.
The more general local differentiation helpers state the actual local decay
and pointwise derivative hypotheses explicitly.

For inverse energy, even-cutoff cancellation produces a symmetric quotient.
The real `energyPrincipalValue` is defined by choice only after cutoff-limit
existence has been proved; its characterization and cutoff independence are
proved. This API assumes polynomial decay of the kernel and its second-variable
gradient, and a uniform second-variable support radius. The localized bilinear
API separately supplies the hypotheses from fixed compact cutoffs and bounded
amplitudes; no convergence or integrability conclusions are assumed there.

For DH21 Lemma 6.3, subtract the amplitude's value at zero on a fixed symmetric
unit interval. The quotient remainder is L¹; the central sine integral is
bounded by its primitive and cutoff variation, uniformly in frequency.
Slice along the outer momentum and use center-uniform local integrability of
|x|⁻¹ (d≥2). For the μ⁻¹ small-energy error, symmetric cancellation and the
Lipschitz bound of the Fourier-modulated amplitude leave |x|⁻² (d≥3).
The low-energy source expression is proved to be the principal value of a
second-cutoff joint integral, equal to the full limit minus the finite
high-energy truncation. This is an explicit alternate proof to the source's
sector decomposition.

`dh21_lemma_6_3_square` uses d≥3 and scale≥1. The constant is chosen before D,
scale, centers, amplitude, frequencies and μ. Both parts share that constant.
Only zeroth and first y-coordinate derivative bounds are needed from
(NTphibounds); the source's smoothness/higher bounds imply these premises.
The theorem uses arbitrary fixed C¹ compact spatial cutoffs and an even C¹
compact scalar cutoff equal to one near zero. C∞ cutoffs are included.

## Exact final checks and output

All Lean invocations were targeted and used `nice -n 5` and the `wt-throttled`
override. No whole-library build, Mathlib rebuild, cleanup or budget override.
Intermediate failed checks were repaired; the final successful checks were:

```text
nice -n 5 lake build WaveTurbulence.Foundations.Resonant.SchwartzSmooth
✔ Built WaveTurbulence.Foundations.Resonant.SchwartzSmooth
Build completed successfully (9062 jobs).

nice -n 5 lake build WaveTurbulence.Foundations.Resonant.EnergyBilinear
✔ Built WaveTurbulence.Foundations.Resonant.PrincipalValueEstimates
✔ Built WaveTurbulence.Foundations.Resonant.EnergyBilinear
Build completed successfully (9075 jobs).

nice -n 5 lake build WaveTurbulence.Foundations.Resonant.Basic
✔ Built WaveTurbulence.Foundations.Resonant.NTOmegainvSource
✔ Built WaveTurbulence.Foundations.Resonant.Basic
Build completed successfully (9097 jobs).

nice -n 5 lake env lean /home/scott/wt-scratch/resonant/FinalAxioms.lean
Exit 0; sixteen #print axioms reports, each containing exactly
[propext, Classical.choice, Quot.sound].

python3 scripts/check_axioms.py /home/scott/wt-scratch/resonant/FinalAxioms.log /home/scott/wt-scratch/resonant/FinalAxioms.lean
All sixteen reports: ok
16 declarations audited

python3 scripts/check_lean_modules.py --root . --max-lines 1500 --files WaveTurbulence/Foundations/Resonant/*.lean
check_lean_modules: PASS (43 Lean files, 0 comparator configurations)

git diff --check
Exit 0, no output.
```

The job totals include cached dependencies; these were targeted module builds.
The final Basic build checks the entire packet import graph without warnings.
The largest packet Lean file is 216 lines.
The Lean source scan for `sorry`, `admit`, `axiom`, `unsafe`, `opaque`,
`set_option`, draft-theorem imports and provider imports returned no matches.

## Axioms of the main results

The probe imports `Resonant.Basic` and checks all sixteen exports below.
Each has exactly the standard three axioms listed above:

```text
collisionOp_eq_resonantIntegral
tendsto_mollified_resonantIntegral_k
abs_resonantIntegral_le_of_decay
hasDerivAt_deltaInt_of_local_decay
contDiffOn_deltaInt_of_local_decay
tendsto_energyInvIntegral
energyPrincipalValue_eq_integral
abs_energyPrincipalValue_le
energyPrincipalValue_cutoff_independent
hasFDerivAt_schwartzResonant_integral
contDiff_resonantIntegral_schwartz
energyInvIntegral_eq_bilinearFourierTruncation
tendsto_energyInvIntegral_localized
dh21_lemma_6_3_square
tendsto_lowBilinearFourierTruncation
norm_bilinearFourier_small_energy_le
```

## Uncertainties, conventions, suspected errata and deviations

- No open proof gaps or frozen-statement defects found. This is a worker
  implementation handoff; manifest/source-node promotion and landing remain
  with the orchestrator.
- Campaign D2: square torus only, β=1; no anisotropic extension claimed.
- The real resonant/PV interfaces and complex Fourier interfaces are separate.
  Collision energy is −2⟨ℓ,x⟩, versus DH21's ⟨x,y⟩. The exact bridge is factor
  −1/2 and truncation scale 2μ. The final source theorem multiplies frequencies
  by 2π, matching e(z)=exp(2πiz).
- The source fixes 1≤λ≤(log L)^4 before Lemma 6.3 (DH21 L1182). The theorem
  works for all λ≥1. Its final statement uses μ>1 as in the source; intermediate
  results often cover all μ>0.
- χ is compactly supported; χ∞=1−χ is its complement and is not compactly
  supported. The singular low-energy expression is a principal value, not an
  ordinary absolutely integrable pole (see also DH21 L1179 and L1667).
- Minor suspected source typo: DH21 `Inventiones-Final_Version.tex` L1345
  writes `\widetilde\Theta(x, -u, y)` in the reflected term of Δ. It should use
  `y'`, as in the definition immediately before it and the integration variables
  in (NTdefNmuxi). The proof uses that consistent reading. No substantive erratum
  was needed.
- No frozen definition, root import, shared API, manifest, finding ledger, or
  other worker's file was edited. All implementation changes are in the assigned
  directory; no pushes or landings were performed.

READY resonant
