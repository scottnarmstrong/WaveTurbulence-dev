# MINOR-ARCS handoff

Branch: `w/minor-arcs`. Source milestones committed through `37d7ccc`; main
`aba1928` merged cleanly in `2619bac`. All packet goals are proved.

## Results and files

All files are under `WaveTurbulence/Foundations/WeylSums/`, namespace
`WaveTurbulence.WeylSums`. `MinorArcTools.lean` is the combined public entrypoint.

- `QuadExpSum2.lean`: `quadExpSum2_bound`, with the audited draft's quantifiers,
  cutoff, finite lattice sum, and power
  `2*d - 2*(d-1)*(1-γ) + η`.
- `QuadExpSum3.lean`: `quadExpSum3_bound`, for both Boolean phases and the exact
  closed time-square window; power `3*d + γ - 2*min γ (1-γ)`, times `log L`.
- `MinorArcs2General.lean`: `dh23_minor2_bound` and
  `dh23_minor2_source_bound`, the weighted DH23 minor-arc estimate with arbitrary
  positive lower support constant `c₀`. The core result assumes `P ≥ 2*d`;
  the source version derives this from `P > η⁻²` and the explicit standing
  smallness condition `0 < η ≤ 1/(2*d)`. Widths may be any value at least one.
- `MinorArcs1.lean`: `dh23_minor1_bound`, the global DH23 bound, including
  integrability, for the finite-regularity amplitude supported in `|s| < L^(2γ)`.
- `BilinearBandCount.lean`: `exists_bilinear_band_count_bound`, the uniform
  bilinear energy-band lattice count.
- `ThreeVectorCount.lean`: `three_vector_lattice_count`, the conserved
  three-vector count with bound `C * δ⁻¹ * L^(2*(d-γ))`, closed unit spatial
  balls, and a proved finite counting set.

Supporting modules cover parity-preserving diagonalization, finite-order
Sobolev Fourier representation, weighted bilinear estimates and dyadic tails,
zero/nonzero Weyl moments, cubic chain/star estimates, and positive Fourier
kernels for band counting. Each source file is a focused module; none exceeds
222 lines. Earlier GAUSSSUM/HUA handoffs remain separate.

## Proof approach

The refined minor-arc moment retains the denominator lower bound, giving the
required interval gain. Exact parity character averages implement bilinear
and cubic lattice changes of variables. Finite-order spatial Fourier inversion
handles joint amplitudes, using only the stated coordinate derivative bounds;
countable interval covers and dyadic summation control weighted time tails.
For arbitrary `c₀`, an enlarged fixed auxiliary scale handles the lower cutoff.

For the cubic chain phase the variables are `(x+y,x-y,x+y-2*z)` with both
parity constraints retained. A three-factor Young inequality and local Weyl
moments give the target power. For the star phase, summing either outer variable
produces the actual minimum of two one-time Weyl bounds. Splitting the Weyl
function into its zero arc and complement, then using product moments,
interpolation, and the pointwise cap proves this minimum bound in dimension
three and higher dimensions. This replaces literal layer-cake integration with
an equivalent product-moment proof, without an assumed exponential-sum bound.

The count uses the positive squared Fourier transform of an interval. Its
band lower bound and convolution upper bound are proved directly. Conservation
reduces three vectors injectively to two differences; the exact identity is
`|k₁|²-|k₂|²+|k₃|² = |k|²-2⟨k₁-k₂,k₃-k₂⟩`.

## Conventions and source fidelity

The cutoff equals the audited draft formula (`chi0_eq_draft_formula`), and the
carriers are the frozen `Mom` and lattice-point carriers. Boolean `true` means
`⟨x,z⟩`; `false` means `⟨z,x+y-z⟩`. The time-square window includes endpoints.
The Japanese weight is `(1+(s/B)^2)^(-P/2)`.

Spatial regularity is finite `C^(10*d)`. Coordinate-word derivative bounds
through total order `10*d` suffice; the source's separate multiindex bounds
supply these. Time measurability is explicit typing data, with no added time
regularity. The width estimate holds for all widths at least one, so the source
upper restriction by a logarithmic power is unnecessary. The small-η condition
above makes the source standing hierarchy quantitative; the core estimate is
available for every positive η with `P ≥ 2*d`.

No frozen statement, provider, manifest, root import, or findings ledger was
edited. Bridging the Foundations results to frozen anchors is the orchestrator's
integration task. There are no remaining mathematical gaps or uncertainties.

## Validation

After merging main, ran:

```
nice -n 5 lake build WaveTurbulence.Foundations.WeylSums.MinorArcTools
Build completed successfully (9189 jobs).

nice -n 5 lake env lean /home/scott/wt-scratch/minor-arcs/AuditFinal.lean
```

The latter printed, for each of `quadExpSum2_bound`, `quadExpSum3_bound`,
`dh23_minor2_source_bound`, `dh23_minor1_bound`, `three_vector_lattice_count`,
and `exists_bilinear_band_count_bound`:

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both commands exited zero. `git diff --check` passed with no output. Structural
audit of all 148 WeylSums Lean modules passed: module headers/public sections,
line limit, no proof holes or prohibited declarations/budget overrides, and no
provider/frozen-theorem imports. Only targeted builds were run; Mathlib was not
rebuilt.

## Suspected source errata and deviations

- Existing F45: DH23 `Revision_Submit.tex` L1099 displays `p·ξ+y·ζ`;
  the second term should be `q·ζ`.
- Suspected literal support-box factor slip under the standard cutoff convention:
  DH23 L1095 says the transformed amplitude is supported in
  `{g^j≤Lz^j≤g^j+2λL, h^j≤Lw^j≤h^j+2λL}`. The standard cutoff at L440 has
  radius one; `z=x+y`, `w=x-y` therefore have radius `2λ`, or total width `4λ`
  up to rounding. The later enlarged box of size `20λL` already accommodates
  this, so it is harmless for the theorem. The source also allows slightly
  different cutoff supports. Our proof establishes the actual transformed
  support and uses a sufficiently enlarged auxiliary Weyl scale.
- The product-moment cubic proof and positive squared-interval counting kernel
  are proof-route changes only; the requested conclusions are unchanged.

READY minor-arcs
