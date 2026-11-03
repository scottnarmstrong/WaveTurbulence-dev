# HUA handoff

Branch: `w/hua`, created from main in the existing gausssum worktree.
All worker-authored changes are confined to `WaveTurbulence/Foundations/WeylSums/`.
Main was merged without conflicts at `6bee635` (integrated main `e247a1d`).

## Files and interfaces

- `HuaPacket.lean`: public packet interface.
- `Hua.lean`: `hua_moment_bounds`, DH21 Lemma A.5. One absolute positive
  constant gives the fourth moment `≤ C N² log(N+2)` and sixth moment
  `≤ C N⁴`, uniformly in real linear frequency and integer center, for `N≥1`.
- `HuaOrthogonality.lean`, `HuaEnergy.lean`, `PositiveMoments.lean`,
  `HuaCutoff.lean`, `HuaMajorization.lean`: exact integer-frequency
  orthogonality, resonance counting, positive-coefficient monotonicity, and
  domination of the sharp inclusive sums by one fixed smooth cutoff.
- `ArcProfile.lean`, `ArcAlgebra.lean`, `RationalArcCover.lean`,
  `ArcIntegration.lean`, `SmoothArcEnvelope.lean`, `SmoothUnitMoments.lean`:
  finite rational covers, exact arc mass, and integration of the proved
  log-free Gauss bound. The denominator sum is harmonic at power four and
  convergent above power four.
- `WeylSupremum.lean`: the actual supremum Weyl sum, equality with the
  two-supremum expression over all integer centers and real linear
  frequencies, finite bounds, lower semicontinuity and measurability.
- `RealArcCover.lean`, `WeylSupremumArcs.lean`, `WeylGlobalMoment.lean`:
  rational approximation and global moments at every real scale `L≥1`.
- `LocalArcCover.lean`, `LocalArcIntegration.lean`, `WeylLocalArcs.lean`,
  `WeylLocalMoment.lean`: away from the zero rational arc, the possible
  numerators have cardinality at most `4qT`. Integration gains the window
  length `T`, with both signs and endpoints included.
- `WeylMoments.lean`: `weyl_moment_bounds` gives `C L^(p-2)` globally
  and `C L^(p-2) T` locally for every real `p>4` (locally `L≥2`).
  `weyl_localized_power_bound` substitutes `T=A L^(2γ-2)` and combines
  exponents exactly. Set `p=3d/2` for TARGET L1567–L1590.
- `Reduction.lean`: shared reduction interface and consumption map.
- `QuadraticDiagonalization.lean`: exact bilinear and cubic quadratic
  identities including transformed linear frequencies; bijections onto
  the parity sublattices; exact reindexing of lattice sums; parity
  constraints expressed as finite sums of shifted linear phases.
- `CompactFourier.lean`: Schwartz and integrable Fourier representations of any smooth
  compact joint cutoff on Euclidean space, and existence of auxiliary
  tensor cutoffs equal to one on its support.
- `FourierTensorReduction.lean`: exact Fourier superposition and tensor
  factorization on arbitrary finite coordinate sets, plus the product bound.
- `LatticeBoxes.lean`, `WeylTensorFactors.lean`, `CompactLatticeReduction.lean`:
  turn the infinite compact lattice sum into a finite box and apply the
  tensor reduction with translated factors bounded by the full Weyl
  supremum. `compact_lattice_weyl_reduction` has a cutoff-dependent constant
  independent of real scale, integer centers, and phase frequencies. The
  explicit plateau premise is support data for the auxiliary coordinate
  cutoffs; the original joint cutoff need not separate.
- `WeylSymmetry.lean`: sign symmetry and integer periodicity of the supremum,
  as used when the diagonalized quadratic frequencies have negative signs.
- `FourierTranslations.lean`: spatial translations multiply the Fourier
  weight by a unit phase and preserve its `L¹` norm.
- `FourierTails.lean`: compact Fourier replacements, an explicit `L¹` tail
  error for bounded kernels, vanishing tails, and arbitrary polynomial
  pointwise error for Schwartz weights (also at lattice sampling points).

## Approach and conventions

Hua is obtained from exact resonance identities and positive smooth
majorization, then rational-arc integration of the independently proved
log-free smooth Gauss bound. This is an alternative to repeating the
source's direct divisor/gcd count. No Hua or Weyl moment estimate is assumed.
The quadratic interval sum includes both endpoints; `N≥1` is required
because the inclusive `N=0` sum has one term. The logarithm is `log(N+2)`.

The supremum is inside the moments. The definition reduces integer centers
to zero only after proving the translation identity, and an explicit
`weylSupremum_eq_full` theorem identifies the literal source expression.
The global theorem allows real `L≥1`; the local theorem allows `L≥2` and
any nonnegative window `T`, without an unnecessary upper restriction on `T`.
The local window is closed; the two inner boundary points are discarded
only in the almost-everywhere comparison, using their zero Lebesgue measure.

The shared reduction is coordinate-generic (`m=2d` or `3d`). All original
lattice parity constraints are retained. The source's compact Fourier
replacement is implemented with a retained remainder, rather than an
assertion that a nonzero compact smooth cutoff has compact Fourier support.

## Checks and axioms

Targeted checks only, through `wt-throttled`; no Mathlib rebuild, full library
build, or budget override. The final checks and their exact outputs are
recorded below.

Final packet build:

- `nice -n 5 lake build WaveTurbulence.Foundations.WeylSums.HuaPacket`:
  `Build completed successfully (3850 jobs).` This is one targeted build;
  the dependency count includes cached Mathlib artifacts.
- Owned-directory module/prohibited-token check:
  `55 Lean modules checked; maximum 222 lines; 0 violations`.
- `git diff --cached --check`: exit 0, no output.

Earlier milestone checks:

- `nice -n 5 lake build WaveTurbulence.Foundations.WeylSums.Hua`: successful.
- `nice -n 5 lake build WaveTurbulence.Foundations.WeylSums.WeylMoments`: successful.
- `nice -n 5 lake env lean /home/scott/wt-scratch/hua/AuditHua.lean`:
  `hua_moment_bounds` depends on `[propext, Classical.choice, Quot.sound]`.
- `nice -n 5 lake env lean /home/scott/wt-scratch/hua/AuditMoments.lean`:
  `weyl_moment_bounds`, `weyl_localized_power_bound`, and
  `measurable_weylSupremum` each depend on
  `[propext, Classical.choice, Quot.sound]`.

Final combined axiom audit:

- `nice -n 5 lake env lean /home/scott/wt-scratch/hua/AuditPacket.lean`:
  exit 0. All 16 declarations printed exactly the axiom set
  `[propext, Classical.choice, Quot.sound]`.
- The audited declarations include all three main results
  (`hua_moment_bounds`, `compact_lattice_weyl_reduction`,
  `weyl_moment_bounds`), the localized power substitution, literal full
  supremum equality, both lattice reindexings, parity phases, Schwartz
  Fourier representation, translated Fourier weights, all tail estimates,
  sign symmetry, and periodicity.

Milestone commits:

- `d57d826`: uniform sharp fourth and sixth Hua moments.
- `b689773`: global and localized moments of the full supremum.
- `0808740`: compact Fourier and lattice reductions, parity reindexing,
  translations, quantitative tails, and packet interface.
- `6bee635`: clean integration of main `e247a1d`.

After merging main, the same targeted `HuaPacket` build again reported
`Build completed successfully (3850 jobs).` The updated smoothness rule was
checked: this packet uses scoped `∞`, with no untyped analytic `⊤` premise.
The combined `AuditPacket.lean` command was rerun after the merge: exit 0,
with the same standard axiom set for all 16 declarations.

## Uncertainties

None in the proved statements. The shared reduction deliberately exposes
ordinary support/plateau data for the auxiliary cutoffs, and proves that
such tensor plateaux exist for every compact joint cutoff after enlargement.
No application-specific estimate is assumed in place of a packet result.

## Source issues and deviations

- DH23 L1099 writes `p·ξ+y·ζ` after changing to `(p,q)` variables.
  The second term must be `q·ζ`. The formal identities retain both transformed
  variables and their exact linear frequencies.
- TARGET L1567 says `|t'|≥L⁻¹` forces `a≠0`. At the single boundary
  `t'=L⁻¹`, `a=0,q=1` can satisfy the weak Dirichlet error. We prove the
  implication with strict inner inequality and recover the closed window
  by null endpoints. This does not change any integral or exponent.
- No frozen declaration was changed. No source estimate was added as a
  hypothesis. No worker-authored changes outside the owned directory or root imports.

READY hua
