# AN-SOB implementation handoff

Worker branch: `w/an-sob`. All owned changes are under
`WaveTurbulence/Foundations/Analysis/`. No root imports, frozen declarations,
manifest entries, shared APIs outside this directory, or findings ledgers were edited.
This is an infrastructure packet handoff, not a sealing/audit verdict for a frozen anchor.

## Public entry points and exact scope

- `IntervalSobolev.norm_le_interval_sobolev_L2` (namespace `WaveTurbulence.Analysis`):
  a globally C¹ normed-space-valued curve, evaluated in `[a,a+1]`, is bounded by
  the square roots of the integrals of its squared norm and squared derivative norm.
  `norm_apply_le_interval_sobolev_L2` gives the counting-measure ℓ² coordinate estimate.
- `WeightedSobolev.norm_le_radial_weighted_sobolev`: a globally smooth function on
  `Fin d → ℝ`, all Boolean mixed partials bounded by `A (1+∑xᵢ²)^(-d)`, has
  `‖f x‖≤(2π)^d A`. `CubeSobolev` also proves the general whole-space mixed-W¹,¹
  estimate with an extended-nonnegative-real integral, without decay assumptions.
- `SquareMorreyReal.norm_rpow_le_square_morrey_largeParameter`: for globally C¹
  `f : Mom 2 → F`, `x` in the closed unit square, conjugate `p,q`, `p≥20002`, `M≥1`,
  
  `‖f x‖^p ≤ 2^p M^(p/200) ∫square ‖f‖^p + (2 C(q))^p M^(-50p) ∫square ‖Df‖^p`.
  
  The explicit finite `C(q)` is `(squareMorreyConstant q).toReal`. Thus `p=2P`
  gives the source powers `M^(P/100)` and `M^(-100P)` for `P≥10001`, with constants.
  The derivative is the first Fréchet derivative, in operator norm.
- `HeapOrderVolume.volume_heapOrderRegion`: for any relation on `Fin n` and `D≥0`,
  the ordered region in `[0,D]^n` has volume equal to its number of compatible
  permutations times `D^n/n!`. `SimplexVolume.volume_orderedSimplex` and
  `volume_two_orderedSimplex` give the chain and two-chain formulas.
  `TwoChainBound.volume_interleavedTwoChains` handles arbitrary coordinate interleavings;
  `two_chain_factorial_bound` supplies the loss `2^(m+n)`.
- `FactorialExponential.pow_div_sub_factorial_le_exp`: for `x≥0`, `d≤z`,
  `x^z/(z-d)!≤x^d exp x`. The all-index theorem assumes `x≥1`.
- `CovariantCubeSobolev.enorm_le_cubeCovariantSobolevL1`: the smooth complex cube
  estimate for the shifted operators `∂ᵢ-π i Lᵢ`, written as equivalent recursive
  iterated cube integrals. `CubeSobolev.enorm_le_cubeSobolevL1` supplies the ordinary version.
- `PaperTimeIntegral.norm_paperTimeIntegral_le` (namespace
  `WaveTurbulence.Analysis.IntegrationTree`): for the local full ternary tree `T`,
  nonnegative branching-edge gaps (zero leaf-edge gaps), and `t∈[0,1]`,
  
  `‖T.paperTimeIntegral t‖ ≤ timeIntegralConstant ^ T.branchCount * ∑d, T.realChoiceWeight 1 d`.
  
  `timeIntegralConstant` is a fixed positive real, independent of the tree,
  frequencies, gaps and time. A leaf integral is one. The complete branch equation is
  `paperTimeIntegral_node`: integrate `exp(π i α s)` times the three child integrals,
  evaluated at `s-σⱼ`, over `0..max(0,t)`.
  `Choice` has one Boolean per branch (`card_choice` proves cardinality `2^n`).
  `outputFrequency` is zero or the vertex resonance according to that Boolean;
  `choiceResonance` is the vertex frequency plus the three child output frequencies.
  `realChoiceWeight 1` is exactly the product of reciprocal Japanese brackets at branches.
  The auxiliary lower-endpoint labels are ignored by the source integral and its weights.

## Proof approach

The interval argument is the fundamental theorem of calculus, averaged in the base point,
followed by Cauchy–Schwarz. Iteration proves the cube and whole-space estimates; a unitary
gauge supplies imaginary derivative shifts. Square Morrey uses the segment/Riesz-potential
formula, radial kernel integrability and Hölder, followed by localization at
`r=M^(-P/200)`.

Ordered chambers partition the cube outside null coordinate ties. Permutation symmetry
and iterated interval integration give the exact simplex and heap-volume formulas.

For the tree estimate, the actual Fourier kernel of cutoff time integration obeys
`‖Kχ(a,τ,q)‖≤Cχ ⟨q⟩⁻¹(W(τ)+W(τ-q))`, `W=(1+s²)⁻¹`, uniformly for `a∈[0,1]`.
The proved Cauchy convolution estimates preserve finite frequency packets. Each packet
contains an actual integrable density and a proved envelope; all operations reconstruct
actual time shifts, products, modulations and cutoff time integrals by Fourier inversion
and Fubini. The feasible threshold theorem handles empty gapped domains and justifies
the lower endpoint at every vertex. Tree induction identifies every packet coefficient
with the source resonance product times a common cost, then bounds that cost by `C^n`.
No spectral input is a hypothesis of the source-facing theorem.

## Source comparison and deviations

- TARGET L2330, literal coefficient-one statement at `M=1` for “any function”, is false:
  on the unit square, `K(t,s)=1+t`, `P=1` gives supremum `4`, but the right side is
  `7/3+1=10/3`. The implementation explicitly includes constants and a sufficient
  large-exponent range. No source or frozen statement was changed.
- DH21 L2428 (10.5) has ordinary mixed derivatives; TARGET L2004 uses the covariant
  variant. Both are implemented. The cube integrals are recursively iterated integrals.
- The factorial estimate needs `d≤z` when `0≤x<1`, because natural subtraction truncates.
- The interval APIs assume a globally C¹ curve, and the cube/weighted APIs global
  smoothness, sufficient for the smooth source applications. No bridge from coordinatewise
  regularity to C¹ regularity as an ℓ²-valued curve is claimed.
- The tree theorem uses a local recursive full ternary carrier, as the brief permits.
  It is not yet transported to the future frozen combinatorial API or to the separate
  parent-map `TimeForest.integral`. The latter has its own actual domain integral,
  frequency characterization and absolute-volume estimate. These are distinct APIs.
- The source standing interval is `[0,1]` (DH21 L429). The implemented gaps may be any
  nonnegative reals, strengthening the source range `[0,1]`. Strict/non-strict endpoint
  choices have the same interval integrals. Leaf edges have no source gap or time variable.
- No other suspected source errata or mathematical uncertainties were found.

## Source-facing theorem binder comparison

This is a local source comparison, not an independent frozen-manifest audit.

| Expanded input/component | Class | Source / reason |
|---|---|---|
| Full ternary tree shape | SOURCE | DH21 Lemma 10.2, L2432–2451 |
| Real frequency at each branch | SOURCE | `α[𝒩]` in that lemma |
| Real edge gap data | SOURCE | `σ[Ξ]`, extended by zero off `Ξ` |
| Nonnegative branch gaps, recursively | SOURCE | Source gaps lie in `[0,1]`; no upper bound needed |
| Zero gaps on leaf edges, recursively | TYPING | Source gaps are indexed by branching vertices only |
| Auxiliary lower-endpoint labels | TYPING | Ignored in the source integral and resonance data |
| External real time | SOURCE | Same lemma |
| `0≤t` | STANDING | DH21 L429, all later times in `[0,1]` |
| `t≤1` | STANDING | DH21 L429 |

There are no analytic estimates, packet certificates, feasibility gates, reconstruction
premises or supplied resonance bounds in the final theorem's inputs. Counts: SOURCE 5,
STANDING 2, TYPING 2, RULED 0, EXCESS 0.

## Pinned source bytes used for comparison

SHA-256 of the local raw source files read for this packet:

- TARGET: `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb`
- DH21: `50d0e236a2df0cfd2b98bace6f0256043ee88fc05079ee44c3524ca9482fe402`
- DH19: `2cc3c13d555fcebd29e913efc47a3294fadf494c1faa60bfbb0ad56edbad6de4`

Exact source locations: TARGET L998, L2004, L2029–2036, L2314–2316 and L2330;
DH21 L429 (standing time interval), L2428 and L2432–2451; DH19 Proposition 2.3,
around L347–407. The quoted suspected defect at TARGET L2330 is “for any function
$\Ks$” following the coefficient-one display; the counterexample and precise replacement
are given above.

## Checks and output

All builds used the `wt-throttled` toolchain gate, one targeted command at a time.
Milestone checks and prior commits are recorded in `AN-SOB-PROGRESS.md` and git history.
Final commands:

1. `nice -n 5 lake build WaveTurbulence.Foundations.Analysis.PaperTimeIntegral`
   
   Output: `Built WaveTurbulence.Foundations.Analysis.TreeFrequencyScaling`,
   `Built WaveTurbulence.Foundations.Analysis.PaperTimeIntegral`,
   `Build completed successfully (3256 jobs).` No warnings.
2. `nice -n 5 lake env lean /home/scott/wt-scratch/an-sob/FinalAxioms.lean`
   
   Exit 0, no errors/warnings. It imports the four packet goal entry modules, checks
   an exact-type use of `norm_paperTimeIntegral_le` and the explicit source resonance
   recursion, and prints axioms for these fifteen exports:
   `norm_le_interval_sobolev_L2`, `norm_apply_le_interval_sobolev_L2`,
   `enorm_le_wholeSobolevL1`, `norm_le_radial_weighted_sobolev`,
   `norm_rpow_le_square_morrey_largeParameter`, `volume_orderedSimplex`,
   `volume_heapOrderRegion`, `volume_interleavedTwoChains`, `two_chain_factorial_bound`,
   `pow_div_sub_factorial_le_exp`, `enorm_le_cubeCovariantSobolevL1`,
   `IntegrationTree.paperTimeIntegral_node`, `IntegrationTree.norm_paperTimeIntegral_le`,
   `IntegrationTree.timeIntegralConstant_pos`, `IntegrationTree.card_choice`.
   
   Every output is `depends on axioms: [propext, Classical.choice, Quot.sound]`.
   No `sorryAx`, project axioms or unproved providers occur.
3. `git diff --check`: empty output, exit 0.
4. Owned Lean files: 56 modules, maximum 217 lines (well below 1500); forbidden-declaration,
   proof-hole, budget-override and quarantined-import scans returned no matches.

No mathematical uncertainty remains in these proved local statements. Transport to the future
frozen tree API, source-facing anchor selection and independent frozen statement audits belong
to the orchestrator's next campaign phase; this packet does not claim those are done.

## Integration closeout

Committed the source-convention implementation and handoff at `78cb9c8`, then merged `main`
cleanly at `6a5f625`. The merge changed neither the owned Analysis files nor their frozen
`Mom` dependency. Re-read the updated `AGENTS.md`; the area namespaces and C∞ notation
already comply. Post-merge command
`nice -n 5 lake build WaveTurbulence.Foundations.Analysis.PaperTimeIntegral` returned
`Build completed successfully (3256 jobs).` No warnings. The worktree was clean after the merge.

READY an-sob
