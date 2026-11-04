# A23-HALF handoff — DH23 Lemma A.2(3), γ > 1/2, saving κ(γ) = min((2γ−1)/3, 1−γ)

Packet A23-HALF (brief `docs/campaign/briefs/A23-HALF.md`). Branch `w/approxnt`, worktree `torus-fourier`.
Commits: `bc9a635`, `68b3234`, `4de4ccd` (these three already landed in main `37ba0aa`), `d709a3c`,
`018d643` (merge of main `37ba0aa`), `b188938`. Namespace `WaveTurbulence.CountLemmas`.

## Main results

Here `τ = δ⁻¹L^{-2γ}`, `γ₀ = 1 − γ` and `κ(γ) = kappaHalf γ = min((2γ−1)/3, 1−γ)`.

**Item 1, the counting input of F75** (`A23Half.lean`). This is DH23 (countc2-1) second line, with `κ(γ)` in place
of `10η`, for every selector `ζ ∈ {x−v, x+y−v, x+y−v−z}` of the landed `coupledTripleSet`, the `𝒞₂` of
(basiccount02):

```lean
theorem a23Half_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (1 / 2 : ℝ) 1 → ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1,
      ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ ax ay az : Mom d, ∀ nv : Fin d → ℤ, ∀ α β : ℝ, ∀ ζsel : Fin 3,
        ((coupledTripleSet L ax ay az (latticePoint L nv) α β (δ⁻¹ * L ^ (-2 * γ)) ζsel).ncard : ℝ) ≤
          C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - (1 - γ) - kappaHalf γ)
```

**Item 1, the system `{(1,2,3),(1,4,5)}` of DH23 Lemma A.3(4)** (L2106), through Lemma 2.1
(`A23HalfReparam.lean`):

```lean
theorem system12345_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (1 / 2 : ℝ) 1 → ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1,
      ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ (a : Fin 5 → Mom d) (εA εB : Fin 3 → ℤˣ),
        ¬ (εA 0 = εA 1 ∧ εA 1 = εA 2) → ¬ (εB 0 = εB 1 ∧ εB 1 = εB 2) →
        ∀ (nA nB : Fin d → ℤ) (βA βB : ℝ),
          ((system12345Set L a εA εB nA nB βA βB (δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) ≤
            C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - (1 - γ) - kappaHalf γ)
```

`system12345Set` is DH23 (counteqn) for the tuples `A = (1,2,3)` and `B = (1,4,5)`, in integer coordinates
(`k_j = n_j/L`, `|k_j − a_j| ≤ 1`). Each tuple has the conservation law `Σ εᵢ n_{jᵢ} = n_k` and the energy window
`|Σ εᵢ |k_{jᵢ}|² − β| ≤ τ`.

**Item 2, the reparametrization identities** (Lemma 2.1, `A23HalfReparam.lean`):

- `reparam_energy_identity`: `|kᵢ|² + |kⱼ|² − |kᵢ + kⱼ − k|² = |k|² − 2(kᵢ − k)·(kⱼ − k)`.
- `tupleEqn_normalize`: each of the 6 sign triples without three equal signs becomes, after multiplying by `s = ±1`,
  the normalized tuple `k_p + k_q − k_o = k` (`NormTuple`). When `k₁` is not odd, it is listed first.
- The four forms are the injections `(k₁, …, k₅) ↦ (x, y, z)` into `coupledTripleSet`:
  - `ncard_le_coupled_cyclic`, form (i): `k₁` odd in both tuples, `ζ = x + y − v − z`.
  - `ncard_le_coupled_mixed`, forms (ii) and (iii): (iii) is (ii) with the tuples exchanged and `v ↦ −v`;
    `ζ = x + y − v`.
  - `ncard_le_coupled_anti`, form (iv): `k₁` odd in neither tuple, `ζ = x − v`.
- `system12345_bound` dispatches the 9 combinations (odd entry of `A`) × (odd entry of `B`). Each combination occurs
  for 4 raw sign pairs, so all 36 non-monochrome pairs are covered.
- `card_admissible12345` (proved by `decide`): exactly **18** pairs satisfy DH23's sign rules (L2096). See erratum E1.

## Files (`WaveTurbulence/Foundations/CountLemmas/`)

| File | Lines | Content |
|---|---|---|
| `A23HalfShell.lean` | 162 | `supNat`, `intBox`; the shell sum `Σ_{0<supNat X≤R} supNat⁻² ≤ 2d·3^{d−1}R^{d−2}` |
| `A23HalfFibers.lean` | 197 | fibres `ysF`/`zsF`; `#S = Σ_X N_y N_z` for `ζ = x − v`; strip bound (P); bilinear sums `≲ τL^{2d}` |
| `A23HalfDense.lean` | 206 | estcross at unit scale; layer cake; `Σ_{k>k₀} k⁻² ≤ k₀⁻¹`; the dense sum |
| `A23HalfStar.lean` | 237 | the small region `supNat X < ρ` or `supNat(X − n_v) < ρ` |
| `A23HalfBig.lean` | 152 | `denseBound`, `sum_big_le`, `sum_star_le` (small + sparse + dense) |
| `A23HalfAnti.lean` | 318 | `kappaHalf`; `coupledTriple_star_bound_half` (`ζ = x − v`, saving `κ(γ)`) |
| `A23HalfCyclic.lean` | 189 | `coupledTriple_sum_bound_half` (`ζ = x+y−v`, `x+y−v−z`, saving `(2γ−1)/3`, `γ ∈ [1/2, 1]`) |
| `A23Half.lean` | 77 | `a23Half_bound` |
| `A23HalfReparam.lean` | 352 | Lemma 2.1 and `system12345_bound` |

Landed inputs reused:

- `exists_broad_bilinear_band_bound` (bilinear count);
- `positive_atom_shell_threshold_bound` (2/3 circle exponent, thin annuli);
- `Counting.card_dense_dot_product_strips_in_balls_le` (estcross, `Counting/EstcrossBalls`);
- `card_dot_strip_ball_le` (`DotStrip`);
- `Counting.card_le_image_card_mul_of_fiber_le`;
- `latticePoint_one_eq_smul` (`PositiveAtomReduction`);
- `WeylSums.latticePoint_add_eq` and `WeylSums.latticePoint_sub_eq`;
- `finite_coupledTripleSet`;
- the `PolynomialGrowth` big-O calculus, including `growth_log_sq`;
- `eventually_monomial_log_le` (`PowerAbsorption`).

## Approach

The referee's proof, §4.3 of `docs/research/case4-gamma-above-half-referee.txt`.

**Sum selectors** (`ζ = x + y − v` and `ζ = x + y − v − z`):

1. Project to `(x + y, z)` and count the projection with the broad bilinear band, `≲ τL^{2d}`.
2. At fixed sum, `x` lies on a same-sign atomic shell. The 2/3 circle-discrepancy threshold with
   `U = 2δ⁻¹L^{(4−2γ)/3}` gives `≲ L^{d−2}U`.
3. The saving is `(2γ−1)/3`.

**Anti-parallel selector** (`ζ = x − v`): `#S = Σ_X N_y(X) N_z(X)`.

- *Small region* (`supNat X < ρ` or `supNat(X − n_v) < ρ`, with `ρ = τL²`): use `(1+a)(1+b) ≤ 2 + a² + b²` and the
  shell sum.
- *Sparse part* (`N < k₀ = ⌈L^{d−1−κ}⌉`): bounded by `k₀ Σ N ≤ 4C δ⁻¹ L^T`. This is the critical term.
- *Dense part*: use `N_y N_z ≤ M·N_y`, a layer cake, and estcross at `θ = max(1, L^{d−1}/k)`.

The non-sparse terms are `O(L^{T − gap/2})` with `gap = min(1−γ, (2γ−1)/3)`; the estcross `(1 + log L)²` factors are
absorbed there. Here `T = 3(d−γ) − (1−γ) − κ`.

**System count**: normalize each tuple, inject into `coupledTripleSet` by the form that applies, and apply
`a23Half_bound`.

## Checks run (after merging main `37ba0aa`, at `b188938`)

- `nice -n 5 lake build WaveTurbulence.Foundations.CountLemmas.A23HalfReparam`, which imports every A23Half module:
  `Build completed successfully (9229 jobs).` No errors and no warnings, including replayed ones.
- `#print axioms` via `lake env lean` on a scratch file. Each of the following gives
  `[propext, Classical.choice, Quot.sound]`:
  - `system12345_bound`, `a23Half_bound`;
  - `coupledTriple_star_bound_half`, `coupledTriple_sum_bound_half`;
  - `card_admissible12345`, `reparam_energy_identity`, `tupleEqn_normalize`;
  - `ncard_le_coupled_cyclic`, `ncard_le_coupled_mixed`, `ncard_le_coupled_anti`.
- Forbidden-token grep over `A23Half*.lean` (`sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `maxHeartbeats`,
  `maxRecDepth`, `synthInstance`, `native_decide`, `Frozen.Theorems`, `Provider.`): no hits.
- The largest file has 352 lines. Every file has copyright, `module`, `public import`, a docstring and
  `public section`. `git diff --check` is clean.
- Duplicate-name scan over `WaveTurbulence/**/*.lean`, and against `main`: no duplicate declarations. `intBox` occurs
  as `WaveTurbulence.ApproxNT.intBox` (`ApproxNT/Cells.lean`) and as `WaveTurbulence.CountLemmas.intBox`. There is no
  clash unless a file opens both namespaces.

## Axioms

Only `propext`, `Classical.choice` and `Quot.sound`.

## Uncertainties

None mathematical.

- Quantifiers: `C` is independent of `δ`, and `L₀` depends on `δ`. This is the same order (`∃ C, ∀ δ, ∃ L₀`) as the
  landed `countLemma_bound`.
- The endpoint `γ = 1/2` is excluded, because `κ(1/2) = 0`. The sum-selector bound itself holds on `[1/2, 1]`.

## Errata and deviations

- **E1 (referee check 4.2 and the brief): "16 admissible sign patterns" should be 18.**
  - Count: 2⁵ sign choices for `(ε₁, ε₂, ε₃, ε₄, ε₅)` once `k₁`'s sign in `B` is fixed as the opposite of its sign
    in `A`. Remove the 8 with `A` monochrome and the 8 with `B` monochrome, and add back the 2 with both monochrome:
    32 − 8 − 8 + 2 = 18.
  - Lean: `card_admissible12345`, by `decide`.
  - The referee's own `check_reparam.py` (`/home/scott/wt-scratch/case4-referee/out_check_reparam.txt`) tests 18
    patterns: its form tally 400 + 800 + 800 + 1600 = 3600 = 18 × 200 instances. Only the text is wrong.
- **E2 (DH23 L2110, already in `CountLemmas/HANDOFF.md`).** `|k₁|²−|k₂|²+|k₃|²−|k|² = 2(k₁−k)·(k₃−k)` should have
  factor **−2**. Reconfirmed as `reparam_energy_identity`.
- **E3 (observation, DH23 L2096).** The rule that `k₁` has opposite signs in the two tuples is not needed for the
  count. `system12345_bound` holds for all 36 non-monochrome sign pairs; only "no tuple has three equal signs" is
  used.
- **D1.** The saving is stated as `κ(γ)`, not `10η`, as the brief asks. DH23's `L^{−10η}` follows whenever
  `10η ≤ κ(γ)`.
- **D2. No log factor.** This is stronger than "up to logs".
  - `4de4ccd`, which has landed, stated `a23Half_bound` and `coupledTriple_star_bound_half` with an extra
    `(1 + log L)²`. `b188938` removes it.
  - Landing note: these two declarations changed type, and are strictly stronger. No consumer exists in main,
    in this branch or in `wt-scratch`.
- **D3.** Thin annuli use the landed 2/3 circle exponent (`positive_atom_shell_threshold_bound`), not the
  `Improved*` 27/41. The brief allows this, and it gives exactly `(2γ−1)/3`.
- **D4.** The anti-parallel dense part uses a layer cake over levels `k`, with estcross at `θ = max(1, L^{d−1}/k)`,
  instead of the referee's dyadic `θ`. It gives the same bound.
- **D5.** The second system of Lemma A.3(4), `{(1,2,3),(1,2,4,5)}`, is not formalized. DH23 says it "follows as a
  consequence" (L2110), and the brief asks only for `{(1,2,3),(1,4,5)}`.
- **D6. Carrier.** Integer indices `n_j` with `k_j = n_j/L`, and the tuple law `Σ εᵢ n_{jᵢ} = n_k`. This is
  equivalent to `Σ εᵢ k_{jᵢ} = k` for `k = n_k/L`, and is the same convention as the landed `atomPairSet` and
  `atomTripleSet`. Both tuples use the window `τ = δ⁻¹L^{−2γ}`, as in (counteqn).

## For consumers (F75, case (4) of DH23 Prop 9.6)

- N1 of the research note §8 is `a23Half_bound`: it replaces the second line of `countLemma_bound` for `γ > 1/2`.
- N2 is `system12345_bound`.
- At `T \ l*`:
  - the cyclic orientation is form (i), `ncard_le_coupled_cyclic`;
  - the anti-parallel orientation is form (iv), `ncard_le_coupled_anti`.

READY a23-half
