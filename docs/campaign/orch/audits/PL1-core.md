# Statement audit: PL1 analytic core (`Foundations/Incoh`, wt-l2s)

Auditor: `wt-orch`, refute-first, findings only. Date: 2026-11-04 (Task 26a).

**Scope.**
- The couple bounds (incohproof12)–(incohproof20) and the tree bounds (incohproof22)–(incohproof28) of
  `WaveTurbulence/Foundations/Incoh`, against TARGET L979–L1093 and the map `~/wave-turbulence/maps/T-part1.md`
  L960–L1060.
- Points checked: the exponents, the `γ₁` bookkeeping, the `𝔛^{−η}` / `𝔛^{1/4}` interpolation, the F62 squared Wick
  factor, and whether the carrier interface (`LayerLink`, `RootCoordinates`, `I`, plus the tree's `TreeClockFibers`)
  admits exactly what C2 LINKS produces.

## Verdict

**PASS WITH ONE REQUIRED COVERAGE ITEM (P-1).** Every audited bound matches TARGET, and in two places the endpoint is
better. The exponents and the `γ₁` bookkeeping add up, the interpolation is the source's, and F62 is implemented.

- **P-1 (REQUIRED).** TARGET's degenerate couple case "one of the trees of `𝒬` is trivial" (L1049) has no final
  `𝔛^η` theorem. The couple results are stated only for two root clocks.
- **Interface.** It admits C2 LINKS' outputs field by field. Two OPTIONAL items (P-2, P-3) concern instantiation
  work that remains for Stage 2.

## 1. Inputs and pins

**Code.** Commit **`fb174c5`** (branch `w/wke-l2s`; *not yet an ancestor of main* at the time of this audit). I read
all sources and its `HANDOFF.md` with `git show fb174c5:…`.

**Build snapshot.**
- I copied `/home/scott/WaveTurbulence-worktrees/wke-l2s/.lake/build/lib/lean/WaveTurbulence` (167 MB) at 03:33 UTC,
  read-only, into my scratchpad. The worktree's live build was not used.
- Checks on the snapshot:
  - all 161 Incoh modules have an `.olean` newer than their source;
  - every tracked source equals `fb174c5`;
  - the worktree head `2ab4c95` only merged main, with no Incoh change;
  - its untracked work-in-progress files are not imported by the audited modules.
- All probes below ran against this snapshot.

**Sources.** TARGET L979–L1093 (the proof of Prop 5.1), `defgamma1` (L613), `normX` / `normX1`, and the map's
T-U979 entry.

## 2. Definitions

| Lean | TARGET | Verdict |
|---|---|---|
| `incoherenceExponent d γ = min(2γ, min 1 (2(d−1)(1−γ)))` | `γ₁ = min(2γ, 1, 2(d−1)(1−γ))` (L613) | **equal** |
| `linkEpsilon x y = 1 − 1_{x=0} − 1_{y=0}` | `ε_𝔫 = 1, 0, −1` when `0, 1, 2` of `x, y` vanish (L1023) | **equal** (single node) |
| `linkWickFactor = linkEpsilon²`, used by `linkAmplitude` | the true per-link factor `ε_𝔫ε_{𝔫'} = ε_𝔫²` (F62) | **F62 implemented** |
| `linkPhase = ⟨x, ξ⟩ + ⟨y, ξ'⟩ + s⟨x, y⟩`, with `x, y = latticePoint L p` | `e[s⟨x,y⟩ + ⟨ξ,x⟩ + ⟨ξ',y⟩]`, `(x, y) ∈ ℤ_L^{2d}` (incohproof10) | **equal** |
| `linkTimeFactor`: `s = ζ·δL^{2γ}(t₀ − t₁)` | `s_𝔫 = ζ_𝔫δL^{2γ}(t_𝔫 − t_{𝔫'})` (L1029) | **equal** |
| `kineticLinkScale = δ⁻¹L^{2(d−γ)}` | the per-link scale of (incohproof13)–(incohproof16) | **equal** |
| `normalizedLinkIntegral = (δ/(2L^{d−γ}))^{2n} ∫_I ∏ linkTimeFactor` | (incohproof9), without the unit `ζ(𝒬)` | **equal** (a unit factor does not change norms) |
| `Fourier.timeFourierNorm θ f = ∫ timeBracket(ξ)^θ \|f̂(ξ)\|` | `𝔛^θ` (normX1) | **equal** (`timeBracket ξ = max(1, maxⱼ⟨ξⱼ⟩) = maxⱼ⟨ξⱼ⟩`; Mathlib's `e^{−2πi⟨ξ,t⟩}` transform) |
| `mixedFourierNorm00 θ F = ∫ timeBracket^θ · sup_v \|F̂(ξ, v)\|` | `𝔛^{θ,0,0}` (normX), with `L^∞_k` inside the `λ` integral | **equal** |
| `timeRestrictionNorm θ B f = inf` over extensions | the norm on `ℬ`, via an extension (L995) | **equal** |

## 3. The couple bounds (incohproof12)–(incohproof20)

Write `λ := δL^{2γ}`. Every principal result has the standard axioms only (§6).

| TARGET | Lean | Check |
|---|---|---|
| (12): replacing `ε_𝔫` by 1 costs `𝒪₀(L^d)` | `norm_linkLatticeSum_sub_bilinear_le`: `‖S − S_bilin‖ ≤ 2(5L)^d` | **equal**. The squared factor differs from 1 only on the two axes minus the origin. |
| (13): `‖S·1_{\|s\|≥L}‖_{L¹(ℬ)} ≲₂ δ⁻¹L^{2(d−γ)}L^{−2(d−1)(1−γ)+η}` | `exists_longTime_box_bounds`: `≤ λ⁻¹·C·L^{2d−2(d−1)(1−γ)+η}`, `C = C(γ, η, T)` | **equal**: `λ⁻¹L^{2d} = δ⁻¹L^{2(d−γ)}`, and `T` plays the role of `𝔇δ` (`≲₂`). |
| (14): `‖S·1_{\|s\|≤L}‖_{L¹} ≲₀ δ⁻¹L^{2(d−γ)}` | `exists_shortTime_box_bounds`, first part: `≤ λ⁻¹·C·L^{2d}`, `C = C(d)` | **equal** |
| (15), incoherent link: `≲₂ δ⁻¹L^{2(d−γ)}L^{−2γ}` | second part: `≤ λ⁻²·C·L^{2d}` | **equal.** `λ⁻²L^{2d} = δ⁻¹L^{2(d−γ)}·δ⁻¹L^{−2γ}`; Lean keeps `δ⁻¹` explicit, which TARGET absorbs into `C₂`. |
| (16): `∫∏\|S\| ≤ C₀ⁿC₂^g δ^{−n}L^{2(d−γ)n}L^{−(γ₁−η)g}` | `exists_linkProduct_decay`: `‖∫_I ∏ linkTimeFactor‖ ≤ (C₀·δ⁻¹L^{2(d−γ)})ⁿ C₂^g L^{−(γ₁−η)g}`. `C₀ = C₀(d)` is chosen before `γ, η, δ, D`, and `C₂ = C₂(γ, η, δ, D)` | **equal.** The hypotheses are the layer range `\|𝔏 − 𝔏'\| + 1 ≤ D` and `I ⊆ ∏ linkBox` (incohproof11). |
| (18), L¹: `‖𝒮‖_{L¹} ≤ (C₀δ)ⁿL^{−(γ₁−2η)g}` | `exists_normalizedLinkIntegral_bound`: `(C₀δ)ⁿ L^{−(γ₁−2η)g}` | **equal**: `(δ/2L^{d−γ})^{2n}·δ^{−n}L^{2(d−γ)n} = (δ/4)ⁿ`, and `C₂^g ≤ L^{ηg}` is absorbed for `L ≥ L₀`. |
| (18) + interpolation to `L^{1+3η}` | `exists_rootDensity_Lp_bound`: `‖R.linkDensity‖_{L^{1+3η}} ≤ (C₀δ)ⁿ L^{−(γ₁−8dη)g}`, given `1 ≤ g` | **consistent.** The `L^∞` loss `L^{2d}` is a single factor, so interpolation costs `L^{2d·3η/(1+3η)} ≤ L^{6dη} ≤ L^{6dηg}`, and `2η + 6dη ≤ 8dη`. |
| (19)–(20): `‖K̃_ext‖_{𝔛^η} ≲₁ (C₀δ)ⁿL^{−(γ₁−100dη)g}` | `exists_coupleExtension_timeFourier_bound` (the literal cutoff extension, for **every** smooth compactly supported `χ`) and `exists_cumulativeKernel_timeRestriction_bound` (the restriction norm of the literal cumulative kernel on the root box): `≤ (C₀δ)ⁿ L^{−(γ₁−100dη)g}` | **equal**, and stronger: no `≲₁` constant (absorbed into `L₀`), and every cutoff rather than "suitable" ones. `η ≤ 1/3` and `η < γ₁` are the smallness conditions. |

**The `γ₁` bookkeeping.**
- `γ₁` collects three gains, each proved below `incoherenceExponent` (`incoherenceExponent_le_two_mul`,
  `_le_longGain`, `_le_one`):
  - `2γ` from (15);
  - `2(d−1)(1−γ)` from (13);
  - `1` from the Wick correction, since `L^d / L^{2(d−γ)} = L^{−(d−2γ)} ≤ L^{−1}` for `d ≥ 3`.
- The losses: `η` in (16), `2η` in (18), `8dη` after the `L^p` interpolation and `100dη` at the end. These match the
  source's chain (16) → (18) → (20).

## 4. The tree bounds (incohproof22)–(incohproof28)

**The carrier `TreeClockFibers m Q`.**
- `m = 0` is (incohproof22): `𝔯' = 𝔲`, two selected clocks. `m = 2` is (incohproof23): `𝔯, 𝔯', 𝔲', 𝔲` nested,
  four clocks. The theorem allows `m ≤ 2`.
- The source's variant "some bounds replaced by a constant integer `r` with `q ≤ r ≤ q'`" is covered by the
  arbitrary measurable `lower` / `upper` fiber endpoints.
- The parameters may depend on `k`: `Q : Mom d → Fin n → LayerLink d` and `T : (k : Mom d) → TreeClockFibers m (Q k)`.
  This is the source's "allowed to depend on `k`" (L1066). The selected link set is fixed across `k`, which is
  structural.

**(26), negative endpoint.** TARGET: `‖·‖_{𝔛^{−η,0,0}} ≲ (C₀δ)ⁿL^{−(γ₁−2dη)g}`. The Lean endpoint is internal to
`exists_treeCausalExtension_decay` (bulk loss `2ηg`, per the handoff) and is consistent with this.

**(27)–(28), quarter endpoint.**
- `exists_treeCausalExtension_quarter_bound`: `𝔛^{1/4,0,0} ≤ C·(C₀δ)ⁿ L^{−(γ₁−2η)g}·L^{2d}`.
- TARGET has `L^{−(γ₁−100dη)g}·L^{4d}`. The Lean endpoint is **better** in both factors.
- The terse "replace `𝒮₀` by a pure phase at loss `L^{4d}`" and the hard-indicator derivative of (27) are done
  rigorously: an expansion into selected-link phases, then smooth windows passed to the hard indicators by dominated
  convergence and Fatou.

**Interpolation.**
- `mixedFourierNorm00_le_of_tree_endpoints`: `𝔛^{−η} ≤ M` and `𝔛^{1/4} ≤ M·L^{2d}` imply `𝔛^η ≤ M·L^{16dη}`. This is
  the source's interpolation of (26) with (28).
- The weight is `treeInterpolationWeight η = 2η/(1/4 + η) ≈ 8η`, so the loss is `L^{2d·8η}`. This is the map's check:
  the source's `L^{4d}` would give `L^{32dη}`.
- `tree_interpolation_scale_le` (with `C ≤ L^{ηg}` and `g ≥ 1`):
  `−(γ₁ − 2η)g + ηg + 16dη ≤ −(γ₁ − 100dη)g`.

**(24), final.** `exists_treeCausalExtension_decay`: `𝔛^{η,0,0}` of the literal tree causal extension
`≤ (C₀δ)ⁿ L^{−(γ₁−100dη)g}`. The conditions are `g ≥ 1`, `0 < η ≤ 1/100`, `η < γ₁`, and cutoffs equal to 1 on the
root and selected boxes. **Equal to (incohproof24).**

## 5. The carrier interface against C2 LINKS

Checked against `LINKS-prefreeze.md` and LINKS' exports:

| Interface field | Supplied by C2 | Verdict |
|---|---|---|
| `Q : Fin n → LayerLink d`, `n` = the number of links | `Q.links`, with `n = \|𝒩^ch\| = size/2` (`card_chosenSet`) | admits |
| `leftLayer`, `rightLayer : ℤ` | `layerAt LG (link).1`, `.2`, cast from `ℕ` | admits |
| `orientation : ℤˣ` | `ζ` of the chosen node, `(Q.links.get j).1`. The time difference is `t_left − t_right`, chosen minus partner; with `zeta_omega_link` and `omegaNode_eq` (`Ω = 2⟨x,y⟩`) this is the source phase | admits |
| per-link `(x, y) ∈ (ℤ^d)²` summed independently | `linkCoords`; `incoh_unimodular`, `decEquiv` and `linkCoords_surjective` turn decoration sums into independent link sums | admits (Stage 2 assembles it) |
| `∏ linkWickFactor` | `epsDec_eq_prod_links`: `ε_ℐ = ∏_j epsXY(x_j, y_j)²`, with `epsXY ≡ linkEpsilon` (same values, same carrier) | **admits exactly** |
| `incoherenceCount Q` | `incoherency_eq_count` (list filter), then a one-line `Finset` conversion | admits |
| `RootCoordinates n` (two root clocks) | the two tree roots as (link, endpoint) positions, through `exists_unique_link`. For type 1 both roots lie in one link, which the permutation allows. | admits, **except a trivial tree** (P-1) |
| `I`, `MeasurableSet I`, `I ⊆ ∏ linkBox` | B1's kernel time domain with layer boxes (incohproof11), in link coordinates. Measurability is a finite intersection of half-spaces and boxes | admits. A Stage-2 obligation; not C2 data. |
| `LinkParameters` (centres, shifts) | localization (treelemma (2) = LINKS `explem_one`) and the Fourier expansion of `W` (incohproof6) | free parameters; see P-2 |
| tree: `TreeClockFibers` | LINKS `tree_exists_unique_link`, ENHANCED `tree_incoh_unimodular`; the root and `𝔲 = 𝔫_lo^pr` cases | admits. The null-boundary identification of closed and half-open conventions is an acknowledged C2/Stage-2 obligation (handoff). |

Every hypothesis of the final couple and tree theorems is dischargeable from C2 data plus B1's kernel definition:
- `1 ≤ g`, PL1's own premise;
- the layer range `≤ D`, with `D = 𝔇 + 1` since every layer is `≤ p ≤ 𝔇`;
- measurability and box containment of `I`;
- the alignment of root and lone-parent clocks;
- cutoffs equal to 1 on the boxes.

No analytic estimate is a hypothesis.

## 6. Checks

**Axioms**, re-run against the snapshot: `[propext, Classical.choice, Quot.sound]` for `norm_linkLatticeSum_sub_bilinear_le`,
`exists_longTime_box_bounds`, `exists_shortTime_box_bounds`, `exists_linkProduct_decay`,
`exists_normalizedLinkIntegral_bound`, `exists_rootDensity_Lp_bound`, `exists_coupleExtension_timeFourier_bound`,
`exists_cumulativeKernel_timeRestriction_bound`, `exists_treeCausalExtension_quarter_bound`,
`exists_treeCausalExtension_decay`, `mixedFourierNorm00_le_of_tree_endpoints`, `tree_interpolation_scale_le` and
`exists_selectedDensity_bound`.

**Statements.** All printed with `#check @…` from the snapshot.

## 7. Findings

**P-1 (REQUIRED before PL1 Stage 2/3 closes `proplayer1`). The couple case with a trivial tree is not covered.**
- TARGET (incohproof17) L1049: "one or both of the integrations … may be taken on a unit interval independent of
  `t` (or `s`) … including the case when one of the trees of `𝒬` is trivial, the function `K̃(t,s)` will not depend on
  `t` (or `s`)".
- If the `−` tree is a single leaf (type 2 with `m₋ = 0` and trivial `𝒬_lp`), there is no second branching root clock.
  The couple theorems (`exists_coupleExtension_timeFourier_bound`, `exists_cumulativeKernel_timeRestriction_bound`)
  take `R : RootCoordinates n`, whose root count is fixed at `r = 2`, and do not apply.
- The other degenerate layerings (a root box lying wholly below `t`) are covered, because `cumulativeKernel` cuts by
  `I ∩ rootCut t`.
- Only the pointwise density bound `exists_selectedDensity_bound` is stated for general `r`.
- **Needed:** a one-clock (`r = 1`) version of the couple extension bound, or an explicit reduction (extension
  `χ(s)·f(t)`, with `‖χ ⊗ f‖_{𝔛^η} ≤ ‖χ‖_{𝔛^η}‖f‖_{𝔛^η}`), with the same exponent.

**P-2 (OPTIONAL, Stage 2). The localization scale.**
- The core takes any centres `a_𝔫, b_𝔫` with the fixed cutoff `χ₀(x − a)χ₀(y − b)`. The source needs
  `|x_𝔫 − a_𝔫|, |y_𝔫 − b_𝔫| ≤ 1/2` (L1005).
- LINKS' `explem_one` / `treelemma_two` gives each `k_𝔫` in a fixed **unit** ball. So `x_𝔫 = k_{𝔫1} − k_𝔫` lies in a
  radius-2 ball, which needs a further finite (`C^n`) cover to reach the cutoff's scale.
- This is a routine Stage-2 step, worth stating where the localization is assembled.

**P-3 (OPTIONAL). Mapping the global sign.** The unit `ζ(𝒬)` / `ζ(𝒯)` is not carried, which is harmless for norms. The
Stage-2 identity with B1's `KQstar` / `KTstar` must still carry it, which ties to ENHANCED E-3 (`zetaOfTrees` vs
`Garden.zeta`).

**Notes (no action).**
- The only source erratum used is F62, and it is implemented exactly.
- The hard-indicator derivative step of (incohproof27) is replaced by a documented uniform first-variation argument,
  a rigorous reading of a terse step rather than an erratum.
- The final couple bound has no `≲₁` constant; it is absorbed into `L₀`.
