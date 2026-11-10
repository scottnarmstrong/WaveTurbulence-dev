# FINALCOUNT part G2 (DH23 Prop 9.4, excessprop1) - handoff, session 4 (2026-11-04)

**Status: STOPPED on the single-vine label count only** (see "Vine count: what is missing"). Everything else of Prop 9.4 is proved:
single cuts (alpha, beta), triangles (all four alpha/beta cases), the generic vine reduction, the vine arithmetic and the label count of a VC
formed by two double bonds (`prop94_vine_double_full`, unconditional). The single-vine statement `prop94_vine_single` is **conditional on the named count input**
`VineCountInput` (defined in `Prop94Statement.lean`).

## Statement file: `Prop94Statement.lean` (namespace `WaveTurbulence.FinalCount`)
Per constructor of `Stage2Op` (`Prop94Ops.lean`; `.post` is the post molecule), all with conclusion
`IsDeviation (M.countA ..) (op.post.countA ..) (ofReal (C * excessRHS L g eta alphaLabels DeltaF DeltaVbeta))`:
* `prop94_alpha` (cut, alpha: labels `[(R,k),(R,k)]`, DeltaF = DeltaVb = 0), hypothesis `hι : κ = 50 → IotaReading ..` (no `hball`).
* `prop94_beta` (cut, beta: `[]`, 1, 2); `n_sub <= (log L)^c` (`hn`).
* `prop94_triangle` (`T.alphaLabels`, `DeltaF = F(kept)-F(M)`, `DeltaVb = 3-|alphaLabels|`), `hι0`, `hι1`, `hnz`.
* `prop94_vine_single` (VC = a single vine with m atoms, labels `[(R,k),(R,k)]`, 0, 0) and `prop94_vine_double`
  (VC formed by two double bonds), **given** `hcount : VineCountInput ..` / `VineCountInputDouble ..`.
Constants: alpha `26*5^d*((8/η)^4+(8/(1-γ))^4)`, beta `10((c+4)/(η²-η³))^(c+4)`, triangle `triConst`, vine single
`Cf*2^d*((e+9)/(2η-η³))^(e+9)`, vine double the same times `(1+δ⁻¹)`.

## Files
Scratch `<scratch>/finalcount/` (namespace `WaveTurbulence.FinalCount`, `WaveB2Draft.Molecules` from lg-spine),
`build.sh <Module>`, `rebuild.sh <modules topological>` (fresh dir `build-fresh`). Session 3 and earlier modules are listed in
PROGRESS.md; session 4 added: Prop94Iota, VineRank2, VineArith, VineArith2, VineExcess, VineExcess2, VineExcess3, VineExcess4,
VineExcess5, Prop94Statement.

## Vine count: what is missing (the reason for STOPPED)
`VineCountInput` = for every `ParamOK` parameter triple, `encard (K.labelSet ..) <= Cf L^d (ρL)^d L^{(m-2)(d-γ)} δ^{-m/2} (log L)^e / ∏_{𝕃_j ⊂ VC} 𝔛_j^{z_j}`
(DH23 L1799-L1801). It is the only unproved ingredient of Prop 9.4. Proving it needs, beyond
VINEPARAM (`<scratch>/vines/src/Contract.lean`, sha256 cd16890b2a057220a69846a4c855fdbb69462e493e8605e9c8fde6a51bb62bd3, `FullVineChart`,
`VINEPARAM`, `vineparam_of_base` in VineParamFinal.lean) four things that the contract does NOT provide:
1. **Universe port.** The contract is stated for `MoleculeDefs.Molecule` (vines/mole universe); our `Molecule` is `WaveB2Draft.Molecules` (same text, different
   declarations; they cannot be imported together). Needs the mechanical port of `Contract.lean` + `IsVine` to `WaveB2Draft`, as at seal time.
2. **Ladder-chart link (the real gap).** The gain `∏ 𝔛_j^{-z_j}` needs, for every maximal ladder `𝕃_j ⊂ VC` of the B2 `maximalLadders` (with its gap `|r_j| ~ P(𝕃_j)`),
   (a) which chart rung pairs `(x_j,y_j)` (`rung_bonds`, `xSlot/ySlot`) are its rungs, (b) that its gap is the chart's `r` (or `0`, "zero-gap normal ladders may use zero
   coefficients", CONTRACT.md L48), so that the rung system is `S₁` of `countLemma_bound` with `Pr = P(𝕃_j)`. The contract has `ζc`, `ζ_unit`, `ζ_bad_nonzero` for the
   rung phases but nothing about maximal ladders; core double bonds of types IV-VIII (`uSlot`) can also be double bonds without being rungs. Without (a),(b) one only gets
   `𝔛(R)^{-(#rungs)}`, and `∏ 𝔛^z <= (log L)^{2z}` is not polylog for long ladders. This needs either a contract field or a per-type template analysis.
3. **Degree facts.** `c_v = 0` at interior vine atoms needs `M.deg v = 4` for `v ∈ C.atoms \ {upper,lower}` (true from the templates, `VineDegreeRange.lean`; not in the contract),
   and the identification of the VC darts of `K.cutMol` with the chart's `internalBondSet` (joint degree `2` inside the VC, flows `incidence`/`dartSign`).
4. **Counting assembly.** `labelSet` injects into `(g-shift x0 slot in a unit box) x (r in a ball: alphaN/ball_of_iota) x ∏ rung systems x core system`;
   per rung `countLemma_bound` part 1 (with `Pr`), the core `part 2`, signs `ζ` handled by `y -> -y`, then the product bound `vineF`. About 1500+ lines.
The previous notes' "(κx₁,κx₂) ranges over a box times an alphaN ball" is right (`card_alphaN_le`), and `Δχ=-m` is proved (`VineCut.circuitRank_diff_card`).

*Two double bonds: DONE.* `prop94_vine_double_full` (Prop94Statement.lean) is unconditional (modulo the source facts listed there). Files: VineDouble1 (`DoubleShape`:
`C.atoms = {a,x,b}`, `M.dartsAt x` = the four mates of `x₁,x₂,y₁,y₂`; directions from `IsCutData`), VineDouble2 (conservation at `x`: `k_{x₁}-k_{x₂}+k_{y₁}-k_{y₂}=0`, integer form,
`Γ_x = 2⟨r, (k_{x₁}-k_{y₁}) - r⟩`), VineDouble3 (`restrS κ` determined by `(κx₁,κx₂,κy₁)`), VineDouble4 (injection of `labelSet` into a finite set of triples: box x gap ball x energy strip),
VineDouble5 (cardinality, using `CountLemmas.card_dot_strip_ball_norm_le`; `card_slabF` of TriLattice is too weak, it lacks the `1/|r|`), VineDouble6 (the real bound by `vineG`, `Cf = 9^d 5^d (2d)`, `e = 0`),
VineDouble7 (`DoubleShape.labelSet_le_vineG`). Extra source facts used: label `R/2 <= |r| <= 2R` (`hlow`, `hgap`), `L⁻¹ <= ρ` for `κ = 50`, `B_VC = 4`, no ladder in the VC, `ΔF = 0`.
The shape `DoubleShape` is a hypothesis (Prop `subsetvc`: "the adjoint of two double bonds"; it is not derived from `IsVC`/`Chain` of two type-I vines).

## Readings (all with line numbers)
* **L1789 (alpha-cut count).** The source writes `(RL)^d(1+RL^{2γ})`; the count is `(RL)^d (1+δ R L^{2γ})`. Harmless as `δ <= 1`; constants depend on `δ` (source: `≲` may depend on `C⁺, δ`).
* **L1801 (the fixed ball for `ι_v ≠ 0`).** "the corresponding gap `r` must belong to a fixed ball of radius `L^{-50η}R`": the ball is centred at `s·c_{v'}`, the charge of the earlier cut atom `v'`
  (`r'` of the earlier cut = charge of the degree-2 cut atom, up to sign), a *parameter* of the molecule, not of the decoration. So the source's "`0<|r±r'| <= L^{-50η}R_v`" (L1782) is the
  hypothesis `IotaReading M L w Adm x₁ x₂ ρ` (Prop94Iota.lean): `∃ v' ∈ atoms` balanced (`∑ ζ = 0`), sign `s=±1`, and for every admissible decoration `0 < ‖gap - s·charge(v')‖ <= ρ`.
  `ball_of_iota` derives the old per-parameter `hball` (centre `s·c(v')`, from `IsDecoration`), so **`hball` is gone from the final statements**. `iota_radius_ge`: `L⁻¹ <= ρ` (from `0<|r±r'|` and
  `r±r' ∈ L⁻¹ℤ^d`) when some decoration is admissible; the vine wrappers carry `L⁻¹ <= L^{-50η}R` for `κ=50`, which is exactly this (without it the vine target fails for balls smaller than the lattice spacing:
  e.g. `ρL<1`, `R=1/L`, `d=3`: the second term `δ⁻¹R⁻¹L^{γ-d}` exceeds `R²L^{γ-97η-η³}` by `L^{97η}`).
  The alpha-cut and triangle arithmetic did not need `L⁻¹ <= ρ` (`η <= (1-γ)/200` handles it).
* **Triangle alpha/beta labelling (L1777-L1779).** Source: `v_3` beta; `v_j (j=1,2)` alpha (resp. beta) if in the same (resp. different) component as `v_3`, except if `v_1,v_2` are in the same component
  different from `v_3`: then `v_1` alpha, `v_2` beta. Lean: sequential cuts `v_1,v_2,v_3` with `α_j := IsAlphaCut`. Components are those of the kept molecule (triangle removed), partition `P` of `{1,2,3}`.
  Cut 1 is alpha iff `v_1'` stays connected to the blob `{v_2,v_3}` (joined by `ℓ_1`) iff the block of `1` in `P` has size >= 2; cut 2 is alpha iff `v_2'` is connected to the triangle blob, whose only external
  attachment is `v_3'`, iff `2 ~ 3`; cut 3 is always beta (the triangle is then a whole component). Five partitions:
  `{123}`: alpha,alpha / source alpha,alpha. `{1|23}`: beta,alpha / beta,alpha. `{2|13}`: alpha,beta / alpha,beta. `{3|12}`: alpha,beta / alpha,beta (the exception clause). `{1|2|3}`: beta,beta / beta,beta.
  All five agree. `DeltaF = F(kept)-F(M)` = 0,1,1,1,2 resp.; `DeltaVb = DeltaF+1`, `Δχ = DeltaF-3` (`TriData.deltaF_eq`).
* **Triangle nonzero-gap reading `hnz`.** The counting for `DeltaF >= 1` uses that the fixed (beta-type) difference `k_{ℓ_j}-k_{ℓ_{j+1}}` is **nonzero** (so `atomCountLemma` (1)/strip count applies). The source assumes
  SG triples at `v_1,v_2` only (L1777: "`(v_j,ℓ_{j+1},ℓ_{j+2})` is an SG triple for `j ∈ {1,2}`"); the triple at `v_3` (always beta) is not required SG. `hnz` assumes nonzero gaps at all three atoms (Remark `subcondition` (iii): SG or LG).
* **Possible erratum at L1794 (ΔF=1 count).** The text "(triangle1) still holds for some `j`" bounds the number of pairs `(k_{ℓ_j},k_{ℓ_{j+1}})`, given the fixed difference `k_{ℓ_j}-k_{ℓ_{j+1}}`, by
  `δ⁻¹min(L^{d-2γ+1},L^d)` (Lemma basiccount (1), "where we also use `R >= L⁻¹`"). That requires the fixed difference to be **nonzero**. If it is zero (possible for `j=3`, whose triple need not be SG, or any ZG triple), the energy
  constraint is vacuous and the pair count is `L^d`, which exceeds `δ⁻¹L^{d+1-2γ}` when `γ>1/2` (`δ=1`, e.g. `γ=3/4`: `L^d` versus `L^{d-1/2}`). Concrete shape: ΔF=1, `v_3` with `k_{ℓ_1}=k_{ℓ_2}`, `k_{ℓ_1}` free in the unit ball
  (`L^d` choices), `α`-atom with `|k_{ℓ_3}-...|~R`. For this configuration the *final* bound of ΔF=1 still holds (`D = L^d(RL)^dL^{-2(d-γ)} = R^dL^{2γ} <= L^{-η³+η²}L^{(γ+3η)/2}R` for `d>=3`, `R <= L^{-γ+η}`),
  so the erratum affects the displayed intermediate bound only. For ΔF=2 with all three gaps zero (`k_{ℓ_1}=k_{ℓ_2}=k_{ℓ_3}`), `D ~ L^{γ}`, which exceeds the claimed `L^{-η³+γ_0+4η²}` for `γ>1/2`, but the SG assumption at `v_1,v_2`
  excludes it. Not checked by Lean beyond the exponent arithmetic.
* **`n_sub <= (log L)^C` (L1789).** An assumption of `betaCut_excess` (`hn`); for the triangle `|M| <= (log L)^c`.
* **Range of γ.** Cut cases hold for all `γ ∈ (0,1)` (given `200η <= min(γ,1-γ)`); the triangle cases also (no use of `γ>1/2`). The vine arithmetic uses `η <= γ`, `η<1`; the double-bond arithmetic also `γ<1`.
* **Standing facts used by the vine reduction as hypotheses** (source facts): `ΔF=0` (`hF`, L1798: "ΔF = ΔV_β = 0 by block_clcn, subpro (a)(e), subsetvc"), the vine bond count `B_VC = 2(m-1)` (`hB`, chart `bond_count`),
  and for two double bonds `B_VC=4`, `|C.atoms|=3`, no ladder in the VC (`hlad`, the source shows no ladder factor).

## Checks run (session 4)
See the end of this file.

## Files (sessions 1-3)

Scratch `<scratch>/finalcount/` (namespace `WaveTurbulence.FinalCount`, universe `WaveB2Draft.Molecules` from
lg-spine). 34 modules, `build.sh <Module>` (one module), `rebuild.sh <modules in topological order>` (fresh dir `build-fresh`,
exit codes in `build-fresh/exits.log`). `FCLadders.lean` is a verbatim copy of `waveb2/src/WaveB2Draft/Ladders.lean` (module
renamed; hashes in `COPIED-SHA256SUMS`). No file above 737 lines (that copy); own files at most 190 lines.

| Part | Modules | Main declarations |
|---|---|---|
| covers | CutCover, CoverProj | `countE_le_mul_of_cover`, `countE_le_mul_of_cover_proj` (cover by sets injecting under a restriction map into a smaller molecule) |
| cut basics | CutBasics, BetaSums, BetaCut, BetaCount, BetaCover | `countE_le_beta_cut` (`𝔈 ≤ (4|𝕄|+6) 𝔈_cut`) |
| components / rank of a cut | CutComponents, CutComp2, CutComp3, CutRank | `numComponents_cut_of_same/not_same`, `isAlphaCut_iff`, `circuitRank_cut_alpha/beta` |
| ladders under a cut (F-FC-3) | FCLadders, CutLad1..5 | `cut_isLadderSet_iff`, `pieces_exist`, `ladderProd_le` |
| deviation of a cut | DevCore, CutDev | `countA_dev_of_parts`, `countA_cut_dev`, `betaCut_isDeviation` |
| `α`-cut | AlphaBasics, AlphaCover, AlphaCover2, AlphaCount, AlphaDev | `alpha_cover`, `countE_le_alpha_cut`, `alphaCut_isDeviation` |
| real analysis | RealBounds0..3 | `alphaDev_kappa0`, `alphaDev_kappa50` |
| **Prop 9.4 for a cut** | Prop94Cut | **`alphaCut_excess`**, **`betaCut_excess`**, `excessRHS` |
| removal infrastructure | Restrict, RestrictComp, RestrictLad, RestrictRank, RemovalDev | `restrictP`, `numComponents_restrictP_add`, `maximalLadders_restrict_union`, `circuitRank_restrictP_add`, **`removal_isDeviation`** |

## Approach and statements (in words)

* `excessRHS L γ η αs ΔF ΔVβ = L^{-η³} · ∏_{(R,κ)∈αs} L^{(γ+3η)/2-κη} R · L^{(2γ₀+5η²)ΔF-(γ₀+2η²)ΔVβ}`, `γ₀ = min(γ,1-γ)`,
  is the right-hand side of (excesseqn2), DH23 L1785–L1786.
* `alphaCut_excess` (L1789–L1792, L1801): `d ≥ 3`, `0<γ<1`, `0<η≤γ`, `η ≤ (1-γ)/200`, `e ≤ L`, `0<δ≤1`, `1≤C₁`, `L⁻¹≤R≤L^{-γ+η}`,
  `κ∈{0,50}`, the gap of the cut bounded by `2R` for admissible decorations; for `κ=50` (`ι_v≠0`) additionally, for every
  parameter triple, an `r₀` with `‖gap-r₀‖ ≤ L^{-50η}R` on the decoration set. Conclusion
  `IsDeviation 𝔄_pre 𝔄_pos (ofReal (C · excessRHS L γ η [(R,κ),(R,κ)] 0 0))`, `C = 26·5^d((8/η)⁴+(8/(1-γ))⁴)`.
* `betaCut_excess` (L1789): the same with `|𝕄| ≤ (log L)^c`; `IsDeviation ... (ofReal (10((c+4)/(η²-η³))^{c+4} · excessRHS L γ η [] 1 2))`,
  and `excessRHS L γ η [] 1 2 = L^{η²-η³}`.
* In both, the ladder scales are *hereditary*: every maximal ladder of the cut inside a maximal ladder of `𝕄` has the same
  scale (`hPinh`, F-FC-3: the sub-ladders of a ladder keep its gap `r`, hence its dyadic scale). `ladderProd_le` shows the cut loses
  at most two rungs of the one ladder through `v` (`pieces_exist`), so the ladder factor changes by at most `(log L)⁴`.
* `removal_isDeviation`: for a closed atom set `P`, `𝔈(𝕄) ≤ N 𝔈(kept)` gives
  `IsDeviation 𝔄(𝕄) 𝔄(kept) (N · L^{-(d-γ)χ'}(C₁⁻¹δ^{1/2})^{χ'} ∏_{removed ladders} 𝔛^z)` (`χ'` = circuit rank of the removed part).
  This is exactly the shape of (fbyg), DH23 L1797–L1799, once `N = 𝔉` is bounded.

## Checks run (all by me, 2026-11-04)

* Fresh rebuild of the whole closure in topological order into `build-fresh` (`rebuild.sh`), exit codes in `build-fresh/exits.log`: all 0.
* `#print axioms` of `alphaCut_excess`, `betaCut_excess`, `ladderProd_le`, `numComponents_cut_of_not_same`, `countE_le_alpha_cut`:
  `propext, Classical.choice, Quot.sound` only (see PROGRESS.md for the later modules).
* Hygiene grep for `sorry|admit|axiom|opaque|unsafe|maxHeartbeats` over own files: clean.
* Exact-type check against a pinned statement: none exists in Lean for Prop 9.4 (no T.ops/G1); the statements above are my formalisation.

## Findings and uncertainties

* **Range of γ.** Prop 9.4's `α`- and `β`-cut cases hold for all `γ∈(0,1)` (given `η ≤ min(γ,(1-γ))/200`); no use of `γ>1/2`. The
  triangle cases are, by the source arithmetic (L1793–L1796), also free of `γ>1/2`: e.g. `ΔF=0` needs `γ₀ + η+2η²+η³ ≤ 2γ`, true for
  small `η`. I did not formalise them.
* **Triangles need an exact-triple cover, not window classes.** Composing three single-cut covers (as for `α`) multiplies in the
  window factors `(1+δ R_j L^{2γ})`, which loses against the source bound for `ΔF=1` when `γ≈1/2` (checked by exponents). The
  source covers by the exact bond vectors `(k_{ℓ1},k_{ℓ2},k_{ℓ3})` (`𝔉`, L1793). Use `countE_le_mul_of_cover_proj` with the
  triple as the index (post parameters `c'(f_j)=c(t_j)+gap_j`, `β'(f_j)=β(t_j)-g_j(t)` exact), then `removal_isDeviation`.
  For `ΔF=2` the bound of `|T|` uses `atomCountLemma` (1) (`nk≠0`, i.e. gap `≥L⁻¹`, from `abNonzero`) at `2n+3` energy shifts.
* **Vines (Step 1)** need the molecule-level reparametrisation M9 `VINEPARAM` (`<scratch>/vineparam-contract/CONTRACT.md`), which
  gausssum is still assembling. After cutting both joints and `restrictP`, `removal_isDeviation` reduces Step 1 to the count `𝔉` of (fbyg).
* G8-INPUTS: `<scratch>/finalcount-g8` did not exist when I looked; nothing was imported or exported. `countE_le_mul_of_cover_proj`
  and `removal_isDeviation` are the reusable pieces for its operation estimates (they are in the B2 `Molecule` universe, not `countAFree`).
* Errata/deviations (source): (i) L1789 writes `(RL)^d(1+RL^{2γ})`, the count is `(RL)^d(1+δRL^{2γ})` (δ dropped); harmless since `δ≤1`.
  (ii) The `ι_v≠0` argument (L1801) says the gap lies in "a fixed ball"; the ball centre is determined by the *parameters* (`c(v')=-r'` of the
  earlier cut atom), not by the decoration — formalised as the hypothesis `hball` (an `∃ r₀` per parameter triple).
  (iii) `n_sub ≤ (log L)^C` (L1789) is an assumption of `betaCut_excess` (`hn`).
* Deviations I introduced: constants are explicit; `κ` is a natural number in `{0,50}`; the `α`-cut count uses the box `(⌊2ρL⌋+1)^d` of gap
  lattice points and `⌈8δRL^{2γ}⌉+4` energy windows (no unit-ball assumption beyond the restriction `‖k-k0‖≤1`).

## Exact next step

1. Triangle `ΔF=2` (all three cuts are `β`): index = exact triple; fix `r_j` by component sums (as in `beta_c_side`), shift energies,
   bound the triple count via `atomCountLemma`; combine with `removal_isDeviation` (`χ(T)=1`, no ladders in `T`) and three
   applications of `ladderProd_le` (each loses `(log L)⁴`).
2. `ΔF=1`, `ΔF=0` (one resp. two `α`-cuts, third gap by the cycle relation).
3. Step 1 once M9 lands. 4. Assembly: an operation datatype (G1) and the statement over a sequence of operations.

## Checks run (session 4, final)
* Fresh rebuild of the 81-module closure of Prop94Statement in topological order into build-fresh (`rebuild.sh $(python3 topo.py Prop94Statement)`): 81 lines in exits.log, all `exit 0`.
* `#print axioms` of prop94_alpha, prop94_beta, prop94_triangle, prop94_vine_single, prop94_vine_double_full, iota_radius_ge: propext, Classical.choice, Quot.sound only.
* Hygiene grep (sorry|admit|axiom|opaque|unsafe|maxHeartbeats) over all closure files incl. the FCLadders copy: no hits. Largest own file < 300 lines.
* Exact-type check: no pinned Lean statement of Prop 9.4 exists (Prop94Statement.lean is the statement); not run.
* VINEPARAM hash recorded above (Contract.lean sha256 cd16890b...); it is not imported or used by any proved theorem.

## Session 5 (2026-11-04): scoping of the ruled route for `VineCountInput` (no new Lean; nothing compiled)

Read: Prop94Statement/VineBase/VineCover*/VineDouble6, lg-spine VineObjects (`Chain`, `IsVC`, `IsSomeVine`; the VINES API is ALREADY in lg-spine's universe, so no UNIVERSE port is needed for `Chain`/`IsVC`), ladder-decay (ClassCount, RungFull, RungBallTime, RungTotal).
Findings (arguments, not Lean-checked):
1. **Ladder-decay is not a label-count library.** `rung_full_same`, `rung_ball_time`, `rung_total` are bounds for time/frequency integrals of oscillatory rung sums with per-rung constants `C0`, `(C0*4L)^d`; `ClassCount`/`LadderBridge` count `Garden`-based `SplicedKernelData` decorations with kernel amplitudes, not `Molecule.labelSet`. A bridge Garden-decorations -> `Molecule.decSet` (flows, `Gamma`, `IsRestricted`) is a separate large piece.
2. **`VineCountInput` as defined is not the right target.** It quantifies over all `P`, `Adm`, `K` with `Cf` independent of `m`:
   (a) `ladderWeight L g d P = min((log L)^2, 1+d L^{2g} P)` and `P` is free; the gain `1/X^z` is only true if `Adm` forces `|r_S| ~0 P S` for each maximal ladder (countA docstring says this restriction "is part of Adm"). With `Adm = True`, `P S = L^100` the claimed gain `(log L)^{-2z}` has no reason to hold (a ladder of 2 rungs, small actual gap, no decay in the count).
   (b) per-atom constants: the true count per interior atom is `c_d * delta^{-1} * L^{d-g} * (rho L^g)^{-1}` (slab of the unit ball: omega_{d-1} * strip width), while the target has `L^{d-g} delta^{-1/2}` with no `c^m`. For `rho ~ L^{-g}`, `delta <= 1`, a chain of `m` type-I vines (double bonds) the ratio count/target grows like `(c_d delta^{-1/2})^m`, so no `Cf` independent of `m` exists. The source absorbs this in `C_1` ("C_1 large"); the Lean `hC : 1 <= C1` is too weak, and `vineF` should carry `C2^m` with `C2 <= C1` assumed (modify VineExcess3 `vine_excess_single`: factor `(C2/C1)^m <= 1`).
   (c) The label count needs source premises that `prop94_vine_single` does not state: `K.C.shape = .vc h` (an actual chain), `|gap| ~ R` from below for the joint (cf. `hlow` in `prop94_vine_double_full`), `L^{-1} <= rho`, SG/nonzero gap on the VC, and `Adm` carrying ladder scales. `prop94_vine_double_full` has the first and third for the 3-atom case only.
3. **Size.** A proof needs: (i) the dart-level description of every template (8 types, `expand`) as flows + `Gamma` strips with the common gap `r` (block conservation); (ii) per-ingredient counting under `Chain.append` induction with boundary data at the shared joint; (iii) the bilinear rung count (x.y strip with the r-linear strip) with an exact per-rung constant; (iv) the identification of `maximalLadders` of `K.vc` with the inserted rungs; (v) assembly. I estimate well above 5000 lines; none of (i)-(v) exists in the `Molecule` universe.

## L1794 erratum candidate: explicit configuration (analytic; matches the earlier note)
`Delta F = 1` triangle count, `gamma > 1/2`, `delta = 1`. Take `v_3` with `k_{l_1} = k_{l_2} = k` (fixed difference ZERO), `k` free in the unit ball: `~ omega_d L^d` pairs `(k_{l_1},k_{l_2})` (every one satisfies the energy window at `v_3`, since the pair energy `|k_{l_1}|^2-|k_{l_2}|^2 = 0`). Source claims the pair count is `<= delta^{-1} min(L^{d-2g+1}, L^d) = L^{d+1-2g} < L^d` for `g > 1/2`, `L` large. So the intermediate bound (triangle1) fails for a ZERO fixed difference (needs nonzero: `hnz`). The final bound still holds there: `D = L^d (RL)^d L^{-2(d-g)} = R^d L^{2g} <= L^{-eta^3+eta^2} L^{(g+3 eta)/2} R` for `d >= 3`, `R <= L^{-g+eta}` (exponent arithmetic only). Not Lean-checked.
