# HANDOFF (session 8, FINAL) -- FINALCOUNT-G8: DH23 Proposition 9.6 for 1/2 < γ < 1

STATUS: **DONE. `Final96c.prop96` is unconditional (no named input), standard axioms.**

```
theorem WaveTurbulence.FinalCountG8.prop96 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1/2) 1) (η : ℝ) (hη : 0 < η)
    (hsm : (d:ℝ) * η ≤ min γ (1-γ) / 1000) (hsm2 : (d:ℝ) * η ≤ (2*γ-1) / 1000) (hηs : 4 * 1440061 * η ≤ 1) (m : ℕ) :
    Prop96At.{u,v} d γ η m
```
Proof: `prop96_of_smallcell … (case4SmallCell_proved …)` (Final96c.lean).

## Files / gluing
* Scratch `<scratch>/finalcount-g8` (namespace `WaveTurbulence.FinalCountG8`).
* g8-xroute's `XRoute/{Base,Basic,Cell,Route,Ring,Small,RouteBound,XMinus,TheoremAX,Branch}.lean` copied byte-for-byte
  (sha256 in `XROUTE-COPIED-SHA256SUMS`, compared with the g8-xroute originals: identical). Its inputs
  (C4NonExc, C4Main, C4Route, PairGain(Input), G8R/ThmA, ThmARoute, CoreCaseI, CoreInputs) were checked to have the same
  sha256 as in finalcount-g8, so ONE closure. Nothing in g8-xroute or moleprop4-t was edited.
* New: `Final96c.lean` (prop96). `rebuild_session8.sh` = session-7 order + XRoute/* + Final96c + Axioms11 (+ transient ExactType96).
  Hashes of the new files: `SHA256SUMS-session8`.

## Checks run (session 8)
* FRESH rebuild of the WHOLE closure (G8 + XRoute, 159 own modules incl. Axioms, new dir `build8`, `buildC.sh`, topological order):
  `rebuild_session8.out` ends `ALLOK`; every log `exit 0` (grep -L "^exit 0" over build8 logs: empty).
* `#print axioms` (build8/Axioms11.log): `prop96` and `case4SmallCell_proved` depend on [propext, Classical.choice, Quot.sound] only.
* Hygiene grep `\b(sorry|admit|axiom|opaque|unsafe)\b|maxHeartbeats` over all 159 own modules (Axioms*, ExactType excluded): no hits.
  Largest file 554 lines (limit 1500). No `set_option` in new files.
* Exact-type check: the transient file `ExactType96.lean` (compiled in build8, exit 0, then deleted) was
  `example (d hd γ hγ η hη hsm hsm2 hηs m) : ∃ Cstar, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Ioc 0 1, ∃ R₀, ∀ L ≥ R₀, ∀ {V D : Type} … (M : Molecule V D) (cls) (odd) (Adm) (P),
  FinalShape M cls odd → FinalDec M cls L γ η Adm → |M.atoms| ≤ (1+log L)^m → (∀ S, 0 ≤ P S) → MaxLadderGapAdm … → (∃ v₂ ∉ M.atoms) →
  M.countA L γ δ C1 0 Adm P ≤ ofReal ((∏_{v ∈ alphaAtoms} L^{-(γ+3η)/2 + κ_v η} · R_v⁻¹) · L^{(min γ (1-γ) + 2η²)·V_β − (2 min γ (1-γ) + 5η²)·G} · L^{-η⁵ ρ₀}) := prop96 …`
  with the RHS written out (not via `finalRHS`), `G = if odd then 0 else 1`. It compiled by `exact`/term `prop96 d hd γ hγ η hη hsm hsm2 hηs m`.

## Reading of DH23 L1818-L1822 (Prop 9.6, `lgmolect`, label `finalcount`) and deviations (all listed)
| source | formal |
|---|---|
| L1818 "for each component 𝕄₀ of 𝕄_fin define (𝔈₀,𝔄₀,𝔓₀), ρ₀ as in Section reductcut0 and (defequan), p replaced by 0" | `M.countA L γ δ C1 0 Adm P`, `M.rho`, `P` |
| L1819 "each α-atom v labeled by dyadic R_v" | `Cls.alpha R κ`, `labRange`, `kapVals` (κ_v ∈ {0,50}) |
| L1820 (finalcount) 𝔄₀ ≲ ∏_v^{(α)} L^{-(γ+3η)/2+κ_vη}R_v^{-1} · L^{(γ₀+2η²)V_β-(2γ₀+5η²)G} · L^{-η⁵ρ₀} | `ENNReal.ofReal(finalRHS …)`, γ₀ = min γ (1-γ) = 1-γ |
| L1821-1822 V_β, G∈{0,1} (odd/even) | `(betaAtoms …).card`, `if odd then 0 else 1` |
Deviations (each also in the earlier sections):
1. `≲` = `≤` with constant 1 for `L ≥ R₀`, for all `C1 ≥ C★`, `δ ∈ (0,1]` (constants absorbed by R₀).
2. `∼ R_v` (alphaGap) read as `R_v/2 ≤ |gap| ≤ 2 R_v`.
3. Size bound `|M₀| ≤ (1+log L)^m` (DH23 Prop 10.2 states none; its proof needs it; APPB erratum R4).
4. `oddDeg` weakened: two distinct odd atoms of degree 1 or 3 (the (3,3) case occurs; see errata).
5. Fresh atom `∃ v₂ ∉ M.atoms` as a typing hypothesis (G3's mapping theorem has `[Infinite V]`).
6. R = 1 (the dyadic parameter of the molecule class); `alphaSG` non-strict (`≤ L^{-γ+η}`); `epsLG`/`vineLG` strict (`>`).
7. `FinalDec.noBetaCut` (N3, L1887) in `FinalDec`; `FinalDec.betaGap` (N1); `FinalDec.iota` (N2) present but UNUSED (a factor 1/2 in its conclusion `L^{-50η} min(R₁,R₂)/2`).
8. η-smallness constants, each an instance of "η ≪_{d,γ} 1" (DH23 L438): `d η ≤ min γ(1-γ)/1000` (hsm), `d η ≤ (2γ-1)/1000` (hsm2, needed for κ(γ) ≥ η/10 in case 4/6 and `case6_arith`), `4·1440061·η ≤ 1` (hηs, from the Theorem A constants).
9. Case-(4) exponent `L^{-η/128}` (was η/20): two operations (d) halve the LG parameter twice; polylog absorption costs another factor 2. Closes inside `case4_finish` (η ≤ 1/(4·1440061)).
10. Operation (e) not needed for γ > 1/2: case (6) by chain removal + Prop 10.1′ (`case6_arith`); it would be needed for γ ≤ 1/2. ACCEPTED reading.
11. X-route (R26, G8-XROUTE): terminal set `IsX ∨ IsQuad` (the quad needed for the ≤ 4-atom disjunct of `Case4SmallCell`), gain L^{-η₀/3}, η₀ = η/8; used `Prop102SecondAt` with m = 2.
12. d ≥ 3, `1/2 < γ < 1` only.

## Errata candidates (exact locations; none changes a DH23 claim to a false statement unless said)
1. **(operc), DH23 L1861**: "𝔇 ≲ 1 + δ⁻¹R⁻¹L^{-γ}" is in truth `L^{γ-1} + δ⁻¹R⁻¹L^{-γ}`; stated bound is weaker/over-estimate (not false). Used in `opC_rho`/`chain_A_bound`.
2. **Case (1), DH23 L1884, the (3,3) odd component**: the argument is written for an odd atom of degree 1 (w = V_α+V_β ≥ 1, 𝔄 ≲ 1 from Prop 10.1). When both odd atoms have degree 3, all others degree 2/4 and there is no α/β atom (w = 0, E = 2V-1), 𝔄₀ ≲ 1 does NOT give (finalcount) (RHS carries `L^{-η⁵ρ₀}·…`). Needs Prop 10.2's first statement (no triple bond, E = 2V-1: 𝔄 ≲ L^{-3γ₀/5}), used in `Odd96` (`odd0_arith`). Exposition gap; this is why `oddDeg` is weakened (also DH23 subpro(b), L1734).
3. **L1862-L1874** ("operations (a), (b) only on ε-atoms"): also needs free deletion of degree-1 protected α/β atoms; proved (`P101.operation_a_normalized_bound_at`, `PMol`). Exposition gap.
4. **DH23 L790 (closed cells)**: the text does not say which of the two parametrizations of a closed ladder cell defines its gap (R26; the source of the spurious `¬YReachesSmallCell` hypothesis of Prop 10.4(2)′). Exposition point, no mathematical error (R26: Prop 10.4(2) proof L1961-L1977 handles 𝕄′ = X under case (I), A.3(4) L2106).
5. **MOLEPROP4-T internal-input defects** (formalization statements, not DH23 errata): `OpCAt` lacked connectivity of M, the chain and M∖Y (false without); `OpDAt` lacked |Y| ≤ 3, connectivity of M/Y/post, `hopen` (GoodCell of post cells) and the end-exemption u,v ∉ Bs; `MergeAt` needed `hconn`/`hopen`; `BiBridgeEqualAt` needed `hopen`; `PairGainInput`/`SmallGapPairInput` only for γ > 1/2; `prop104_two_proved` requires `¬YReachesSmallCell` and `5 ≤ |𝕄₁|` (artifact; closed by the X-route and the ≤ 4-atom branch in `Case4SmallCell`). All discharged inside this closure.
6. Source-side: DH23 6.5/6.7 style issues are not touched here; the APPB `(log L)^3` vs `N³` erratum (R4) is the reason for the size bound (deviation 3).

## Uncertainties
* Prop96At is a formal reading (above); fidelity at the points listed is by owner rulings (R4, R18, R26). `FinalShape`/`FinalDec` are conclusions of G3's Prop 9.5 package (R18) and must be supplied by it at composition; `FinalDec.iota` is unused.
* The orchestrator should run its own audit of the transient exact-type statement above (not retained as a file).

READY finalcount-g8

---
(Earlier sessions follow; session-7 head and details preserved below.)

# HANDOFF (session 7) -- FINALCOUNT-G8: DH23 Proposition 9.6 for 1/2 < γ < 1

STATUS: **F6-1 DONE; one named input remains: `Case4SmallCell` (C4NonExc.lean).**
`Final96b.prop96_of_smallcell : Case4SmallCell d γ η m → Prop96At d γ η m` is proved (standard axioms, no sorry).
The non-exceptional branch of case (4) is proved (decoration-level consumption of `SplitBound`) except when the
closure `𝕄₁` reaches a small cell (F6-2, pending an orchestrator ruling) or has at most four atoms.

Scratch: `<scratch>/finalcount-g8` (namespace `WaveTurbulence.FinalCountG8`). PROGRESS.md has the module log.

## Session 7: F6-1 (all exit 0, no sorry; axioms propext, Classical.choice, Quot.sound: Axioms10.lean)
| module | content |
|---|---|
| `OpDW`, `OpDW2` | decoration-level operation (d): `TwoExit.PostGoodOff`, `TwoExit.postAdmOff` (post decorations that are images of `Adm`-decorations with `W g`), `countEFree_le_chainW`, `TwoExit.afreeSupPost`, **`opDW`** (`𝔄(M;Adm) ≤ 21125 (log L)^14 · sup_{g∈[0,4]} 𝔄(post; postAdmOff Adm W g)`); clone of `OpDCount`/`opDAt` following `TwoExit.countEFree_le_adm` |
| `OpCFree` | **`opCFree`**: operation (c) keeping `erasedFreeAdmissibility M Y Adm` (clone of `opCAt` without the `lgAdmOff` weakening) |
| `Split2Iso` | `crossDarts_addBond_inl`, **`bondPostEquiv`** (dart isomorphism between the two orders of contracting two chains: erase-then-add vs. add-then-erase) with `_atom/_mate/_out/_atoms`, `withoutEquiv` (darts of `N` ≃ darts of `N∖(Φ(inr true))`) |
| `Split2Gen` | `countAFree_or_le` (subadditivity of the count in the admissibility), `postGoodOff_largeGap` |
| `Split2Class1`, `Split2Class2` | abstract two-step lemmas: `Cls1` (some good pair `(g₁,g₂)` whose transported `𝕄₁`-decoration fails `Q`), **`class1_bound`** (op (d) twice, clause 1 of `SplitBound`), **`class2_bound`** (op (d) on chain 1, op (c) on chain 2, clause 2 of `SplitBound`), `largeGap_relabel`, `relabel_apply` |
| `Split2Arith` | `splitK`, `split_arith` (polylog absorption: `A(Aε₁)+A(Cε₂) ≤ L^{-η_s/32}`) |
| `Split2Main`, `Split2Thm` | **`case4_two_split`**: two chains, `RegCore(𝕄₁)`, `¬YReachesQT`, `¬YReachesSmallCell`, `5 ≤ |𝕄₁|` ⇒ `𝔄₀ ≤ L^{-η/128}`; `triple_of_tripSet`, `bb_le_three_of_nonexc`, `ofReal_sum_bound` |
| `Split1Thm` | **`case4_one_split`**: one chain `u→b→b′→v` (`Cls1One`; one op (d) or one op (c)) |
| `C4Main` (edited) | exponent `η/20 → η/128` in `case4_finish`, `Case4NonExc`, and the T/Q branches (weakening) |
| `C4NonExc` | **`Case4SmallCell`** (named input), **`case4_nonexc_of_smallcell : Case4SmallCell → Case4NonExc`** (plumbing of the data from `FinalShape`/`Case4TwoData` into `case4_two_split`/`_one_split`) |
| `Final96b` | **`prop96_of_smallcell`** |

### The decoration-level split (how `SplitBound` is consumed)
`prop104_two_proved` is applied to `𝕄₁ = closureTwo` at `η_s = η/4` (two chains) resp. `η/2` (one chain), `e` = the bond of the
second contracted chain (`Φ(inr true)`). The decorations κ of `𝕄₀` split by the predicate `Cls1`: *∃ good pair of multipliers
(g₁,g₂) ∈ [0,4]² (LG of both posts, `PostGoodOff`) with ¬Q of the transported decoration* (class 1, counted on `𝕄₁` by op (d) twice) versus
*all good pairs give Q* (class 2: op (d) on chain 1, then op (c) on chain 2, whose erased post is `𝕄₁∖ℓ₂`; the missing bond label is
supplied by a good g₂ for the extension, which carries `Q` and `LargeGap`). The transport is `T.postLabels κ g = κ(x₂)+g(κ(x₁)−κ(x₂))` on the new bond.
Class 1 total: `(21125 log^14)² ε₁`; class 2: `21125 log^14 · 2·3^d(dδ⁻¹+1) log^8 L^{1-γ} ε₂`, with `ε₁ = K_s(|𝕄₁|+1)L^{-η_s/16}`,
`ε₂ = K_s(|𝕄₁|+1)L^{-(γ₀+η_s/16)}`, `γ₀ = 1-γ` (γ>1/2) so both are `≲ L^{-η_s/16}`·polylog `≤ L^{-η_s/32}`.

### Deviations and readings (session 7)
* **Exponent `η/128`** (was `η/20`) in `Case4NonExc` / `Case4SmallCell` / `case4_finish`: the two op (d) halve the LG parameter twice
  (`η_s = η/4`), `prop104_two_proved` gives `L^{-η_s/16}`, and the polylog factors cost another factor 2 (`η_s/32 = η/128`).
  `case4_finish` closes with `η/128` unchanged (η ≤ 1/(4·1440061)).
* **`Case4SmallCell` hypothesis `YReachesSmallCell 𝕄₁ ∨ |𝕄₁| ≤ 4`**, not just `YReachesSmallCell 𝕄₁`: the last operation (d) lands on a
  molecule isomorphic to `𝕄₁` and needs `GoodCell` for its ladder cells (`goodCell_of_connected` for `≥ 5` atoms). A 4-regular `𝕄₁` with
  `≤ 4` atoms and a closed cell (e.g. `X`) has no (Y)-route (no triple bond) and is not covered; it is a tiny configuration of the same
  nature as the X-route. F6-2 must cover it as well (or show it does not occur).
* Operation (e) is not needed for γ > 1/2 (case (6) via chain removal and Prop 10.1′): ACCEPTED reading (see session 6).
* `Case4NonExc` is now PROVED from `Case4SmallCell`; it remains in the code only as the intermediate statement consumed by `case_four_of_nonexc`.

## Rulings applied
* `noBetaCut`, non-strict `alphaSG`, strict `epsLG`/`vineLG`, weakened `oddDeg`, R = 1: accepted (in force).
* Fresh-atom hypothesis `∃ v₂ : V, v₂ ∉ M.atoms`: kept as a TYPING condition of `Prop96At`, `EvenCaseAt`, `Case4NonExc`. The source's molecules live in an
  unbounded ambient atom set; **G3's mapping theorem has `[Infinite V]`, which supplies it at composition.**
* (3,3) odd component, DH23 L1884: recorded as a CANDIDATE exposition gap (below).

## Session 6 (kept for reference; all exit 0, no sorry; `#print axioms` = propext, Classical.choice, Quot.sound; Axioms8.lean, Axioms9.lean)
Build order: `rebuild_session4.sh`, `rebuild_session5.sh`, then **`rebuild_session6.sh`**; hashes `SHA256SUMS-session6`.
| module | content |
|---|---|
| `C4Route` | `RegCore` (caps, loop-free, 4-regular, connected, no cut vertex), `YRouteQ`, `tripSet`, `RegCore.not_y1` (no (Y1) step in a regular molecule without cut vertex), **`reach_cases`**: `YReachesQT N → RegCore N → #tripSet ≤ j → (∃ k ≤ j, YRouteT k N) ∨ YRouteQ N` |
| `C4ZQ` | ladder `Z_m(Q)`: `zBB`, `IsZQ`, chain bond counts, `zq_step`, **`yrouteQ_zq : YRouteQ N → RegCore N → #tripSet ≤ 2 → ∃ m φ, IsZQ N m φ`** (case-4 note Lemma 3.3 / (Z) generation) |
| `C4Vine1`, `C4Vine2` | half-ladder = `IsVineIIHalfClosure` (`isVineHalf_of_ladder`); **`halfClosure_of_zq`** (`Z_m(Q)` minus the bond of one chain is a half-closed vine (II)) |
| `C4Cut` | **`cutvertex_cut`** (degree-4 cut vertex of a balanced even connected molecule gives a separating `IsCutData`), **`nocut_M0`** (an even `FinalShape` component with `FinalDec` has no cut vertex: ε-atoms by `noBetaCut`+`epsLG`, β-atoms by parity) |
| `C4Close` | `regcore_closureOne` (TwoExit literal), `closureTwo_dir` (in/out degrees of `𝕄₁` equal those of `𝕄₀`), bond-count connectivity (`sc_iff_bb`, `sc_erase_iff`), `graph_transfer`, **`regcore_closureTwo`**, `trip_closureTwo` |
| `C4Data` | `Case4TwoData`/`Case4OneData`, `c4_atoms`, `c4_data` (chain data from `FinalShape`) |
| `C4Vine3` | `c4_two_vine`: a `Q`-type closure makes `𝕄₀` a vine (II) (reuses case (5)'s `isVine_of_halfClosure`) |
| `C4Main` | `Case4NonExc` (named input), `case4_finish`, **`case_four_of_nonexc`** : `Case4NonExc → EvenCaseAt (a=0 ∧ b=2)` |
| `Case6_96`, `Final96` | **`case_six`** (V_α=2, V_β=1), `case_six_even`, **`prop96_of_nonexc : Case4NonExc d γ η m → Prop96At d γ η m`** |

### Case (4) as proved
`𝕄₁` = closure (each β-chain replaced by a bond). *T-type* (a complete (Y)-route to `T`, ≤ 2 sequences): `theorem_A`/`theorem_A_one` (all ~25 hypotheses
discharged); *Q-type*: two chains: `𝕄₀` is a vine (II) (`yrouteQ_zq`, `halfClosure_of_zq`, `isVine_of_halfClosure`), hence LG (`vineLG`), and operation (c) with
Prop 10.1′ at ρ = L^{-γ+η} (`chain_A_bound`) gives L^{-η/2}; one chain: impossible (`zq_no_single`); *not Y-exceptional*: `Case4NonExc`.
Interpolation with roughbd (`case4_finish`, uses `hsm2` for κ(γ) ≥ η/10).

### Case (6) WITHOUT operation (e)  (deviation from the plan; strengthening)
For 1/2 < γ < 1 the chain through an α-atom + Prop 10.1′ suffices: the second α-atom contributes `L^{(γ-5η)/2}` to the right side, which beats `L^{-γ₀}` since
γ > γ₀ = 1-γ (`case6_arith`: margin 2γ-1-4η-… > 0 by `hsm2`). So **operation (e), the ι/κ property (N2), the triple-bond analysis and the three-chain configurations are not needed**
in the range of this packet (they are needed for γ ≤ 1/2, where γ₀ = γ). `FinalDec.iota` is therefore unused by Prop 9.6 here. The orchestrator's instruction "prove operation (e)" is superseded.

## Session 6 analysis of the open input `Case4NonExc` (F6-1 RESOLVED in session 7; F6-2 is the content of `Case4SmallCell`)
For `Case4TwoData`/`Case4OneData` (the chain data of an even V_α=0, V_β=2 component) with `¬ YReachesQT (closure)`: `countA ≤ L^{-(η/128)}` (session 7; was η/20). = DH23 Prop 10.4(2)
as consumed at L1883-L1886.
* **F6-1 (decoration-level consumption) -- RESOLVED in session 7 (see the table above).** `prop104_two_proved` gives `SplitBound M₁ e`: an EXISTENTIAL decoration predicate `Q` with `𝔄(𝕄₁; lgAdm ∧ ¬Q) ≤ ε₁` and
  `𝔄(𝕄₁∖e; erasedBondAdmissibility M₁ e (LargeGap ∧ Q) ∧ lgAdm) ≤ ε₂`. `OpCAt`/`OpDAt` (ThmAOps) abstract the decorations (their post admissibility is the FIXED `lgAdmOff post`) and cannot
  carry `Q`. Needed (estimate 600-900 lines): (i) a W-version of `OpDCount.countEFree_le_chain` (follow MOLEPROP4-T `TwoExit.countEFree_le_adm`/`postAdm`: add `W : ℤ → κ → Prop`,
  conclusion with `postAdm`); (ii) `OpCCount.countEFree_le_chain` already keeps `erasedFreeAdmissibility M Y Adm_Q`; (iii) the transport `κ ↦ φ_{g₁,g₂}(κ)` to `𝕄₁`-decorations (new bond vector
  `κ(x₂)+g(κ(x₁)-κ(x₂))`, `g` from `exists_post_largeGap_off`), and the classes "∃ good g with ¬Q" / "all good g have Q"; (iv) ε₁-side = op(d)W twice, ε₂-side = op(c) on chain 1 then op(d)W on chain 2.
* **F6-2 (structural obstruction) -- OPEN, = `Case4SmallCell`.** `prop104_two_proved` needs `¬ YReachesSmallCell M₁` (MOLEPROP4-T HANDOFF deviation 3). It is NOT derivable from the shape of `𝕄₀`.
  `YReachesSmallCell M₁` means a (Y2)-route reaches a post with ≤4 atoms and a ladder cell; the only such molecule is `X = (a=b, c=d, ac, bd, ad, bc)` (a ladder needs 4 distinct atoms, rungs exactly 2, rails exactly 1; degrees force the two chords).
  Explicit valid case-(4) component: atoms `a,b,c,d,a0,b0` (ε, degree 4), β-atoms `β1` (between a0,b0), `β2` (between a,c); bonds `ab, aβ2, β2c, ad, bc, bd, cd×2, a a0, b b0, a0b0×2, a0β1, β1b0`
  (14 bonds, no triple bond, connected, no cut vertex, chain ends distinct ε-atoms, an Eulerian orientation gives in=out). Its `𝕄₁` has ONE triple bond `a0≡b0`, is not Y-exceptional, and its unique
  complete route is the chain `{a0,b0}` (n=0, exits a0–a, b0–b, `bb(a,b)=1≠2`) with post `X`. So `YReachesSmallCell 𝕄₁` holds, `prop104_two_proved` does not apply, and `theorem_A` does not apply (`X` is not `T`).
  Repairs: (R1) Prop 10.4(2)′ without the small-cell hypothesis (MOLEPROP4-T area; the good-cell condition fails only for the post `X`); (R2) an `X`-terminal variant of Theorem A:
  `X∖ℓ*` with `ℓ*` a copy of a double bond of `X` is two adjacent degree-3 atoms joined by a single bond (Lemma A.3(4), then the double bond `c=d`), but `ℓ*` can be a single bond (`ac`) of `X`
  (when the new bond of the last sequence joins two non-adjacent atoms), for which no gain is known. Whether DH23's claim is true in that sub-case is not decided here.
  Decision needed from the orchestrator: which repair (or a ruling to accept an explicit named hypothesis).

## Checks run (session 6)
* `rebuild_session6.sh` modules compiled one by one (exit 0); `#print axioms prop96_of_nonexc, case_six_even, case_four_of_nonexc, prop96_of_cases46, yrouteQ_zq, reach_cases, nocut_M0`: propext, Classical.choice, Quot.sound.
* Hygiene grep (`sorry|admit|axiom|opaque|unsafe|maxHeartbeats`) over C4*.lean, Case6_96.lean, Final96.lean: clean. Largest file 554 lines.
* Exact type: `prop96_of_nonexc … : Prop96At d γ η m` is checked by the declared type (Prop96At is the literal formal statement below).
* NOT run: fresh rebuild of the whole closure in a NEW directory (not READY, so skipped; `rebuild_session4.sh`, `rebuild_session5.sh`, `rebuild_session6.sh` give the order; they must be pointed at a new build dir via `build.sh`).

### Literal reading of the target (DH23 L1818-L1822 vs `Prop96At`)
L1818-1819 "For each component 𝕄₀ of the final molecule 𝕄_fin, define (𝔈₀,𝔄₀,𝔓₀) and ρ₀ … associated with 𝕄₀ (here p should be replaced by 0 … no more SG atoms)" = `M.countA L γ δ C1 0 Adm P`, `M.rho`, `P`;
L1819 "Let also each α-atom v be labeled by the dyadic number R_v" = `Cls.alpha R κ`, `labRange`; L1820 (finalcount) "𝔄₀ ≲ ∏_v^{(α)} L^{-(γ+3η)/2+κ_vη}R_v^{-1} · L^{(γ₀+2η²)V_β-(2γ₀+5η²)G} · L^{-η⁵ρ₀}" =
`ENNReal.ofReal (finalRHS M cls odd L γ η)` (γ₀ = min γ (1-γ) = 1-γ); L1821-1822 "V_β number of β-atoms; G is 0 or 1 whether 𝕄₀ is odd or even" = `betaAtoms.card`, `if odd then 0 else 1`.
Reading choices: "≲" = "≤ with constant 1 for L ≥ R₀ (C₁ ≥ C★)"; "∼ R_v" = R_v/2 ≤ |gap| ≤ 2R_v; the hypotheses on the component are the conclusions of Prop 9.5 (`FinalShape`, `FinalDec`, R18).

## Deviations and readings (cumulative)
1. 1/2<γ<1, d≥3; polylog size bound |M₀| ≤ (1+log L)^m (DH23 Prop 10.2 states none, its proof needs it; APPB erratum R4); L ≥ R₀; constant 1 in ≲; master smallness d·η ≤ min(γ,1-γ)/1000, d·η ≤ (2γ-1)/1000, 4·1440061·η ≤ 1 (instances of L438's η ≪_{d,γ} 1).
2. `FinalShape`/`FinalDec` carry (as conclusions of G3's Prop 9.5 package, R18): `dir2`, `degPos`, `classes` (both directions), N1 `betaGap`, N2 `iota` (now unused), `vineLG` incl. the double-bond disjunct, `alphaSG` (non-strict), `epsLG`/`vineLG` strict, `noBetaCut`.
3. `oddDeg` weakened (two distinct odd atoms of degree 1 or 3: the (3,3) case occurs, DH23 subpro(b) L1734); R = 1.
4. Fresh atom (see Rulings).
5. MOLEPROP4-T internal named-input defects (not DH23 errata; internal statements): `OpCAt` lacked connectivity of M, the chain and M∖Y (false without); `OpDAt` lacked |Y| ≤ 3, connectivity of M/Y/post, `hopen` (GoodCell of post cells) and the end-exemption u,v ∉ Bs; `MergeAt` needed `hconn`/`hopen`; `BiBridgeEqualAt` needed `hopen`; `PairGainInput`/`SmallGapPairInput` only for γ>1/2.
6. Case (6) is proved without operation (e) (above).
7. `Case4NonExc` is a conditional helper with a distinct name; it is never a source result.

## Source remarks / errata
* DH23 (operc) L1861 "𝔇 ≲ 1 + δ⁻¹R⁻¹L^{-γ}" is in truth `L^{γ-1} + δ⁻¹R⁻¹L^{-γ}` (an over-estimate when the first term is dominated; not a false statement). Located at L1861; used in `opC_rho`/`chain_A_bound`.
* CANDIDATE exposition gap, L1862-L1874: "operations (a), (b) only on ε-atoms" also needs free deletion of degree-1 protected α/β atoms; proved (`P101.operation_a_normalized_bound_at`, `PMol`).
* CANDIDATE exposition gap, case (1), DH23 L1884 (the (3,3) odd component): the argument is written for an odd atom of degree 1 (so w = V_α+V_β ≥ 1 and 𝔄 ≲ 1 from Prop 10.1 suffices). Exact configuration: an odd component whose two odd atoms both have degree 3,
  all others degree 2 or 4, no α/β atom (w = 0, E = 2V-1). Then 𝔄₀ ≲ 1 is NOT enough for (finalcount) (the right side is L^{-η⁵ρ₀}·…); the proof needs Prop 10.2's first statement (no triple bond, E=2V-1: 𝔄 ≲ L^{-3γ₀/5}), which `Odd96` uses (`odd0_arith`).
* The case-4 note (F75) is consistent with what was formalized for the T- and Q-type; it does not address the non-exceptional branch beyond citing Prop 10.4(2)′ (YLEM1 R2).

## Uncertainties
* F6-2 (above) is the one real mathematical uncertainty.
* `reach_cases` uses `RegCore.nocut` to exclude (Y1) case 3; `nocut_M0` uses `FinalDec.noBetaCut` (decoration-dependent), so case (4) needs some `κ ∈ Adm` (else `countA = 0`, handled).

READY/STOPPED line: see the final message.

## Checks run (session 7)
* FRESH rebuild of the whole closure (149 own modules, topological order, new dir build7, `rebuild_session7.sh`): ALLOK, every exit 0.
* `Axioms10.lean` (build7/Axioms10.log): prop96_of_smallcell, case4_nonexc_of_smallcell, case4_two_split, case4_one_split, opDW, opCFree, class1_bound, class2_bound, case_four_of_nonexc -- see log (expected: propext, Classical.choice, Quot.sound only).
* Hygiene grep (sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option) over the new/edited modules: clean. Largest new file 397 lines. Hashes: SHA256SUMS-session7.
* Open input: `Case4SmallCell` (exact type at top of PROGRESS.md).

## G8-DCB (session 9): `Prop96DamagedAt` (R29 item 5)
Files: `Damaged96Statement.lean` (defs, `DamagedShape`, `DamagedDec`, `Prop96DamagedAt`), `Damaged96.lean` (`rough96D`, `pmol_damaged`,
`damagedRHS_ge`, `damaged_arith`, **`prop96_damaged`**), `Axioms12.lean`, `buildD.sh`, `SHA256SUMS-dcb`. Exact statement: top of PROGRESS.md.
Approach: A <= 1 by `P101.proposition_one_off_bound` (B = alpha/beta atoms; `pmol_damaged` from conn + imperf; LG off B from `epsLG`);
A <= L^(-eta^2 rho + (16d+28)(w+1)) by a verbatim copy of the `rough96` proof for `DamagedShape` (`rough96D`); `interp_L` at theta = eta^3;
arithmetic `damaged_arith`: 2(16d+28)eta^2 <= 1 (from d*eta <= 1/2000), eta <= (gamma-5eta)/2, eta <= gamma0 + 2eta^2, w <= Va+Vb+Z, w >= 1.
Closing arithmetic used the actual G8 hypotheses (hsm, hηs); hsm2 and gamma>1/2 are NOT needed.
Checks: fresh build in new dir `buildD` with `build8` read-only on LEAN_PATH, all exit 0; `#print axioms prop96_damaged` = propext, Classical.choice, Quot.sound;
transient exact-type example (RHS written out) compiled, deleted; hygiene grep (sorry/admit/axiom/opaque/unsafe/maxHeartbeats) empty.
Deviations: (1) `DamagedDec` has `labRange` besides `epsLG` (needed to lower-bound ∏ R_v⁻¹ L^...; a FinalDec field, so `FinalDec.toDamaged` is trivial);
(2) `DamagedShape` omits `caps`/`prot` as separate fields: caps = `isMolecule.1`, prot follows from `classes`; (3) Z = #(eps atoms of degree ≠ 4).
For G3: a damaged component supplies `DamagedShape` (imperf from non-perfectness) and `FinalDec.toDamaged`-style data (labRange, epsLG at strict LG). Prop96At unchanged.
No errata found.
AMENDMENT (session 10): `DamagedShape.classes` replaced by `degPos : 1 ≤ deg` and `abLow : ¬IsEps → deg ≤ 2` (= G3's DamagedShapeW; the iff is false after Op 5). Only the abLow direction was ever used (nonEps ⊆ deg≠4, PMol protected set, hw1), so the proof changed by three one-line substitutions; low-degree eps atoms are unprotected, large-gap via epsLG, counted in Z. No step needed eps => deg>=3. Fresh rebuild of Damaged96Statement, Damaged96, Axioms12 exit 0; axioms std; hygiene clean. Backups *.pre-w.
READY g8-dcb


## G8-QUANT (R34) section
Files: APPB Algorithm/{S33LabelReduction,RuleTwoReduction,RuleThreePrimaryReduction,RuleSixReduction,DispatchExistence,ForestStepMain,ForestProp102,ForestRhoCore,ForestProp102Rho,SGMain,Prop102}.lean (m moved inside, after C₀); G8: Prop96Statement, Damaged96Statement, Damaged96, Rough96, Prop102Bridge, Prop104TwoProved, Odd96, Case23_96, Case6_96, EvenCase96, CaseV96, Case5, Case5Final, Assembly96, C4Main, C4NonExc, Split1Thm, Split2Thm, Final96/b/c, G8R/{Prop104One,Step0Y1c3,CoreCommon,CoreSplit,CoreTheorem,Prop104Two}, XRoute/{Branch,XMinus}.
Approach/finding: NO constant genuinely depends on m. Every multiplicative threshold C₀ comes from m-free lemmas (exists_s33_normal_reduction, exists_d33_*_reduction, exists_r3_normal_reduction, cleanup reductions, budget_final, theorem_A*, chain_A_bound, proposition_one_off_bound, ylem2_*); m enters only via L₀ (good-reductions, forest_half_gap_uniform, polylog absorption, splitK d m δ). Leaf count lemmas with `∃ C` after m (Uniform*/AppB*) were left unchanged: their C is absorbed into L₀ downstream. The change was purely quantifier order, compiler-checked. New helpers uniform_and_m, uniform_lift (G8R/CoreSplit). Inputs Prop102Input, Prop102SecondInput, Prop104TwoInputs lost their m argument.
Checks: fresh rebuild of the closure in buildQ2, 163/163 exit 0; axioms of prop96, case4SmallCell_proved, prop96_damaged: [propext, Classical.choice, Quot.sound]; hygiene grep clean over edited files; appb Prop102 rebuilt in build-quant exit 0 (docstring edit).
Deviation: G8R/ files are copies of moleprop4-t (G7); the copies were changed (originals untouched), so G7's Prop102Input etc. differ from these.
Errata: none new. Uncertainty: other packets compiling against old arities (finalcount-asm) must adapt: Prop96At d γ η (no m).
