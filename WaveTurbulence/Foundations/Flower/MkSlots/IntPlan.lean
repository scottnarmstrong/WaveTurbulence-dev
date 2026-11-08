/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntPiece

/-! # B3s MK-SLOTS (integration): plan, the `|J| = R` finding, and the corrected α statements

## Finding F-B3s-8 (STATEMENT; accepted, ruling R185): without `J.card = R` the mass `b ^ N` is false

`ClassRepAlpha cP P` (and B4's `MarkedClassRepresentsMK`, `MkDefs.Stage1ReductionAtMK(Full)`) concludes
`RepresentsIntMK … (b ^ N) (classValue …)` for EVERY cap set `J`, while `MarkedComponentBoundAtI` (the consumer) has
`J.card = R`. The class value is homogeneous in the profile family `h`: `leafProdCap LG J h k` is a product over the
`N + R` input leaves (sign `+`, one per leaf pair of a garden of order `N` with `2R` trees), with profile `1` exactly on
the pairs meeting a cap tree, and every other factor of `markedWt` (frontier, dagger, stem filters) is independent of
`h`. So `classValue(b • h₀) = b ^ n_free · classValue(h₀)` with `n_free = N + R - #{pairs meeting J}`, while
`SNormR (b • h₀) = b · SNormR h₀` and the bound of `RepresentsIntMK` at mass `b ^ N` is `K(P, piece) · b ^ N` times
`|splicedKernelMK| ≤ M(P, piece, roots)`, both independent of `b, h`. Configuration: `J = ∅`, any canonical
irreducible class with a nonzero class value at some `h₀` with `SNormR h₀ ≤ 1` (plain patterns, no selection, no stem
filter, frontier scales `none`, dagger `none`): then `n_free = N + R > N`, and `b → ∞` contradicts the bound. With
`J.card = R`, `CapGeo` (cap trees are single leaves) and irreducibility (no pair of two cap roots), exactly `R` pairs
meet `J` and `n_free = N`.

Fix (ruling R185): add `J.card = R →` after the `J` binder (as in `MarkedComponentBoundAtI`). The corrected α
statements are `ClassRepAlphaJ` and `MarkedClassRepresentsMKαJ` below; `markedClassRepresentsMKαJ_of_rep` is the α
bridge for them (the proof of `AlphaTop.markedClassRepresentsMKα_of_rep`). `ClassRepAlphaJ` states the
representation for the α piece at the class marking, `pieceAt … (classMk mkF (repPt π))` (definitionally
`AlphaTop.pieceα`); this file does not import `AlphaTop`/`Statement` (whose `markedClassRepresentsMKα_of` reads B4's
`MarkedClassRepresentsMK`, now carrying `J.card = R` after R185).

## Plan and status of the integration (files `MkSlots/Int*.lean`, all built, standard axioms)
Done:
1. `IntCapHyp`: **`CapSlotObligation`** (the isolated analytic input on cap-couple slots) and its monotonicity.
2. `IntAdm`: the run-start admissibility from B4's data — `twistClosedAdm_of_marked`, `startAt_admP` (B3's two
   hypotheses `TwistClosedAdm` and `Adm (startAt …)` follow from `MarkedTwistClosed` and `FineMarking.sub`).
3. `IntClass`: `classValue_eq_outputs` (the class value is the sum over the fine′ outputs of the representative;
   no further hypothesis), `sum_members_eq_gen`.
4. `IntWeight`: `classSummand_eq_capKernel` (the frozen class summand is the pinned weighted leaf kernel with the
   anchored profiles `anchProfiles` and the node weight `capNodeW`).
5. `IntSplit` / `IntGeo`: the native split `∏ capNodeW = (∏ chainW) · restW`; `nonCap_slotFn_eq_slotFW` (every slot
   that is not a cap pair has B3's `slotFW` as pinned slot kernel: pins, anchored leaves and the non-core dagger lie in
   cap natives).
6. `IntT4`: the pinned class sum (`sum_classU_outerValMμ`, `weightedClassFactorizationμ`).
7. `IntSlotFam`: the cap swap (`skelValF_capSwap`, `unitKernelMG_capSwap`, `RegBound.capSwap`, `capPair_label`,
   `capPair_not_regional`) and the combined outer family (`combineFam`, `hasSum_combineFam_of_not/_of_cap`,
   `mass_combineFam`).
8. `IntMass`, `IntCount`, `IntPiece`: `representsIntMK_C₁_lift`, `card_freeInputs` (`N` free input leaves when
   `J.card = R`), `pieceAt` (the α piece at a marked set) and `representsIntMK_pieceAt_congr`.
Remaining for `ClassRepAlphaJ` (in order):
(R-core) class-commonness of the core pins / capped flower parents at `G_sb` atoms (a core is a capped flower parent
  iff a child of its skeleton branch is a skeleton leaf paired with a cap root whose couple code is trivial:
  `SpliceShape` `child`/`leaf`/`pair`/`tree_eq`, and outer couple codes are preserved by every operation,
  `LFConstruction.couple_other`, lifted along batches as B3's `batch_spliceKerQMk`);
(R-cap) class-commonness of the pinned cap slot kernels (B3's `WAlign` chain with `native_couple_eq` and the ordinary
  correspondence `OrdCorr` transporting `fixCap`, `dagNodeW`, `anchProfiles`);
(M) the member identity: `classSummand_eq_capKernel` → reconstruction (B3's `selPMk_iff_related`) →
  `prod_capNodeW_split` + `restW_cosetDecoration` (the indicator into the selection, `restConst` into `sgn`, with
  `RestInd` on the skeleton = the piece's `sibIndOf` on `G_sb` through `SpliceShape.child`/`leaf`/`sign` and
  (R-core)) → `kernelLeaves_skeleton_reduction_selNWF` (node weight `chainW`) →
  `skelValF_capSwap` → `hasSum_skelValF_outerValMμ` (B3's `memShape_*`, `hZ_commonMk`, `member_ker_eqWMk` through
  `nonCap_slotFn_eq_slotFW` and `unitKernelMG_capSwap`; pins `fixMeasure` through (R-core)); class sum by
  `weightedClassFactorizationμ`;
(A) the assembly with `representsIntMK_of_vineModesFix` at `pieceAt … (mkU a.prime)` (B3's `WAssembly` with the
  combined family, mass `c_F^{16N} · L^{(31d+6)R} · b^N` via `card_freeInputs`, then `representsIntMK_C₁_lift` and
  `representsIntMK_absorb`, `37 ≤ cP`);
(P) the prefix (`prefix_and` of B3's prefix data with `CapSlotObligation`, `capSlotObligationAt_mono`). -/


@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.Flower.Stage1MKGate

namespace WaveTurbulence.Flower.MkSlots

/-- **The α analytic core with `|J| = R`** (`ClassRepAlpha` with the hypothesis `J.card = R`, F-B3s-8). -/
def ClassRepAlphaJ (cP : ℝ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (J : Finset (Fin (2 * R))), J.card = R → ∀ (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ),
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t,
  (∀ j, pat j = FixPat.plain) → (∀ j, kSel j = none) →
  ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    (∀ j, σ j = none) →
    1 ≤ b → (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) → (∀ j, P.L ≤ Rs j) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∀ (mkF : Stage1Mk.MarkFn (2 * R)), FineMarking J pat t s kSel σ mkF →
  ∀ π : PcA R p (objKind (2 * R)) A mkF,
    (¬ StemDep σ kSel ∨ ∀ a : PrescribedPrimeGarden (2 * R),
      Related (p := p) (kind := objKind (2 * R)) (repPt π) a mkF → CleanPt J a) →
  (pieceAt P J t s kSel (repPt π) (classMk mkF (repPt π)) dag).RepresentsIntMK N cP (fun _ => t) 0 roots (b ^ N)
    (classValue P p J pat kSel t s A roots h Rf σ Rs dag mkF π)

/-- **Milestone α with `|J| = R`** (`MarkedClassRepresentsMKα` with the hypothesis `J.card = R`, F-B3s-8). -/
def MarkedClassRepresentsMKαJ (cP cθ : ℝ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (J : Finset (Fin (2 * R))), J.card = R → ∀ (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ),
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t,
  (∀ j, pat j = FixPat.plain) → (∀ j, kSel j = none) →
  ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    (∀ j, σ j = none) →
    1 ≤ b → (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) → (∀ j, P.L ≤ Rs j) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∀ (mkF : Stage1Mk.MarkFn (2 * R)), FineMarking J pat t s kSel σ mkF →
  ∀ π : PcA R p (objKind (2 * R)) A mkF,
    (¬ StemDep σ kSel ∨ ∀ a : PrescribedPrimeGarden (2 * R),
      Related (p := p) (kind := objKind (2 * R)) (repPt π) a mkF → CleanPt J a) →
  ∃ (prot : Finset (GBranch (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree))
    (fix : GBranch (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree → Option ℝ)
    (filt : GBranch (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree →
      Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree → Mom P.d) →
      ℝ)
    (selR : Finset (GBranch (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree)),
    ClassPieceOK (classPiece P mkF (repPt π) prot (protI (repPt π).layered J pat t s kSel).card fix filt ind) selR
      N cP cθ t b roots kSel Rs (classValue P p J pat kSel t s A roots h Rf σ Rs dag mkF π)

/-- **Milestone α (`|J| = R`) from the analytic core** (the proof of `markedClassRepresentsMKα_of_rep`). -/
theorem markedClassRepresentsMKαJ_of_rep {cP cθ : ℝ} {P : WTParams} (hL : 1 ≤ P.L) (hrep : ClassRepAlphaJ cP P) :
    MarkedClassRepresentsMKαJ cP cθ P := by
  intro p hp R h1 h2 N hN1 hN2 J hJ pat kSel t ht s hs hpat hk A hA hpl hTC roots hh b Rf σ Rs dag hσ hb hsn hRf hRs
    hhigh mkF hmk π hπ
  have hrep' := hrep p hp R h1 h2 N hN1 hN2 J hJ pat kSel t ht s hs hpat hk A hA hpl hTC roots hh b Rf σ Rs dag hσ hb
    hsn hRf hRs hhigh mkF hmk π hπ
  have hpat' : pat = fun _ => FixPat.plain := funext hpat
  have hk' : kSel = fun _ => none := funext hk
  subst hpat' hk'
  have hG : CapGeo (repPt π).layered J p := (hA _ (repPt_layered_memMk π)).2.2.2.2.1
  refine ⟨protOf J (fun _ => FixPat.plain) t s (fun _ => none) mkF (repPt π),
    fixOf J (fun _ => FixPat.plain) t s mkF (repPt π), fun _ => none,
    sibIndOf J mkF (repPt π) dag (flwAt J (repPt π) (classMk mkF (repPt π))), ∅, ?_⟩
  refine ⟨?_, pieceRest_alpha P J p mkF (repPt π) hG t s hs ht.2 _ dag (flwAt J (repPt π) (classMk mkF (repPt π)))
      cθ,
    fun v hv => absurd hv (Finset.notMem_empty v), fun v hv => absurd hv (Finset.notMem_empty v),
    Nat.zero_le _, representsIntMK_mono_cPJ _ (by linarith) hL hrep',
    fun v hv => absurd hv (Finset.notMem_empty v)⟩
  rw [selMassMK_noneJ]
  exact (representsIntMKSel_empty (pieceAt P J t s (fun _ => none) (repPt π) (classMk mkF (repPt π)) dag) N cP
    (fun _ => t) 0 roots (b ^ N) _).2 hrep'

end WaveTurbulence.Flower.MkSlots
