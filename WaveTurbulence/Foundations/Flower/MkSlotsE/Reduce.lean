/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsE.ReduceMode

/-! # B3s-HELPER9 (MkSlotsE) 9: the reduction to δ's engine (centre-independent chain families)

If the chain pieces do not depend on the centre, `famC i c x = Q i c` (`famC i := fun c _ => Q i c`), then the slot
family `famX (fam₀ i) (famC i) X` is (definitionally) the same for every outer centre `X`; write
`famQ i := famX (fam₀ i) (fun c _ => Q i c) 0`. Then

* `hasSum_outerVal_modeX`: at one mode, `Σ_X outerValMμD … (Zw · chiX X) … = outerValMμD … Zw …`;
* `centre_value_const`: the centre-indexed value of `MkSlotsI.CentreForm` is δ's value
  `Σ_i sgn i Σ'_ξ (Π w) · outerValMμD … Zw …` for the families `famQ i` (all sums absolutely convergent: the joint
  summability over `⟨X, ξ⟩` is `EngX.repIntCMKS_centre_one`);
* **`representsIntMKSel_of_vineModesFixD_viaCentre`**: δ's engine `MkSlotsS.representsIntMKSel_of_vineModesFixD`
  for the families `famQ i` (hypotheses VERBATIM) follows from the centre-indexed engine (`centreEngine`): the
  centre-free engine is the special case. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.MkSlots
  WaveTurbulence.Flower.MkSlotsS
open WaveTurbulence.Flower.MkSlotsI (CentredSlot chiX famX ChainPiece)
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsE

open scoped Classical

/-- **The outer centres sum to one at a mode**: `Σ_X outerValMμD … (Zw · chiX X) … = outerValMμD … Zw …`. -/
theorem hasSum_outerVal_modeX {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL0 : 0 < P.L) (π : Stage1PieceMK P.d R)
    (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ fixLB π.Gsb π.layer tt π.fix π.lb)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    (amp : ReplacementSlot π.Gsb → Mom P.d → ℂ) (ctr : ReplacementSlot π.Gsb → Fin P.d → ℤ)
    (h1 : ∀ s k, ‖amp s k‖ ≤ 1) (h2 : ∀ s, SNorm (30 * P.d) 0 (amp s) ≤ 1)
    (h3 : ∀ p k, amp (Sum.inl p) k ≠ 0 → ‖k - latPt P.d (ctr (Sum.inl p))‖ ≤ 1)
    (frq : ReplacementSlot π.Gsb → Fin 2 → ℤ) {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ)
    (H : HingeFam J P.d) (Mh : J → ℝ) (hMh : ∀ j c, ∑' l, H.w j c l ≤ Mh j)
    (hHk : HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom (fun j => HkM j (modLam frq route j)) H)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r) :
    HasSum (fun X : CentredSlot π.Gsb → (Fin P.d → ℤ) =>
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0) *
            chiX P.L base X z) hS
          (fixMeasure π.fix) amp frq route hclk hmom HkM)
      (outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
          (fixMeasure π.fix) amp frq route hclk hmom HkM) := by
  have hsum := summable_mode_kernel hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk
    hmom HkM H Mh hMh hHk src src_dart src_root hfilt hind
  have h := hasSum_cindX (S := π.Gsb)
    (fun ξh : (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H
      Mh hMh hHk src src_dart src_root).Xi => ξh.1.2)
    (fun ξh => (π.Gsb.zeta * (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route
      hclk hmom HkM H Mh hMh hHk src src_dart src_root).constWH ξh) *
      modeKer hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh
        hHk src src_dart src_root ξh) hsum
  have e1 := outerVal_mode_eq hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom
    HkM H Mh hMh hHk src src_dart src_root hfilt hind hroute
  have e2 := fun X => outerVal_modeX_eq hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route
    hclk hmom HkM H Mh hMh hHk src src_dart src_root hfilt hind hroute X
  rw [← e1] at h
  exact h.congr_fun e2

/-- **One class term in the constant case**: with `famC = fun c _ => Q c`, the centre-indexed sum is δ's mode sum for
`famX fam₀ (fun c _ => Q c) 0`. -/
theorem centre_value_const_one {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL0 : 0 < P.L) (π : Stage1PieceMK P.d R)
    (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ fixLB π.Gsb π.layer tt π.fix π.lb)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    (sel : Finset (GBranch π.Gsb.tree)) (hselclk : ∀ v ∈ sel, ∀ j i, hclk j i ≠ Sum.inr v)
    (fam₀ : SlotFam π.Gsb P.d) (Q : CentredSlot π.Gsb → ChainPiece P.d)
    (μs : ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (θs : ReplacementSlot π.Gsb → ℝ) (hcθ : ∀ s, 2 * c + (selE route sel s 0 + selE route sel s 1) ≤ θs s)
    (hμ : ∀ s, ∑' l, maxBracketPow (θs s) (half ((famX fam₀ (fun c _ => Q c) 0).m s l)) *
      ENNReal.ofReal ((famX fam₀ (fun c _ => Q c) 0).w s l) ≤ μs s)
    (Kh : ℝ) (hKh : 0 ≤ Kh)
    (hhinge : ∀ ξ : ∀ s, (famX fam₀ (fun c _ => Q c) 0).Λ s,
      ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom
        (fun j => HkM j (modLam (fun s => (famX fam₀ (fun c _ => Q c) 0).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ Kh * ∏ j,
        (1 + |((modLam (fun s => (famX fam₀ (fun c _ => Q c) 0).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (Bi : ℝ) (hBi : 0 ≤ Bi)
    (hBi' : ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
        ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * Kh) *
        ∏ s, (ENNReal.ofReal (9 * selF route sel s) * μs s) ≤ ENNReal.ofReal Bi) :
    ∑' X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∑' ξ : ∀ t, (famX fam₀ (fun c _ => Q c) X).Λ t,
        centreVal π hS tt base roots selSk Dom route hclk hmom fam₀ (fun c _ => Q c) HkM ⟨X, ξ⟩ =
      ∑' ξ : ∀ t, (famX fam₀ (fun c _ => Q c) 0).Λ t,
        (((∏ t, (famX fam₀ (fun c _ => Q c) 0).w t (ξ t) : ℝ)) : ℂ) *
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
          (fixMeasure π.fix)
          (fun t => (famX fam₀ (fun c _ => Q c) 0).a t (ξ t)) (fun t => (famX fam₀ (fun c _ => Q c) 0).m t (ξ t))
          route hclk hmom HkM := by
  set F0 := famX fam₀ (fun c _ => Q c) 0 with hF0
  obtain ⟨hsv, -⟩ := repIntCMKS_centre_one hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD hfilt hind route hroute
    hclk hmom src src_dart src_root sel hselclk fam₀ (fun c _ => Q c) μs HkM hc hc1 θs hcθ (fun _ s => hμ s) Kh hKh
    (fun _ ξ => hhinge ξ) Bi hBi hBi'
  set f : (CentredSlot π.Gsb → (Fin P.d → ℤ)) → (∀ t, F0.Λ t) → ℂ := fun X ξ =>
    centreVal π hS tt base roots selSk Dom route hclk hmom fam₀ (fun c _ => Q c) HkM ⟨X, ξ⟩ with hf
  have hf2 : Summable (Function.uncurry f) :=
    ((Equiv.sigmaEquivProd (CentredSlot π.Gsb → (Fin P.d → ℤ)) (∀ t, F0.Λ t)).symm.summable_iff
      (f := centreVal π hS tt base roots selSk Dom route hclk hmom fam₀ (fun c _ => Q c) HkM)).mpr hsv
  have hcomm : ∑' X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∑' ξ : ∀ t, F0.Λ t, f X ξ =
      ∑' ξ : ∀ t, F0.Λ t, ∑' X : CentredSlot π.Gsb → (Fin P.d → ℤ), f X ξ := hf2.tsum_comm.symm
  refine hcomm.trans (tsum_congr fun ξ => ?_)
  obtain ⟨H, Mh, hMh, hHk, -⟩ := hhinge ξ
  have hm := hasSum_outerVal_modeX hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD hfilt hind
    (fun t => F0.a t (ξ t)) (fun t => F0.n t (ξ t)) (fun s k => F0.a_one s _ k) (fun s => F0.a_snorm s _)
    (fun q k hk => F0.a_supp q _ k hk) (fun t => F0.m t (ξ t)) route hroute hclk hmom HkM H Mh hMh hHk src src_dart
    src_root
  have := hm.mul_left (((∏ t, F0.w t (ξ t) : ℝ)) : ℂ)
  exact this.tsum_eq

/-- **The centre-indexed value in the constant case is δ's value.** -/
theorem centre_value_const {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL0 : 0 < P.L) (π : Stage1PieceMK P.d R)
    (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ fixLB π.Gsb π.layer tt π.fix π.lb)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    (sel : Finset (GBranch π.Gsb.tree)) (hselclk : ∀ v ∈ sel, ∀ j i, hclk j i ≠ Sum.inr v)
    {I : Type} [Fintype I] (sgn : I → ℂ)
    (fam₀ : I → SlotFam π.Gsb P.d) (Q : I → CentredSlot π.Gsb → ChainPiece P.d)
    (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (θs : ReplacementSlot π.Gsb → ℝ) (hcθ : ∀ s, 2 * c + (selE route sel s 0 + selE route sel s 1) ≤ θs s)
    (hμ : ∀ i s, ∑' l, maxBracketPow (θs s) (half ((famX (fam₀ i) (fun c _ => Q i c) 0).m s l)) *
      ENNReal.ofReal ((famX (fam₀ i) (fun c _ => Q i c) 0).w s l) ≤ μs i s)
    (Kh : I → ℝ) (hKh : ∀ i, 0 ≤ Kh i)
    (hhinge : ∀ i (ξ : ∀ s, (famX (fam₀ i) (fun c _ => Q i c) 0).Λ s),
      ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom
        (fun j => HkM i j (modLam (fun s => (famX (fam₀ i) (fun c _ => Q i c) 0).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ Kh i * ∏ j,
        (1 + |((modLam (fun s => (famX (fam₀ i) (fun c _ => Q i c) 0).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (Bi : I → ℝ) (hBi : ∀ i, 0 ≤ Bi i)
    (hBi' : ∀ i, ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
        ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * Kh i) *
        ∏ s, (ENNReal.ofReal (9 * selF route sel s) * μs i s) ≤ ENNReal.ofReal (Bi i)) :
    (∑ i, sgn i * ∑' X : CentredSlot π.Gsb → (Fin P.d → ℤ),
      ∑' ξ : ∀ t, (famX (fam₀ i) (fun c _ => Q i c) X).Λ t,
        (((∏ t, (famX (fam₀ i) (fun c _ => Q i c) X).w t (ξ t) : ℝ)) : ℂ) *
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0) *
            chiX P.L base X z) hS
          (fixMeasure π.fix)
          (fun t => (famX (fam₀ i) (fun c _ => Q i c) X).a t (ξ t))
          (fun t => (famX (fam₀ i) (fun c _ => Q i c) X).m t (ξ t))
          route hclk hmom (HkM i)) =
      ∑ i, sgn i * ∑' ξ : ∀ t, (famX (fam₀ i) (fun c _ => Q i c) 0).Λ t,
        (((∏ t, (famX (fam₀ i) (fun c _ => Q i c) 0).w t (ξ t) : ℝ)) : ℂ) *
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
          (fixMeasure π.fix)
          (fun t => (famX (fam₀ i) (fun c _ => Q i c) 0).a t (ξ t))
          (fun t => (famX (fam₀ i) (fun c _ => Q i c) 0).m t (ξ t))
          route hclk hmom (HkM i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact centre_value_const_one hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD hfilt hind route hroute hclk hmom
    src src_dart src_root sel hselclk (fam₀ i) (Q i) (μs i) (HkM i) hc hc1 θs hcθ (hμ i) (Kh i) (hKh i) (hhinge i)
    (Bi i) (hBi i) (hBi' i)

/-- **The reduction lemma**: δ's engine `MkSlotsS.representsIntMKSel_of_vineModesFixD` for centre-independent chain
families `famX (fam₀ i) (fun c _ => Q i c) 0`, with its hypotheses VERBATIM, is a consequence of the centre-indexed
engine (`representsIntMKSel_of_centreModes`): the centre-indexed `hval` is δ's (`centre_value_const`). -/
theorem representsIntMKSel_of_vineModesFixD_viaCentre {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    (hη0 : 0 ≤ P.η)
    (π : Stage1PieceMK P.d R) (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ fixLB π.Gsb π.layer tt π.fix π.lb)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    (cP : ℝ) (hcP : 0 ≤ cP)
    {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    (sel : Finset (GBranch π.Gsb.tree)) (hselclk : ∀ v ∈ sel, ∀ j i, hclk j i ≠ Sum.inr v)
    {I : Type} [Fintype I] (sgn : I → ℂ)
    (fam₀ : I → SlotFam π.Gsb P.d) (Q : I → CentredSlot π.Gsb → ChainPiece P.d)
    (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (θs : ReplacementSlot π.Gsb → ℝ) (hcθ : ∀ s, 2 * c + (selE route sel s 0 + selE route sel s 1) ≤ θs s)
    (hμ : ∀ i s, ∑' l, maxBracketPow (θs s) (half ((famX (fam₀ i) (fun c _ => Q i c) 0).m s l)) *
      ENNReal.ofReal ((famX (fam₀ i) (fun c _ => Q i c) 0).w s l) ≤ μs i s)
    (x K Ch : ℝ) (hx : x = P.C₁ * Real.sqrt P.δ) (hK : 1 ≤ K) (hCh : 1 ≤ Ch)
    (hC : Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch ≤ P.C₁)
    (sz g : ReplacementSlot π.Gsb → ℕ) (lf : I → ReplacementSlot π.Gsb → ℝ) (hlf : ∀ i s, 0 ≤ lf i s)
    (hμb : ∀ i s, μs i s ≤ ENNReal.ofReal (K * x ^ (sz s) * P.L ^ (-(P.η ^ 8) * (g s : ℝ)) * lf i s))
    (M0 : I → J → ℝ) (cl2 gj nj : J → ℕ) (lfj : I → J → ℝ) (hlfj : ∀ i j, 0 ≤ lfj i j)
    (hM : ∀ i j, 0 ≤ M0 i j ∧ M0 i j ≤ x ^ (cl2 j) *
      P.L ^ (-(P.η ^ 8) * (gj j : ℝ) - P.η ^ 2 / 2 * (nj j : ℝ) + P.η ^ 7) * lfj i j)
    (hhinge : ∀ i (ξ : ∀ s, (famX (fam₀ i) (fun c _ => Q i c) 0).Λ s), ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom
        (fun j => HkM i j (modLam (fun s => (famX (fam₀ i) (fun c _ => Q i c) 0).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ (∏ j, (Ch * M0 i j)) *
        ∏ j, (1 + |((modLam (fun s => (famX (fam₀ i) (fun c _ => Q i c) 0).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (n : ℕ) (s : ℝ)
    (hs : ∑ i, ‖sgn i‖ * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j) ≤
      P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s)
    (hexp : (∑ t, sz t) + ∑ j, cl2 j = n - π.Gsb.order)
    (hg : π.gsk ≤ (∑ t, g t) + ∑ j, gj j) (hb : π.bsk ≤ ∑ j, nj j) (hh : Fintype.card J ≤ π.Cs.hinges.card)
    (hJ : Fintype.card J ≤ π.Gsb.order) (val : ℂ)
    (hval : val = ∑ i, sgn i * ∑' ξ : ∀ t, (famX (fam₀ i) (fun c _ => Q i c) 0).Λ t,
        (((∏ t, (famX (fam₀ i) (fun c _ => Q i c) 0).w t (ξ t) : ℝ)) : ℂ) *
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
          (fixMeasure π.fix)
          (fun t => (famX (fam₀ i) (fun c _ => Q i c) 0).a t (ξ t))
          (fun t => (famX (fam₀ i) (fun c _ => Q i c) 0).m t (ξ t)) route hclk hmom (HkM i)) :
    RepresentsIntMKSel π sel n cP tt base roots s val := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hC1 : 0 ≤ P.C₁ := C₁_nonneg_of_hC hd1 hK hCh hC
  have hT0 : 0 ≤ repCoreMK P π n := repCoreMK_nonneg π n hL1 hC1
  have hBi0 : ∀ i, 0 ≤ repCoreMK P π n * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j) := fun i =>
    mul_nonneg hT0 (mul_nonneg (Finset.prod_nonneg fun t _ => mul_nonneg (selF_nonneg route sel t) (hlf i t))
      (Finset.prod_nonneg fun j _ => hlfj i j))
  have hcv := centre_value_const hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD hfilt hind route hroute hclk hmom
    src src_dart src_root sel hselclk sgn fam₀ Q μs HkM hc hc1 θs hcθ hμ (fun i => ∏ j, (Ch * M0 i j))
    (fun i => Finset.prod_nonneg fun j _ => mul_nonneg (by linarith) (hM i j).1) hhinge
    (fun i => repCoreMK P π n * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j)) hBi0
    (fun i => centre_numerics hd1 hL1 hη0 π hS route sel μs x K Ch hx hK hCh hC sz g lf hlf hμb M0 cl2 gj nj lfj hlfj
      hM n hexp hg hb hh hJ i)
  exact representsIntMKSel_of_centreModes hd1 hL1 hη0 π hS tt base roots selSk hgsp Dom hsliceD hfilt hind cP hcP
    route hroute hclk hmom src src_dart src_root sel hselclk sgn fam₀ (fun i c _ => Q i c) μs HkM hc hc1 θs hcθ
    (fun i _ s => hμ i s) x K Ch hx hK hCh hC sz g lf hlf hμb M0 cl2 gj nj lfj hlfj hM (fun i _ ξ => hhinge i ξ) n s
    hs hexp hg hb hh hJ val (hval.trans hcv.symm)

end WaveTurbulence.Flower.MkSlotsE
