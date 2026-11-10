/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsE.EngX

/-! # B3s-HELPER9 (MkSlotsE) 7: the centre-indexed engine — `CentreEngine`

* `centre_numerics`: the numerics of δ's `MkSlotsS.repIntCMKS_of_vineModesFixD` (copied verbatim: they concern only
  `μs`, `lf`, `M0`, … which do not depend on the outer centres; the constant is the engine's
  `Cchi · nodeBallCard · (9K)² · Ch ≤ C₁`, no new constant);
* `repIntCMKS_of_centreModes`: the count-measure representation of the centre-indexed value;
* **`representsIntMKSel_of_centreModes`**: δ's `representsIntMKSel_of_vineModesFixD` with the centre-indexed slot
  families `famX (fam₀ i) (famC i) X` (moment and hinge hypotheses for EVERY outer centre assignment `X`, uniformly)
  and the centre-indexed `hval` of `MkSlotsI.CentreForm`;
* **`repMK_of_centreModes`**: the `repMK` companion (δ's `repMK_of_rep`);
* **`centreEngine : MkSlotsI.CentreEngine`**. -/

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

/-- **The numerics of δ's engine** (the first branch of `MkSlotsS.repIntCMKS_of_vineModesFixD`, copied). -/
theorem centre_numerics {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (hη0 : 0 ≤ P.η)
    (π : Stage1PieceMK P.d R) (hS : π.Gsb.IsPlain) {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J) (sel : Finset (GBranch π.Gsb.tree))
    {I : Type} [Fintype I] (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (x K Ch : ℝ) (hx : x = P.C₁ * Real.sqrt P.δ) (hK : 1 ≤ K) (hCh : 1 ≤ Ch)
    (hC : Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch ≤ P.C₁)
    (sz g : ReplacementSlot π.Gsb → ℕ) (lf : I → ReplacementSlot π.Gsb → ℝ) (hlf : ∀ i s, 0 ≤ lf i s)
    (hμb : ∀ i s, μs i s ≤ ENNReal.ofReal (K * x ^ (sz s) * P.L ^ (-(P.η ^ 8) * (g s : ℝ)) * lf i s))
    (M0 : I → J → ℝ) (cl2 gj nj : J → ℕ) (lfj : I → J → ℝ) (hlfj : ∀ i j, 0 ≤ lfj i j)
    (hM : ∀ i j, 0 ≤ M0 i j ∧ M0 i j ≤ x ^ (cl2 j) *
      P.L ^ (-(P.η ^ 8) * (gj j : ℝ) - P.η ^ 2 / 2 * (nj j : ℝ) + P.η ^ 7) * lfj i j)
    (n : ℕ)
    (hexp : (∑ t, sz t) + ∑ j, cl2 j = n - π.Gsb.order)
    (hg : π.gsk ≤ (∑ t, g t) + ∑ j, gj j) (hb : π.bsk ≤ ∑ j, nj j) (hh : Fintype.card J ≤ π.Cs.hinges.card)
    (hJ : Fintype.card J ≤ π.Gsb.order) (i : I) :
    ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
        ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * ∏ j, (Ch * M0 i j)) *
        ∏ s, (ENNReal.ofReal (9 * selF route sel s) * μs i s) ≤
      ENNReal.ofReal (repCoreMK P π n * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j)) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  obtain ⟨hCge, -⟩ := Cchi_spec hd1
  have hb1 : (1 : ℝ) ≤ nodeBallCard P.d := by exact_mod_cast nodeBallCard_pos P.d
  have hC1 : 0 ≤ P.C₁ := C₁_nonneg_of_hC hd1 hK hCh hC
  have hx0 : 0 ≤ x := by
    rw [hx]
    exact mul_nonneg hC1 (Real.sqrt_nonneg _)
  have hbr : Fintype.card (GBranch π.Gsb.tree) = π.Gsb.order := WaveTurbulence.Mole.card_gbranch π.Gsb.tree
  have hslotsc : Fintype.card (ReplacementSlot π.Gsb) = 2 * π.Gsb.order + R := by
    have hpairs := sourcePair_card_twice π.Gsb hS
    unfold ReplacementSlot
    rw [Fintype.card_sum, hbr]
    omega
  have hord : ∑ j, (π.Gsb.tree j).order = π.Gsb.order := rfl
  have hKh0 : 0 ≤ ∏ j, (Ch * M0 i j) := Finset.prod_nonneg fun j _ => mul_nonneg (by linarith) (hM i j).1
  have hlf' : ∀ t, 0 ≤ selF route sel t * lf i t := fun t => mul_nonneg (selF_nonneg route sel t) (hlf i t)
  have hne : ∀ t, μs i t ≠ ⊤ := fun t => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hμb i t)
  have hμr : ∀ t, 0 ≤ selF route sel t * (μs i t).toReal ∧ selF route sel t * (μs i t).toReal ≤ K * x ^ (sz t) *
      P.L ^ (-(P.η ^ 8) * (g t : ℝ)) * (selF route sel t * lf i t) := fun t => by
    have h0 : (μs i t).toReal ≤ K * x ^ (sz t) * P.L ^ (-(P.η ^ 8) * (g t : ℝ)) * lf i t :=
      ENNReal.toReal_le_of_le_ofReal (by
        have := hlf i t
        have : 0 ≤ P.L ^ (-(P.η ^ 8) * (g t : ℝ)) := Real.rpow_nonneg hL0.le _
        have : 0 ≤ x ^ (sz t) := pow_nonneg hx0 _
        have : 0 ≤ K := by linarith
        positivity) (hμb i t)
    have hF := selF_nonneg route sel t
    refine ⟨mul_nonneg hF ENNReal.toReal_nonneg, ?_⟩
    calc selF route sel t * (μs i t).toReal
        ≤ selF route sel t * (K * x ^ (sz t) * P.L ^ (-(P.η ^ 8) * (g t : ℝ)) * lf i t) :=
          mul_le_mul_of_nonneg_left h0 hF
      _ = _ := by ring
  have hreal := vine_mass_le_repBound (nsb := π.Gsb.order) (R := R)
    (ιs := ReplacementSlot π.Gsb) (ιj := J) hslotsc hJ x P.L K (Cchi P.d) (nodeBallCard P.d : ℝ) Ch P.C₁
    (P.η ^ 8) (P.η ^ 2 / 2) (P.η ^ 7) hx0 hL1 hK hCge hb1 hCh hC (by positivity) (by positivity) (by positivity)
    (fun t => selF route sel t * (μs i t).toReal) sz g (fun t => selF route sel t * lf i t) hlf' hμr
    (M0 i) cl2 gj nj (lfj i) (hlfj i) (hM i)
    n π.Gsb.order π.gsk π.bsk π.Cs.hinges.card hexp rfl hg hb hh
  have ht : ∀ t, ENNReal.ofReal (9 * selF route sel t) * μs i t =
      ENNReal.ofReal (9 * (selF route sel t * (μs i t).toReal)) := fun t => by
    have hF := selF_nonneg route sel t
    rw [← mul_assoc, ENNReal.ofReal_mul (p := 9 * selF route sel t) (q := (μs i t).toReal) (by positivity),
      ENNReal.ofReal_toReal (hne t)]
  have hmu : ∏ t, (ENNReal.ofReal (9 * selF route sel t) * μs i t) =
      ENNReal.ofReal (9 ^ (2 * π.Gsb.order + R) * ∏ t, (selF route sel t * (μs i t).toReal)) := by
    rw [Finset.prod_congr rfl fun t _ => ht t, ← ENNReal.ofReal_prod_of_nonneg
      (fun t _ => mul_nonneg (by norm_num) (mul_nonneg (selF_nonneg route sel t) ENNReal.toReal_nonneg)),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hslotsc]
  rw [hmu, hbr, hord, ← ENNReal.ofReal_mul (by
    have := hKh0; have := Cchi_spec hd1; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hCχ0 : 0 ≤ Cchi P.d := by linarith
  calc _ = Cchi P.d ^ π.Gsb.order * (9 ^ (2 * π.Gsb.order + R) *
          ∏ t, (selF route sel t * (μs i t).toReal)) *
        (nodeBallCard P.d : ℝ) ^ π.Gsb.order * ∏ j, (Ch * M0 i j) := by
        push_cast; ring
    _ ≤ _ := hreal
    _ = _ := by simp only [repCoreMK, hx]

open scoped Classical in
/-- **The count-measure core of the centre-indexed engine**: a `RepIntCMKS` of mass `repCoreMK · L^{7(47d+2)·#sel} · s`
(δ's `repIntCMKS_of_vineModesFixD` with the centre-indexed families). -/
theorem repIntCMKS_of_centreModes {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (hη0 : 0 ≤ P.η)
    (π : Stage1PieceMK P.d R) (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
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
    (fam₀ : I → SlotFam π.Gsb P.d) (famC : I → CentredSlot π.Gsb → (Fin P.d → ℤ) → ChainPiece P.d)
    (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (θs : ReplacementSlot π.Gsb → ℝ) (hcθ : ∀ s, 2 * c + (selE route sel s 0 + selE route sel s 1) ≤ θs s)
    (hμ : ∀ i (X : CentredSlot π.Gsb → (Fin P.d → ℤ)) s, ∑' l, maxBracketPow (θs s)
      (half ((famX (fam₀ i) (famC i) X).m s l)) * ENNReal.ofReal ((famX (fam₀ i) (famC i) X).w s l) ≤ μs i s)
    (x K Ch : ℝ) (hx : x = P.C₁ * Real.sqrt P.δ) (hK : 1 ≤ K) (hCh : 1 ≤ Ch)
    (hC : Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch ≤ P.C₁)
    (sz g : ReplacementSlot π.Gsb → ℕ) (lf : I → ReplacementSlot π.Gsb → ℝ) (hlf : ∀ i s, 0 ≤ lf i s)
    (hμb : ∀ i s, μs i s ≤ ENNReal.ofReal (K * x ^ (sz s) * P.L ^ (-(P.η ^ 8) * (g s : ℝ)) * lf i s))
    (M0 : I → J → ℝ) (cl2 gj nj : J → ℕ) (lfj : I → J → ℝ) (hlfj : ∀ i j, 0 ≤ lfj i j)
    (hM : ∀ i j, 0 ≤ M0 i j ∧ M0 i j ≤ x ^ (cl2 j) *
      P.L ^ (-(P.η ^ 8) * (gj j : ℝ) - P.η ^ 2 / 2 * (nj j : ℝ) + P.η ^ 7) * lfj i j)
    (hhinge : ∀ i (X : CentredSlot π.Gsb → (Fin P.d → ℤ)) (ξ : ∀ s, (famX (fam₀ i) (famC i) X).Λ s),
      ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom
        (fun j => HkM i j (modLam (fun s => (famX (fam₀ i) (famC i) X).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ (∏ j, (Ch * M0 i j)) *
        ∏ j, (1 + |((modLam (fun s => (famX (fam₀ i) (famC i) X).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (n : ℕ) (s : ℝ)
    (hs : ∑ i, ‖sgn i‖ * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j) ≤
      P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s)
    (hexp : (∑ t, sz t) + ∑ j, cl2 j = n - π.Gsb.order)
    (hg : π.gsk ≤ (∑ t, g t) + ∑ j, gj j) (hb : π.bsk ≤ ∑ j, nj j) (hh : Fintype.card J ≤ π.Cs.hinges.card)
    (hJ : Fintype.card J ≤ π.Gsb.order) :
    RepIntCMKS π sel tt base roots
      (∑ i, sgn i * ∑' X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∑' ξ : ∀ t, (famX (fam₀ i) (famC i) X).Λ t,
        centreVal π hS tt base roots selSk Dom route hclk hmom (fam₀ i) (famC i) (HkM i) ⟨X, ξ⟩)
      (repCoreMK P π n * (P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s)) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hC1 : 0 ≤ P.C₁ := C₁_nonneg_of_hC hd1 hK hCh hC
  set T : ℝ := repCoreMK P π n with hT
  have hT0 : 0 ≤ T := repCoreMK_nonneg π n hL1 hC1
  have hlf' : ∀ i t, 0 ≤ selF route sel t * lf i t := fun i t => mul_nonneg (selF_nonneg route sel t) (hlf i t)
  have hBi0 : ∀ i, 0 ≤ T * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j) := fun i =>
    mul_nonneg hT0 (mul_nonneg (Finset.prod_nonneg fun t _ => hlf' i t) (Finset.prod_nonneg fun j _ => hlfj i j))
  have hfin := RepIntCMKS.finset_sum (π := π) (sel := sel) (tt := tt) (base := base) (roots := roots)
    Finset.univ (fun i => sgn i * ∑' X : CentredSlot π.Gsb → (Fin P.d → ℤ),
      ∑' ξ : ∀ t, (famX (fam₀ i) (famC i) X).Λ t,
        centreVal π hS tt base roots selSk Dom route hclk hmom (fam₀ i) (famC i) (HkM i) ⟨X, ξ⟩) (fun i => ‖sgn i‖ * (T * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j)))
    (fun i _ => mul_nonneg (norm_nonneg _) (hBi0 i)) (fun i _ => by
      refine RepIntCMKS.smul ?_ (sgn i)
      refine (repIntCMKS_centre_one hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD hfilt hind route hroute
        hclk hmom src src_dart src_root sel hselclk (fam₀ i) (famC i) (μs i) (HkM i) hc hc1 θs hcθ (hμ i)
        (∏ j, (Ch * M0 i j)) (Finset.prod_nonneg fun j _ => mul_nonneg (by linarith) (hM i j).1) (hhinge i)
        _ (hBi0 i) ?_).2
      exact centre_numerics hd1 hL1 hη0 π hS route sel μs x K Ch hx hK hCh hC sz g lf hlf hμb M0 cl2 gj nj lfj hlfj hM
        n hexp hg hb hh hJ i)
  refine hfin.mono ?_
  calc ∑ i, ‖sgn i‖ * (T * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j))
      = T * ∑ i, ‖sgn i‖ * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ T * (P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s) := mul_le_mul_of_nonneg_left hs hT0

open scoped Classical in
/-- **The centre-indexed selected engine** (B3s-HELPER9 deliverable): δ's `representsIntMKSel_of_vineModesFixD` in
which the value is the centre-indexed outer mode form of `MkSlotsI.CentreForm`: the chain-slot families of the centred
slots are indexed by the outer centre assignment `X` (`famX (fam₀ i) (famC i) X`), combined through the node partition
`chiX X` in the decoration weight; the moment and hinge hypotheses hold for every `X` with bounds independent of `X`. -/
theorem representsIntMKSel_of_centreModes {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
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
    (fam₀ : I → SlotFam π.Gsb P.d) (famC : I → CentredSlot π.Gsb → (Fin P.d → ℤ) → ChainPiece P.d)
    (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (θs : ReplacementSlot π.Gsb → ℝ) (hcθ : ∀ s, 2 * c + (selE route sel s 0 + selE route sel s 1) ≤ θs s)
    (hμ : ∀ i (X : CentredSlot π.Gsb → (Fin P.d → ℤ)) s, ∑' l, maxBracketPow (θs s)
      (half ((famX (fam₀ i) (famC i) X).m s l)) * ENNReal.ofReal ((famX (fam₀ i) (famC i) X).w s l) ≤ μs i s)
    (x K Ch : ℝ) (hx : x = P.C₁ * Real.sqrt P.δ) (hK : 1 ≤ K) (hCh : 1 ≤ Ch)
    (hC : Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch ≤ P.C₁)
    (sz g : ReplacementSlot π.Gsb → ℕ) (lf : I → ReplacementSlot π.Gsb → ℝ) (hlf : ∀ i s, 0 ≤ lf i s)
    (hμb : ∀ i s, μs i s ≤ ENNReal.ofReal (K * x ^ (sz s) * P.L ^ (-(P.η ^ 8) * (g s : ℝ)) * lf i s))
    (M0 : I → J → ℝ) (cl2 gj nj : J → ℕ) (lfj : I → J → ℝ) (hlfj : ∀ i j, 0 ≤ lfj i j)
    (hM : ∀ i j, 0 ≤ M0 i j ∧ M0 i j ≤ x ^ (cl2 j) *
      P.L ^ (-(P.η ^ 8) * (gj j : ℝ) - P.η ^ 2 / 2 * (nj j : ℝ) + P.η ^ 7) * lfj i j)
    (hhinge : ∀ i (X : CentredSlot π.Gsb → (Fin P.d → ℤ)) (ξ : ∀ s, (famX (fam₀ i) (famC i) X).Λ s),
      ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom
        (fun j => HkM i j (modLam (fun s => (famX (fam₀ i) (famC i) X).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ (∏ j, (Ch * M0 i j)) *
        ∏ j, (1 + |((modLam (fun s => (famX (fam₀ i) (famC i) X).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (n : ℕ) (s : ℝ)
    (hs : ∑ i, ‖sgn i‖ * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j) ≤
      P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s)
    (hexp : (∑ t, sz t) + ∑ j, cl2 j = n - π.Gsb.order)
    (hg : π.gsk ≤ (∑ t, g t) + ∑ j, gj j) (hb : π.bsk ≤ ∑ j, nj j) (hh : Fintype.card J ≤ π.Cs.hinges.card)
    (hJ : Fintype.card J ≤ π.Gsb.order) (val : ℂ)
    (hval : val = ∑ i, sgn i * ∑' X : CentredSlot π.Gsb → (Fin P.d → ℤ),
      ∑' ξ : ∀ t, (famX (fam₀ i) (famC i) X).Λ t, (((∏ t, (famX (fam₀ i) (famC i) X).w t (ξ t) : ℝ)) : ℂ) *
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0) *
            chiX P.L base X z) hS
          (fixMeasure π.fix)
          (fun t => (famX (fam₀ i) (famC i) X).a t (ξ t)) (fun t => (famX (fam₀ i) (famC i) X).m t (ξ t))
          route hclk hmom (HkM i)) :
    RepresentsIntMKSel π sel n cP tt base roots s val := by
  have h := repIntCMKS_of_centreModes hd1 hL1 hη0 π hS tt base roots selSk hgsp Dom hsliceD hfilt hind route
    hroute hclk hmom src src_dart src_root sel hselclk sgn fam₀ famC μs HkM hc hc1 θs hcθ hμ x K Ch hx hK hCh hC sz
    g lf hlf hμb M0 cl2 gj nj lfj hlfj hM hhinge n s hs hexp hg hb hh hJ
  rw [hval]
  refine h.toRepresentsIntMKSel n cP s (repCoreMK_le_repBoundSel P π sel.card n cP s hL1 hcP
    (repCoreMK_nonneg π n hL1 (C₁_nonneg_of_hC hd1 hK hCh hC)) ?_)
  exact le_trans (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (mul_nonneg
    (Finset.prod_nonneg fun t _ => mul_nonneg (selF_nonneg route sel t) (hlf i t))
    (Finset.prod_nonneg fun j _ => hlfj i j))) hs

open scoped Classical in
/-- **`repMK` companion** (δ's `repMK_of_rep`): from the same data, plain `RepresentsIntMK` at `cP + 343` and mass
`bN`, when `s ≤ bN` and `L^{7(47d+2)·#sel} ≤ L^{343·d·nProt}`. -/
theorem repMK_of_centreModes {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
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
    (fam₀ : I → SlotFam π.Gsb P.d) (famC : I → CentredSlot π.Gsb → (Fin P.d → ℤ) → ChainPiece P.d)
    (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (θs : ReplacementSlot π.Gsb → ℝ) (hcθ : ∀ s, 2 * c + (selE route sel s 0 + selE route sel s 1) ≤ θs s)
    (hμ : ∀ i (X : CentredSlot π.Gsb → (Fin P.d → ℤ)) s, ∑' l, maxBracketPow (θs s)
      (half ((famX (fam₀ i) (famC i) X).m s l)) * ENNReal.ofReal ((famX (fam₀ i) (famC i) X).w s l) ≤ μs i s)
    (x K Ch : ℝ) (hx : x = P.C₁ * Real.sqrt P.δ) (hK : 1 ≤ K) (hCh : 1 ≤ Ch)
    (hC : Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch ≤ P.C₁)
    (sz g : ReplacementSlot π.Gsb → ℕ) (lf : I → ReplacementSlot π.Gsb → ℝ) (hlf : ∀ i s, 0 ≤ lf i s)
    (hμb : ∀ i s, μs i s ≤ ENNReal.ofReal (K * x ^ (sz s) * P.L ^ (-(P.η ^ 8) * (g s : ℝ)) * lf i s))
    (M0 : I → J → ℝ) (cl2 gj nj : J → ℕ) (lfj : I → J → ℝ) (hlfj : ∀ i j, 0 ≤ lfj i j)
    (hM : ∀ i j, 0 ≤ M0 i j ∧ M0 i j ≤ x ^ (cl2 j) *
      P.L ^ (-(P.η ^ 8) * (gj j : ℝ) - P.η ^ 2 / 2 * (nj j : ℝ) + P.η ^ 7) * lfj i j)
    (hhinge : ∀ i (X : CentredSlot π.Gsb → (Fin P.d → ℤ)) (ξ : ∀ s, (famX (fam₀ i) (famC i) X).Λ s),
      ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom
        (fun j => HkM i j (modLam (fun s => (famX (fam₀ i) (famC i) X).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ (∏ j, (Ch * M0 i j)) *
        ∏ j, (1 + |((modLam (fun s => (famX (fam₀ i) (famC i) X).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (n : ℕ) (s : ℝ)
    (hs : ∑ i, ‖sgn i‖ * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j) ≤
      P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s)
    (hexp : (∑ t, sz t) + ∑ j, cl2 j = n - π.Gsb.order)
    (hg : π.gsk ≤ (∑ t, g t) + ∑ j, gj j) (hb : π.bsk ≤ ∑ j, nj j) (hh : Fintype.card J ≤ π.Cs.hinges.card)
    (hJ : Fintype.card J ≤ π.Gsb.order) (val : ℂ)
    (hval : val = ∑ i, sgn i * ∑' X : CentredSlot π.Gsb → (Fin P.d → ℤ),
      ∑' ξ : ∀ t, (famX (fam₀ i) (famC i) X).Λ t, (((∏ t, (famX (fam₀ i) (famC i) X).w t (ξ t) : ℝ)) : ℂ) *
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0) *
            chiX P.L base X z) hS
          (fixMeasure π.fix)
          (fun t => (famX (fam₀ i) (famC i) X).a t (ξ t)) (fun t => (famX (fam₀ i) (famC i) X).m t (ξ t))
          route hclk hmom (HkM i))
    (bN : ℝ) (hsb : s ≤ bN)
    (hLsel : P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) ≤ P.L ^ ((343 : ℝ) * P.d * (π.nProt : ℝ))) :
    π.RepresentsIntMK n (cP + 343) tt base roots bN val := by
  have h := repIntCMKS_of_centreModes hd1 hL1 hη0 π hS tt base roots selSk hgsp Dom hsliceD hfilt hind route
    hroute hclk hmom src src_dart src_root sel hselclk sgn fam₀ famC μs HkM hc hc1 θs hcθ hμ x K Ch hx hK hCh hC sz
    g lf hlf hμb M0 cl2 gj nj lfj hlfj hM hhinge n s hs hexp hg hb hh hJ
  rw [hval]
  refine h.toRepIntCMK.toRepresentsIntMK n (cP + 343) bN ?_
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hT0 := repCoreMK_nonneg π n hL1 (C₁_nonneg_of_hC hd1 hK hCh hC)
  have hLs : 0 < P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hs0 : 0 ≤ s := by
    have h0 : 0 ≤ P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s :=
      le_trans (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (mul_nonneg
        (Finset.prod_nonneg fun t _ => mul_nonneg (selF_nonneg route sel t) (hlf i t))
        (Finset.prod_nonneg fun j _ => hlfj i j))) hs
    exact nonneg_of_mul_nonneg_right (by linarith) hLs
  have hLc : 1 ≤ P.L ^ (cP * P.d * (π.nProt : ℝ)) := Real.one_le_rpow hL1 (by positivity)
  have hsplit : P.L ^ ((cP + 343) * P.d * (π.nProt : ℝ)) =
      P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ ((343 : ℝ) * P.d * (π.nProt : ℝ)) := by
    rw [← Real.rpow_add hL0]; ring_nf
  have h343 : 0 ≤ P.L ^ ((343 : ℝ) * P.d * (π.nProt : ℝ)) := Real.rpow_nonneg hL0.le _
  calc repCoreMK P π n * (P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s)
      ≤ repCoreMK P π n * (P.L ^ ((343 : ℝ) * P.d * (π.nProt : ℝ)) * bN) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hLsel hsb hs0 h343) hT0
    _ ≤ repCoreMK P π n * (P.L ^ (cP * P.d * (π.nProt : ℝ)) *
          (P.L ^ ((343 : ℝ) * P.d * (π.nProt : ℝ)) * bN)) := by
        refine mul_le_mul_of_nonneg_left ?_ hT0
        exact le_mul_of_one_le_left (mul_nonneg h343 (hs0.trans hsb)) hLc
    _ = repBoundMK P π n (cP + 343) bN := by
        simp only [repCoreMK, repBoundMK, hsplit]; ring

end WaveTurbulence.Flower.MkSlotsE
