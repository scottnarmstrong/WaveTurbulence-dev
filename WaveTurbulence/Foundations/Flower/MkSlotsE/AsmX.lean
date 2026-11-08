/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsE.NodeX

/-! # B3s-HELPER9 (MkSlotsE) 2: the assembled expansion restricted to an outer centre

Copies of main's pointwise identities (`Represents.hasSum_node_slots` RepNode2, `hasSum_assembled` RepAsm3,
`hasSum_assembledH` RepH7) with the assembled node-centre assignments `x` restricted to those with `x|centred = X`
(indicator `ResX X x`). The restricted sum of the assembled terms is the product of the slot kernels times
`chiX X = ∏_{c centred} χ_{X c}(k_c)` (instead of times `1`):

* `hasSum_node_slotsX` (RepNode2 with the restriction; the fibre sum over `x` is `hasSum_chiResC`);
* `slotTerm_eq_term` (the pointwise identity inside main's `hasSum_assembled`, RepAsm3);
* `hasSum_assembledX`, `hasSum_assembledHX` (RepAsm3, RepH7 with the restriction). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkSlotsI (CentredSlot chiX)
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsE

variable {w d : ℕ} {S : Garden w}

open scoped Classical in
/-- **Main's `hasSum_node_slots` restricted to the outer centre `X`** (RepNode2, copied and adapted). -/
theorem hasSum_node_slotsX (fam : SlotFam S d) (hS : S.IsPlain)
    (Fn : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (ts : ReplacementSlot S → Fin 2 → ℝ)
    (k : ReplacementSlot S → Mom d)
    (hFn : ∀ s, HasSum (fun l => (fam.w s l : ℂ) * fam.a s l (k s) * fsPhase (fam.m s l) (ts s))
      (Fn s (ts s) (k s)))
    (δ : GNode S.tree → Mom d)
    (hδ : ∀ b : GBranch S.tree, δ b.toNode = δ (b.child 0) - δ (b.child 1) + δ (b.child 2))
    (hleaf : ∀ ℓ : GLeaf S.tree, δ ℓ.toNode = k (Sum.inl (pairOfLeaf S hS ℓ)))
    (hbr : ∀ b : GBranch S.tree, δ b.toNode = k (Sum.inr b)) (X : CentredSlot S → (Fin d → ℤ)) :
    HasSum (fun p : (∀ s, fam.Λ s) × (GBranch S.tree → Fin d → ℤ) =>
        (if ResX X p.2 then (1 : ℂ) else 0) * fam.term hS k ts p)
      ((∏ c : CentredSlot S, chiC d (X c) (k (Sum.inr c.1))) * ∏ s, Fn s (ts s) (k s)) := by
  set u : ∀ s, fam.Λ s → ℂ := fun s l =>
    (fam.w s l : ℂ) * fam.a s l (k s) * fsPhase (fam.m s l) (ts s) with hu
  have hunorm : ∀ s, Summable fun l => ‖u s l‖ := by
    intro s
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_) (fam.w_sum s)
    simp only [hu, norm_mul, fsPhase_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (fam.w_nn s l)]
    exact mul_le_of_le_one_right (fam.w_nn s l) (fam.a_one s l _)
  obtain ⟨hgs, hgsum⟩ := hasSum_prod_fintype u hunorm
  have htsum : ∏ s, ∑' l, u s l = ∏ s, Fn s (ts s) (k s) :=
    Finset.prod_congr rfl fun s _ => (hFn s).tsum_eq
  rw [htsum] at hgsum
  set g : (∀ s, fam.Λ s) → ℂ := fun ξ => ∏ s, u s (ξ s) with hg
  -- the node partition of unity
  have hchi := hasSum_node_chi (tree := S.tree) (d := d) δ
  set c : (GBranch S.tree → Fin d → ℤ) → ℝ := fun x => ∏ b, chi d (x b) (k (Sum.inr b)) with hc
  have hchi' : HasSum c 1 := by
    have : ∀ x, ∏ b, chi d (x b) (δ b.toNode) = c x := fun x =>
      Finset.prod_congr rfl fun b _ => by rw [hbr b]
    simpa only [this] using hchi
  have hc0 : ∀ x, 0 ≤ c x := fun x => Finset.prod_nonneg fun b _ => chi_nonneg d _ _
  have hcC : ∀ x, ∏ b, chiC d (x b) (k (Sum.inr b)) = (c x : ℂ) := by
    intro x; simp [chiC, c, Complex.ofReal_prod]
  -- the restricted node partition
  set cX : ℂ := ∏ c' : CentredSlot S, chiC d (X c') (k (Sum.inr c'.1)) with hcX
  have hchiX : HasSum (fun x => (if ResX X x then (1 : ℂ) else 0) * (c x : ℂ)) cX :=
    hasSum_chiResC X (fun b => k (Sum.inr b))
  have hgfac : ∀ ξ : ∀ s, fam.Λ s, g ξ = (∏ s, ((fam.w s (ξ s) : ℝ) : ℂ)) * (∏ s, fam.a s (ξ s) (k s)) *
      ∏ s, fsPhase (fam.m s (ξ s)) (ts s) := by
    intro ξ
    simp only [hg, hu, Finset.prod_mul_distrib]
  have hterm_eq : ∀ p : (∀ s, fam.Λ s) × (GBranch S.tree → Fin d → ℤ), fam.term hS k ts p =
      g p.1 * ((if p.2 ∈ nodeCentreSet (fam.leafCentre hS p.1) then (1 : ℂ) else 0) *
        ∏ b : GBranch S.tree, chiC d (p.2 b) (k (Sum.inr b))) := by
    intro p
    unfold SlotFam.term
    rw [hgfac]
    ring
  -- for g ξ ≠ 0 the indicator is automatic
  have hind : ∀ ξ : ∀ s, fam.Λ s, g ξ ≠ 0 → ∀ x : GBranch S.tree → Fin d → ℤ,
      (if x ∈ nodeCentreSet (fam.leafCentre hS ξ) then (1 : ℂ) else 0) *
        ∏ b : GBranch S.tree, chiC d (x b) (k (Sum.inr b)) = (c x : ℂ) := by
    intro ξ hξ x
    have hprod : ∏ s, fam.a s (ξ s) (k s) ≠ 0 := by
      rw [hgfac] at hξ
      intro h0; apply hξ; rw [h0]; ring
    have hne : ∀ s, fam.a s (ξ s) (k s) ≠ 0 := fun s => (Finset.prod_ne_zero_iff.1 hprod) s (Finset.mem_univ _)
    have hleaf' : ∀ ℓ : GLeaf S.tree, ‖δ ℓ.toNode - latPt d (fam.leafCentre hS ξ ℓ)‖ ≤ 1 := by
      intro ℓ
      rw [hleaf ℓ]
      exact fam.a_supp _ _ _ (hne _)
    rw [hcC]
    by_cases hx : x ∈ nodeCentreSet (fam.leafCentre hS ξ)
    · simp [hx]
    · have : c x = 0 := by
        by_contra hcx
        apply hx
        have h1 : ∏ b, chi d (x b) (δ b.toNode) ≠ 0 := by
          have : ∏ b, chi d (x b) (δ b.toNode) = c x := Finset.prod_congr rfl fun b _ => by rw [hbr b]
          rw [this]; exact hcx
        exact nodeCentreAdm_of_prod_ne_zero δ hδ hleaf' h1
      simp [hx, this]
  have hfib : ∀ ξ : ∀ s, fam.Λ s,
      HasSum (fun x => (if ResX X x then (1 : ℂ) else 0) * fam.term hS k ts (ξ, x)) (g ξ * cX) := by
    intro ξ
    by_cases hξ : g ξ = 0
    · have : ∀ x, (if ResX X x then (1 : ℂ) else 0) * fam.term hS k ts (ξ, x) = 0 := fun x => by
        rw [hterm_eq]; simp [hξ]
      simp only [this, hξ, zero_mul]
      exact hasSum_zero
    · have : ∀ x, (if ResX X x then (1 : ℂ) else 0) * fam.term hS k ts (ξ, x) =
          g ξ * ((if ResX X x then (1 : ℂ) else 0) * (c x : ℂ)) := fun x => by
        rw [hterm_eq]; simp only; rw [hind ξ hξ x]; ring
      simp only [this]
      exact hchiX.mul_left (g ξ)
  have hbound : ∀ p : (∀ s, fam.Λ s) × (GBranch S.tree → Fin d → ℤ),
      ‖(if ResX X p.2 then (1 : ℂ) else 0) * fam.term hS k ts p‖ ≤ ‖g p.1‖ * c p.2 := by
    intro p
    have h1 : ‖fam.term hS k ts p‖ ≤ ‖g p.1‖ * c p.2 := by
      rw [hterm_eq, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      by_cases hx : p.2 ∈ nodeCentreSet (fam.leafCentre hS p.1)
      · simp only [hx, ite_true, one_mul]
        rw [hcC, Complex.norm_real, Real.norm_of_nonneg (hc0 _)]
      · simp [hx, hc0]
    have h2 : ‖(if ResX X p.2 then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
    calc ‖(if ResX X p.2 then (1 : ℂ) else 0) * fam.term hS k ts p‖
        = ‖(if ResX X p.2 then (1 : ℂ) else 0)‖ * ‖fam.term hS k ts p‖ := norm_mul _ _
      _ ≤ 1 * ‖fam.term hS k ts p‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h1
  have hterm : Summable (fun p : (∀ s, fam.Λ s) × (GBranch S.tree → Fin d → ℤ) =>
      (if ResX X p.2 then (1 : ℂ) else 0) * fam.term hS k ts p) := by
    refine Summable.of_norm_bounded (g := fun p => ‖g p.1‖ * c p.2) ?_ hbound
    exact Summable.mul_of_nonneg (f := fun ξ => ‖g ξ‖) (g := c) hgs hchi'.summable
      (fun _ => norm_nonneg _) hc0
  have htot : ∑' p : (∀ s, fam.Λ s) × (GBranch S.tree → Fin d → ℤ),
      (if ResX X p.2 then (1 : ℂ) else 0) * fam.term hS k ts p = cX * ∏ s, Fn s (ts s) (k s) := by
    rw [Summable.tsum_prod' hterm (fun ξ => (hfib ξ).summable)]
    rw [tsum_congr fun ξ => (hfib ξ).tsum_eq, tsum_mul_right, hgsum.tsum_eq]
    ring
  rw [← htot]
  exact hterm.hasSum

open scoped Classical in
/-- The pointwise identity inside main's `hasSum_assembled` (RepAsm3, copied): the joint term of an assembled mode is
its slot part `constW · E · timeFac`. -/
theorem slotTerm_eq_term (fam : SlotFam S d) (hS : S.IsPlain) (Cχ : ℝ) (hCχ : Cχ ≠ 0) (L : ℝ)
    (base : Mom d) (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ) (κ : GenDecoration S d roots 0)
    (τ : GBranch S.tree → ℝ) (ξ : XiT fam) :
    slotTerm fam hS Cχ L base roots tt ξ κ.1 τ =
      fam.term hS (fun s => base + latticePoint L (κ.1 (slotNode hS s))) (slotTs hS tt τ) ξ := by
  have hdec := κ.2.1
  have hz : ∀ ℓ : GLeaf S.tree, κ.1 ℓ.toNode = κ.1 (S.pair ℓ).toNode := hdec.2
  have hroot : ∀ j, κ.1 (GNode.root S.tree j) = roots j := κ.2.2.1
  set kk : ReplacementSlot S → Mom d := fun s => base + latticePoint L (κ.1 (slotNode hS s)) with hkk
  unfold slotTerm
  have hE : ∏ x ∈ S.molecule.bonds, edgeS fam hS Cχ ξ x (base + latticePoint L (bondIndex S κ.1 x)) =
      ∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (hasBond hS), ampS fam Cχ ξ s (kk s) := by
    rw [← prod_bonds_eq hS (fun s => ampS fam Cχ ξ s (kk s))]
    refine Finset.prod_congr rfl fun x _ => ?_
    unfold edgeS
    simp only [hkk]
    rw [bondIndex_eq_slotNode hS κ.1 hz x]
  have hN : ∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
        ampS fam Cχ ξ s (base + latticePoint L (kconstInt hS roots s)) =
      ∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
        ampS fam Cχ ξ s (kk s) := by
    refine Finset.prod_congr rfl fun s hs => ?_
    have hs' : ¬ hasBond hS s := by simpa using hs
    simp only [hkk]
    rw [kconstInt_spec hS roots s hs' κ.1 hz hroot]
  have hAll : (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (hasBond hS), ampS fam Cχ ξ s (kk s)) *
      (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
        ampS fam Cχ ξ s (kk s)) = ∏ s, ampS fam Cχ ξ s (kk s) :=
    Finset.prod_filter_mul_prod_filter_not _ _ _
  have hsplit : ∏ s, ampS fam Cχ ξ s (kk s) =
      (∏ s, fam.a s (ξ.1 s) (kk s)) *
        ((∏ b : GBranch S.tree, chiC d (ξ.2 b) (kk (Sum.inr b))) / (Cχ : ℂ) ^ (Fintype.card (GBranch S.tree))) := by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type (fun s => fam.a s (ξ.1 s) (kk s))]
    simp only [ampS, Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_univ]
    ring
  have hph := prod_fsPhase_slotTs fam hS tt τ ξ
  have hCne : (Cχ : ℂ) ^ (Fintype.card (GBranch S.tree)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hCχ)
  unfold SlotFam.term constW
  rw [hN, hE]
  have hfull : (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (hasBond hS), ampS fam Cχ ξ s (kk s)) *
      (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
        ampS fam Cχ ξ s (kk s)) =
      (∏ s, fam.a s (ξ.1 s) (kk s)) *
        ((∏ b : GBranch S.tree, chiC d (ξ.2 b) (kk (Sum.inr b))) / (Cχ : ℂ) ^ (Fintype.card (GBranch S.tree))) :=
    hAll.trans hsplit
  rw [hph]
  have hfull' : (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (hasBond hS), ampS fam Cχ ξ s (kk s)) *
      (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
        ampS fam Cχ ξ s (kk s)) * (Cχ : ℂ) ^ (Fintype.card (GBranch S.tree)) =
      (∏ s, fam.a s (ξ.1 s) (kk s)) * ∏ b : GBranch S.tree, chiC d (ξ.2 b) (kk (Sum.inr b)) := by
    rw [hfull]; field_simp
  linear_combination ((∏ s, ((fam.w s (ξ.1 s) : ℝ) : ℂ)) *
    (if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then (1 : ℂ) else 0) *
    (∏ j : Fin w, Complex.exp (((Real.pi * modeFreq fam hS ξ (Sum.inl j) * tt j : ℝ) : ℂ) * Complex.I)) *
    timeFac fam hS ξ τ) * hfull'

open scoped Classical in
/-- **Main's `hasSum_assembled` restricted to the outer centre `X`**: the assembled slot parts with node centres
restricting to `X` sum to `chiX X · ∏_s Fn_s`. -/
theorem hasSum_assembledX (fam : SlotFam S d) (hS : S.IsPlain) (Cχ : ℝ) (hCχ : Cχ ≠ 0) (L : ℝ)
    (base : Mom d) (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ)
    (Fn : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (κ : GenDecoration S d roots 0)
    (τ : GBranch S.tree → ℝ)
    (hFn : ∀ s, HasSum (fun l => (fam.w s l : ℂ) * fam.a s l (base + latticePoint L (κ.1 (slotNode hS s))) *
      fsPhase (fam.m s l) (slotTs hS tt τ s))
      (Fn s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))))
    (X : CentredSlot S → (Fin d → ℤ)) :
    HasSum (fun ξ : XiT fam => (if ResX X ξ.2 then (1 : ℂ) else 0) *
        slotTerm fam hS Cχ L base roots tt ξ κ.1 τ)
      (chiX L base X κ * ∏ s, Fn s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) := by
  have hdec := κ.2.1
  have hz : ∀ ℓ : GLeaf S.tree, κ.1 ℓ.toNode = κ.1 (S.pair ℓ).toNode := hdec.2
  set kk : ReplacementSlot S → Mom d := fun s => base + latticePoint L (κ.1 (slotNode hS s)) with hkk
  have key := hasSum_node_slotsX fam hS Fn (slotTs hS tt τ) kk hFn
    (cosetDecoration S L base κ.1)
    (fun b => by
      simp only [cosetDecoration]
      rw [hdec.1 b, latticePoint_sub_add]
      abel)
    (fun ℓ => by
      simp only [cosetDecoration, hkk, slotNode]
      rw [dec_leaf_eq_first hS κ.1 hz ℓ])
    (fun b => rfl) X
  refine key.congr_fun (fun ξ => ?_)
  rw [slotTerm_eq_term fam hS Cχ hCχ L base roots tt κ τ ξ]

open scoped Classical in
/-- The restricted assembled terms with hinge modes are absolutely summable (main's `summable_hingeWeight`). -/
theorem summable_indH (fam : SlotFam S d) (hS : S.IsPlain) (hd : 1 ≤ d) (Cχ : ℝ)
    (hC : ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H → ∀ n : Fin d → ℤ,
      SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal Cχ * SNorm (30 * d) 0 H)
    (hCpos : 0 < Cχ) (L : ℝ) (base : Mom d) (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ)
    {J : Type} [Fintype J] (H : HingeFam J d) (hmom : J → Fin 4 → GNode S.tree) (hclk : J → Fin 3 → ClkSrc S)
    (Mh : J → ℝ) (hMh : ∀ j c, ∑' l, H.w j c l ≤ Mh j) (κ : GNode S.tree → Fin d → ℤ) (τ : GBranch S.tree → ℝ)
    (X : CentredSlot S → (Fin d → ℤ)) :
    Summable fun ξh : XiH fam hS H hmom =>
      ‖(if ResX X ξh.1.2 then (1 : ℂ) else 0) *
        (slotTerm fam hS Cχ L base roots tt ξh.1 κ τ * hingeTerm fam hS H hmom hclk L base tt ξh κ τ)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξh => ?_)
    (summable_hingeWeight fam hS hd Cχ hC hCpos L base roots tt H hmom Mh hMh κ τ)
  have h2 : ‖(if ResX X ξh.1.2 then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
  have h3 := norm_hingeTerm_le fam hS H hmom hclk L base tt ξh κ τ
  rw [norm_mul, norm_mul]
  calc ‖(if ResX X ξh.1.2 then (1 : ℂ) else 0)‖ *
        (‖slotTerm fam hS Cχ L base roots tt ξh.1 κ τ‖ * ‖hingeTerm fam hS H hmom hclk L base tt ξh κ τ‖)
      ≤ 1 * (‖slotTerm fam hS Cχ L base roots tt ξh.1 κ τ‖ * ∏ j, H.w j _ (ξh.2 j)) := by
        gcongr
    _ = _ := one_mul _

open scoped Classical in
/-- **Main's `hasSum_assembledH` restricted to the outer centre `X`** (RepH7, copied and adapted). -/
theorem hasSum_assembledHX (fam : SlotFam S d) (hS : S.IsPlain) (hd : 1 ≤ d) (Cχ : ℝ)
    (hC : ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H → ∀ n : Fin d → ℤ,
      SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal Cχ * SNorm (30 * d) 0 H)
    (hCpos : 0 < Cχ) (L : ℝ) (base : Mom d) (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ)
    (Fn : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (κ : GenDecoration S d roots 0)
    (τ : GBranch S.tree → ℝ)
    (hFn : ∀ s, HasSum (fun l => (fam.w s l : ℂ) * fam.a s l (base + latticePoint L (κ.1 (slotNode hS s))) *
      fsPhase (fam.m s l) (slotTs hS tt τ s))
      (Fn s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))))
    {J : Type} [Fintype J] (H : HingeFam J d) (hmom : J → Fin 4 → GNode S.tree) (hclk : J → Fin 3 → ClkSrc S)
    (Hk : J → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) (Mh : J → ℝ)
    (hMh : ∀ j c, ∑' l, H.w j c l ≤ Mh j)
    (hHk : ∀ j c, (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c i)‖ ≤ 1) →
      HasSum (fun l => (H.w j c l : ℂ) * H.a j c l (fun i => base + latticePoint L (κ.1 (hmom j i))) *
        fsPhase (H.m j c l) (fun i => clockOf S tt τ (hclk j i)))
        (Hk j (fun i => clockOf S tt τ (hclk j i)) (fun i => base + latticePoint L (κ.1 (hmom j i)))))
    (X : CentredSlot S → (Fin d → ℤ)) :
    HasSum (fun ξh : XiH fam hS H hmom => (if ResX X ξh.1.2 then (1 : ℂ) else 0) *
        (slotTerm fam hS Cχ L base roots tt ξh.1 κ.1 τ * hingeTerm fam hS H hmom hclk L base tt ξh κ.1 τ))
      (chiX L base X κ * ((∏ s, Fn s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) *
        ∏ j, Hk j (fun i => clockOf S tt τ (hclk j i)) (fun i => base + latticePoint L (κ.1 (hmom j i))))) := by
  set PH : ℂ := ∏ j, Hk j (fun i => clockOf S tt τ (hclk j i)) (fun i => base + latticePoint L (κ.1 (hmom j i)))
    with hPH
  set F : XiH fam hS H hmom → ℂ := fun ξh => (if ResX X ξh.1.2 then (1 : ℂ) else 0) *
    (slotTerm fam hS Cχ L base roots tt ξh.1 κ.1 τ * hingeTerm fam hS H hmom hclk L base tt ξh κ.1 τ) with hF
  set G : XiT fam → ℂ := fun ξ => (if ResX X ξ.2 then (1 : ℂ) else 0) *
    (slotTerm fam hS Cχ L base roots tt ξ κ.1 τ * PH) with hG
  have hs := hasSum_assembledX fam hS Cχ hCpos.ne' L base roots tt Fn κ τ hFn X
  obtain ⟨T, hT⟩ := (summable_indH fam hS hd Cχ hC hCpos L base roots tt H hmom hclk Mh hMh κ.1 τ X).of_norm
  have hin : ∀ ξ : XiT fam, HasSum (fun ζ : (∀ j, H.Λ j (hingeCen fam hS hmom ξ j)) => F ⟨ξ, ζ⟩) (G ξ) := by
    intro ξ
    have h0 := (hasSum_hinge_inner fam hS Cχ L base roots tt κ τ H hmom hclk Hk hHk ξ).mul_left
      (if ResX X ξ.2 then (1 : ℂ) else 0)
    exact h0
  have h1 : HasSum G T := hT.sigma hin
  have h3 : HasSum G (chiX L base X κ *
      ((∏ s, Fn s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) * PH)) := by
    have h2 := hs.mul_right PH
    rw [mul_assoc] at h2
    refine h2.congr_fun fun ξ => ?_
    simp only [hG]
    ring
  rwa [← h3.unique h1] at hT

end WaveTurbulence.Flower.MkSlotsE
