/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCChainF

/-!
# The expansion of the chain integral over the subcouple masks

DH21 (newexp4) (L1114): inserting the expansions (maincoef3)
`F_j = Σ_{Z_j ⊆ S_j} ∏_{z ∈ Z_j} Φ_z · G_{j,Z_j}` of the pair coefficients into the chain integral
gives a sum over `Z ⊆ ⋃_j S_j`. The chain integral is multilinear in the coefficients and linear in
the continuation (`chainT_finsum`, `chainT_expand`), for continuous data.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Linear

variable {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ}

theorem intervalIntegral_finsum_cont {κ : Type*} (K : Finset κ) (f : κ → ℝ → ℂ)
    (hf : ∀ k, Continuous (f k)) (a b : ℝ) :
    ∫ x in a..b, ∑ k ∈ K, f k x = ∑ k ∈ K, ∫ x in a..b, f k x :=
  intervalIntegral.integral_finsetSum fun k _ => (hf k).intervalIntegrable a b

/-- **The chain integral is linear in the continuation.** -/
theorem chainT_finsum : ∀ (c : LegalCode) (q : ℕ) {F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ} (α : V → ℝ)
    (_ : ∀ j, Continuous fun p : ℝ × ℝ => F j α p.1 p.2) {κ : Type} (K : Finset κ)
    (a : κ → ℂ) {h : κ → ℝ → ℂ} (_ : ∀ k, Continuous (h k)) (t : ℝ),
    chainT σ ε c q F α t (fun t' => ∑ k ∈ K, a k * h k t') =
      ∑ k ∈ K, a k * chainT σ ε c q F α t (h k)
  | .nil, _, _, _, _, _, _, _, _, _, _ => rfl
  | .node i r, q, F, α, hF, κ, K, a, h, hh, t => by
    simp_rw [chainT_node]
    -- the rest
    have hR : ∀ tb, chainT σ ε r (q + i.size + 1) F α tb (fun t' => ∑ k ∈ K, a k * h k t') =
        ∑ k ∈ K, a k * chainT σ ε r (q + i.size + 1) F α tb (h k) :=
      fun tb => chainT_finsum r _ α hF K a hh tb
    have hRc : ∀ k, Continuous fun tb => chainT σ ε r (q + i.size + 1) F α tb (h k) := fun k =>
      (continuous_chainT (σ := σ) (ε := ε) r _ (X := Unit) (F := fun _ => F) α
        (fun j => (hF j).comp continuous_snd) (E := fun _ => h k) ((hh k).comp continuous_snd)).comp
        (continuous_const.prodMk continuous_id : Continuous fun tb : ℝ => ((), tb))
    have he₂ : Continuous fun tb : ℝ => cexp (π * I * (-(ε q * α (σ q)) * tb)) := by fun_prop
    -- the continuation of the inner block for each `k`, a function of `(ta, t')`
    set H : κ → ℝ → ℝ → ℂ := fun k ta t' => ∫ tb in (0 : ℝ)..t',
      cexp (π * I * (-(ε q * α (σ q)) * tb)) * F q α ta tb *
        chainT σ ε r (q + i.size + 1) F α tb (h k) with hH
    have hHc : ∀ k, Continuous fun p : ℝ × ℝ => H k p.1 p.2 := fun k =>
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : ℝ × ℝ) (tb : ℝ) => cexp (π * I * (-(ε q * α (σ q)) * tb)) *
          F q α p.1 tb * chainT σ ε r (q + i.size + 1) F α tb (h k))
        (((he₂.comp continuous_snd).mul ((hF q).comp
          ((continuous_fst.comp continuous_fst).prodMk continuous_snd))).mul
          ((hRc k).comp continuous_snd)) (continuous_snd)
    have hcont : ∀ ta, (fun t' => ∫ tb in (0 : ℝ)..t', cexp (π * I * (-(ε q * α (σ q)) * tb)) *
        F q α ta tb * chainT σ ε r (q + i.size + 1) F α tb (fun t' => ∑ k ∈ K, a k * h k t')) =
        fun t' => ∑ k ∈ K, a k * H k ta t' := fun ta => by
      funext t'
      simp_rw [hR, Finset.mul_sum]
      rw [intervalIntegral_finsum_cont _ _ (fun k => ?_)]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun tb _ => ?_
        ring
      · have hFq : Continuous fun tb => F q α ta tb :=
          (hF q).comp (continuous_const.prodMk continuous_id)
        exact (he₂.mul hFq).mul (continuous_const.mul (hRc k))
    simp_rw [hcont]
    have hI : ∀ ta, chainT σ ε i (q + 1) F α ta (fun t' => ∑ k ∈ K, a k * H k ta t') =
        ∑ k ∈ K, a k * chainT σ ε i (q + 1) F α ta (H k ta) := fun ta =>
      chainT_finsum i _ α hF K a (fun k => (hHc k).comp (continuous_const.prodMk continuous_id)) ta
    simp_rw [hI, Finset.mul_sum]
    have hIc : ∀ k, Continuous fun ta => chainT σ ε i (q + 1) F α ta (H k ta) := fun k =>
      (continuous_chainT (σ := σ) (ε := ε) i _ (X := ℝ) (F := fun _ => F) α
        (fun j => (hF j).comp continuous_snd) (E := H k) (hHc k)).comp
        (continuous_id.prodMk continuous_id)
    rw [intervalIntegral_finsum_cont _ _ (fun k => by
      exact (by fun_prop : Continuous fun ta : ℝ => cexp (π * I * (ε q * α (σ q) * ta))).mul
        (continuous_const.mul (hIc k)))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun ta _ => ?_
    simp only [hH]
    ring

end Linear

section Expand

variable {V : Type} [DecidableEq V] {σ : ℕ → V} {ε : ℕ → ℤ}

/-- The union of the variable sets of the pairs `[q, q + m)`. -/
@[expose] def unionS (S : ℕ → Finset V) (q m : ℕ) : Finset V :=
  (Finset.Ico q (q + m)).biUnion S

theorem unionS_node (S : ℕ → Finset V) (i r : LegalCode) (q : ℕ) :
    unionS S q (LegalCode.node i r).size =
      S q ∪ unionS S (q + 1) i.size ∪ unionS S (q + i.size + 1) r.size := by
  ext x
  simp only [unionS, Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_union, LegalCode.size]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, hx⟩
    by_cases hq : j = q
    · subst hq; exact Or.inl (Or.inl hx)
    · by_cases hj : j < q + 1 + i.size
      · exact Or.inl (Or.inr ⟨j, ⟨by omega, hj⟩, hx⟩)
      · exact Or.inr ⟨j, ⟨by omega, by omega⟩, hx⟩
  · rintro ((hx | ⟨j, ⟨h1, h2⟩, hx⟩) | ⟨j, ⟨h1, h2⟩, hx⟩)
    · exact ⟨q, ⟨le_rfl, by omega⟩, hx⟩
    · exact ⟨j, ⟨by omega, by omega⟩, hx⟩
    · exact ⟨j, ⟨by omega, by omega⟩, hx⟩

theorem subset_unionS {S : ℕ → Finset V} {q m j : ℕ} (hj : j ∈ Set.Ico q (q + m)) :
    S j ⊆ unionS S q m := fun x hx => by
  simp only [unionS, Finset.mem_biUnion, Finset.mem_Ico]
  exact ⟨j, hj, hx⟩

theorem disjoint_unionS {S : ℕ → Finset V} {q m : ℕ}
    (hS : ∀ j ∈ Set.Ico q (q + m), ∀ k ∈ Set.Ico q (q + m), j ≠ k → Disjoint (S j) (S k))
    {j : ℕ} (hj : j ∈ Set.Ico q (q + m)) {q' m' : ℕ}
    (hsub : Set.Ico q' (q' + m') ⊆ Set.Ico q (q + m)) (hjn : j ∉ Set.Ico q' (q' + m')) :
    Disjoint (S j) (unionS S q' m') := by
  rw [unionS, Finset.disjoint_biUnion_right]
  intro k hk
  have hk' : k ∈ Set.Ico q' (q' + m') := by simpa [Finset.mem_Ico] using hk
  exact hS j hj k (hsub hk') (fun h => hjn (h ▸ hk'))

theorem inter_union3_left {Zq Zi Zr T : Finset V} (hq : Zq ⊆ T) (hi : Disjoint Zi T)
    (hr : Disjoint Zr T) : (Zq ∪ Zi ∪ Zr) ∩ T = Zq := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨(h | h) | h, hx⟩
    · exact h
    · exact absurd hx (Finset.disjoint_left.1 hi h)
    · exact absurd hx (Finset.disjoint_left.1 hr h)
  · intro h; exact ⟨Or.inl (Or.inl h), hq h⟩

theorem inter_union3_mid {Zq Zi Zr T : Finset V} (hq : Disjoint Zq T) (hr : Disjoint Zr T) :
    (Zq ∪ Zi ∪ Zr) ∩ T = Zi ∩ T := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨(h | h) | h, hx⟩
    · exact absurd hx (Finset.disjoint_left.1 hq h)
    · exact ⟨h, hx⟩
    · exact absurd hx (Finset.disjoint_left.1 hr h)
  · rintro ⟨h, hx⟩; exact ⟨Or.inl (Or.inr h), hx⟩

theorem inter_union3_right {Zq Zi Zr T : Finset V} (hq : Disjoint Zq T) (hi : Disjoint Zi T) :
    (Zq ∪ Zi ∪ Zr) ∩ T = Zr ∩ T := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨(h | h) | h, hx⟩
    · exact absurd hx (Finset.disjoint_left.1 hq h)
    · exact absurd hx (Finset.disjoint_left.1 hi h)
    · exact ⟨h, hx⟩
  · rintro ⟨h, hx⟩; exact ⟨Or.inr h, hx⟩

/-- **The expansion of the chain integral** over the masks of its pair coefficients (continuous
data, every `t`). -/
theorem chainT_expand (α : V → ℝ) (w : V → ℂ) {S : ℕ → Finset V}
    {R : ℕ → Finset V → (V → ℝ) → ℝ → ℝ → ℂ}
    (hR : ∀ j Z, Continuous fun p : ℝ × ℝ => R j Z α p.1 p.2) :
    ∀ (c : LegalCode) (q : ℕ),
      (∀ j ∈ Set.Ico q (q + c.size), ∀ k ∈ Set.Ico q (q + c.size), j ≠ k →
        Disjoint (S j) (S k)) →
      ∀ {g : ℝ → ℂ}, Continuous g → ∀ t : ℝ,
        chainT σ ε c q (fun j β t s => ∑ Z ∈ (S j).powerset, (∏ z ∈ Z, w z) * R j Z β t s) α t g =
          ∑ Z ∈ (unionS S q c.size).powerset, (∏ z ∈ Z, w z) *
            chainT σ ε c q (fun j => R j (Z ∩ S j)) α t g
  | .nil, q, _, g, _, t => by
    simp [unionS, LegalCode.size, chainT_nil]
  | .node i r, q, hS, g, hg, t => by
    have hsz : (LegalCode.node i r).size = i.size + r.size + 1 := rfl
    have hq : q ∈ Set.Ico q (q + (LegalCode.node i r).size) := by
      simp only [Set.mem_Ico]; omega
    have hsi : Set.Ico (q + 1) (q + 1 + i.size) ⊆ Set.Ico q (q + (LegalCode.node i r).size) :=
      fun j hj => by simp only [Set.mem_Ico] at hj ⊢; omega
    have hsr : Set.Ico (q + i.size + 1) (q + i.size + 1 + r.size) ⊆
        Set.Ico q (q + (LegalCode.node i r).size) :=
      fun j hj => by simp only [Set.mem_Ico] at hj ⊢; omega
    have hSi := fun j hj k hk hjk => hS j (hsi hj) k (hsi hk) hjk
    have hSr := fun j hj k hk hjk => hS j (hsr hj) k (hsr hk) hjk
    -- disjointness of the three blocks
    have hqi : Disjoint (S q) (unionS S (q + 1) i.size) :=
      disjoint_unionS hS hq hsi (by simp only [Set.mem_Ico]; omega)
    have hqr : Disjoint (S q) (unionS S (q + i.size + 1) r.size) :=
      disjoint_unionS hS hq hsr (by simp only [Set.mem_Ico]; omega)
    have hir : Disjoint (unionS S (q + 1) i.size) (unionS S (q + i.size + 1) r.size) := by
      rw [unionS, Finset.disjoint_biUnion_left]
      intro j hj
      have hj' : j ∈ Set.Ico (q + 1) (q + 1 + i.size) := by simpa [Finset.mem_Ico] using hj
      exact disjoint_unionS hS (hsi hj') hsr (by simp only [Set.mem_Ico] at hj' ⊢; omega)
    -- notation
    set Ui := unionS S (q + 1) i.size with hUi
    set Ur := unionS S (q + i.size + 1) r.size with hUr
    have hFc : ∀ j, Continuous fun p : ℝ × ℝ =>
        (fun j β t s => ∑ Z ∈ (S j).powerset, (∏ z ∈ Z, w z) * R j Z β t s) j α p.1 p.2 :=
      fun j => continuous_finsetSum _ fun Z _ => continuous_const.mul (hR j Z)
    have he₁ : Continuous fun ta : ℝ => cexp (π * I * (ε q * α (σ q) * ta)) := by fun_prop
    have he₂ : Continuous fun tb : ℝ => cexp (π * I * (-(ε q * α (σ q)) * tb)) := by fun_prop
    -- the rest of the chain for each mask
    set Tr : Finset V → ℝ → ℂ := fun Zr tb => chainT σ ε r (q + i.size + 1)
      (fun j => R j (Zr ∩ S j)) α tb g with hTr
    have hTrc : ∀ Zr, Continuous (Tr Zr) := fun Zr =>
      (continuous_chainT (σ := σ) (ε := ε) r _ (X := Unit) (F := fun _ j => R j (Zr ∩ S j)) α
        (fun j => (hR j _).comp continuous_snd) (E := fun _ => g) (hg.comp continuous_snd)).comp
        (continuous_const.prodMk continuous_id : Continuous fun tb : ℝ => ((), tb))
    -- the inner continuation for each pair of masks
    set K := (S q).powerset ×ˢ Ur.powerset with hK
    set a : Finset V × Finset V → ℂ := fun k => (∏ z ∈ k.1, w z) * ∏ z ∈ k.2, w z with ha
    set H : Finset V × Finset V → ℝ → ℝ → ℂ := fun k ta t' => ∫ tb in (0 : ℝ)..t',
      cexp (π * I * (-(ε q * α (σ q)) * tb)) * R q k.1 α ta tb * Tr k.2 tb with hH
    have hHc : ∀ k, Continuous fun p : ℝ × ℝ => H k p.1 p.2 := fun k =>
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : ℝ × ℝ) (tb : ℝ) => cexp (π * I * (-(ε q * α (σ q)) * tb)) *
          R q k.1 α p.1 tb * Tr k.2 tb)
        (((he₂.comp continuous_snd).mul ((hR q k.1).comp
          ((continuous_fst.comp continuous_fst).prodMk continuous_snd))).mul
          ((hTrc k.2).comp continuous_snd)) continuous_snd
    -- Step 1: the inner continuation
    have hstep1 : ∀ ta t', ∫ tb in (0 : ℝ)..t', cexp (π * I * (-(ε q * α (σ q)) * tb)) *
        (fun j β t s => ∑ Z ∈ (S j).powerset, (∏ z ∈ Z, w z) * R j Z β t s) q α ta tb *
          chainT σ ε r (q + i.size + 1)
            (fun j β t s => ∑ Z ∈ (S j).powerset, (∏ z ∈ Z, w z) * R j Z β t s) α tb g =
        ∑ k ∈ K, a k * H k ta t' := by
      intro ta t'
      have hpt : ∀ tb : ℝ, cexp (π * I * (-(ε q * α (σ q)) * tb)) *
          (fun j β t s => ∑ Z ∈ (S j).powerset, (∏ z ∈ Z, w z) * R j Z β t s) q α ta tb *
            chainT σ ε r (q + i.size + 1)
              (fun j β t s => ∑ Z ∈ (S j).powerset, (∏ z ∈ Z, w z) * R j Z β t s) α tb g =
          ∑ k ∈ K, a k * (cexp (π * I * (-(ε q * α (σ q)) * tb)) * R q k.1 α ta tb * Tr k.2 tb) := by
        intro tb
        rw [chainT_expand α w hR r (q + i.size + 1) hSr hg tb, hK, Finset.sum_product]
        beta_reduce
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun Zq _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun Zr _ => ?_
        simp only [ha, hTr]
        ring
      simp_rw [hpt]
      have hck : ∀ k : Finset V × Finset V, Continuous fun tb : ℝ => a k *
          (cexp (π * I * (-(ε q * α (σ q)) * tb)) * R q k.1 α ta tb * Tr k.2 tb) := fun k => by
        have h1 : Continuous fun tb => R q k.1 α ta tb :=
          (hR q k.1).comp (continuous_const.prodMk continuous_id)
        exact continuous_const.mul ((he₂.mul h1).mul (hTrc k.2))
      rw [intervalIntegral_finsum_cont K (fun k tb => a k *
        (cexp (π * I * (-(ε q * α (σ q)) * tb)) * R q k.1 α ta tb * Tr k.2 tb)) hck]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_const_mul]
    -- Step 6: the terms
    have hstep6 : ∀ Zq ∈ (S q).powerset, ∀ Zi ∈ Ui.powerset, ∀ Zr ∈ Ur.powerset,
        ∫ ta in (0 : ℝ)..t, cexp (π * I * (ε q * α (σ q) * ta)) *
          chainT σ ε i (q + 1) (fun j => R j (Zi ∩ S j)) α ta (H (Zq, Zr) ta) =
        chainT σ ε (.node i r) q (fun j => R j ((Zq ∪ Zi ∪ Zr) ∩ S j)) α t g := by
      intro Zq hZq Zi hZi Zr hZr
      rw [Finset.mem_powerset] at hZq hZi hZr
      rw [chainT_node]
      refine intervalIntegral.integral_congr fun ta _ => ?_
      congr 1
      rw [chainT_congr_range i (q + 1) (F := fun j => R j ((Zq ∪ Zi ∪ Zr) ∩ S j))
        (F' := fun j => R j (Zi ∩ S j)) α (fun j hj => by
          have hjS : S j ⊆ Ui := subset_unionS hj
          rw [inter_union3_mid (Finset.disjoint_of_subset_left hZq
              (Finset.disjoint_of_subset_right hjS hqi))
            (Finset.disjoint_of_subset_left hZr (Finset.disjoint_of_subset_right hjS hir.symm))])]
      congr 1
      funext t'
      simp only [hH, hTr]
      refine intervalIntegral.integral_congr fun tb _ => ?_
      have hq' : (Zq ∪ Zi ∪ Zr) ∩ S q = Zq :=
        inter_union3_left hZq (Finset.disjoint_of_subset_left hZi hqi.symm)
          (Finset.disjoint_of_subset_left hZr hqr.symm)
      simp only [hq']
      congr 1
      exact chainT_congr_range r (q + i.size + 1) α (fun j hj => by
        have hjS : S j ⊆ Ur := subset_unionS hj
        rw [inter_union3_right (Finset.disjoint_of_subset_left hZq
            (Finset.disjoint_of_subset_right hjS hqr))
          (Finset.disjoint_of_subset_left hZi (Finset.disjoint_of_subset_right hjS hir))]) tb g
    have hIc : ∀ k Zi, Continuous fun ta =>
        chainT σ ε i (q + 1) (fun j => R j (Zi ∩ S j)) α ta (H k ta) := fun k Zi =>
      (continuous_chainT (σ := σ) (ε := ε) i _ (X := ℝ) (F := fun _ j => R j (Zi ∩ S j)) α
        (fun j => (hR j _).comp continuous_snd) (E := H k) (hHc k)).comp
        (continuous_id.prodMk continuous_id)
    calc chainT σ ε (.node i r) q
          (fun j β t s => ∑ Z ∈ (S j).powerset, (∏ z ∈ Z, w z) * R j Z β t s) α t g
        = ∫ ta in (0 : ℝ)..t, cexp (π * I * (ε q * α (σ q) * ta)) *
            ∑ k ∈ K, a k * ∑ Zi ∈ Ui.powerset, (∏ z ∈ Zi, w z) *
              chainT σ ε i (q + 1) (fun j => R j (Zi ∩ S j)) α ta (H k ta) := by
          rw [chainT_node]
          refine intervalIntegral.integral_congr fun ta _ => ?_
          congr 1
          have e : (fun t' => ∫ tb in (0 : ℝ)..t', cexp (π * I * (-(ε q * α (σ q)) * tb)) *
              (fun j β t s => ∑ Z ∈ (S j).powerset, (∏ z ∈ Z, w z) * R j Z β t s) q α ta tb *
                chainT σ ε r (q + i.size + 1)
                  (fun j β t s => ∑ Z ∈ (S j).powerset, (∏ z ∈ Z, w z) * R j Z β t s) α tb g) =
              fun t' => ∑ k ∈ K, a k * H k ta t' := funext fun t' => hstep1 ta t'
          have hHta : ∀ k, Continuous (H k ta) := fun k =>
            (hHc k).comp (continuous_const.prodMk continuous_id : Continuous fun t' : ℝ => (ta, t'))
          rw [e, chainT_finsum i (q + 1) α hFc K a (h := fun k => H k ta) hHta ta]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [chainT_expand α w hR i (q + 1) hSi (hHta k) ta]
      _ = ∑ k ∈ K, ∑ Zi ∈ Ui.powerset, a k * (∏ z ∈ Zi, w z) *
            ∫ ta in (0 : ℝ)..t, cexp (π * I * (ε q * α (σ q) * ta)) *
              chainT σ ε i (q + 1) (fun j => R j (Zi ∩ S j)) α ta (H k ta) := by
          simp_rw [Finset.mul_sum]
          have hc2 : ∀ k Zi, Continuous fun ta : ℝ => cexp (π * I * (ε q * α (σ q) * ta)) *
              (a k * ((∏ z ∈ Zi, w z) *
                chainT σ ε i (q + 1) (fun j => R j (Zi ∩ S j)) α ta (H k ta))) := fun k Zi =>
            he₁.mul (continuous_const.mul (continuous_const.mul (hIc k Zi)))
          rw [intervalIntegral_finsum_cont K (fun k ta => ∑ Zi ∈ Ui.powerset,
            cexp (π * I * (ε q * α (σ q) * ta)) * (a k * ((∏ z ∈ Zi, w z) *
              chainT σ ε i (q + 1) (fun j => R j (Zi ∩ S j)) α ta (H k ta))))
            (fun k => continuous_finsetSum _ fun Zi _ => hc2 k Zi)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [intervalIntegral_finsum_cont Ui.powerset (fun Zi ta =>
            cexp (π * I * (ε q * α (σ q) * ta)) * (a k * ((∏ z ∈ Zi, w z) *
              chainT σ ε i (q + 1) (fun j => R j (Zi ∩ S j)) α ta (H k ta)))) (hc2 k)]
          refine Finset.sum_congr rfl fun Zi _ => ?_
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun ta _ => ?_
          ring
      _ = ∑ Zq ∈ (S q).powerset, ∑ Zi ∈ Ui.powerset, ∑ Zr ∈ Ur.powerset,
            (∏ z ∈ Zq ∪ Zi ∪ Zr, w z) *
              chainT σ ε (.node i r) q (fun j => R j ((Zq ∪ Zi ∪ Zr) ∩ S j)) α t g := by
          rw [hK, Finset.sum_product]
          refine Finset.sum_congr rfl fun Zq hZq => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun Zi hZi => Finset.sum_congr rfl fun Zr hZr => ?_
          rw [hstep6 Zq hZq Zi hZi Zr hZr]
          rw [Finset.mem_powerset] at hZq hZi hZr
          rw [Finset.prod_union (Finset.disjoint_of_subset_left (Finset.union_subset_union hZq hZi)
              (Finset.disjoint_of_subset_right hZr (Finset.disjoint_union_left.2 ⟨hqr, hir⟩))),
            Finset.prod_union (Finset.disjoint_of_subset_left hZq
              (Finset.disjoint_of_subset_right hZi hqi))]
          simp only [ha]
          ring
      _ = _ := by
          rw [unionS_node, sum_powerset_union_of_disjoint
            (Finset.disjoint_union_left.2 ⟨hqr, hir⟩), sum_powerset_union_of_disjoint hqi]

end Expand

end WaveTurbulence.ClassJR
