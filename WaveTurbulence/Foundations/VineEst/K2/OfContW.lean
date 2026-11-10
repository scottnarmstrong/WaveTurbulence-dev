/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.Clamp2Bound

/-! # W2 session 20 (6B): the certified expansion with a selected clamp

`clampSel fl q J`: the two-sided clamp `clamp2J q J` when `fl` holds (the gate level is the root layer, so the total vanishes at `t = q`),
else the one-sided `clampJ q J`.  `sum_clampSel_eq`: the sum of the separated terms is the one of `clampJ` whenever the vanishing holds
below the gate (`couple_gate_vanish`, `tree_gate_vanish`).  `ofContW`: `ObjCert.ofCont` with the clamped time factors given as a family.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.LGSpine WaveTurbulence.VineEstS5C
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 MeasureTheory Set Filter
open scoped ENNReal

/-- The selected clamp. -/
noncomputable def clampSel (fl : Prop) [Decidable fl] (q : ℝ) (J : (Fin 2 → ℝ) → ℂ) : (Fin 2 → ℝ) → ℂ :=
  if fl then clamp2J q J else clampJ q J

theorem clampSel_of_pos {fl : Prop} [Decidable fl] (h : fl) (q : ℝ) (J : (Fin 2 → ℝ) → ℂ) :
    clampSel fl q J = clamp2J q J := if_pos h

theorem clampSel_of_neg {fl : Prop} [Decidable fl] (h : ¬ fl) (q : ℝ) (J : (Fin 2 → ℝ) → ℂ) :
    clampSel fl q J = clampJ q J := if_neg h

theorem clampSel_eq_clampJ_of_le {fl : Prop} [Decidable fl] {q : ℝ} {J : (Fin 2 → ℝ) → ℂ} {ts : Fin 2 → ℝ} (h : q ≤ ts 0) :
    clampSel fl q J ts = clampJ q J ts := by
  by_cases hf : fl
  · rw [clampSel_of_pos hf]; exact clamp2J_eq_clampJ h
  · rw [clampSel_of_neg hf]

theorem clampSel_continuousOn_ge {fl : Prop} [Decidable fl] {q : ℝ} {J : (Fin 2 → ℝ) → ℂ} (hJ : Continuous J) :
    ContinuousOn (clampSel fl q J) {ts | q ≤ ts 0} := by
  by_cases hf : fl
  · rw [clampSel_of_pos hf]; exact (clamp2J_continuous hJ).continuousOn
  · rw [clampSel_of_neg hf]
    have h : Continuous fun ts : Fin 2 → ℝ => J ![min (ts 0) (q + 1), ts 1] := by
      refine hJ.comp (continuous_pi fun l => ?_)
      fin_cases l
      · exact ((continuous_apply 0).min continuous_const)
      · exact continuous_apply 1
    refine h.continuousOn.congr fun ts hts => ?_
    unfold clampJ
    rw [if_neg (not_lt.2 hts)]

theorem clampSel_continuousOn_lt {fl : Prop} [Decidable fl] {q : ℝ} {J : (Fin 2 → ℝ) → ℂ} (hJ : Continuous J) :
    ContinuousOn (clampSel fl q J) {ts | ts 0 < q} := by
  by_cases hf : fl
  · rw [clampSel_of_pos hf]; exact (clamp2J_continuous hJ).continuousOn
  · rw [clampSel_of_neg hf]
    refine (continuousOn_const (c := (0 : ℂ))).congr fun ts hts => ?_
    unfold clampJ
    exact if_pos hts

/-- **The sums of the selected clamp and of `clampJ` agree** when the total vanishes at the gate level whenever the two-sided clamp is selected. -/
theorem sum_clampSel_eq {d m : ℕ} (fl : Prop) [Decidable fl] (c : ℝ) (Jg : Fin m → (Fin 2 → ℝ) → ℂ) (Mg : Fin m → Mom d → ℝ) {q : ℝ}
    (t s : ℝ) (k : Mom d) (hvan : fl → t < q → ∑ i, (c : ℂ) * Jg i ![q, s] * (Mg i k : ℂ) = 0) :
    ∑ i, sepTerm c (clampSel fl q (Jg i)) (Mg i) t s k = ∑ i, sepTerm c (clampJ q (Jg i)) (Mg i) t s k := by
  by_cases hf : fl
  · by_cases ht : t < q
    · simp only [clampSel_of_pos hf]
      exact sum_clamp2_eq_sum_clamp c Jg Mg t s k (hvan hf ht)
    · refine Finset.sum_congr rfl fun i _ => ?_
      unfold sepTerm
      rw [clampSel_eq_clampJ_of_le (fl := fl) (by simpa using ht)]
  · simp only [clampSel_of_neg hf]

section Root
open WaveTurbulence.VineEstS5C.P1 WaveTurbulence.Reg TTree
variable {P : WTParams} {h : ℕ → Mom P.d → ℝ} {n W p q q' : ℕ} {cost : ℝ}

/-- The couple total vanishes at the gate level when the gate level is the root layer. -/
theorem couple_gate_vanish {Q : RegCpl} {LG : LayeredGarden 2}
    (E : ContExp P n W (timeBox (q : ℝ) q') (fun ts k => SourceApp.couple P.δ h LG Q q q' (ts 0) (ts 1) k) cost)
    (hqq : q' ≤ q) (hqp : q ≤ p) (hcoh : IsCoherentCoupleAt p q q' Q LG) (hgt : q' < q) (hql : q ≤ cplRootLayer LG)
    {s : ℝ} (hs1 : (q' : ℝ) ≤ s) (hs2 : s ≤ q' + 1) (k : Mom P.d) :
    ∑ i, (P.δ ^ n : ℝ) * E.J i ![(q : ℝ), s] * (E.M i k : ℂ) = 0 := by
  have hr := (cpl_root_bounds hqq hqp hcoh).2
  have hrq : q = cplRootLayer LG := le_antisymm hql hr
  have hmem : ![(q : ℝ), s] ∈ timeBox (q : ℝ) q' := ⟨⟨by simp, by simp⟩, by simpa using And.intro hs1 hs2⟩
  have h1 := E.hexp _ hmem k
  have h2 : SourceApp.couple P.δ h LG Q q q' (q : ℝ) s k = 0 := by
    have := couple_root_vanish P.δ h hqq hqp hcoh (hrq ▸ hgt) s k
    rw [← hrq] at this
    exact this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  rw [h2] at h1
  push_cast
  exact h1.symm

/-- The tree total vanishes at the gate level when the gate level is the root layer. -/
theorem tree_gate_vanish {X : RegChain} {LG : LayeredGarden 1}
    (E : ContExp P n W (timeBoxGt (q : ℝ) q') (fun ts k => SourceApp.tree P.δ h LG X q q' (ts 0) (ts 1) k) cost)
    (hqq : q' ≤ q) (hcoh : IsCoherentTreeAt p q q' X LG) (hgt : q' < q) (hql : q ≤ treeRootLayer LG)
    {s : ℝ} (hs1 : (q' : ℝ) ≤ s) (hs2 : s < q' + 1) (k : Mom P.d) :
    ∑ i, (P.δ ^ n : ℝ) * E.J i ![(q : ℝ), s] * (E.M i k : ℂ) = 0 := by
  have hr := (tree_root_bounds hqq hcoh).2.1
  rw [← treeRootLayer_eq] at hr
  have hrq : q = treeRootLayer LG := le_antisymm hql hr
  have h2q : (q' : ℝ) + 1 ≤ q := by exact_mod_cast hgt
  have hmem : ![(q : ℝ), s] ∈ timeBoxGt (q : ℝ) q' :=
    ⟨⟨⟨by simp, by simp⟩, by simpa using And.intro hs1 hs2.le⟩, by simpa using (by linarith : s < q)⟩
  have h1 := E.hexp _ hmem k
  have h2 : SourceApp.tree P.δ h LG X q q' (q : ℝ) s k = 0 := by
    have := tree_root_vanish P.δ h hqq hcoh (hrq ▸ hgt) s k
    rw [← hrq] at this
    exact this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  rw [h2] at h1
  push_cast
  exact h1.symm

end Root

section OfContW
variable {P : WTParams} {n W : ℕ} {T : Set (Fin 2 → ℝ)} {F : (Fin 2 → ℝ) → Mom P.d → ℂ} {cost : ℝ}

/-- `ObjCert.ofCont` with the clamped time factors given as the family `J'` (with the window bounds and the identity on `V` stated for it). -/
noncomputable def ofContW (E : ContExp P n W T F cost) (J' : Fin E.m → (Fin 2 → ℝ) → ℂ) (f : ℝ → ℝ → Mom P.d → ℂ)
    (V : Set (Fin 2 → ℝ))
    (hV : ∀ t s : ℝ, ![t, s] ∈ V → ∀ k, f t s k = ∑ i, sepTerm (P.δ ^ n) (J' i) (E.M i) t s k)
    {Blo Bhi : Set (Fin 2 → ℝ)} {qlo qhi : Fin 2 → ℝ} (hclo : Blo ⊆ cell qlo) (hilo : Blo ⊆ closure (interior Blo))
    (hchi : Bhi ⊆ cell qhi) (hihi : Bhi ⊆ closure (interior Bhi)) (hC : 1 ≤ P.C₁) (hη : P.η ≤ 1) (hcost : 0 ≤ cost)
    (hlo : ∀ i, XNorm00Restr (V := Unit) (1 - P.η) Blo Set.univ (fun ts _ => J' i ts) ≤
      ENNReal.ofReal (TR P.η * (P.C₁ * P.C₁ ^ n)))
    (hhi : ∀ i, XNorm00Restr (V := Unit) (1 - P.η) Bhi Set.univ (fun ts _ => J' i ts) ≤
      ENNReal.ofReal (TR P.η * (P.C₁ * P.C₁ ^ n))) :
    ObjCert P W f Blo Bhi qlo qhi where
  toObjExp := ObjExp.ofPad (P.δ ^ n) J' E.M V hV
  CJ := certCJ P n
  CM := certCM P n cost
  lo := sepTPad hclo hilo (certCJ_pos hC hη n) (by unfold certCM; have h0 : 0 ≤ P.C₁ := (by linarith); exact mul_nonneg (mul_nonneg h0 (pow_nonneg h0 n)) hcost) (P.δ ^ n)
    J' E.M (fun i => (hlo i).trans_lt (lt_certCJ hC hη n)) E.hM
  hi := sepTPad hchi hihi (certCJ_pos hC hη n) (by unfold certCM; have h0 : 0 ≤ P.C₁ := (by linarith); exact mul_nonneg (mul_nonneg h0 (pow_nonneg h0 n)) hcost) (P.δ ^ n)
    J' E.M (fun i => (hhi i).trans_lt (lt_certCJ hC hη n)) E.hM
  lo_c _ := rfl
  lo_J _ := rfl
  lo_M _ := rfl
  hi_c _ := rfl
  hi_J _ := rfl
  hi_M _ := rfl

end OfContW

section SelBound
variable {η : ℝ} (hθ : 0 ≤ 1 - η) (hη : η ≤ 1)
include hθ hη

theorem clampSel_bound_C {fl : Prop} [Decidable fl] {q w L2 : ℕ} (hL2q : L2 ≤ q) (hcase : w = q ∨ q + 1 ≤ w ∨ w + 1 ≤ q)
    {Jc : (Fin 2 → ℝ) → ℂ} (hJc : Continuous Jc) {X : ℝ} (hX : 0 ≤ X)
    (hJ : XNorm00Restr (V := Unit) (1 - η) (timeBox (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X) :
    XNorm00Restr (V := Unit) (1 - η) (timeBox (w : ℝ) L2) Set.univ (fun ts _ => clampSel fl (q : ℝ) Jc ts) ≤
      ENNReal.ofReal (TR η * X) := by
  by_cases hf : fl
  · simp only [clampSel_of_pos hf]; exact clamp2_bound_C hθ hη hL2q hcase hJc hX hJ
  · simp only [clampSel_of_neg hf]; exact clamp_bound_C hθ hη hL2q hcase hJc hX hJ

theorem clampSel_bound_T {fl : Prop} [Decidable fl] {q w L2 : ℕ} (hL2q : L2 ≤ q) (hL2w : L2 ≤ w)
    (hcase : w = q ∨ q + 1 ≤ w ∨ w + 1 ≤ q)
    {Jc : (Fin 2 → ℝ) → ℂ} (hJc : Continuous Jc) {X : ℝ} (hX : 0 ≤ X)
    (hJ : XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X) :
    XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (w : ℝ) L2) Set.univ (fun ts _ => clampSel fl (q : ℝ) Jc ts) ≤
      ENNReal.ofReal (TR η * X) := by
  by_cases hf : fl
  · simp only [clampSel_of_pos hf]; exact clamp2_bound_T hθ hη hL2q hL2w hcase hJc hX hJ
  · simp only [clampSel_of_neg hf]; exact clamp_bound_T hθ hη hL2q hcase hJc hX hJ

end SelBound

end WaveTurbulence.VineEstS5C.P4.W2.K2
