/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTriPot
/-! **FINALCOUNT-ASSEMBLY, phase 2: the potential form of a general (ghost or not) triangle step.**
`stepRHS h (triPost T Q kp hcl) = excessRHS (triAlphaNew h T Q kp) (ΔF) (betaCount' - betaCount) / labelProd (alphaGhostList h T)`,
which is the right-hand side of the charged G3 `UStep2.excess`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section
variable {s : St.{u} V D₀} (T : TriData s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)

theorem triSt_atoms' (hcl : PClosed T.kept (triKeep s T)) :
    (triSt s T Q kp hcl).M.atoms =
      ((Finset.univ.filter fun j : Fin 3 => s.cls (T.t j) = .eps).image T.f) ∪ s.M.atoms.filter T.TP := by
  show ((T.m3.atoms.filter T.TP).filter (triKeep s T)) = _
  ext a
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, TriData.m3_atoms, Finset.mem_insert]
  constructor
  · rintro ⟨⟨hm, hP⟩, hk⟩
    rcases hm with rfl | rfl | rfl | hm
    · exact Or.inl ⟨2, by_contra fun hn => hk 2 hn rfl, rfl⟩
    · exact Or.inl ⟨1, by_contra fun hn => hk 1 hn rfl, rfl⟩
    · exact Or.inl ⟨0, by_contra fun hn => hk 0 hn rfl, rfl⟩
    · exact Or.inr ⟨hm, hP⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨hm, hP⟩)
    · refine ⟨⟨?_, T.TP_f j⟩, fun i hi e => hi (T.f_inj e ▸ hj)⟩
      fin_cases j
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · exact ⟨⟨Or.inr (Or.inr (Or.inr hm)), hP⟩, fun j _ e => T.f_fresh j (e ▸ hm)⟩

theorem apProd_tri_split (L γ η : ℝ) :
    apProd L γ η s = (∏ a ∈ s.M.atoms.filter T.TP, apFactor L γ η (s.cls a)) * ∏ j : Fin 3, apFactor L γ η (s.cls (T.t j)) := by
  unfold apProd
  have hsplit : s.M.atoms = s.M.atoms.filter T.TP ∪ Finset.univ.image T.t := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, TriData.TP]
    constructor
    · intro ha
      by_cases hP : ∀ j, a ≠ T.t j
      · exact Or.inl ⟨ha, hP⟩
      · push Not at hP; obtain ⟨j, hj⟩ := hP; exact Or.inr ⟨j, hj.symm⟩
    · rintro (⟨ha, -⟩ | ⟨j, rfl⟩)
      · exact ha
      · exact T.t_mem j
  have hdis : Disjoint (s.M.atoms.filter T.TP) (Finset.univ.image T.t) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hb
    exact (Finset.mem_filter.1 ha).2 j rfl
  conv_lhs => rw [hsplit]
  rw [Finset.prod_union hdis, Finset.prod_image (fun i _ j _ e => T.t_inj e)]

theorem apProd_triSt_split (L γ η : ℝ) (hcl : PClosed T.kept (triKeep s T)) :
    apProd L γ η (triSt s T Q kp hcl) =
      (∏ j : Fin 3, if s.cls (T.t j) = .eps then apFactor L γ η (triCls s T Q kp (T.f j)) else 1) *
        ∏ a ∈ s.M.atoms.filter T.TP, apFactor L γ η (s.cls a) := by
  unfold apProd
  rw [triSt_atoms' T Q kp hcl, Finset.prod_union, Finset.prod_image (fun i hi j hj e => T.f_inj e)]
  · congr 1
    · rw [← Finset.prod_filter]; rfl
    · refine Finset.prod_congr rfl fun a ha => ?_
      have hf : ∀ j, a ≠ T.f j := fun j e => T.f_fresh j (e ▸ (Finset.mem_filter.1 ha).1)
      show apFactor L γ η (triCls s T Q kp a) = _
      rw [triCls_other T Q kp hf]
  · rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
    exact T.f_fresh j (Finset.mem_filter.1 hb).1


end

theorem prod_ghost_eq (L γ η : ℝ) (h : HSt V D₀) (T : TriData h.s.M) :
    ∏ j : Fin 3, apFactor L γ η (h.s.cls (T.t j)) = labelProd L γ η (alphaGhostList h T) := by
  unfold alphaGhostList labelProd
  rw [Fin.prod_univ_three]
  rcases hc0 : h.s.cls (T.t 0) with _ | ⟨R0, k0⟩ | _ | _ <;> rcases hc1 : h.s.cls (T.t 1) with _ | ⟨R1, k1⟩ | _ | _ <;>
    rcases hc2 : h.s.cls (T.t 2) with _ | ⟨R2, k2⟩ | _ | _ <;>
    simp [List.finRange, apFactor, hc0, hc1, hc2, List.filterMap_cons] <;> ring

theorem prod_new_eq (L γ η : ℝ) (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ) :
    ∏ j : Fin 3, (if h.s.cls (T.t j) = .eps then apFactor L γ η (triCls h.s T Q kp (T.f j)) else 1) =
      labelProd L γ η (triAlphaNew h T Q kp) := by
  unfold triAlphaNew labelProd
  rw [Fin.prod_univ_three, triCls_f0, triCls_f1, triCls_f2]
  by_cases e0 : h.s.cls (T.t 0) = .eps <;> by_cases e1 : h.s.cls (T.t 1) = .eps <;> by_cases e2 : h.s.cls (T.t 2) = .eps <;>
    by_cases s0 : T.kept.SameComponent (T.f 0) (T.f 2) ∨ T.kept.SameComponent (T.f 0) (T.f 1) <;>
    by_cases s1 : T.kept.SameComponent (T.f 1) (T.f 2) <;>
    simp [List.finRange, apFactor, e0, e1, e2, s0, s1, triCls_f0, triCls_f1, List.filterMap_cons]

/-- **The potential form of a general triangle step** (`stepRHS = excessRHS(new α) / ∏(α-ghosts)`). -/
theorem stepRHS_tri' {L γ η : ℝ} (hL : 0 < L) {h : HSt V D₀} (hap : ApPos h.s) (T : TriData h.s.M) (Q : Fin 2 → ℝ)
    (kp : Fin 2 → ℕ) (hcl : PClosed T.kept (triKeep h.s T)) :
    stepRHS L γ η h (h.triPost T Q kp hcl) =
      excessRHS L γ η (triAlphaNew h T Q kp) (((h.triPost T Q kp hcl).s.M.numComponents : ℤ) - h.s.M.numComponents)
        (betaCount (h.triPost T Q kp hcl).s - betaCount h.s) / labelProd L γ η (alphaGhostList h T) := by
  have hAp := apProd_pos (L := L) (γ := γ) (η := η) hL hap
  have hY : 0 < labelProd L γ η (alphaGhostList h T) := by
    rw [← prod_ghost_eq]
    exact Finset.prod_pos fun j _ => apFactor_pos hL (hap _ (T.t_mem j))
  have e1 := apProd_tri_split T L γ η
  have e2 := apProd_triSt_split T Q kp L γ η hcl
  rw [prod_ghost_eq] at e1
  rw [prod_new_eq] at e2
  have hA : (∏ a ∈ h.s.M.atoms.filter T.TP, apFactor L γ η (h.s.cls a)) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e1; exact hAp.ne' e1
  have hrat : apProd L γ η (h.triPost T Q kp hcl).s / apProd L γ η h.s =
      labelProd L γ η (triAlphaNew h T Q kp) / labelProd L γ η (alphaGhostList h T) := by
    have : apProd L γ η (h.triPost T Q kp hcl).s = apProd L γ η (triSt h.s T Q kp hcl) := rfl
    rw [this, e2]
    conv_lhs => rw [e1]
    field_simp
  unfold stepRHS excessRHS
  rw [hrat]
  have hb : ((betaCount (h.triPost T Q kp hcl).s - betaCount h.s : ℤ) : ℝ) = (vBeta (h.triPost T Q kp hcl).s : ℝ) - vBeta h.s := by
    simp [betaCount, vBeta]
  have hF : ((((h.triPost T Q kp hcl).s.M.numComponents : ℤ) - h.s.M.numComponents : ℤ) : ℝ) =
      ((h.triPost T Q kp hcl).s.M.numComponents : ℝ) - h.s.M.numComponents := by push_cast; ring
  rw [hb, hF]
  unfold labelProd
  ring

end WaveTurbulence.FinalCountAsm
