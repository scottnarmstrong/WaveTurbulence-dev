/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTriBridge
public import WaveTurbulence.Foundations.FinalCount.AsmPot3
/-! **FINALCOUNT-ASSEMBLY, phase 2: the potential bookkeeping of a ghost-free triangle step.**  For a triangle `T` of `ε` atoms:
`numComponents (triSt …) = T.kept.numComponents`, `vBeta' = vBeta + 1 + [¬A₀] + [¬A₁]`, `apProd' = apProd · ∏ new α factors`, hence
`stepRHS h (triPost …) = excessRHS (alphaLabels …) ΔF (3 - #α)` (the form of G3 `UStep2.excess`). -/
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

theorem numComponents_restrictP_true {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (P : V → Prop)
    [DecidablePred P] (h : PClosed M P) (hP : ∀ a ∈ M.atoms, P a) :
    (restrictP M P h).numComponents = M.numComponents := by
  unfold Molecule.numComponents
  have hmem : ∀ u : V, u ∈ (restrictP M P h).atoms ↔ u ∈ M.atoms := fun u => by
    show u ∈ M.atoms.filter P ↔ _
    rw [Finset.mem_filter]; exact ⟨fun h => h.1, fun hu => ⟨hu, hP u hu⟩⟩
  let e : (restrictP M P h).atoms ≃ M.atoms := Equiv.subtypeEquivRight hmem
  refine Nat.card_congr (Quot.congr e (fun a b => ?_))
  show (restrictP M P h).Adj a.1 b.1 ↔ M.Adj a.1 b.1
  constructor
  · rintro ⟨x, h1, h2⟩; exact ⟨x.1, h1, h2⟩
  · rintro ⟨x, h1, h2⟩
    exact ⟨⟨x, hP _ (h1 ▸ M.atom_mem x)⟩, h1, h2⟩

section tri
variable {s : St.{u} V D₀} (T : TriData s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)

theorem triKeep_true (hε : ∀ j, s.cls (T.t j) = .eps) : ∀ a, triKeep s T a := fun a j hj => absurd (hε j) hj

theorem triSt_atoms (hcl : PClosed T.kept (triKeep s T)) (hε : ∀ j, s.cls (T.t j) = .eps) :
    (triSt s T Q kp hcl).M.atoms = (Finset.univ.image T.f) ∪ s.M.atoms.filter T.TP := by
  show ((T.m3.atoms.filter T.TP).filter (triKeep s T)) = _
  rw [Finset.filter_true_of_mem (fun a _ => triKeep_true T hε a), TriData.m3_atoms, Finset.filter_insert, Finset.filter_insert,
    Finset.filter_insert]
  have h0 : T.TP (T.f 0) := T.TP_f 0
  have h1 : T.TP (T.f 1) := T.TP_f 1
  have h2 : T.TP (T.f 2) := T.TP_f 2
  rw [if_pos h2, if_pos h1, if_pos h0]
  ext a
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro (rfl | rfl | rfl | h)
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inr h
  · rintro (⟨j, rfl⟩ | h)
    · fin_cases j
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr h))

theorem triSt_cls (hcl : PClosed T.kept (triKeep s T)) : (triSt s T Q kp hcl).cls = triCls s T Q kp := rfl

theorem triSt_numComponents (hcl : PClosed T.kept (triKeep s T)) (hε : ∀ j, s.cls (T.t j) = .eps) :
    (triSt s T Q kp hcl).M.numComponents = T.kept.numComponents := by
  show (restrictP T.kept (triKeep s T) hcl).numComponents = _
  refine numComponents_restrictP_true _ _ hcl (fun a _ => triKeep_true T hε a)

/-- Sum over the atoms of the triangle state. -/
theorem triSt_sum (hcl : PClosed T.kept (triKeep s T)) (hε : ∀ j, s.cls (T.t j) = .eps) (g : V → ℕ)
    (hg : ∀ j, g (T.t j) = 0) :
    ∑ a ∈ (triSt s T Q kp hcl).M.atoms, g a = ∑ j : Fin 3, g (T.f j) + ∑ a ∈ s.M.atoms, g a := by
  rw [triSt_atoms T Q kp hcl hε, Finset.sum_union, Finset.sum_image (fun i _ j _ e => T.f_inj e), Finset.sum_filter]
  · congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    by_cases hP : T.TP a
    · simp [hP]
    · simp only [TriData.TP, not_forall, not_not] at hP
      obtain ⟨j, rfl⟩ := hP
      simp [TriData.TP, hg j]
  · rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
    exact T.f_fresh j (Finset.mem_filter.1 hb).1

theorem triSt_prod (hcl : PClosed T.kept (triKeep s T)) (hε : ∀ j, s.cls (T.t j) = .eps) (g : V → ℝ)
    (hg : ∀ j, g (T.t j) = 1) :
    ∏ a ∈ (triSt s T Q kp hcl).M.atoms, g a = (∏ j : Fin 3, g (T.f j)) * ∏ a ∈ s.M.atoms, g a := by
  rw [triSt_atoms T Q kp hcl hε, Finset.prod_union, Finset.prod_image (fun i _ j _ e => T.f_inj e), Finset.prod_filter]
  · congr 1
    refine Finset.prod_congr rfl fun a ha => ?_
    by_cases hP : T.TP a
    · simp [hP]
    · simp only [TriData.TP, not_forall, not_not] at hP
      obtain ⟨j, rfl⟩ := hP
      simp [TriData.TP, hg j]
  · rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
    exact T.f_fresh j (Finset.mem_filter.1 hb).1

end tri

section tri2
variable {s : St.{u} V D₀} (T : TriData s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)

theorem triCls_t (hε : ∀ j, s.cls (T.t j) = .eps) (j : Fin 3) : triCls s T Q kp (T.t j) = .eps := by
  rw [triCls_other T Q kp (fun k e => T.f_ne_t k j e.symm)]; exact hε j

theorem triSt_vBeta (hcl : PClosed T.kept (triKeep s T)) (hε : ∀ j, s.cls (T.t j) = .eps) :
    vBeta (triSt s T Q kp hcl) = vBeta s + 1 + (if T.IsA0 then 0 else 1) + (if T.IsA1 then 0 else 1) := by
  have key := triSt_sum T Q kp hcl hε (fun a => if triCls s T Q kp a = .beta then 1 else 0)
    (fun j => by simp [triCls_t T Q kp hε j])
  have e1 : vBeta (triSt s T Q kp hcl) = ∑ a ∈ (triSt s T Q kp hcl).M.atoms, (if triCls s T Q kp a = .beta then 1 else 0) := by
    unfold vBeta; rw [Finset.card_filter]; rfl
  have e2 : vBeta s = ∑ a ∈ s.M.atoms, (if triCls s T Q kp a = .beta then 1 else 0) := by
    unfold vBeta; rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [triCls_other T Q kp (fun k e => T.f_fresh k (e ▸ ha))]
  rw [e1, key, e2, Fin.sum_univ_three, triCls_f0, triCls_f1, triCls_f2, hε 0, hε 1, hε 2]
  by_cases h0 : T.IsA0 <;> by_cases h1 : T.IsA1 <;> simp [← isA0_iff T, ← isA1_iff T, h0, h1] <;> ring

theorem triSt_apProd (L γ η : ℝ) (hcl : PClosed T.kept (triKeep s T)) (hε : ∀ j, s.cls (T.t j) = .eps) :
    apProd L γ η (triSt s T Q kp hcl) = apProd L γ η s *
      ((if T.IsA0 then apFactor L γ η (.alpha (Q 0) (kp 0)) else 1) * (if T.IsA1 then apFactor L γ η (.alpha (Q 1) (kp 1)) else 1)) := by
  have key := triSt_prod T Q kp hcl hε (fun a => apFactor L γ η (triCls s T Q kp a))
    (fun j => by simp [triCls_t T Q kp hε j, apFactor])
  have e2 : apProd L γ η s = ∏ a ∈ s.M.atoms, apFactor L γ η (triCls s T Q kp a) := by
    unfold apProd
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [triCls_other T Q kp (fun k e => T.f_fresh k (e ▸ ha))]
  have e1 : apProd L γ η (triSt s T Q kp hcl) = ∏ a ∈ (triSt s T Q kp hcl).M.atoms, apFactor L γ η (triCls s T Q kp a) := rfl
  rw [e1, key, e2, Fin.prod_univ_three, triCls_f0, triCls_f1, triCls_f2, hε 0, hε 1, hε 2]
  by_cases h0 : T.IsA0 <;> by_cases h1 : T.IsA1 <;> simp [← isA0_iff T, ← isA1_iff T, h0, h1, apFactor] <;> ring

end tri2

/-- **The potential form of a ghost-free triangle step is the form of G2/G3 `excessprop1`.** -/
theorem stepRHS_tri {L γ η : ℝ} (hL : 0 < L) {h : HSt V D₀} (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hcl : PClosed T.kept (triKeep h.s T)) (hε : ∀ j, h.s.cls (T.t j) = .eps) (hAp : 0 < apProd L γ η h.s) :
    stepRHS L γ η h (h.triPost T Q kp hcl) =
      excessRHS L γ η (T.alphaLabels (Q 0) (Q 1) (kp 0) (kp 1)) ((T.kept.numComponents : ℤ) - h.s.M.numComponents)
        (3 - ((T.alphaLabels (Q 0) (Q 1) (kp 0) (kp 1)).length : ℤ)) := by
  have hF : (triSt h.s T Q kp hcl).M.numComponents = T.kept.numComponents := triSt_numComponents T Q kp hcl hε
  have hB := triSt_vBeta T Q kp hcl hε
  have hA := triSt_apProd T Q kp L γ η hcl hε
  have hdF := T.deltaF_eq
  unfold stepRHS excessRHS
  change L ^ (-η ^ 3) * L ^ ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((triSt h.s T Q kp hcl).M.numComponents : ℝ) - h.s.M.numComponents) -
      (min γ (1 - γ) + 2 * η ^ 2) * ((vBeta (triSt h.s T Q kp hcl) : ℝ) - vBeta h.s)) *
      (apProd L γ η (triSt h.s T Q kp hcl) / apProd L γ η h.s) = _
  rw [hF, hB, hA, mul_div_cancel_left₀ _ hAp.ne']
  have hdF' : ((T.kept.numComponents : ℝ) - h.s.M.numComponents) = (if T.IsA0 then 0 else 1) + (if T.IsA1 then 0 else 1) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hdF
    simpa using this
  have key : ∀ (e1 e2 : ℝ), e1 = e2 → ∀ X P : ℝ, X * L ^ e1 * P = X * P * L ^ e2 := by
    intro e1 e2 e X P; subst e; ring
  push_cast
  rw [hdF']
  unfold TriData.alphaLabels
  by_cases h0 : T.IsA0 <;> by_cases h1 : T.IsA1 <;> simp [h0, h1, apFactor]
  all_goals first | exact key _ _ (by ring) _ _ | (left; congr 1; ring)

end WaveTurbulence.FinalCountAsm
