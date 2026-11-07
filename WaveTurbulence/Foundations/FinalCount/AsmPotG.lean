/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPotW
public import WaveTurbulence.Foundations.FinalCount.AsmRho1
/-! **FINALCOUNT-ASSEMBLY: the exponent `g = 4η⁶(ρ + crit)` and the losses of the single-cut and triangle steps.**
`critCount crit s` = the number of present `ε` atoms satisfying the predicate `crit` (to be the critical `SG` atoms of the
counting choices).  A cut lowers `ρ` by at most `1` and `critCount` by at most `1`; a triangle step lowers `critCount` by at most `3`. -/
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

/-- Present `ε` atoms satisfying `crit`. -/
noncomputable def critCount (crit : V → Prop) (s : St.{u} V D₀) : ℕ := (s.M.atoms.filter fun a => s.cls a = .eps ∧ crit a).card

/-- The exponent of the potential. -/
noncomputable def gExp (η : ℝ) (crit : V → Prop) (h : HSt V D₀) : ℝ :=
  4 * η ^ 6 * ((h.s.M.rho : ℝ) + (critCount crit h.s : ℝ))

theorem critCount_cutSt (crit : V → Prop) (s : St.{u} V D₀) {v v₂ : V} {x₁ x₂ : s.D} (hc : s.M.IsCutData v v₂ x₁ x₂) (c₁ c₂ : Cls) :
    critCount crit s ≤ critCount crit (s.cutSt v v₂ x₁ x₂ c₁ c₂) + 1 := by
  obtain ⟨hv, hv₂, -⟩ := hc
  have hne : v ≠ v₂ := fun e => hv₂ (e ▸ hv)
  unfold critCount
  have hsub : (s.M.atoms.filter fun a => s.cls a = .eps ∧ crit a).erase v ⊆
      (s.cutSt v v₂ x₁ x₂ c₁ c₂).M.atoms.filter fun a => (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls a = .eps ∧ crit a := by
    intro a ha
    obtain ⟨hav, ha'⟩ := Finset.mem_erase.1 ha
    obtain ⟨ham, hε, hcr⟩ := Finset.mem_filter.1 ha'
    have hav2 : a ≠ v₂ := fun e => hv₂ (e ▸ ham)
    refine Finset.mem_filter.2 ⟨?_, ?_, hcr⟩
    · rw [cutSt_atoms]; exact Finset.mem_insert_of_mem ham
    · rw [cutSt_cls, Function.update_of_ne hav2, Function.update_of_ne hav]; exact hε
  have := Finset.card_le_card hsub
  have h2 := Finset.pred_card_le_card_erase (s := s.M.atoms.filter fun a => s.cls a = .eps ∧ crit a) (a := v)
  omega

theorem critCount_triSt (crit : V → Prop) {s : St.{u} V D₀} (T : TriData s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hcl : PClosed T.kept (triKeep s T)) :
    critCount crit s ≤ critCount crit (triSt s T Q kp hcl) + 3 := by
  unfold critCount
  set S := s.M.atoms.filter fun a => s.cls a = .eps ∧ crit a
  have hsub : S \ (Finset.univ.image T.t) ⊆
      (triSt s T Q kp hcl).M.atoms.filter fun a => (triSt s T Q kp hcl).cls a = .eps ∧ crit a := by
    intro a ha
    obtain ⟨haS, hat⟩ := Finset.mem_sdiff.1 ha
    obtain ⟨ham, hε, hcr⟩ := Finset.mem_filter.1 haS
    have hf : ∀ j, a ≠ T.f j := fun j e => T.f_fresh j (e ▸ ham)
    have hP : T.TP a := fun j e => hat (Finset.mem_image.2 ⟨j, Finset.mem_univ _, e.symm⟩)
    refine Finset.mem_filter.2 ⟨?_, ?_, hcr⟩
    · show a ∈ (T.m3.atoms.filter T.TP).filter (triKeep s T)
      refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨?_, hP⟩, fun j _ => hf j⟩
      rw [TriData.m3_atoms]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ham))
    · show triCls s T Q kp a = .eps
      rw [triCls_other T Q kp hf]; exact hε
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ.image T.t).card ≤ 3 := by
    refine (Finset.card_image_le).trans ?_; simp
  have h3 := Finset.le_card_sdiff (Finset.univ.image T.t) S
  omega

end WaveTurbulence.FinalCountAsm
