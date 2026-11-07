/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPotG
/-! **FINALCOUNT-ASSEMBLY: `ρ` under a triangle removal** (`ρ(M) ≤ ρ(triSt) + 9`: three cuts, the removal of the triangle component,
the deletion of the ghosts). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [DecidableEq D₀]

theorem deg4_cut {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D} (hcd : M.IsCutData v v₂ x₁ x₂)
    (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) : ∀ x ∈ (M.cut v v₂ x₁ x₂).atoms, (M.cut v v₂ x₁ x₂).deg x ≤ 4 := by
  intro x hx
  by_cases h1 : x = v
  · subst h1; rw [cut_deg_v M hcd]; omega
  · by_cases h2 : x = v₂
    · subst h2; have := cut_deg_v₂ M hcd; have := hM v hcd.1; omega
    · rw [cut_deg_other hcd h1 h2]
      exact hM x ((Finset.mem_insert.1 hx).resolve_left h2)

theorem deg4_restrict {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (P : V → Prop) [DecidablePred P] (h : PClosed M P)
    (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) : ∀ x ∈ (restrictP M P h).atoms, (restrictP M P h).deg x ≤ 4 := by
  intro x hx
  have hx' := Finset.mem_filter.1 hx
  rw [restrictP_deg M P h hx'.2]; exact hM x hx'.1

theorem rho_tri_le {s : St.{u} V D₀} [Fintype D₀] (T : TriData s.M) (hM : ∀ x ∈ s.M.atoms, s.M.deg x ≤ 4)
    (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ) (hcl : PClosed T.kept (triKeep s T)) :
    s.M.rho ≤ (triSt s T Q kp hcl).M.rho + 9 := by
  have hM1 := deg4_cut s.M T.cd1 hM
  have hM2 := deg4_cut T.m1 T.cd2 hM1
  have hM3 := deg4_cut T.m2 T.cd3 hM2
  have r1 := rho_le_cut s.M T.cd1 hM
  have r2 := rho_le_cut T.m1 T.cd2 hM1
  have r3 := rho_le_cut T.m2 T.cd3 hM2
  have hk : ∀ x ∈ T.kept.atoms, T.kept.deg x ≤ 4 := deg4_restrict T.m3 T.TP T.pclosed hM3
  -- restriction to the complement of the triangle
  have t1 := (restrictTransfer T.m3 T.TP T.pclosed).rho_le
  have l1 := ladderLoss_le_card T.m3 hM3 (T.m3.atoms.filter T.TP)
  have c1 : (T.m3.atoms \ T.m3.atoms.filter T.TP).card ≤ 3 := by
    have : T.m3.atoms \ T.m3.atoms.filter T.TP ⊆ Finset.univ.image T.t := by
      intro a ha
      obtain ⟨ham, hn⟩ := Finset.mem_sdiff.1 ha
      have : ¬ T.TP a := fun hP => hn (Finset.mem_filter.2 ⟨ham, hP⟩)
      simp only [TriData.TP, not_forall, not_not] at this
      obtain ⟨j, rfl⟩ := this
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    exact (Finset.card_le_card this).trans (Finset.card_image_le.trans (by simp))
  -- ghost deletion
  have t2 := (restrictTransfer T.kept (triKeep s T) hcl).rho_le
  have l2 := ladderLoss_le_card T.kept hk (T.kept.atoms.filter (triKeep s T))
  have c2 : (T.kept.atoms \ T.kept.atoms.filter (triKeep s T)).card ≤ 3 := by
    have : T.kept.atoms \ T.kept.atoms.filter (triKeep s T) ⊆ Finset.univ.image T.f := by
      intro a ha
      obtain ⟨ham, hn⟩ := Finset.mem_sdiff.1 ha
      have : ¬ triKeep s T a := fun hP => hn (Finset.mem_filter.2 ⟨ham, hP⟩)
      simp only [triKeep, not_forall, not_not] at this
      obtain ⟨j, -, rfl⟩ := this
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    exact (Finset.card_le_card this).trans (Finset.card_image_le.trans (by simp))
  show s.M.rho ≤ (restrictP T.kept (triKeep s T) hcl).rho + 9
  change T.kept.rho ≤ (restrictP T.kept (triKeep s T) hcl).rho + ladderLoss T.kept (T.kept.atoms.filter (triKeep s T)) at t2
  change T.m3.rho ≤ T.kept.rho + ladderLoss T.m3 (T.m3.atoms.filter T.TP) at t1
  change s.M.rho ≤ T.m1.rho + 1 at r1
  change T.m1.rho ≤ T.m2.rho + 1 at r2
  change T.m2.rho ≤ T.m3.rho + 1 at r3
  omega

end WaveTurbulence.FinalCountAsm
