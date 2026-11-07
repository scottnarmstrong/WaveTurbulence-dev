/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineDouble2
/-! The label count of a VC formed by two double bonds, part 3: the label vector `restrS κ` is determined by
`(κ x₁, κ x₂, κ y₁)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace DoubleShape
variable {M : Molecule V D} {K : VineCut M} (S : DoubleShape K)
variable {L γ δ : ℝ} {w : Mom d} {Adm : (D → (Fin d → ℤ)) → Prop} {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d}
  {κ κ' : D → (Fin d → ℤ)}
include S

theorem cutMol_dartsAt_a : K.cutMol.dartsAt K.C.upper = {K.x₁, K.x₂} := by
  rw [VineCut.cutMol_eq, cut_dartsAt_other K.m1 K.cut_b K.ab_ne K.fb_ne_a.symm]
  exact cut_dartsAt_v_eq M K.cut_a

theorem cutMol_dartsAt_b : K.cutMol.dartsAt K.C.lower = {K.y₁, K.y₂} := cut_dartsAt_v_eq K.m1 K.cut_b

theorem restrS_eq (hP : ParamOK M c k0) (hL : 0 < L) (hκ : κ ∈ decSet M L γ δ w Adm c β k0)
    (hκ' : κ' ∈ decSet M L γ δ w Adm c β k0) (h1 : κ K.x₁ = κ' K.x₁) (h2 : κ K.x₂ = κ' K.x₂)
    (h3 : κ K.y₁ = κ' K.y₁) : K.restrS κ = K.restrS κ' := by
  have h4 : κ K.y₂ = κ' K.y₂ := by
    rw [S.lat_cons hP hL hκ, S.lat_cons hP hL hκ', h1, h2, h3]
  funext z
  unfold VineCut.restrS
  by_cases hz : K.cutMol.atom z ∈ K.C.atoms
  · rw [if_pos hz, if_pos hz]
    have hm : z ∈ K.cutMol.dartsAt (K.cutMol.atom z) := (mem_dartsAt _ _ _).2 rfl
    have hm1 : ∀ y, κ (M.mate y) = κ y := fun y => hκ.1.1 y
    have hm2 : ∀ y, κ' (M.mate y) = κ' y := fun y => hκ'.1.1 y
    rw [S.atoms_eq] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz
    · rw [hz, S.cutMol_dartsAt_a] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl <;> assumption
    · rw [hz, K.dartsAt_other S.x_mem S.x_ne_a S.x_ne_b, S.darts_x] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · rw [hm1, hm2]; exact h1
      · rw [hm1, hm2]; exact h2
      · rw [hm1, hm2]; exact h3
      · rw [hm1, hm2]; exact h4
    · rw [hz, S.cutMol_dartsAt_b] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl <;> assumption
  · rw [if_neg hz, if_neg hz]

end DoubleShape
end WaveTurbulence.FinalCount
