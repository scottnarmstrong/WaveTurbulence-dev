/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriCount1
/-! Triangles, part 11 (FINALCOUNT-G2): the relations between two decorations of the same parameter triple
forced by a `β`-cut (DH23 L1790--L1793: the gap `k_{ℓ_j} - k_{ℓ_{j+1}}` is fixed by summing over the component, and
the energy lies in one window). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem two_window {a b B : ℝ} {W : ℝ} (ha : |a - B| ≤ W) (hb : |b - B| ≤ W) : |a - b| ≤ 2 * W := by
  have := abs_sub_le a B b
  rw [abs_sub_comm B b] at this
  linarith

namespace TriData
variable {M : Molecule V D} (T : TriData M)

theorem idx_S0 : T.idx T.S0 = {0} := by
  ext j
  simp only [idx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact T.f_mem_S0_iff j

theorem idx_S1_cases : T.idx T.S1 = {1} ∨ T.idx T.S1 = {0, 1} := by
  have h1 : (1 : Fin 3) ∈ T.idx T.S1 := by simp [idx, T.f1_mem_S1]
  have h2 : (2 : Fin 3) ∉ T.idx T.S1 := by simp [idx, T.f2_nmem_S1]
  by_cases h0 : (0 : Fin 3) ∈ T.idx T.S1
  · right
    ext j
    fin_cases j <;> simp_all
  · left
    ext j
    fin_cases j <;> simp_all

/-- Relation from the first `β`-cut. -/
theorem rel0 (hβ : ¬ T.m1.SameComponent (T.t 0) (T.f 0)) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ κ' : D → (Fin d → ℤ))
    (hκ : κ ∈ decSet M L γ δ w Adm c β k0) (hκ' : κ' ∈ decSet M L γ δ w Adm c β k0) :
    triC L w (T.triZ κ) 0 = triC L w (T.triZ κ') 0 ∧
      |triG L w (T.triZ κ) 0 - triG L w (T.triZ κ') 0| ≤ 2 * (M.atoms.card * (δ⁻¹ * L ^ (-2 * γ))) := by
  have r1 := T.closed_rel (T.S0_closed hβ) T.S0_sub3 (T.t_nmem_S0 hβ) L γ δ w Adm c β k0 κ hκ
  have r2 := T.closed_rel (T.S0_closed hβ) T.S0_sub3 (T.t_nmem_S0 hβ) L γ δ w Adm c β k0 κ' hκ'
  rw [T.idx_S0] at r1 r2
  simp only [Finset.sum_singleton] at r1 r2
  refine ⟨r1.1.trans r2.1.symm, ?_⟩
  have hc := T.card_le_atoms (T.t_nmem_S0 hβ)
  rw [T.idx_S0] at hc
  have hW : (0 : ℝ) ≤ δ⁻¹ * L ^ (-2 * γ) := by positivity
  have hcr : (((T.S0.filter (fun a => a ∈ M.atoms)).card + ({0} : Finset (Fin 3)).card : ℕ) : ℝ) ≤ M.atoms.card := by
    exact_mod_cast hc
  have h1 := r1.2.trans (mul_le_mul_of_nonneg_right hcr hW)
  have h2 := r2.2.trans (mul_le_mul_of_nonneg_right hcr hW)
  exact two_window h1 h2

/-- Shared set-up of the second `β`-cut. -/
theorem rel1_base (hβ : ¬ T.m2.SameComponent (T.t 1) (T.f 1)) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ κ' : D → (Fin d → ℤ))
    (hκ : κ ∈ decSet M L γ δ w Adm c β k0) (hκ' : κ' ∈ decSet M L γ δ w Adm c β k0) :
    ∑ j ∈ T.idx T.S1, triC L w (T.triZ κ) j = ∑ j ∈ T.idx T.S1, triC L w (T.triZ κ') j ∧
      |∑ j ∈ T.idx T.S1, triG L w (T.triZ κ) j - ∑ j ∈ T.idx T.S1, triG L w (T.triZ κ') j| ≤
        2 * (M.atoms.card * (δ⁻¹ * L ^ (-2 * γ))) := by
  have r1 := T.closed_rel (T.S1_closed hβ) T.S1_sub3 (T.t_nmem_S1 hβ) L γ δ w Adm c β k0 κ hκ
  have r2 := T.closed_rel (T.S1_closed hβ) T.S1_sub3 (T.t_nmem_S1 hβ) L γ δ w Adm c β k0 κ' hκ'
  have hc := T.card_le_atoms (T.t_nmem_S1 hβ)
  have hcr : (((T.S1.filter (fun a => a ∈ M.atoms)).card + (T.idx T.S1).card : ℕ) : ℝ) ≤ M.atoms.card := by
    exact_mod_cast hc
  have hW : (0 : ℝ) ≤ δ⁻¹ * L ^ (-2 * γ) := by positivity
  have h1 := r1.2.trans (mul_le_mul_of_nonneg_right hcr hW)
  have h2 := r2.2.trans (mul_le_mul_of_nonneg_right hcr hW)
  exact ⟨r1.1.trans r2.1.symm, two_window h1 h2⟩

/-- Second `β`-cut, when only the second gap is involved. -/
theorem rel1a (hi : T.idx T.S1 = {1}) (hβ : ¬ T.m2.SameComponent (T.t 1) (T.f 1)) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ κ' : D → (Fin d → ℤ))
    (hκ : κ ∈ decSet M L γ δ w Adm c β k0) (hκ' : κ' ∈ decSet M L γ δ w Adm c β k0) :
    triC L w (T.triZ κ) 1 = triC L w (T.triZ κ') 1 ∧
      |triG L w (T.triZ κ) 1 - triG L w (T.triZ κ') 1| ≤ 2 * (M.atoms.card * (δ⁻¹ * L ^ (-2 * γ))) := by
  have := T.rel1_base hβ L γ δ hL hδ w Adm c β k0 κ κ' hκ hκ'
  rw [hi] at this
  simpa using this

/-- Second `β`-cut, when the first gap is involved too. -/
theorem rel1b (hi : T.idx T.S1 = {0, 1}) (hβ : ¬ T.m2.SameComponent (T.t 1) (T.f 1)) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ κ' : D → (Fin d → ℤ))
    (hκ : κ ∈ decSet M L γ δ w Adm c β k0) (hκ' : κ' ∈ decSet M L γ δ w Adm c β k0) :
    triC L w (T.triZ κ) 1 + triC L w (T.triZ κ) 0 = triC L w (T.triZ κ') 1 + triC L w (T.triZ κ') 0 ∧
      |(triG L w (T.triZ κ) 1 + triG L w (T.triZ κ) 0) - (triG L w (T.triZ κ') 1 + triG L w (T.triZ κ') 0)| ≤
        2 * (M.atoms.card * (δ⁻¹ * L ^ (-2 * γ))) := by
  have := T.rel1_base hβ L γ δ hL hδ w Adm c β k0 κ κ' hκ hκ'
  rw [hi] at this
  have eC : ∀ z : Fin 3 → (Fin d → ℤ), ∑ j ∈ ({0, 1} : Finset (Fin 3)), triC L w z j = triC L w z 1 + triC L w z 0 := by
    intro z; rw [Finset.sum_pair (by decide)]; abel
  have eG : ∀ z : Fin 3 → (Fin d → ℤ), ∑ j ∈ ({0, 1} : Finset (Fin 3)), triG L w z j = triG L w z 1 + triG L w z 0 := by
    intro z; rw [Finset.sum_pair (by decide)]; ring
  rw [eC, eC, eG, eG] at this
  exact this

/-- Relation from the second `β`-cut: either the second gap alone is fixed, or the sum of the first two. -/
theorem rel1 (hβ : ¬ T.m2.SameComponent (T.t 1) (T.f 1)) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ κ' : D → (Fin d → ℤ))
    (hκ : κ ∈ decSet M L γ δ w Adm c β k0) (hκ' : κ' ∈ decSet M L γ δ w Adm c β k0) :
    (triC L w (T.triZ κ) 1 = triC L w (T.triZ κ') 1 ∧
      |triG L w (T.triZ κ) 1 - triG L w (T.triZ κ') 1| ≤ 2 * (M.atoms.card * (δ⁻¹ * L ^ (-2 * γ)))) ∨
    (triC L w (T.triZ κ) 1 + triC L w (T.triZ κ) 0 = triC L w (T.triZ κ') 1 + triC L w (T.triZ κ') 0 ∧
      |(triG L w (T.triZ κ) 1 + triG L w (T.triZ κ) 0) - (triG L w (T.triZ κ') 1 + triG L w (T.triZ κ') 0)| ≤
        2 * (M.atoms.card * (δ⁻¹ * L ^ (-2 * γ)))) := by
  rcases T.idx_S1_cases with hi | hi
  · exact Or.inl (T.rel1a hi hβ L γ δ hL hδ w Adm c β k0 κ κ' hκ hκ')
  · exact Or.inr (T.rel1b hi hβ L γ δ hL hδ w Adm c β k0 κ κ' hκ hκ')

end TriData
end WaveTurbulence.FinalCount
