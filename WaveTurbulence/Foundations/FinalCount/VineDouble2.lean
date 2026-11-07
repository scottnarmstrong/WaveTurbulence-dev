/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineDouble1
/-! The label count of a VC formed by two double bonds, part 2: conservation and energy at the middle atom `x`:
`k_{x₁} - k_{x₂} + k_{y₁} - k_{y₂} = 0` and `Γ_x = 2⟨r, (k_{x₁} - k_{y₁}) - r⟩`, `r = k_{x₁} - k_{x₂}`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem inner_identity (a b c : Mom d) :
    ‖a‖ ^ 2 - ‖b‖ ^ 2 + ‖c‖ ^ 2 - ‖c + (a - b)‖ ^ 2 = 2 * inner ℝ (a - b) (a - c - (a - b)) := by
  have h1 := real_inner_self_eq_norm_sq a
  have h2 := real_inner_self_eq_norm_sq b
  have h3 := real_inner_self_eq_norm_sq c
  have h4 := real_inner_self_eq_norm_sq (c + (a - b))
  rw [← h1, ← h2, ← h3, ← h4]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  have c1 := real_inner_comm a b
  have c2 := real_inner_comm a c
  have c3 := real_inner_comm b c
  linear_combination c1 - c2 + c3

namespace DoubleShape
variable {M : Molecule V D} {K : VineCut M} (S : DoubleShape K)
variable {L γ δ : ℝ} {w : Mom d} {Adm : (D → (Fin d → ℤ)) → Prop} {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d}
  {κ : D → (Fin d → ℤ)}
include S

theorem kvec_mate (hκ : κ ∈ decSet M L γ δ w Adm c β k0) (z : D) :
    Molecule.kvec L w κ (M.mate z) = Molecule.kvec L w κ z := by
  unfold Molecule.kvec; rw [hκ.1.1 z]

theorem cons (hP : ParamOK M c k0) (hκ : κ ∈ decSet M L γ δ w Adm c β k0) :
    Molecule.kvec L w κ K.x₁ - Molecule.kvec L w κ K.x₂ + Molecule.kvec L w κ K.y₁ -
      Molecule.kvec L w κ K.y₂ = 0 := by
  have h := hκ.1.2 S.x S.x_mem
  rw [S.sum_x, sign_m₁ (K := K), sign_m₂ (K := K), sign_m₃ (K := K), sign_m₄ (K := K), S.kvec_mate hκ, S.kvec_mate hκ, S.kvec_mate hκ,
    S.kvec_mate hκ, hP.1 S.x S.x_mem S.deg_x] at h
  rw [← h]
  simp only [one_smul, neg_smul]
  abel

theorem lat_cons (hP : ParamOK M c k0) (hL : 0 < L) (hκ : κ ∈ decSet M L γ δ w Adm c β k0) :
    κ K.y₂ = κ K.y₁ + κ K.x₁ - κ K.x₂ := by
  have h := S.cons hP hκ
  funext i
  have hi := congrArg (fun v : Mom d => v i) h
  simp only [Molecule.kvec, latticePoint] at hi
  simp at hi
  have hL' : L ≠ 0 := hL.ne'
  have : ((κ K.x₁ i : ℝ) - κ K.x₂ i + κ K.y₁ i - κ K.y₂ i) = 0 := by
    field_simp at hi
    linarith
  have : (κ K.x₁ i - κ K.x₂ i + κ K.y₁ i - κ K.y₂ i : ℤ) = 0 := by exact_mod_cast this
  simp only [Pi.add_apply, Pi.sub_apply]
  omega

theorem gamma_x (hP : ParamOK M c k0) (hκ : κ ∈ decSet M L γ δ w Adm c β k0) :
    M.Gamma L w κ S.x =
      2 * inner ℝ (Molecule.gapAt L w κ K.x₁ K.x₂)
        (Molecule.kvec L w κ K.x₁ - Molecule.kvec L w κ K.y₁ - Molecule.gapAt L w κ K.x₁ K.x₂) := by
  have hcons := S.cons hP hκ
  have he : Molecule.kvec L w κ K.y₂ = Molecule.kvec L w κ K.y₁ +
      (Molecule.kvec L w κ K.x₁ - Molecule.kvec L w κ K.x₂) := by
    have : Molecule.kvec L w κ K.y₂ = Molecule.kvec L w κ K.x₁ - Molecule.kvec L w κ K.x₂ +
        Molecule.kvec L w κ K.y₁ := by
      exact (sub_eq_zero.mp hcons).symm
    rw [this]; abel
  unfold Molecule.Gamma
  rw [S.sum_x, sign_m₁ (K := K), sign_m₂ (K := K), sign_m₃ (K := K), sign_m₄ (K := K), S.kvec_mate hκ, S.kvec_mate hκ, S.kvec_mate hκ,
    S.kvec_mate hκ, he]
  have := inner_identity (Molecule.kvec L w κ K.x₁) (Molecule.kvec L w κ K.x₂) (Molecule.kvec L w κ K.y₁)
  unfold Molecule.gapAt
  linarith

end DoubleShape
end WaveTurbulence.FinalCount
