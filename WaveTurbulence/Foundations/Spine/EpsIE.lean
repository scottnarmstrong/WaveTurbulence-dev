/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ChartAff
public import WaveTurbulence.Foundations.Spine.GardenPos
/-! # Inclusion-exclusion for epsilon, and slot-difference forms (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Finset

variable {n d : ℕ}

/-- `ε_{n₁n₂n₃} = 1 - 1[n₂ = n₁] - 1[n₂ = n₃]`. -/
theorem epsCoef_eq_sub (n₁ n₂ n₃ : Fin d → ℤ) :
    epsCoef n₁ n₂ n₃ = 1 - (if n₂ = n₁ then 1 else 0) - (if n₂ = n₃ then 1 else 0) := by
  unfold epsCoef
  split_ifs <;> simp_all <;> norm_num

/-- Differences of two slot labels of an anchored atom are differences of `tau`. -/
lemma uSlot_sub (S : ChainSigns n) (L : ChainLab n (Fin d → ℤ)) (h : S.IsSol L) (i : Fin n)
    (s s' : Fin 4) :
    L.uSlot i s - L.uSlot i s' = tauHom S i s' (S.pairs L i) - tauHom S i s (S.pairs L i) := by
  rw [S.uSlot_eq L h i s, S.uSlot_eq L h i s']
  simp only [tau_eq_tauHom] at *
  abel

/-- The six slot-difference forms: the offsets are `(0, x+y, x, y)`. -/
lemma tvec_sub_forms (x y : Fin d → ℤ) (j j' : Fin 4) :
    tvec x y j - tvec x y j' ∈ ({0, x, -x, y, -y, x + y, -(x + y), x - y, y - x} :
      Set (Fin d → ℤ)) := by
  fin_cases j <;> fin_cases j' <;> simp [tvec]

/-- The sign of the slot `σ j` is `+1` for `j < 2` and `-1` otherwise. -/
lemma sg_sigma (S : ChainSigns n) (i : Fin n) (j : Fin 4) :
    S.sg i (S.σ i j) = if j.1 < 2 then 1 else -1 := by
  obtain ⟨h0, h1⟩ := S.plus i
  obtain ⟨h2, h3⟩ := S.minus i
  fin_cases j <;> simp [h0, h1, h2, h3]

/-- Slots of opposite sign differ by `±x` or `±y`: the gap forms are axis forms. -/
lemma tvec_sub_axis (S : ChainSigns n) (i : Fin n) (k k' : Fin 4) (h : S.sg i k ≠ S.sg i k')
    (x y : Fin d → ℤ) :
    tvec x y ((S.σ i).symm k) - tvec x y ((S.σ i).symm k') ∈
      ({x, -x, y, -y} : Set (Fin d → ℤ)) := by
  have hk := sg_sigma S i ((S.σ i).symm k)
  have hk' := sg_sigma S i ((S.σ i).symm k')
  rw [Equiv.apply_symm_apply] at hk hk'
  rw [hk, hk'] at h
  generalize (S.σ i).symm k = j at h ⊢
  generalize (S.σ i).symm k' = j' at h ⊢
  fin_cases j <;> fin_cases j' <;> simp_all [tvec]

end WaveTurbulence.LadderDecay
