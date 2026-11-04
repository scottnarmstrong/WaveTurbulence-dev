/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.EnergyTracePartition

/-! # Literal surviving coordinates after an energy block trace -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset ClassJR

/-- The surviving NT pairs, independently of which coordinates are special. -/
def survivingEnergyEquiv {n : ℕ} (T : Finset (Fin n)) :
    {j : Fin n // j ∉ T} ≃ Fin (Fintype.card {j : Fin n // j ∉ T}) :=
  Fintype.equivFin _

/-- Keep precisely the original special factors among the surviving pairs. -/
def survivingSpecial {n : ℕ} (T J : Finset (Fin n)) :
    Finset (Fin (Fintype.card {j : Fin n // j ∉ T})) :=
  univ.filter (fun i => ((survivingEnergyEquiv T).symm i).val ∈ J)

/-- Active surviving variables are exactly the untraced original variables
outside the special set, with no extra coordinate or Jacobian. -/
def survivingActiveEquiv {n : ℕ} (T J : Finset (Fin n)) :
    {i : Fin (Fintype.card {j : Fin n // j ∉ T}) // i ∉ survivingSpecial T J} ≃
      {j : Fin n // j ∉ T ∧ j ∉ J} where
  toFun i := ⟨((survivingEnergyEquiv T).symm i.val).val,
    ((survivingEnergyEquiv T).symm i.val).property, by
      simpa only [survivingSpecial,mem_filter,mem_univ,true_and] using i.property⟩
  invFun j := ⟨survivingEnergyEquiv T ⟨j.val,j.property.1⟩,by
    simpa only [survivingSpecial,mem_filter,mem_univ,true_and,Equiv.symm_apply_apply] using j.property.2⟩
  left_inv i := Subtype.ext (Equiv.apply_symm_apply _ _)
  right_inv j := by
    apply Subtype.ext
    change ((survivingEnergyEquiv T).symm ((survivingEnergyEquiv T) ⟨j.val,j.property.1⟩)).val = j.val
    rw [Equiv.symm_apply_apply]

/-- The actual traced coefficient in the exact finite NT enumeration. -/
def survivingTraceCoefficient {n : ℕ} (T J : Finset (Fin n)) (h : Disjoint T J)
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) :
    ({i : Fin (Fintype.card {j : Fin n // j ∉ T}) // i ∉ survivingSpecial T J} → ℝ) →
      ℝ × ℝ → ℂ :=
  fun β lam => energyTraceCoefficient T J h C
    (fun j => β ((survivingActiveEquiv T J).symm j)) lam

/-- The surviving coefficient inherits the exact source regularity. -/
theorem symReg_survivingTraceCoefficient {n : ℕ} (T J : Finset (Fin n)) (h : Disjoint T J)
    {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) :
    SymReg (survivingTraceCoefficient T J h C) :=
  (symReg_energyTraceCoefficient T J h hC).reindex (survivingActiveEquiv T J).symm

end WaveTurbulence.RegAsymp
