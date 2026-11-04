/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PhaseCharacterForm

/-!
# The lattice-dependent source phase after removing the zero-input phase

The time parameters and the affine zeta2*r and xi3*r terms cancel
exactly. The remaining real exponent is the sum of independent linear,
bilinear and normal quadratic factors. No coefficient restriction is
needed for this algebraic identity.
-/

public section

open Finset

namespace WaveTurbulence.Sumint

/-- The zero integer input gives the zero momentum at every scale. -/
theorem latticePoint_zero_input {d : ℕ} (L : ℝ) : latticePoint L (0 : Fin d → ℤ) = 0 := by
  ext j
  simp [latticePoint]

/-- The spatial real exponent of the distinguished linear input. -/
@[expose] noncomputable def linearSpatialExponent {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) (i : Fin D.S.I) : ℝ :=
  δ*L^(2*γ)*(τ (.inl ⟨i,0⟩)-t)*inner ℝ r (latticePoint L (x (D.S.x0Slot i)))

/-- The spatial real exponent of one x/y pair, retaining both unrestricted linear modulations. -/
@[expose] noncomputable def pairSpatialExponent {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ)
    (p : Σ i : Fin D.S.I, Fin (D.S.m i)) : ℝ :=
  let c := δ*L^(2*γ)
  let X := latticePoint L (x (D.S.xSlot p.1 p.2))
  let Y := latticePoint L (x (D.S.ySlot p.1 p.2))
  c*(τ (.inl ⟨p.1,p.2.succ⟩)-τ (.inr (.inl p)))*inner ℝ X Y +
  c*(τ (.inl ⟨p.1,p.2.succ⟩)-t)*
    ((D.ζc p.1 p.2 0 : ℝ)*inner ℝ r X+(D.ζc p.1 p.2 1 : ℝ)*inner ℝ r Y)

/-- The spatial real exponent of the normal cubic input triple. -/
@[expose] noncomputable def normalSpatialExponent {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) : ℝ :=
  let c := δ*L^(2*γ)
  let u := fun j : Fin 3 => latticePoint L (x (D.S.uSlot i.1 i.2 j))
  let τ' := fun j : Fin 3 => τ (.inr (.inr ⟨i,j⟩))
  c*(τ' 0-τ' 2)*inner ℝ (u 0) (u 1) +
  c*(τ' 1-τ' 2)*(if D.Λsel i.1 then inner ℝ (u 0) (u 2) else inner ℝ (u 2) (u 0+u 1-u 2)) +
  c*(τ' 2-t)*((D.ξc i.1 0 : ℝ)*inner ℝ r (u 0)+(D.ξc i.1 1 : ℝ)*inner ℝ r (u 1)+
    (D.ξc i.1 2 : ℝ)*inner ℝ r (u 2))

/-- The complete lattice-dependent real source exponent. -/
@[expose] noncomputable def spatialPhaseExponent {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) : ℝ :=
  (∑ i, linearSpatialExponent D L γ δ x r t τ i) +
    (∑ p, pairSpatialExponent D L γ δ x r t τ p) +
    ∑ i, normalSpatialExponent D L γ δ x r t τ i

/-- Separate the lattice-independent affine pair term inside a real inner product. -/
theorem inner_affine_pair_split {d : ℕ} (r X Y : Mom d) (a b c : ℝ) :
    inner ℝ r (a • X+b • Y+c • r) = inner ℝ r (c • r)+(a*inner ℝ r X+b*inner ℝ r Y) := by
  simp only [inner_add_right,real_inner_smul_right]
  ring

/-- Separate the lattice-independent affine normal term inside a real inner product. -/
theorem inner_affine_triple_split {d : ℕ} (r X Y Z : Mom d) (a b c e : ℝ) :
    inner ℝ r (a • X+b • Y+c • Z+e • r) =
      inner ℝ r (e • r)+(a*inner ℝ r X+b*inner ℝ r Y+c*inner ℝ r Z) := by
  simp only [inner_add_right,real_inner_smul_right]
  ring

/-- All first-block time-only terms cancel in the zero-input subtraction. -/
theorem firstPhaseExponent_sub_zero {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) (i : Fin D.S.I) :
    firstPhaseExponent D L γ δ x r t τ i-firstPhaseExponent D L γ δ (fun _ => 0) r t τ i =
      linearSpatialExponent D L γ δ x r t τ i +
        ∑ j : Fin (D.S.m i), pairSpatialExponent D L γ δ x r t τ ⟨i,j⟩ := by
  unfold firstPhaseExponent linearSpatialExponent pairSpatialExponent
  simp only [latticePoint_zero_input,inner_zero_right,smul_zero,zero_add,add_zero,
    mul_zero,Finset.sum_const_zero]
  simp_rw [inner_affine_pair_split,mul_add,Finset.sum_add_distrib]
  ring

/-- All normal-block time-only terms cancel in the zero-input subtraction. -/
theorem normalPhaseExponent_sub_zero {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) :
    normalPhaseExponent D L γ δ x r t τ i-normalPhaseExponent D L γ δ (fun _ => 0) r t τ i =
      normalSpatialExponent D L γ δ x r t τ i := by
  unfold normalPhaseExponent normalSpatialExponent
  simp only [latticePoint_zero_input,inner_zero_right,smul_zero,zero_add,add_zero,sub_zero,
    ite_self,mul_zero]
  simp_rw [inner_affine_triple_split,mul_add]
  ring

/-- The exact full zero-input subtraction is the independent spatial exponent. -/
theorem fullPhaseExponent_sub_zero {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    fullPhaseExponent D L γ δ x r t τ-fullPhaseExponent D L γ δ (fun _ => 0) r t τ =
      spatialPhaseExponent D L γ δ x r t τ := by
  unfold fullPhaseExponent spatialPhaseExponent
  rw [show ((∑ i, firstPhaseExponent D L γ δ x r t τ i)+
      ∑ i, normalPhaseExponent D L γ δ x r t τ i) -
      ((∑ i, firstPhaseExponent D L γ δ (fun _ => 0) r t τ i)+
        ∑ i, normalPhaseExponent D L γ δ (fun _ => 0) r t τ i) =
      (∑ i, (firstPhaseExponent D L γ δ x r t τ i-firstPhaseExponent D L γ δ (fun _ => 0) r t τ i)) +
        ∑ i, (normalPhaseExponent D L γ δ x r t τ i-normalPhaseExponent D L γ δ (fun _ => 0) r t τ i) by
          rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]; ring]
  simp_rw [firstPhaseExponent_sub_zero,normalPhaseExponent_sub_zero]
  rw [Finset.sum_add_distrib,Fintype.sum_sigma]

/-- The actual source phase separates by multiplication, even where the case-(c) factor vanishes. -/
theorem phase_eq_zero_mul_spatialCharacter {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    D.phase L γ δ η x r t τ = D.phase L γ δ η (fun _ => 0) r t τ *
      piCharacter (spatialPhaseExponent D L γ δ x r t τ) := by
  rw [phase_eq_zero_mul_exponent_difference,fullPhaseExponent_sub_zero]

end WaveTurbulence.Sumint
