/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamIncidence
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! # Translation transport through a symmetric insertion cap

Uniform translation of a balanced four-valent atom preserves its resonance
because its momentum divergence and signed degree both vanish. Joint
resonances change by the explicit linear gap term. These are exact identities.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- Exact translation law for any finite signed collection of momenta. -/
theorem signed_energy_translate {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : ι → ℝ) (k : ι → E) (t : E) :
    (∑ i,s i*‖k i+t‖^2)=(∑ i,s i*‖k i‖^2)+
      2*inner ℝ (∑ i,s i • k i) t+(∑ i,s i)*‖t‖^2 := by
  simp only [norm_add_sq_real,mul_add,sum_add_distrib,sum_inner,real_inner_smul_left]
  rw [Finset.sum_mul,Finset.mul_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Balanced source momentum and signed degree make the translation invariant. -/
theorem signed_energy_translate_of_zero {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : ι → ℝ) (k : ι → E) (t : E)
    (hflow : ∑ i,s i • k i=0) (hbal : ∑ i,s i=0) :
    (∑ i,s i*‖k i+t‖^2)=∑ i,s i*‖k i‖^2 := by
  rw [signed_energy_translate,hflow,hbal,inner_zero_left,mul_zero,zero_mul,add_zero,add_zero]

/-- Joint translation has precisely the linear gap correction. -/
theorem joint_energy_translate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b t : E) : ‖a+t‖^2-‖b+t‖^2=‖a‖^2-‖b‖^2+2*inner ℝ (a-b) t := by
  simp only [norm_add_sq_real,inner_sub_left]
  ring

/-- The actual four-incidence source resonance is translation invariant. -/
theorem four_energy_translate {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (hM : M.IsMolecule) {v : V} {ns : Fin 4 → V}
    (F : FourIncidences M v ns) {d : ℕ} (L : ℝ) (w : Mom d)
    (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ z ∈ M.atoms,M.deg z=4 → c z=0)
    (t : Mom d) :
    (∑ i : Fin 4,M.dartSign (F.dart i)*‖Molecule.kvec L w κ (F.dart i)+t‖^2)=M.Gamma L w κ v := by
  rw [signed_energy_translate_of_zero _ _ t (four_momentum M hM F L w c κ hκ hc)
    (four_signs_sum M hM F)]
  exact (four_gamma M hM F L w κ).symm

end WaveTurbulence.Vine.Param
