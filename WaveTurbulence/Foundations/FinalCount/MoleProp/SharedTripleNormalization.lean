/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.ActualSharedTripleDeletion
public import WaveTurbulence.Foundations.FinalCount.MoleProp.GoodNormalization
import Mathlib.Tactic

/-! # Normalized actual adjacent-star counting bound -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem actual_shared_triples_normalized_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, 1 ≤ Real.log L → ∀ C1 ≥ (1 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
    ∀ x y r s t : D, x ≠ y → x ≠ r → y ≠ r →
      M.mate x ≠ s → M.mate x ≠ t → s ≠ t →
      M.dartsAt a = {x,y,r} → M.dartsAt b = {M.mate x,s,t} →
    (M.circuitRank-(Degen.eraseAtoms M {a,b}).circuitRank = 3) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        ENNReal.ofReal (C*(δ⁻¹)^3*L^(-min γ (1-γ))) *
          countAFree (Degen.eraseAtoms M {a,b}) L γ δ C1 (0 : Mom d)
            (erasedFreeAdmissibility M {a,b} Adm) P := by
  classical
  obtain ⟨C,R,hC,hB⟩ := actual_shared_triples_deletion_count_bound d hd γ hγ
  refine ⟨C+1,max R 1,by linarith only [hC],?_⟩
  intro L hL hlog C1 hC1 δ hδ V D _ _ _ M hM hsimp a ha b hb x y r s t hxy hxr hyr hxs hxt hst hA hStarB hχ Adm P
  have hL1 : 1 ≤ L := (le_max_right R 1).trans hL
  have hLR : R ≤ L := (le_max_left R 1).trans hL
  have hg : min γ (1-γ) ≤ ((d : ℝ)-γ)*3 := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hm := min_le_left γ (1-γ)
    linarith only [hdR,hm,hγ.2]
  have hc := hB L hLR δ hδ M hM a ha b hb x y r s t hxy hxr hyr hxs hxt hst hA hStarB Adm
  have hc' : countEFree M L γ δ (0 : Mom d) Adm ≤
      (⌈C*1^2*(δ⁻¹)^2*L^(((d : ℝ)-γ)*(3 : ℕ)-min γ (1-γ))⌉₊ : ℕ∞)*
        countEFree (Degen.eraseAtoms M {a,b}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) := by
    simpa only [one_pow,mul_one,Nat.cast_ofNat,mul_comm ((d : ℝ)-γ) 3] using hc
  have hh := good_normalization_of_count_bound M (Degen.eraseAtoms M {a,b})
    hL1 hlog hδ hC1 hC.le (le_refl (1 : ℝ)) (by decide : (2 : ℕ) ≤ 3) hg
    hsimp (simple_eraseAtoms M {a,b} hsimp) hχ Adm (erasedFreeAdmissibility M {a,b} Adm) P hc'
  simpa only [one_pow,mul_one] using hh

end WaveTurbulence.MoleProp
