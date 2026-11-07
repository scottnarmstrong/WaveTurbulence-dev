/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.SevenLabelDeletion
public import WaveTurbulence.Foundations.FinalCount.MoleProp.GoodNormalization
import Mathlib.Tactic

/-! # Normalized actual post-removal beta counting branch -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem seven_label_normalized_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, 1 ≤ Real.log L → ∀ C1 ≥ (1 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
    ∀ x y z r s t u : D, x ≠ y → x ≠ z → y ≠ z → x ≠ r → x ≠ s →
      r ≠ s → r ≠ t → s ≠ t → u ∉ ({r,s,t} : Finset D) →
      M.dartsAt a = {x,y,z} → M.dartsAt b = {r,s,t,u} →
      M.out r = false → M.out s = true → M.out t = false → M.out u = true →
    ∀ U : Finset V, U ⊆ M.atoms →
      Degen.boundaryDarts M U = {M.mate x,M.mate r,M.mate s} →
    (M.circuitRank-(Degen.eraseAtoms M {a,b}).circuitRank = 4) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        ENNReal.ofReal (C*((U.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-(min γ (1-γ)+η))) *
          countAFree (Degen.eraseAtoms M {a,b}) L γ δ C1 (0 : Mom d)
            (erasedFreeAdmissibility M {a,b} Adm) P := by
  classical
  obtain ⟨C,R,hC,hB⟩ := seven_label_deletion_count_bound d hd γ hγ η hη hηmax
  refine ⟨C+1,max R 1,by linarith only [hC],?_⟩
  intro L hL hlog C1 hC1 δ hδ V D _ _ _ M hM hsimp a ha b hb x y z r s t u hxy hxz hyz hxr hxs hrs hrt hst hu hA hStarB hro hso hto huo U hU hcut hχ Adm P hAdm
  have hL1 : 1 ≤ L := (le_max_right R 1).trans hL
  have hLR : R ≤ L := (le_max_left R 1).trans hL
  have hg : min γ (1-γ)+η ≤ ((d : ℝ)-γ)*4 := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hm := min_le_left γ (1-γ)
    linarith only [hdR,hm,hγ.2,hηmax]
  have hc := hB L hLR δ hδ M hM a ha b hb x y z r s t u hxy hxz hyz hxr hxs hrs hrt hst hu hA hStarB hro hso hto huo U hU hcut Adm hAdm
  have hc' : countEFree M L γ δ (0 : Mom d) Adm ≤
      (⌈C*((U.card : ℝ)+1)^2*(δ⁻¹)^3*L^(((d : ℝ)-γ)*(4 : ℕ)-(min γ (1-γ)+η))⌉₊ : ℕ∞)*
        countEFree (Degen.eraseAtoms M {a,b}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) := by
    have he : ((d : ℝ)-γ)*(4 : ℕ)-(min γ (1-γ)+η)=4*((d : ℝ)-γ)-min γ (1-γ)-η := by push_cast; ring
    rw [he]
    exact hc
  exact good_normalization_of_count_bound M (Degen.eraseAtoms M {a,b})
    hL1 hlog hδ hC1 hC (le_add_of_nonneg_left (Nat.cast_nonneg _))
    (le_refl (3 : ℕ)) hg hsimp (simple_eraseAtoms M {a,b} hsimp)
    hχ Adm (erasedFreeAdmissibility M {a,b} Adm) P hc'

end WaveTurbulence.MoleProp
