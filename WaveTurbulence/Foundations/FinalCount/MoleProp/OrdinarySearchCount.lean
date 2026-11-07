/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103SearchProgress
public import WaveTurbulence.Foundations.FinalCount.MoleProp.InducedAdmissibility
public import WaveTurbulence.Foundations.FinalCount.MoleProp.BridgeCoreNormalization
public import WaveTurbulence.Foundations.FinalCount.MoleProp.ThreeLabelNormalization
import Mathlib.Tactic

/-! # Actual neutral ordinary search steps

R, removal of every old bridge, and selection of the actual remaining
component preserve the required upper bound. Admissibility always records
an original completion, with its original large-gap constraints.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def ordinaryDescendant (M : Molecule V D) (v a : V) :=
  Mole.induced (bridgeCore (Degen.eraseAtoms M {v}))
    (Degen.componentSet (bridgeCore (Degen.eraseAtoms M {v})) a)

def ordinaryDescendantAdmissibility (M : Molecule V D) (v a : V) {d : ℕ}
    (Adm : (D → (Fin d → ℤ)) → Prop) :=
  inducedFreeAdmissibility (bridgeCore (Degen.eraseAtoms M {v}))
    (Degen.componentSet (bridgeCore (Degen.eraseAtoms M {v})) a)
    (bridgeCoreAdmissibility (Degen.eraseAtoms M {v}) (erasedFreeAdmissibility M {v} Adm))

theorem ordinaryDescendantAdmissibility_largeGap (M : Molecule V D) (v a : V)
    {d : ℕ} (L γ η : ℝ) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) :
    ∀ κ, ordinaryDescendantAdmissibility M v a Adm κ →
      LargeGap (ordinaryDescendant M v a) L γ η (0 : Mom d) κ := by
  apply inducedFreeAdmissibility_largeGap
  apply bridgeCoreAdmissibility_largeGap
  exact projected_largeGap M L γ η (0 : Mom d) {v} Adm hAdm

theorem countAFree_le_ordinaryDescendant (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), SearchInput M → ∀ v ∈ M.atoms, M.deg v=3 → ∀ a : V,
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (ordinaryDescendant M v a) L γ δ C1 (0 : Mom d)
          (ordinaryDescendantAdmissibility M v a Adm) P := by
  obtain ⟨C₁,R₁,hC₁,hB₁⟩ := countAFree_erase_three_two_circuits d hd γ hγ
  obtain ⟨C₂,hC₂,hB₂⟩ := countAFree_le_induced_component d hd γ hγ η hη hηmax
  refine ⟨max C₁ C₂,hC₁.trans (le_max_left _ _),?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R₂,hR₂⟩ := hB₂ C1 ((le_max_right _ _).trans hC1) δ hδ
  refine ⟨max (max R₁ R₂) 1,?_⟩
  intro L hL hlog V D _ _ _ M hI v hv hv3 a Adm P hAdm
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hLR₁ : R₁ ≤ L := (le_max_left R₁ R₂).trans ((le_max_left _ _).trans hL)
  have hLR₂ : R₂ ≤ L := (le_max_right R₁ R₂).trans ((le_max_left _ _).trans hL)
  have hs := simple_eraseAtoms M {v} hI.simple
  have hAdm' := projected_largeGap M L γ η (0 : Mom d) {v} Adm hAdm
  have hR := hB₁ C1 ((le_max_left _ _).trans hC1) L hLR₁ hlog δ hδ M hI.molecule v hv hv3
    (no_operation_b_of_simple M hI.simple)
    (circuitRank_erase_three_of_bridgeless M hI.loopless hI.bridgeless hv hv3) Adm P
    (by rw [ladderCells_eq_empty_of_simple M hI.simple]; simp)
  have hB := countAFree_le_bridgeCore (Degen.eraseAtoms M {v}) hs hLp.ne' γ δ C1 (0 : Mom d)
    (erasedFreeAdmissibility M {v} Adm) P
  have hS := hR₂ L hLR₂ hlog (bridgeCore (Degen.eraseAtoms M {v}))
    (bridgeCore_isMolecule _ (Degen.isMolecule_eraseAtoms M hI.molecule {v}))
    (simple_bridgeCore _ hs) a _ P
    (bridgeCoreAdmissibility_largeGap _ L γ η (0 : Mom d) _ hAdm')
  exact hR.trans (hB.trans hS)

end WaveTurbulence.MoleProp
