/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.InducedClosedCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.BridgeNormalization
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaBridge
import Mathlib.Tactic

/-! # Actual bridge-side selection in initial-profile preprocessing -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def inducedBridgeDartEquiv (M : Molecule V D) (e : D) (he : Degen.IsBridge M e) :
    {x : WithoutBondDart M e // (eraseBond M e).InGroup (bridgeSide M e) x} ≃
      {x : D // M.InGroup (bridgeSide M e) x} where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,by
    classical
    have hout : M.atom (M.mate e) ∉ bridgeSide M e := fun h => he (mem_filter.mp h).2
    constructor
    · intro hx
      exact hout (by simpa only [hx] using x.property.2)
    · intro hx
      exact hout (by simpa only [hx] using x.property.1)⟩,x.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem countAFree_induced_bridge_le_original (M : Molecule V D) (e : D)
    (he : Degen.IsBridge M e) {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    countAFree (Mole.induced (eraseBond M e) (bridgeSide M e)) L γ δ C1 w
      (inducedFreeAdmissibility (eraseBond M e) (bridgeSide M e) (erasedBondAdmissibility M e Adm)) P ≤
    countAFree (Mole.induced M (bridgeSide M e)) L γ δ C1 w
      (inducedFreeAdmissibility M (bridgeSide M e) Adm) P := by
  apply countAFree_le_of_dart_equiv _ _ (inducedBridgeDartEquiv M e he)
  · rfl
  · intro x; rfl
  · intro x; exact Subtype.ext rfl
  · intro x; rfl
  · intro κ hκ
    obtain ⟨κpost,hpost,_hb,rfl⟩ := hκ
    obtain ⟨κold,hAdm,hb,rfl⟩ := hpost
    exact ⟨κold,hAdm,hb,by funext x; rfl⟩

theorem countAFree_le_bridgeSide (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) →
    ∀ (e : D), Degen.IsBridge M e →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Mole.induced M (bridgeSide M e)) L γ δ C1 (0 : Mom d)
          (inducedFreeAdmissibility M (bridgeSide M e) Adm) P := by
  classical
  obtain ⟨C,hC,hB⟩ := countAFree_le_induced_closed d hd γ hγ η hη hηmax
  refine ⟨C,hC,?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R,hR⟩ := hB C1 hC1 δ hδ
  refine ⟨max R 1,?_⟩
  intro L hL hlog V D _ _ _ M hM hsimp e he Adm P hAdm
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right _ _).trans hL)
  have hclose : ∀ a ∈ bridgeSide M e, ∀ b, (eraseBond M e).SameComponent a b → b ∈ bridgeSide M e := by
    intro a ha b hab
    obtain ⟨haM,haPath⟩ := mem_filter.mp ha
    have hab' := (eraseBond_sameComponent_iff M e a b).mp hab
    exact mem_filter.mpr ⟨(Mole.sameComponent_mem_iff (eraseBond M e) hab).mp haM,
      Relation.EqvGen.trans _ _ _ haPath hab'⟩
  have hB0 := countAFree_le_erase_bridge M e he hsimp hLp.ne' γ δ C1 (0 : Mom d) Adm P
  have hS := hR L ((le_max_left _ _).trans hL) hlog (eraseBond M e)
    (eraseBond_isMolecule M hM e) (simple_eraseBond M e hsimp)
    (bridgeSide M e) (bridgeSide_subset M e) hclose _ P
    (erasedBondAdmissibility_largeGap M e L γ η (0 : Mom d) Adm hAdm)
  exact hB0.trans (hS.trans (countAFree_induced_bridge_le_original M e he L γ δ C1 (0 : Mom d) Adm P))

end WaveTurbulence.MoleProp
