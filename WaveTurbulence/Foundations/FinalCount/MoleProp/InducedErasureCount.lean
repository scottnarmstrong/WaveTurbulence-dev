/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.InducedClosedCount
import Mathlib.Tactic

/-! # Identifying an induced surviving side with the original induced graph -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def inducedErasureDartEquiv (M : Molecule V D) (Y S : Finset V)
    (hS : S ⊆ M.atoms \ Y) :
    {x : Degen.RetainedDart M Y // (Degen.eraseAtoms M Y).InGroup S x} ≃
      {x : D // M.InGroup S x} where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,⟨(mem_sdiff.mp (hS x.property.1)).2,
    (mem_sdiff.mp (hS x.property.2)).2⟩⟩,x.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem countAFree_induced_erasure_le_original (M : Molecule V D) (Y S : Finset V)
    (hS : S ⊆ M.atoms \ Y) {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    countAFree (Mole.induced (Degen.eraseAtoms M Y) S) L γ δ C1 w
      (inducedFreeAdmissibility (Degen.eraseAtoms M Y) S (erasedFreeAdmissibility M Y Adm)) P ≤
    countAFree (Mole.induced M S) L γ δ C1 w (inducedFreeAdmissibility M S Adm) P := by
  apply countAFree_le_of_dart_equiv _ _ (inducedErasureDartEquiv M Y S hS)
  · rfl
  · intro x; rfl
  · intro x; exact Subtype.ext rfl
  · intro x; rfl
  · intro κ hκ
    obtain ⟨κpost,hpost,_hb,rfl⟩ := hκ
    obtain ⟨κold,hAdm,hb,rfl⟩ := hpost
    exact ⟨κold,hAdm,hb,by funext x; rfl⟩

end WaveTurbulence.MoleProp
