/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineLocalDartErasure
public import WaveTurbulence.Foundations.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.Molecule.VineHyperAdjointVC
import Mathlib.Tactic

/-! # Local dart identifications preserve designated hyper-adjoint objects -/

public section
namespace WaveTurbulence.Vine
variable {V D E : Type*} [DecidableEq V] [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E]
    {M : Molecule V D} {N : Molecule V E} {A : Finset V}
namespace LocalDartEmbedding
variable (F : LocalDartEmbedding M N A)

include F in
/-- The existential HV/HVC classification is preserved by identifying all
actual internal darts. Matched designated bond deletions are transported
before applying the exact VC equivalence. -/
theorem hyperLike_iff (a b : V) :
    (IsHV N A a b ∨ IsHVC N A a b) ↔ (IsHV M A a b ∨ IsHVC M A a b) := by
  constructor
  · intro hN
    obtain ⟨f,hf,hVC⟩ := hyperLike_iff_adjoint_VC.mp hN
    apply hyperLike_iff_adjoint_VC.mpr
    exact ⟨F.toFun f,(F.ends_eq f).trans hf,((F.eraseBond f).isVC_iff A (Finset.Subset.refl _) a b).mp hVC⟩
  · intro hM
    obtain ⟨f,hf,hVC⟩ := hyperLike_iff_adjoint_VC.mp hM
    have hfi : M.InGroup A f := by
      rcases Sym2.eq_iff.mp hf with hh | hh
      · exact ⟨hh.1.symm ▸ hVC.1.2.1,hh.2.symm ▸ hVC.1.2.2.1⟩
      · exact ⟨hh.1.symm ▸ hVC.1.2.2.1,hh.2.symm ▸ hVC.1.2.1⟩
    obtain ⟨g,hg⟩ := F.surjective_internal f hfi
    have hgN : N.ends g=s(a,b) := by
      rw [← F.ends_eq,hg]
      exact hf
    cases hg
    exact hyperLike_iff_adjoint_VC.mpr
      ⟨g,hgN,((F.eraseBond g).isVC_iff A (Finset.Subset.refl _) a b).mpr hVC⟩

end LocalDartEmbedding
end WaveTurbulence.Vine
