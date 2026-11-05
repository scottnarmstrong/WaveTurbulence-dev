/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.JointBondBounds

/-! # Triple-bond invariance under the exact directed molecule isomorphism -/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Three actual bonds are preserved and reflected by the concrete dart bijection. -/
theorem tripleBond_unitTwist_iff (a b : GBranch G.tree) :
    TripleBond G.molecule a b ↔ TripleBond (unitTwistGarden G P).molecule
      (coreBranchEquiv G P a) (coreBranchEquiv G P b) := by
  constructor
  · rintro ⟨f,hf,ha,hb⟩
    refine ⟨twistDartEquiv G P ∘ f,(twistDartEquiv G P).injective.comp hf,?_,?_⟩
    · intro i
      change (unitTwistGarden G P).molecule.atom (twistDartEquiv G P (f i)) = _
      rw [twistDartEquiv_atom,ha]
    · intro i
      change (unitTwistGarden G P).molecule.atom ((unitTwistGarden G P).molecule.mate (twistDartEquiv G P (f i))) = _
      rw [twistDartEquiv_mate,twistDartEquiv_atom,hb]
  · rintro ⟨f,hf,ha,hb⟩
    refine ⟨(twistDartEquiv G P).symm ∘ f,(twistDartEquiv G P).symm.injective.comp hf,?_,?_⟩
    · intro i
      have hh := twistDartEquiv_atom G P ((twistDartEquiv G P).symm (f i))
      rw [Equiv.apply_symm_apply,ha] at hh
      exact ((coreBranchEquiv G P).injective hh).symm
    · intro i
      have hm := twistDartEquiv_mate G P ((twistDartEquiv G P).symm (f i))
      have hh := twistDartEquiv_atom G P (G.molecule.mate ((twistDartEquiv G P).symm (f i)))
      rw [← hm,Equiv.apply_symm_apply,hb] at hh
      exact ((coreBranchEquiv G P).injective hh).symm

/-- Absence of three parallel bonds at a specified actual atom. -/
@[expose] def NoTripleAt (b : GBranch G.tree) : Prop :=
  ∀ q : GBranch G.tree, b ≠ q → ¬ TripleBond G.molecule b q

/-- The exact molecule isomorphism preserves absence of a triple bond at the lower joint. -/
theorem noTripleAt_unitTwist (h : NoTripleAt G P.lower) :
    NoTripleAt (unitTwistGarden G P) (coreBranchEquiv G P P.lower) := by
  intro q hq ht
  obtain ⟨q,rfl⟩ := (coreBranchEquiv G P).surjective q
  have hne : P.lower ≠ q := fun he => hq (congrArg (coreBranchEquiv G P) he)
  exact h q hne ((tripleBond_unitTwist_iff G P P.lower q).mpr ht)

end WaveTurbulence.Twist
