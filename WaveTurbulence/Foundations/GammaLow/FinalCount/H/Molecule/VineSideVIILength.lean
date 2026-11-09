/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineSideVIILength
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Member
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineSideVIILength`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's statement names the drawn vine types; in the low family
`𝒱_{γL}` a vine is of type (I), (II) or a T-vine, and the drawn-type classification is replaced by N3 Cor 1.16′
(`Src.DSInputs`, see `H/DS/Member.lean`). Low-range change: main's `typeVII_VC_side_length` (a VC avoiding the joints of a vine (VII) is
a full side) becomes `VC_avoiding_joints_shape`: a VC nested in a vine of the low family and missing one of its joints is a
member, hence one or two double bonds or a T-vine.

# A VC in a vine of the low family missing one of its joints is a member 
Main's proof of `typeVII_VC_side_length` uses `not_isVC_five_or_seven_of_erase_connected`, which is FALSE over the
low family (L6 finding H-1: five- and seven-atom T-vines are VCs); neither that lemma nor main's side structure is used
here: the low statement follows from N3 Cor 1.16′ (L3, unconditional).
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- A VC nested in a vine of the low family and missing one of the outer joints is a proper sub-object, so it is one or
two double bonds or a T-vine (N3 Cor 1.16′(2)). -/
theorem VC_avoiding_joints_shape (M : Molecule V D) {S A : Finset V} {a b x y : V}
    (hV : Src.IsSomeVine Src.γL M S a b) (hVC : Src.IsVC Src.γL M A x y) (hAS : A ⊆ S) (hmiss : a ∉ A ∨ b ∉ A) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsTVine A x y := by
  have hne : A ≠ S := by
    rintro rfl
    rcases hmiss with h | h
    · exact h hV.block.2.1
    · exact h hV.block.2.2.1
  exact DS.vc_member_shape hV hVC (Finset.ssubset_iff_subset_ne.mpr ⟨hAS, hne⟩)

end WaveTurbulence.GammaLow.FinalCount.H
