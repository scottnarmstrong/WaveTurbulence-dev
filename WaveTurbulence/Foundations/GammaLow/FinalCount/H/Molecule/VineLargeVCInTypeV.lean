/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineLargeVCInTypeV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCInTypeV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineLargeVCInTypeV`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's statement names the drawn vine types; in the low family
`𝒱_{γL}` a vine is of type (I), (II) or a T-vine, and the drawn-type classification is replaced by N3 Cor 1.16′
(`Src.DSInputs`, see `H/DS/Member.lean`). Low-range change: main's `large_VC_in_typeV_eq` (a nested VC with more than three atoms in a
vine (V) is the whole vine) is false for T-vines (a T-vine has T-vine members); its low form is `VC_in_TVine_joint_eq`: a
nested VC meeting a joint of the T-vine is the whole T-vine (members avoid the joints, N3 Cor 1.16′(1)).

# A VC in a T-vine meeting one of its joints is the whole T-vine -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- A VC nested in a T-vine and containing one of its joints equals the whole T-vine (N3 Cor 1.16′(1)). -/
theorem VC_in_TVine_joint_eq (M : Molecule V D) {A S : Finset V} {a b x y : V}
    (hV : M.IsTVine S a b) (hA : Src.IsVC Src.γL M A x y) (hAS : A ⊆ S) (hj : a ∈ A ∨ b ∈ A) : A = S := by
  by_contra he
  have hc := DS.cor116_low (Src.isSomeVine_of_T hV) ⟨A, x, y, .vc hA⟩
    (Finset.ssubset_iff_subset_ne.mpr ⟨hAS, he⟩)
  rcases hj with h | h
  · exact hc.1 h
  · exact hc.2.1 h

end WaveTurbulence.GammaLow.FinalCount.H
