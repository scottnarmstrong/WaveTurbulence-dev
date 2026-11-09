/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineSGNonVII
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Member
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineSGNonVII`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's statement names the drawn vine types; in the low family
`𝒱_{γL}` a vine is of type (I), (II) or a T-vine, and the drawn-type classification is replaced by N3 Cor 1.16′
(`Src.DSInputs`, see `H/DS/Member.lean`). Low-range change: main's `SG_VC_in_nonVII` (every outer type but (VII)) becomes `SG_VC_in_badVine`: an SG VC in an LG/ZG vine
(I) or (II) is a single double bond (a vine (I) has no proper sub-object; the members of a vine (II) are blocks I).

# SG VCs in a vine (I) or (II) -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc for an outer vine (I) or (II) of the low family: under the source decoration and SG/LG/ZG gap
premises the inner VC is one double bond. -/
theorem SG_VC_in_badVine (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hV : M.IsVine .I S a b ∨ M.IsVine .II S a b)
    {A : Finset V} {x y : V} (hVC : Src.IsVC Src.γL M A x y) (hAS : A ⊆ S)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG)
    (hsmall : Molecule.gapKind L γ η r' = .SG) : DoubleChain M A x y 1 := by
  have hS : Src.IsSomeVine Src.γL M S a b := hV.elim Src.isSomeVine_of_I Src.isSomeVine_of_II
  have hj := SG_block_outer_joints_absent M hM hS.block hVC.1 hAS L γ η w c κ hκ hc hr hr' houter hsmall
  have hne : A ≠ S := by
    rintro rfl
    exact hj.1 hS.block.2.1
  have hss : A ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hAS, hne⟩
  have hcor := DS.cor116_low hS ⟨A, x, y, .vc hVC⟩ hss
  rcases hV with hI | hII
  · exact (DS.typeI_no_proper hI hVC.1.2.1 hVC.1.2.2.1 hVC.1.2.2.2.1 hss).elim
  · exact DoubleChain.single (hcor.2.2.2 hII).2

end WaveTurbulence.GammaLow.FinalCount.H
