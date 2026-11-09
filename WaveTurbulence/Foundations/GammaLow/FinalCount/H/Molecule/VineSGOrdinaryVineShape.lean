/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineSGOrdinaryVineShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGSingleVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineSGOrdinaryVineShape`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's statement names the drawn vine types; in the low family
`𝒱_{γL}` a vine is of type (I), (II) or a T-vine, and the drawn-type classification is replaced by N3 Cor 1.16′ (proved
by L3; `H/DS/Member.lean`, `H/DS/Removal.lean`). Low-range change: the outer vine is a member of the low family (main: `M.IsVine X`); an SG vine in it is type I or a
T-vine (main: type I, or type V when `X = .VII`); main's `typeVII_SG_nonI_vine_side` becomes `SG_nonI_vine_member` (a
non-(I) SG vine is a proper T-vine member avoiding the outer joints).

# SG vines in a single vine of the low family -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- An ordinary SG vine in one LG/ZG vine of the low family is type I or a T-vine. -/
theorem SG_ordinary_vine_shape (M : Molecule V D) (hM : M.IsMolecule)
    {S A : Finset V} {a b x y : V} (hV : Src.IsSomeVine Src.γL M S a b)
    (hA : Src.IsSomeVine Src.γL M A x y) (hAS : A ⊆ S)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG)
    (hsmall : Molecule.gapKind L γ η r' = .SG) :
    M.IsVine .I A x y ∨ M.IsTVine A x y := by
  have hVC : Src.IsVC Src.γL M A x y := ⟨hA.block, 1, Src.Chain.single hA⟩
  rcases SG_VC_in_single_vine M hM hV hVC hAS L γ η w c κ hκ hc hr hr' houter hsmall with h | h | h
  · exact Or.inl (DS.typeI_of_card_lt_four hA (by have := doubleChain_card h; omega))
  · exact Or.inl (DS.typeI_of_card_lt_four hA (by have := doubleChain_card h; omega))
  · exact Or.inr h

/-- A non-type-I ordinary SG vine in an LG/ZG vine of the low family is a T-vine, properly contained, avoiding the outer
joints (low counterpart of main's `typeVII_SG_nonI_vine_side`). -/
theorem SG_nonI_vine_member (M : Molecule V D) (hM : M.IsMolecule)
    {S A : Finset V} {a b x y : V} (hV : Src.IsSomeVine Src.γL M S a b)
    (hA : Src.IsSomeVine Src.γL M A x y) (hnot : ¬M.IsVine .I A x y) (hAS : A ⊆ S)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG)
    (hsmall : Molecule.gapKind L γ η r' = .SG) :
    M.IsTVine A x y ∧ A ⊂ S ∧ a ∉ A ∧ b ∉ A := by
  have hj := SG_block_outer_joints_absent M hM hV.block hA.block hAS L γ η w c κ hκ hc hr hr' houter hsmall
  refine ⟨(SG_ordinary_vine_shape M hM hV hA hAS L γ η w c κ hκ hc hr hr' houter hsmall).resolve_left hnot,
    Finset.ssubset_iff_subset_ne.mpr ⟨hAS, fun h => hj.1 (by rw [h]; exact hV.block.2.1)⟩, hj⟩

end WaveTurbulence.GammaLow.FinalCount.H
