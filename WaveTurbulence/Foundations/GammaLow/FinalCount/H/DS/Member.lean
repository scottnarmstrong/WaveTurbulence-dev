/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Base
/-! # H-DS: members of a vine of the low family (N3 Cor 1.16′ (1), (2); packet L6-HDS; hand-written)

TARGET Lemma `subsetvc` (L2431) and DH23 Prop `subsetvc` (L2128) classify the vine-like objects inside a vine by the drawn
types ("a double bond, two double bonds, or a vine (V)"). For the low family the list is N3 Corollary 1.16′(2)
(`research-gamma-half-3/NOTES.txt` L459–L499, REFEREED; Lean: L3's `Struct.Cor116SingleStatement`, field `cor116` of
`Src.DSInputs`): a proper sub-object of a T-vine is a block I, a block or hyper VC:I+I, a block T-vine or a hyper
T-vine, and one of a vine (II) is a block I; it avoids the joints (1). In main's `subsetvc` vocabulary:
* `vc_member_shape`: an ordinary proper sub-object is `DoubleChain 1`, `DoubleChain 2` or a T-vine;
* `hyper_member_shape`: a hyper one has, for its designated bond, an adjoint `DoubleChain 2` or a T-vine;
* `vc_in_tvine`, `hyper_in_vine`: the same without properness (a VC equal to a T-vine is that T-vine; a hyper object is
  never a block);
* `SG_VC_in_vine`: an SG VC in an LG/ZG vine of the low family (no gap premise beyond main's
  `SG_block_outer_joints_absent`, which makes it proper). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H.DS
open Finset WaveTurbulence.Vine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S A : Finset V}
  {a b x y : V}

/-- The realization of an HV/HVC of the low family. -/
theorem hyperLike_realization (h : Src.IsHV Src.γL M A x y ∨ Src.IsHVC Src.γL M A x y) :
    Nonempty (Src.HyperLikeRealization Src.γL M A x y) := by
  rcases h with ⟨e, he, hv⟩ | ⟨e, he, hB, n, -, hC⟩
  · exact ⟨⟨e, he, ⟨Src.isBlock_of_isSomeVine hv, 1, Src.Chain.single hv⟩⟩⟩
  · exact ⟨⟨e, he, ⟨hB, n, hC⟩⟩⟩

/-- A hyper object is not a block (its joints have degree `3` in its atom set). -/
theorem hyper_not_block (R : Src.HyperLikeRealization Src.γL M A x y) (hB : M.IsBlock A a b) : False := by
  have hH : Mole.IsHyperBlock M A x y := ⟨R.added, R.ends_eq, R.adjoint.1⟩
  have hd := (Mole.hyperBlock_degrees M hH).1
  have hx : x ∈ A := R.adjoint.1.2.1
  have hb := Mole.block_joint_degrees M hB
  by_cases hxa : x = a
  · subst hxa; omega
  by_cases hxb : x = b
  · subst hxb; omega
  have := hB.2.2.2.2.2.2.2.2.1 x hx hxa hxb
  omega

/-- A vine (I) has no proper sub-object with two distinct atoms. -/
theorem typeI_no_proper (hI : M.IsVine .I S a b) (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) (hAS : A ⊂ S) : False := by
  have h1 := card_lt_card hAS
  rw [Vine.typeI_atoms hI, card_pair hI.1.2.2.2.1] at h1
  have hsub : ({x, y} : Finset V) ⊆ A := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hx
    · exact hy
  have h2 := card_le_card hsub
  rw [card_pair hxy] at h2
  omega

section inputs

/-- N3 Cor 1.16′ (1), (2) for a vine of the low family. -/
theorem cor116_low (hV : Src.IsSomeVine Src.γL M S a b) (U : Src.Object Src.γL M) (hUS : U.atoms ⊂ S) :
    a ∉ U.atoms ∧ b ∉ U.atoms ∧ (M.IsTVine S a b → TVine.Struct.TVineMemberType M U) ∧
      (M.IsVine .II S a b → (∃ h, U.shape = .vc h) ∧ M.IsVine .I U.atoms U.upper U.lower) :=
  (Src.DSInputs.cor116 (V := V) (D := D) M Src.γL Src.γL_le S a b (Src.isSomeVine_γL_iff.mp hV)).1 U hUS

/-- **Ordinary members** of a vine of the low family: one double bond, two double bonds, or a T-vine. -/
theorem vc_member_shape (hV : Src.IsSomeVine Src.γL M S a b) (hA : Src.IsVC Src.γL M A x y) (hAS : A ⊂ S) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsTVine A x y := by
  have hc := cor116_low hV ⟨A, x, y, .vc hA⟩ hAS
  rcases hV.cases with hI | hII | hT
  · exact (typeI_no_proper hI hA.1.2.1 hA.1.2.2.1 hA.1.2.2.2.1 hAS).elim
  · exact Or.inl (DoubleChain.single (hc.2.2.2 hII).2)
  · exact vc_shape_of_memberType (U := ⟨A, x, y, .vc hA⟩) rfl (hc.2.2.1 hT)

/-- **Hyper members** of a vine of the low family: the adjoint of the designated bond is two double bonds or a T-vine. -/
theorem hyper_member_shape (hV : Src.IsSomeVine Src.γL M S a b) (R : Src.HyperLikeRealization Src.γL M A x y)
    (hAS : A ⊂ S) :
    ∃ e : D, M.ends e = s(x, y) ∧
      (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsTVine A x y) := by
  have hc := cor116_low hV ⟨A, x, y, .hyper R⟩ hAS
  rcases hV.cases with hI | hII | hT
  · exact (typeI_no_proper hI R.adjoint.1.2.1 R.adjoint.1.2.2.1 R.adjoint.1.2.2.2.1 hAS).elim
  · obtain ⟨h, hh⟩ := (hc.2.2.2 hII).1
    cases hh
  · exact hyper_shape_of_memberType (U := ⟨A, x, y, .hyper R⟩) rfl (hc.2.2.1 hT)

/-- A VC inside a T-vine is the T-vine itself or one of its members. -/
theorem vc_in_tvine (hV : M.IsTVine S a b) (hA : Src.IsVC Src.γL M A x y) (hAS : A ⊆ S) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsTVine A x y := by
  by_cases he : A = S
  · subst he
    exact Or.inr (Or.inr (isTVine_rejoint hV hA.1))
  · exact vc_member_shape (Src.isSomeVine_of_T hV) hA (Finset.ssubset_iff_subset_ne.mpr ⟨hAS, he⟩)

/-- A hyper object inside a vine of the low family is a hyper member (it is not the vine, a block). -/
theorem hyper_in_vine (hV : Src.IsSomeVine Src.γL M S a b) (R : Src.HyperLikeRealization Src.γL M A x y)
    (hAS : A ⊆ S) :
    ∃ e : D, M.ends e = s(x, y) ∧
      (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsTVine A x y) := by
  have he : A ≠ S := by
    intro h
    exact hyper_not_block R (by rw [h]; exact hV.block)
  exact hyper_member_shape hV R (Finset.ssubset_iff_subset_ne.mpr ⟨hAS, he⟩)

/-- **TARGET `subsetvc`, single-vine container (low family).** An SG VC in an LG/ZG vine of the low family avoids the
outer joints (main's `SG_block_outer_joints_absent`), hence is a member. -/
theorem SG_VC_in_vine (hM : M.IsMolecule) (hV : Src.IsSomeVine Src.γL M S a b) (hA : Src.IsVC Src.γL M A x y)
    (hAS : A ⊆ S) {d : ℕ} (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0) {r r' : Mom d}
    (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG)
    (hsmall : Molecule.gapKind L γ η r' = .SG) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsTVine A x y := by
  have hj := SG_block_outer_joints_absent M hM hV.block hA.1 hAS L γ η w c κ hκ hc hr hr' houter hsmall
  have hne : A ≠ S := by
    intro h
    exact hj.1 (by rw [h]; exact hV.block.2.1)
  exact vc_member_shape hV hA (Finset.ssubset_iff_subset_ne.mpr ⟨hAS, hne⟩)

end inputs

end WaveTurbulence.GammaLow.FinalCount.H.DS
