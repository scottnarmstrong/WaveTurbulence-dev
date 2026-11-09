/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.InputsDS
public import WaveTurbulence.Foundations.TVine.Core.Bridge
public import WaveTurbulence.Foundations.TVine.Core.TCap
public import WaveTurbulence.Foundations.TVine.Struct.Kinds
public import WaveTurbulence.Foundations.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.Molecule.VineObjects
public import WaveTurbulence.Foundations.Molecule.VineNestedBlockRecognition
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry
public import WaveTurbulence.Foundations.Molecule.VineSGJointExclusion
public import WaveTurbulence.Foundations.Spine.SourceVineSigma
/-! # H-DS base: the low-family facts replacing main's drawn-type structure (packet L6-HDS; hand-written)

In the low family `𝒱_{γL}` a vine is of type (I), (II) or a T-vine (`Src.IsSomeVine.cases`). This module collects the
facts the layer H-DS uses in place of main's drawn-type classifications:
* T-vines: joint swap and re-jointing (`isTVine_swap`, `isTVine_rejoint`), at least five atoms (L3's
  `Struct.card_isTVineU`), `σ ≤ 1` (the closure is defined), and a member with `σ = 1` is a T-vine (`isTVine_of_sigma_one`;
  (I) has `σ = 2`, (II) has `σ = 0`, main's `LGSpine.isVine_bondsBetween`);
* small chains of the low family consist of double bonds (`chain_doubleChain`, `isVC_doubleChain`; main's
  `isVC_doubleChain_of_card_le_three` over `Src.Chain Src.γL`);
* the member types of N3 Cor 1.16′(2) (`TVine.Struct.TVineMemberType`) in the shape vocabulary of main's `subsetvc`
  (`DoubleChain` with one or two double bonds, now with a T-vine instead of a vine (V)): `vc_shape_of_memberType`,
  `hyper_shape_of_memberType`.
Namespace `…H.DS` (no clash with the ported names of `…H`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H.DS
open Finset WaveTurbulence.Vine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S A : Finset V}
  {a b x y : V}

/-! ### T-vines -/

theorem isTVine_swap (h : M.IsTVine S a b) : M.IsTVine S b a := by
  rw [TVine.Core.isTVine_iff M] at h ⊢
  exact ⟨Mole.block_swap_joints M h.1, h.2.swap⟩

/-- A T-vine is a T-vine for every joint labelling of its block. -/
theorem isTVine_rejoint (h : M.IsTVine S a b) (hB : M.IsBlock S x y) : M.IsTVine S x y := by
  have hj := block_joints_unique M h.1 hB
  have hxy : x ≠ y := hB.2.2.2.1
  have hx : x ∈ ({a, b} : Finset V) := by rw [hj]; simp
  have hy : y ∈ ({a, b} : Finset V) := by rw [hj]; simp
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact h
  · exact isTVine_swap h
  · exact absurd rfl hxy

/-- A T-vine has at least five atoms (L3, `Struct.card_isTVineU`). -/
theorem isTVine_card (h : M.IsTVine S a b) : 5 ≤ S.card :=
  (TVine.Struct.card_isTVineU (TVine.Core.isTVineU_of_isTVine M h)).2

/-- A T-vine is not contained in the pair of its joints. -/
theorem tvine_not_subset_pair (h : M.IsTVine S a b) : ¬ S ⊆ {a, b} := by
  intro hsub
  have h5 := isTVine_card h
  have h2 := card_le_card hsub
  have h2' : ({a, b} : Finset V).card ≤ 2 := card_le_two
  omega

/-- A vine (II) has at least four atoms (L3, `Struct.card_isVineXU_II`). -/
theorem isVineII_card (h : M.IsVine .II S a b) : 4 ≤ S.card :=
  (TVine.Struct.card_isVineXU_II ((TVine.Core.isVine_iff M .II).mp h).2).2

/-- The closure of a T-vine is defined, so `σ ≤ 1`. -/
theorem isTVine_sigma_le (h : M.IsTVine S a b) : M.sigma a b ≤ 1 := by
  obtain ⟨-, -, G, -, hC, -, -⟩ := h
  have := hC.1
  omega

/-- A member of the low family with `σ = 1` is a T-vine: (I) has `σ = 2` and (II) has `σ = 0`. -/
theorem isTVine_of_sigma_one (h : Src.IsSomeVine Src.γL M S a b) (hσ : M.sigma a b = 1) : M.IsTVine S a b := by
  unfold Molecule.sigma at hσ
  rcases h.cases with h | h | h
  · have h2 : M.bondsBetween a b = 2 := LGSpine.isVine_bondsBetween h
    omega
  · have h0 : M.bondsBetween a b = 0 := LGSpine.isVine_bondsBetween h
    omega
  · exact h

/-! ### Small chains -/

theorem typeI_of_card_lt_four (h : Src.IsSomeVine Src.γL M S a b) (hc : S.card < 4) : M.IsVine .I S a b := by
  rcases h.cases with h | h | h
  · exact h
  · exact absurd (isVineII_card h) (by omega)
  · exact absurd (isTVine_card h) (by omega)

theorem chain_pos {n : ℕ} (h : Src.Chain Src.γL M S a b n) : 1 ≤ n := by
  cases h <;> omega

/-- A chain of the low family with fewer than four atoms consists of double bonds. -/
theorem chain_doubleChain {n : ℕ} (h : Src.Chain Src.γL M S a b n) (hc : S.card < 4) : DoubleChain M S a b n := by
  induction h with
  | single h => exact DoubleChain.single (typeI_of_card_lt_four h hc)
  | @append S T a b c n _hS hT hi hne ih =>
    have hcS : S.card < 4 := (card_le_card (subset_union_left : S ⊆ S ∪ T)).trans_lt hc
    have hcT : T.card < 4 := (card_le_card (subset_union_right : T ⊆ S ∪ T)).trans_lt hc
    exact DoubleChain.append (ih hcS) (typeI_of_card_lt_four hT hcT) hi hne

/-- A VC of the low family with at most three atoms is one or two double bonds. -/
theorem isVC_doubleChain (hA : Src.IsVC Src.γL M A x y) (hc : A.card ≤ 3) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 := by
  obtain ⟨_, n, hC⟩ := hA
  have hp := chain_pos hC
  have hD := chain_doubleChain hC (by omega)
  have hcount := doubleChain_card hD
  have hn : n = 1 ∨ n = 2 := by omega
  rcases hn with rfl | rfl
  · exact Or.inl hD
  · exact Or.inr hD

/-! ### The member types of N3 Cor 1.16′(2) in the `subsetvc` vocabulary -/

theorem card_of_isVCII {N : Molecule V D} {T : Finset V} {k₁ k₂ : V} (h : TVine.Struct.IsVCII N T k₁ k₂) :
    T.card = 3 := by
  obtain ⟨c, hc1, hc2, h12, rfl, -, -⟩ := h
  rw [card_insert_of_notMem (by simp [h12, hc1.symm]), card_pair hc2]

/-- An ordinary member of a T-vine is one double bond, two double bonds, or a T-vine. -/
theorem vc_shape_of_memberType {U : Src.Object Src.γL M} {h : Src.IsVC Src.γL M U.atoms U.upper U.lower}
    (hsh : U.shape = .vc h) (ht : TVine.Struct.TVineMemberType M U) :
    DoubleChain M U.atoms U.upper U.lower 1 ∨ DoubleChain M U.atoms U.upper U.lower 2 ∨
      M.IsTVine U.atoms U.upper U.lower := by
  simp only [TVine.Struct.TVineMemberType, hsh] at ht
  rcases ht with h1 | h2 | hT
  · exact Or.inl (DoubleChain.single h1)
  · rcases isVC_doubleChain h (card_of_isVCII h2).le with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr hT)

/-- A hyper member of a T-vine has, for its designated bond, an adjoint that is two double bonds or a T-vine. -/
theorem hyper_shape_of_memberType {U : Src.Object Src.γL M}
    {R : Src.HyperLikeRealization Src.γL M U.atoms U.upper U.lower} (hsh : U.shape = .hyper R)
    (ht : TVine.Struct.TVineMemberType M U) :
    ∃ e : D, M.ends e = s(U.upper, U.lower) ∧
      (DoubleChain (Mole.eraseBond M e) U.atoms U.upper U.lower 2 ∨
        (Mole.eraseBond M e).IsTVine U.atoms U.upper U.lower) := by
  simp only [TVine.Struct.TVineMemberType, hsh] at ht
  refine ⟨R.added, R.ends_eq, ?_⟩
  rcases ht with h2 | hT
  · left
    have hc := card_of_isVCII h2
    rcases isVC_doubleChain R.adjoint hc.le with h1 | h2
    · have := doubleChain_card h1; omega
    · exact h2
  · exact Or.inr hT

end WaveTurbulence.GammaLow.FinalCount.H.DS
