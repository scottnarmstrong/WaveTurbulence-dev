/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineDVOrdinaryShapes
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVOrdinary
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVBlockBranchEquality
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineDVOrdinaryShapes`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's DV is two vines (V); here it is the DV′ of D11
(`Src.IsDV Src.γL`), whose branches are T-vines with `σ = 1` (`H/DS/DV.lean`); the removal arguments are N3 Cor 1.16′(3) and
N3 Lemma P (proved by L3, L3-LP; `H/DS/Removal.lean`, `H/DS/RemovalDV.lean`). Low-range change: a vine in a DV′ is type I or a T-vine (main: I or V); main's `typeV_in_DV_eq_branch` (a vine (V)
in a DV is a branch) is false for T-vines (a branch has T-vine members) and becomes `vine_in_DV_branch_or_split` (a branch,
or inside one branch and disjoint from the other); `typeI_in_DV_split_disjoint` takes the DV′ data (`σ = 1`, T-vine
branches); new `vc_in_DV_split_disjoint` (a VC missing a joint).

# Vines in a DV′ -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Any vine of the low family contained in a DV′ is type I or a T-vine. -/
theorem ordinary_vine_in_DV_shape (M : Molecule V D) (hM : M.IsMolecule)
    {P U : Finset V} {x y a b : V} (hU : Src.IsDV Src.γL M U a b)
    (hP : Src.IsSomeVine Src.γL M P x y) (hPU : P ⊆ U) : M.IsVine .I P x y ∨ M.IsTVine P x y := by
  rcases VC_in_DV M hM hU ⟨hP.block, 1, Src.Chain.single hP⟩ hPU with h | h | h
  · exact Or.inl (DS.typeI_of_card_lt_four hP (by have := doubleChain_card h; omega))
  · exact Or.inl (DS.typeI_of_card_lt_four hP (by have := doubleChain_card h; omega))
  · exact Or.inr h

/-- A VC in a DV′ missing one of its joints lies in one branch and is disjoint from the other (its proper sub-objects
avoid the joints, N3 Cor 1.16′(1)). -/
theorem vc_in_DV_split_disjoint (M : Molecule V D) (hM : M.IsMolecule)
    {S T P : Finset V} {a b x y : V} (hσ : M.sigma a b = 1) (hS : M.IsTVine S a b) (hT : M.IsTVine T a b)
    (hi : S ∩ T = {a, b}) (hP : Src.IsVC Src.γL M P x y) (hPU : P ⊆ S ∪ T) (hmiss : ¬(a ∈ P ∧ b ∈ P)) :
    (P ⊆ S ∧ Disjoint P T) ∨ (P ⊆ T ∧ Disjoint P S) := by
  have side : ∀ {B C : Finset V}, M.IsTVine B a b → B ∩ C = {a, b} → P ⊆ B → P ⊆ B ∧ Disjoint P C := by
    intro B C hB hBC hPB
    have hne : P ≠ B := fun h => hmiss ⟨by rw [h]; exact hB.1.2.1, by rw [h]; exact hB.1.2.2.1⟩
    have hc := DS.cor116_low (Src.isSomeVine_of_T hB) ⟨P, x, y, .vc hP⟩
      (Finset.ssubset_iff_subset_ne.mpr ⟨hPB, hne⟩)
    refine ⟨hPB, disjoint_left.mpr fun v hvP hvC => ?_⟩
    have hv : v ∈ B ∩ C := mem_inter.mpr ⟨hPB hvP, hvC⟩
    rw [hBC] at hv
    rcases mem_insert.mp hv with h | h
    · exact hc.1 (h ▸ hvP)
    · exact hc.2.1 (mem_singleton.mp h ▸ hvP)
  rcases VC_in_DV_missing_joint_side M hM hσ (Src.isSomeVine_of_T hS) (Src.isSomeVine_of_T hT) hi hP hPU hmiss
    with hPS | hPT
  · exact Or.inl (side hS hi hPS)
  · exact Or.inr (side hT (by rw [inter_comm]; exact hi) hPT)

/-- A vine of the low family in a DV′ is one of the branches, or lies in one branch and is disjoint from the other. -/
theorem vine_in_DV_branch_or_split (M : Molecule V D) (hM : M.IsMolecule)
    {S T P : Finset V} {a b x y : V} (hσ : M.sigma a b = 1) (hS : M.IsTVine S a b) (hT : M.IsTVine T a b)
    (hi : S ∩ T = {a, b}) (hP : Src.IsSomeVine Src.γL M P x y) (hPU : P ⊆ S ∪ T) :
    P = S ∨ P = T ∨ (P ⊆ S ∧ Disjoint P T) ∨ (P ⊆ T ∧ Disjoint P S) := by
  by_cases hboth : a ∈ P ∧ b ∈ P
  · rcases block_in_DV_both_joints_eq_branch M hM hσ hS hT hi hP.block hPU hboth.1 hboth.2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (vc_in_DV_split_disjoint M hM hσ hS hT hi ⟨hP.block, 1, Src.Chain.single hP⟩ hPU hboth))

/-- A double-bond piece in a DV′ lies in one branch and is disjoint from the other (it cannot contain both joints:
`σ(a, b) = 1`). -/
theorem typeI_in_DV_split_disjoint (M : Molecule V D) (hM : M.IsMolecule)
    {S T P : Finset V} {a b x y : V} (hσ : M.sigma a b = 1) (hS : M.IsTVine S a b) (hT : M.IsTVine T a b)
    (hi : S ∩ T = {a, b}) (hP : M.IsVine .I P x y) (hPU : P ⊆ S ∪ T) :
    (P ⊆ S ∧ Disjoint P T) ∨ (P ⊆ T ∧ Disjoint P S) := by
  have hmiss : ¬(a ∈ P ∧ b ∈ P) := by
    rintro ⟨ha, hb⟩
    have h2 : M.bondsBetween x y = 2 := LGSpine.isVine_bondsBetween hP
    have h2' : M.bondsBetween y x = 2 := by
      unfold Molecule.bondsBetween at h2 ⊢
      rw [Sym2.eq_swap]
      exact h2
    unfold Molecule.sigma at hσ
    have hab : a ≠ b := hS.1.2.2.2.1
    rw [Vine.typeI_atoms hP] at ha hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hab rfl
    · omega
    · omega
    · exact hab rfl
  exact vc_in_DV_split_disjoint M hM hσ hS hT hi ⟨hP.1, 1, Src.Chain.single (Src.isSomeVine_of_I hP)⟩ hPU hmiss

end WaveTurbulence.GammaLow.FinalCount.H
