/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceHyperBlockFalse
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionAtoms
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.DV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceHyperBlockFalse`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 The one-joint union of two selected ordinary objects is never a hyper-block either. 

**Low-range change (L6-HDS).** The double vines are DV′s of the low family (`Src.DoubleVine`: `σ = 1`, two members
of `𝒱_{γL}`; main: two vines (V)); only their blocks, `σ = 1` and the degree profile (`DS.dv_degree_profile`) are used.
-/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem isContained_of_vc_left (P U : Src.Object Src.γL M) (hP : ∃ h, P.shape = .vc h)
    (hsub : P.atoms ⊆ U.atoms) : P.IsContained U := by
  obtain ⟨hh, hs⟩ := hP
  rcases P with ⟨A, x, y, Psh⟩
  rcases U with ⟨S, a, b, Ush⟩
  cases Psh with
  | vc h' => cases Ush <;> exact hsub
  | hyper R => cases hs

theorem isContained_of_vc_right (P U : Src.Object Src.γL M) (hU : ∃ h, U.shape = .vc h)
    (hsub : P.atoms ⊆ U.atoms) : P.IsContained U := by
  obtain ⟨hh, hs⟩ := hU
  rcases P with ⟨A, x, y, Psh⟩
  rcases U with ⟨S, a, b, Ush⟩
  cases Ush with
  | vc h' => cases Psh <;> exact hsub
  | hyper R => cases hs

theorem one_joint_hyperblock_false {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Src.Object Src.γL G.molecule)}
    (hc : Src.IsSourceSecondCollection Src.γL G L γ η base κ F omitted collection)
    {P Q : Src.Object Src.γL G.molecule} (hPm : P ∈ collection) (hQm : Q ∈ collection)
    {cj : GBranch G.tree} {n m : ℕ}
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h)
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPch : Src.Chain Src.γL G.molecule P.atoms P.upper cj n) (hQch : Src.Chain Src.γL G.molecule Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj})
    (hH : Mole.IsHyperBlock G.molecule (P.atoms ∪ Q.atoms) P.upper Q.lower) : False := by
  obtain ⟨hPsg, hPel⟩ := ((hc.2.2 P).mp hPm).1
  obtain ⟨hQsg, _⟩ := ((hc.2.2 Q).mp hQm).1
  have hQF := eligible_atoms_disjoint ((hc.2.2 Q).mp hQm).1
  have hPB0 := object_vc_block P hPvc
  have hQB0 := object_vc_block Q hQvc
  obtain ⟨U, hUat, hUu, hUl, ⟨RU, hUsh, hUends, hUB⟩, hUgap⟩ :=
    hyper_union_object hPl hQu hPch hQch hPQ hPB0 hQB0 hH
  obtain ⟨rP, hrP, hkP⟩ := (object_vc_hasGapKind_iff P hPvc L γ η base κ .SG).mp hPsg
  have hUsg : U.HasGapKind L γ η base κ .SG := hUgap L γ η base κ .SG ⟨rP, hrP, hkP⟩
  have hbP : Q.lower ∉ P.atoms := by
    intro h
    have : Q.lower ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨h, hQB0.2.2.1⟩
    rw [hPQ] at this
    exact hQB0.2.2.2.1 (hQu.trans (mem_singleton.mp this).symm)
  have hUel : Src.eligibleSecondObject Src.γL G L γ η base κ F U := by
    refine ⟨hUsg, ?_⟩
    rcases one_joint_union_contained G hM hκ hc0 hPvc hQvc hPl hQu hPQ hPsg hQsg hQF hPel with
      ⟨C, hCk, hsub, hCvc, hCF⟩ | ⟨C, hCk, hsub, ⟨RC, hCsh⟩, hCF⟩ | ⟨D, hD, hDF⟩
    · exact Or.inl ⟨C, hUat ▸ hsub, hCk, hCF⟩
    · exact Or.inl ⟨C, hUat ▸ hsub, hCk, hCF⟩
    · exact Or.inr ⟨D, hUat ▸ hD, hDF⟩
  have hUo : U.atoms ∉ omitted := by
    intro ho
    obtain ⟨D, _, _, _, hS⟩ := hc.1 _ ho
    have hdeg := (Mole.hyperBlock_degrees G.molecule ⟨RU.added, hUends, hUB⟩).1
    have hUa : P.upper ∈ P.atoms ∪ Q.atoms := mem_union_left _ hPB0.2.1
    have hvine : ∀ {S : Finset (GBranch G.tree)} {x y : GBranch G.tree},
        Src.IsSomeVine Src.γL G.molecule S x y → U.atoms = S → False := by
      intro S x y hV hS
      rw [hUat] at hS
      rw [hS] at hdeg hUa
      obtain ⟨_, _, _, _, _, _, _, _, hint⟩ := hV.block
      by_cases h1 : P.upper = x
      · have := (Mole.block_joint_degrees G.molecule hV.block).1
        rw [← h1] at this; omega
      · by_cases h2 : P.upper = y
        · have := (Mole.block_joint_degrees G.molecule hV.block).2
          rw [← h2] at this; omega
        · have := hint.1 _ hUa h1 h2
          omega
    rcases hS with h | h
    · exact hvine D.first_vine h
    · exact hvine D.second_vine h
  have hcont := ((hc.2.2 P).mp hPm).2.2 U hUel hUo (isContained_of_vc_left P U hPvc (hUat ▸ subset_union_left))
  have hsub : U.atoms ⊆ P.atoms := Src.Object.contained_atoms_subset U P hcont
  have hl : Q.lower ∈ P.atoms ∩ Q.atoms :=
    mem_inter.mpr ⟨hsub (hUat ▸ mem_union_right _ hQB0.2.2.1), hQB0.2.2.1⟩
  rw [hPQ] at hl
  exact hQB0.2.2.2.1 ((hQu.trans (mem_singleton.mp hl).symm))

end WaveTurbulence.GammaLow.FinalCount.H
