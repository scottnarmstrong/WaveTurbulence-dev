/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Final2
public import WaveTurbulence.Foundations.Molecule.GardenNodeCounts
import Mathlib.Tactic
/-! Combinatorial facts: ranges of `K_S`, the decomposition of the atoms. -/
@[expose] public section
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical
variable {w d : ℕ} {G : Garden w}
variable {D : SplicedKernelData G d} {L γ δ : ℝ} {base : Mom d} {roots : Fin w → (Fin d → ℤ)}
  {hp : G.IsPlain} {π0 : PF G} {εS : LQ G → ℝ}

theorem CD.Kn_zero (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop) (S : LQ G)
    (h : ¬ isSmall S) : cd.Kn isSmall S = 0 := by
  unfold CD.Kn CD.JS
  rw [ite_eq_right h]; simp

theorem CD.Kn_le (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop) (S : LQ G) :
    cd.Kn isSmall S ≤ π0.m S := by
  unfold CD.Kn CD.JS
  by_cases h : isSmall S
  · rw [ite_eq_left h]
    calc (Finset.Icc 1 (π0.m S - 1) \ cd.sel S).card ≤ (Finset.Icc 1 (π0.m S - 1)).card :=
          Finset.card_le_card Finset.sdiff_subset
      _ = π0.m S - 1 := by simp
      _ ≤ π0.m S := Nat.sub_le _ _
  · rw [ite_eq_right h]; simp

theorem CD.m_le_Kn (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop) (S : LQ G)
    (h : isSmall S) : π0.m S ≤ cd.Kn isSmall S + d + 1 := by
  unfold CD.Kn CD.JS
  rw [ite_eq_left h]
  have h1 : (Finset.Icc 1 (π0.m S - 1)).card ≤ (Finset.Icc 1 (π0.m S - 1) \ cd.sel S).card + (cd.sel S).card := by
    calc (Finset.Icc 1 (π0.m S - 1)).card ≤ ((Finset.Icc 1 (π0.m S - 1) \ cd.sel S) ∪ cd.sel S).card := by
          apply Finset.card_le_card; intro x hx
          by_cases hs : x ∈ cd.sel S
          · exact Finset.mem_union_right _ hs
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hs⟩)
      _ ≤ _ := Finset.card_union_le _ _
  have h2 : (cd.sel S).card ≤ cd.q S := by
    unfold CD.sel; exact Finset.card_image_le.trans (by simp)
  have h3 := cd.hq S
  simp only [Nat.card_Icc] at h1
  omega

theorem PF.m_eq_ladderLength (π : PF G) (S : LQ G) : π.m S = Molecule.ladderLength S.1 := by
  have h1 := ladderAtoms_card (π.ladder S).2.1
  rw [π.atoms S] at h1
  unfold Molecule.ladderLength
  omega

theorem card_atoms_decomp (G : Garden w) :
    G.order = G.molecule.numFree + ∑ S : LQ G, S.1.card := by
  have h1 : G.molecule.atoms.card = G.order := WaveTurbulence.Mole.garden_card_atoms G
  have hdisj := WaveTurbulence.Molecule.maximalLadders_pairwiseDisjoint G.molecule
    (WaveTurbulence.Mole.garden_isMolecule G)
  set F := G.molecule.atoms.filter (fun v => ∀ S ∈ G.molecule.maximalLadders, v ∉ S) with hF
  have hU : G.molecule.atoms = F ∪ G.molecule.maximalLadders.biUnion id := by
    ext v
    simp only [hF, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, id]
    constructor
    · intro hv
      by_cases h : ∀ S ∈ G.molecule.maximalLadders, v ∉ S
      · exact Or.inl ⟨hv, h⟩
      · push Not at h; exact Or.inr h
    · rintro (⟨hv, _⟩ | ⟨S, hS, hvS⟩)
      · exact hv
      · exact Finset.mem_univ _
  have hd2 : Disjoint F (G.molecule.maximalLadders.biUnion id) := by
    rw [Finset.disjoint_left]
    intro v hvF hvB
    simp only [hF, Finset.mem_filter, Finset.mem_biUnion, id] at hvF hvB
    obtain ⟨S, hS, hvS⟩ := hvB
    exact hvF.2 S hS hvS
  have h2 : (G.molecule.maximalLadders.biUnion id).card = ∑ S ∈ G.molecule.maximalLadders, S.card := by
    rw [Finset.card_biUnion]
    · rfl
    · intro S hS T hT hST
      exact hdisj hS hT hST
  have h3 : ∑ S : LQ G, S.1.card = ∑ S ∈ G.molecule.maximalLadders, S.card :=
    Finset.sum_coe_sort G.molecule.maximalLadders (fun S => S.card)
  have hnf : G.molecule.numFree = F.card := by
    unfold Molecule.numFree; convert rfl
  calc G.order = G.molecule.atoms.card := h1.symm
    _ = (F ∪ G.molecule.maximalLadders.biUnion id).card := congrArg Finset.card hU
    _ = F.card + (G.molecule.maximalLadders.biUnion id).card := Finset.card_union_of_disjoint hd2
    _ = _ := by rw [hnf, h2, h3]


end WaveTurbulence.Ladder
