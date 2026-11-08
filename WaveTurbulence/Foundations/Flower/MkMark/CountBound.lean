/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.Owner
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.Molecule.VineBlockJoints
public import WaveTurbulence.Foundations.Molecule.TwistSeparatedVines

/-! # B2b MK-MARK (b): Lemma 1⁺, `MarkCountBound`

o75 Lemma 1⁺ (B0 SCOPE §2): at most `3|Π|` vines of `𝒱` are marked by the enlarged rule.

* A skeleton branch is a non-upper atom of at most one vine of `𝒱` (`vinesV_eq_of_nonupper`). Two distinct
  members of `𝒱` share at most one atom, and a shared atom has internal degree two in both, so it is a joint
  of both (main's `ing_pair`, `block_degree_two_joint`). If it were the lower joint of both, its parent
  would be a second shared atom (both lower joints have internal parents).
* An address lies in the near regions of at most three branches (`card_nearBranches_le`).
* Hence every protected vertex marks at most three vines (`markCountBound`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg.Skeleton WaveTurbulence.Stage1

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-- **A skeleton branch is a non-upper atom of at most one vine of `𝒱`.** Two vines of `𝒱` are atom-disjoint
or share exactly one atom, which is the upper joint of one of them (o75 §4.1, T1433, T1936). -/
theorem vinesV_eq_of_nonupper {G : Garden w} {c c' : CLVine G} (hc : c ∈ vinesV G) (hc' : c' ∈ vinesV G)
    {b : GBranch G.tree} (hb : b ∈ c.atoms) (hbu : b ≠ c.upper) (hb' : b ∈ c'.atoms) (hbu' : b ≠ c'.upper) :
    c = c' := by
  by_contra hne
  have hsep := VineA.vinesV_separated hc hc' hne
  obtain ⟨S, hS, hi, _⟩ := hc
  obtain ⟨T, hT, hi', _⟩ := hc'
  by_cases he : S = T
  · subst T
    have hat : c.atoms ≠ c'.atoms := fun h => hne (VineA.clVine_eq_of_atoms h)
    have hdeg := (ing_pair (Mole.garden_isMolecule G) hi hi' hat).2 b (Finset.mem_inter.mpr ⟨hb, hb'⟩)
    obtain ⟨X, hX⟩ := c.isVine
    obtain ⟨X', hX'⟩ := c'.isVine
    have hl : b = c.lower :=
      (Vine.block_degree_two_joint G.molecule hX.1 hb hdeg.1).resolve_left hbu
    have hl' : b = c'.lower :=
      (Vine.block_degree_two_joint G.molecule hX'.1 hb' hdeg.2).resolve_left hbu'
    obtain ⟨hn, hp⟩ := c.parentLower
    obtain ⟨hn', hp'⟩ := c'.parentLower
    have hn0 : b.1.2 ≠ [] := hl ▸ hn
    have hpar : GNode.parent b.toNode hn0 ∈ c.atoms := by
      have e : ∀ (x : GBranch G.tree) (hx : x = c.lower) (hxn : x.1.2 ≠ []), GNode.parent x.toNode hxn ∈ c.atoms := by
        intro x hx hxn
        subst hx
        exact hp
      exact e b hl hn0
    have hpar' : GNode.parent b.toNode hn0 ∈ c'.atoms := by
      have e : ∀ (x : GBranch G.tree) (hx : x = c'.lower) (hxn : x.1.2 ≠ []), GNode.parent x.toNode hxn ∈ c'.atoms := by
        intro x hx hxn
        subst hx
        exact hp'
      exact e b hl' hn0
    exact Twist.branch_ne_parent G b hn0 (hsep b hb hb' _ hpar hpar')
  · exact Finset.disjoint_left.mp (maximalGroups_disjoint (Mole.garden_isMolecule G) hS hT he)
      (ing_subset hi hb) (ing_subset hi' hb')

/-- **Lemma 1⁺ (B2b target, o75 Lemma 1⁺).** At most `3|Π|` vines of `𝒱` are marked. -/
theorem markCountBound : MarkCountBound := by
  intro w LG A Pi
  haveI : Fintype (CLVine A.skeleton) := Fintype.ofFinite _
  let V : GBranch A.skeleton.tree → Finset (CLVine A.skeleton) := fun b =>
    Finset.univ.filter fun c => c ∈ vinesV A.skeleton ∧ b ∈ c.atoms ∧ b ≠ c.upper
  have hV : ∀ b, (V b).card ≤ 1 := by
    intro b
    refine Finset.card_le_one.mpr fun c hc c' hc' => ?_
    obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.mp hc).2
    obtain ⟨h1', h2', h3'⟩ := (Finset.mem_filter.mp hc').2
    exact vinesV_eq_of_nonupper h1 h1' h2 h3 h2' h3'
  let U : Finset (CLVine A.skeleton) :=
    Pi.biUnion fun a => (nearBranches A.skeleton A.data.tree a.1).biUnion V
  have hsub : markedVinesRaw A.skeleton A.data.tree Pi ⊆ (U : Set (CLVine A.skeleton)) := by
    rintro c ⟨hc, b, hb, hbu, a, ha, hab⟩
    simp only [U, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop]
    exact ⟨a, ha, b, (mem_nearBranches _ _).mpr hab, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hb, hbu⟩⟩
  have hU : ∀ a ∈ Pi, ((nearBranches A.skeleton A.data.tree a.1).biUnion V).card ≤ 3 := by
    intro a _
    calc ((nearBranches A.skeleton A.data.tree a.1).biUnion V).card
        ≤ ∑ b ∈ nearBranches A.skeleton A.data.tree a.1, (V b).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ nearBranches A.skeleton A.data.tree a.1, 1 := Finset.sum_le_sum fun b _ => hV b
      _ = (nearBranches A.skeleton A.data.tree a.1).card := by simp
      _ ≤ 3 := card_nearBranches_le _ _ _
  calc (markedVinesRaw A.skeleton A.data.tree Pi).ncard ≤ (U : Set (CLVine A.skeleton)).ncard :=
        Set.ncard_le_ncard hsub
    _ = U.card := Set.ncard_coe_finset U
    _ ≤ ∑ a ∈ Pi, ((nearBranches A.skeleton A.data.tree a.1).biUnion V).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ Pi, 3 := Finset.sum_le_sum hU
    _ = 3 * Pi.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end WaveTurbulence.Flower.MkMark
