/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRepGap
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedDesignatedSupport
public import WaveTurbulence.Foundations.Vine.A.VineHVCObjectGap
public import WaveTurbulence.Foundations.Vine.A.VineGapJointChoice
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvData
public import WaveTurbulence.Foundations.FinalCount.RedSpliceHVC
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO (ruling R171): the gap kind of a survivor pair

The gap entry of a marked group (o75 (2.3); `gapSpecificationMk`'s marked branch) uses an out/in pair of its first
survivor at the survivor's upper joint.  This file proves, in the original garden, that such a pair has the gap kind of
the designated object of the group, for a VC group and for an HVC group:

* `chainIngredient_not_both`: an ingredient of a chain of at least two vines does not contain both outer joints;
* `exists_survPairSpec`: a vine has an out/in pair inside it at each joint;
* `ingredient_pair_gapKind`: a pair of an ingredient at one of its joints has the gap kind of the designated object.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

section generic
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An ingredient of a chain of at least two vines does not contain both outer joints of the chain. -/
theorem chainIngredient_not_both {M : Molecule V D} {U A : Finset V} {a b x y : V} {n : ℕ}
    (h : Vine.ChainIngredient M U a b n A x y) (hn : 2 ≤ n) : ¬ (a ∈ A ∧ b ∈ A) := by
  revert hn
  induction h with
  | single _ => intro hn; omega
  | append_left hI hT hST _ _ =>
    intro _ hab
    obtain ⟨X, hX⟩ := hT
    have hcS := (Vine.chainIngredient_spec hI).2.2 hab.2
    have hcST : _ ∈ _ ∩ _ := Finset.mem_inter.mpr ⟨hcS, hX.1.2.2.1⟩
    rw [hST, Finset.mem_singleton] at hcST
    exact hX.1.2.2.2.1 hcST.symm
  | append_last hC hT hST _ =>
    intro _ hab
    have haS := (Vine.chain_joints_mem hC).1
    have haST : _ ∈ _ ∩ _ := Finset.mem_inter.mpr ⟨haS, hab.1⟩
    rw [hST, Finset.mem_singleton] at haST
    exact Vine.chain_joints_ne hC haST

end generic

variable {w : ℕ} {G : Garden w}

/-- A vine has an out/in pair of darts inside it at its upper joint. -/
theorem exists_survPairSpec {T : Finset (GBranch G.tree)} {j l : GBranch G.tree}
    (hT : Vine.IsSomeVine G.molecule T j l) : ∃ p, SurvPairSpec G T j p := by
  obtain ⟨X, hX⟩ := hT
  let O : Object G.molecule := ⟨T, j, l, .vc ⟨hX.1, 1, Chain.single ⟨X, hX⟩⟩⟩
  obtain ⟨x, y, hxy, hx, hy⟩ := objectJoint_pair O (Or.inl rfl)
  exact ⟨(x, y), hxy, hx, hy⟩

/-- **The gap kind of an ingredient pair** (o75 Lemma 3: survivors carry the gap of their chain; R171).  An out/in pair
of darts inside an ingredient `T` of the group `S`, at a joint of `T`, has the gap kind of the designated object of
`S`. -/
theorem ingredient_pair_gapKind (hM : G.molecule.IsMolecule) {S T : Finset (GBranch G.tree)} {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L w c κ) (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (hS : S ∈ maximalGroups G.molecule) (hI : IsIngredient G.molecule S T)
    {j l : GBranch G.tree} (hT : Vine.IsSomeVine G.molecule T j l) {p : GardenDart G × GardenDart G}
    (hp : SurvPairSpec G T j p) {P : Object G.molecule} (hP : designatedObject G S = some P)
    {k : Molecule.GapKind} (hk : P.HasGapKind L γ η w κ k) :
    Molecule.gapKind L γ η (Molecule.gapAt L w κ p.1 p.2) = k := by
  obtain ⟨hk1, hc1⟩ := kvec_cons L w c κ hκ hc0
  obtain ⟨⟨hpx, hpy, -, hne⟩, hgx, hgy⟩ := hp
  obtain ⟨X, hX⟩ := hT
  unfold Molecule.gapAt
  rcases hI with ⟨a, b, n, x0, y0, hU, hCI⟩ | ⟨a, b, e, n, x0, y0, hends, hn2, hUN, hCI⟩
  · -- a VC group
    obtain ⟨hchain, ⟨X0, hX0⟩, -⟩ := Vine.chainIngredient_spec hCI
    have hj : j = x0 ∨ j = y0 := by
      have hu := Vine.block_joints_unique G.molecule hX.1 hX0.1
      have : j ∈ ({x0, y0} : Finset _) := by rw [← hu]; simp
      simpa using this
    have hn := pair_norm_ingredient G.molecule hM hCI hU hj (Molecule.kvec L w κ) hk1 hc1 hpx hpy hgx hgy hne
    have hVC : IsVC G.molecule S a b := ⟨hU, n, Chain.ofVine hchain⟩
    obtain ⟨P', hP', hPa, hPt⟩ := designatedObject_ordinary hS hVC
    rw [hP] at hP'
    cases hP'
    let OS : Object G.molecule := ⟨S, a, b, .vc hVC⟩
    have hOS : OS.HasGapKind L γ η w κ k :=
      (ordinary_objects_gapKind_iff hM OS P hPa.symm rfl hPt L γ η w c κ hκ hc0 k).mpr hk
    obtain ⟨r, hr, rfl⟩ := hOS
    exact kind_of_flow_norm G.molecule hU L γ η w κ hr hn
  · -- an HVC group: the chain lives in the adjoint `eraseBond`
    obtain ⟨hchain, ⟨X0, hX0⟩, -⟩ := Vine.chainIngredient_spec hCI
    have hnot : ¬ (a ∈ T ∧ b ∈ T) := chainIngredient_not_both hCI hn2
    have hX0M : G.molecule.IsBlock T x0 y0 := (block_transfer G.molecule hends hnot x0 y0).mp hX0.1
    have hj : j = x0 ∨ j = y0 := by
      have hu := Vine.block_joints_unique G.molecule hX.1 hX0M
      have : j ∈ ({x0, y0} : Finset _) := by rw [← hu]; simp
      simpa using this
    have hab : a ≠ b := hUN.2.2.2.1
    have hne' := Vine.ends_distinct_of_pair G.molecule e hends hab
    have hN := Vine.eraseBond_isMolecule G.molecule hM e hne'
    obtain ⟨cN, hκN, hcN⟩ := Vine.eraseBond_decoration_exists G.molecule hM e hne' L w c κ hκ hc0
    obtain ⟨hk2, hc2⟩ := kvec_cons L w cN (fun z => κ z.1) hκN hcN
    -- the darts of the pair avoid the added bond: its ends are the outer joints `a, b`
    have hendsat : G.molecule.ends e = s(G.molecule.atom e, G.molecule.atom (G.molecule.mate e)) := rfl
    have havoid : ∀ z : GardenDart G, G.molecule.InGroup T z → z ≠ e ∧ z ≠ G.molecule.mate e := by
      intro z hz
      have hab' : ({G.molecule.atom e, G.molecule.atom (G.molecule.mate e)} : Finset _) = {a, b} := by
        rw [hendsat] at hends
        rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2, Finset.pair_comm]
      have hboth : G.molecule.atom e ∈ T ∧ G.molecule.atom (G.molecule.mate e) ∈ T → False := by
        intro ⟨h1, h2⟩
        apply hnot
        have ha : a ∈ ({G.molecule.atom e, G.molecule.atom (G.molecule.mate e)} : Finset _) := by
          rw [hab']; simp
        have hb : b ∈ ({G.molecule.atom e, G.molecule.atom (G.molecule.mate e)} : Finset _) := by
          rw [hab']; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        constructor
        · rcases ha with rfl | rfl <;> assumption
        · rcases hb with rfl | rfl <;> assumption
      refine ⟨fun hze => hboth ?_, fun hze => hboth ?_⟩
      · subst hze; exact ⟨hz.1, hz.2⟩
      · subst hze
        refine ⟨?_, hz.1⟩
        have := hz.2
        rwa [G.molecule.mate_mate] at this
    obtain ⟨he1, he2⟩ := havoid p.1 hgx
    obtain ⟨he3, he4⟩ := havoid p.2 hgy
    have hn := pair_norm_ingredient (eraseBond G.molecule e) hN hCI hUN hj (Molecule.kvec L w (fun z => κ z.1))
      hk2 hc2 (x := ⟨p.1, he1, he2⟩) (y := ⟨p.2, he3, he4⟩) hpx hpy hgx hgy hne
    have hHVC : IsHVC G.molecule S a b := ⟨e, hends, hUN, n, hn2, Chain.ofVine hchain⟩
    obtain ⟨P', hP', hPa⟩ := designatedObject_atoms hS ⟨a, b, Or.inr (Or.inr hHVC)⟩
    rw [hP] at hP'
    cases hP'
    let OS : Object G.molecule := ⟨S, a, b, .hyper ⟨e, hends, ⟨hUN, n, Chain.ofVine hchain⟩⟩⟩
    have hOS : OS.HasGapKind L γ η w κ k :=
      (objects_gapKind_iff_of_HVC hM OS P hPa.symm hHVC L γ η w c κ hκ hc0 k).mpr hk
    obtain ⟨r, hr, rfl⟩ := hOS
    unfold VineLikeObject.IsGap at hr
    exact kind_of_flow_norm (eraseBond G.molecule e) hUN L γ η w (fun z => κ z.1) hr hn

end WaveTurbulence.VineA.NormalizedSplice
