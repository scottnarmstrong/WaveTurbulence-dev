/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossIso
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrown
public import WaveTurbulence.Foundations.FinalCount.SubproItems2
import Mathlib.Tactic

/-!
# SUBPRO (S4): the contained darts of an object at a joint (R28 session 2, `crossing`)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1 WaveTurbulence.Mole

theorem block_unique_dart {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}
    {S : Finset V} {a c : V} (hB : N.IsBlock S a c) (b : Bool) :
    ∃ x, N.atom x = a ∧ N.InGroup S x ∧ N.out x = b ∧
      ∀ x', N.atom x' = a → N.InGroup S x' → N.out x' = b → x' = x := by
  classical
  have key : ∀ (card1 : ((N.dartsAt a).filter fun x => N.InGroup S x ∧ N.out x = b).card = 1),
      ∃ x, N.atom x = a ∧ N.InGroup S x ∧ N.out x = b ∧
        ∀ x', N.atom x' = a → N.InGroup S x' → N.out x' = b → x' = x := by
    intro card1
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp card1
    have hmem : ∀ z, N.atom z = a → N.InGroup S z → N.out z = b → z = y := by
      intro z hz hzS hzo
      have : z ∈ (N.dartsAt a).filter fun x => N.InGroup S x ∧ N.out x = b := by
        simp [Molecule.dartsAt, hz, hzS, hzo]
      rw [hy] at this; simpa using this
    have hy' : y ∈ (N.dartsAt a).filter fun x => N.InGroup S x ∧ N.out x = b := by rw [hy]; simp
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
    exact ⟨y, hy'.1, hy'.2.1, hy'.2.2, hmem⟩
  cases b
  · exact key hB.2.2.2.2.2.1
  · exact key hB.2.2.2.2.1

/-- At a joint of an object there is exactly one contained out-dart and exactly one contained in-dart. -/
theorem contained_unique {w : ℕ} (G' : Garden w) (P : Object G'.molecule) {v : GBranch G'.tree}
    (hv : v = P.upper ∨ v = P.lower) (b : Bool) :
    ∃ x, G'.molecule.atom x = v ∧ P.ContainsDart x ∧ G'.molecule.out x = b ∧
      ∀ x', G'.molecule.atom x' = v → P.ContainsDart x' → G'.molecule.out x' = b → x' = x := by
  obtain ⟨A, a, c, sh⟩ := P
  simp only at hv
  cases sh with
  | vc h =>
    have hB : G'.molecule.IsBlock A a c := h.1
    have hB' : ∃ c', G'.molecule.IsBlock A v c' := by
      rcases hv with rfl | rfl
      · exact ⟨c, hB⟩
      · exact ⟨a, block_swap_joints _ hB⟩
    obtain ⟨c', hc'⟩ := hB'
    obtain ⟨x, h1, h2, h3, h4⟩ := block_unique_dart hc' b
    exact ⟨x, h1, h2, h3, fun x' h1' h2' h3' => h4 x' h1' h2' h3'⟩
  | hyper R =>
    have hB : (Mole.eraseBond G'.molecule R.added).IsBlock A a c := R.adjoint.1
    have hB' : ∃ c', (Mole.eraseBond G'.molecule R.added).IsBlock A v c' := by
      rcases hv with rfl | rfl
      · exact ⟨c, hB⟩
      · exact ⟨a, block_swap_joints _ hB⟩
    obtain ⟨c', hc'⟩ := hB'
    obtain ⟨x, h1, h2, h3, h4⟩ := block_unique_dart hc' b
    refine ⟨x.1, h1, ⟨x.2.1, x.2.2, h2⟩, h3, ?_⟩
    intro x' h1' h2' h3'
    have := h4 ⟨x', h2'.1, h2'.2.1⟩ h1' h2'.2.2 h3'
    exact congrArg Subtype.val this

variable {R : ℕ} {G : Garden (2 * R)}

/-- **The two inside darts of `P` at a hinge sit at one common joint of the unit** (the hinge pair is not split by `P`). -/
theorem hinge_common_joint (hM : G.molecule.IsMolecule) (σ : Prescription G)
    (P : Object (stSt G σ).G.molecule) {v : GBranch (stSt G σ).G.tree} (hvh : v ∈ (stSt G σ).hinges)
    (hvj : v = P.upper ∨ v = P.lower)
    (hnx : ∀ x y, hingePair G σ v = some (x, y) → (P.ContainsDart x ↔ P.ContainsDart y)) :
    ∃ u ∈ unitBlocks G σ, (stSt G σ).M.ob v = u.upper ∧ ∃ j, (j = u.upper ∨ j = u.lower) ∧
      ∀ x, (stSt G σ).G.molecule.atom x = v → P.ContainsDart x → G.molecule.atom ((stSt G σ).M.od x) = j := by
  classical
  obtain ⟨x, y, hp, hPP, -⟩ := hingePair_spec hM σ hvh
  have hnx' := hnx x y hp
  obtain ⟨hT, u, hu, hob, jc, hjc, hxj, hyj, hxe, hye⟩ := hPP
  obtain ⟨ao, hao, hao_c, hao_o, hao_u⟩ := contained_unique (stSt G σ).G P hvj true
  obtain ⟨ai, hai, hai_c, hai_o, hai_u⟩ := contained_unique (stSt G σ).G P hvj false
  have main : ∀ oc ic : GardenDart (stSt G σ).G, G.molecule.atom ((stSt G σ).M.od oc) = jc →
      G.molecule.atom ((stSt G σ).M.od ic) = jc → ¬ G.molecule.InGroup u.atoms ((stSt G σ).M.od oc) →
      ¬ G.molecule.InGroup u.atoms ((stSt G σ).M.od ic) → (stSt G σ).G.molecule.out oc = true →
      (stSt G σ).G.molecule.out ic = false → (P.ContainsDart oc ↔ P.ContainsDart ic) →
      (stSt G σ).G.molecule.atom oc = v → (stSt G σ).G.molecule.atom ic = v →
      ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((stSt G σ).M.od ao) = j ∧
        G.molecule.atom ((stSt G σ).M.od ai) = j := by
    intro oc ic hoc hic hoe hie hoo hio hiff hoa hia
    refine common_joint hM σ hu hob hjc hoc hic hoe hie hoo hio hao hai hao_o hai_o ?_
    by_cases hc : P.ContainsDart oc
    · exact Or.inl ⟨(hao_u oc hoa hc hoo).symm, (hai_u ic hia (hiff.mp hc) hio).symm⟩
    · refine Or.inr ⟨fun h => hc (h ▸ hao_c), fun h => (fun hc' => hc (hiff.mpr hc')) (h ▸ hai_c)⟩
  have hout : (stSt G σ).G.molecule.out x ≠ (stSt G σ).G.molecule.out y := hT.2.2.2
  obtain ⟨j, hj, hjao, hjai⟩ : ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((stSt G σ).M.od ao) = j ∧
      G.molecule.atom ((stSt G σ).M.od ai) = j := by
    cases hox : (stSt G σ).G.molecule.out x
    · have hoy : (stSt G σ).G.molecule.out y = true := by
        cases hoy' : (stSt G σ).G.molecule.out y
        · exact absurd (hox.trans hoy'.symm) hout
        · rfl
      exact main y x hyj hxj hye hxe hoy hox hnx'.symm hT.2.1 hT.1
    · have hoy : (stSt G σ).G.molecule.out y = false := by
        cases hoy' : (stSt G σ).G.molecule.out y
        · rfl
        · exact absurd (hox.trans hoy'.symm) hout
      exact main x y hxj hyj hxe hye hox hoy hnx' hT.1 hT.2.1
  refine ⟨u, hu, hob, j, hj, ?_⟩
  intro x' hx' hc'
  cases hox : (stSt G σ).G.molecule.out x'
  · rw [hai_u x' hx' hc' hox]; exact hjai
  · rw [hao_u x' hx' hc' hox]; exact hjao

end WaveTurbulence.Subpro
