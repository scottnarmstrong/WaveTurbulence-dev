/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.GardenReconstructionCount
import Mathlib.Tactic

/-!
# CLASSCOUNT: molecules as arc lists

A molecule is a directed multigraph.  `molOfArcs n L` is the molecule on the atoms `Fin n` with one bond
for each arc `L.get i = (tail, head)`; its darts are `(i, true)` (the dart at the tail, outgoing) and
`(i, false)` (the dart at the head).  Every garden with an atom labelling `ℓ : GBranch G.tree ≃ Fin n` and
a bond enumeration realizing the list `L` has `GardenMoleculeIso G (molOfArcs n L)`
(`exists_iso_arcs`); so, by DH21-2 Prop 6.4 / TARGET `propcplmol` (`garden_reconstruction_bound_fixed_order`),
a set of gardens each isomorphic to some `molOfArcs n L`, `L ∈ 𝓛`, has at most `|𝓛| (20736 R)! 20736^n` elements.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open WaveTurbulence WaveTurbulence.Mole

/-- The molecule on `Fin n` with the arcs of `L` as bonds. -/
def molOfArcs (n : ℕ) (L : List (Fin n × Fin n)) : Molecule (Fin n) (Fin L.length × Bool) where
  atoms := Finset.univ
  atom := fun d => if d.2 then (L.get d.1).1 else (L.get d.1).2
  mate := fun d => (d.1, !d.2)
  out := fun d => d.2
  atom_mem := fun _ => Finset.mem_univ _
  mate_mate := fun d => by simp
  mate_ne := fun d h => by
    have := congrArg Prod.snd h
    simp at this
  out_mate := fun d => rfl

theorem molOfArcs_atom_true (n : ℕ) (L : List (Fin n × Fin n)) (i : Fin L.length) :
    (molOfArcs n L).atom (i, true) = (L.get i).1 := rfl

theorem molOfArcs_atom_false (n : ℕ) (L : List (Fin n × Fin n)) (i : Fin L.length) :
    (molOfArcs n L).atom (i, false) = (L.get i).2 := rfl

/-- An isomorphism from the molecule of a garden to `molOfArcs n L`, from a labelling and a bond
enumeration realizing `L`. -/
theorem exists_iso_arcs {w : ℕ} (G : Garden w) {n : ℕ} (ℓ : GBranch G.tree ≃ Fin n)
    (L : List (Fin n × Fin n))
    (e : {x : GardenDart G // G.molecule.out x = true} ≃ Fin L.length)
    (he : ∀ x, L.get (e x) = (ℓ (G.molecule.atom x.1), ℓ (G.molecule.atom (G.molecule.mate x.1)))) :
    Nonempty (GardenMoleculeIso G (molOfArcs n L)) := by
  classical
  have hmo : ∀ x : GardenDart G, G.molecule.out x = false → G.molecule.out (G.molecule.mate x) = true := by
    intro x hx; rw [G.molecule.out_mate, hx]; rfl
  let toD : GardenDart G → Fin L.length × Bool := fun x =>
    if h : G.molecule.out x = true then (e ⟨x, h⟩, true)
    else (e ⟨G.molecule.mate x, hmo x (by simpa using h)⟩, false)
  let ofD : Fin L.length × Bool → GardenDart G := fun d =>
    if d.2 then (e.symm d.1).1 else G.molecule.mate (e.symm d.1).1
  have h1 : ∀ x, ofD (toD x) = x := by
    intro x
    by_cases h : G.molecule.out x = true
    · simp [toD, ofD, h]
    · simp only [toD, ofD, h, dif_neg, not_false_eq_true]
      simp [G.molecule.mate_mate]
  have h2 : ∀ d, toD (ofD d) = d := by
    rintro ⟨i, b⟩
    cases b
    · have ho : G.molecule.out (G.molecule.mate (e.symm i).1) = false := by
        rw [G.molecule.out_mate, (e.symm i).2]; rfl
      simp [toD, ofD, ho, G.molecule.mate_mate]
    · simp [toD, ofD, (e.symm i).2]
  refine ⟨{ branches := ℓ.trans (Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _)).symm
            darts := ⟨toD, ofD, h1, h2⟩
            atom_comm := ?_
            mate_comm := ?_
            out_comm := ?_ }⟩
  · intro x
    by_cases h : G.molecule.out x = true
    · simp only [Equiv.coe_fn_mk, toD, dif_pos h, molOfArcs_atom_true, he]
      rfl
    · simp only [Equiv.coe_fn_mk, toD, dif_neg h, molOfArcs_atom_false]
      have := he ⟨G.molecule.mate x, hmo x (by simpa using h)⟩
      simp only [G.molecule.mate_mate] at this
      rw [this]; rfl
  · intro x
    by_cases h : G.molecule.out x = true
    · have ho : G.molecule.out (G.molecule.mate x) = false := by rw [G.molecule.out_mate, h]; rfl
      simp [Equiv.coe_fn_mk, toD, h, ho, molOfArcs, G.molecule.mate_mate]
    · have ho : G.molecule.out (G.molecule.mate x) = true := hmo x (by simpa using h)
      simp [Equiv.coe_fn_mk, toD, h, ho, molOfArcs, G.molecule.mate_mate]
  · intro x
    by_cases h : G.molecule.out x = true
    · simp [Equiv.coe_fn_mk, toD, h, molOfArcs]
    · simp [Equiv.coe_fn_mk, toD, h, molOfArcs]

/-- The number of positions of a list carrying a given value is its count. -/
theorem card_filter_get {X : Type*} [DecidableEq X] (L : List X) (x : X) :
    (Finset.univ.filter (fun i : Fin L.length => L.get i = x)).card = L.count x := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [Finset.card_filter]
    show (∑ i : Fin (L.length + 1), if (a :: L).get i = x then 1 else 0) = _
    rw [Fin.sum_univ_succ]
    have h2 := Finset.card_filter (fun i : Fin L.length => L.get i = x) Finset.univ
    rw [ih] at h2
    have hs : ∀ i : Fin L.length, (a :: L).get i.succ = L.get i := fun i => rfl
    have h0 : (a :: L).get 0 = a := rfl
    simp only [hs, h0]
    rw [List.count_cons, h2]
    by_cases hax : a = x
    · simp [hax, add_comm]
    · simp [hax]

/-- Two finite families with the same fibre cardinalities are enumerated compatibly. -/
theorem exists_equiv_of_count_eq {B X : Type*} [Fintype B] [Fintype X] [DecidableEq X] (f : B → X)
    (L : List X) (h : ∀ x, Fintype.card {b // f b = x} = L.count x) :
    ∃ e : B ≃ Fin L.length, ∀ b, L.get (e b) = f b := by
  classical
  have hc : ∀ x, Fintype.card {b // f b = x} = Fintype.card {i : Fin L.length // L.get i = x} := by
    intro x
    rw [h x, Fintype.card_subtype, card_filter_get]
  let φ : ∀ x, {b // f b = x} ≃ {i : Fin L.length // L.get i = x} := fun x => Fintype.equivOfCardEq (hc x)
  let eB := Equiv.sigmaFiberEquiv f
  let eL := Equiv.sigmaFiberEquiv (fun i : Fin L.length => L.get i)
  refine ⟨eB.symm.trans ((Equiv.sigmaCongrRight φ).trans eL), fun b => ?_⟩
  have : (eB.symm b) = ⟨f b, ⟨b, rfl⟩⟩ := by
    apply eB.injective
    simp [eB]
  simp only [Equiv.trans_apply, this, Equiv.sigmaCongrRight_apply, eL, Equiv.sigmaFiberEquiv_apply]
  exact (φ (f b) ⟨b, rfl⟩).2

/-- **Arc lists of gardens**: a labelling `ℓ` and a list `L` with the same arc counts as the bonds of `G`
give an isomorphism `GardenMoleculeIso G (molOfArcs n L)`. -/
theorem exists_iso_arcs_of_count {w : ℕ} (G : Garden w) {n : ℕ} (ℓ : GBranch G.tree ≃ Fin n)
    (L : List (Fin n × Fin n))
    (h : ∀ x : Fin n × Fin n,
      Fintype.card {b : {y : GardenDart G // G.molecule.out y = true} //
        (ℓ (G.molecule.atom b.1), ℓ (G.molecule.atom (G.molecule.mate b.1))) = x} = L.count x) :
    Nonempty (GardenMoleculeIso G (molOfArcs n L)) := by
  classical
  obtain ⟨e, he⟩ := exists_equiv_of_count_eq
    (fun b : {y : GardenDart G // G.molecule.out y = true} =>
      (ℓ (G.molecule.atom b.1), ℓ (G.molecule.atom (G.molecule.mate b.1)))) L h
  exact exists_iso_arcs G ℓ L e he

/-- The atoms of the molecule of a garden are the branching nodes. -/
def atomsEquiv {w : ℕ} (G : Garden w) : GBranch G.tree ≃ G.molecule.atoms where
  toFun := fun x => ⟨x, Finset.mem_univ x⟩
  invFun := fun x => x.1
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Two garden isomorphisms to a common molecule compose to an isomorphism between the gardens' molecules. -/
noncomputable def gardenIsoOfCommon {w : ℕ} {G G0 : Garden w} {V D : Type*} [DecidableEq V] [Fintype D]
    {M : Molecule V D} (f : GardenMoleculeIso G M) (f0 : GardenMoleculeIso G0 M) :
    GardenMoleculeIso G G0.molecule where
  branches := f.branches.trans (f0.branches.symm.trans (atomsEquiv G0))
  darts := f.darts.trans f0.darts.symm
  atom_comm := by
    intro x
    have h1 := f.atom_comm x
    have h2 := f0.atom_comm (f0.darts.symm (f.darts x))
    rw [Equiv.apply_symm_apply] at h2
    have h3 : f0.branches (G0.molecule.atom (f0.darts.symm (f.darts x))) = f.branches (G.molecule.atom x) :=
      Subtype.ext (h2.symm.trans h1)
    simp only [Equiv.trans_apply]
    rw [← h3]
    simp [atomsEquiv]
  mate_comm := by
    intro x
    simp only [Equiv.trans_apply]
    have h := f0.mate_comm (f0.darts.symm (f.darts x))
    rw [Equiv.apply_symm_apply] at h
    have h' := f.mate_comm x
    have : f0.darts (G0.molecule.mate (f0.darts.symm (f.darts x))) = f.darts (G.molecule.mate x) :=
      h.symm.trans h'
    rw [← this]; simp
  out_comm := by
    intro x
    have h1 := f.out_comm x
    have h2 := f0.out_comm (f0.darts.symm (f.darts x))
    rw [Equiv.apply_symm_apply] at h2
    simp only [Equiv.trans_apply]
    exact h2.symm.trans h1

/-- **Counting gardens through arc lists.**  If every garden of `A` (plain, of order `n`) is isomorphic to
`molOfArcs n L` for some `L ∈ 𝓛`, then `#A ≤ #𝓛 · (20736 R)! · 20736^n` (TARGET `propcplmol`). -/
theorem card_le_of_arc_lists {R n : ℕ} (𝓛 : Finset (List (Fin n × Fin n)))
    (A : Finset (Garden (2 * R)))
    (hA : ∀ G ∈ A, G.IsPlain ∧ G.order = n ∧ ∃ L ∈ 𝓛, Nonempty (GardenMoleculeIso G (molOfArcs n L))) :
    A.card ≤ 𝓛.card * ((20736 * R).factorial * 20736 ^ n) := by
  classical
  have hcover : A ⊆ 𝓛.biUnion (fun L => A.filter fun G => Nonempty (GardenMoleculeIso G (molOfArcs n L))) := by
    intro G hG
    obtain ⟨-, -, L, hL, hiso⟩ := hA G hG
    exact Finset.mem_biUnion.mpr ⟨L, hL, Finset.mem_filter.mpr ⟨hG, hiso⟩⟩
  have hfib : ∀ L ∈ 𝓛, (A.filter fun G => Nonempty (GardenMoleculeIso G (molOfArcs n L))).card ≤
      (20736 * R).factorial * 20736 ^ n := by
    intro L hL
    set AL := A.filter fun G => Nonempty (GardenMoleculeIso G (molOfArcs n L)) with hAL
    rcases AL.eq_empty_or_nonempty with he | ⟨G0, hG0⟩
    · rw [he]; simp
    · obtain ⟨hG0A, ⟨f0⟩⟩ := Finset.mem_filter.mp hG0
      have hbound := garden_reconstruction_bound_fixed_order G0.molecule (Mole.garden_isMolecule G0) n R
      let T := {G : Garden (2 * R) // G.IsPlain ∧ G.order = n ∧ Nonempty (GardenMoleculeIso G G0.molecule)}
      have : Finite (GardensWithMolecule G0.molecule (2 * R)) := finite_gardensWithMolecule _ _
      have : Finite T := Finite.of_injective
        (fun G : T => (⟨G.1, G.2.1, G.2.2.2⟩ : GardensWithMolecule G0.molecule (2 * R)))
        (fun a b h => Subtype.ext (congrArg (fun x : GardensWithMolecule G0.molecule (2 * R) => x.1) h))
      let F : AL → T := fun G =>
        have hG := Finset.mem_filter.mp G.2
        ⟨G.1, (hA G.1 hG.1).1, (hA G.1 hG.1).2.1, ⟨gardenIsoOfCommon hG.2.some f0⟩⟩
      have hF : Function.Injective F := fun a b h => Subtype.ext (congrArg (fun x : T => x.1) h)
      have := Nat.card_le_card_of_injective F hF
      rw [Nat.card_eq_fintype_card, Fintype.card_coe] at this
      exact this.trans hbound
  calc A.card ≤ (𝓛.biUnion (fun L => A.filter fun G => Nonempty (GardenMoleculeIso G (molOfArcs n L)))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ L ∈ 𝓛, (A.filter fun G => Nonempty (GardenMoleculeIso G (molOfArcs n L))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ L ∈ 𝓛, (20736 * R).factorial * 20736 ^ n := Finset.sum_le_sum hfib
    _ = 𝓛.card * ((20736 * R).factorial * 20736 ^ n) := by simp

end WaveTurbulence.ClassCount
