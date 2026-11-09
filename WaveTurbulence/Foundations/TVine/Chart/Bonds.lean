/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.Contract

/-!
# Internal bonds of an atomic group: ends, incidences, degrees, cut sums, local embeddings

Basic API over main's `VineParamContract.Bond M S` (the internal bonds of `S`, each named by its outgoing dart):
* `tl e`, `hd e`: the tail and head atom of a bond; `incidence M v e = [tl e = v] − [hd e = v]`;
* the tail and head counts at `v` are `M.outIn S v` and `M.inIn S v`; in a molecule every atom of degree 4 within
  `S` is balanced (`2` in, `2` out), and so is every joint of a block;
* the flow out of a set `X` is the sum of the labels of the bonds leaving `X` minus those entering it;
* a **local embedding** of a small directed graph with external stubs into `S` (all bonds of `S` at the embedded
  atoms are images of local bonds) transports incidence sums and energies to local sums.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

variable {V D : Type*} [DecidableEq V] [Fintype D]

section Basic

variable {M : Molecule V D} {S : Finset V}

/-- The tail atom of an internal bond. -/
def tl (e : Bond M S) : V := M.atom e.1

/-- The head atom of an internal bond. -/
def hd (e : Bond M S) : V := M.atom (M.mate e.1)

theorem bond_spec (e : Bond M S) : M.out e.1 = true ∧ M.InGroup S e.1 := by
  have h := e.2
  unfold internalBondSet at h
  classical
  simp only [Molecule.bonds, mem_filter, mem_univ, true_and] at h
  convert h using 2

theorem tl_mem (e : Bond M S) : tl e ∈ S := (bond_spec e).2.1

theorem hd_mem (e : Bond M S) : hd e ∈ S := (bond_spec e).2.2

theorem incidence_eq (v : V) (e : Bond M S) :
    incidence M v e.1 = (if tl e = v then 1 else 0) - (if hd e = v then 1 else 0) := rfl

/-- A dart of `S` that is outgoing is an internal bond. -/
theorem mem_internalBondSet {x : D} (hout : M.out x = true) (hS : M.InGroup S x) :
    x ∈ internalBondSet M S := by
  classical
  unfold internalBondSet
  simp only [Molecule.bonds, mem_filter, mem_univ, true_and]
  convert And.intro hout hS using 2

/-- The number of internal bonds with tail `v` is the out-degree of `v` within `S`. -/
theorem card_tl (v : V) :
    ((univ : Finset (Bond M S)).filter fun e => tl e = v).card = M.outIn S v := by
  classical
  unfold Molecule.outIn
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    have hs := bond_spec e
    simp only [mem_filter, mem_univ, true_and] at he
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]
    exact ⟨he, hs.2, hs.1⟩
  · intro e _ f _ h
    exact Subtype.ext h
  · intro x hx
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and] at hx
    refine ⟨⟨x, mem_internalBondSet hx.2.2 hx.2.1⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    exact hx.1

/-- The number of internal bonds with head `v` is the in-degree of `v` within `S`. -/
theorem card_hd (v : V) :
    ((univ : Finset (Bond M S)).filter fun e => hd e = v).card = M.inIn S v := by
  classical
  unfold Molecule.inIn
  apply Finset.card_bij (fun e _ => M.mate e.1)
  · intro e he
    have hs := bond_spec e
    simp only [mem_filter, mem_univ, true_and] at he
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]
    refine ⟨he, ⟨hs.2.2, by rw [M.mate_mate]; exact hs.2.1⟩, ?_⟩
    rw [M.out_mate, hs.1]; rfl
  · intro e _ f _ h
    apply Subtype.ext
    have := congrArg M.mate h
    simpa only [M.mate_mate] using this
  · intro x hx
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and] at hx
    have hout : M.out (M.mate x) = true := by rw [M.out_mate, hx.2.2]; rfl
    have hS : M.InGroup S (M.mate x) := ⟨hx.2.1.2, by rw [M.mate_mate]; exact hx.2.1.1⟩
    refine ⟨⟨M.mate x, mem_internalBondSet hout hS⟩, ?_, by simp [M.mate_mate]⟩
    rw [Finset.mem_filter]
    refine ⟨mem_univ _, ?_⟩
    show M.atom (M.mate (M.mate x)) = v
    rw [M.mate_mate]
    exact hx.1

/-- The incidence sum at an atom is its out-degree minus its in-degree within `S`. -/
theorem sum_incidence (v : V) :
    (∑ e : Bond M S, incidence M v e.1) = (M.outIn S v : ℤ) - M.inIn S v := by
  classical
  simp only [incidence_eq, Finset.sum_sub_distrib, Finset.sum_boole]
  rw [card_tl, card_hd]

/-- The degree within `S` splits into out- and in-degree. -/
theorem degIn_eq (v : V) : M.degIn S v = M.outIn S v + M.inIn S v := by
  classical
  unfold Molecule.degIn Molecule.outIn Molecule.inIn
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [mem_filter, mem_union]
    cases M.out x <;> simp
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    rw [h1.2] at h2
    exact Bool.noConfusion h2.2

/-- In a molecule, an atom of degree `4` within `S` has two outgoing and two incoming bonds in `S`. -/
theorem balanced_of_deg4 (hM : M.IsMolecule) {v : V} (hv : v ∈ M.atoms) (h4 : M.degIn S v = 4) :
    M.outIn S v = 2 ∧ M.inIn S v = 2 := by
  classical
  have ho : M.outIn S v ≤ 2 := by
    refine le_trans ?_ (hM.1 v hv).1
    unfold Molecule.outIn Molecule.outdeg
    exact Finset.card_le_card (fun x hx => by
      simp only [mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.2⟩)
  have hi : M.inIn S v ≤ 2 := by
    refine le_trans ?_ (hM.1 v hv).2
    unfold Molecule.inIn Molecule.indeg
    exact Finset.card_le_card (fun x hx => by
      simp only [mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.2⟩)
  have := degIn_eq (M := M) (S := S) v
  omega

/-- In a molecule, every atom of a block is balanced: the incidence sum vanishes. -/
theorem sum_incidence_block (hM : M.IsMolecule) {a b : V} (hB : M.IsBlock S a b) {v : V} (hv : v ∈ S) :
    (∑ e : Bond M S, incidence M v e.1) = 0 := by
  rw [sum_incidence]
  by_cases ha : v = a
  · subst ha; rw [hB.2.2.2.2.1, hB.2.2.2.2.2.1]; simp
  by_cases hb : v = b
  · subst hb; rw [hB.2.2.2.2.2.2.1, hB.2.2.2.2.2.2.2.1]; simp
  have := balanced_of_deg4 hM (hB.1 hv) (hB.2.2.2.2.2.2.2.2.1 v hv ha hb)
  rw [this.1, this.2]; simp

/-- The sum of the incidences of a bond over a set of atoms. -/
theorem sum_incidence_set (X : Finset V) (e : Bond M S) :
    (∑ v ∈ X, incidence M v e.1) = (if tl e ∈ X then 1 else 0) - (if hd e ∈ X then 1 else 0) := by
  classical
  simp only [incidence_eq, Finset.sum_sub_distrib, Finset.sum_ite_eq]

/-- **The flow out of a set** is the sum over bonds leaving it minus the sum over bonds entering it (internal
bonds of the set cancel). -/
theorem sum_flow_set {E : Type*} [AddCommGroup E] (X : Finset V) (k : Bond M S → E) :
    (∑ v ∈ X, flow M S k v) =
      ∑ e : Bond M S, ((if tl e ∈ X then (1 : ℤ) else 0) - (if hd e ∈ X then 1 else 0)) • k e := by
  unfold flow
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [← Finset.sum_smul, sum_incidence_set]

end Basic

/-! ## Local embeddings -/

/-- A small directed graph with external stubs: `nA` atoms, `nB` bonds, each with a tail and a head that is a
local atom or `none` (outside). -/
structure LocalGraph where
  nA : ℕ
  nB : ℕ
  src : Fin nB → Option (Fin nA)
  dst : Fin nB → Option (Fin nA)

namespace LocalGraph

/-- The local incidence (out − in) of the local bond `l` at the local atom `u`. -/
def inc (G : LocalGraph) (u : Fin G.nA) (l : Fin G.nB) : ℤ :=
  (if G.src l = some u then 1 else 0) - (if G.dst l = some u then 1 else 0)

end LocalGraph

variable {M : Molecule V D} {S : Finset V}

/-- **A local embedding** of `G` into the internal bonds of `S`: injective on atoms and bonds, preserving tails and
heads, mapping stubs to bonds whose outer end is not an embedded atom, and complete (every bond of `S` at an
embedded atom is the image of a local bond). -/
structure LocEmb (G : LocalGraph) (M : Molecule V D) (S : Finset V) where
  atom : Fin G.nA → V
  bond : Fin G.nB → Bond M S
  atom_inj : Function.Injective atom
  bond_inj : Function.Injective bond
  tl_eq : ∀ l u, G.src l = some u → tl (bond l) = atom u
  tl_out : ∀ l, G.src l = none → ∀ u, tl (bond l) ≠ atom u
  hd_eq : ∀ l u, G.dst l = some u → hd (bond l) = atom u
  hd_out : ∀ l, G.dst l = none → ∀ u, hd (bond l) ≠ atom u
  complete : ∀ u (e : Bond M S), tl e = atom u ∨ hd e = atom u → ∃ l, bond l = e

namespace LocEmb

variable {G : LocalGraph} (φ : LocEmb G M S)

theorem tl_iff (l : Fin G.nB) (u : Fin G.nA) : tl (φ.bond l) = φ.atom u ↔ G.src l = some u := by
  constructor
  · intro h
    cases hs : G.src l with
    | none => exact absurd h (φ.tl_out l hs u)
    | some w => rw [φ.tl_eq l w hs] at h; rw [φ.atom_inj h]
  · intro h; exact φ.tl_eq l u h

theorem hd_iff (l : Fin G.nB) (u : Fin G.nA) : hd (φ.bond l) = φ.atom u ↔ G.dst l = some u := by
  constructor
  · intro h
    cases hs : G.dst l with
    | none => exact absurd h (φ.hd_out l hs u)
    | some w => rw [φ.hd_eq l w hs] at h; rw [φ.atom_inj h]
  · intro h; exact φ.hd_eq l u h

theorem incidence_bond (u : Fin G.nA) (l : Fin G.nB) :
    incidence M (φ.atom u) (φ.bond l).1 = G.inc u l := by
  rw [incidence_eq]
  unfold LocalGraph.inc
  have h1 := φ.tl_iff l u
  have h2 := φ.hd_iff l u
  by_cases a1 : tl (φ.bond l) = φ.atom u <;> by_cases a2 : hd (φ.bond l) = φ.atom u <;>
    simp_all

/-- **Transfer of incidence sums** to the local graph. -/
theorem sum_transfer {β : Type*} [AddCommMonoid β] (f : ℤ → Bond M S → β) (hf : ∀ e, f 0 e = 0)
    (u : Fin G.nA) :
    (∑ e : Bond M S, f (incidence M (φ.atom u) e.1) e) = ∑ l, f (G.inc u l) (φ.bond l) := by
  classical
  have himg : (∑ e ∈ (univ : Finset (Fin G.nB)).image φ.bond, f (incidence M (φ.atom u) e.1) e) =
      ∑ l, f (incidence M (φ.atom u) (φ.bond l).1) (φ.bond l) :=
    Finset.sum_image (fun x _ y _ h => φ.bond_inj h)
  rw [← Finset.sum_subset (Finset.subset_univ _), himg]
  · exact Finset.sum_congr rfl (fun l _ => by rw [φ.incidence_bond])
  · intro e _ he
    have hz : incidence M (φ.atom u) e.1 = 0 := by
      rw [incidence_eq]
      have hn : ¬ (tl e = φ.atom u ∨ hd e = φ.atom u) := by
        rintro h
        obtain ⟨l, rfl⟩ := φ.complete u e h
        exact he (Finset.mem_image_of_mem _ (mem_univ l))
      have h1 : tl e ≠ φ.atom u := fun h => hn (Or.inl h)
      have h2 : hd e ≠ φ.atom u := fun h => hn (Or.inr h)
      simp [h1, h2]
    rw [hz, hf]

/-- Transfer of the flow at an embedded atom. -/
theorem flow_transfer {E : Type*} [AddCommGroup E] (k : Bond M S → E) (u : Fin G.nA) :
    flow M S k (φ.atom u) = ∑ l, G.inc u l • k (φ.bond l) := by
  unfold flow
  exact φ.sum_transfer (fun z e => z • k e) (fun e => zero_smul _ _) u

/-- Transfer of the energy at an embedded atom. -/
theorem energy_transfer {d : ℕ} (k : Bond M S → Mom d) (u : Fin G.nA) :
    energy M S k (φ.atom u) = ∑ l, -(G.inc u l : ℝ) * ‖k (φ.bond l)‖ ^ 2 := by
  unfold energy
  exact φ.sum_transfer (fun z e => -(z : ℝ) * ‖k e‖ ^ 2) (fun e => by simp) u

end LocEmb

end WaveTurbulence.TVine.Chart
