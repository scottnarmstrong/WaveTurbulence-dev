/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Prop96Statement
public import WaveTurbulence.Foundations.FinalCount.P101.Main
public import WaveTurbulence.Foundations.FinalCount.OpCChain
import Mathlib.Tactic

/-! # Prop 9.6: structural lemmas for chains (step (d), part 1)

* `connected_erase_of_two_cross`: in a connected molecule with all degrees even, removing a set `K` with exactly two cross
  darts leaves a connected molecule (parity of the degree sum of a component).
* `pmol_erase_of_connected`: erasing a nonempty set from a connected molecule with caps leaves a `PMol`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8.P101

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem exists_boundary_of_connected (M : Molecule V D)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) (S : Finset V) (hS : S ⊆ M.atoms)
    (hne : S.Nonempty) (hproper : ∃ z ∈ M.atoms, z ∉ S) : (Degen.boundaryDarts M S).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  obtain ⟨s, hs⟩ := hne
  obtain ⟨z, hz, hzS⟩ := hproper
  have hstep : ∀ x : D, M.atom x ∈ S → M.atom (M.mate x) ∈ S := by
    intro x hx
    by_contra hw
    have : x ∈ Degen.boundaryDarts M S := by
      simp only [Degen.boundaryDarts, mem_filter, mem_univ, true_and]
      exact ⟨hx, hw⟩
    rw [hempty] at this; simp at this
  have hclosed : ∀ c d, M.SameComponent c d → (c ∈ S ↔ d ∈ S) := by
    intro c d h
    unfold Molecule.SameComponent at h
    induction h with
    | rel u w huw =>
      obtain ⟨x, hx1, hx2⟩ := huw
      constructor
      · intro hu; exact hx2 ▸ hstep x (hx1 ▸ hu)
      · intro hw
        have := hstep (M.mate x) (by rw [hx2]; exact hw)
        rw [M.mate_mate, hx1] at this; exact this
    | refl u => exact Iff.rfl
    | symm u w _ ih => exact ih.symm
    | trans u w t _ _ ih1 ih2 => exact ih1.trans ih2
  exact hzS ((hclosed s z (hconn s (hS hs) z hz)).mp hs)


/-- The mates of the boundary darts of a union of components of `M ∖ K` are cross darts of `K`. -/
theorem bd_mate_cross (M : Molecule V D) (K S : Finset V) (hS : S ⊆ M.atoms \ K)
    (hclosed : ∀ x : D, M.atom x ∈ S → M.atom (M.mate x) ∈ M.atoms \ K → M.atom (M.mate x) ∈ S) :
    ∀ x ∈ Degen.boundaryDarts M S, M.mate x ∈ crossDarts M K := by
  intro x hx
  simp only [Degen.boundaryDarts, mem_filter, mem_univ, true_and] at hx
  rw [mem_crossDarts, M.mate_mate]
  refine ⟨?_, fun h => ?_⟩
  · by_contra hK
    exact hx.2 (hclosed x hx.1 (mem_sdiff.mpr ⟨M.atom_mem _, hK⟩))
  · exact (mem_sdiff.mp (hS hx.1)).2 h

theorem connected_erase_of_two_cross (M : Molecule V D)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) (heven : ∀ a ∈ M.atoms, M.deg a % 2 = 0)
    (K : Finset V) (hcross : (crossDarts M K).card = 2) :
    ∀ a ∈ (Degen.eraseAtoms M K).atoms, ∀ b ∈ (Degen.eraseAtoms M K).atoms,
      (Degen.eraseAtoms M K).SameComponent a b := by
  classical
  intro a ha b hb
  by_contra hab
  set N := Degen.eraseAtoms M K with hN
  have hT : N.atoms = M.atoms \ K := rfl
  set C : Finset V := N.atoms.filter (fun c => N.SameComponent a c) with hC
  set R : Finset V := N.atoms.filter (fun c => ¬ N.SameComponent a c) with hR
  have hCT : C ⊆ M.atoms \ K := fun c hc => hT ▸ (mem_filter.mp hc).1
  have hRT : R ⊆ M.atoms \ K := fun c hc => hT ▸ (mem_filter.mp hc).1
  have hAdjN : ∀ x : D, M.atom x ∈ M.atoms \ K → M.atom (M.mate x) ∈ M.atoms \ K →
      N.SameComponent (M.atom x) (M.atom (M.mate x)) := by
    intro x h1 h2
    exact Relation.EqvGen.rel _ _ ⟨⟨x, (mem_sdiff.mp h1).2, (mem_sdiff.mp h2).2⟩, rfl, rfl⟩
  have hCcl : ∀ x : D, M.atom x ∈ C → M.atom (M.mate x) ∈ M.atoms \ K → M.atom (M.mate x) ∈ C := by
    intro x hx hy
    obtain ⟨hx1, hx2⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hT ▸ hy, Relation.EqvGen.trans _ _ _ hx2 (hAdjN x (hCT hx) hy)⟩
  have hRcl : ∀ x : D, M.atom x ∈ R → M.atom (M.mate x) ∈ M.atoms \ K → M.atom (M.mate x) ∈ R := by
    intro x hx hy
    obtain ⟨hx1, hx2⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨hT ▸ hy, fun h => hx2 ?_⟩
    have h' : N.SameComponent (M.atom (M.mate x)) (M.atom x) := by
      have := hAdjN (M.mate x) hy (by rw [M.mate_mate]; exact hT ▸ hx1)
      simpa [M.mate_mate] using this
    exact Relation.EqvGen.trans _ _ _ h h'
  have haC : a ∈ C := mem_filter.mpr ⟨ha, Relation.EqvGen.refl _⟩
  have hbR : b ∈ R := mem_filter.mpr ⟨hb, hab⟩
  have hbnC : b ∉ C := fun h => hab (mem_filter.mp h).2
  have hCne : (Degen.boundaryDarts M C).Nonempty :=
    exists_boundary_of_connected M hconn C (fun c hc => (mem_sdiff.mp (hCT hc)).1) ⟨a, haC⟩
      ⟨b, (mem_sdiff.mp (hRT hbR)).1, hbnC⟩
  have hRne : (Degen.boundaryDarts M R).Nonempty :=
    exists_boundary_of_connected M hconn R (fun c hc => (mem_sdiff.mp (hRT hc)).1) ⟨b, hbR⟩
      ⟨a, (mem_sdiff.mp (hCT haC)).1, fun h => (mem_filter.mp h).2 (Relation.EqvGen.refl _)⟩
  have hdisj : Disjoint (Degen.boundaryDarts M C) (Degen.boundaryDarts M R) := by
    rw [Finset.disjoint_left]
    intro x hxC hxR
    simp only [Degen.boundaryDarts, mem_filter, mem_univ, true_and] at hxC hxR
    exact (mem_filter.mp hxR.1).2 (mem_filter.mp hxC.1).2
  have hsub : ((Degen.boundaryDarts M C ∪ Degen.boundaryDarts M R).image M.mate) ⊆ crossDarts M K := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    rcases mem_union.mp hx with h | h
    · exact bd_mate_cross M K C hCT hCcl x h
    · exact bd_mate_cross M K R hRT hRcl x h
  have hinj : Function.Injective M.mate := fun x y h => by
    have := congrArg M.mate h; simpa [M.mate_mate] using this
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ hinj, card_union_of_disjoint hdisj, hcross] at hcard
  have h1 : (Degen.boundaryDarts M C).card = 1 := by
    have := card_pos.mpr hCne; have := card_pos.mpr hRne; omega
  have hsum := Degen.sum_degrees_cut M C
  rw [h1] at hsum
  have hev : (∑ z ∈ C, M.deg z) % 2 = 0 := by
    rw [Finset.sum_nat_mod]
    have : ∀ z ∈ C, M.deg z % 2 = 0 := fun z hz => heven z (mem_sdiff.mp (hCT hz)).1
    rw [Finset.sum_congr rfl this]; simp
  omega


theorem pmol_erase_of_connected {M : Molecule V D} {B : Finset V} (hcaps : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2)
    (hprot : ∀ v ∈ M.atoms, v ∈ B → M.deg v ≤ 2)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) (Y : Finset V) (hY : Y ⊆ M.atoms)
    (hYne : Y.Nonempty) : PMol B (Degen.eraseAtoms M Y) := by
  classical
  have hdeg : ∀ v ∈ M.atoms, M.deg v ≤ cap B v := by
    intro v hv
    have h1 := hcaps v hv
    have he := Mole.outdeg_add_indeg M v
    unfold cap
    split_ifs with hB
    · exact hprot v hv hB
    · omega
  constructor
  · intro z hz
    have ho := Degen.card_filtered_dartsAt_erase_le M Y z (fun x => M.out x = true)
    have hi := Degen.card_filtered_dartsAt_erase_le M Y z (fun x => M.out x = false)
    exact ⟨ho.trans (hcaps z (mem_sdiff.mp hz).1).1, hi.trans (hcaps z (mem_sdiff.mp hz).1).2⟩
  · intro z hz hzB
    have he := Degen.deg_eraseAtoms_add_removed M Y (mem_sdiff.mp hz).2
    have := hprot z (mem_sdiff.mp hz).1 hzB
    omega
  · intro z hz
    by_contra hn
    have hsat (a : V) (ha : a ∈ (Degen.eraseAtoms M Y).atoms)
        (hza : (Degen.eraseAtoms M Y).SameComponent z a) : (Degen.eraseAtoms M Y).deg a = cap B a := by
      by_contra hne
      exact hn ⟨a, ha, hza, hne⟩
    let C := fun a => a ∈ (Degen.eraseAtoms M Y).atoms ∧ (Degen.eraseAtoms M Y).SameComponent z a
    have hclosed (a b : V) (hab : M.Adj a b) (ha : C a) : C b := by
      obtain ⟨hb, hab'⟩ := adj_erase_of_surviving_sat hdeg Y ha.1 (hsat a ha.1 ha.2) hab
      exact ⟨hb, Relation.EqvGen.trans _ _ _ ha.2 (Relation.EqvGen.rel _ _ hab')⟩
    have hpath (a b : V) (hab : M.SameComponent a b) : C a ↔ C b := by
      induction hab with
      | rel a b h => exact ⟨hclosed a b h, hclosed b a (Mole.adj_symmetric M h)⟩
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
    obtain ⟨y, hy⟩ := hYne
    have hCy := (hpath z y (hconn z (mem_sdiff.mp hz).1 y (hY hy))).mp ⟨hz, Relation.EqvGen.refl z⟩
    exact (mem_sdiff.mp hCy.1).2 hy

theorem chain_piece_connected {M : Molecule V D} {cls : V → Cls} {K : Finset V} (hK : IsChainSet M cls K) :
    ∀ a ∈ K, ∀ b ∈ K, (piece M K).SameComponent a b := by
  classical
  intro a ha b hb
  have hKA : K ⊆ M.atoms := hK.2.1
  have hall : ∀ u v, u ∈ K → v ∈ K → M.Adj u v → (piece M K).Adj u v := by
    intro u v hu hv ⟨x, hx1, hx2⟩
    exact ⟨pieceDart M K x ⟨hx1 ▸ hu, hx2 ▸ hv⟩, hx1, hx2⟩
  have := hK.2.2.2.2 a ha b hb
  clear ha hb
  unfold Molecule.SameComponent
  induction this with
  | rel u v h => exact Relation.EqvGen.rel _ _ (hall u v h.1 h.2.1 h.2.2)
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem exists_chainSet (M : Molecule V D) (cls : V → Cls) {b : V} (hb : b ∈ M.atoms) (hbn : ¬ (cls b).IsEps) :
    ∃ K, IsChainSet M cls K ∧ b ∈ K := by
  classical
  let r : V → V → Prop := fun x y => ¬ (cls x).IsEps ∧ ¬ (cls y).IsEps ∧ M.Adj x y
  have hrsymm : ∀ x y, r x y → r y x := fun x y h => ⟨h.2.1, h.1, Mole.adj_symmetric M h.2.2⟩
  let K : Finset V := M.atoms.filter fun v => Relation.ReflTransGen r b v
  have hreach : ∀ v, Relation.ReflTransGen r b v → ¬ (cls v).IsEps := by
    intro v h
    induction h with
    | refl => exact hbn
    | tail _ h2 _ => exact h2.2.1
  have hKmem : ∀ v, v ∈ K ↔ v ∈ M.atoms ∧ Relation.ReflTransGen r b v := fun v => mem_filter
  refine ⟨K, ⟨⟨b, (hKmem b).mpr ⟨hb, Relation.ReflTransGen.refl⟩⟩, filter_subset _ _,
    fun v hv => hreach v ((hKmem v).mp hv).2, ?_, ?_⟩, (hKmem b).mpr ⟨hb, Relation.ReflTransGen.refl⟩⟩
  · intro u hu v huv hvn
    have hu' := (hKmem u).mp hu
    refine (hKmem v).mpr ⟨?_, hu'.2.tail ⟨hreach u hu'.2, hvn, huv⟩⟩
    obtain ⟨x, hx1, hx2⟩ := huv
    exact hx2 ▸ M.atom_mem _
  · -- connectivity inside K
    have hrtg : ∀ {r' : V → V → Prop} {x y : V}, Relation.ReflTransGen r' x y → Relation.EqvGen r' x y := by
      intro r' x y h
      induction h with
      | refl => exact Relation.EqvGen.refl _
      | tail _ h2 ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ h2)
    have hchain : ∀ v, Relation.ReflTransGen r b v →
        Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ M.Adj x y) b v := by
      intro v h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail h1 h2 ih =>
        rename_i u w
        obtain ⟨x, hx1, hx2⟩ := h2.2.2
        have huA : u ∈ M.atoms := hx1 ▸ M.atom_mem x
        have hwA : w ∈ M.atoms := hx2 ▸ M.atom_mem _
        have hu : u ∈ K := (hKmem u).mpr ⟨huA, h1⟩
        have hw : w ∈ K := (hKmem w).mpr ⟨hwA, h1.tail h2⟩
        exact ih.tail ⟨hu, hw, x, hx1, hx2⟩
    intro u hu v hv
    have h1 := hrtg (hchain u ((hKmem u).mp hu).2)
    have h2 := hrtg (hchain v ((hKmem v).mp hv).2)
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h1) h2

end
end WaveTurbulence.FinalCountG8
