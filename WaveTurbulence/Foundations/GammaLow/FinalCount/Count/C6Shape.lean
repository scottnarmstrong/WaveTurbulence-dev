/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.OpEGen
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.OpEShape
import Mathlib.Tactic

/-! # The generalized theta chain in an ambient molecule (packet L6-COUNT, Case6TopLow)

`ThetaGenData N S p q a b z₁ z₂ C C'`: the removed set `S = {p, q} ∪ C ∪ C'` of operation (e), described by facts about
the ambient molecule `N`. From it:
* `ThetaGenData.isThetaGen_piece`: the piece `𝕄[S]` is an `IsThetaGen` (for `opE_gen_one`, `opE_gen_bound`);
* `ThetaGenData.isThetaGen_self`: if `S` is all of `N`, `N` itself is one (for `opE_gen_none`);
* `IsThetaGen.connected`: a generalized theta chain is connected;
* `ThetaGenData.card_cross_le`, `ThetaGenData.balanced`: at most two exits (one at `p`, one at `q`), and with two exits
  `S` is balanced (`p, q` of degree four with in/out caps two). -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount.Count
open WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The generalized theta chain, described in the ambient molecule `N`.** -/
structure ThetaGenData (N : Molecule V D) (S : Finset V) (p q : V) (a b z₁ z₂ : D) (C C' : Finset V) : Prop where
  sub : S ⊆ N.atoms
  hS : S = insert p (insert q (C ∪ C'))
  hpq : p ≠ q
  hpC : p ∉ C ∪ C'
  hqC : q ∉ C ∪ C'
  disj : Disjoint C C'
  ha : N.atom a = p
  hb : N.atom b = p
  hz₁ : N.atom z₁ = p
  hz₂ : N.atom z₂ = q
  hma : N.atom (N.mate a) = q
  hmb : (C' = ∅ ∧ N.atom (N.mate b) = q) ∨ N.atom (N.mate b) ∈ C'
  hab : a ≠ b
  hmz₁ : N.atom (N.mate z₁) ∈ C
  hmz₂ : N.atom (N.mate z₂) ∈ C
  pin : ∀ z, N.atom z = p → N.atom (N.mate z) ∈ S → z = a ∨ z = b ∨ z = z₁
  qdeg : (univ.filter fun z => N.atom z = q ∧ N.atom (N.mate z) ∈ S).card = 3
  signs : ¬ (N.out a = N.out b ∧ N.out b = N.out z₁)
  dir : N.out z₁ ≠ N.out z₂
  closed : ∀ z, N.atom z ∈ C ∪ C' → N.atom (N.mate z) ∈ S
  chain : ∀ v ∈ C ∪ C', N.outdeg v = 1 ∧ N.indeg v = 1
  crossC : ∀ z, N.atom z ∈ C → N.atom (N.mate z) ∉ C → z = N.mate z₁ ∨ z = N.mate z₂
  connC : ∀ u ∈ C, ∀ v ∈ C, (piece N C).SameComponent u v
  connC' : ∀ u ∈ C', ∀ v ∈ C', (piece N C').SameComponent u v
  noLoop : ∀ x, N.atom x ≠ N.atom (N.mate x)

/-- The degree of an atom of `S` in the piece `𝕄[S]`: its darts whose far end lies in `S`. -/
theorem piece_deg_eq_card {N : Molecule V D} {S : Finset V} {v : V} (hv : v ∈ S) :
    (piece N S).deg v = (univ.filter fun z => N.atom z = v ∧ N.atom (N.mate z) ∈ S).card := by
  classical
  unfold Molecule.deg
  refine card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and] at hx ⊢
    exact ⟨hx, (piece_dart_mem x).2⟩
  · intro x _ y _ h; exact Subtype.ext h
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz
    refine ⟨pieceDart N S z ⟨hz.1 ▸ hv, hz.2⟩, ?_, rfl⟩
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]
    exact hz.1

/-- Connectivity in an erasure is connectivity in the molecule. -/
theorem sameComponent_of_erase {N : Molecule V D} {Y : Finset V} {u v : V}
    (h : (Degen.eraseAtoms N Y).SameComponent u v) : N.SameComponent u v := by
  induction h with
  | rel a b hab =>
    obtain ⟨z, rfl, rfl⟩ := hab
    exact Relation.EqvGen.rel _ _ ⟨z.val, rfl, rfl⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- **A generalized theta chain is connected.** -/
theorem IsThetaGen.connected {M : Molecule V D} {p q : V} {a b z₁ z₂ : D} {C C' : Finset V}
    (h : IsThetaGen M p q a b z₁ z₂ C C') : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v := by
  classical
  have hp : ∀ u ∈ M.atoms, M.SameComponent p u := by
    intro u hu
    by_cases hup : u = p
    · rw [hup]; exact Relation.EqvGen.refl _
    by_cases huq : u = q
    · rw [huq]; exact Relation.EqvGen.rel _ _ ⟨a, h.atom_a, h.hma⟩
    have huC : u ∈ C ∪ C' := h.atoms_eq ▸ mem_sdiff.mpr ⟨hu, by simp [hup, huq]⟩
    rcases mem_union.mp huC with huC | huC'
    · have h1 : M.SameComponent p (M.atom (M.mate z₁)) := Relation.EqvGen.rel _ _ ⟨z₁, h.atom_z₁, rfl⟩
      exact Relation.EqvGen.trans _ _ _ h1 (sameComponent_of_erase (h.connC _ h.z₁in u huC))
    · rcases h.hmb with ⟨hC', _⟩ | hbC'
      · rw [hC'] at huC'; simp at huC'
      · have h1 : M.SameComponent p (M.atom (M.mate b)) := Relation.EqvGen.rel _ _ ⟨b, h.atom_b, rfl⟩
        exact Relation.EqvGen.trans _ _ _ h1 (sameComponent_of_erase (h.connC' _ hbC' u huC'))
  intro u hu v hv
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hp u hu)) (hp v hv)

namespace ThetaGenData
variable {N : Molecule V D} {S : Finset V} {p q : V} {a b z₁ z₂ : D} {C C' : Finset V}
  (h : ThetaGenData N S p q a b z₁ z₂ C C')
include h

theorem p_mem : p ∈ S := by rw [h.hS]; exact mem_insert_self _ _
theorem q_mem : q ∈ S := by rw [h.hS]; exact mem_insert_of_mem (mem_insert_self _ _)
theorem C_mem {v : V} (hv : v ∈ C ∪ C') : v ∈ S := by rw [h.hS]; exact mem_insert_of_mem (mem_insert_of_mem hv)
theorem sdiff_eq : S \ {p, q} = C ∪ C' := by
  rw [h.hS]
  ext v
  simp only [mem_sdiff, mem_insert, mem_singleton, mem_union, not_or]
  constructor
  · rintro ⟨h1 | h1 | h1, h2, h3⟩
    · exact absurd h1 h2
    · exact absurd h1 h3
    · exact h1
  · intro hv
    have hv' : v ∈ C ∪ C' := mem_union.mpr hv
    exact ⟨Or.inr (Or.inr hv), fun e => h.hpC (e ▸ hv'), fun e => h.hqC (e ▸ hv')⟩

theorem haS : N.atom a ∈ S ∧ N.atom (N.mate a) ∈ S := by rw [h.ha, h.hma]; exact ⟨h.p_mem, h.q_mem⟩
theorem hbS : N.atom b ∈ S ∧ N.atom (N.mate b) ∈ S := by
  rw [h.hb]
  refine ⟨h.p_mem, ?_⟩
  rcases h.hmb with ⟨_, e⟩ | e
  · rw [e]; exact h.q_mem
  · exact h.C_mem (mem_union_right _ e)
theorem hz₁S : N.atom z₁ ∈ S ∧ N.atom (N.mate z₁) ∈ S := by
  rw [h.hz₁]; exact ⟨h.p_mem, h.C_mem (mem_union_left _ h.hmz₁)⟩
theorem hz₂S : N.atom z₂ ∈ S ∧ N.atom (N.mate z₂) ∈ S := by
  rw [h.hz₂]; exact ⟨h.q_mem, h.C_mem (mem_union_left _ h.hmz₂)⟩

theorem haz : a ≠ z₁ := by
  intro e; have := h.hmz₁; rw [← e, h.hma] at this; exact h.hqC (mem_union_left _ this)
theorem hbz : b ≠ z₁ := by
  intro e
  have hz := h.hmz₁
  rw [← e] at hz
  rcases h.hmb with ⟨_, e2⟩ | e2
  · rw [e2] at hz; exact h.hqC (mem_union_left _ hz)
  · exact disjoint_left.mp h.disj hz e2

/-- The darts at `p` whose far end lies in `S` are exactly `a, b, z₁`. -/
theorem p_internal : (N.dartsAt p).filter (fun z => N.atom (N.mate z) ∈ S) = {a, b, z₁} := by
  ext z
  simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hz, hm⟩; exact h.pin z hz hm
  · rintro (rfl | rfl | rfl)
    · exact ⟨h.ha, h.haS.2⟩
    · exact ⟨h.hb, h.hbS.2⟩
    · exact ⟨h.hz₁, h.hz₁S.2⟩

/-- **The piece `𝕄[S]` is a generalized theta chain.** -/
theorem isThetaGen_piece :
    IsThetaGen (piece N S) p q (pieceDart N S a h.haS) (pieceDart N S b h.hbS) (pieceDart N S z₁ h.hz₁S)
      (pieceDart N S z₂ h.hz₂S) C C' := by
  classical
  have hA : (piece N S).atoms = S := piece_atoms h.sub
  have hval : ∀ x y : Degen.RetainedDart N (N.atoms \ S), x.val ≠ y.val → x ≠ y := fun x y hne e => hne (e ▸ rfl)
  refine
    { hp := by rw [hA]; exact h.p_mem
      hq := by rw [hA]; exact h.q_mem
      hpq := h.hpq
      hab := hval _ _ h.hab
      haz := hval _ _ h.haz
      hbz := hval _ _ h.hbz
      starp := ?_
      degq := by rw [piece_deg_eq_card h.q_mem]; exact h.qdeg
      atoms_eq := by rw [hA]; exact h.sdiff_eq
      disj := h.disj
      hma := h.hma
      hmb := h.hmb
      z₁in := h.hmz₁
      hz₂ := h.hz₂
      z₂in := h.hmz₂
      crossC := ?_
      signs := h.signs
      dir := h.dir
      chain := ?_
      connC := fun u hu v hv => sameComponent_piece_piece (fun x hx => h.C_mem (mem_union_left _ hx)) (h.connC u hu v hv)
      connC' := fun u hu v hv => sameComponent_piece_piece (fun x hx => h.C_mem (mem_union_right _ hx))
        (h.connC' u hu v hv)
      noLoop := fun x => h.noLoop x.val }
  · ext x
    rw [Mole.mem_dartsAt]
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hx
      rcases h.pin x.val hx (piece_dart_mem x).2 with e | e | e
      · left; exact Subtype.ext e
      · right; left; exact Subtype.ext e
      · right; right; exact Subtype.ext e
    · rintro (rfl | rfl | rfl)
      · exact h.ha
      · exact h.hb
      · exact h.hz₁
  · ext x
    rw [mem_crossDarts]
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h.crossC x.val h1 h2 with e | e
      · left; exact Subtype.ext e
      · right; exact Subtype.ext e
    · rintro (rfl | rfl)
      · refine ⟨h.hmz₁, ?_⟩
        change N.atom (N.mate (N.mate z₁)) ∉ C
        rw [N.mate_mate, h.hz₁]; exact fun hp => h.hpC (mem_union_left _ hp)
      · refine ⟨h.hmz₂, ?_⟩
        change N.atom (N.mate (N.mate z₂)) ∉ C
        rw [N.mate_mate, h.hz₂]; exact fun hq => h.hqC (mem_union_left _ hq)
  · intro v hv'
    have hcl : ∀ z, N.atom z = v → N.atom (N.mate z) ∈ S := fun z hz => h.closed z (hz ▸ hv')
    rw [piece_outdeg_eq hcl (h.C_mem hv'), piece_indeg_eq hcl (h.C_mem hv')]
    exact h.chain v hv'

/-- **If `S` is the whole molecule, `N` is a generalized theta chain.** -/
theorem isThetaGen_self (hSA : S = N.atoms) : IsThetaGen N p q a b z₁ z₂ C C' := by
  classical
  refine
    { hp := hSA ▸ h.p_mem
      hq := hSA ▸ h.q_mem
      hpq := h.hpq
      hab := h.hab
      haz := h.haz
      hbz := h.hbz
      starp := ?_
      degq := ?_
      atoms_eq := by rw [← hSA]; exact h.sdiff_eq
      disj := h.disj
      hma := h.hma
      hmb := h.hmb
      z₁in := h.hmz₁
      hz₂ := h.hz₂
      z₂in := h.hmz₂
      crossC := ?_
      signs := h.signs
      dir := h.dir
      chain := h.chain
      connC := h.connC
      connC' := h.connC'
      noLoop := h.noLoop }
  · ext z
    rw [Mole.mem_dartsAt]
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hz; exact h.pin z hz (hSA ▸ N.atom_mem _)
    · rintro (rfl | rfl | rfl)
      · exact h.ha
      · exact h.hb
      · exact h.hz₁
  · have e : N.dartsAt q = univ.filter (fun z => N.atom z = q ∧ N.atom (N.mate z) ∈ S) := by
      ext z
      simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]
      exact ⟨fun hz => ⟨hz, hSA ▸ N.atom_mem _⟩, fun hz => hz.1⟩
    unfold Molecule.deg
    rw [e]; exact h.qdeg
  · ext x
    rw [mem_crossDarts]
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact h.crossC x h1 h2
    · rintro (rfl | rfl)
      · refine ⟨h.hmz₁, ?_⟩
        rw [N.mate_mate, h.hz₁]; exact fun hp => h.hpC (mem_union_left _ hp)
      · refine ⟨h.hmz₂, ?_⟩
        rw [N.mate_mate, h.hz₂]; exact fun hq => h.hqC (mem_union_left _ hq)

/-- The exits of `S` at `p` (resp. `q`): at most one each when degrees are at most four. -/
theorem card_exits_p :
    ((N.dartsAt p).filter fun z => N.atom (N.mate z) ∉ S).card + 3 = N.deg p := by
  classical
  have h1 := card_filter_add_card_filter_not (s := N.dartsAt p) (p := fun z => N.atom (N.mate z) ∈ S)
  rw [h.p_internal] at h1
  have h3 : ({a, b, z₁} : Finset D).card = 3 := by
    rw [card_insert_of_notMem (by simp [h.hab, h.haz]), card_pair h.hbz]
  unfold Molecule.deg
  omega

theorem card_exits_q :
    ((N.dartsAt q).filter fun z => N.atom (N.mate z) ∉ S).card + 3 = N.deg q := by
  classical
  have h1 := card_filter_add_card_filter_not (s := N.dartsAt q) (p := fun z => N.atom (N.mate z) ∈ S)
  have h2 : ((N.dartsAt q).filter fun z => N.atom (N.mate z) ∈ S).card = 3 := by
    rw [← h.qdeg]; congr 1; ext z; simp [Molecule.dartsAt]
  unfold Molecule.deg
  omega

theorem cross_sub : crossDarts N S ⊆ ((N.dartsAt p).filter fun z => N.atom (N.mate z) ∉ S) ∪
    ((N.dartsAt q).filter fun z => N.atom (N.mate z) ∉ S) := by
  intro x hx
  obtain ⟨h1, h2⟩ := mem_crossDarts.mp hx
  rw [h.hS] at h1
  simp only [mem_insert] at h1
  rcases h1 with e | e | e
  · exact mem_union_left _ (mem_filter.mpr ⟨(Mole.mem_dartsAt N p x).mpr e, h2⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨(Mole.mem_dartsAt N q x).mpr e, h2⟩)
  · exact absurd (h.closed x e) h2

/-- **At most two exits.** -/
theorem card_cross_le (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) : (crossDarts N S).card ≤ 2 := by
  have hp4 : N.deg p ≤ 4 := by
    have := hcap p (h.sub h.p_mem); have := Mole.outdeg_add_indeg N p; omega
  have hq4 : N.deg q ≤ 4 := by
    have := hcap q (h.sub h.q_mem); have := Mole.outdeg_add_indeg N q; omega
  have e1 := h.card_exits_p
  have e2 := h.card_exits_q
  exact (card_le_card h.cross_sub).trans ((card_union_le _ _).trans (by omega))

/-- **With two exits `S` is balanced.** -/
theorem balanced (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) (h2 : (crossDarts N S).card = 2) :
    ∀ v ∈ S, N.outdeg v = N.indeg v := by
  have hp4 : N.deg p ≤ 4 := by
    have := hcap p (h.sub h.p_mem); have := Mole.outdeg_add_indeg N p; omega
  have hq4 : N.deg q ≤ 4 := by
    have := hcap q (h.sub h.q_mem); have := Mole.outdeg_add_indeg N q; omega
  have e1 := h.card_exits_p
  have e2 := h.card_exits_q
  have hle := (card_le_card h.cross_sub).trans (card_union_le _ _)
  have hdp : N.deg p = 4 := by omega
  have hdq : N.deg q = 4 := by omega
  intro v hv
  rw [h.hS] at hv
  simp only [mem_insert] at hv
  rcases hv with rfl | rfl | hv
  · have := hcap v (h.sub h.p_mem); have := Mole.outdeg_add_indeg N v; omega
  · have := hcap v (h.sub h.q_mem); have := Mole.outdeg_add_indeg N v; omega
  · rw [(h.chain v hv).1, (h.chain v hv).2]

/-- **With two exits `p` and `q` have degree four.** -/
theorem deg_four_of_two (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) (h2 : (crossDarts N S).card = 2) :
    N.deg p = 4 ∧ N.deg q = 4 := by
  have hp4 : N.deg p ≤ 4 := by
    have := hcap p (h.sub h.p_mem); have := Mole.outdeg_add_indeg N p; omega
  have e1 := h.card_exits_p
  have e2 := h.card_exits_q
  have hle := (card_le_card h.cross_sub).trans (card_union_le _ _)
  have hq4 : N.deg q ≤ 4 := by
    have := hcap q (h.sub h.q_mem); have := Mole.outdeg_add_indeg N q; omega
  omega

end ThetaGenData
end

end WaveTurbulence.GammaLow.FinalCount.Count
