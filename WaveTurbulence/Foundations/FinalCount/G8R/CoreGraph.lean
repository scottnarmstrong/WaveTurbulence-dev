/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreInputs
import Mathlib.Tactic

/-! # Cuts of a molecule: crossing darts, parity, connected sides

Graph facts used by the case analysis of Prop 10.4(2)′. The key lemma `erase_disconnected_cross`: if erasing `Y`
disconnects two atoms `a, b`, their components `C₁, C₂` in `𝕄 ∖ Y` are disjoint and every dart leaving `Cᵢ` goes to
`Y`, so `|∂C₁| + |∂C₂| ≤ |∂Y|`. With `Y` the complement of `S` this says that a piece with few crossing darts is
connected.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- The complement has as many crossing darts (their mates). -/
theorem card_crossDarts_compl (N : Molecule V D) (S : Finset V) :
    (crossDarts N (N.atoms \ S)).card = (crossDarts N S).card := by
  refine card_bij (fun x _ => N.mate x) ?_ ?_ ?_
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_crossDarts.mp hx
    refine mem_crossDarts.mpr ⟨?_, ?_⟩
    · by_contra h; exact h2 (mem_sdiff.mpr ⟨N.atom_mem _, h⟩)
    · rw [N.mate_mate]; exact fun h => (mem_sdiff.mp h1).2 h
  · intro x _ y _ h; have := congrArg N.mate h; rwa [N.mate_mate, N.mate_mate] at this
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_crossDarts.mp hx
    refine ⟨N.mate x, mem_crossDarts.mpr ⟨mem_sdiff.mpr ⟨N.atom_mem _, h2⟩, ?_⟩, N.mate_mate x⟩
    rw [N.mate_mate]; exact fun h => (mem_sdiff.mp h).2 h1

omit [DecidableEq D] in
/-- A proper part of a connected molecule has a crossing dart. -/
theorem crossDarts_nonempty (N : Molecule V D) (hconn : ∀ u ∈ N.atoms, ∀ v ∈ N.atoms, N.SameComponent u v)
    {S : Finset V} {a b : V} (ha : a ∈ S) (haN : a ∈ N.atoms) (hb : b ∈ N.atoms) (hbS : b ∉ S) :
    (crossDarts N S).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hclosed : ∀ z, N.atom z ∈ S → N.atom (N.mate z) ∈ S := by
    intro z hz
    by_contra hz'
    have : z ∈ crossDarts N S := mem_crossDarts.mpr ⟨hz, hz'⟩
    rw [h] at this; exact notMem_empty z this
  exact hbS ((mem_iff_of_sameComponent_of_closed hclosed (hconn a haN b hb)).mp ha)

/-- Component sets are closed under adjacency. -/
theorem componentSet_closed (K : Molecule V D) (a : V) :
    ∀ z, K.atom z ∈ Degen.componentSet K a → K.atom (K.mate z) ∈ Degen.componentSet K a := by
  intro z hz
  obtain ⟨_, h⟩ := (Degen.mem_componentSet K a _).mp hz
  exact (Degen.mem_componentSet K a _).mpr ⟨K.atom_mem _,
    Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ ⟨z, rfl, rfl⟩)⟩

/-- **Two components after erasing `Y`**: if `a, b ∉ Y` are not connected in `𝕄 ∖ Y`, their components `C₁ ∋ a`,
`C₂ ∋ b` are disjoint, and `|∂C₁| + |∂C₂| ≤ |∂Y|`. -/
theorem erase_disconnected_cross (N : Molecule V D) (Y : Finset V) {a b : V} (ha : a ∈ N.atoms \ Y)
    (hb : b ∈ N.atoms \ Y) (hab : ¬ (Degen.eraseAtoms N Y).SameComponent a b) :
    ∃ C₁ C₂ : Finset V, C₁ ⊆ N.atoms \ Y ∧ C₂ ⊆ N.atoms \ Y ∧ a ∈ C₁ ∧ b ∈ C₂ ∧ Disjoint C₁ C₂ ∧
      (∀ z, N.atom z ∈ C₁ → N.atom (N.mate z) ∉ Y → N.atom (N.mate z) ∈ C₁) ∧
      (∀ z, N.atom z ∈ C₂ → N.atom (N.mate z) ∉ Y → N.atom (N.mate z) ∈ C₂) ∧
      (crossDarts N C₁).card + (crossDarts N C₂).card ≤ (crossDarts N Y).card := by
  classical
  set K := Degen.eraseAtoms N Y
  let C₁ := Degen.componentSet K a
  let C₂ := Degen.componentSet K b
  have hsub : ∀ c, Degen.componentSet K c ⊆ N.atoms \ Y := fun c x hx => ((Degen.mem_componentSet K c x).mp hx).1
  -- closure in `𝕄`, away from `Y`
  have hcl : ∀ c, ∀ z, N.atom z ∈ Degen.componentSet K c → N.atom (N.mate z) ∉ Y →
      N.atom (N.mate z) ∈ Degen.componentSet K c := by
    intro c z hz hzY
    have hzY' : N.atom z ∉ Y := (mem_sdiff.mp (hsub c hz)).2
    exact componentSet_closed K c ⟨z, hzY', hzY⟩ hz
  have hdisj : Disjoint C₁ C₂ := by
    rw [disjoint_left]
    intro x hx1 hx2
    obtain ⟨_, h1⟩ := (Degen.mem_componentSet K a x).mp hx1
    obtain ⟨_, h2⟩ := (Degen.mem_componentSet K b x).mp hx2
    exact hab (Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ h2))
  have hcross : ∀ c, ∀ x ∈ crossDarts N (Degen.componentSet K c), N.mate x ∈ crossDarts N Y := by
    intro c x hx
    obtain ⟨h1, h2⟩ := mem_crossDarts.mp hx
    refine mem_crossDarts.mpr ⟨?_, ?_⟩
    · by_contra h; exact h2 (hcl c x h1 h)
    · rw [N.mate_mate]; exact (mem_sdiff.mp (hsub c h1)).2
  refine ⟨C₁, C₂, hsub a, hsub b, ?_, ?_, hdisj, hcl a, hcl b, ?_⟩
  · exact (Degen.mem_componentSet K a a).mpr ⟨ha, Relation.EqvGen.refl _⟩
  · exact (Degen.mem_componentSet K b b).mpr ⟨hb, Relation.EqvGen.refl _⟩
  · rw [← card_union_of_disjoint]
    · refine card_le_card_of_injOn N.mate ?_ ?_
      · intro x hx
        rcases mem_union.mp hx with h | h
        · exact hcross a x h
        · exact hcross b x h
      · intro x _ y _ h; have := congrArg N.mate h; rwa [N.mate_mate, N.mate_mate] at this
    · rw [disjoint_left]
      intro x h1 h2
      exact disjoint_left.mp hdisj (mem_crossDarts.mp h1).1 (mem_crossDarts.mp h2).1

/-- **Few crossing darts give a connected piece**: if every proper part of `𝕄` has at least `k` crossing darts and
`|∂S| < 2k`, the piece on `S` is connected. -/
theorem piece_connected_of_cross (N : Molecule V D) {k : ℕ} (hk : ∀ T ⊆ N.atoms, ∀ a ∈ T, ∀ b ∈ N.atoms, b ∉ T → k ≤ (crossDarts N T).card)
    {S : Finset V} (hS : S ⊆ N.atoms) (hlt : (crossDarts N S).card < 2 * k) :
    ∀ a ∈ S, ∀ b ∈ S, (piece N S).SameComponent a b := by
  intro a ha b hb
  by_contra hab
  have hY : N.atoms \ (N.atoms \ S) = S := by rw [sdiff_sdiff_right_self, inf_eq_right.mpr hS]
  have ha' : a ∈ N.atoms \ (N.atoms \ S) := by rw [hY]; exact ha
  have hb' : b ∈ N.atoms \ (N.atoms \ S) := by rw [hY]; exact hb
  obtain ⟨C₁, C₂, h1, h2, ha1, hb2, hdisj, _, _, hcard⟩ := erase_disconnected_cross N (N.atoms \ S) ha' hb' hab
  rw [card_crossDarts_compl] at hcard
  rw [hY] at h1 h2
  have k1 := hk C₁ (h1.trans hS) a ha1 b (hS hb) (fun h => disjoint_left.mp hdisj h hb2)
  have k2 := hk C₂ (h2.trans hS) b hb2 a (hS ha) (fun h => disjoint_left.mp hdisj ha1 h)
  omega

omit [DecidableEq D] in
/-- In a 4-regular molecule, every cut has an even number of crossing darts. -/
theorem cross_even_of_reg (N : Molecule V D) (h4 : ∀ v ∈ N.atoms, N.deg v = 4) {S : Finset V} (hS : S ⊆ N.atoms) :
    Even (crossDarts N S).card := by
  have h := two_mul_piece_bonds N hS
  rw [sum_congr rfl fun v hv => h4 v (hS hv), sum_const, smul_eq_mul] at h
  exact ⟨2 * S.card - (piece N S).bonds.card, by omega⟩

omit [DecidableEq D] in
/-- In a connected 4-regular molecule every proper part has at least two crossing darts (no bridge). -/
theorem two_le_cross_of_reg (N : Molecule V D) (h4 : ∀ v ∈ N.atoms, N.deg v = 4)
    (hconn : ∀ u ∈ N.atoms, ∀ v ∈ N.atoms, N.SameComponent u v) :
    ∀ T ⊆ N.atoms, ∀ a ∈ T, ∀ b ∈ N.atoms, b ∉ T → 2 ≤ (crossDarts N T).card := by
  intro T hT a ha b hb hbT
  have hne := crossDarts_nonempty N hconn ha (hT ha) hb hbT
  obtain ⟨k, hk⟩ := cross_even_of_reg N h4 hT
  have := card_pos.mpr hne
  omega

omit [DecidableEq D] in
/-- In a loop-free molecule, every dart at `w` leaves `{w}`. -/
theorem card_cross_singleton (N : Molecule V D) (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (w : V) :
    (crossDarts N {w}).card = N.deg w := by
  unfold Molecule.deg Molecule.dartsAt crossDarts
  congr 1; ext z
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · exact fun h => h.1
  · intro h; exact ⟨h, fun h' => hloop z (h.trans h'.symm)⟩

omit [DecidableEq D] in
/-- A crossing dart lowers the degree of its atom in the piece. -/
theorem piece_deg_lt (N : Molecule V D) {S : Finset V} {x : D} (hx : x ∈ crossDarts N S) :
    (piece N S).deg (N.atom x) < N.deg (N.atom x) := by
  classical
  obtain ⟨h1, h2⟩ := mem_crossDarts.mp hx
  have h := deg_eraseAtoms_add (N := N) (N.atoms \ S) (v := N.atom x) (fun h => (mem_sdiff.mp h).2 h1)
  have hmem : x ∈ Degen.removedDartsAt N (N.atoms \ S) (N.atom x) := by
    unfold Degen.removedDartsAt Molecule.dartsAt
    simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    exact ⟨N.atom_mem _, h2⟩
  have := card_pos.mpr ⟨x, hmem⟩
  change (Degen.eraseAtoms N (N.atoms \ S)).deg (N.atom x) < _
  omega

/-- **Flow balance across a cut**: if every atom of `S` has as many outgoing as incoming darts, so do the crossing
darts. -/
theorem cross_out_eq_in (N : Molecule V D) {S : Finset V} (hbal : ∀ v ∈ S, N.outdeg v = N.indeg v) :
    ((crossDarts N S).filter fun x => N.out x = true).card = ((crossDarts N S).filter fun x => N.out x = false).card := by
  classical
  -- all darts at `S`, split by direction
  have hsum : ∀ b : Bool, ∑ v ∈ S, ((N.dartsAt v).filter fun x => N.out x = b).card =
      (univ.filter fun x => N.atom x ∈ S ∧ N.out x = b).card := by
    intro b
    rw [card_eq_sum_card_fiberwise (s := univ.filter fun x => N.atom x ∈ S ∧ N.out x = b) (t := S) (f := N.atom)
      (fun z hz => (mem_filter.mp hz).2.1)]
    refine sum_congr rfl fun v hv => ?_
    congr 1; ext z
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1 ▸ hv, h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
  have hbal' : (univ.filter fun x => N.atom x ∈ S ∧ N.out x = true).card =
      (univ.filter fun x => N.atom x ∈ S ∧ N.out x = false).card := by
    rw [← hsum, ← hsum]
    exact sum_congr rfl fun v hv => hbal v hv
  -- internal darts: out ↔ in by the mate
  have hint : (univ.filter fun x => N.atom x ∈ S ∧ N.atom (N.mate x) ∈ S ∧ N.out x = true).card =
      (univ.filter fun x => N.atom x ∈ S ∧ N.atom (N.mate x) ∈ S ∧ N.out x = false).card := by
    refine card_bij (fun x _ => N.mate x) ?_ ?_ ?_
    · intro x hx
      obtain ⟨_, h1, h2, h3⟩ := mem_filter.mp hx
      refine mem_filter.mpr ⟨mem_univ _, h2, by rw [N.mate_mate]; exact h1, ?_⟩
      rw [N.out_mate, h3]; rfl
    · intro x _ y _ h; have := congrArg N.mate h; rwa [N.mate_mate, N.mate_mate] at this
    · intro x hx
      obtain ⟨_, h1, h2, h3⟩ := mem_filter.mp hx
      refine ⟨N.mate x, mem_filter.mpr ⟨mem_univ _, h2, by rw [N.mate_mate]; exact h1, ?_⟩, N.mate_mate x⟩
      rw [N.out_mate, h3]; rfl
  have hsplit : ∀ b : Bool, (univ.filter fun x => N.atom x ∈ S ∧ N.out x = b).card =
      (univ.filter fun x => N.atom x ∈ S ∧ N.atom (N.mate x) ∈ S ∧ N.out x = b).card +
        ((crossDarts N S).filter fun x => N.out x = b).card := by
    intro b
    rw [← card_union_of_disjoint]
    · congr 1; ext x
      simp only [mem_filter, mem_univ, true_and, mem_union, crossDarts]
      tauto
    · rw [disjoint_left]
      intro x h1 h2
      simp only [mem_filter, mem_univ, true_and, crossDarts] at h1 h2
      exact h2.1.2 h1.2.1
  have e1 := hsplit true
  have e2 := hsplit false
  omega

end WaveTurbulence.MoleProp4
