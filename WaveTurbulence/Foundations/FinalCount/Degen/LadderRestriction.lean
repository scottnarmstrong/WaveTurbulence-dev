/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.Degen.Removal
public import WaveTurbulence.Foundations.FinalCount.Degen.SourceLadder
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! # Exact ladder preservation under induced atom deletion

TARGET defvine and ladderl1old. Retained ladders use the same actual
outgoing bonds, multiplicities and directions. The original induced B2
draft exports also preserve induced-group edge counts; separate selected
source-ladder exports implement the adopted reading allowing end chords.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D]

private theorem card_filter_retained (M : Molecule V D) (Y : Finset V)
    (p : D → Prop) [DecidablePred p]
    (hp : ∀ x, p x → M.atom x ∉ Y ∧ M.atom (M.mate x) ∉ Y) :
    (univ.filter (fun x : RetainedDart M Y => p x.val)).card = (univ.filter p).card := by
  apply card_bij (fun x _ => x.val)
  · intro x hx
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    have hpx := (mem_filter.mp hx).2
    exact ⟨⟨x, hp x hpx⟩, mem_filter.mpr ⟨mem_univ _, hpx⟩, rfl⟩

theorem bondsBetween_erase_eq (M : Molecule V D) (Y : Finset V) {a b : V}
    (ha : a ∉ Y) (hb : b ∉ Y) :
    (eraseAtoms M Y).bondsBetween a b = M.bondsBetween a b := by
  unfold Molecule.bondsBetween Molecule.bonds
  simp only [filter_filter]
  change (univ.filter fun x : RetainedDart M Y => M.out x.val = true ∧ M.ends x.val = s(a,b)).card = _
  apply card_filter_retained M Y (fun x => M.out x = true ∧ M.ends x = s(a,b))
  intro x hx
  have he : s(M.atom x, M.atom (M.mate x)) = s(a,b) := hx.2
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · simpa only [h1,h2] using (show a ∉ Y ∧ b ∉ Y from ⟨ha,hb⟩)
  · simpa only [h1,h2] using (show b ∉ Y ∧ a ∉ Y from ⟨hb,ha⟩)

omit [Fintype D] in
theorem directed_erase_iff (M : Molecule V D) (Y : Finset V) {a b : V}
    (ha : a ∉ Y) (hb : b ∉ Y) : (eraseAtoms M Y).Directed a b ↔ M.Directed a b := by
  constructor
  · rintro ⟨x,hout,hx,hy⟩
    exact ⟨x.val,hout,hx,hy⟩
  · rintro ⟨x,hout,hx,hy⟩
    exact ⟨⟨x,by simpa only [hx] using ha,by simpa only [hy] using hb⟩,hout,hx,hy⟩

/-! ## Selected source ladders under the adopted reading -/

/-- Selected rung-and-rail ladders are unchanged when all atoms survive. -/
theorem sourceLadder_erase_iff (M : Molecule V D) (Y : Finset V) {m : ℕ}
    (u v : Fin (m+1) → V) (hnot : ∀ j, u j ∉ Y ∧ v j ∉ Y) :
    SourceLadder (eraseAtoms M Y) u v ↔ SourceLadder M u v := by
  have hatoms : (∀ j, u j ∈ (eraseAtoms M Y).atoms ∧ v j ∈ (eraseAtoms M Y).atoms) ↔
      (∀ j, u j ∈ M.atoms ∧ v j ∈ M.atoms) := by
    constructor
    · intro h j
      exact ⟨(mem_sdiff.mp (h j).1).1, (mem_sdiff.mp (h j).2).1⟩
    · intro h j
      exact ⟨mem_sdiff.mpr ⟨(h j).1,(hnot j).1⟩,mem_sdiff.mpr ⟨(h j).2,(hnot j).2⟩⟩
  unfold SourceLadder
  rw [hatoms]
  simp_rw [bondsBetween_erase_eq M Y (hnot _).1 (hnot _).2,
    bondsBetween_erase_eq M Y (hnot _).1 (hnot _).1,
    bondsBetween_erase_eq M Y (hnot _).2 (hnot _).2,
    directed_erase_iff M Y (hnot _).1 (hnot _).1,
    directed_erase_iff M Y (hnot _).2 (hnot _).2]

/-- The source-reading ladder atom sets after erasure are exactly surviving
old source-reading ladder atom sets. -/
theorem sourceLadderSet_erase_iff (M : Molecule V D) (Y S : Finset V) :
    SourceLadderSet (eraseAtoms M Y) S ↔ SourceLadderSet M S ∧ Disjoint S Y := by
  constructor
  · rintro ⟨m,u,v,hL,rfl⟩
    have hnot : ∀ j, u j ∉ Y ∧ v j ∉ Y := fun j =>
      ⟨(mem_sdiff.mp (hL.2.2.1 j).1).2,(mem_sdiff.mp (hL.2.2.1 j).2).2⟩
    refine ⟨⟨m,u,v,(sourceLadder_erase_iff M Y u v hnot).mp hL,rfl⟩, ?_⟩
    apply disjoint_left.mpr
    intro x hx hy
    obtain hx | hx := mem_union.mp hx
    · obtain ⟨j,_,rfl⟩ := mem_image.mp hx
      exact (hnot j).1 hy
    · obtain ⟨j,_,rfl⟩ := mem_image.mp hx
      exact (hnot j).2 hy
  · rintro ⟨⟨m,u,v,hL,rfl⟩,hSY⟩
    have hnot : ∀ j, u j ∉ Y ∧ v j ∉ Y := by
      intro j
      constructor
      · exact fun hy => (disjoint_left.mp hSY) (mem_union_left _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)) hy
      · exact fun hy => (disjoint_left.mp hSY) (mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)) hy
    exact ⟨m,u,v,(sourceLadder_erase_iff M Y u v hnot).mpr hL,rfl⟩

/-- Every actual selected ladder set extends to an actual maximal one.
This is finite powerset maximality, with no geometric decomposition input. -/
theorem exists_sourceMaximalLadder_superset (M : Molecule V D) {S : Finset V}
    (hL : SourceLadderSet M S) : ∃ T ∈ sourceMaximalLadders M, S ⊆ T := by
  classical
  let C := M.atoms.powerset.filter fun T => SourceLadderSet M T ∧ S ⊆ T
  have hC : C.Nonempty := by
    refine ⟨S,mem_filter.mpr ⟨?_,hL,Subset.rfl⟩⟩
    exact mem_powerset.mpr (sourceLadderSet_atoms_subset M hL)
  obtain ⟨T,hT,hmax⟩ := exists_max_image C Finset.card hC
  obtain ⟨hTatoms,hTL,hST⟩ := mem_filter.mp hT
  refine ⟨T,mem_filter.mpr ⟨hTatoms,hTL,?_⟩,hST⟩
  intro U hUL hTU
  have hUC : U ∈ C := mem_filter.mpr
    ⟨mem_powerset.mpr (sourceLadderSet_atoms_subset M hUL),hUL,hST.trans hTU⟩
  exact (eq_of_subset_of_card_le hTU (hmax U hUC)).symm

omit [DecidableEq V] [Fintype D] in
private theorem not_mem_of_ends (M : Molecule V D) (Y : Finset V) {a b : V} {x : D}
    (ha : a ∉ Y) (hb : b ∉ Y) (hx : M.ends x = s(a,b)) :
    M.atom x ∉ Y ∧ M.atom (M.mate x) ∉ Y := by
  have he : s(M.atom x, M.atom (M.mate x)) = s(a,b) := hx
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · simpa only [h1,h2] using (show a ∉ Y ∧ b ∉ Y from ⟨ha,hb⟩)
  · simpa only [h1,h2] using (show b ∉ Y ∧ a ∉ Y from ⟨hb,ha⟩)

omit [Fintype D] in
/-- Every surviving actual rail pair has exactly its original physical gap.
This is independent of whether the ladder was selected or induced. -/
theorem isLadderGap_erase_iff (M : Molecule V D) (Y : Finset V) {d m : ℕ}
    (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (u v : Fin (m+1) → V)
    (hm : 1 ≤ m) (hnot : ∀ j, u j ∉ Y ∧ v j ∉ Y) (r : Mom d) :
    (eraseAtoms M Y).IsLadderGap L w (fun x => κ x.val) u v hm r ↔
      M.IsLadderGap L w κ u v hm r := by
  constructor
  · rintro ⟨x,y,hx,hy,hax,hay,hr⟩
    exact ⟨x.val,y.val,hx,hy,hax,hay,hr⟩
  · rintro ⟨x,y,hx,hy,hax,hay,hr⟩
    let x' : RetainedDart M Y := ⟨x,not_mem_of_ends M Y (hnot _).1 (hnot _).1 hx⟩
    let y' : RetainedDart M Y := ⟨y,not_mem_of_ends M Y (hnot _).2 (hnot _).2 hy⟩
    exact ⟨x',y',hx,hy,hax,hay,hr⟩

end WaveTurbulence.Degen
