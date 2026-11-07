/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.WorldSelectedLadderDisjoint
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-!
# Actual matched-rail alignment inside a selected source ladder

An unmatched extra end chord is allowed. A matched pair closing both ends
would make the entire component saturated and is excluded by IsMolecule.
No scale-transport or gap-estimate conclusion is assumed.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Exact finite-fiber form of the degree sum over distinct neighbors. -/
theorem sum_neighbor_bonds_eq_filter_card (M : Molecule V D) (a : V) (N : Finset V)
    (ha : a ∉ N) :
    (∑ b ∈ N, M.bondsBetween a b) =
      ((M.dartsAt a).filter fun x => M.atom (M.mate x) ∈ N).card := by
  classical
  let F := (M.dartsAt a).filter (fun x => M.atom (M.mate x) ∈ N)
  have he := card_eq_sum_card_fiberwise (s := F) (t := N)
    (f := fun x => M.atom (M.mate x)) (fun x hx => (mem_filter.mp hx).2)
  have hf (b : V) (hb : b ∈ N) : F.filter (fun x => M.atom (M.mate x) = b) = neighborDarts M a b := by
    ext x
    simp only [F,neighborDarts,mem_filter]
    constructor
    · rintro ⟨⟨hx,_⟩,heq⟩
      exact ⟨hx,heq⟩
    · rintro ⟨hx,heq⟩
      exact ⟨⟨hx,heq.symm ▸ hb⟩,heq⟩
  calc
    _ = ∑ b ∈ N, (F.filter (fun x => M.atom (M.mate x) = b)).card := by
      apply sum_congr rfl
      intro b hb
      rw [hf b hb,card_neighborDarts M (by intro heq; exact ha (heq.symm ▸ hb))]
    _ = _ := he.symm

/-- Four accounted-for incident darts exhaust a degree-at-most-four atom. -/
theorem neighbor_cover_of_sum_four (M : Molecule V D) {a : V} {N : Finset V}
    (ha : a ∉ N) (hcount : (∑ b ∈ N, M.bondsBetween a b) = 4) (hdeg : M.deg a ≤ 4) :
    M.deg a = 4 ∧ ∀ x : D, M.atom x = a → M.atom (M.mate x) ∈ N := by
  classical
  let F := (M.dartsAt a).filter fun x => M.atom (M.mate x) ∈ N
  have hF : F.card = 4 := (sum_neighbor_bonds_eq_filter_card M a N ha).symm.trans hcount
  have hsub : F ⊆ M.dartsAt a := filter_subset _ _
  have hle := card_le_card hsub
  have hdegree : M.deg a = 4 := by change F.card ≤ M.deg a at hle; omega
  have he : F = M.dartsAt a := eq_of_subset_of_card_le hsub (by change M.deg a ≤ F.card; omega)
  refine ⟨hdegree,fun x hx => ?_⟩
  have hxF : x ∈ F := by rw [he]; exact (Mole.mem_dartsAt M a x).mpr hx
  exact (mem_filter.mp hxF).2

/-- A nonempty closed atomic set of degree-four atoms is forbidden by the
actual no-saturated-component clause, not a new hypothesis. -/
theorem no_closed_degree_four_group (M : Molecule V D) (hM : M.IsMolecule)
    (S : Finset V) (hS : S.Nonempty) (hsub : S ⊆ M.atoms)
    (hfour : ∀ a ∈ S, M.deg a = 4)
    (hclosed : ∀ a ∈ S, ∀ x : D, M.atom x = a → M.atom (M.mate x) ∈ S) : False := by
  classical
  have hbdy : boundaryDarts M S = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hh := (mem_filter.mp hx).2
    exact hh.2 (hclosed _ hh.1 x rfl)
  obtain ⟨a,ha⟩ := hS
  obtain ⟨b,hb,hpath,hdeg⟩ := hM.2 a (hsub ha)
  have hbS := (sameComponent_mem_iff_of_boundary_empty M S hbdy hpath).mp ha
  exact hdeg (hfour b hbS)

/-- Three distinct neighbors carrying 2+1+1 bonds determine all darts. -/
theorem three_neighbor_cover (M : Molecule V D) {a b c e : V}
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e)
    (h2 : M.bondsBetween a b = 2) (h1 : M.bondsBetween a c = 1)
    (h1' : M.bondsBetween a e = 1) (hdeg : M.deg a ≤ 4) :
    M.deg a = 4 ∧ ∀ x : D, M.atom x = a → M.atom (M.mate x) ∈ ({b,c,e} : Finset V) := by
  classical
  apply neighbor_cover_of_sum_four M (by simp only [mem_insert,mem_singleton,not_or]; exact ⟨hab,hac,hae⟩) _ hdeg
  rw [sum_insert (by simp only [mem_insert,mem_singleton,not_or]; exact ⟨hbc,hbe⟩),sum_pair hce,h2,h1,h1']
  norm_num

/-- Every interior selected rung atom has exactly its rung partner and two
row neighbors; no additional internal or external chord is possible. -/
theorem sourceLadder_interior_neighbor_cover (M : Molecule V D)
    (hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4) {m : ℕ} {u v : Fin (m+1) → V}
    (h : SourceLadder M u v) (j : Fin (m+1)) (hlo : 0 < j.val) (hhi : j.val < m) :
    ∃ l r : Fin (m+1), l.val + 1 = j.val ∧ j.val + 1 = r.val ∧
      M.deg (u j) = 4 ∧ ∀ x : D, M.atom x = u j → M.atom (M.mate x) ∈ ({v j,u l,u r} : Finset V) := by
  classical
  let l : Fin m := ⟨j.val-1,by omega⟩
  let r : Fin m := ⟨j.val,hhi⟩
  have hel : l.succ = j := Fin.ext (by change (j.val-1)+1 = j.val; omega)
  have her : r.castSucc = j := Fin.ext rfl
  have hleft : M.bondsBetween (u j) (u l.castSucc) = 1 := by
    rw [← hel,bondsBetween_comm M]
    exact (h.2.2.2.2 l).1
  have hright : M.bondsBetween (u j) (u r.succ) = 1 := by
    rw [← her]
    exact (h.2.2.2.2 r).1
  obtain ⟨hu,_,huv⟩ := Sum.elim_injective.mp h.2.1
  have hjl : j ≠ l.castSucc := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc] at hh
    dsimp only [l] at hh
    omega
  have hjr : j ≠ r.succ := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_succ] at hh
    dsimp only [r] at hh
    omega
  have hlr : l.castSucc ≠ r.succ := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc,Fin.val_succ] at hh
    dsimp only [l,r] at hh
    omega
  refine ⟨l.castSucc,r.succ,?_,?_,?_⟩
  · change (j.val-1)+1 = j.val
    omega
  · rfl
  · exact three_neighbor_cover M (huv j j) (hu.ne hjl) (hu.ne hjr)
      (huv l.castSucc j).symm (huv r.succ j).symm (hu.ne hlr)
      (h.2.2.2.1 j) hleft hright (hdeg _ (h.2.2.1 j).1)


/-- Every single neighbor of an interior rung atom is one of its two
consecutive row neighbors. -/
theorem sourceLadder_interior_single_neighbor (M : Molecule V D)
    (hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4) {m : ℕ} {u v : Fin (m+1) → V}
    (h : SourceLadder M u v) (j : Fin (m+1)) (hlo : 0 < j.val) (hhi : j.val < m)
    {a : V} (hne : u j ≠ a) (hsingle : M.bondsBetween (u j) a = 1) :
    ∃ k : Fin (m+1), (k.val + 1 = j.val ∨ j.val + 1 = k.val) ∧ a = u k := by
  classical
  obtain ⟨l,r,hl,hr,hfour,hcover⟩ := sourceLadder_interior_neighbor_cover M hdeg h j hlo hhi
  have hcard : (neighborDarts M (u j) a).card = 1 := by rw [card_neighborDarts M hne,hsingle]
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < (neighborDarts M (u j) a).card)
  have hx' := (mem_neighborDarts M (u j) a x).mp hx
  have hh := hcover x hx'.1
  rw [hx'.2] at hh
  rcases mem_insert.mp hh with he | hh
  · have hh := h.2.2.2.1 j
    rw [← he,hsingle] at hh
    omega
  · rcases mem_insert.mp hh with he | hh
    · exact ⟨l,Or.inl hl,he⟩
    · exact ⟨r,Or.inr hr,mem_singleton.mp hh⟩

private theorem index_interior_of_not_end {m : ℕ} (j : Fin (m+1))
    (h : ¬(j = 0 ∨ j = Fin.last m)) : 0 < j.val ∧ j.val < m := by
  constructor
  · by_contra hh
    exact h (Or.inl (Fin.ext (by change j.val = 0; omega)))
  · by_contra hh
    exact h (Or.inr (Fin.ext (by change j.val = m; have := j.isLt; omega)))

/-- A nonconsecutive single bond on one row can only join the two ends. -/
theorem sourceLadder_nonconsecutive_single_at_ends (M : Molecule V D)
    (hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4) {m : ℕ} {u v : Fin (m+1) → V}
    (h : SourceLadder M u v) (i j : Fin (m+1)) (hij : i ≠ j)
    (hnon : ¬(i.val+1 = j.val ∨ j.val+1 = i.val))
    (hsingle : M.bondsBetween (u i) (u j) = 1) :
    (i = 0 ∨ i = Fin.last m) ∧ (j = 0 ∨ j = Fin.last m) := by
  classical
  have hu := (Sum.elim_injective.mp h.2.1).1
  have hfirst (i j : Fin (m+1)) (hij : i ≠ j)
      (hnon : ¬(i.val+1 = j.val ∨ j.val+1 = i.val))
      (hs : M.bondsBetween (u i) (u j) = 1) : i = 0 ∨ i = Fin.last m := by
    by_contra he
    obtain ⟨hlo,hhi⟩ := index_interior_of_not_end i he
    obtain ⟨k,hk,heq⟩ := sourceLadder_interior_single_neighbor M hdeg h i hlo hhi (hu.ne hij) hs
    have hjk : j = k := hu heq
    subst k
    exact hnon (hk.elim Or.inr Or.inl)
  refine ⟨hfirst i j hij hnon hsingle,?_⟩
  apply hfirst j i hij.symm (by tauto)
  rw [bondsBetween_comm M]
  exact hsingle

/-- A cross-row single chord can only connect end rungs. -/
theorem sourceLadder_cross_single_at_ends (M : Molecule V D)
    (hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4) {m : ℕ} {u v : Fin (m+1) → V}
    (h : SourceLadder M u v) (i j : Fin (m+1))
    (hsingle : M.bondsBetween (u i) (v j) = 1) :
    i ≠ j ∧ (i = 0 ∨ i = Fin.last m) ∧ (j = 0 ∨ j = Fin.last m) := by
  classical
  have huv := (Sum.elim_injective.mp h.2.1).2.2
  have hne : i ≠ j := by
    intro he
    subst j
    have hh := h.2.2.2.1 i
    omega
  have hfirst {m : ℕ} {u v : Fin (m+1) → V} (h : SourceLadder M u v)
      (i j : Fin (m+1)) (hs : M.bondsBetween (u i) (v j) = 1) : i = 0 ∨ i = Fin.last m := by
    by_contra he
    obtain ⟨hlo,hhi⟩ := index_interior_of_not_end i he
    have huv := (Sum.elim_injective.mp h.2.1).2.2
    obtain ⟨k,_,heq⟩ := sourceLadder_interior_single_neighbor M hdeg h i hlo hhi (huv i j) hs
    exact huv k j heq.symm
  refine ⟨hne,hfirst h i j hsingle,?_⟩
  apply hfirst (sourceLadder_swap M h) j i
  rw [bondsBetween_comm M]
  exact hsingle

private theorem cover_mono (M : Molecule V D) {a : V} {N S : Finset V}
    (h : M.deg a = 4 ∧ ∀ x : D, M.atom x = a → M.atom (M.mate x) ∈ N)
    (hsub : N ⊆ S) :
    M.deg a = 4 ∧ ∀ x : D, M.atom x = a → M.atom (M.mate x) ∈ S :=
  ⟨h.1,fun x hx => hsub (h.2 x hx)⟩

/-- Given one additional neighbor at each end, every row atom has degree
four and every incident bond stays inside the old ladder atom set. -/
theorem sourceLadder_row_complete (M : Molecule V D)
    (hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4) {m : ℕ} {u v : Fin (m+1) → V}
    (h : SourceLadder M u v) (e0 eM : V)
    (he0 : e0 ∈ Molecule.ladderAtoms u v) (heM : eM ∈ Molecule.ladderAtoms u v)
    (hne00 : u 0 ≠ e0) (hne0v : v 0 ≠ e0)
    (hne01 : u ⟨1,by have := h.1; omega⟩ ≠ e0)
    (hneMM : u (Fin.last m) ≠ eM) (hneMv : v (Fin.last m) ≠ eM)
    (hneMp : u ⟨m-1,by have := h.1; omega⟩ ≠ eM)
    (hclose0 : M.bondsBetween (u 0) e0 = 1)
    (hcloseM : M.bondsBetween (u (Fin.last m)) eM = 1) :
    ∀ j : Fin (m+1), M.deg (u j) = 4 ∧
      ∀ x : D, M.atom x = u j → M.atom (M.mate x) ∈ Molecule.ladderAtoms u v := by
  classical
  obtain ⟨hu,_,huv⟩ := Sum.elim_injective.mp h.2.1
  have hmemu (j : Fin (m+1)) : u j ∈ Molecule.ladderAtoms u v := mem_union_left _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
  have hmemv (j : Fin (m+1)) : v j ∈ Molecule.ladderAtoms u v := mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
  intro j
  by_cases hj0 : j = 0
  · subst j
    let one : Fin (m+1) := ⟨1,by have := h.1; omega⟩
    have h01 : (0 : Fin (m+1)) ≠ one := by intro he; have hh := congrArg Fin.val he; change (0 : ℕ) = 1 at hh; omega
    have hinner : M.bondsBetween (u 0) (u one) = 1 := (h.2.2.2.2 ⟨0,by have := h.1; omega⟩).1
    apply cover_mono M (three_neighbor_cover M (huv 0 0) (hu.ne h01) hne00 (huv one 0).symm
      hne0v hne01 (h.2.2.2.1 0) hinner hclose0 (hdeg _ (h.2.2.1 0).1))
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact hmemv 0
    · rcases mem_insert.mp ha with rfl | ha
      · exact hmemu one
      · exact (mem_singleton.mp ha).symm ▸ he0
  by_cases hjM : j = Fin.last m
  · subst j
    let prev : Fin (m+1) := ⟨m-1,by have := h.1; omega⟩
    let k : Fin m := ⟨m-1,by have := h.1; omega⟩
    have hks : k.succ = Fin.last m := Fin.ext (by change (m-1)+1=m; have := h.1; omega)
    have hp : k.castSucc = prev := Fin.ext rfl
    have hlastp : Fin.last m ≠ prev := by
      intro he
      have hh := congrArg Fin.val he
      change m = m-1 at hh
      have := h.1
      omega
    have hinner : M.bondsBetween (u (Fin.last m)) (u prev) = 1 := by
      rw [bondsBetween_comm M,← hks,← hp]
      exact (h.2.2.2.2 k).1
    apply cover_mono M (three_neighbor_cover M (huv _ _) (hu.ne hlastp) hneMM (huv prev _).symm
      hneMv hneMp (h.2.2.2.1 _) hinner hcloseM (hdeg _ (h.2.2.1 _).1))
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact hmemv _
    · rcases mem_insert.mp ha with rfl | ha
      · exact hmemu prev
      · exact (mem_singleton.mp ha).symm ▸ heM
  obtain ⟨hlo,hhi⟩ := index_interior_of_not_end j (by tauto)
  obtain ⟨l,r,_,_,hc⟩ := sourceLadder_interior_neighbor_cover M hdeg h j hlo hhi
  apply cover_mono M hc
  intro a ha
  rcases mem_insert.mp ha with rfl | ha
  · exact hmemv _
  · rcases mem_insert.mp ha with rfl | ha
    · exact hmemu l
    · exact (mem_singleton.mp ha).symm ▸ hmemu r


private theorem sourceLadder_not_both_rows_complete (M : Molecule V D) (hM : M.IsMolecule)
    {m : ℕ} {u v : Fin (m+1) → V} (h : SourceLadder M u v)
    (hU : ∀ j, M.deg (u j) = 4 ∧ ∀ x : D, M.atom x = u j → M.atom (M.mate x) ∈ Molecule.ladderAtoms u v)
    (hV : ∀ j, M.deg (v j) = 4 ∧ ∀ x : D, M.atom x = v j → M.atom (M.mate x) ∈ Molecule.ladderAtoms u v) : False := by
  classical
  apply no_closed_degree_four_group M hM (Molecule.ladderAtoms u v)
    ⟨u 0,mem_union_left _ (mem_image.mpr ⟨0,mem_univ _,rfl⟩)⟩
    (sourceLadderSet_atoms_subset M ⟨m,u,v,h,rfl⟩)
  · intro a ha
    rcases mem_union.mp ha with ha | ha
    · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
      exact (hU j).1
    · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
      exact (hV j).1
  · intro a ha x hx
    rcases mem_union.mp ha with ha | ha
    · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
      exact (hU j).2 x hx
    · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
      exact (hV j).2 x hx

/-- Two additional straight end rails would close a saturated component.
The `m≥2` clause distinguishes them from the existing length-one rails. -/
theorem sourceLadder_no_straight_end_closure (M : Molecule V D) (hM : M.IsMolecule)
    {m : ℕ} {u v : Fin (m+1) → V} (h : SourceLadder M u v) (hm : 2 ≤ m)
    (hU0 : M.bondsBetween (u 0) (u (Fin.last m)) = 1)
    (hV0 : M.bondsBetween (v 0) (v (Fin.last m)) = 1) : False := by
  classical
  obtain ⟨hu,hv,huv⟩ := Sum.elim_injective.mp h.2.1
  have hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun _ hx => Mole.deg_le_four M hM hx
  have hmem (f g : Fin (m+1) → V) (j : Fin (m+1)) : f j ∈ Molecule.ladderAtoms f g :=
    mem_union_left _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
  have h0M : (0 : Fin (m+1)) ≠ Fin.last m := by
    intro he; have hh := congrArg Fin.val he; change (0 : ℕ) = m at hh; omega
  have h1M : (⟨1,by omega⟩ : Fin (m+1)) ≠ Fin.last m := by
    intro he; have hh := congrArg Fin.val he; change (1 : ℕ) = m at hh; omega
  have hp0 : (⟨m-1,by omega⟩ : Fin (m+1)) ≠ 0 := by
    intro he; have hh := congrArg Fin.val he; change m-1 = 0 at hh; omega
  have hU1 : M.bondsBetween (u (Fin.last m)) (u 0) = 1 := by rw [bondsBetween_comm M]; exact hU0
  have hV1 : M.bondsBetween (v (Fin.last m)) (v 0) = 1 := by rw [bondsBetween_comm M]; exact hV0
  have hU := sourceLadder_row_complete M hdeg h (u (Fin.last m)) (u 0)
    (hmem u v _) (hmem u v _) (hu.ne h0M) (huv _ _).symm (hu.ne h1M)
    (hu.ne h0M.symm) (huv _ _).symm (hu.ne hp0) hU0 hU1
  have hV := sourceLadder_row_complete M hdeg (sourceLadder_swap M h) (v (Fin.last m)) (v 0)
    (hmem v u _) (hmem v u _) (hv.ne h0M) (huv _ _) (hv.ne h1M)
    (hv.ne h0M.symm) (huv _ _) (hv.ne hp0) hV0 hV1
  rw [ladderAtoms_swap] at hV
  exact sourceLadder_not_both_rows_complete M hM h hU hV

/-- Two crossed matched end rails would also close a saturated component. -/
theorem sourceLadder_no_cross_end_closure (M : Molecule V D) (hM : M.IsMolecule)
    {m : ℕ} {u v : Fin (m+1) → V} (h : SourceLadder M u v)
    (hU0 : M.bondsBetween (u 0) (v (Fin.last m)) = 1)
    (hV0 : M.bondsBetween (v 0) (u (Fin.last m)) = 1) : False := by
  classical
  obtain ⟨hu,hv,huv⟩ := Sum.elim_injective.mp h.2.1
  have hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun _ hx => Mole.deg_le_four M hM hx
  have hmemu (j : Fin (m+1)) : u j ∈ Molecule.ladderAtoms u v := mem_union_left _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
  have hmemv (j : Fin (m+1)) : v j ∈ Molecule.ladderAtoms u v := mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
  have h0M : (0 : Fin (m+1)) ≠ Fin.last m := by
    intro he; have hh := congrArg Fin.val he; change (0 : ℕ) = m at hh; have := h.1; omega
  have hU1 : M.bondsBetween (u (Fin.last m)) (v 0) = 1 := by rw [bondsBetween_comm M]; exact hV0
  have hV1 : M.bondsBetween (v (Fin.last m)) (u 0) = 1 := by rw [bondsBetween_comm M]; exact hU0
  have hU := sourceLadder_row_complete M hdeg h (v (Fin.last m)) (v 0)
    (hmemv _) (hmemv _) (huv _ _) (hv.ne h0M) (huv _ _)
    (huv _ _) (hv.ne h0M.symm) (huv _ _) hU0 hU1
  have hmemu' (j : Fin (m+1)) : u j ∈ Molecule.ladderAtoms v u := by rw [ladderAtoms_swap]; exact hmemu j
  have hV := sourceLadder_row_complete M hdeg (sourceLadder_swap M h) (u (Fin.last m)) (u 0)
    (hmemu' _) (hmemu' _) (huv _ _).symm (hu.ne h0M) (huv _ _).symm
    (huv _ _).symm (hu.ne h0M.symm) (huv _ _).symm hV0 hV1
  rw [ladderAtoms_swap] at hV
  exact sourceLadder_not_both_rows_complete M hM h hU hV

/-- Matched rails within one old ladder connect consecutive rung indices. -/
theorem sourceLadder_matched_straight_indices_adjacent (M : Molecule V D) (hM : M.IsMolecule)
    {m : ℕ} {u v : Fin (m+1) → V} (h : SourceLadder M u v) (i j : Fin (m+1)) (hij : i ≠ j)
    (hU : M.bondsBetween (u i) (u j) = 1) (hV : M.bondsBetween (v i) (v j) = 1) :
    i.val+1 = j.val ∨ j.val+1 = i.val := by
  classical
  by_contra hn
  have he := sourceLadder_nonconsecutive_single_at_ends M (fun x hx => Mole.deg_le_four M hM hx) h i j hij hn hU
  rcases he.1 with hi | hi <;> rcases he.2 with hj | hj
  · exact hij (hi.trans hj.symm)
  · subst i; subst j
    have hm : 2 ≤ m := by simp only [Fin.val_zero,Fin.val_last] at hn; omega
    exact sourceLadder_no_straight_end_closure M hM h hm hU hV
  · subst i; subst j
    have hm : 2 ≤ m := by simp only [Fin.val_zero,Fin.val_last] at hn; omega
    exact sourceLadder_no_straight_end_closure M hM h hm
      (by rw [bondsBetween_comm M]; exact hU) (by rw [bondsBetween_comm M]; exact hV)
  · exact hij (hi.trans hj.symm)

/-- A crossed matched rail pair inside one old ladder is impossible. -/
theorem sourceLadder_no_cross_matched_step (M : Molecule V D) (hM : M.IsMolecule)
    {m : ℕ} {u v : Fin (m+1) → V} (h : SourceLadder M u v) (i j : Fin (m+1))
    (hU : M.bondsBetween (u i) (v j) = 1) (hV : M.bondsBetween (v i) (u j) = 1) : False := by
  classical
  obtain ⟨hne,hi,hj⟩ := sourceLadder_cross_single_at_ends M (fun x hx => Mole.deg_le_four M hM hx) h i j hU
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact hne (hi.trans hj.symm)
  · subst i; subst j
    exact sourceLadder_no_cross_end_closure M hM h hU hV
  · subst i; subst j
    exact sourceLadder_no_cross_end_closure M hM h
      (by rw [bondsBetween_comm M]; exact hV) (by rw [bondsBetween_comm M]; exact hU)
  · exact hne (hi.trans hj.symm)


/-- When a matched step begins on one old row, it ends on that same row
at a consecutive index. Additional unmatched end chords do not enter. -/
theorem sourceLadder_matched_step_alignment (M : Molecule V D) (hM : M.IsMolecule)
    {m : ℕ} {u v : Fin (m+1) → V} (h : SourceLadder M u v) (j : Fin (m+1))
    {c e : V} (hc : c ∈ Molecule.ladderAtoms u v) (hneq : u j ≠ c) (hce : c ≠ e)
    (hrung : M.bondsBetween c e = 2)
    (hU : M.bondsBetween (u j) c = 1) (hV : M.bondsBetween (v j) e = 1) :
    ∃ i : Fin m,
      (j = i.castSucc ∧ c = u i.succ ∧ e = v i.succ) ∨
      (j = i.succ ∧ c = u i.castSucc ∧ e = v i.castSucc) := by
  classical
  have hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun _ hx => Mole.deg_le_four M hM hx
  rcases mem_union.mp hc with hc | hc
  · obtain ⟨k,_,rfl⟩ := mem_image.mp hc
    have he := sourceLadder_double_partner_eq M hdeg h k hce hrung
    subst e
    have hjk : j ≠ k := by intro he; apply hneq; rw [he]
    rcases sourceLadder_matched_straight_indices_adjacent M hM h j k hjk hU hV with ha | ha
    · let i : Fin m := ⟨j.val,by have := k.isLt; omega⟩
      have h0 : j = i.castSucc := Fin.ext rfl
      have h1 : k = i.succ := Fin.ext (by change k.val = j.val+1; omega)
      exact ⟨i,Or.inl ⟨h0,congrArg u h1,congrArg v h1⟩⟩
    · let i : Fin m := ⟨k.val,by have := j.isLt; omega⟩
      have h0 : j = i.succ := Fin.ext (by change j.val = k.val+1; omega)
      have h1 : k = i.castSucc := Fin.ext rfl
      exact ⟨i,Or.inr ⟨h0,congrArg u h1,congrArg v h1⟩⟩
  · obtain ⟨k,_,rfl⟩ := mem_image.mp hc
    have he := sourceLadder_double_partner_eq M hdeg (sourceLadder_swap M h) k hce hrung
    subst e
    exact False.elim (sourceLadder_no_cross_matched_step M hM h j k hU hV)

/-- The first actual rail pair of any contained selected ladder is an old
consecutive rail pair, up to row exchange and/or reversal. This is the
geometric input needed for transporting the actual physical gap scale. -/
theorem sourceLadder_first_pair_alignment (M : Molecule V D) (hM : M.IsMolecule)
    {m n : ℕ} {u v : Fin (m+1) → V} {p q : Fin (n+1) → V}
    (hOld : SourceLadder M u v) (hNew : SourceLadder M p q)
    (hsub : Molecule.ladderAtoms p q ⊆ Molecule.ladderAtoms u v) :
    ∃ i : Fin m,
      (p 0 = u i.castSucc ∧ q 0 = v i.castSucc ∧
        p ⟨1,by have := hNew.1; omega⟩ = u i.succ ∧ q ⟨1,by have := hNew.1; omega⟩ = v i.succ) ∨
      (p 0 = v i.castSucc ∧ q 0 = u i.castSucc ∧
        p ⟨1,by have := hNew.1; omega⟩ = v i.succ ∧ q ⟨1,by have := hNew.1; omega⟩ = u i.succ) ∨
      (p 0 = u i.succ ∧ q 0 = v i.succ ∧
        p ⟨1,by have := hNew.1; omega⟩ = u i.castSucc ∧ q ⟨1,by have := hNew.1; omega⟩ = v i.castSucc) ∨
      (p 0 = v i.succ ∧ q 0 = u i.succ ∧
        p ⟨1,by have := hNew.1; omega⟩ = v i.castSucc ∧ q ⟨1,by have := hNew.1; omega⟩ = u i.castSucc) := by
  classical
  let one : Fin (n+1) := ⟨1,by have := hNew.1; omega⟩
  have hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun _ hx => Mole.deg_le_four M hM hx
  obtain ⟨hp,hq,hpq⟩ := Sum.elim_injective.mp hNew.2.1
  have h01 : (0 : Fin (n+1)) ≠ one := by
    intro he; have hh := congrArg Fin.val he; change (0 : ℕ) = 1 at hh; omega
  have hU : M.bondsBetween (p 0) (p one) = 1 := (hNew.2.2.2.2 ⟨0,by have := hNew.1; omega⟩).1
  have hV : M.bondsBetween (q 0) (q one) = 1 := (hNew.2.2.2.2 ⟨0,by have := hNew.1; omega⟩).2.1
  have hp0 : p 0 ∈ Molecule.ladderAtoms u v := hsub (mem_union_left _ (mem_image.mpr ⟨0,mem_univ _,rfl⟩))
  have hp1 : p one ∈ Molecule.ladderAtoms u v := hsub (mem_union_left _ (mem_image.mpr ⟨one,mem_univ _,rfl⟩))
  rcases mem_union.mp hp0 with hp0 | hp0
  · obtain ⟨j,_,hj⟩ := mem_image.mp hp0
    have hj' : p 0 = u j := hj.symm
    have hq0 : q 0 = v j := sourceLadder_double_partner_eq M hdeg hOld j
      (by rw [← hj']; exact hpq 0 0) (by rw [← hj']; exact hNew.2.2.2.1 0)
    obtain ⟨i,hi | hi⟩ := sourceLadder_matched_step_alignment M hM hOld j hp1
      (by rw [← hj']; exact hp.ne h01) (hpq one one) (hNew.2.2.2.1 one)
      (by rw [← hj']; exact hU) (by rw [← hq0]; exact hV)
    · exact ⟨i,Or.inl ⟨hj'.trans (congrArg u hi.1),hq0.trans (congrArg v hi.1),hi.2.1,hi.2.2⟩⟩
    · exact ⟨i,Or.inr (Or.inr (Or.inl ⟨hj'.trans (congrArg u hi.1),hq0.trans (congrArg v hi.1),hi.2.1,hi.2.2⟩))⟩
  · obtain ⟨j,_,hj⟩ := mem_image.mp hp0
    have hj' : p 0 = v j := hj.symm
    have hq0 : q 0 = u j := sourceLadder_double_partner_eq M hdeg (sourceLadder_swap M hOld) j
      (by rw [← hj']; exact hpq 0 0) (by rw [← hj']; exact hNew.2.2.2.1 0)
    have hp1' : p one ∈ Molecule.ladderAtoms v u := by rw [ladderAtoms_swap]; exact hp1
    obtain ⟨i,hi | hi⟩ := sourceLadder_matched_step_alignment M hM (sourceLadder_swap M hOld) j hp1'
      (by rw [← hj']; exact hp.ne h01) (hpq one one) (hNew.2.2.2.1 one)
      (by rw [← hj']; exact hU) (by rw [← hq0]; exact hV)
    · exact ⟨i,Or.inr (Or.inl ⟨hj'.trans (congrArg v hi.1),hq0.trans (congrArg u hi.1),hi.2.1,hi.2.2⟩)⟩
    · exact ⟨i,Or.inr (Or.inr (Or.inr ⟨hj'.trans (congrArg v hi.1),hq0.trans (congrArg u hi.1),hi.2.1,hi.2.2⟩))⟩

end WaveTurbulence.Degen
