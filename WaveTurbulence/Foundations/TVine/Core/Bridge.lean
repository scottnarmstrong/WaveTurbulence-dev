/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.VineLike

/-!
# The bridge B0: molecules and the U-layer (M4 §2.1)

For an atomic group `S` of a molecule `M`, `groupGraph M S` is its undirected multigraph. This module proves that the
pinned molecule-level notions are the U-level ones read in `groupGraph M S`:

* `bondsBetween_eq`, `sigma_eq`, `groupNbrs_eq`, `degIn_eq`, `groupConnected_iff`;
* `isClosure_iff`, `isBlockU_of_isBlock`, `isTVine_iff` (**B0**), `isVine_iff`, `isVineEnl_iff`;
* `cut_groupGraph` (the cut is the number of crossing bonds of `S`), `samePiece_iff`, `pieces_eq`,
  `tvineGroups_eq`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-! ## Bond counts -/

/-- The bonds of the atomic group `S`, each named by its outgoing dart. -/
def groupDarts (S : Finset V) : Finset D := Finset.univ.filter fun x => M.out x = true ∧ M.InGroup S x

theorem mem_groupDarts {S : Finset V} {x : D} :
    x ∈ groupDarts M S ↔ M.out x = true ∧ M.atom x ∈ S ∧ M.atom (M.mate x) ∈ S := by
  rw [groupDarts, Finset.mem_filter]; simp only [Finset.mem_univ, true_and, Molecule.InGroup]

theorem groupGraph_mult_eq_card (S : Finset V) (e : Sym2 V) :
    (groupGraph M S).mult e = ((groupDarts M S).filter fun x => M.ends x = e).card := by
  rw [groupGraph_mult, Molecule.groupBonds, Multiset.count_map, ← Finset.filter_val, Finset.card_val]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, groupDarts]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩

theorem mem_of_ends_eq {S : Finset V} {u v : V} (hu : u ∈ S) (hv : v ∈ S) {x : D} (h : M.ends x = s(u, v)) :
    M.atom x ∈ S ∧ M.atom (M.mate x) ∈ S := by
  simp only [Molecule.ends, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> exact ⟨by assumption, by assumption⟩

theorem bondsBetween_eq {S : Finset V} {u v : V} (hu : u ∈ S) (hv : v ∈ S) :
    M.bondsBetween u v = (groupGraph M S).mult s(u, v) := by
  rw [groupGraph_mult_eq_card, Molecule.bondsBetween]
  congr 1
  ext x
  simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and, mem_groupDarts]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, mem_of_ends_eq M hu hv h2⟩, h2⟩
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩

theorem sigma_eq {S : Finset V} {j₁ j₂ : V} (h₁ : j₁ ∈ S) (h₂ : j₂ ∈ S) :
    M.sigma j₁ j₂ = (groupGraph M S).mult s(j₁, j₂) := bondsBetween_eq M h₁ h₂

/-! ## Neighbours and degrees -/

/-- The darts at `v` of the group `S` with far end `w`: one per bond `{v, w}`, two per loop at `v`. -/
theorem card_dartsFar {S : Finset V} {v w : V} :
    ((M.dartsAt v).filter fun x => M.InGroup S x ∧ M.atom (M.mate x) = w).card =
      (if w = v then 2 else 1) * (groupGraph M S).mult s(v, w) := by
  rw [groupGraph_mult_eq_card]
  have memA : ∀ x, x ∈ (M.dartsAt v).filter (fun x => M.InGroup S x ∧ M.atom (M.mate x) = w) ↔
      M.atom x = v ∧ M.InGroup S x ∧ M.atom (M.mate x) = w := by
    intro x; simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
  have memO : ∀ y, y ∈ (groupDarts M S).filter (fun x => M.ends x = s(v, w)) ↔
      M.out y = true ∧ M.InGroup S y ∧ M.ends y = s(v, w) := by
    intro y; rw [Finset.mem_filter, mem_groupDarts]; simp only [Molecule.InGroup, and_assoc]
  generalize (M.dartsAt v).filter (fun x => M.InGroup S x ∧ M.atom (M.mate x) = w) = A at memA ⊢
  generalize (groupDarts M S).filter (fun x => M.ends x = s(v, w)) = O at memO ⊢
  -- the outgoing darts of `A` are the bonds of `O` sitting at `v`
  have h1 : A.filter (fun x => M.out x = true) = O.filter (fun y => M.atom y = v) := by
    ext x
    simp only [Finset.mem_filter, memA, memO, Molecule.ends]
    constructor
    · rintro ⟨⟨hxv, hg, hxw⟩, ho⟩
      exact ⟨⟨ho, hg, by rw [hxv, hxw]⟩, hxv⟩
    · rintro ⟨⟨ho, hg, he⟩, hxv⟩
      rw [hxv, Sym2.congr_right] at he
      exact ⟨⟨hxv, hg, he⟩, ho⟩
  -- the incoming darts of `A` are the mates of the bonds of `O` sitting at `w`
  have h2 : (A.filter (fun x => ¬ M.out x = true)).card = (O.filter (fun y => M.atom y = w)).card := by
    apply Finset.card_bij' (fun x _ => M.mate x) (fun y _ => M.mate y)
    · intro x hx
      rw [Finset.mem_filter, memA] at hx
      obtain ⟨⟨hxv, hg, hxw⟩, hno⟩ := hx
      rw [Finset.mem_filter, memO]
      refine ⟨⟨by rw [M.out_mate]; simpa using hno, ⟨hg.2, by rw [M.mate_mate]; exact hg.1⟩, ?_⟩, hxw⟩
      rw [Molecule.ends, M.mate_mate, hxv, hxw, Sym2.eq_swap]
    · intro y hy
      rw [Finset.mem_filter, memO] at hy
      obtain ⟨⟨ho, hg, he⟩, hyw⟩ := hy
      have hmv : M.atom (M.mate y) = v := by
        rw [Molecule.ends, hyw, Sym2.eq_swap, Sym2.congr_left] at he
        exact he
      rw [Finset.mem_filter, memA, M.mate_mate, M.out_mate, ho]
      exact ⟨⟨hmv, ⟨hg.2, by rw [M.mate_mate]; exact hg.1⟩, hyw⟩, by simp⟩
    · intro x _; exact M.mate_mate x
    · intro y _; exact M.mate_mate y
  have h3 : (O.filter (fun y => M.atom y = v)).card + (O.filter (fun y => M.atom y = w)).card =
      (if w = v then 2 else 1) * O.card := by
    have hends : ∀ y ∈ O, M.atom y = v ∨ M.atom y = w := by
      intro y hy
      have he := ((memO y).mp hy).2.2
      simp only [Molecule.ends, Sym2.eq_iff] at he
      rcases he with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    split_ifs with hwv
    · subst hwv
      have : O.filter (fun y => M.atom y = w) = O := by
        apply Finset.filter_true_of_mem
        intro y hy
        rcases hends y hy with h | h <;> exact h
      rw [this]; ring
    · have : O.filter (fun y => M.atom y = w) = O.filter (fun y => ¬ M.atom y = v) := by
        apply Finset.filter_congr
        intro y hy
        rcases hends y hy with h | h
        · rw [h]; exact ⟨fun h' => absurd h'.symm hwv, fun h' => absurd rfl h'⟩
        · rw [h]; exact ⟨fun _ => hwv, fun _ => rfl⟩
      rw [this, Finset.card_filter_add_card_filter_not, one_mul]
  rw [← h3, ← h1, ← h2, Finset.card_filter_add_card_filter_not]

theorem count_nbrs (G : UMultigraph V) (v w : V) :
    (nbrs G v).count w = (if w ∈ G.verts then G.mult s(v, w) else 0) + (if v = w then G.mult s(v, v) else 0) := by
  rw [nbrs, Multiset.count_add, Multiset.count_sum', Multiset.count_replicate]
  simp_rw [Multiset.count_replicate]
  rw [Finset.sum_ite_eq']

theorem card_nbrs (G : UMultigraph V) (v : V) : Multiset.card (nbrs G v) = deg G v := by
  rw [nbrs, deg, Multiset.card_add, Multiset.card_sum, Multiset.card_replicate]
  simp_rw [Multiset.card_replicate]

theorem groupNbrs_eq {S : Finset V} {v : V} (hv : v ∈ S) : M.groupNbrs S v = nbrs (groupGraph M S) v := by
  ext w
  rw [count_nbrs, groupGraph_verts, Molecule.groupNbrs, Multiset.count_map, ← Finset.filter_val,
    Finset.card_val, Finset.filter_filter]
  have hc := card_dartsFar M (S := S) (v := v) (w := w)
  have hfe : ((M.dartsAt v).filter fun x => M.InGroup S x ∧ w = M.atom (M.mate x)) =
      (M.dartsAt v).filter fun x => M.InGroup S x ∧ M.atom (M.mate x) = w := by
    apply Finset.filter_congr; intro x _; exact and_congr_right fun _ => eq_comm
  rw [hfe, hc]
  by_cases hw : w ∈ S
  · by_cases hwv : w = v
    · subst hwv; simp [hw]; ring
    · simp [hw, hwv, Ne.symm hwv]
  · have hvw : v ≠ w := fun h => hw (h ▸ hv)
    have : (groupGraph M S).mult s(v, w) = 0 := mult_eq_zero_of_right _ hw v
    simp [hw, hvw, this]

theorem degIn_eq {S : Finset V} {v : V} (hv : v ∈ S) : M.degIn S v = deg (groupGraph M S) v := by
  rw [← card_nbrs, ← groupNbrs_eq M hv, Molecule.groupNbrs, Multiset.card_map, Finset.card_val]
  rfl

theorem degIn_eq_outIn_add_inIn (S : Finset V) (v : V) : M.degIn S v = M.outIn S v + M.inIn S v := by
  rw [Molecule.degIn, Molecule.outIn, Molecule.inIn,
    ← Finset.card_filter_add_card_filter_not (s := (M.dartsAt v).filter fun x => M.InGroup S x)
      (fun x => M.out x = true), Finset.filter_filter, Finset.filter_filter]
  have : ((M.dartsAt v).filter fun x => M.InGroup S x ∧ ¬ M.out x = true) =
      (M.dartsAt v).filter fun x => M.InGroup S x ∧ M.out x = false :=
    Finset.filter_congr (fun x _ => by simp)
  rw [this]

/-! ## Connectivity -/

theorem adjIn_groupGraph_iff {S : Finset V} {a b : V} :
    AdjIn (groupGraph M S) S a b ↔ ∃ x, M.InGroup S x ∧ M.atom x = a ∧ M.atom (M.mate x) = b := by
  rw [AdjIn, groupGraph_mult_eq_card, Finset.card_ne_zero]
  constructor
  · rintro ⟨ha, hb, y, hy⟩
    rw [Finset.mem_filter, mem_groupDarts] at hy; simp only [Molecule.ends, Sym2.eq_iff] at hy
    obtain ⟨⟨_, hy₁, hy₂⟩, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hy
    · exact ⟨y, ⟨hy₁, hy₂⟩, h1, h2⟩
    · exact ⟨M.mate y, ⟨hy₂, by rw [M.mate_mate]; exact hy₁⟩, h2, by rw [M.mate_mate]; exact h1⟩
  · rintro ⟨x, hx, rfl, rfl⟩
    refine ⟨hx.1, hx.2, ?_⟩
    by_cases ho : M.out x = true
    · exact ⟨x, by simp [mem_groupDarts, ho, hx.1, hx.2, Molecule.ends]⟩
    · refine ⟨M.mate x, ?_⟩
      rw [Finset.mem_filter, mem_groupDarts]; simp only [M.out_mate, M.mate_mate, Molecule.ends]
      refine ⟨⟨by simpa using ho, hx.2, hx.1⟩, Sym2.eq_swap⟩

private theorem rtg_symm_of {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (hr _ _ hbc) ih

private theorem eqvGen_iff_rtg {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a) {a b : α} :
    Relation.EqvGen r a b ↔ Relation.ReflTransGen r a b := by
  constructor
  · intro h
    induction h with
    | rel _ _ h => exact .single h
    | refl => exact .refl
    | symm _ _ _ ih => exact rtg_symm_of hr ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    induction h with
    | refl => exact .refl _
    | tail _ h ih => exact .trans _ _ _ ih (.rel _ _ h)

theorem groupConnected_iff {S : Finset V} : M.GroupConnected S ↔ Connected (groupGraph M S) := by
  have hR : AdjIn (groupGraph M S) S = fun a b => ∃ x, M.InGroup S x ∧ M.atom x = a ∧ M.atom (M.mate x) = b := by
    funext a b; exact propext (adjIn_groupGraph_iff M)
  have hs : ∀ a b, (∃ x, M.InGroup S x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) →
      ∃ x, M.InGroup S x ∧ M.atom x = b ∧ M.atom (M.mate x) = a := by
    rintro a b ⟨x, hx, rfl, rfl⟩
    exact ⟨M.mate x, ⟨hx.2, by rw [M.mate_mate]; exact hx.1⟩, rfl, by rw [M.mate_mate]⟩
  unfold Molecule.GroupConnected Connected ConnOn
  rw [groupGraph_verts, hR]
  simp only [eqvGen_iff_rtg hs]

/-! ## Closure, blocks, T-vines (B0), vines -/

theorem count_groupBonds_filter (S : Finset V) (j₁ j₂ : V) (e : Sym2 V) :
    ((M.groupBonds S).filter fun f => j₁ ∉ f ∧ j₂ ∉ f).count e =
      if j₁ ∈ e ∨ j₂ ∈ e then 0 else (groupGraph M S).mult e := by
  rw [Multiset.count_filter, groupGraph_mult]
  by_cases h : j₁ ∈ e ∨ j₂ ∈ e
  · have : ¬ (j₁ ∉ e ∧ j₂ ∉ e) := by tauto
    simp [h, this]
  · have : j₁ ∉ e ∧ j₂ ∉ e := by tauto
    simp [h, this]

theorem isClosure_iff {S : Finset V} {j₁ j₂ : V} (h₁ : j₁ ∈ S) (h₂ : j₂ ∈ S) (C : UMultigraph V) :
    M.IsClosure S j₁ j₂ C ↔ IsClosureU (groupGraph M S) j₁ j₂ C := by
  unfold Molecule.IsClosure IsClosureU
  simp only [sigma_eq M h₁ h₂, groupNbrs_eq M h₁, groupNbrs_eq M h₂, count_groupBonds_filter, groupGraph_verts]

theorem isBlockU_of_isBlock {S : Finset V} {j₁ j₂ : V} (h : M.IsBlock S j₁ j₂) :
    IsBlockU (groupGraph M S) j₁ j₂ := by
  obtain ⟨_, h₁, h₂, hne, ho₁, hi₁, ho₂, hi₂, hdeg, hconn⟩ := h
  refine ⟨h₁, h₂, hne, ?_, ?_, ?_, (groupConnected_iff M).mp hconn⟩
  · rw [← degIn_eq M h₁, degIn_eq_outIn_add_inIn, ho₁, hi₁]
  · rw [← degIn_eq M h₂, degIn_eq_outIn_add_inIn, ho₂, hi₂]
  · intro v hv hv₁ hv₂
    have hv' : v ∈ S := hv
    rw [← degIn_eq M hv']
    exact hdeg v hv' hv₁ hv₂

/-- **B0** (M4 §2.1): a T-vine of the molecule is a block whose undirected multigraph is a U-level T-vine, and
conversely. -/
theorem isTVine_iff {S : Finset V} {j₁ j₂ : V} :
    M.IsTVine S j₁ j₂ ↔ M.IsBlock S j₁ j₂ ∧ IsTVineU (groupGraph M S) j₁ j₂ := by
  constructor
  · rintro ⟨hB, hm, G, G', hC, hr, hT⟩
    have h₁ := hB.2.1
    have h₂ := hB.2.2.1
    refine ⟨hB, isBlockU_of_isBlock M hB, ?_, G, (isClosure_iff M h₁ h₂ G).mp hC, G', hr, hT⟩
    intro u hu v hv huv
    have hu' : u ∈ S := hu
    have hv' : v ∈ S := hv
    rw [← bondsBetween_eq M hu' hv']
    exact hm u hu' v hv' huv
  · rintro ⟨hB, -, hm, C, hC, C', hr, hT⟩
    have h₁ := hB.2.1
    have h₂ := hB.2.2.1
    refine ⟨hB, ?_, C, C', (isClosure_iff M h₁ h₂ C).mpr hC, hr, hT⟩
    intro u hu v hv huv
    rw [bondsBetween_eq M hu hv]
    exact hm u hu v hv huv

theorem isTVineU_of_isTVine {S : Finset V} {j₁ j₂ : V} (h : M.IsTVine S j₁ j₂) :
    IsTVineU (groupGraph M S) j₁ j₂ := ((isTVine_iff M).mp h).2

theorem count_bondMultiset (G : UMultigraph V) (e : Sym2 V) : (bondMultiset G).count e = G.mult e := by
  rw [bondMultiset, Multiset.count_sum']
  simp_rw [Multiset.count_replicate]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (Finset.mem_sym2_iff.mpr fun x hx => G.supp e (Ne.symm hne) x hx)

theorem bondMultiset_groupGraph (S : Finset V) : bondMultiset (groupGraph M S) = M.groupBonds S := by
  ext e; rw [count_bondMultiset, groupGraph_mult]

theorem isVine_iff (X : VineType) {S : Finset V} {j₁ j₂ : V} :
    M.IsVine X S j₁ j₂ ↔ M.IsBlock S j₁ j₂ ∧ IsVineXU X (groupGraph M S) j₁ j₂ := by
  unfold Molecule.IsVine IsVineXU
  rw [bondMultiset_groupGraph, groupGraph_verts]
  constructor
  · rintro ⟨hB, rest⟩; exact ⟨hB, isBlockU_of_isBlock M hB, rest⟩
  · rintro ⟨hB, -, rest⟩; exact ⟨hB, rest⟩

theorem isVineEnl_iff {S : Finset V} {j₁ j₂ : V} :
    M.IsVineEnl S j₁ j₂ ↔ M.IsBlock S j₁ j₂ ∧ IsVineEnlU (groupGraph M S) j₁ j₂ := by
  unfold Molecule.IsVineEnl IsVineEnlU
  rw [isVine_iff, isVine_iff, isTVine_iff]
  constructor
  · rintro (⟨hB, h⟩ | ⟨hB, h⟩ | ⟨hB, h⟩)
    · exact ⟨hB, Or.inl h⟩
    · exact ⟨hB, Or.inr (Or.inl h)⟩
    · exact ⟨hB, Or.inr (Or.inr h)⟩
  · rintro ⟨hB, h | h | h⟩
    · exact Or.inl ⟨hB, h⟩
    · exact Or.inr (Or.inl ⟨hB, h⟩)
    · exact Or.inr (Or.inr ⟨hB, h⟩)

/-! ## Cuts and pieces -/

/-- The bonds of `S` (outgoing darts) with exactly one end in `X`. -/
def crossDarts (S X : Finset V) : Finset D :=
  (groupDarts M S).filter fun y => (M.atom y ∈ X ↔ M.atom (M.mate y) ∉ X)

private theorem sum_fiber_pairs {S X : Finset V} (P : Finset D) (f g : D → V)
    (hP : ∀ y ∈ P, f y ∈ X ∧ g y ∈ S \ X) :
    P.card = ∑ u ∈ X, ∑ w ∈ S \ X, (P.filter fun y => f y = u ∧ g y = w).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := X) (fun y hy => (hP y hy).1)]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := S \ X)
    (fun y hy => (hP y (Finset.mem_filter.mp hy).1).2)]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.filter_filter]

/-- The cut of `X ⊆ S` in `groupGraph M S` is the number of bonds of `S` crossing `X`. -/
theorem cut_groupGraph {S X : Finset V} (hX : X ⊆ S) :
    cut (groupGraph M S) X = (crossDarts M S X).card := by
  set O := groupDarts M S
  set P₁ := O.filter fun y => M.atom y ∈ X ∧ M.atom (M.mate y) ∉ X
  set P₂ := O.filter fun y => M.atom y ∉ X ∧ M.atom (M.mate y) ∈ X
  have hsplit : crossDarts M S X = P₁ ∪ P₂ := by
    ext y; simp only [crossDarts, P₁, P₂, Finset.mem_union, Finset.mem_filter]; tauto
  have hdisj : Disjoint P₁ P₂ := by
    rw [Finset.disjoint_left]; intro y h1 h2
    exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
  have hO : ∀ y ∈ O, M.atom y ∈ S ∧ M.atom (M.mate y) ∈ S := fun y hy => ((mem_groupDarts M).mp hy).2
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  rw [sum_fiber_pairs P₁ M.atom (fun y => M.atom (M.mate y)) (fun y hy => by
      have h := Finset.mem_filter.mp hy
      exact ⟨h.2.1, Finset.mem_sdiff.mpr ⟨(hO y h.1).2, h.2.2⟩⟩)]
  rw [sum_fiber_pairs P₂ (fun y => M.atom (M.mate y)) M.atom (fun y hy => by
      have h := Finset.mem_filter.mp hy
      exact ⟨h.2.2, Finset.mem_sdiff.mpr ⟨(hO y h.1).1, h.2.1⟩⟩)]
  rw [← Finset.sum_add_distrib, cut, groupGraph_verts]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.mem_sdiff] at hw
  have huw : u ≠ w := fun h => hw.2 (h ▸ hu)
  rw [groupGraph_mult_eq_card, Finset.filter_filter, Finset.filter_filter,
    ← Finset.card_union_of_disjoint]
  · congr 1
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, O]; simp only [Molecule.ends, Sym2.eq_iff]
    constructor
    · rintro ⟨hy, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · left; exact ⟨hy, ⟨h1 ▸ hu, h2 ▸ hw.2⟩, h1, h2⟩
      · right; exact ⟨hy, ⟨h1 ▸ hw.2, h2 ▸ hu⟩, h2, h1⟩
    · rintro (⟨hy, -, h1, h2⟩ | ⟨hy, -, h2, h1⟩)
      · exact ⟨hy, Or.inl ⟨h1, h2⟩⟩
      · exact ⟨hy, Or.inr ⟨h1, h2⟩⟩
  · rw [Finset.disjoint_left]
    intro y h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact huw (h1.2.2.1.symm.trans h2.2.2.2)

private theorem cross_iff_of_connectedWithout {S X : Finset V} {a b : V}
    (hc : M.ConnectedWithout S (crossDarts M S X) a b) : (a ∈ X ↔ b ∈ X) := by
  unfold Molecule.ConnectedWithout at hc
  induction hc with
  | rel a b hab =>
    obtain ⟨x, hx, hxF, hmF, rfl, rfl⟩ := hab
    by_cases ho : M.out x = true
    · have : x ∈ groupDarts M S := (mem_groupDarts M).mpr ⟨ho, hx⟩
      simp only [crossDarts, Finset.mem_filter, this, true_and] at hxF
      tauto
    · have : M.mate x ∈ groupDarts M S :=
        (mem_groupDarts M).mpr ⟨by simpa [M.out_mate] using ho, hx.2, by rw [M.mate_mate]; exact hx.1⟩
      simp only [crossDarts, Finset.mem_filter, this, true_and, M.mate_mate] at hmF
      tauto
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem samePiece_iff {S : Finset V} {u w : V} (hu : u ∈ S) :
    M.SamePiece S u w ↔ SamePieceU (groupGraph M S) u w := by
  constructor
  · intro h X hX hcut
    rw [groupGraph_verts] at hX
    have hF : crossDarts M S X ⊆ M.bonds := by
      intro y hy
      simp only [crossDarts, Finset.mem_filter, mem_groupDarts] at hy
      simp [Molecule.bonds, hy.1.1]
    exact cross_iff_of_connectedWithout M
      (h (crossDarts M S X) hF (by rw [← cut_groupGraph M hX]; exact hcut))
  · intro h F hF hcard
    classical
    set X := S.filter fun v => M.ConnectedWithout S F u v
    have hXS : X ⊆ S := Finset.filter_subset _ _
    have hsub : crossDarts M S X ⊆ F := by
      intro y hy
      by_contra hyF
      simp only [crossDarts, Finset.mem_filter, mem_groupDarts] at hy
      obtain ⟨⟨ho, hy₁, hy₂⟩, hcross⟩ := hy
      have hmF : M.mate y ∉ F := by
        intro hm
        have := hF hm
        simp [Molecule.bonds, M.out_mate, ho] at this
      have hstep : M.ConnectedWithout S F (M.atom y) (M.atom (M.mate y)) :=
        .rel _ _ ⟨y, ⟨hy₁, hy₂⟩, hyF, hmF, rfl, rfl⟩
      have hiff : M.atom y ∈ X ↔ M.atom (M.mate y) ∈ X := by
        simp only [X, Finset.mem_filter, hy₁, hy₂, true_and]
        exact ⟨fun h' => .trans _ _ _ h' hstep, fun h' => .trans _ _ _ h' (.symm _ _ hstep)⟩
      tauto
    have hcut : cut (groupGraph M S) X ≤ 2 := by
      rw [cut_groupGraph M hXS]; exact (Finset.card_le_card hsub).trans hcard
    have huX : u ∈ X := Finset.mem_filter.mpr ⟨hu, .refl _⟩
    have := (h X (by rw [groupGraph_verts]; exact hXS) hcut).mp huX
    exact (Finset.mem_filter.mp this).2

theorem pieces_eq (S : Finset V) (j₁ j₂ : V) : M.pieces S j₁ j₂ = piecesU (groupGraph M S) j₁ j₂ := by
  classical
  unfold Molecule.pieces piecesU interior
  rw [groupGraph_verts]
  apply Finset.image_congr
  intro u hu
  apply Finset.filter_congr
  intro w _
  exact samePiece_iff M (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hu))

theorem tvineGroups_eq (S : Finset V) (j₁ j₂ : V) :
    M.tvineGroups S j₁ j₂ = piecesU (groupGraph M S) j₁ j₂ := pieces_eq M S j₁ j₂

end WaveTurbulence.TVine.Core
