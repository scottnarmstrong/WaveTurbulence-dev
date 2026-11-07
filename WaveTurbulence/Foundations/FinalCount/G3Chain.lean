/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Bal
/-! **FINALCOUNT-G3: boundary count of a connected balanced set of atoms.**  If `C` is a connected set of atoms, each
with exactly one outgoing and one incoming dart, then `C` has at most one outgoing and one incoming boundary dart
(a connected graph on `n` vertices has `≥ n-1` edges); if `C` is not closed it has exactly one of each. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem Adj_symm' {u v : V} (h : M.Adj u v) : M.Adj v u := by
  obtain ⟨z, h1, h2⟩ := h
  exact ⟨M.mate z, h2, by rw [M.mate_mate]; exact h1⟩

theorem card_darts_in (C : Finset V) (p : D → Prop) [DecidablePred p] :
    (Finset.univ.filter fun x => p x ∧ M.atom x ∈ C).card = ∑ c ∈ C, ((M.dartsAt c).filter p).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := M.atom) (t := C) (fun x hx => by
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx.2)]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Molecule.dartsAt]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩; exact ⟨⟨h1, h2 ▸ ‹_›⟩, h2⟩


/-- Outgoing boundary darts of `C`. -/
def outBd (C : Finset V) : Finset D :=
  Finset.univ.filter fun x => M.out x = true ∧ M.atom x ∈ C ∧ M.atom (M.mate x) ∉ C
/-- Incoming boundary darts of `C`. -/
def inBd (C : Finset V) : Finset D :=
  Finset.univ.filter fun x => M.out x = false ∧ M.atom x ∈ C ∧ M.atom (M.mate x) ∉ C
/-- Internal bonds of `C`, by their outgoing dart. -/
def intBd (C : Finset V) : Finset D :=
  Finset.univ.filter fun x => M.out x = true ∧ M.atom x ∈ C ∧ M.atom (M.mate x) ∈ C

theorem out_card_eq {C : Finset V} (hbal : ∀ c ∈ C, M.outdeg c = 1 ∧ M.indeg c = 1) :
    (Finset.univ.filter fun x => M.out x = true ∧ M.atom x ∈ C).card = C.card := by
  rw [card_darts_in M C (fun x => M.out x = true)]
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl fun c hc => (hbal c hc).1

theorem in_card_eq {C : Finset V} (hbal : ∀ c ∈ C, M.outdeg c = 1 ∧ M.indeg c = 1) :
    (Finset.univ.filter fun x => M.out x = false ∧ M.atom x ∈ C).card = C.card := by
  rw [card_darts_in M C (fun x => M.out x = false)]
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl fun c hc => (hbal c hc).2

theorem outBd_add_intBd (C : Finset V) :
    (outBd M C).card + (intBd M C).card = (Finset.univ.filter fun x => M.out x = true ∧ M.atom x ∈ C).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [outBd, intBd, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [outBd, intBd, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h1.2.2 h2.2.2

theorem inBd_add_intBd (C : Finset V) :
    (inBd M C).card + (intBd M C).card = (Finset.univ.filter fun x => M.out x = false ∧ M.atom x ∈ C).card := by
  have hint : (Finset.univ.filter fun x => M.out x = false ∧ M.atom x ∈ C ∧ M.atom (M.mate x) ∈ C).card =
      (intBd M C).card := by
    refine Finset.card_bij (fun x _ => M.mate x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [intBd, Finset.mem_filter, Finset.mem_univ, true_and, M.out_mate, hx.1, M.mate_mate]
      exact ⟨rfl, hx.2.2, hx.2.1⟩
    · intro x _ y _ e; simpa [M.mate_mate] using congrArg M.mate e
    · intro y hy
      simp only [intBd, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨M.mate y, ?_, M.mate_mate y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, M.out_mate, hy.1, M.mate_mate]
      exact ⟨rfl, hy.2.2, hy.2.1⟩
  rw [← hint, ← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [inBd, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [inBd, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h1.2.2 h2.2.2


/-- The simple graph on `C` induced by adjacency of atoms. -/
def indGraph (C : Finset V) : SimpleGraph C where
  Adj a b := a ≠ b ∧ M.Adj a.1 b.1
  symm := ⟨fun a b h => ⟨h.1.symm, Adj_symm' M h.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

theorem indGraph_connected {C : Finset V} {a₀ : V} (ha₀ : a₀ ∈ C)
    (hconn : ∀ c ∈ C, Relation.ReflTransGen (fun x y => M.Adj x y ∧ y ∈ C) a₀ c) :
    (indGraph M C).Connected := by
  have key : ∀ c, Relation.ReflTransGen (fun x y => M.Adj x y ∧ y ∈ C) a₀ c →
      ∃ h : c ∈ C, (indGraph M C).Reachable ⟨a₀, ha₀⟩ ⟨c, h⟩ := by
    intro c hc
    induction hc with
    | refl => exact ⟨ha₀, SimpleGraph.Reachable.refl _⟩
    | @tail b c' _ hs ih =>
      obtain ⟨hb, hr⟩ := ih
      refine ⟨hs.2, ?_⟩
      by_cases hbc : b = c'
      · subst hbc; exact hr
      · exact hr.trans (SimpleGraph.Adj.reachable ⟨fun e => hbc (congrArg Subtype.val e), hs.1⟩)
  have : Nonempty C := ⟨⟨a₀, ha₀⟩⟩
  refine SimpleGraph.Connected.mk ?_
  intro u v
  obtain ⟨_, hu⟩ := key u.1 (hconn u.1 u.2)
  obtain ⟨_, hv⟩ := key v.1 (hconn v.1 v.2)
  exact hu.symm.trans hv

theorem card_le_intBd_add_one {C : Finset V} {a₀ : V} (ha₀ : a₀ ∈ C)
    (hconn : ∀ c ∈ C, Relation.ReflTransGen (fun x y => M.Adj x y ∧ y ∈ C) a₀ c) :
    C.card ≤ (intBd M C).card + 1 := by
  have hc := (indGraph_connected M ha₀ hconn).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hc
  have hE : Nat.card (indGraph M C).edgeSet ≤ (intBd M C).card := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    let φ : D → Sym2 C := fun x =>
      if h : M.atom x ∈ C ∧ M.atom (M.mate x) ∈ C then s(⟨M.atom x, h.1⟩, ⟨M.atom (M.mate x), h.2⟩)
      else s((⟨a₀, ha₀⟩ : C), (⟨a₀, ha₀⟩ : C))
    refine Finset.card_le_card_of_surjOn φ ?_
    intro e he
    have he' : e ∈ (indGraph M C).edgeSet := by simpa using he
    induction e using Sym2.ind with
    | h u v =>
      have huv : (indGraph M C).Adj u v := he'
      obtain ⟨z, hz1, hz2⟩ := huv.2
      by_cases hz : M.out z = true
      · refine ⟨z, ?_, ?_⟩
        · simp only [intBd, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
          exact ⟨hz, hz1 ▸ u.2, hz2 ▸ v.2⟩
        · have h : M.atom z ∈ C ∧ M.atom (M.mate z) ∈ C := ⟨hz1 ▸ u.2, hz2 ▸ v.2⟩
          simp only [φ, dif_pos h]
          rw [Sym2.eq_iff]; left; exact ⟨Subtype.ext hz1, Subtype.ext hz2⟩
      · have hz' : M.out z = false := by simpa using hz
        have hm : M.out (M.mate z) = true := by rw [M.out_mate, hz']; rfl
        refine ⟨M.mate z, ?_, ?_⟩
        · simp only [intBd, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, M.mate_mate]
          exact ⟨hm, hz2 ▸ v.2, hz1 ▸ u.2⟩
        · have h : M.atom (M.mate z) ∈ C ∧ M.atom (M.mate (M.mate z)) ∈ C := ⟨hz2 ▸ v.2, by rw [M.mate_mate]; exact hz1 ▸ u.2⟩
          simp only [φ, dif_pos h]
          rw [Sym2.eq_iff]; right; exact ⟨Subtype.ext hz2, Subtype.ext (by show M.atom (M.mate (M.mate z)) = u.1; simpa [M.mate_mate] using hz1)⟩
  omega

/-- **Boundary count.** -/
theorem boundary_card {C : Finset V} {a₀ : V} (ha₀ : a₀ ∈ C)
    (hbal : ∀ c ∈ C, M.outdeg c = 1 ∧ M.indeg c = 1)
    (hconn : ∀ c ∈ C, Relation.ReflTransGen (fun x y => M.Adj x y ∧ y ∈ C) a₀ c)
    (hex : ∃ x, M.atom x ∈ C ∧ M.atom (M.mate x) ∉ C) :
    (outBd M C).card = 1 ∧ (inBd M C).card = 1 := by
  have h1 := outBd_add_intBd M C
  have h2 := inBd_add_intBd M C
  rw [out_card_eq M hbal] at h1
  rw [in_card_eq M hbal] at h2
  have h3 := card_le_intBd_add_one M ha₀ hconn
  have hpos : 0 < (outBd M C).card + (inBd M C).card := by
    obtain ⟨x, hx1, hx2⟩ := hex
    by_cases ho : M.out x = true
    · have : x ∈ outBd M C := by simp [outBd, ho, hx1, hx2]
      have := Finset.card_pos.2 ⟨x, this⟩; omega
    · have ho' : M.out x = false := by simpa using ho
      have : x ∈ inBd M C := by simp [inBd, ho', hx1, hx2]
      have := Finset.card_pos.2 ⟨x, this⟩; omega
  omega

end WaveTurbulence.FinalCountG3
