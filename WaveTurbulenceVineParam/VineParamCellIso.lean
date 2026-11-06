/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphMatch
public import WaveTurbulenceVineParam.VineParamSkipEquiv
public import WaveTurbulenceVineParam.VineParamRawSourceCell
import Mathlib.Tactic

/-! # The contracted rung cell of a directed graph on `Fin (n+2)`

If the unordered shadow of a directed graph on `Fin (n+2)` is a prescribed six-bond
cell at two atoms `f0 < f1` plus a rest avoiding both, the graph is isomorphic to
the raw source cell (any orientation of the six bonds) over the order preserving
relabeled rest on `Fin n`.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset

variable {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]

/-- Edges touching neither removed atom. -/
@[expose] def touchFree (f0 f1 : ℕ) (ends : β → Fin (n+2) × Fin (n+2)) (e : β) : Prop :=
  (ends e).1.1 ≠ f0 ∧ (ends e).1.1 ≠ f1 ∧ (ends e).2.1 ≠ f0 ∧ (ends e).2.1 ≠ f1

instance (f0 f1 : ℕ) (ends : β → Fin (n+2) × Fin (n+2)) : DecidablePred (touchFree f0 f1 ends) :=
  fun _ => by unfold touchFree; infer_instance

/-- The retained occurrences. -/
@[expose, reducible] def RestEdge (f0 f1 : ℕ) (ends : β → Fin (n+2) × Fin (n+2)) : Type :=
  ↥((univ : Finset β).filter (touchFree f0 f1 ends))

instance (f0 f1 : ℕ) (ends : β → Fin (n+2) × Fin (n+2)) : Fintype (RestEdge f0 f1 ends) := by
  unfold RestEdge; infer_instance

/-- Relabel an atom of `Fin (n+2)` other than the removed two. -/
@[expose] def skipFin (f0 f1 : ℕ) (h : f0 < f1) (h1 : f1 < n+2) (t : Fin (n+2))
    (h0' : t.1 ≠ f0) (h1' : t.1 ≠ f1) : Fin n :=
  ⟨skip2 f0 f1 t.1,skip2_lt_of_ne n f0 f1 t.1 h h1 t.2 h0' h1'⟩

/-- The relabeled retained edges. -/
@[expose] def restEnds (f0 f1 : ℕ) (h : f0 < f1) (h1 : f1 < n+2)
    (ends : β → Fin (n+2) × Fin (n+2)) (e : RestEdge f0 f1 ends) : Fin n × Fin n :=
  (skipFin f0 f1 h h1 (ends e.1).1 (mem_filter.mp e.2).2.1 (mem_filter.mp e.2).2.2.1,
   skipFin f0 f1 h h1 (ends e.1).2 (mem_filter.mp e.2).2.2.2.1 (mem_filter.mp e.2).2.2.2.2)

/-- Relabeled atom, with its two nonremoval facts packaged. -/
@[expose] def skipFinP (f0 f1 : ℕ) (h : f0 < f1) (h1 : f1 < n+2) (t : Fin (n+2))
    (ht : t.1 ≠ f0 ∧ t.1 ≠ f1) : Fin n := skipFin f0 f1 h h1 t ht.1 ht.2

theorem orient_of_or {α : Type*} (d l : α×α) (h : d = l ∨ d = l.swap) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ d = orientPair s l.1 l.2 := by
  rcases h with rfl | rfl
  · exact ⟨1,Or.inl rfl,by simp [orientPair]⟩
  · exact ⟨-1,Or.inr rfl,by simp [orientPair,Prod.swap]⟩

theorem exists_signs_of_forall₂ {α : Type*} (L : List (α×α)) (D : List (α×α))
    (h : List.Forall₂ (fun d l => d = l ∨ d = l.swap) D L) :
    ∃ s : Fin L.length → ℤ, (∀ i, s i = 1 ∨ s i = -1) ∧
      D = List.ofFn (fun j : Fin L.length => orientPair (s j) (L[j.1]'j.2).1 (L[j.1]'j.2).2) := by
  induction h with
  | nil => exact ⟨fun i => i.elim0,fun i => i.elim0,by simp⟩
  | @cons d l D' L' h0 _ ih =>
    obtain ⟨s0,hs0,e0⟩ := orient_of_or d l h0
    obtain ⟨s',hs',e'⟩ := ih
    refine ⟨Fin.cons s0 s',?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hs0
      · simpa using hs' j
    · rw [List.ofFn_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,List.getElem_cons_zero,List.getElem_cons_succ,Fin.val_zero,
        Fin.val_succ]
      rw [← e0,← e']

theorem orientPair_map {α γ : Type*} (f : α → γ) (s : ℤ) (u w : α) :
    Prod.map f f (orientPair s u w) = orientPair s (f u) (f w) := by
  unfold orientPair; split_ifs <;> rfl

/-- The cell shadow list. -/
@[expose] def cellRef (f0 f1 p q c d : ℕ) : List (ℕ×ℕ) :=
  [(p,f0),(q,f1),(f0,f1),(f0,f1),(f0,c),(f1,d)]

theorem exists_cell_orientation (f0 f1 : ℕ) (ends : β → Fin (n+2) × Fin (n+2))
    (p q c d : ℕ) (Rest : Multiset (Sym2 ℕ))
    (hcell : ∀ z ∈ ((cellRef f0 f1 p q c d).map fun e => s(e.1,e.2)),
      ¬ (∀ w ∈ z, w ≠ f0 ∧ w ≠ f1))
    (hRest : ∀ e ∈ Rest, ∀ z ∈ e, z ≠ f0 ∧ z ≠ f1)
    (hU : (univ : Finset β).val.map (fun e => s((ends e).1.1,(ends e).2.1)) =
      (((cellRef f0 f1 p q c d).map fun e => s(e.1,e.2) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) + Rest) :
    (((univ : Finset β).filter (touchFree f0 f1 ends)).val.map
        (fun e => s((ends e).1.1,(ends e).2.1)) = Rest) ∧
    ∃ s : Fin 6 → ℤ, (∀ i, s i = 1 ∨ s i = -1) ∧
      ((univ : Finset β).filter (fun e => ¬ touchFree f0 f1 ends e)).val.map
        (fun e => ((ends e).1.1,(ends e).2.1)) =
      ((List.ofFn fun j : Fin 6 => orientPair (s j) ((cellRef f0 f1 p q c d)[j.1]'(by
        simp [cellRef])).1 ((cellRef f0 f1 p q c d)[j.1]'(by simp [cellRef])).2 :
        List (ℕ×ℕ)) : Multiset (ℕ×ℕ)) := by
  classical
  let Q : Sym2 ℕ → Prop := fun z => ∀ w ∈ z, w ≠ f0 ∧ w ≠ f1
  have hQ : ∀ e, Q s((ends e).1.1,(ends e).2.1) ↔ touchFree f0 f1 ends e := by
    intro e
    simp only [Q,touchFree,Sym2.mem_iff,forall_eq_or_imp,forall_eq]
    tauto
  have hA : (univ : Finset β).val.filter (Q ∘ fun e => s((ends e).1.1,(ends e).2.1)) =
      ((univ : Finset β).filter (touchFree f0 f1 ends)).val := by
    rw [Finset.filter_val]
    exact Multiset.filter_congr (fun e _ => hQ e)
  have hA' : (univ : Finset β).val.filter ((fun z => ¬ Q z) ∘ fun e => s((ends e).1.1,(ends e).2.1)) =
      ((univ : Finset β).filter (fun e => ¬ touchFree f0 f1 ends e)).val := by
    rw [Finset.filter_val]
    exact Multiset.filter_congr (fun e _ => not_congr (hQ e))
  have hcellQ : Multiset.filter Q (((cellRef f0 f1 p q c d).map fun e => s(e.1,e.2) : List (Sym2 ℕ)) :
      Multiset (Sym2 ℕ)) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro z hz
    exact hcell z (by simpa using hz)
  have hcellQ' : Multiset.filter (fun z => ¬ Q z) (((cellRef f0 f1 p q c d).map fun e => s(e.1,e.2) :
      List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) =
      (((cellRef f0 f1 p q c d).map fun e => s(e.1,e.2) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) := by
    rw [Multiset.filter_eq_self]
    intro z hz
    exact hcell z (by simpa using hz)
  have hRestQ : Multiset.filter Q Rest = Rest := by
    rw [Multiset.filter_eq_self]; exact fun e he => hRest e he
  have hRestQ' : Multiset.filter (fun z => ¬ Q z) Rest = 0 := by
    rw [Multiset.filter_eq_nil]; exact fun e he => not_not.mpr (hRest e he)
  have h1 := congrArg (Multiset.filter Q) hU
  have h2 := congrArg (Multiset.filter (fun z => ¬ Q z)) hU
  rw [Multiset.filter_add,hcellQ,hRestQ,zero_add] at h1
  rw [Multiset.filter_add,hcellQ',hRestQ',add_zero] at h2
  rw [Multiset.filter_map,hA] at h1
  rw [Multiset.filter_map,hA'] at h2
  refine ⟨h1,?_⟩
  have h3 := exists_orientation (cellRef f0 f1 p q c d)
    (((univ : Finset β).filter (fun e => ¬ touchFree f0 f1 ends e)).val.map
      (fun e => ((ends e).1.1,(ends e).2.1))) (by
    rw [Multiset.map_map]
    exact h2)
  obtain ⟨D',hD',hF⟩ := h3
  obtain ⟨s,hs,hDs⟩ := exists_signs_of_forall₂ _ D' hF
  refine ⟨s,hs,?_⟩
  rw [hD',hDs]
  rfl


theorem exists_cell_iso (f0 f1 : ℕ) (h : f0 < f1) (h1 : f1 < n+2)
    (ends : β → Fin (n+2) × Fin (n+2)) (p q c d : Fin (n+2))
    (hp : p.1 ≠ f0 ∧ p.1 ≠ f1) (hq : q.1 ≠ f0 ∧ q.1 ≠ f1)
    (hc : c.1 ≠ f0 ∧ c.1 ≠ f1) (hd : d.1 ≠ f0 ∧ d.1 ≠ f1)
    (p' q' c' d' : Fin n) (hp' : p' = skipFinP f0 f1 h h1 p hp) (hq' : q' = skipFinP f0 f1 h h1 q hq)
    (hc' : c' = skipFinP f0 f1 h h1 c hc) (hd' : d' = skipFinP f0 f1 h h1 d hd)
    (Rest : Multiset (Sym2 ℕ)) (hRest : ∀ e ∈ Rest, ∀ z ∈ e, z ≠ f0 ∧ z ≠ f1)
    (hU : (univ : Finset β).val.map (fun e => s((ends e).1.1,(ends e).2.1)) =
      (((cellRef f0 f1 p.1 q.1 c.1 d.1).map fun e => s(e.1,e.2) : List (Sym2 ℕ)) :
        Multiset (Sym2 ℕ)) + Rest) :
    ∃ s : Fin 6 → ℤ, (∀ i, s i = 1 ∨ s i = -1) ∧
      (((univ : Finset β).filter (touchFree f0 f1 ends)).val.map
        (fun e => s((ends e).1.1,(ends e).2.1)) = Rest) ∧
      ((univ : Finset (RestEdge f0 f1 ends)).val.map
          (fun e => s((restEnds f0 f1 h h1 ends e).1.1,(restEnds f0 f1 h h1 ends e).2.1)) =
        Rest.map (Sym2.map (skip2 f0 f1))) ∧
      ∃ I : DirectedGraphIso ends (rawSourceCellEnds (restEnds f0 f1 h h1 ends) p' q' c' d' s),
        ∀ v, I.atom v = skipEquiv n f0 f1 h h1 v := by
  classical
  subst hp' hq' hc' hd'
  have hcell : ∀ z ∈ ((cellRef f0 f1 p.1 q.1 c.1 d.1).map fun e => s(e.1,e.2)),
      ¬ (∀ w ∈ z, w ≠ f0 ∧ w ≠ f1) := by
    intro z hz hall
    simp only [cellRef,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hall f0 (Sym2.mem_mk_right _ _)).1 rfl
    · exact (hall f1 (Sym2.mem_mk_right _ _)).2 rfl
    · exact (hall f0 (Sym2.mem_mk_left _ _)).1 rfl
    · exact (hall f0 (Sym2.mem_mk_left _ _)).1 rfl
    · exact (hall f0 (Sym2.mem_mk_left _ _)).1 rfl
    · exact (hall f1 (Sym2.mem_mk_left _ _)).2 rfl
  obtain ⟨hrest,s,hs,hD⟩ := exists_cell_orientation f0 f1 ends p.1 q.1 c.1 d.1 Rest hcell hRest hU
  refine ⟨s,hs,hrest,?_,?_⟩
  · have hu := univ_subtype_map ((univ : Finset β).filter (touchFree f0 f1 ends))
      (fun e => s((ends e).1.1,(ends e).2.1))
    rw [← hrest,← hu,Multiset.map_map]
    apply Multiset.map_congr rfl
    intro e _
    rfl
  let φ := skipEquiv n f0 f1 h h1
  let ℓ : Fin n ⊕ Fin 2 → ℕ := fun w => (φ.symm w).1
  let Γ := rawSourceCellEnds (restEnds f0 f1 h h1 ends)
    (skipFin f0 f1 h h1 p hp.1 hp.2) (skipFin f0 f1 h h1 q hq.1 hq.2)
    (skipFin f0 f1 h h1 c hc.1 hc.2) (skipFin f0 f1 h h1 d hd.1 hd.2) s
  have hℓl : ∀ (t : Fin (n+2)) (h0 : t.1 ≠ f0) (h1' : t.1 ≠ f1),
      ℓ (Sum.inl (skipFin f0 f1 h h1 t h0 h1')) = t.1 := by
    intro t h0 h1'
    exact unskip2_skip2 f0 f1 t.1 h h0 h1'
  have hℓ0 : ℓ (Sum.inr 0) = f0 := by simp [ℓ,φ,skipEquiv]
  have hℓ1 : ℓ (Sum.inr 1) = f1 := by simp [ℓ,φ,skipEquiv]
  let f : β → ℕ×ℕ := fun e => ((ends e).1.1,(ends e).2.1)
  let g : RestEdge f0 f1 ends ⊕ Fin 6 → ℕ×ℕ := fun y => (ℓ (Γ y).1,ℓ (Γ y).2)
  have hmap : (univ : Finset β).val.map f =
      (univ : Finset (RestEdge f0 f1 ends ⊕ Fin 6)).val.map g := by
    have hsum : (univ : Finset (RestEdge f0 f1 ends ⊕ Fin 6)).val.map g =
        (univ : Finset (RestEdge f0 f1 ends)).val.map (fun y => g (Sum.inl y)) +
          (univ : Finset (Fin 6)).val.map (fun y => g (Sum.inr y)) := by
      change ((univ : Finset (RestEdge f0 f1 ends)).disjSum (univ : Finset (Fin 6))).val.map g = _
      rw [Finset.val_disjSum,Multiset.map_disjSum]
    rw [hsum]
    have hl : (fun y : RestEdge f0 f1 ends => g (Sum.inl y)) = fun y => f y.1 := by
      funext y
      have hy := (mem_filter.mp y.2).2
      change (ℓ (Sum.inl (skipFin f0 f1 h h1 (ends y.1).1 hy.1 hy.2.1)),
        ℓ (Sum.inl (skipFin f0 f1 h h1 (ends y.1).2 hy.2.2.1 hy.2.2.2))) = _
      rw [hℓl,hℓl]
    have hr : (fun y : Fin 6 => g (Sum.inr y)) =
        fun j => orientPair (s j) ((cellRef f0 f1 p.1 q.1 c.1 d.1)[j.1]'(by simp [cellRef])).1
          ((cellRef f0 f1 p.1 q.1 c.1 d.1)[j.1]'(by simp [cellRef])).2 := by
      funext j
      change Prod.map ℓ ℓ (orientPair (s j) _ _) = _
      rw [orientPair_map]
      have hpl := hℓl p hp.1 hp.2
      have hql := hℓl q hq.1 hq.2
      have hcl := hℓl c hc.1 hc.2
      have hdl := hℓl d hd.1 hd.2
      fin_cases j <;> simp [sourceCellPorts,cellRef,hpl,hql,hcl,hdl,hℓ0,hℓ1]
    rw [hl,hr,univ_subtype_map ((univ : Finset β).filter (touchFree f0 f1 ends)) f,Fin.univ_val_map]
    rw [← hD]
    rw [← Multiset.map_add]
    congr 1
    rw [Finset.filter_val,Finset.filter_val]
    exact (Multiset.filter_add_not _ _).symm
  obtain ⟨e,he⟩ := exists_label_matching f g hmap
  refine ⟨{ atom := φ,edge := e,endpoints := ?_ },fun v => rfl⟩
  intro x
  have hx := he x
  have h1x := congrArg Prod.fst hx
  have h2x := congrArg Prod.snd hx
  apply Prod.ext
  · exact φ.symm_apply_eq.mp (Fin.ext h1x)
  · exact φ.symm_apply_eq.mp (Fin.ext h2x)

end WaveTurbulence.Vine.Param
