/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineInsertionPaths
public import WaveTurbulence.Foundations.Molecule.VineEndpointBounds
import Mathlib.Tactic

/-! # Paths within the nonjoint atoms of a vine template -/

public section
namespace WaveTurbulence.Vine

/-- An edge between two nonjoint labels. -/
@[expose] def InteriorAdj (es : List (ℕ×ℕ)) (u v : ℕ) : Prop :=
  2 ≤ u ∧ 2 ≤ v ∧ EdgeAdj es u v

instance (es : List (ℕ×ℕ)) (u v : ℕ) : Decidable (InteriorAdj es u v) := by
  unfold InteriorAdj
  infer_instance

/-- Connectivity of the nonjoint atom interval, rooted at label 2 whenever
that interval is nonempty. Type I has no nonjoint atoms. -/
@[expose] def InteriorConnected (T : VineTemplate) : Prop :=
  ∀ v,2 ≤ v → v<T.n → Relation.EqvGen (InteriorAdj T.bonds) 2 v

/-- Edges of a rail stay above a lower bound shared by all rail vertices. -/
theorem railBonds_lower (a b l : ℕ) (ws : List ℕ) (ha : l ≤ a) (hb : l ≤ b)
    (hw : ∀ w ∈ ws,l ≤ w) (e : ℕ×ℕ) (he : e ∈ railBonds a ws b) : l ≤ e.1 ∧ l ≤ e.2 := by
  obtain ⟨h1,h2⟩ := List.of_mem_zip he
  constructor
  · rcases List.mem_cons.mp h1 with h | h
    · exact h ▸ ha
    · exact hw _ h
  · rcases List.mem_append.mp h2 with h | h
    · exact hw _ h
    · exact List.mem_singleton.mp h ▸ hb

/-- A path whose every edge endpoint is nonjoint is an interior path. -/
theorem interior_path_of_path {es : List (ℕ×ℕ)}
    (hb : ∀ e ∈ es,2 ≤ e.1 ∧ 2 ≤ e.2) {u v : ℕ}
    (hp : Relation.EqvGen (EdgeAdj es) u v) : Relation.EqvGen (InteriorAdj es) u v := by
  induction hp with
  | rel u v huv =>
    have hlow : 2 ≤ u ∧ 2 ≤ v := huv.elim (fun h => hb _ h) (fun h => (hb _ h).symm)
    exact Relation.EqvGen.rel _ _ ⟨hlow.1,hlow.2,huv⟩
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- Adding bonds preserves interior paths. -/
theorem interior_path_mono {es fs : List (ℕ×ℕ)} (h : ∀ e ∈ es,e ∈ fs) {u v : ℕ}
    (hp : Relation.EqvGen (InteriorAdj es) u v) : Relation.EqvGen (InteriorAdj fs) u v := by
  induction hp with
  | rel u v huv => exact Relation.EqvGen.rel _ _ ⟨huv.1,huv.2.1,
      huv.2.2.elim (fun he => Or.inl (h _ he)) (fun he => Or.inr (h _ he))⟩
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- A fresh rail atom reaches the initial port without using the final
port. Thus the final port may be a joint, as in type II (F72). -/
theorem interior_rail_mem_prefix (a b : ℕ) (ws : List ℕ) (ha : 2 ≤ a)
    (hw : ∀ w ∈ ws, 2 ≤ w) {v : ℕ} (hv : v ∈ ws) :
    Relation.EqvGen (InteriorAdj (railBonds a ws b)) a v := by
  induction ws generalizing a with
  | nil => exact False.elim (List.not_mem_nil hv)
  | cons w ws ih =>
    change Relation.EqvGen (InteriorAdj ((a,w)::railBonds w ws b)) a v
    have hw2 := hw w List.mem_cons_self
    have he : InteriorAdj ((a,w)::railBonds w ws b) a w :=
      ⟨ha,hw2,Or.inl List.mem_cons_self⟩
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Relation.EqvGen.rel _ _ he
    · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ he)
        (interior_path_mono (fun _ h => List.mem_cons_of_mem _ h)
          (ih w hw2 (fun x hx => hw x (List.mem_cons_of_mem _ hx)) hv))

/-- An interior old edge is replaced by an interior path at every rung count. -/
theorem insertion_interior_edge_path (T : VineTemplate) (hn : 2 ≤ T.n)
    (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) {a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (he : (a,b) ∈ T.bonds) :
    Relation.EqvGen (InteriorAdj (insertRungs T s k).bonds) a b := by
  by_cases hk : k=0
  · rw [hk,insertRungs_zero]
    exact Relation.EqvGen.rel _ _ ⟨ha,hb,Or.inl he⟩
  · by_cases h1 : (a,b)=s.1
    · have hp := interior_path_of_path
        (railBonds_lower a b 2 ((List.range k).map (T.n+·)) ha hb (by
          intro w hw
          obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hw
          omega)) (rail_path a b ((List.range k).map (T.n+·)))
      apply interior_path_mono _ hp
      intro e he
      apply first_rail_mem T s hk
      simpa only [← h1] using he
    · by_cases h2 : (a,b)=s.2
      · have hp := interior_path_of_path
          (railBonds_lower a b 2 ((List.range k).map (T.n+k+·)) ha hb (by
            intro w hw
            obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hw
            omega)) (rail_path a b ((List.range k).map (T.n+k+·)))
        apply interior_path_mono _ hp
        intro e he
        apply second_rail_mem T s hk
        simpa only [← h2] using he
      · exact Relation.EqvGen.rel _ _ ⟨ha,hb,Or.inl (mem_insertRungs_bonds he h1 h2 k)⟩

/-- All old interior paths survive arbitrary rung insertion. -/
theorem insertion_interior_path (T : VineTemplate) (hn : 2 ≤ T.n)
    (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) {a b : ℕ}
    (hp : Relation.EqvGen (InteriorAdj T.bonds) a b) :
    Relation.EqvGen (InteriorAdj (insertRungs T s k).bonds) a b := by
  induction hp with
  | rel u v huv =>
    rcases huv.2.2 with he | he
    · exact insertion_interior_edge_path T hn s k huv.1 huv.2.1 he
    · exact Relation.EqvGen.symm _ _ (insertion_interior_edge_path T hn s k huv.2.1 huv.1 he)
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end WaveTurbulence.Vine
