/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VinePaths
import Mathlib.Tactic

/-! # Undirected paths avoiding one atom -/

public section
namespace WaveTurbulence.Vine

/-- An edge with neither endpoint equal to the removed atom. -/
@[expose] def AvoidAdj (es : List (ℕ×ℕ)) (z u v : ℕ) : Prop :=
  u ≠ z ∧ v ≠ z ∧ EdgeAdj es u v

instance (es : List (ℕ×ℕ)) (z u v : ℕ) : Decidable (AvoidAdj es z u v) := by
  unfold AvoidAdj
  infer_instance

/-- A path which uses no edge incident to the removed atom. Endpoints are
required to differ from that atom when connectivity is asserted. -/
@[expose] def AvoidPath (es : List (ℕ×ℕ)) (z u v : ℕ) : Prop :=
  Relation.EqvGen (AvoidAdj es z) u v

/-- A template remains connected after removal of any one atom. -/
@[expose] def VertexConnected (n : ℕ) (es : List (ℕ×ℕ)) : Prop :=
  ∀ z u v,u<n → v<n → u ≠ z → v ≠ z → AvoidPath es z u v

/-- Replacing each allowed edge by an allowed path transports every path. -/
theorem avoidPath_lift {es fs : List (ℕ×ℕ)} {z w : ℕ}
    (h : ∀ u v,AvoidAdj es z u v → AvoidPath fs w u v)
    {u v : ℕ} (hp : AvoidPath es z u v) : AvoidPath fs w u v := by
  induction hp with
  | rel u v huv => exact h u v huv
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- Adding edges preserves every path avoiding an atom. -/
theorem avoidPath_mono {es fs : List (ℕ×ℕ)} (h : ∀ e ∈ es,e ∈ fs)
    {z u v : ℕ} (hp : AvoidPath es z u v) : AvoidPath fs z u v := by
  apply avoidPath_lift (fun u v huv => ?_) hp
  refine Relation.EqvGen.rel _ _ ⟨huv.1,huv.2.1,?_⟩
  exact huv.2.2.elim (fun he => Or.inl (h _ he)) (fun he => Or.inr (h _ he))

/-- Every edge endpoint lies in the declared finite atom interval. -/
@[expose] def EdgeBounded (n : ℕ) (es : List (ℕ×ℕ)) : Prop :=
  ∀ e ∈ es,e.1<n ∧ e.2<n

/-- An undirected old edge has two old endpoints. -/
theorem EdgeBounded.adj {n : ℕ} {es : List (ℕ×ℕ)} (h : EdgeBounded n es)
    {u v : ℕ} (he : EdgeAdj es u v) : u<n ∧ v<n := by
  rcases he with he | he
  · exact h _ he
  · exact (h _ he).symm

/-- A path avoiding an endpoint of a deleted edge uses only retained edges.
Any atom outside the old interval can be excluded simultaneously. -/
theorem avoidPath_erase_edge {n : ℕ} {es : List (ℕ×ℕ)} (hb : EdgeBounded n es)
    (a b w : ℕ) (hw : n ≤ w) {u v : ℕ} (h : AvoidPath es a u v) :
    AvoidPath (es.erase (a,b)) w u v := by
  apply avoidPath_lift (fun x y hxy => ?_) h
  have hbounds := hb.adj hxy.2.2
  refine Relation.EqvGen.rel _ _ ⟨by omega,by omega,?_⟩
  rcases hxy.2.2 with he | he
  · exact Or.inl ((List.mem_erase_of_ne (by intro hh; have := congrArg Prod.fst hh; exact hxy.1 this)).mpr he)
  · exact Or.inr ((List.mem_erase_of_ne (by intro hh; have := congrArg Prod.fst hh; exact hxy.2.1 this)).mpr he)

/-- An old path avoiding the other endpoint also survives the deletion. -/
theorem avoidPath_erase_edge_other {n : ℕ} {es : List (ℕ×ℕ)} (hb : EdgeBounded n es)
    (a b w : ℕ) (hw : n ≤ w) {u v : ℕ} (h : AvoidPath es b u v) :
    AvoidPath (es.erase (a,b)) w u v := by
  apply avoidPath_lift (fun x y hxy => ?_) h
  have hbounds := hb.adj hxy.2.2
  refine Relation.EqvGen.rel _ _ ⟨by omega,by omega,?_⟩
  rcases hxy.2.2 with he | he
  · exact Or.inl ((List.mem_erase_of_ne (by intro hh; have := congrArg Prod.snd hh; exact hxy.2.1 this)).mpr he)
  · exact Or.inr ((List.mem_erase_of_ne (by intro hh; have := congrArg Prod.snd hh; exact hxy.1 this)).mpr he)

/-- In a graph without a separating atom, deleting an edge still leaves
its endpoints connected. The third atom provides two paths avoiding the
opposite endpoints; neither can use the deleted edge. -/
theorem VertexConnected.erase_edge_path {n : ℕ} {es : List (ℕ×ℕ)}
    (hc : VertexConnected n es) (hb : EdgeBounded n es) (hn : 3 ≤ n)
    {a b : ℕ} (ha : a<n) (hbn : b<n) (hab : a ≠ b) (w : ℕ) (hw : n ≤ w) :
    AvoidPath (es.erase (a,b)) w a b := by
  have hex : ∃ c,c<n ∧ c ≠ a ∧ c ≠ b := by
    by_cases ha0 : a=0
    · by_cases hb1 : b=1
      · exact ⟨2,by omega,by omega,by omega⟩
      · exact ⟨1,by omega,by omega,by omega⟩
    · by_cases hb0 : b=0
      · by_cases ha1 : a=1
        · exact ⟨2,by omega,by omega,by omega⟩
        · exact ⟨1,by omega,by omega,by omega⟩
      · exact ⟨0,by omega,by omega,by omega⟩
  obtain ⟨c,hcn,hca,hcb⟩ := hex
  have hp := hc b a c ha hcn hab hcb
  have hq := hc a c b hcn hbn hca hab.symm
  exact Relation.EqvGen.trans _ _ _
    (avoidPath_erase_edge_other hb a b w hw hp)
    (avoidPath_erase_edge hb a b w hw hq)

end WaveTurbulence.Vine
