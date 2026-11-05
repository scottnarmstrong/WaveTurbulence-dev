/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRailAvoidPaths
import Mathlib.Tactic

/-! # Subdivision of one edge preserves absence of separating atoms -/

public section
namespace WaveTurbulence.Vine

/-- Replace a single encoded bond occurrence by a rail of fresh atoms. -/
@[expose] def subdivideBonds (n : ℕ) (es : List (ℕ×ℕ)) (a b k : ℕ) : List (ℕ×ℕ) :=
  es.erase (a,b) ++ railBonds a ((List.range k).map (n+·)) b

/-- Old surviving atoms remain connected when one old bond is subdivided,
even when the removed atom lies on its replacement rail. -/
theorem subdivide_old_connected {n : ℕ} {es : List (ℕ×ℕ)}
    (hc : VertexConnected n es) (hb : EdgeBounded n es) (hn : 3 ≤ n)
    (a b k : ℕ) (ha : a<n) (hbn : b<n) (hab : a ≠ b)
    (z u v : ℕ) (hu : u<n) (hv : v<n) (huz : u ≠ z) (hvz : v ≠ z) :
    AvoidPath (subdivideBonds n es a b k) z u v := by
  have hkeep : ∀ e ∈ es.erase (a,b),e ∈ subdivideBonds n es a b k :=
    fun _ h => List.mem_append_left _ h
  have hrail : ∀ e ∈ railBonds a ((List.range k).map (n+·)) b,
      e ∈ subdivideBonds n es a b k := fun _ h => List.mem_append_right _ h
  have hedge : ∀ x y,AvoidAdj es z x y →
      AvoidPath (subdivideBonds n es a b k) z x y := by
    intro x y hxy
    have orient (x y : ℕ) (hxz : x ≠ z) (hyz : y ≠ z) (he : (x,y) ∈ es) :
        AvoidPath (subdivideBonds n es a b k) z x y := by
      by_cases heq : (x,y)=(a,b)
      · have hxa : x=a := congrArg Prod.fst heq
        have hyb : y=b := congrArg Prod.snd heq
        subst x
        subst y
        by_cases hz : z<n
        · have hw : ∀ w ∈ (List.range k).map (n+·),w ≠ z := by
            intro w hw
            obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hw
            omega
          exact avoidPath_mono hrail (rail_avoid_path a b z _ hxz hyz hw)
        · exact avoidPath_mono hkeep (hc.erase_edge_path hb hn ha hbn hab z (by omega))
      · exact Relation.EqvGen.rel _ _ ⟨hxz,hyz,Or.inl
          (hkeep _ ((List.mem_erase_of_ne heq).mpr he))⟩
    rcases hxy.2.2 with he | he
    · exact orient x y hxy.1 hxy.2.1 he
    · exact Relation.EqvGen.symm _ _ (orient y x hxy.2.1 hxy.1 he)
  exact avoidPath_lift hedge (hc z u v hu hv huz hvz)

/-- Every surviving fresh atom reaches a surviving old endpoint along its
rail. The nodup condition needed for a removed fresh atom follows from allocation. -/
theorem subdivide_fresh_attachment (n : ℕ) (es : List (ℕ×ℕ)) (a b k z v : ℕ)
    (ha : a<n) (hb : b<n) (hab : a ≠ b) (hv : n ≤ v) (hvn : v<n+k) (hvz : v ≠ z) :
    ∃ p,p<n ∧ p ≠ z ∧ AvoidPath (subdivideBonds n es a b k) z p v := by
  let ws := (List.range k).map (n+·)
  have hvm : v ∈ ws := by
    refine List.mem_map.mpr ⟨v-n,List.mem_range.mpr (by omega),?_⟩
    omega
  have hrail : ∀ e ∈ railBonds a ws b,e ∈ subdivideBonds n es a b k :=
    fun _ h => List.mem_append_right _ h
  by_cases hz : z<n
  · have hw : ∀ w ∈ ws,w ≠ z := by
      intro w hw
      obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hw
      omega
    by_cases haz : a=z
    · have hbz : b ≠ z := by omega
      exact ⟨b,hb,hbz,avoidPath_mono hrail (rail_mem_avoid_end a b z ws hbz hw hvm)⟩
    · exact ⟨a,ha,haz,avoidPath_mono hrail (rail_mem_avoid_start a b z ws haz hw hvm)⟩
  · have hd : ws.Nodup := (show (List.range k).Nodup from List.nodup_range).map (fun _ _ h => Nat.add_left_cancel h)
    obtain ⟨p,hp,hpath⟩ := rail_mem_avoid_endpoint a b z ws hd (by omega) (by omega) hvm hvz
    refine ⟨p,?_,?_,avoidPath_mono hrail hpath⟩
    · rcases hp with rfl | rfl <;> assumption
    · omega

/-- Subdividing any old nonloop edge in a graph with at least three atoms
preserves connectivity after removal of any single atom. -/
theorem subdivide_vertexConnected {n : ℕ} {es : List (ℕ×ℕ)}
    (hc : VertexConnected n es) (hb : EdgeBounded n es) (hn : 3 ≤ n)
    (a b k : ℕ) (ha : a<n) (hbn : b<n) (hab : a ≠ b) :
    VertexConnected (n+k) (subdivideBonds n es a b k) := by
  intro z u v hu hv huz hvz
  have attach (w : ℕ) (hw : w<n+k) (hwz : w ≠ z) :
      ∃ p,p<n ∧ p ≠ z ∧ AvoidPath (subdivideBonds n es a b k) z p w := by
    by_cases hwo : w<n
    · exact ⟨w,hwo,hwz,Relation.EqvGen.refl _⟩
    · exact subdivide_fresh_attachment n es a b k z w ha hbn hab (by omega) hw hwz
  obtain ⟨p,hp,hpz,hpu⟩ := attach u hu huz
  obtain ⟨q,hq,hqz,hqv⟩ := attach v hv hvz
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpu)
    (Relation.EqvGen.trans _ _ _ (subdivide_old_connected hc hb hn a b k ha hbn hab z p q hp hq hpz hqz) hqv)

end WaveTurbulence.Vine
