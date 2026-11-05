/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineAvoidPaths
import Mathlib.Tactic

/-! # Every surviving rail atom reaches a surviving endpoint -/

public section
namespace WaveTurbulence.Vine

/-- A full rail avoids an atom absent from all its vertices. -/
theorem rail_avoid_path (a b z : ℕ) (ws : List ℕ) (ha : a ≠ z) (hb : b ≠ z)
    (hw : ∀ w ∈ ws,w ≠ z) : AvoidPath (railBonds a ws b) z a b := by
  induction ws generalizing a with
  | nil => exact Relation.EqvGen.rel _ _ ⟨ha,hb,Or.inl List.mem_cons_self⟩
  | cons w ws ih =>
    have hwz := hw w List.mem_cons_self
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.rel _ _ ⟨ha,hwz,Or.inl List.mem_cons_self⟩)
      (avoidPath_mono (fun _ h => List.mem_cons_of_mem _ h)
        (ih w hwz (fun x hx => hw x (List.mem_cons_of_mem _ hx))))

/-- A prefix of a rail avoids an atom when its initial port and all
intermediate atoms do. The final port is not used. -/
theorem rail_mem_avoid_start (a b z : ℕ) (ws : List ℕ) (ha : a ≠ z)
    (hw : ∀ w ∈ ws,w ≠ z) {v : ℕ} (hv : v ∈ ws) :
    AvoidPath (railBonds a ws b) z a v := by
  induction ws generalizing a with
  | nil => exact False.elim (List.not_mem_nil hv)
  | cons w ws ih =>
    have hwz := hw w List.mem_cons_self
    have hedge : AvoidPath (railBonds a (w::ws) b) z a w :=
      Relation.EqvGen.rel _ _ ⟨ha,hwz,Or.inl List.mem_cons_self⟩
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hedge
    · exact Relation.EqvGen.trans _ _ _ hedge
        (avoidPath_mono (fun _ h => List.mem_cons_of_mem _ h)
          (ih w hwz (fun x hx => hw x (List.mem_cons_of_mem _ hx)) hv))

/-- A suffix of a rail avoids an atom when its final port and all
intermediate atoms do. The initial port is not used. -/
theorem rail_mem_avoid_end (a b z : ℕ) (ws : List ℕ) (hb : b ≠ z)
    (hw : ∀ w ∈ ws,w ≠ z) {v : ℕ} (hv : v ∈ ws) :
    AvoidPath (railBonds a ws b) z b v := by
  induction ws generalizing a with
  | nil => exact False.elim (List.not_mem_nil hv)
  | cons w ws ih =>
    have hwz := hw w List.mem_cons_self
    have htail : ∀ x ∈ ws,x ≠ z := fun x hx => hw x (List.mem_cons_of_mem _ hx)
    rcases List.mem_cons.mp hv with rfl | hv
    · have hp := rail_avoid_path v b z ws hwz hb htail
      exact avoidPath_mono (fun _ h => List.mem_cons_of_mem _ h) (Relation.EqvGen.symm _ _ hp)
    · exact avoidPath_mono (fun _ h => List.mem_cons_of_mem _ h) (ih w htail hv)

/-- A rail with distinct intermediate atoms cannot lose both routes from
any surviving intermediate atom when one atom is removed. -/
theorem rail_mem_avoid_endpoint (a b z : ℕ) (ws : List ℕ) (hd : ws.Nodup)
    (ha : a ≠ z) (hb : b ≠ z) {v : ℕ} (hv : v ∈ ws) (hvz : v ≠ z) :
    ∃ p,(p=a ∨ p=b) ∧ AvoidPath (railBonds a ws b) z p v := by
  induction ws generalizing a with
  | nil => exact False.elim (List.not_mem_nil hv)
  | cons w ws ih =>
    obtain ⟨hwn,hdup⟩ := List.nodup_cons.mp hd
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨a,Or.inl rfl,Relation.EqvGen.rel _ _ ⟨ha,hvz,Or.inl List.mem_cons_self⟩⟩
    · by_cases hwz : w=z
      · have htail : ∀ x ∈ ws,x ≠ z := by
          intro x hx he
          exact hwn (he.trans hwz.symm ▸ hx)
        exact ⟨b,Or.inr rfl,avoidPath_mono (fun _ h => List.mem_cons_of_mem _ h)
          (rail_mem_avoid_end w b z ws hb htail hv)⟩
      · obtain ⟨p,hp,hpath⟩ := ih w hdup hwz hv
        rcases hp with hp | hp
        · rw [hp] at hpath
          exact ⟨a,Or.inl rfl,Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.rel _ _ ⟨ha,hwz,Or.inl List.mem_cons_self⟩)
            (avoidPath_mono (fun _ h => List.mem_cons_of_mem _ h) hpath)⟩
        · rw [hp] at hpath
          exact ⟨b,Or.inr rfl,avoidPath_mono (fun _ h => List.mem_cons_of_mem _ h) hpath⟩

end WaveTurbulence.Vine
