/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.DecodedPairRecovery

/-! # Deterministic maximal spines from the actual property-L predicate -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- The chosen slot is the unique child with property L. -/
def UniqueExternalChild {w : ℕ} (G : Garden w) (a : Fin w × Path) (j : Fin 3) : Prop :=
  ∀ k : Fin 3, ExternalAt G (addrExt a [k]) ↔ k = j

/-- Follow unique L-children along the specified literal path. -/
def ExternalSegment {w : ℕ} (G : Garden w) : (Fin w × Path) → Path → Prop
  | _,[] => True
  | a,j :: p => UniqueExternalChild G a j ∧ ExternalSegment G (addrExt a [j]) p

/-- No further unique-L-child continuation is possible. -/
def ExternalStop {w : ℕ} (G : Garden w) (a : Fin w × Path) : Prop :=
  ¬ ∃ j : Fin 3, UniqueExternalChild G a j

/-- A source-maximal path obtained by following unique L-children. -/
def MaximalExternalSpine {w : ℕ} (G : Garden w) (a : Fin w × Path) (p : Path) : Prop :=
  ExternalSegment G a p ∧ ExternalStop G (addrExt a p)

/-- The actual L-predicate determines the continuation slot. -/
theorem uniqueExternalChild_slot {w : ℕ} {G : Garden w} {a : Fin w × Path} {i j : Fin 3}
    (hi : UniqueExternalChild G a i) (hj : UniqueExternalChild G a j) : i = j :=
  (hj i).mp ((hi i).mpr rfl)

/-- Concatenation composes literal unique-child paths. -/
theorem externalSegment_append {w : ℕ} (G : Garden w) (a : Fin w × Path) (p q : Path) :
    ExternalSegment G a (p ++ q) ↔ ExternalSegment G a p ∧ ExternalSegment G (addrExt a p) q := by
  induction p generalizing a with
  | nil => simp [ExternalSegment,addrExt]
  | cons j p ih =>
    change (UniqueExternalChild G a j ∧ ExternalSegment G (addrExt a [j]) (p ++ q)) ↔ _
    rw [ih,addrExt_cons a j p]
    change (_ ∧ (_ ∧ _)) ↔ ((_ ∧ _) ∧ _)
    exact and_assoc.symm

/-- The maximal stopping rule makes the whole path uniquely determined. -/
theorem maximalExternalSpine_unique {w : ℕ} (G : Garden w) (a : Fin w × Path) (p q : Path)
    (hp : MaximalExternalSpine G a p) (hq : MaximalExternalSpine G a q) : p = q := by
  induction p generalizing a q with
  | nil =>
    cases q with
    | nil => rfl
    | cons j q =>
      have hs : ExternalStop G a := by simpa only [addrExt,List.append_nil,Prod.eta] using hp.2
      exact (hs ⟨j,hq.1.1⟩).elim
  | cons i p ih =>
    cases q with
    | nil =>
      have hs : ExternalStop G a := by simpa only [addrExt,List.append_nil,Prod.eta] using hq.2
      exact (hs ⟨i,hp.1.1⟩).elim
    | cons j q =>
      have hij := uniqueExternalChild_slot hp.1.1 hq.1.1
      subst j
      have hsP := hp.2
      have hsQ := hq.2
      rw [addrExt_cons] at hsP hsQ
      exact congrArg (List.cons i) (ih (addrExt a [i]) q ⟨hp.1.2,hsP⟩ ⟨hq.1.2,hsQ⟩)

end WaveTurbulence.Reg
