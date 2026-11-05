/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Multiset.Filter
import Mathlib.Tactic

/-! # Finite matching of repeated labels by exact multiset equality -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- Mapping the full finite subtype is the same multiset as mapping its
original finite set. -/
theorem univ_subtype_map {A Z : Type*} (T : Finset A) (f : A → Z) :
    (univ : Finset T).val.map (fun x => f x.1)=T.val.map f := by
  have he : T.attach=(univ : Finset T) := by ext x; simp only [mem_attach,mem_univ]
  rw [← he]
  change (T.val.attach.map (fun x => f x.1))=T.val.map f
  exact Multiset.attach_map_val' T.val f

/-- Equality of label multisets gives an actual bijection matching labels,
including repetitions. It is obtained by matching each finite label fiber. -/
theorem exists_label_matching {A B Z : Type*} [Fintype A] [Fintype B] [DecidableEq Z]
    (f : A → Z) (g : B → Z)
    (hmap : (univ : Finset A).val.map f=(univ : Finset B).val.map g) :
    ∃ e : A ≃ B,∀ a,g (e a)=f a := by
  classical
  have hc (z : Z) : Fintype.card {a // f a=z}=Fintype.card {b // g b=z} := by
    have hh := congrArg (Multiset.count z) hmap
    have he : (univ.filter (fun a => f a=z)).card=(univ.filter (fun b => g b=z)).card := by
      simpa only [Multiset.count_map,← filter_val,Finset.card_val,eq_comm] using hh
    simpa only [Fintype.card_subtype] using he
  let e (z : Z) : {a // f a=z} ≃ {b // g b=z} := Fintype.equivOfCardEq (hc z)
  exact ⟨Equiv.ofFiberEquiv e,Equiv.ofFiberEquiv_map e⟩

end WaveTurbulence.Vine
