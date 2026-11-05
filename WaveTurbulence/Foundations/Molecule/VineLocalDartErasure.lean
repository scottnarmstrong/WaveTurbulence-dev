/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineLocalDartEmbedding
public import WaveTurbulence.Foundations.Molecule.MoleculeBondEdits
import Mathlib.Tactic

/-! # Local dart identifications survive matched bond deletions -/

public section
namespace WaveTurbulence.Vine
variable {V D E : Type*} [DecidableEq V]

/-- A deleted bond outside the atomic group leaves every internal dart
identified by the canonical subtype injection. -/
@[expose] def eraseBond_local_embedding (M : Molecule V D) (e : D) (A : Finset V)
    (h : ¬M.InGroup A e) : LocalDartEmbedding M (Mole.eraseBond M e) A where
  toFun := Subtype.val
  injective := Subtype.val_injective
  atom_eq := fun _ => rfl
  mate_eq := fun _ => rfl
  out_eq := fun _ => rfl
  atoms_eq := rfl
  surjective_internal := by
    intro d hd
    have hde : d ≠ e := by intro he; exact h (he ▸ hd)
    have hdm : d ≠ M.mate e := by
      intro he
      have hh : M.InGroup A (M.mate e) := he ▸ hd
      exact h ⟨by simpa only [M.mate_mate] using hh.2,hh.1⟩
    exact ⟨⟨d,hde,hdm⟩,rfl⟩

/-- Choosing the other mate of a deleted bond changes only the proof
fields of the surviving dart subtype, with every actual dart retained. -/
@[expose] def eraseBond_mate_local_embedding (M : Molecule V D) (e : D) (A : Finset V) :
    LocalDartEmbedding (Mole.eraseBond M e) (Mole.eraseBond M (M.mate e)) A where
  toFun := fun d => ⟨d.1,by simpa only [M.mate_mate] using d.2.2,d.2.1⟩
  injective := by
    intro d f h
    apply Subtype.ext
    exact congrArg (fun x : {d : D // d ≠ e ∧ d ≠ M.mate e} => x.1) h
  atom_eq := fun _ => rfl
  mate_eq := fun _ => Subtype.ext rfl
  out_eq := fun _ => rfl
  atoms_eq := rfl
  surjective_internal := by
    intro d _hd
    exact ⟨⟨d.1,d.2.2,by simpa only [M.mate_mate] using d.2.1⟩,Subtype.ext rfl⟩

namespace LocalDartEmbedding
variable {M : Molecule V D} {N : Molecule V E} {A : Finset V}

/-- Delete matched actual bonds on both sides of a local dart injection.
Surjectivity on the remaining internal darts is proved from the original
surjectivity; no new graph-equivalence assumption is introduced. -/
@[expose] def eraseBond (F : LocalDartEmbedding M N A) (f : E) :
    LocalDartEmbedding (Mole.eraseBond M (F.toFun f)) (Mole.eraseBond N f) A where
  toFun := fun d => ⟨F.toFun d.1,
    fun he => d.2.1 (F.injective he),
    fun he => d.2.2 (F.injective (he.trans (F.mate_eq f).symm))⟩
  injective := by
    intro d e he
    exact Subtype.ext (F.injective (congrArg Subtype.val he))
  atom_eq := fun d => F.atom_eq d.1
  mate_eq := fun d => Subtype.ext (F.mate_eq d.1)
  out_eq := fun d => F.out_eq d.1
  atoms_eq := F.atoms_eq
  surjective_internal := by
    intro d hd
    obtain ⟨e,he⟩ := F.surjective_internal d.1 hd
    have hef : e ≠ f := by
      intro hh
      exact d.2.1 (he.symm.trans (congrArg F.toFun hh))
    have hem : e ≠ N.mate f := by
      intro hh
      exact d.2.2 (he.symm.trans ((congrArg F.toFun hh).trans (F.mate_eq f)))
    exact ⟨⟨e,hef,hem⟩,Subtype.ext he⟩

end LocalDartEmbedding
end WaveTurbulence.Vine
