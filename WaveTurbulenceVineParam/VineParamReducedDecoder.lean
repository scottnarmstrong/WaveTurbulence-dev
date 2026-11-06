/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamConservationFiber
import Mathlib.Tactic

/-! # Exact truncation of an integer decoder to free coordinates and the gap -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {β E : Type*} [AddCommGroup E] {n q : ℕ}

/-- Free coordinates followed by the prescribed gap, with no divergence slots. -/
@[expose] def attachGap (x : Fin q → E) (r : E) : Fin (q+1) → E :=
  fun i => if hi : i.1<q then x ⟨i.1,hi⟩ else r

/-- The initial coordinate block embeds in the full conservation vector. -/
@[expose] def coordinateEmbedding (hq : q<n) : Fin (q+1) ↪ Fin n where
  toFun := fun i => ⟨i.1,by have := i.2; omega⟩
  inj' := by
    intro i j he
    exact Fin.ext (congrArg (fun v : Fin n => v.1) he)

/-- Packing agrees with the reduced coordinates on their complete block. -/
theorem pack_small (hq : q<n) (x : Fin q → E) (r : E) (i : Fin (q+1)) :
    packCoordinates hq x r (coordinateEmbedding hq i)=attachGap x r i := by
  change (if hi : i.1<q then x ⟨i.1,hi⟩ else if i.1=q then r else 0)=
    (if hi : i.1<q then x ⟨i.1,hi⟩ else r)
  by_cases hi : i.1<q
  · rw [dite_eq_left hi,dite_eq_left hi]
  · have he : i.1=q := by have := i.2; omega
    rw [dite_eq_right hi,dite_eq_right hi,ite_eq_left he]

/-- All later entries are the actual zero momentum divergences. -/
theorem pack_large (hq : q<n) (x : Fin q → E) (r : E) (i : Fin n) (hi : q < i.1) :
    packCoordinates hq x r i=0 := by
  have hlt : ¬i.1<q := by omega
  have hne : i.1 ≠ q := by omega
  simp only [packCoordinates,dite_eq_right hlt,ite_eq_right hne]

/-- The reduced integer decoder consists of the free and gap columns. -/
@[expose] def reducedDecoder (hq : q<n) (A : Matrix β (Fin n) ℤ) : Matrix β (Fin (q+1)) ℤ :=
  fun e i => A e (coordinateEmbedding hq i)

/-- A full conservation-fiber decoder and its reduced matrix agree exactly. -/
theorem intEval_pack (hq : q<n) (A : Matrix β (Fin n) ℤ) (x : Fin q → E) (r : E) :
    intEval A (packCoordinates hq x r)=intEval (reducedDecoder hq A) (attachGap x r) := by
  funext e
  let g : Fin n → E := fun i => A e i • packCoordinates hq x r i
  have hs := Finset.sum_subset (show (univ : Finset (Fin (q+1))).image
      (coordinateEmbedding hq) ⊆ univ from subset_univ _) (f := g) (by
    intro i _hi hnot
    have hbig : q < i.1 := by
      by_contra h
      have him : i ∈ (univ : Finset (Fin (q+1))).image (coordinateEmbedding hq) := by
        exact mem_image.mpr ⟨⟨i.1,by omega⟩,mem_univ _,Fin.ext rfl⟩
      exact hnot him
    dsimp only [g]
    rw [pack_large hq x r i hbig,smul_zero])
  rw [Finset.sum_image (fun _ _ _ _ he => (coordinateEmbedding hq).injective he)] at hs
  change (∑ i : Fin n,g i)=_
  rw [← hs]
  apply Finset.sum_congr rfl
  intro i _hi
  dsimp only [g,reducedDecoder,intEval]
  rw [pack_small]

end WaveTurbulence.Vine.Param
