/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBaseMasks
import Mathlib.Tactic

/-! # Cardinality information retained by the finite core masks -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Summing a complete finite membership vector counts the selected atoms. -/
theorem membershipMask_sum (U : Finset ℕ) (N : ℕ) (hU : U ⊆ range N) :
    ((List.range N).map (membershipMask U)).sum=U.card := by
  change (∑ i ∈ range N,if i ∈ U then 1 else 0)=U.card
  rw [sum_boole]
  have he : (range N).filter (fun i => i ∈ U)=U := by
    ext i
    simp only [mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hU h,h⟩⟩
  rw [he]
  rfl

/-- A complete base-core mask has exactly the actual subgroup's cardinality. -/
theorem VineRealization.base_mask_sum {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hk : R.k=List.replicate X.template.slots.length 0)
    {A : Finset V} (hAS : A ⊆ S) :
    (coreMaskVector X (membershipMask (A.image R.f))).sum=A.card := by
  rw [coreMaskVector,membershipMask_sum]
  · exact card_image_of_injOn (fun _ hx _ hy he => R.injOn (hAS hx) (hAS hy) he)
  · intro i hi
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
    have hh := R.image_eq ▸ mem_image_of_mem R.f (hAS hv)
    simpa only [hk,expand_zero_rungs] using hh

/-- A full membership vector forces the actual selected group to be the
entire realized base core. -/
theorem VineRealization.base_eq_of_full_mask {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hk : R.k=List.replicate X.template.slots.length 0)
    {A : Finset V} (hAS : A ⊆ S)
    (hmask : coreMaskVector X (membershipMask (A.image R.f))=List.replicate X.template.n 1) : A=S := by
  have hc := R.base_mask_sum hk hAS
  rw [hmask,List.sum_replicate] at hc
  have hs : S.card=X.template.n := by
    have hh := congrArg Finset.card R.image_eq
    rw [card_image_of_injOn R.injOn,card_range,hk,expand_zero_rungs] at hh
    exact hh
  apply eq_of_subset_of_card_le hAS
  simp only [nsmul_eq_mul,mul_one,Nat.cast_id] at hc
  omega

end WaveTurbulence.Vine
