/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineLocalDartEmbedding
public import WaveTurbulence.Foundations.Molecule.VineLatticeGaps
import Mathlib.Tactic

/-! # Actual gap darts transport through a local graph identification -/

public section
namespace WaveTurbulence.Vine
variable {V D E W : Type*} [DecidableEq V] [Fintype D] [Fintype E]
    [AddCommGroup W] [Module ℝ W]
    {M : Molecule V D} {N : Molecule V E} {A : Finset V}
namespace LocalDartEmbedding
variable (F : LocalDartEmbedding M N A)

omit [Fintype D] [Fintype E] [Module ℝ W] in
/-- Local identification preserves the actual outgoing/incoming dart
witnesses of a gap, with the same momentum labels on matched darts. -/
theorem groupGap_iff (S : Finset V) (hSA : S ⊆ A) (k : D → W) (v : V) (r : W) :
    IsGroupGap N S (fun d => k (F.toFun d)) v r ↔ IsGroupGap M S k v r := by
  constructor
  · rintro ⟨x,y,hx,hy,hxg,hyg,hxo,hyo,hr⟩
    exact ⟨F.toFun x,F.toFun y,(F.atom_eq x).trans hx,(F.atom_eq y).trans hy,
      (F.inGroup_iff S x).mpr hxg,(F.inGroup_iff S y).mpr hyg,
      (F.out_eq x).trans hxo,(F.out_eq y).trans hyo,hr⟩
  · rintro ⟨x,y,hx,hy,hxg,hyg,hxo,hyo,hr⟩
    obtain ⟨x',hx'⟩ := F.surjective_internal x ⟨hSA hxg.1,hSA hxg.2⟩
    obtain ⟨y',hy'⟩ := F.surjective_internal y ⟨hSA hyg.1,hSA hyg.2⟩
    refine ⟨x',y',?_,?_,?_,?_,?_,?_,?_⟩
    · rw [← F.atom_eq,hx']; exact hx
    · rw [← F.atom_eq,hy']; exact hy
    · apply (F.inGroup_iff S x').mp; rwa [hx']
    · apply (F.inGroup_iff S y').mp; rwa [hy']
    · rw [← F.out_eq,hx']; exact hxo
    · rw [← F.out_eq,hy']; exact hyo
    · change r=k (F.toFun x')-k (F.toFun y')
      rwa [hx',hy']

omit [Fintype D] [Fintype E] in
/-- In particular the exact source lattice block-gap predicate is preserved,
with integer labels restricted along the actual dart injection. -/
theorem blockGap_iff {d : ℕ} (S : Finset V) (hSA : S ⊆ A) (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (v : V) (r : Mom d) :
    N.IsBlockGap L w (fun e => κ (F.toFun e)) S v r ↔ M.IsBlockGap L w κ S v r :=
  F.groupGap_iff S hSA (Molecule.kvec L w κ) v r

end LocalDartEmbedding
end WaveTurbulence.Vine
