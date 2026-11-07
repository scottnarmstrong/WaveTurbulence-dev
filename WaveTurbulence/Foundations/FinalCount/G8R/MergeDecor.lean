/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.MergeCore
import Mathlib.Tactic

/-! # Decorations of the merged molecule

* A decoration of `𝕄` restricts to one of `merge 𝕄`; it stays LG if `𝕄`'s is LG with no small gap across the pair
  (DH23 L1977: "a decoration of M′ naturally leads to a decoration of M″, which is also LG by our assumptions").
* `merge (𝕄 ∖ ℓ) ≅ (merge 𝕄) ∖ ℓ` for a bond `ℓ` off the pair: the same darts.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace Merge
variable {M : Molecule V D} {v₁ v₂ : V} {hv₁ : v₁ ∈ M.atoms} {hne : v₁ ≠ v₂}

omit [Fintype D] [DecidableEq D] in
/-- **LG survives merging** without a small gap across the pair. -/
theorem largeGap {d : ℕ} {L γ η : ℝ} {κ : D → (Fin d → ℤ)} (hLG : MoleProp.LargeGap M L γ η 0 κ)
    (hSG : ¬ SmallPairGap M v₁ v₂ L γ η κ) :
    MoleProp.LargeGap (mergePair M v₁ v₂ hv₁ hne) L γ η 0 (fun y => κ y.val) := by
  intro x y hxy hdir
  change L ^ (-γ + η) ≤ ‖Molecule.kvec L 0 κ x.val - Molecule.kvec L 0 κ y.val‖
  rw [atom_eq, atom_eq] at hxy
  rw [out_eq, out_eq] at hdir
  by_cases h : M.atom x.val = M.atom y.val
  · exact hLG x.val y.val h hdir
  -- the two darts sit at `v₁` and `v₂`
  have hoff : ∀ z : OffPair M v₁ v₂, M.atom z.val = v₁ → M.atom (M.mate z.val) ≠ v₂ :=
    fun z hz h' => z.property ((ends_eq_pair_iff hne hz).mpr h')
  have hoff' : ∀ z : OffPair M v₁ v₂, M.atom z.val = v₂ → M.atom (M.mate z.val) ≠ v₁ := by
    intro z hz h'
    apply z.property
    unfold Molecule.ends; rw [hz, h']; exact Sym2.eq_swap
  have hcase : (M.atom x.val = v₁ ∧ M.atom y.val = v₂) ∨ (M.atom x.val = v₂ ∧ M.atom y.val = v₁) := by
    unfold mergeMap at hxy
    by_cases hx : M.atom x.val = v₂
    · rw [ite_of_pos hx] at hxy
      by_cases hy : M.atom y.val = v₂
      · exact absurd (hx.trans hy.symm) h
      · rw [ite_of_not hy] at hxy; exact Or.inr ⟨hx, hxy.symm⟩
    · rw [ite_of_not hx] at hxy
      by_cases hy : M.atom y.val = v₂
      · rw [ite_of_pos hy] at hxy; exact Or.inl ⟨hxy, hy⟩
      · rw [ite_of_not hy] at hxy; exact absurd hxy h
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · by_contra hlt; push Not at hlt
    exact hSG ⟨x.val, y.val, h1, hoff x h1, h2, hoff' y h2, Or.inl hlt.le⟩
  · by_contra hlt; push Not at hlt
    rw [norm_sub_rev] at hlt
    exact hSG ⟨y.val, x.val, h2, hoff y h2, h1, hoff' x h1, Or.inl hlt.le⟩

end Merge

omit [Fintype D] [DecidableEq D] in
omit [DecidableEq V] in
/-- A small gap of `𝕄 ∖ ℓ` is a small gap of `𝕄`. -/
theorem smallPairGap_of_eraseBond {M : Molecule V D} {e : D} {v₁ v₂ : V} {d : ℕ} {L γ η : ℝ}
    {κ : D → (Fin d → ℤ)} (h : SmallPairGap (MoleProp.eraseBond M e) v₁ v₂ L γ η (fun z => κ z.val)) :
    SmallPairGap M v₁ v₂ L γ η κ := by
  obtain ⟨x, y, h1, h2, h3, h4, h5⟩ := h
  exact ⟨x.val, y.val, h1, h2, h3, h4, h5⟩

section EraseEquiv
variable (M : Molecule V D) {v₁ v₂ : V} (hv₁ : v₁ ∈ M.atoms) (hne : v₁ ≠ v₂) (e : D) (he : M.ends e ≠ s(v₁, v₂))

/-- **`merge (𝕄 ∖ ℓ) ≅ (merge 𝕄) ∖ ℓ`** on darts. -/
def mergeEraseEquiv :
    OffPair (MoleProp.eraseBond M e) v₁ v₂ ≃ MoleProp.WithoutBondDart (mergePair M v₁ v₂ hv₁ hne) ⟨e, he⟩ where
  toFun y := ⟨⟨y.val.val, y.property⟩, fun h => y.val.property.1 (congrArg Subtype.val h),
    fun h => y.val.property.2 (congrArg Subtype.val h)⟩
  invFun z := ⟨⟨z.val.val, fun h => z.property.1 (Subtype.ext h), fun h => z.property.2 (Subtype.ext h)⟩,
    z.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype D] [DecidableEq D] in
theorem mergeErase_atoms :
    (mergePair (MoleProp.eraseBond M e) v₁ v₂ hv₁ hne).atoms =
      (MoleProp.eraseBond (mergePair M v₁ v₂ hv₁ hne) ⟨e, he⟩).atoms := rfl

omit [Fintype D] [DecidableEq D] in
/-- The relabelling data of `mergeEraseEquiv`. -/
theorem mergeErase_compat :
    (∀ y, (MoleProp.eraseBond (mergePair M v₁ v₂ hv₁ hne) ⟨e, he⟩).atom (mergeEraseEquiv M hv₁ hne e he y) =
      (mergePair (MoleProp.eraseBond M e) v₁ v₂ hv₁ hne).atom y) ∧
    (∀ y, (MoleProp.eraseBond (mergePair M v₁ v₂ hv₁ hne) ⟨e, he⟩).mate (mergeEraseEquiv M hv₁ hne e he y) =
      mergeEraseEquiv M hv₁ hne e he ((mergePair (MoleProp.eraseBond M e) v₁ v₂ hv₁ hne).mate y)) ∧
    (∀ y, (MoleProp.eraseBond (mergePair M v₁ v₂ hv₁ hne) ⟨e, he⟩).out (mergeEraseEquiv M hv₁ hne e he y) =
      (mergePair (MoleProp.eraseBond M e) v₁ v₂ hv₁ hne).out y) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

end EraseEquiv

end WaveTurbulence.MoleProp4
