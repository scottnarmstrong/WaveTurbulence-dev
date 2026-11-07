/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MergeRank
import Mathlib.Tactic

/-! # The fibre of the restriction to the merged molecule has at most `⌈C δ⁻¹ L^{d−γ−η/2}⌉` elements -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.CountLemmas
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace MergeSum
variable {M : Molecule V D} {v₁ v₂ : V}

theorem merge_fiber_encard (m : ℕ) {γ η : ℝ} {Cp : ℝ} {L δ : ℝ}
    (hCp : ∀ (a b : Mom (m + 2)) (nk : Fin (m + 2) → ℤ) (β : ℝ) (ε : ℤˣ),
      (ε = -1 → L ^ (-γ + η) ≤ ‖latticePoint L nk‖) →
      ((atomPairSet L a b nk β (δ⁻¹ * L ^ (-2 * γ)) ε).ncard : ℝ) ≤ Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2))
    (hLp : 0 < L) (hv₁ : v₁ ∈ M.atoms)
    {x y r₁ r₂ : D} (hxy : x ≠ y) (hxr₁ : x ≠ r₁) (hxr₂ : x ≠ r₂) (hyr₁ : y ≠ r₁) (hyr₂ : y ≠ r₂) (hrr : r₁ ≠ r₂)
    (hxa : M.atom x = v₁) (hxb : M.atom (M.mate x) = v₂) (hya : M.atom y = v₁) (hyb : M.atom (M.mate y) = v₂)
    (hne : v₁ ≠ v₂) (hA : M.dartsAt v₁ = {x, y, r₁, r₂})
    (hpair : ∀ z, M.ends z = s(v₁, v₂) → z = x ∨ z = y ∨ z = M.mate x ∨ z = M.mate y)
    (Adm : (D → (Fin (m + 2) → ℤ)) → Prop)
    (c : V → Mom (m + 2)) (β : V → ℝ) (k0 : D → Mom (m + 2)) (κ₀ : D → (Fin (m + 2) → ℤ))
    (hdec₀ : M.IsDecoration L (0 : Mom (m + 2)) c κ₀) (hres₀ : M.IsRestricted L γ δ (0 : Mom (m + 2)) β k0 κ₀)
    (hLG₀ : MoleProp.LargeGap M L γ η 0 κ₀) :
    {κ | (M.IsDecoration L (0 : Mom (m + 2)) c κ ∧ M.IsRestricted L γ δ (0 : Mom (m + 2)) β k0 κ ∧ Adm κ) ∧
        (fun z : OffPair M v₁ v₂ => κ z.val) = fun z => κ₀ z.val}.encard ≤
      (⌈Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)⌉₊ : ℕ∞) := by
  classical
  have hr1A : r₁ ∈ M.dartsAt v₁ := by rw [hA]; simp
  have hr2A : r₂ ∈ M.dartsAt v₁ := by rw [hA]; simp
  have hatr1 : M.atom r₁ = v₁ := (Mole.mem_dartsAt M v₁ r₁).mp hr1A
  have hatr2 : M.atom r₂ = v₁ := (Mole.mem_dartsAt M v₁ r₂).mp hr2A
  have hoff : ∀ r, M.atom r = v₁ → r ≠ x → r ≠ y → M.ends r ≠ s(v₁, v₂) := by
    intro r hr h1 h2 h
    rcases hpair r h with e | e | e | e
    · exact h1 e
    · exact h2 e
    · rw [e, hxb] at hr; exact hne hr.symm
    · rw [e, hyb] at hr; exact hne hr.symm
  have hr1off := hoff r₁ hatr1 hxr₁.symm hyr₁.symm
  have hr2off := hoff r₂ hatr2 hxr₂.symm hyr₂.symm
  set S := atomPairSet L (k0 x) (k0 y) ((sgn M x : ℤ) • (doubleSign (M.out x) • κ₀ x + doubleSign (M.out y) • κ₀ y))
    ((doubleSign (M.out x) : ℝ) * (β v₁ - (M.dartSign r₁ * ‖latticePoint L (κ₀ r₁)‖ ^ 2 +
      M.dartSign r₂ * ‖latticePoint L (κ₀ r₂)‖ ^ 2))) (δ⁻¹ * L ^ (-2 * γ)) (sgn M x * sgn M y) with hS
  have hSfin : S.Finite := finite_atomPairSet hLp _ _ _ _ _ _
  have hfib := fiber_subset_pairSet (M := M) (v₂ := v₂) (γ := γ) (δ := δ) hLp hv₁ hxy hxr₁ hxr₂ hyr₁ hyr₂ hrr hA hpair
    c β k0 κ₀ hdec₀
  -- the map to the pair set
  have hmaps : ∀ κ ∈ {κ | (M.IsDecoration L (0 : Mom (m + 2)) c κ ∧ M.IsRestricted L γ δ (0 : Mom (m + 2)) β k0 κ ∧
        Adm κ) ∧ (fun z : OffPair M v₁ v₂ => κ z.val) = fun z => κ₀ z.val}, (κ x, κ y) ∈ S := by
    rintro κ ⟨⟨hdec, hres, _⟩, hκeq⟩
    refine hfib κ ⟨hdec, hres⟩ ⟨?_, ?_⟩
    · exact congrFun hκeq ⟨r₁, hr1off⟩
    · exact congrFun hκeq ⟨r₂, hr2off⟩
  have hinj : Set.InjOn (fun κ : D → (Fin (m + 2) → ℤ) => (κ x, κ y))
      {κ | (M.IsDecoration L (0 : Mom (m + 2)) c κ ∧ M.IsRestricted L γ δ (0 : Mom (m + 2)) β k0 κ ∧ Adm κ) ∧
        (fun z : OffPair M v₁ v₂ => κ z.val) = fun z => κ₀ z.val} := by
    rintro κ ⟨⟨hdec, _, _⟩, hκeq⟩ κ' ⟨⟨hdec', _, _⟩, hκeq'⟩ hxy'
    simp only [Prod.mk.injEq] at hxy'
    funext z
    by_cases hz : M.ends z = s(v₁, v₂)
    · rcases hpair z hz with rfl | rfl | rfl | rfl
      · exact hxy'.1
      · exact hxy'.2
      · rw [hdec.1, hdec'.1]; exact hxy'.1
      · rw [hdec.1, hdec'.1]; exact hxy'.2
    · exact (congrFun hκeq ⟨z, hz⟩).trans (congrFun hκeq' ⟨z, hz⟩).symm
  -- the large gap for the opposite-sign case
  have hgap : (sgn M x * sgn M y) = -1 → L ^ (-γ + η) ≤ ‖latticePoint L ((sgn M x : ℤ) •
      (doubleSign (M.out x) • κ₀ x + doubleSign (M.out y) • κ₀ y))‖ := by
    intro hε
    have hmem := hfib κ₀ ⟨hdec₀, hres₀⟩ ⟨rfl, rfl⟩
    have h3 := hmem.2.2.1
    have h3' : κ₀ x + (-1 : ℤ) • κ₀ y = (sgn M x : ℤ) • (doubleSign (M.out x) • κ₀ x + doubleSign (M.out y) • κ₀ y) := by
      have := h3
      change κ₀ x + (((sgn M x * sgn M y : ℤˣ)) : ℤ) • κ₀ y = _ at this
      rw [hε] at this
      simpa using this
    have hout : M.out x ≠ M.out y := by
      intro h
      have hs : sgn M x = sgn M y := (sgn_eq_iff M x y).mpr h
      rw [hs] at hε
      have : (sgn M y * sgn M y : ℤˣ) = 1 := by unfold sgn; split_ifs <;> decide
      rw [this] at hε
      exact absurd hε (by decide)
    have := hLG₀ x y (hxa.trans hya.symm) hout
    rw [← h3']
    have hk : ∀ z, Molecule.kvec L (0 : Mom (m + 2)) κ₀ z = latticePoint L (κ₀ z) := fun z => by simp [Molecule.kvec]
    rw [hk, hk] at this
    have hsub : latticePoint L (κ₀ x + (-1 : ℤ) • κ₀ y) = latticePoint L (κ₀ x) - latticePoint L (κ₀ y) := by
      rw [neg_one_zsmul, ← sub_eq_add_neg]
      exact WeylSums.latticePoint_sub_eq L _ _
    rw [hsub]
    exact this
  have hcard : (S.ncard : ℝ) ≤ Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2) := hCp (k0 x) (k0 y) ((sgn M x : ℤ) • (doubleSign (M.out x) • κ₀ x + doubleSign (M.out y) • κ₀ y))
    ((doubleSign (M.out x) : ℝ) * (β v₁ - (M.dartSign r₁ * ‖latticePoint L (κ₀ r₁)‖ ^ 2 +
      M.dartSign r₂ * ‖latticePoint L (κ₀ r₂)‖ ^ 2))) (sgn M x * sgn M y) hgap
  calc _ ≤ S.encard := Set.encard_le_encard_of_injOn hmaps hinj
    _ = (S.ncard : ℕ∞) := hSfin.cast_ncard_eq.symm
    _ ≤ (⌈Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)⌉₊ : ℕ∞) := by
        have h1 : (S.ncard : ℝ) ≤ (⌈Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)⌉₊ : ℝ) := hcard.trans (Nat.le_ceil _)
        have h2 : S.ncard ≤ ⌈Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)⌉₊ := by exact_mod_cast h1
        exact_mod_cast h2

end MergeSum
end WaveTurbulence.FinalCountG8
