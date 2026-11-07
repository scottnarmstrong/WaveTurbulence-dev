/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriDev4
/-! Triangles, sibling part 1 (G2-SIBLING): the **relative-ball** pair count.  DH23 L1796 (`ΔF = 0`) counts the pair of
`α`-gaps `(r₀, r₁)` of a triangle as `(R₀L)^d (R₁L)^d`; with `ι_{v₂} ≠ 0` caused by the *first cut of the same triangle*
(Remark `remiota`, L1782: `0 < |r ± r'| ≤ L^{-50η}R₁` with `r' = r₀` the gap of the cut at `v₁`) the second gap lies in a
ball of radius `ρ₁` around `± r₀`, whose centre is the *variable* `r₀`.  We count the pair by `(r₀, r₁ ∓ r₀)`: the same bound
as for a fixed ball.  For a `β`-cut at `v₁` the gap `r₀` is a function of the parameters, so the ball is fixed
(`gap0_const_of_beta`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem latticePoint_sub_smul (L : ℝ) (s : ℤ) (a b : Fin d → ℤ) :
    latticePoint L (b - s • a) = latticePoint L b - (s : ℝ) • latticePoint L a := by
  ext j
  simp [latticePoint, sub_div, mul_div_assoc]

namespace TriData
variable {M : Molecule V D} (T : TriData M)

/-- **`ΔF = 0` with a relative ball**: the first gap lies in a fixed ball `(r₀, ρ₀)`, the second within `ρ₁` of
`s · (first gap)`, `s = ±1`.  Same bound as `card_αα`. -/
theorem card_αα_sib (L γ δ : ℝ) (hL : 0 < L) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (r₀ : Mom d) (ρ₀ : ℝ) (s : ℤ) (ρ₁ : ℝ)
    (hb0 : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ (T.a 0) (T.b 0) - r₀‖ ≤ ρ₀)
    (hb1 : ∀ κ ∈ decSet M L γ δ w Adm c β k0,
      ‖Molecule.gapAt L w κ (T.a 1) (T.b 1) - (s : ℝ) • Molecule.gapAt L w κ (T.a 0) (T.b 0)‖ ≤ ρ₁) :
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((2 * ⌊2 * L⌋₊ + 1) ^ d * ((⌊2 * ρ₀ * L⌋₊ + 1) ^ d * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d) : ℕ) : ℕ∞) := by
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  swap
  · rw [T.tripleSet_empty L γ δ w Adm c β k0 hne]; simp
  obtain ⟨κs, hκs⟩ := hne
  have hball0 := card_alphaN_le L r₀ ρ₀ hL (T.rho_nonneg L γ δ w Adm c β k0 0 r₀ ρ₀ κs hκs hb0)
  have hρ₁ : 0 ≤ ρ₁ := (norm_nonneg _).trans (hb1 κs hκs)
  have hball1 := card_alphaN_le L (0 : Mom d) ρ₁ hL hρ₁
  have hsub : T.tripleSet L γ δ w Adm c β k0 ⊆
      (fun p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) => fun j : Fin 3 =>
        if j = 0 then T.triZ κs 0 + p.1 else if j = 1 then T.triZ κs 0 + p.1 - (p.2.2 + s • p.2.1)
        else T.triZ κs 0 + p.1 + p.2.1) ''
        ((boxF d ⌊2 * L⌋₊ ×ˢ (alphaN d L r₀ ρ₀ ×ˢ alphaN d L (0 : Mom d) ρ₁) : Finset _) :
          Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))) := by
    rintro _ ⟨κ, hκ, rfl⟩
    have hg0 := gapAt_eq M T L w κ hκ.1.1 0
    have hg1 := gapAt_eq M T L w κ hκ.1.1 1
    rw [fin3_zero_sub] at hg0
    rw [fin3_one_sub] at hg1
    refine ⟨(T.triZ κ 0 - T.triZ κs 0, T.triZ κ 2 - T.triZ κ 0,
      (T.triZ κ 0 - T.triZ κ 1) - s • (T.triZ κ 2 - T.triZ κ 0)), ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product]
      refine ⟨T.box_u L γ δ hL w Adm c β k0 κ κs hκ hκs 0, ?_, ?_⟩
      · have := T.gap_mem_alphaN L hL w 0 r₀ ρ₀ κ hκ.1.1 (hb0 κ hκ)
        rwa [fin3_zero_sub] at this
      · apply mem_alphaN_of_norm_le L hL
        have h := hb1 κ hκ
        rw [hg0, hg1, ← latticePoint_sub_smul] at h
        simpa using h
    · funext j
      fin_cases j
      · simp
      · show T.triZ κs 0 + (T.triZ κ 0 - T.triZ κs 0) -
          (((T.triZ κ 0 - T.triZ κ 1) - s • (T.triZ κ 2 - T.triZ κ 0)) + s • (T.triZ κ 2 - T.triZ κ 0)) = T.triZ κ 1
        funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega
      · show T.triZ κs 0 + (T.triZ κ 0 - T.triZ κs 0) + (T.triZ κ 2 - T.triZ κ 0) = T.triZ κ 2
        funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega
  have h1 := encard_le_of_subset_image _ _ _ hsub
  refine h1.trans ?_
  rw [Finset.card_product, Finset.card_product, card_boxF]
  have h3 : (2 * ⌊2 * L⌋₊ + 1) ^ d * ((alphaN d L r₀ ρ₀).card * (alphaN d L (0 : Mom d) ρ₁).card) ≤
      (2 * ⌊2 * L⌋₊ + 1) ^ d * ((⌊2 * ρ₀ * L⌋₊ + 1) ^ d * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d) :=
    Nat.mul_le_mul le_rfl (Nat.mul_le_mul hball0 hball1)
  exact_mod_cast h3

/-- **`ΔF = 1`, first cut a `β`-cut: its gap is a function of the parameters.** -/
theorem gap0_const_of_beta (hβ0 : ¬ T.m1.SameComponent (T.t 0) (T.f 0)) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (κ κs : D → (Fin d → ℤ)) (hκ : κ ∈ decSet M L γ δ w Adm c β k0) (hκs : κs ∈ decSet M L γ δ w Adm c β k0) :
    Molecule.gapAt L w κ (T.a 0) (T.b 0) = Molecule.gapAt L w κs (T.a 0) (T.b 0) := by
  obtain ⟨hC0, -⟩ := T.rel0 hβ0 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
  have hC0' := (triC_eq_iff L hL.ne' w (T.triZ κ) (T.triZ κs) 0).1 hC0
  rw [fin3_zero_sub] at hC0'
  have hg0 := gapAt_eq M T L w κ hκ.1.1 0
  have hg0s := gapAt_eq M T L w κs hκs.1.1 0
  rw [fin3_zero_sub] at hg0 hg0s
  rw [hg0, hg0s]
  congr 1
  funext k; have := congrFun hC0' k; simp only [Pi.sub_apply] at this ⊢; omega

end TriData
end WaveTurbulence.FinalCount
