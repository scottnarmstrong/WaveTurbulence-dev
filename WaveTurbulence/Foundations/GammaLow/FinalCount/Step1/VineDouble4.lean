/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineDouble4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble3
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VineDouble4`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 The label count of a VC formed by two double bonds, part 4: `labelSet` injects into a finite set of triples
`(κx₁, κx₁-κx₂, κx₁-κy₁)` (box × gap ball × energy strip), and the cardinality of that set. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace DoubleShape
open WaveTurbulence.FinalCount.DoubleShape
variable {M : Molecule V D} {K : VineCut g M} (S : DoubleShape K)

variable {L γ δ : ℝ} {w : Mom d} {Adm : (D → (Fin d → ℤ)) → Prop} {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d}
include S

theorem labelSet_encard_le (hP : ParamOK M c k0) (hL : 0 < L) (R ρ : ℝ) (r₀ : Mom d)
    (hgapLow : ∀ κ', Adm κ' → R / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖)
    (hball : ∀ κ' ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ' K.x₁ K.x₂ - r₀‖ ≤ ρ) :
    (K.labelSet L γ δ w Adm c β k0).encard ≤
      (tripleFin L (δ⁻¹ * L ^ (-2 * γ) / 2) R ρ (β S.x) (k0 K.x₁ - w) r₀ (k0 K.x₁ - k0 K.y₁)).card := by
  set Φ : (D → (Fin d → ℤ)) → (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) :=
    fun ℓ => (ℓ K.x₁, ℓ K.x₁ - ℓ K.x₂, ℓ K.x₁ - ℓ K.y₁) with hΦ
  have hinj : Set.InjOn Φ (K.labelSet L γ δ w Adm c β k0) := by
    rintro _ ⟨κ, hκ, rfl⟩ _ ⟨κ', hκ', rfl⟩ h
    simp only [hΦ, K.restrS_x₁, K.restrS_x₂, K.restrS_y₁, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have h2' : κ K.x₂ = κ' K.x₂ := by
      have : κ K.x₁ - κ K.x₂ = κ' K.x₁ - κ' K.x₂ := h2
      rw [h1] at this
      exact (sub_right_inj.mp this)
    have h3' : κ K.y₁ = κ' K.y₁ := by
      have : κ K.x₁ - κ K.y₁ = κ' K.x₁ - κ' K.y₁ := h3
      rw [h1] at this
      exact (sub_right_inj.mp this)
    exact S.restrS_eq hP hL hκ hκ' h1 h2' h3'
  have hsub : Φ '' (K.labelSet L γ δ w Adm c β k0) ⊆
      ↑(tripleFin L (δ⁻¹ * L ^ (-2 * γ) / 2) R ρ (β S.x) (k0 K.x₁ - w) r₀ (k0 K.x₁ - k0 K.y₁)) := by
    rintro _ ⟨_, ⟨κ, hκ, rfl⟩, rfl⟩
    simp only [hΦ, K.restrS_x₁, K.restrS_x₂, K.restrS_y₁]
    obtain ⟨hdec, hres, hadm⟩ := hκ
    have hk1 : ‖Molecule.kvec L w κ K.x₁ - k0 K.x₁‖ ≤ 1 := hres.2 K.x₁
    have hk3 : ‖Molecule.kvec L w κ K.y₁ - k0 K.y₁‖ ≤ 1 := hres.2 K.y₁
    have hgap : latticePoint L (κ K.x₁ - κ K.x₂) = Molecule.gapAt L w κ K.x₁ K.x₂ := by
      unfold Molecule.gapAt Molecule.kvec; rw [lp_sub_eq]; abel
    have hu : latticePoint L (κ K.x₁ - κ K.y₁) = Molecule.kvec L w κ K.x₁ - Molecule.kvec L w κ K.y₁ := by
      unfold Molecule.kvec; rw [lp_sub_eq]; abel
    have hmem1 : κ K.x₁ ∈ alphaN d L (k0 K.x₁ - w) 1 := by
      refine mem_alphaN_of_norm_le L hL _ _ _ ?_
      have : latticePoint L (κ K.x₁) - (k0 K.x₁ - w) = Molecule.kvec L w κ K.x₁ - k0 K.x₁ := by
        unfold Molecule.kvec; abel
      rw [this]; exact hk1
    have hdecκ : κ ∈ decSet M L γ δ w Adm c β k0 := ⟨hdec, hres, hadm⟩
    have hmem2 : κ K.x₁ - κ K.x₂ ∈ (alphaN d L r₀ ρ).filter fun nr => R / 2 ≤ ‖latticePoint L nr‖ := by
      rw [Finset.mem_filter]
      exact ⟨mem_alphaN_of_norm_le L hL r₀ ρ _ (by rw [hgap]; exact hball κ hdecκ),
        by rw [hgap]; exact hgapLow κ hadm⟩
    have hnorm : ‖latticePoint L (κ K.x₁ - κ K.y₁) - (k0 K.x₁ - k0 K.y₁)‖ ≤ 2 := by
      rw [hu]
      have : Molecule.kvec L w κ K.x₁ - Molecule.kvec L w κ K.y₁ - (k0 K.x₁ - k0 K.y₁) =
          (Molecule.kvec L w κ K.x₁ - k0 K.x₁) - (Molecule.kvec L w κ K.y₁ - k0 K.y₁) := by abel
      rw [this]
      calc _ ≤ ‖Molecule.kvec L w κ K.x₁ - k0 K.x₁‖ + ‖Molecule.kvec L w κ K.y₁ - k0 K.y₁‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hk1 hk3
        _ = 2 := by norm_num
    have hstrip : |inner ℝ (latticePoint L (κ K.x₁ - κ K.x₂)) (latticePoint L (κ K.x₁ - κ K.y₁)) -
        (‖latticePoint L (κ K.x₁ - κ K.x₂)‖ ^ 2 + β S.x / 2)| ≤ δ⁻¹ * L ^ (-2 * γ) / 2 := by
      have hG := S.gamma_x hP hdecκ
      have hb := hres.1 S.x S.x_mem
      rw [hgap, hu]
      rw [hG, inner_sub_right, real_inner_self_eq_norm_sq] at hb
      have e : inner ℝ (Molecule.gapAt L w κ K.x₁ K.x₂) (Molecule.kvec L w κ K.x₁ - Molecule.kvec L w κ K.y₁) -
          (‖Molecule.gapAt L w κ K.x₁ K.x₂‖ ^ 2 + β S.x / 2) =
          (2 * (inner ℝ (Molecule.gapAt L w κ K.x₁ K.x₂) (Molecule.kvec L w κ K.x₁ - Molecule.kvec L w κ K.y₁) -
            ‖Molecule.gapAt L w κ K.x₁ K.x₂‖ ^ 2) - β S.x) / 2 := by ring
      rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hmemu : κ K.x₁ - κ K.y₁ ∈ stripSet L (δ⁻¹ * L ^ (-2 * γ) / 2) (β S.x) (k0 K.x₁ - k0 K.y₁)
        (κ K.x₁ - κ K.x₂) := by
      unfold stripSet
      rw [Finset.mem_filter]
      exact ⟨mem_alphaN_of_norm_le L hL _ _ _ hnorm, hnorm, hstrip⟩
    unfold tripleFin
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨(κ K.x₁, κ K.x₁ - κ K.x₂), Finset.mem_product.2 ⟨hmem1, hmem2⟩,
      Finset.mem_image.2 ⟨_, hmemu, rfl⟩⟩
  calc _ = (Φ '' (K.labelSet L γ δ w Adm c β k0)).encard := (hinj.encard_image).symm
    _ ≤ (↑(tripleFin L (δ⁻¹ * L ^ (-2 * γ) / 2) R ρ (β S.x) (k0 K.x₁ - w) r₀ (k0 K.x₁ - k0 K.y₁)) : Set _).encard :=
        Set.encard_le_encard hsub
    _ = _ := by rw [Set.encard_coe_eq_coe_finsetCard]

end DoubleShape
end WaveTurbulence.GammaLow.FinalCount.Step1
