/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.CutCone
public import WaveTurbulence.Foundations.FinalCount.G3Ex34
/-! **Ghost assembly: the `α`-cut creation cone in `excessRHS` form, and for a uniform Step 3.**

`alphaCut_excess_cone`: under the cut cone of aperture `θ₀ = L^{-6η}` and a critical label, the `α`-cut deviation is at
most `3·5^d·cAlpha·L^{-5ηk}·excessRHS [(R,0),(R,0)] 0 0` for `k ≤ 2` (main's `alphaCut_excess`, `κ = 0`, times the cone
factor `3·5^{d-1}θ₀^{d-1} ≤ 3·5^d L^{-12η}`). `UStep3.excess_cone`: the same for a uniform Step 3 of the run (main's
`cut_excess` form). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

/-- **The `α`-cut deviation with the creation cone.** -/
theorem alphaCut_excess_cone (hd : 3 ≤ d) (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hα : M.IsAlphaCut v v₂ x₁ x₂)
    (L γ η δ C₁ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (h200a : 200 * η ≤ γ) (h200b : 200 * η ≤ 1 - γ)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) (hL : Real.exp 1 ≤ L)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hPinh : ∀ S' ∈ (M.cut v v₂ x₁ x₂).maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (R : ℝ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (hcrit : Crit L γ η R)
    (hgap : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' x₁ x₂‖ ≤ 2 * R)
    (hcone : CutCone M x₁ x₂ L γ δ (L ^ (-6 * η)) w Adm) (k : ℕ) (hk : k ≤ 2) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((M.cut v v₂ x₁ x₂).countA L γ δ C₁ w Adm P)
      (ENNReal.ofReal ((3 * 5 ^ d * cAlpha d γ η) * L ^ (-5 * η * (k : ℝ)) *
        excessRHS L γ η [(R, 0), (R, 0)] 0 0)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hR0 : 0 ≤ R := (inv_nonneg.2 hL0.le).trans hRl
  have hη2 : η ≤ 1 / 2 := by linarith
  have hηγ : η ≤ γ := by linarith
  set θ := L ^ (-6 * η) with hθdef
  have hθ0 : 0 ≤ θ := Real.rpow_nonneg hL0.le _
  have h := alphaCut_isDeviation_cone M hcd hdeg hM hα L γ δ C₁ θ w Adm P hL hδ0 (by linarith) hP0 hPinh R hR0 hθ0
    hgap hcone
  refine isDeviation_mono h ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  set F := L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ 4 with hF
  have hF0 : 0 ≤ F := by
    have : 0 ≤ Real.log L := Real.log_nonneg hL1
    positivity
  have hRL : 1 ≤ 2 * R * L := by
    have := mul_le_mul_of_nonneg_right hRl hL0.le
    rw [inv_mul_cancel₀ hL0.ne'] at this
    nlinarith
  have hθρ : 1 ≤ θ * (2 * R * L) := by
    have := theta_rho_ge_one hL1 hγ0 hγ1 hη h200a h200b hcrit
    simpa [hθdef, mul_assoc] using this
  have hN := coneCutN_le L (δ⁻¹ * L ^ (-2 * γ)) R θ hL0 hRL hθρ hθ0 (by omega : 1 ≤ d)
  have hb := alphaDev_kappa0 d (L := L) (γ := γ) (δ := δ) (C₁ := C₁) (R := R) hd hη hη2 hL hδ0 hδ1 hC hRl hRu hηγ
  have hE0 : excessRHS L γ η [(R, 0), (R, 0)] 0 0 = L ^ (-η ^ 3) * (L ^ ((γ + 3 * η) / 2) * R) ^ 2 := by
    rw [excessRHS_alpha]; simp
  have hθd : θ ^ (d - 1) ≤ L ^ (-5 * η * (k : ℝ)) := by
    refine (coneFactor_le hL1 hη.le hd).trans (Real.rpow_le_rpow_of_exponent_le hL1 ?_)
    have : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    nlinarith
  have hcα : 26 * 5 ^ d * (8 / η) ^ 4 ≤ cAlpha d γ η := by
    unfold cAlpha
    have h1g : 0 < 1 - γ := by linarith
    have h8 : 0 ≤ (8 / (1 - γ)) ^ 4 := by positivity
    have h26 : (0 : ℝ) ≤ 26 * 5 ^ d := by positivity
    nlinarith
  have h5 : (5 : ℝ) ^ (d - 1) ≤ 5 ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
  have hX0 : 0 ≤ excessRHS L γ η [(R, 0), (R, 0)] 0 0 := by rw [hE0]; positivity
  have hcα0 : 0 ≤ 26 * 5 ^ d * (8 / η) ^ 4 := by positivity
  calc (coneCutN d L (δ⁻¹ * L ^ (-2 * γ)) R θ : ℝ) * F
      ≤ (3 * 5 ^ (d - 1) * θ ^ (d - 1) * (alphaN' d L (δ⁻¹ * L ^ (-2 * γ)) R (2 * R) : ℝ)) * F :=
        mul_le_mul_of_nonneg_right hN hF0
    _ = 3 * 5 ^ (d - 1) * θ ^ (d - 1) * ((alphaN' d L (δ⁻¹ * L ^ (-2 * γ)) R (2 * R) : ℝ) * F) := by ring
    _ ≤ 3 * 5 ^ (d - 1) * θ ^ (d - 1) * ((26 * 5 ^ d * (8 / η) ^ 4) * excessRHS L γ η [(R, 0), (R, 0)] 0 0) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hE0]; exact hb
    _ ≤ 3 * 5 ^ d * L ^ (-5 * η * (k : ℝ)) * (cAlpha d γ η * excessRHS L γ η [(R, 0), (R, 0)] 0 0) := by
        have hA : 0 ≤ (26 * 5 ^ d * (8 / η) ^ 4) * excessRHS L γ η [(R, 0), (R, 0)] 0 0 := by positivity
        have hθ1 : 0 ≤ θ ^ (d - 1) := by positivity
        calc 3 * 5 ^ (d - 1) * θ ^ (d - 1) * ((26 * 5 ^ d * (8 / η) ^ 4) * excessRHS L γ η [(R, 0), (R, 0)] 0 0)
            ≤ 3 * 5 ^ d * L ^ (-5 * η * (k : ℝ)) * ((26 * 5 ^ d * (8 / η) ^ 4) *
                excessRHS L γ η [(R, 0), (R, 0)] 0 0) := by
              refine mul_le_mul_of_nonneg_right ?_ hA
              exact mul_le_mul (by linarith) hθd hθ1 (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcα hX0) (by positivity)
    _ = (3 * 5 ^ d * cAlpha d γ η) * L ^ (-5 * η * (k : ℝ)) * excessRHS L γ η [(R, 0), (R, 0)] 0 0 := by ring

end

section
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop}

/-- **Step 3 (`α`-cut, `κ = 0`, critical label) with the creation cone** (main's `cut_excess`, `α` part, with the cone). -/
theorem cut_excess_cone {δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) {Rn : ℕ} {h : HSt V D₀} (hI : Inv Rn h.s)
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S) {v v₂ : V} {x₁ x₂ : h.s.D}
    (hc : h.s.M.IsCutData v v₂ x₁ x₂)
    (hPinh : ∀ S' ∈ (h.s.M.cut v v₂ x₁ x₂).maximalLadders, ∀ S ∈ h.s.M.maximalLadders, S' ⊆ S → P S' = P S)
    (R : ℝ) (hR : IsLabel L γ η R) (hcrit : Crit L γ η R)
    (hsim : ∀ k0, Adm0 k0 → GapSim L w (k0 ∘ h.s.down) x₁ x₂ R)
    (hα : h.s.M.IsAlphaCut v v₂ x₁ x₂)
    (hcone : CutCone h.s.M x₁ x₂ L γ δ (L ^ (-6 * η)) w (AdmS Adm0 h.s)) (k : ℕ) (hk : k ≤ 2) :
    IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P)
      ((h.s.M.cut v v₂ x₁ x₂).countA L γ δ C₁ w (AdmS Adm0 h.s) P)
      (ENNReal.ofReal ((3 * 5 ^ d * cAlpha d γ η) * L ^ (-5 * η * (k : ℝ)) *
        excessRHS L γ η [(R, 0), (R, 0)] 0 0)) := by
  have hM : ∀ a ∈ h.s.M.atoms, h.s.M.deg a ≤ 4 := fun a ha => deg_le_four _ (hI.bounds a ha)
  obtain ⟨-, hRl, hRu⟩ := hR
  exact alphaCut_excess_cone h.s.M H.hd hc (hM v hc.1) hM hα L γ η δ C₁ H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 w
    (AdmS Adm0 h.s) P H.hL H.hδ0 H.hδ1 H.hC hP0 hPinh R hRl hRu hcrit
    (fun κ' hκ' => by obtain ⟨k0, hk0, rfl⟩ := hκ'; exact (hsim k0 hk0).2) hcone k hk

end

end WaveTurbulence.GammaLow.FinalCount.Ghost
