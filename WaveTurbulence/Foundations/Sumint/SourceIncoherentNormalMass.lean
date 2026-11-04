/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceFactorMasses
public import WaveTurbulence.Foundations.Sumint.SourceEndpointNormalMass
public import WaveTurbulence.Foundations.Sumint.SourceGainGeometry

/-!
# Incoherence gain for the native normal source mass

A normal triple counted in M₀ has a label different from its third
label. Its third time therefore belongs to one of two endpoint strips;
the total two-gap radius is sufficient for either discrepant label.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- TARGET sumint normal incoherence: both native-mass contributions remain explicit. -/
theorem exists_incoherent_normalFactorMass_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ Cs Cm R : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∀ A η : ℝ, D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
        (i : {i : Fin D.S.I // D.S.nor i = true}), h ∈ Icc (0:ℝ) 1 →
      ¬ (D.q (.inr (.inr ⟨i,0⟩)) = D.q (.inr (.inr ⟨i,1⟩)) ∧
        D.q (.inr (.inr ⟨i,1⟩)) = D.q (.inr (.inr ⟨i,2⟩))) →
      normalFactorMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) i ≤
        ENNReal.ofReal ((16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹ *
          (Cs*(4*L)^(3*d)*(Real.sqrt h+(16*sourceHalfScale L γ δ)^(-(1/2:ℝ)))+
            (1+2*h)*Cm*(4*L)^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log (4*L))) := by
  obtain ⟨Cs,Cm,R,hCs,hCm,hR,hbound⟩ := exists_endpointNormalMass_bound d hd γ hγ τstar hτstar
  refine ⟨2*Cs,2*Cm,R,mul_nonneg (by norm_num) hCs,mul_nonneg (by norm_num) hCm,hR,?_⟩
  intro L hL D δ N hδ hτ A η hD p ν r t c h i hh hq
  have hLp : 0 < L := by linarith [hR.trans hL]
  let e0 := (D.q (.inr (.inr ⟨i,2⟩)):ℝ)-c
  let e1 := (D.q (.inr (.inr ⟨i,2⟩)):ℝ)+1-c
  let F := fun (e : ℝ) (z : Fin 3 → ℝ) =>
    if |z 2-e| ≤ 2*h+(|z 0-z 2|+|z 1-z 2|) then ‖normalTimeSum D L γ δ p ν r t i z‖ₑ else 0
  have hpoint (z : Fin 3 → ℝ) (hz : z ∈ Icc
      (fun j => enlargedTimeLower D c h (.inr (.inr ⟨i,j⟩)))
      (fun j => enlargedTimeUpper D c h (.inr (.inr ⟨i,j⟩)))) :
      ‖normalTimeSum D L γ δ p ν r t i z‖ₑ ≤ F e0 z+F e1 z := by
    have hget (j : Fin 3) (hqj : D.q (.inr (.inr ⟨i,j⟩)) ≠ D.q (.inr (.inr ⟨i,2⟩))) :=
      enlarged_unit_gap_endpoint hqj.symm hh.1
        (show (D.q (.inr (.inr ⟨i,2⟩)):ℝ)-c-h ≤ z 2 ∧
          z 2 ≤ (D.q (.inr (.inr ⟨i,2⟩)):ℝ)+1-c+h from ⟨hz.1 2,hz.2 2⟩)
        (show (D.q (.inr (.inr ⟨i,j⟩)):ℝ)-c-h ≤ z j ∧
          z j ≤ (D.q (.inr (.inr ⟨i,j⟩)):ℝ)+1-c+h from ⟨hz.1 j,hz.2 j⟩)
    have hs : ∃ e : ℝ, (e = e0 ∨ e = e1) ∧ |z 2-e| ≤ 2*h+(|z 0-z 2|+|z 1-z 2|) := by
      rcases source_normal_incoherence_choice D i hq with hq0 | hq1
      · obtain ⟨e,he,heq⟩ := hget 0 hq0
        refine ⟨e,he,?_⟩
        rw [abs_sub_comm (z 2) (z 0)] at heq
        linarith only [heq,abs_nonneg (z 1-z 2)]
      · obtain ⟨e,he,heq⟩ := hget 1 hq1
        refine ⟨e,he,?_⟩
        rw [abs_sub_comm (z 2) (z 1)] at heq
        linarith only [heq,abs_nonneg (z 0-z 2)]
    obtain ⟨e,he,hs⟩ := hs
    rcases he with he | he
    · have hs0 : |z 2-e0| ≤ 2*h+(|z 0-z 2|+|z 1-z 2|) := by simpa only [he] using hs
      dsimp only [F]
      rw [ite_eq_left hs0]
      exact le_add_right le_rfl
    · have hs1 : |z 2-e1| ≤ 2*h+(|z 0-z 2|+|z 1-z 2|) := by simpa only [he] using hs
      dsimp only [F]
      rw [ite_eq_left hs1]
      exact le_add_left le_rfl
  let U := (16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹ *
    (Cs*(4*L)^(3*d)*(Real.sqrt h+(16*sourceHalfScale L γ δ)^(-(1/2:ℝ)))+
      (1+2*h)*Cm*(4*L)^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log (4*L))
  have hU : 0 ≤ U := by
    have hs : 0 < 16*sourceHalfScale L γ δ := by
      unfold sourceHalfScale
      exact mul_pos (by norm_num) (div_pos (mul_pos hδ.1 (Real.rpow_pos_of_pos hLp _)) (by norm_num))
    have hlog : 0 ≤ Real.log (4*L) := Real.log_nonneg (by linarith [hR.trans hL])
    have hh0 : 0 ≤ h := hh.1
    dsimp [U]
    positivity
  have hb0 := hbound L hL D δ N hδ hτ A η hD p ν r t c h e0 i hh
  have hb1 := hbound L hL D δ N hδ hτ A η hD p ν r t c h e1 i hh
  calc
    _ ≤ ∫⁻ z in Icc (fun j => enlargedTimeLower D c h (.inr (.inr ⟨i,j⟩)))
        (fun j => enlargedTimeUpper D c h (.inr (.inr ⟨i,j⟩))), F e0 z+F e1 z := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      rw [ofReal_norm]
      exact hpoint z hz
    _ = endpointNormalMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) h e0 i+
        endpointNormalMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) h e1 i :=
      lintegral_add_left (measurable_endpointNormalMass_integrand D hLp γ δ p ν r t h e0 i) _
    _ ≤ ENNReal.ofReal U+ENNReal.ofReal U := add_le_add hb0 hb1
    _ = _ := by
      rw [← ENNReal.ofReal_add hU hU]
      congr 1
      dsimp [U]
      ring

end WaveTurbulence.Sumint
