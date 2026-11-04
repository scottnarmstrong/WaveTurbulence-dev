/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PairMassDomination
public import WaveTurbulence.Foundations.Sumint.SourceEndpointPairMass

/-!
# Incoherence gain for the exact source pair mass

Different unit labels force the pair into one of two enlarged endpoint
strips. Both choices are integrated using the actual strip estimate;
constants are doubled once, before δ and Dsteps are selected.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- TARGET sumint pair incoherence: the plain native mass keeps the small-width gain and Weyl reserve. -/
theorem exists_incoherent_plainPairMass_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ Cs Cm R : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∀ A : ℝ, D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
        (a : Σ i : Fin D.S.I, Fin (D.S.m i)), h ∈ Icc (0:ℝ) 1 →
      D.q (.inl ⟨a.1,a.2.succ⟩) ≠ D.q (.inr (.inl a)) →
      plainPairMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) a ≤
        ENNReal.ofReal ((16*sourceHalfScale L γ δ)⁻¹*(Cs*(4*L)^(2*d)*(4*h+2/(16*sourceHalfScale L γ δ)))+
          (1+2*h)*(16*sourceHalfScale L γ δ)⁻¹*Cm*
            (4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by
  obtain ⟨Cs,Cm,R,hCs,hCm,hR,hbound⟩ := exists_endpointPairMass_bound d hd γ hγ η hη τstar hτstar
  refine ⟨2*Cs,2*Cm,R,mul_nonneg (by norm_num) hCs,mul_nonneg (by norm_num) hCm,hR,?_⟩
  intro L hL D δ N hδ hτ A hD p ν r t c h a hh hq
  have hLp : 0 < L := by linarith [hR.trans hL]
  let e0 := (D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)-c
  let e1 := (D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)+1-c
  let F := fun (e : ℝ) (z : ℝ × ℝ) =>
    if |z.1-e| ≤ 2*h+|z.1-z.2| then ‖pairTimeSum D L γ δ p ν r t a z‖ₑ else 0
  have hpoint (z : ℝ × ℝ) (hz : z ∈ Icc
      (enlargedTimeLower D c h (.inl ⟨a.1,a.2.succ⟩),enlargedTimeLower D c h (.inr (.inl a)))
      (enlargedTimeUpper D c h (.inl ⟨a.1,a.2.succ⟩),enlargedTimeUpper D c h (.inr (.inl a)))) :
      ‖pairTimeSum D L γ δ p ν r t a z‖ₑ ≤ F e0 z+F e1 z := by
    obtain ⟨e,he,hs⟩ := enlarged_unit_gap_endpoint hq hh.1
      (show (D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)-c-h ≤ z.1 ∧
        z.1 ≤ (D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)+1-c+h from ⟨hz.1.1,hz.2.1⟩)
      (show (D.q (.inr (.inl a)):ℝ)-c-h ≤ z.2 ∧
        z.2 ≤ (D.q (.inr (.inl a)):ℝ)+1-c+h from ⟨hz.1.2,hz.2.2⟩)
    rcases he with he | he
    · have hs0 : |z.1-e0| ≤ 2*h+|z.1-z.2| := by simpa only [he] using hs
      dsimp only [F]
      rw [ite_eq_left hs0]
      exact le_add_right le_rfl
    · have hs1 : |z.1-e1| ≤ 2*h+|z.1-z.2| := by simpa only [he] using hs
      dsimp only [F]
      rw [ite_eq_left hs1]
      exact le_add_left le_rfl
  let U := (16*sourceHalfScale L γ δ)⁻¹*(Cs*(4*L)^(2*d)*(4*h+2/(16*sourceHalfScale L γ δ)))+
    (1+2*h)*(16*sourceHalfScale L γ δ)⁻¹*Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)
  have hU : 0 ≤ U := by
    have hs : 0 < 16*sourceHalfScale L γ δ := by
      unfold sourceHalfScale
      exact mul_pos (by norm_num) (div_pos (mul_pos hδ.1 (Real.rpow_pos_of_pos hLp _)) (by norm_num))
    have hh0 : 0 ≤ h := hh.1
    dsimp [U]
    positivity
  have hb0 := hbound L hL D δ N hδ hτ A hD p ν r t c h e0 a hh
  have hb1 := hbound L hL D δ N hδ hτ A hD p ν r t c h e1 a hh
  calc
    _ ≤ ∫⁻ z in Icc
        (enlargedTimeLower D c h (.inl ⟨a.1,a.2.succ⟩),enlargedTimeLower D c h (.inr (.inl a)))
        (enlargedTimeUpper D c h (.inl ⟨a.1,a.2.succ⟩),enlargedTimeUpper D c h (.inr (.inl a))),
        F e0 z+F e1 z := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      exact hpoint z hz
    _ = endpointPairMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) h e0 a+
        endpointPairMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) h e1 a :=
      lintegral_add_left (measurable_endpointPairMass_integrand D hLp γ δ p ν r t h e0 a) _
    _ ≤ ENNReal.ofReal U+ENNReal.ofReal U := add_le_add hb0 hb1
    _ = _ := by
      rw [← ENNReal.ofReal_add hU hU]
      congr 1
      dsimp [U]
      ring

end WaveTurbulence.Sumint
