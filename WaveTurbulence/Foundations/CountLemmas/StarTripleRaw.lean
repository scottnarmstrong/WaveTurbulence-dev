/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.TripleWeight
public import WaveTurbulence.Foundations.CountLemmas.CoupledSets
public import WaveTurbulence.Foundations.CountLemmas.FullStarIntegral

/-! # Fourier counting for the shared-variable triple constraint -/

public section
open MeasureTheory Set Finset
open WaveTurbulence.WeylSums
namespace WaveTurbulence.CountLemmas

/-- The star counting estimate before bandwidth power comparison. Constants
are uniform in the three centers, the translation v, and both energy levels. -/
theorem exists_star_triple_raw_bound (d : ℕ) (hd : 3 ≤ d)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L τ : ℝ, 2 ≤ L → 0 < τ → 1/τ ≤ 4*L^2 →
    ∀ a b c v : Mom d, ∀ α β : ℝ,
      ((coupledTripleSet L a b c v α β τ 0).ncard : ℝ) ≤
      C*τ^2*(4*L)^(3*(d : ℝ)+1)*((48*L)^(2*ε)*(1/(4*τ*L^2))^2+
        (48*L)^(-1+4*ε)*(1/(4*τ*L^2))+(48*L)^(-1 : ℝ)) := by
  obtain ⟨Cb,hCb,hcount⟩ := exists_double_band_count_bound
  obtain ⟨Ci,hCi,hint⟩ := exists_full_star_integral_bound d hd ε hε hε1
  refine ⟨Cb*Ci/256,by positivity,?_⟩
  intro L τ hL hτ hwin a b c v α β
  have hLp : 0 < L := by linarith only [hL]
  let w := tripleBandWeight L a b c
  let I := (finite_tripleBandWeight hLp a b c).toFinset
  let S := (finite_coupledTripleSet hLp a b c v α β τ 0).toFinset
  let E := fun q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) =>
    inner ℝ (latticePoint L q.1) (latticePoint L q.2.1)-α
  let F := fun q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) =>
    inner ℝ (latticePoint L q.1-v) (latticePoint L q.2.2)-β
  have hweight (q) (hq : q ∈ S) : w q = 1 := by
    have hh := (finite_coupledTripleSet hLp a b c v α β τ 0).mem_toFinset.mp hq
    exact tripleBandWeight_eq_one L a b c q hh.1 hh.2.1 hh.2.2.1
  have hSI : S ⊆ I := by
    intro q hq
    apply (finite_tripleBandWeight hLp a b c).mem_toFinset.mpr
    change w q ≠ 0
    rw [hweight q hq]
    exact one_ne_zero
  have hc := hcount I S w E F τ hτ hSI (fun q _ => tripleBandWeight_nonneg L a b c q)
    (fun q hq => (hweight q hq).ge) (by
      intro q hq
      have hh := (finite_coupledTripleSet hLp a b c v α β τ 0).mem_toFinset.mp hq
      exact ⟨hh.2.2.2.1,hh.2.2.2.2⟩)
  let ω := fun ts : ℝ × ℝ => (-ts.2/4) • v
  let f := fun ts : ℝ × ℝ => ‖cubicLatticeSum (4*L) ts.1 ts.2 true
    ((4 : ℝ)⁻¹ • a) ((4 : ℝ)⁻¹ • b) ((4 : ℝ)⁻¹ • c) 0 0 (ω ts)‖
  obtain ⟨_hi,hb⟩ := hint (4*L) (16/τ) (by linarith only [hL]) (by positivity)
    (by have hh := mul_le_mul_of_nonneg_left hwin (by norm_num : (0 : ℝ) ≤ 16); convert hh using 1 <;> ring)
    ((4 : ℝ)⁻¹ • a) ((4 : ℝ)⁻¹ • b) ((4 : ℝ)⁻¹ • c)
    (fun _ => 0) (fun _ => 0) ω continuous_const continuous_const (by dsimp only [ω]; fun_prop)
  have hJ : (0 : ℝ) < 1/16 := by norm_num
  have hB : (1/τ)/(1/16 : ℝ) = 16/τ := by ring
  have hnorm (ts : ℝ × ℝ) : ‖doubleEnergySum I w E F ts‖ = f (ts.1/(1/16),ts.2/(1/16)) := by
    rw [tripleWeight_star_norm hLp a b c v α β ts]
    dsimp only [f,ω]
    rw [show ts.1/(1/16 : ℝ) = 16*ts.1 by ring,
      show ts.2/(1/16 : ℝ) = 16*ts.2 by ring,
      show -(16*ts.2)/4 = -4*ts.2 by ring]
  have hphysical : (∫ ts : ℝ × ℝ in ({t : ℝ | |t| ≤ 1/τ} ×ˢ {t : ℝ | |t| ≤ 1/τ}),
      ‖doubleEnergySum I w E F ts‖) =
      (1/16 : ℝ)^2*(∫ ts : ℝ × ℝ in ({t : ℝ | |t| ≤ 16/τ} ×ˢ {t : ℝ | |t| ≤ 16/τ}), f ts) := by
    simp_rw [hnorm]
    rw [integral_fullSquare_div f (1/τ) hJ,hB]
  rw [hphysical] at hc
  have ht : (16/τ)/(4*(4*L)^2) = 1/(4*τ*L^2) := by ring
  rw [show 12*(4*L) = 48*L by ring,ht] at hb
  rw [Set.ncard_eq_toFinset_card _ (finite_coupledTripleSet hLp a b c v α β τ 0)]
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ Cb*τ^2*(1/16 : ℝ)^2)
  have hfin := hc.trans (by simpa only [mul_assoc] using hh)
  convert hfin using 1; ring

end WaveTurbulence.CountLemmas
