/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.WickCorrection
public import WaveTurbulence.Foundations.ApproxNT.PoissonPair
public import WaveTurbulence.Foundations.NTSP.FullSum

/-!
# Poisson summation for the localized link

TARGET (incohproof12)–(incohproof14), reusing the landed pair Poisson
formula and the exact tensor cutoff of Lemma 5.2.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff SchwartzMap

namespace WaveTurbulence.Incoh

variable {d : ℕ}

/-- The smooth physical integrand underlying the unmasked link sum. -/
@[expose] def pairLinkIntegrand (s : ℝ) (A : LinkParameters d) (z : Mom d × Mom d) : ℂ :=
  Real.fourierChar (inner ℝ z.1 A.leftShift + inner ℝ z.2 A.rightShift +
    s * inner ℝ z.1 z.2) •
    (Fourier.chi0MomSchwartz d (z.1 - A.leftCenter) *
      Fourier.chi0MomSchwartz d (z.2 - A.rightCenter))

theorem contDiff_pairLinkIntegrand (s : ℝ) (A : LinkParameters d) :
    ContDiff ℝ ∞ (pairLinkIntegrand s A) := by
  have hphase : ContDiff ℝ ∞ (fun z : Mom d × Mom d =>
      ((Real.fourierChar (inner ℝ z.1 A.leftShift + inner ℝ z.2 A.rightShift +
        s * inner ℝ z.1 z.2) : Circle) : ℂ)) := by
    simp_rw [Real.fourierChar_apply]
    refine Complex.contDiff_exp.comp ?_
    refine ContDiff.mul ?_ contDiff_const
    refine Complex.ofRealCLM.contDiff.comp ?_
    refine contDiff_const.mul ?_
    exact ((contDiff_fst.inner ℝ contDiff_const).add (contDiff_snd.inner ℝ contDiff_const)).add
      (contDiff_const.mul (contDiff_fst.inner ℝ contDiff_snd))
  have hχ := (Fourier.chi0MomSchwartz d).smooth (⊤ : ℕ∞)
  unfold pairLinkIntegrand
  simp_rw [Circle.smul_def]
  exact hphase.mul ((hχ.comp (contDiff_fst.sub contDiff_const)).mul
    (hχ.comp (contDiff_snd.sub contDiff_const)))

theorem hasCompactSupport_pairLinkIntegrand (s : ℝ) (A : LinkParameters d) :
    HasCompactSupport (pairLinkIntegrand s A) := by
  have hc : HasCompactSupport (fun x : Mom d => Fourier.chi0MomSchwartz d x) :=
    (Fourier.chi0TensorComplex_hasCompactSupport d).comp_homeomorph
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toHomeomorph
  have ha := hc.comp_homeomorph (Homeomorph.subRight A.leftCenter)
  have hb := hc.comp_homeomorph (Homeomorph.subRight A.rightCenter)
  apply HasCompactSupport.of_support_subset_isCompact (ha.isCompact.prod hb.isCompact)
  intro z hz
  have hza : Fourier.chi0MomSchwartz d (z.1 - A.leftCenter) ≠ 0 := by
    intro h; apply hz; simp only [pairLinkIntegrand, h, zero_mul, smul_zero]
  have hzb : Fourier.chi0MomSchwartz d (z.2 - A.rightCenter) ≠ 0 := by
    intro h; apply hz; simp only [pairLinkIntegrand, h, mul_zero, smul_zero]
  exact ⟨subset_tsupport _ hza, subset_tsupport _ hzb⟩

/-- The lattice evaluation is the literal unmasked factor, with the same `2π` convention. -/
theorem pairLinkIntegrand_lattice (L s : ℝ) (A : LinkParameters d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    pairLinkIntegrand s A (latticePoint L p.1, latticePoint L p.2) =
      cutoffAmplitude L A p * WeylSums.e (linkPhase L s A p) := by
  simp only [pairLinkIntegrand, Fourier.chi0MomSchwartz_apply, Fourier.chi0TensorComplex,
    Fourier.chi0Tensor, WeylSums.latticeCutoff, cutoffAmplitude, linkPhase,
    Real.fourierChar_apply, Circle.smul_def, WeylSums.e, Complex.ofReal_mul]
  simp only [smul_eq_mul, mul_comm, mul_assoc, Complex.ofReal_ofNat]

/-- The unmasked lattice factor is exactly its absolutely summable Poisson-dual series. -/
theorem bilinearLatticeSum_eq_poisson {L : ℝ} (hL : 0 < L) (s : ℝ)
    (A : LinkParameters d) :
    WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift =
      (L ^ (2 * d) : ℂ) * ∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
        Fourier.bilinearPhaseIntegral (Fourier.chi0MomSchwartz d) (Fourier.chi0MomSchwartz d)
          A.leftCenter A.rightCenter (L • NTSP.intVec gh.1 + A.leftShift)
            (L • NTSP.intVec gh.2 + A.rightShift) s := by
  have hP := ApproxNT.poisson_pair (F := fun x y => pairLinkIntegrand s A (x, y))
    (contDiff_pairLinkIntegrand s A) (hasCompactSupport_pairLinkIntegrand s A) hL
  simp only [pairLinkIntegrand_lattice, pureLink_eq_bilinearLatticeSum] at hP
  rw [hP]
  congr 1
  rw [← (Equiv.neg ((Fin d → ℤ) × (Fin d → ℤ))).tsum_eq]
  refine tsum_congr fun gh => ?_
  let A' : LinkParameters d := { A with
    leftShift := L • NTSP.intVec gh.1 + A.leftShift
    rightShift := L • NTSP.intVec gh.2 + A.rightShift }
  have hint : Integrable (pairLinkIntegrand s A') :=
    (contDiff_pairLinkIntegrand s A').continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_pairLinkIntegrand s A')
  rw [Fourier.bilinearPhaseIntegral]
  change _ = ∫ y : Mom d, ∫ x : Mom d, pairLinkIntegrand s A' (x, y)
  rw [← integral_prod_symm _ hint]
  apply integral_congr_ae
  filter_upwards [] with z
  have hneg (g : Fin d → ℤ) : NTSP.intVec (-g) = -NTSP.intVec g := by
    ext i; simp only [NTSP.intVec_apply, Pi.neg_apply, Int.cast_neg, PiLp.neg_apply]
  simp only [Equiv.neg_apply, Prod.fst_neg, Prod.snd_neg, pairLinkIntegrand, smul_smul, hneg]
  congr 1
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [A', inner_add_right, inner_neg_right, inner_smul_right]
  ring

end WaveTurbulence.Incoh
