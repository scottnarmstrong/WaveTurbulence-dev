/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1TypeBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1Gate
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1Interface
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.Stage1TypeBound`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 AMEND6' (R47-FINAL): the Stage 1 bound applied to a pair-type family (the new gate `Stage1ReductionAt`):
`stage1_type_bound` is `stage1_family_bound` with `F := U.toLF`, `U.Bounded p` in place of `Controlled`, and the
premise `TwistClosed p A`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset
open scoped Classical

theorem stage1_type_bound (C₀ : ℕ) (P : WTParams) (hs : PieceSmall P)
    (hcoarse : CoarseSplicedAt P) (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    (habs : FinalAbsorptionAt (6 * C₀) P) (hlog : 1 ≤ Real.log P.L) (hd : 1 ≤ P.d)
    (hgate : Stage1ReductionAt C₀ P)
    {p R N : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1)) (hN1 : 1 ≤ N)
    (hN : N ≤ P.N (p + 1) ^ 4) (A : Finset (LayeredGarden (2 * R)))
    (hA : ∀ LG ∈ A, Stage1Carries P p N LG) (hcl : TwistClosed p A) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (U : TypeFamily P (2 * R)) (s : ℝ) (hs0 : 0 < s) (hU : U.Bounded p)
    (hsize : ∀ LG ∈ A, U.toLF.size LG ≤ s) :
    ‖∑ LG ∈ A, U.toLF.value tt base roots LG‖ ≤ s *
      (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))) := by
  have hctrl : ∀ LG ∈ A, U.toLF.Controlled LG := fun LG hLG =>
    U.controlled_of_bounded hU LG (Canon.layer_le_of_isCanonGC (hA LG hLG).1)
  obtain ⟨S, Cl, hCl, cls, members, sel, hpart, hrep, hsound, hord, hcounts⟩ :=
    hgate p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots U s hs0 hU hsize
  letI := S.fin
  letI := hCl
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hsumm : ∀ LG ∈ A, ∀ j, Summable fun κ : GenDecoration LG.garden P.d roots 0 =>
      kernelLeavesTerm P.L P.γ P.δ LG (U.toLF.H LG j) (fun b => tt b.1.1) 0 base κ := by
    intro LG hLG j
    have hplain : LG.garden.IsPlain := (hA LG hLG).1.1
    exact summable_leafKernel_summand P.L P.γ P.δ LG (U.toLF.H LG j) _ 0 base roots 0
      (card_lone_le_one_of_plain LG.garden hplain)
      ((hctrl LG hLG j).summable_coset hd hL1 base)
  have hsum : ∑ LG ∈ A, U.toLF.value tt base roots LG = ∑ π, S.val π := by
    rw [sum_eq_sum_pieces roots A members cls sel hpart tt base U.toLF hsumm]
    exact Finset.sum_congr rfl fun π _ => ((hrep π).1).symm
  rw [hsum]
  have hnn : 0 ≤ s * (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))) := by
    have hL0 : 0 < P.L := by linarith [hs.L_ge]
    have := hs.delta_pos
    positivity
  by_cases hne : Nonempty S.Pc
  · obtain ⟨π⟩ := hne
    have hRN : R ≤ 2 * N := by
      have h1 := (hsound π).bond_count
      have h2 := hord π
      omega
    have hNlog : (N : ℝ) ≤ Real.log P.L ^ (4 * (40 * P.d) ^ (2 * P.D + 2)) := by
      have h1 : (N : ℝ) ≤ (P.N (p + 1) : ℝ) ^ 4 := by exact_mod_cast hN
      exact h1.trans (N_quartic_le_log_pow P hd hlog (p + 1))
    obtain ⟨hT2, hS2, hL⟩ := habs.2 N R hR hRN hNlog
    exact stage1_core_bound P hs hcoarse hfourier hcount hp hR hRmax S base roots C₀ tt Cl cls members sel U.toLF s hs0
      hsound hord (fun π => (hrep π)) hcounts.1 hcounts.2.1 hcounts.2.2 habs.1 hT2 hS2 hL
  · have hemp : IsEmpty S.Pc := not_nonempty_iff.mp hne
    simpa [Finset.univ_eq_empty] using hnn

end WaveTurbulence.GammaLow.FinalCount.H
