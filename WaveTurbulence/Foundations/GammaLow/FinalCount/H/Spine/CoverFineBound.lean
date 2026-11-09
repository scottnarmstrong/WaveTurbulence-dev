/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoverFineBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.CoverBudget
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSplicedBounds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedCoverChoiceScaleBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.CoverFineBound`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 The counting cover assembled: TARGET finalsbest2 (L2078) for the spliced kernel of an actual
choice datum, from `ladderl1old` and `finalcount1` (conditional helper, RULINGS R7). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine.Cover
open WaveTurbulence.Induct
open WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Set Finset
open scoped Classical

theorem fine_spliced_of_subpro_choices (P : WTParams)
    (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    (hL : 2 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁) (hδ1 : P.δ ≤ 1)
    (hcap : 2 * P.L⁻¹ ≤ P.L ^ (-P.γ + P.η)) (hb1 : P.L ^ (-P.γ + P.η) ≤ 1)
    (ha : P.δ ^ (5 * P.ν) ≤ P.η ^ 6)
    (hb : Real.log (Real.log P.L / Real.log 2 + 2) ≤ P.η ^ 6 * Real.log P.L)
    (hsmall : Real.log P.C₁ + Real.log (((3 ^ 16 * 17 : ℕ) : ℝ)) + 5 * P.ν * Real.log P.δ ≤ 0)
    {p R : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (G : Garden (2 * R)) (hplain : G.IsPlain) (hirred : G.Irreducible)
    (hbal : IsBalancedSig G.sig) (hn : 1 ≤ G.order) (hnmax : G.order ≤ P.N (p + 1) ^ 4)
    (D : SplicedKernelData G P.d) (hD : SplicedAmplitudeBounds G D) (hlayer : ∀ v, D.layer v ≤ p)
    (hM : G.molecule.IsMolecule) (hconn : G.molecule.IsConnected)
    (hatoms : G.molecule.atoms.card = G.order) (hbonds : G.molecule.bonds.card + R = 2 * G.order)
    (Cs : Src.SubproChoices Src.γL G) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hS : SubproConclusions G D Cs P.L P.γ P.η base roots) :
    ‖splicedKernel G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) *
          P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) := by
  have hL1 : 1 < P.L := by linarith
  have hL0 : 0 < P.L := by linarith
  have hC₁0 : 0 < P.C₁ := by linarith
  have hfin := finite_coverIndex G hM D Cs hL0 P.γ P.η hb1 base roots
  letI : Fintype (CoverIndex G hM D Cs P.L P.γ P.η base roots) := Fintype.ofFinite _
  have hcover : ∀ z : GenDecoration G P.d roots 0,
      splicedMomentumAmplitude G D P.L P.γ P.η base z.1 ≠ 0 →
        ∃ j : CoverIndex G hM D Cs P.L P.γ P.η base roots,
          j.choice.Admissible P.L P.γ P.η base (bondIndex G z.1) := by
    intro z hz
    obtain ⟨t, s, hs⟩ := exists_cover_choice_of_subpro_choices G hplain hM D hD Cs hL P.γ P.η
      hcap base roots hS z hz
    exact ⟨⟨⟨t, s⟩, z, hz, hs⟩, hs⟩
  have hbud := norm_splicedKernel_le_choiceScale_budget P hfourier hcount hL1 hδ hC₁ hp hR hRmax
    G hplain hirred hbal hn hnmax D hD hlayer (fun j => j.choice)
    (fun j => hS.hinges) (fun j => coverIndex_geometry_of_subpro_choices G hM hconn hatoms hbonds
      D Cs P.γ P.η base roots hS j) base roots hcover
    (((3 ^ 16 * 17 : ℕ) : ℝ)) (Real.log P.L / Real.log 2 + 2) (by positivity)
    (by have : 0 ≤ Real.log P.L / Real.log 2 :=
          div_nonneg (Real.log_nonneg hL1.le) (Real.log_nonneg (by norm_num))
        linarith) hδ1 ha hb hsmall
  have hw := coverIndex_weight_le_one G hM D Cs hL1.le P.γ P.η hb1 base roots
    (((3 ^ 16 * 17 : ℕ) : ℝ)) le_rfl
  have hpos : 0 ≤ P.C₁ * Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ) +
        (-P.η ^ 6 * (G.molecule.rho + D.hinges.card) -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L) := by positivity
  rw [← exp_form_eq_fine G P hL0 hC₁0 hδ _]
  refine hbud.trans ?_
  calc _ ≤ (P.C₁ * Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ) +
        (-P.η ^ 6 * (G.molecule.rho + D.hinges.card) -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L)) * 1 :=
        mul_le_mul_of_nonneg_left hw hpos
    _ = _ := mul_one _

end WaveTurbulence.GammaLow.FinalCount.H
