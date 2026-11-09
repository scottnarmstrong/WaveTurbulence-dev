/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1PieceBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1Interface
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.Stage1PieceBound`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 TARGET (finalproof2), L2224-L2227, for one Stage 1 piece: the redvine representation, the
coarse spliced estimate (finalsbest1, S3), the fine spliced estimate (finalsbest2, proved here from
ladderl1old and finalcount1 through the counting cover) and their interpolation. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset
open scoped Classical

/-- TARGET (finalproof2), L2224-L2227, for the integral conjunct of `Represents` alone (R23 (2)): the bound of
a piece value from its spliced-kernel average. The flower pieces (whose values are not `LeafFamily` values)
use this directly. The prefactor carries `C_1^{n_sb}` (R24 D3). -/
theorem stage1_piece_bound_int (P : WTParams) (hs : PieceSmall P)
    (hcoarse : CoarseSplicedAt P) (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (π : Stage1Piece P R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hπ : π.Sound p base roots) (hnsb : π.Gsb.order ≤ n) (val : ℂ)
    (s : ℝ) (hs0 : 0 < s) (hval : π.RepresentsInt n tt base roots s val) :
    ‖val‖ ≤ s * (P.C₂ * (P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
      P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
      P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) := by
  obtain ⟨Ξ, _, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwbound, hD⟩ := hval
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  set M : ℝ := P.C₂ * Real.exp ((π.Gsb.order : ℝ) * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
        (-40 * P.ν * P.η * (π.gsb : ℝ) -
          P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * Real.log P.L) with hM
  have hKle : ∀ ξ, ‖splicedKernel π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots‖ ≤ M := by
    intro ξ
    set D := π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ) with hDdef
    have hlayer : ∀ v, D.layer v ≤ p := hπ.layer_le
    have hconc : SubproConclusions π.Gsb D π.Cs P.L P.γ P.η base roots :=
      ⟨hπ.structural, rfl, fun z he hg => hπ.support z he hg, hπ.hingeOutsideFirst,
        hπ.tripleDesignated, hπ.hingeNoLoop⟩
    have hprem : SplicedSourcePremises P π.Gsb D base roots :=
      ⟨hπ.molecule, hπ.connected, hπ.atom_count, hπ.bond_count,
        ⟨π.Cs, hπ.structural, rfl, fun z he hg => hπ.support z he hg⟩⟩
    have hc := hcoarse p hp R hR hRmax π.Gsb hπ.plain hπ.irreducible hπ.balanced hπ.order_pos
      hπ.order_le D (hD ξ) hlayer π.ladders base roots hprem
    have hf := fine_spliced_of_subpro_choices P hfourier hcount hs.L_ge hs.delta_pos hs.c1_ge
      hs.delta_le hs.cap hs.cap_le hs.delta_exp hs.scale_log hs.count_const hp hR hRmax π.Gsb
      hπ.plain hπ.irreducible hπ.balanced hπ.order_pos hπ.order_le D (hD ξ) hlayer
      hπ.molecule hπ.connected hπ.atom_count hπ.bond_count π.Cs base roots hconc
    have hν0 : 0 ≤ P.ν := hs.nu_pos.le
    have := spliced_scale_interpolation (z := splicedKernel π.Gsb D P.L P.γ P.η P.δ base roots)
      (C := P.C₁) (H := P.C₂) (δ := P.δ) (L := P.L) (η := P.η) (ν := P.ν) (d := (P.d : ℝ))
      (ρ := (π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) (g := (π.gsb : ℝ)) (R := (R : ℝ))
      π.Gsb.order (by linarith [hs.c1_ge]) (by linarith [hs.c1_ge, hs.c1_le_c2]) hs.c1_le_c2
      hs.delta_pos hs.delta_le hL1 hν0 hs.nu_small hs.cost (by positivity) (by exact_mod_cast hR)
      (by simpa [Stage1PieceD.gsb, hDdef, Stage1Piece.data] using hc)
      (by simpa [hDdef, Stage1Piece.data] using hf)
    simpa [hM] using this
  have hM0 : 0 ≤ M := by
    rw [hM]; exact mul_nonneg (by linarith [hs.c1_ge, hs.c1_le_c2]) (Real.exp_pos _).le
  have hnorm : ‖val‖ ≤ (∫ ξ, ‖w ξ‖ ∂μ) * M := by
    rw [hv]
    have h := norm_integral_le_of_norm_le (hwint.mul_const M)
      (Filter.Eventually.of_forall (fun ξ => by
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hKle ξ) (norm_nonneg _))))
    simpa only [integral_mul_const] using h
  have hW0 : 0 ≤ ∫ ξ, ‖w ξ‖ ∂μ := integral_nonneg fun ξ => norm_nonneg _
  have hW1 : 0 ≤ (∫ ξ, ‖w ξ‖ ∂μ) / s := div_nonneg hW0 hs0.le
  have hwb : (∫ ξ, ‖w ξ‖ ∂μ) / s ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) := by
    rw [div_le_iff₀ hs0]; exact hwbound
  have hcls := class_piece_bound (C := P.C₁) (δ := P.δ) (L := P.L) (η := P.η) (ν := P.ν)
    (n := n) (nsb := π.Gsb.order) (R := R) (m := π.Gsb.order + 2 * R) (W := (∫ ξ, ‖w ξ‖ ∂μ) / s) (X := M) (H := P.C₂)
    (gsk := (π.gsk : ℝ)) (bsk := (π.bsk : ℝ)) (qsk := (π.Cs.hinges.card : ℝ))
    (gsb := (π.gsb : ℝ)) (ρsb := (π.Gsb.molecule.rho : ℝ))
    hs.c1_ge hs.delta_pos hs.delta_le hL1 hs.nu_pos (by linarith [hs.nu_small]) hs.nu_eta
    hs.eta_pos hs.eta_le hnsb (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith [hs.c1_ge, hs.c1_le_c2]) hW1 hM0
    hwb (by rw [hM])
  calc ‖val‖ ≤ (∫ ξ, ‖w ξ‖ ∂μ) * M := hnorm
    _ = s * (((∫ ξ, ‖w ξ‖ ∂μ) / s) * M) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hcls hs0.le

/-- TARGET (finalproof2), L2224-L2227, for one Stage 1 piece: `stage1_piece_bound_int` for the integral
conjunct of `Represents`. -/
theorem stage1_piece_bound (P : WTParams) (hs : PieceSmall P)
    (hcoarse : CoarseSplicedAt P) (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (π : Stage1Piece P R) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hπ : π.Sound p base roots) (hnsb : π.Gsb.order ≤ n) (val : ℂ)
    (tt : Fin (2 * R) → ℝ) (members : Finset (LayeredGarden (2 * R)))
    (sel : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (F : LeafFamily P (2 * R))
    (s : ℝ) (hs0 : 0 < s) (hval : π.Represents n tt base roots members sel F s val) :
    ‖val‖ ≤ s * (P.C₂ * (P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
      P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
      P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) :=
  stage1_piece_bound_int P hs hcoarse hfourier hcount hp hR hRmax π tt base roots hπ hnsb val s hs0 hval.2

end WaveTurbulence.GammaLow.FinalCount.H
