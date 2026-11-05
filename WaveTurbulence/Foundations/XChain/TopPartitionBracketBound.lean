/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopPartitionErrorBounds
public import WaveTurbulence.Foundations.XChain.ForestBracketWeightSum
public import WaveTurbulence.Foundations.XChain.PartitionWeightProduct
/-! The decoration-summed cmattr input error retains external root decay. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem norm_topPartitionError_le_of_bracket_weights {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (c : Ω → (Fin d → ℤ) → ℂ)
    (p Natt : ℕ) (t : ℝ) (n : Fin w → (Fin d → ℤ))
    (b : ℝ) (hL : 1 ≤ L) (hb : (d : ℝ) + 1 ≤ b)
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmain : ∀ (κ : ForestDecoration top d n) (B : P.parts),
      ‖topBlockKernel L γ δ F sig top P p Natt κ B‖ ≤ C * (∏ l ∈ B.1, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b)))
    (herr : ∀ (κ : ForestDecoration top d n) (B : P.parts),
      ‖topBlockCumulant μ sig top c κ B.1 - topBlockKernel L γ δ F sig top P p Natt κ B‖ ≤
        ε * (C * (∏ l ∈ B.1, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b)))) :
    ‖topPartitionError μ L γ δ F sig top P c p Natt t n‖ ≤
      (∏ j, SysAPI.boxVol (top j) p t) *
        (2 ^ P.parts.card * ε * C ^ P.parts.card *
          (2 ^ Fintype.card (GLeaf top) : ℝ) ^ b *
            (∏ j, jbr (latticePoint L (n j))) ^ (-b) *
              (∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-b)) ^ Fintype.card (GLeaf top)) := by
  classical
  let A : ℝ := (∏ j, SysAPI.boxVol (top j) p t) * (2 ^ P.parts.card * ε * C ^ P.parts.card)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (prod_nonneg (fun j _ => SysAPI.boxVol_nonneg (top j) p t))
      (mul_nonneg (mul_nonneg (by positivity) hε) (pow_nonneg hC _))
  have hb0 : 0 ≤ b := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  have hv := summable_lattice_bracket_weight L (2 * b) hL (by linarith)
  have ht := forest_weight_summable top n
    (fun m => jbr (latticePoint L m) ^ (-(2 * b))) hv
  have hweight (κ : ForestDecoration top d n) :
      (∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b)) =
        ∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode)) ^ (-(2 * b)) :=
    (Real.finsetProd_rpow univ _ (fun l _ => (jbr_pos _).le) (-(2 * b))).symm
  have ht' : Summable (fun κ : ForestDecoration top d n =>
      (∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b))) :=
    ht.congr (fun κ => (hweight κ).symm)
  have hs := ht'.mul_left A
  have hintegrand (κ : ForestDecoration top d n) :
      ‖topPartitionErrorIntegrand μ L γ δ F sig top P c p Natt t n κ‖ ≤
        A * (∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b)) := by
    have h := norm_topPartitionErrorIntegrand_le μ L γ δ F sig top P c p Natt t n κ
      (fun B => C * (∏ l ∈ B.1, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b))) hε hε1
      (fun B => mul_nonneg hC (Real.rpow_nonneg (prod_nonneg (fun l _ => (jbr_pos _).le)) _)) (hmain κ) (herr κ)
    have he : (∏ B : P.parts, C * (∏ l ∈ B.1, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b))) =
        C ^ P.parts.card * (∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b)) := by
      exact prod_finpartition_rpow P (fun l => jbr (latticePoint L (κ.1 l.toNode)))
        (fun l _ => (jbr_pos _).le) C (-(2 * b))
    rw [he] at h
    exact h.trans_eq (by dsimp [A]; ring)
  have hnrm : Summable (fun κ : ForestDecoration top d n =>
      ‖topPartitionErrorIntegrand μ L γ δ F sig top P c p Natt t n κ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hintegrand hs
  calc
    ‖topPartitionError μ L γ δ F sig top P c p Natt t n‖ ≤
        ∑' κ : ForestDecoration top d n, ‖topPartitionErrorIntegrand μ L γ δ F sig top P c p Natt t n κ‖ :=
      norm_tsum_le_tsum_norm hnrm
    _ ≤ ∑' κ : ForestDecoration top d n, A * (∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b)) :=
      hnrm.tsum_le_tsum hintegrand hs
    _ = A * ∑' κ : ForestDecoration top d n, (∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode))) ^ (-(2 * b)) := tsum_mul_left
    _ ≤ A * ((2 ^ Fintype.card (GLeaf top) : ℝ) ^ b *
        (∏ j, jbr (latticePoint L (n j))) ^ (-b) *
          (∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-b)) ^ Fintype.card (GLeaf top)) :=
      mul_le_mul_of_nonneg_left (tsum_forest_bracket_weight_le top n L b hL hb) hA
    _ = _ := by dsimp [A]; ring

end WaveTurbulence.Induct
