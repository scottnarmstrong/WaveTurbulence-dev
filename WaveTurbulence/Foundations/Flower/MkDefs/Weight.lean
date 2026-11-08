/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Bounds
public import WaveTurbulence.Foundations.Flower.MkDefs.CardBound

/-! # A1 MK-DEFS: the `markedWeight` bound, scaling, and the `Stage1Carries` layer bound. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

namespace WaveTurbulence.Flower.MkDefs

variable {w : ℕ}

theorem selFactor_nonneg {LG : LayeredGarden w} (v : Fin w → Option (GBranch LG.garden.tree))
    (Rs : Fin w → ℝ) : 0 ≤ ∏ j : Fin w, (if (v j).isSome then chiDConst * |Rs j|⁻¹ else 1) := by
  refine Finset.prod_nonneg fun j _ => ?_
  split_ifs
  · exact mul_nonneg chiDConst_nonneg (by positivity)
  · norm_num

/-- **`markedWeight` bound.** If the profiles are pointwise bounded by `b` at layers `≤ p` and the garden's layers
are at most `p`, then `|markedWeight| ≤ b ^ #(non-cap input leaves) · ∏_j (selected ? Cχ |R_j|⁻¹ : 1)`; here
`#(non-cap input leaves) ≤ #(input leaves) ≤ #nodes`. -/
theorem abs_markedWeight_le {d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (p : ℕ) (L : ℝ)
    (Rf : Fin w → Option ℝ) (σ : Fin w → Option ℕ) (v : Fin w → Option (GBranch LG.garden.tree))
    (Rs : Fin w → ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (dag : Option (Fin w → Fin 3 → Mom d))
    (b : ℝ) (hb : 0 ≤ b) (hh : ∀ q ≤ p, ∀ j j' x, |h q j j' x| ≤ b) (hlay : ∀ a, LG.layer a ≤ p)
    (k : GNode LG.garden.tree → Mom d) :
    |markedWeight LG J p L Rf σ v Rs h dag k| ≤
      b ^ (nonCapLeaves LG J).card * ∏ j : Fin w, (if (v j).isSome then chiDConst * |Rs j|⁻¹ else 1) := by
  unfold markedWeight
  have hF := Fam.abs_frontierW_le LG p Rf k
  have hS := abs_stemFilterCap_le_one LG J L σ k
  have hW := abs_selWeightCap_le LG J v Rs k
  have hP := abs_leafProdCap_le LG J h p b hb hh hlay k
  have hD : |dag.elim (1 : ℝ) (fun c => sibWeightCap LG J c k)| ≤ 1 := by
    cases dag with
    | none => simp
    | some c => exact abs_sibWeightCap_le_one LG J c k
  have hsel0 : 0 ≤ ∏ j : Fin w, (if (v j).isSome then chiDConst * |Rs j|⁻¹ else 1) := selFactor_nonneg v Rs
  rw [abs_mul, abs_mul, abs_mul, abs_mul]
  have hb0 : 0 ≤ b ^ (nonCapLeaves LG J).card := by positivity
  calc |Typed.frontierW LG p Rf k| * |stemFilterCap LG J L σ k| * |selWeightCap LG J v Rs k| *
        |leafProdCap LG J h k| * |dag.elim (1 : ℝ) (fun c => sibWeightCap LG J c k)|
      ≤ 1 * 1 * (∏ j : Fin w, (if (v j).isSome then chiDConst * |Rs j|⁻¹ else 1)) *
        b ^ (nonCapLeaves LG J).card * 1 := by
        gcongr
    _ = _ := by ring

/-- Scaling of the marked weight in the profile: `markedWeight h = b ^ n · markedWeight (h / b)`. -/
theorem markedWeight_scale {d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (p : ℕ) (L : ℝ)
    (Rf : Fin w → Option ℝ) (σ : Fin w → Option ℕ) (v : Fin w → Option (GBranch LG.garden.tree))
    (Rs : Fin w → ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (dag : Option (Fin w → Fin 3 → Mom d))
    (b : ℝ) (hb : b ≠ 0) (k : GNode LG.garden.tree → Mom d) :
    markedWeight LG J p L Rf σ v Rs h dag k =
      b ^ (nonCapLeaves LG J).card *
        markedWeight LG J p L Rf σ v Rs (fun q j j' x => h q j j' x / b) dag k := by
  unfold markedWeight
  rw [leafProdCap_scale LG J h b hb k]
  ring

/-- Layers of a `Stage1Carries` garden are at most `p`. -/
theorem layer_le_of_stage1Carries {P : WTParams} {p N : ℕ} {LG : LayeredGarden w}
    (h : Stage1Carries P p N LG) (a : GNode LG.garden.tree) : LG.layer a ≤ p :=
  Canon.layer_le_of_isCanonGC h.1 a

/-- The profile bound of `MarkedComponentBoundAt`'s hypothesis (`SNormR ≤ b`) gives the pointwise bound. -/
theorem abs_le_of_snorm_hyp {P : WTParams} {p : ℕ} {R : ℕ} (b : ℝ) (hb : 1 ≤ b)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (hh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) :
    ∀ q ≤ p, ∀ j j' x, |h q j j' x| ≤ b :=
  fun q hq j j' x => abs_le_of_SNormR_le _ _ _ b (by linarith) (hh q hq j j') x

end WaveTurbulence.Flower.MkDefs
