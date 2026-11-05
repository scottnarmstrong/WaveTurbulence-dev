/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeLeafFrequencyBudget
public import WaveTurbulence.Foundations.RegAsymp.TreeRootPairedProfile

/-! # Actual tree modulation normalizes scalar NT/Wick profiles by one leaf moment -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh IncohInst WithLp
open scoped ENNReal

/-- The two modulation arrays are computed from the original augmented tree input rows. -/
def treeLeafModulations {d : ℕ} {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (α : Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ) :
    (Fin (X.treeLinks (G.sig 0)).length → Mom d) × (Fin (X.treeLinks (G.sig 0)).length → Mom d) :=
  ((fun j => treeLeafFrequency (treeCarrier hX).withRootInput (fun a => toLp 2 (α a)) (some (j,0))),
    (fun j => treeLeafFrequency (treeCarrier hX).withRootInput (fun a => toLp 2 (α a)) (some (j,1))))

theorem continuous_treeLeafModulations {d : ℕ} {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    Continuous (treeLeafModulations (d := d) hX) := by
  unfold treeLeafModulations treeLeafFrequency
  fun_prop

/-- The scalar normalization is independent of root position and of its partition center. -/
def treeLeafModulationWeight {d m : ℕ} (α : Fin m → Fin d → ℝ) : ℝ :=
  1+∑ a, ‖(toLp 2 (α a):Mom d)‖

theorem treeLeafModulationWeight_pos {d m : ℕ} (α : Fin m → Fin d → ℝ) :
    0 < treeLeafModulationWeight α := by unfold treeLeafModulationWeight; positivity

theorem continuous_treeLeafModulationWeight {d m : ℕ} :
    Continuous (treeLeafModulationWeight (d := d) (m := m)) := by
  unfold treeLeafModulationWeight
  fun_prop

/-- The original scalar profile divided by the single moment already placed in the root amplitude. -/
def treeNormalizedScalar {d : ℕ} {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (R : (ℝ × ℝ) → (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ) → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (lam : ℝ × ℝ) (u : SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) : ℂ :=
  R lam (treeLeafModulations hX u.2).1 (treeLeafModulations hX u.2).2 u.1.2.val /
    (treeLeafModulationWeight u.2:ℂ)

/-- The actual polynomial row loss pays every scalar modulation uniformly in the selected cells. -/
theorem treeNormalizedScalar_norm_le {d : ℕ} {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (R : (ℝ × ℝ) → (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ) → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (lam : ℝ × ℝ)
    (hb : ∀ z β γ, ‖R lam β γ z‖ ≤ P*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ j‖)))*E)
    (u : SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) :
    ‖treeNormalizedScalar hX R S lam u‖ ≤ P*treeSpectralFrequencyLoss X (G.sig 0)*E := by
  rw [treeNormalizedScalar, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (treeLeafModulationWeight_pos u.2).le]
  apply (div_le_iff₀ (treeLeafModulationWeight_pos u.2)).mpr
  apply (hb _ _ _).trans
  have hh := tree_leaf_modulation_weight_le hX u.2
  change 1+((∑ j, ‖(treeLeafModulations hX u.2).1 j‖)+
      (∑ j, ‖(treeLeafModulations hX u.2).2 j‖)) ≤
    treeSpectralFrequencyLoss X (G.sig 0)*treeLeafModulationWeight u.2 at hh
  calc
    _ ≤ P*(treeSpectralFrequencyLoss X (G.sig 0)*treeLeafModulationWeight u.2)*E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hP) hE
    _ = _ := by ring

/-- Strong measurability includes every counted center and original time/leaf frequency. -/
theorem stronglyMeasurable_treeNormalizedScalar {d : ℕ} {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (R : (ℝ × ℝ) → (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ) → ℂ)
    (hR : ∀ z, StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin (X.treeLinks (G.sig 0)).length → Mom d) × (Fin (X.treeLinks (G.sig 0)).length → Mom d)) =>
        R p.1 p.2.1 p.2.2 z))
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (Function.uncurry (treeNormalizedScalar hX R S)) := by
  have hm : Measurable (fun p : SourceCellIndex S ×
      ((ℝ × ℝ) × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) =>
      R p.2.1 (treeLeafModulations hX p.2.2).1 (treeLeafModulations hX p.2.2).2 p.1.2.val /
        (treeLeafModulationWeight p.2.2:ℂ)) := by
    apply measurable_from_prod_countable_right
    intro cell
    have hmap : Measurable (fun p : (ℝ × ℝ) × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ) =>
        (p.1,treeLeafModulations hX p.2)) :=
      measurable_fst.prodMk ((continuous_treeLeafModulations hX).measurable.comp measurable_snd)
    have hscalar := (hR cell.2.val).comp_measurable hmap
    exact hscalar.measurable.div (Complex.continuous_ofReal.comp
      (continuous_treeLeafModulationWeight.comp continuous_snd)).measurable
  have hp : Measurable (fun p : (ℝ × ℝ) ×
      (SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) => (p.2.1,(p.1,p.2.2))) :=
    measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)
  exact (hm.comp hp).stronglyMeasurable

end WaveTurbulence.RegAsymp
