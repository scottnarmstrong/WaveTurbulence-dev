/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.Kernel

/-! # D6a PROT-PTW: exact integration of one selected time (S Lemma 9.1, one vertex)

The selected branch `v` is the endpoint `ev` of link `j`. In the weighted link integrand the time `t_v` enters only
through the phase `e(β_p t_v)` of link `j`, `β_p = ±ζ_j δ L^{2γ} ⟨x_j, y_j⟩`. Integrating `t_v` over an interval
`(a, b)` gives the difference of the antiderivative at the two endpoints: the same integrand with the link weight
`ψ_j / (2πiβ)` (`selWeight`). This is o82's "the selected reciprocal is retained" (`R = (πcμ)^{-a}M₂^{-a}`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs WaveTurbulence.Links

variable {d : ℕ}

/-- `∫_{(a,b)} e(βx) dx = (e(βb) - e(βa)) / (2πiβ)`. -/
theorem integral_Ioo_e_mul {β : ℝ} (hβ : β ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Ioo a b, WeylSums.e (β * x) =
      (WeylSums.e (β * b) - WeylSums.e (β * a)) / (2 * Real.pi * Complex.I * β) := by
  have hc : (2 * Real.pi * Complex.I * β : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hb : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
    simp [this, hb, Complex.I_ne_zero]
  have he (x : ℝ) : WeylSums.e (β * x) = Complex.exp ((2 * Real.pi * Complex.I * β : ℂ) * x) := by
    unfold WeylSums.e; congr 1; push_cast; ring
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  simp_rw [he]
  exact integral_exp_mul_complex hc

/-! ### The clock and the phase as functions of one branch time -/

variable {LG : LayeredGarden 1} {X : RegChain}

theorem treeClockEquiv_symm_apply (hX : X.DecodesTree LG.garden) (g : GBranch LG.garden.tree → ℝ)
    (i : Fin (X.treeLinks (LG.garden.sig 0)).length) (e : Fin 2) :
    (treeClockEquiv hX).symm g i e = g (treeLinkBranch hX i e) := by
  have h := treeClockEquiv_apply hX ((treeClockEquiv hX).symm g) i e
  rw [MeasurableEquiv.apply_symm_apply] at h
  exact h.symm

theorem treeLinkBranch_eq_iff (hX : X.DecodesTree LG.garden) (i j : Fin (X.treeLinks (LG.garden.sig 0)).length)
    (e ev : Fin 2) : treeLinkBranch hX i e = treeLinkBranch hX j ev ↔ i = j ∧ e = ev := by
  constructor
  · intro h
    have := (treeLinkEquiv hX).injective (show treeLinkEquiv hX (i, e) = treeLinkEquiv hX (j, ev) from h)
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The phase frequency of the selected time on a link array. -/
def selFreq (L γ δ : ℝ) (Q : Fin (X.treeLinks (LG.garden.sig 0)).length → LayerLink d)
    (j : Fin (X.treeLinks (LG.garden.sig 0)).length) (ev : Fin 2) (q : LPair d) : ℝ :=
  (if ev = 0 then 1 else -1) * ((((Q j).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ)) * linkBilinear L q

theorem sourceTemporalPhase_update (hX : X.DecodesTree LG.garden) (L γ δ : ℝ)
    (Q : Fin (X.treeLinks (LG.garden.sig 0)).length → LayerLink d)
    (j : Fin (X.treeLinks (LG.garden.sig 0)).length) (ev : Fin 2)
    (p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ) (g : GBranch LG.garden.tree → ℝ) (x : ℝ) :
    sourceTemporalPhase L γ δ Q p ((treeClockEquiv hX).symm (Function.update g (treeLinkBranch hX j ev) x)) =
      sourceTemporalPhase L γ δ Q p ((treeClockEquiv hX).symm (Function.update g (treeLinkBranch hX j ev) 0)) *
        WeylSums.e (selFreq (X := X) (LG := LG) L γ δ Q j ev (p (j, 0), p (j, 1)) * x) := by
  unfold sourceTemporalPhase
  simp_rw [treeClockEquiv_symm_apply]
  have hfac (i : Fin (X.treeLinks (LG.garden.sig 0)).length) :
      (linkWickFactor (p (i, 0)) (p (i, 1)) : ℂ) * WeylSums.e ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        (Function.update g (treeLinkBranch hX j ev) x (treeLinkBranch hX i 0) -
          Function.update g (treeLinkBranch hX j ev) x (treeLinkBranch hX i 1)) *
          inner ℝ (latticePoint L (p (i, 0))) (latticePoint L (p (i, 1)))) =
      ((linkWickFactor (p (i, 0)) (p (i, 1)) : ℂ) * WeylSums.e ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        (Function.update g (treeLinkBranch hX j ev) 0 (treeLinkBranch hX i 0) -
          Function.update g (treeLinkBranch hX j ev) 0 (treeLinkBranch hX i 1)) *
          inner ℝ (latticePoint L (p (i, 0))) (latticePoint L (p (i, 1))))) *
        (if i = j then WeylSums.e (selFreq (X := X) (LG := LG) L γ δ Q j ev (p (j, 0), p (j, 1)) * x) else 1) := by
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl]
      conv_rhs => rw [mul_assoc, ← WeylSums.e_add]
      congr 2
      unfold selFreq linkBilinear
      have h10 : treeLinkBranch hX i 1 ≠ treeLinkBranch hX i 0 := fun h =>
        absurd ((treeLinkBranch_eq_iff hX i i 1 0).1 h).2 (by decide)
      have h01 : treeLinkBranch hX i 0 ≠ treeLinkBranch hX i 1 := fun h =>
        absurd ((treeLinkBranch_eq_iff hX i i 0 1).1 h).2 (by decide)
      fin_cases ev
      · simp only [Fin.zero_eta, Function.update_self, ite_true, Function.update_of_ne h10]
        ring
      · simp only [Fin.mk_one, Function.update_self, one_ne_zero, ite_false, Function.update_of_ne h01]
        ring
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hij), mul_one]
      rw [Function.update_of_ne (fun h => hij ((treeLinkBranch_eq_iff hX i j 0 ev).1 h).1),
        Function.update_of_ne (fun h => hij ((treeLinkBranch_eq_iff hX i j 1 ev).1 h).1),
        Function.update_of_ne (fun h => hij ((treeLinkBranch_eq_iff hX i j 0 ev).1 h).1),
        Function.update_of_ne (fun h => hij ((treeLinkBranch_eq_iff hX i j 1 ev).1 h).1)]
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

/-! ### The antiderivative weight -/

/-- The selected link weight divided by `2πiβ`. -/
def selWeight (L γ δ : ℝ) (Q : Fin (X.treeLinks (LG.garden.sig 0)).length → LayerLink d)
    (j : Fin (X.treeLinks (LG.garden.sig 0)).length) (ev : Fin 2)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ) :
    Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ :=
  Function.update ψ j (fun q => ψ j q / (2 * Real.pi * Complex.I * selFreq (X := X) (LG := LG) L γ δ Q j ev q))

theorem arrayWeight_selWeight (L γ δ : ℝ) (Q : Fin (X.treeLinks (LG.garden.sig 0)).length → LayerLink d)
    (j : Fin (X.treeLinks (LG.garden.sig 0)).length) (ev : Fin 2)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ)
    (p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ) :
    arrayWeight (selWeight (X := X) (LG := LG) L γ δ Q j ev ψ) p =
      arrayWeight ψ p / (2 * Real.pi * Complex.I * selFreq (X := X) (LG := LG) L γ δ Q j ev (p (j, 0), p (j, 1))) := by
  unfold arrayWeight selWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    Function.update_self]
  rw [Finset.prod_congr rfl (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])]
  ring

/-! ### Exact integration of the selected time in the tree integrand -/

/-- **One selected time integrated exactly**: the integral over `(a, b)` is the difference of the antiderivative
integrand (weight `selWeight`) at the endpoints. Requires the selected link weight to vanish where `⟨x, y⟩ = 0`
(the annular factor `chiD` vanishes there). -/
theorem integral_Ioo_treeIntegrand (hX : X.DecodesTree LG.garden) {α : Type*} [MeasurableSpace α] {L : ℝ}
    (_hL : 0 < L) (γ δ : ℝ) (H : LeafProfiles 1 d) (k : Mom d)
    (F : SpatialMeasure (PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) α)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ) {Bψ : ℝ} (hBψ : 0 ≤ Bψ)
    (hψ : ∀ i q, ‖ψ i q‖ ≤ Bψ) (j : Fin (X.treeLinks (LG.garden.sig 0)).length) (ev : Fin 2)
    (hann : ∀ q, selFreq (X := X) (LG := LG) L γ δ (treeLayerLinks LG hX) j ev q = 0 → ψ j q = 0)
    {Bψ' : ℝ} (hBψ' : 0 ≤ Bψ') (hψ' : ∀ i q, ‖selWeight L γ δ (treeLayerLinks LG hX) j ev ψ i q‖ ≤ Bψ')
    (hs : Summable (fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
      ‖(treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k (fun i j => latticePoint L (p (i, j)))‖))
    (g : GBranch LG.garden.tree → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Ioo a b, treeIntegrand hX L γ δ H k F ψ (Function.update g (treeLinkBranch hX j ev) x) =
      treeIntegrand hX L γ δ H k F (selWeight L γ δ (treeLayerLinks LG hX) j ev ψ)
          (Function.update g (treeLinkBranch hX j ev) b) -
        treeIntegrand hX L γ δ H k F (selWeight L γ δ (treeLayerLinks LG hX) j ev ψ)
          (Function.update g (treeLinkBranch hX j ev) a) := by
  set Q := treeLayerLinks (d := d) LG hX
  set v := treeLinkBranch hX j ev
  let lw := fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
    (treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k (fun i j => latticePoint L (p (i, j)))
  let β := fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
    selFreq (X := X) (LG := LG) L γ δ Q j ev (p (j, 0), p (j, 1))
  let c := fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
    F.value (pairedLattice L p) * arrayWeight ψ p *
      sourceTemporalPhase L γ δ Q p ((treeClockEquiv hX).symm (Function.update g v 0)) * ((gardenCircle LG.garden : ℂ) * lw p)
  have hc (p) : ‖c p‖ ≤ F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length * ‖lw p‖ := by
    have h1 := F.norm_value_le (pairedLattice L p)
    have h2 := norm_arrayWeight_le ψ hBψ hψ p
    have h3 := norm_sourceTemporalPhase_le_one L γ δ Q p ((treeClockEquiv hX).symm (Function.update g v 0))
    simp only [c, norm_mul, Circle.norm_coe, one_mul]
    calc _ ≤ F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length * 1 * ‖lw p‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) F.mass_nonneg) h3
            (norm_nonneg _) (mul_nonneg F.mass_nonneg (pow_nonneg hBψ _))) (norm_nonneg _)
      _ = _ := by ring
  have hcs : Summable (fun p => ‖c p‖) :=
    (hs.mul_left (F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length)).of_nonneg_of_le (fun _ => norm_nonneg _) hc
  have hterm (p) (x : ℝ) : F.value (pairedLattice L p) * arrayWeight ψ p *
      sourceTemporalPhase L γ δ Q p ((treeClockEquiv hX).symm (Function.update g v x)) *
        ((gardenCircle LG.garden : ℂ) * lw p) = c p * WeylSums.e (β p * x) := by
    rw [sourceTemporalPhase_update hX L γ δ Q j ev p g x]
    simp only [c, β]
    ring
  have hterm' (p) (x : ℝ) : F.value (pairedLattice L p) * arrayWeight (selWeight L γ δ Q j ev ψ) p *
      sourceTemporalPhase L γ δ Q p ((treeClockEquiv hX).symm (Function.update g v x)) *
        ((gardenCircle LG.garden : ℂ) * lw p) =
        c p / (2 * Real.pi * Complex.I * β p) * WeylSums.e (β p * x) := by
    rw [sourceTemporalPhase_update hX L γ δ Q j ev p g x, arrayWeight_selWeight]
    simp only [c, β]
    ring
  have hlhs (x : ℝ) : treeIntegrand hX L γ δ H k F ψ (Function.update g v x) = ∑' p, c p * WeylSums.e (β p * x) := by
    unfold treeIntegrand arrayIntegrand
    exact tsum_congr fun p => hterm p x
  have hrhs (x : ℝ) : treeIntegrand hX L γ δ H k F (selWeight L γ δ Q j ev ψ) (Function.update g v x) =
      ∑' p, c p / (2 * Real.pi * Complex.I * β p) * WeylSums.e (β p * x) := by
    unfold treeIntegrand arrayIntegrand
    exact tsum_congr fun p => hterm' p x
  have hint (p) : Integrable (fun x => c p * WeylSums.e (β p * x)) (volume.restrict (Ioo a b)) := by
    refine (integrableOn_const (C := ‖c p‖) (by simp [Real.volume_Ioo])).mono' ?_ ?_
    · exact (continuous_const.mul ((by unfold WeylSums.e; fun_prop :
        Continuous fun x : ℝ => WeylSums.e (β p * x)))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by simp [WeylSums.norm_e]
  have hnorm (p) : (∫ x in Ioo a b, ‖c p * WeylSums.e (β p * x)‖) = ‖c p‖ * (b - a) := by
    simp only [norm_mul, WeylSums.norm_e, mul_one, setIntegral_const, Measure.real, Real.volume_Ioo,
      smul_eq_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
    ring
  have hsum : Summable (fun p => ∫ x in Ioo a b, ‖c p * WeylSums.e (β p * x)‖) := by
    simp_rw [hnorm]; exact hcs.mul_right _
  simp_rw [hlhs, hrhs]
  rw [← (hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq]
  let c' := fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
    c p / (2 * Real.pi * Complex.I * β p)
  have hc' (p) : ‖c' p‖ ≤ F.mass * Bψ' ^ (X.treeLinks (LG.garden.sig 0)).length * ‖lw p‖ := by
    have he := hterm' p 0
    rw [mul_zero, WeylSums.e_zero, mul_one] at he
    change ‖c' p‖ ≤ _
    rw [show c' p = c p / (2 * Real.pi * Complex.I * β p) from rfl, ← he]
    have h1 := F.norm_value_le (pairedLattice L p)
    have h2 := norm_arrayWeight_le _ hBψ' hψ' p
    have h3 := norm_sourceTemporalPhase_le_one L γ δ Q p ((treeClockEquiv hX).symm (Function.update g v 0))
    simp only [norm_mul, Circle.norm_coe, one_mul]
    calc _ ≤ F.mass * Bψ' ^ (X.treeLinks (LG.garden.sig 0)).length * 1 * ‖lw p‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) F.mass_nonneg) h3
            (norm_nonneg _) (mul_nonneg F.mass_nonneg (pow_nonneg hBψ' _))) (norm_nonneg _)
      _ = _ := by ring
  have hcs' : Summable (fun p => ‖c' p‖) :=
    (hs.mul_left (F.mass * Bψ' ^ (X.treeLinks (LG.garden.sig 0)).length)).of_nonneg_of_le
      (fun _ => norm_nonneg _) hc'
  have hsx (x : ℝ) : Summable (fun p => c' p * WeylSums.e (β p * x)) :=
    Summable.of_norm_bounded hcs' fun p => by simp [WeylSums.norm_e]
  change (∑' p, ∫ x in Ioo a b, c p * WeylSums.e (β p * x)) =
    (∑' p, c' p * WeylSums.e (β p * b)) - ∑' p, c' p * WeylSums.e (β p * a)
  rw [← (hsx b).tsum_sub (hsx a)]
  apply tsum_congr
  intro p
  by_cases hβ : β p = 0
  · have hc0 : c p = 0 := by
      have hw : arrayWeight ψ p = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (hann _ hβ)
      simp only [c, hw, mul_zero, zero_mul]
    simp only [c', hc0, zero_div, zero_mul, sub_self, integral_zero]
  · rw [integral_const_mul, integral_Ioo_e_mul hβ hab]
    simp only [c']
    ring

end WaveTurbulence.Flower.ProtPtw
