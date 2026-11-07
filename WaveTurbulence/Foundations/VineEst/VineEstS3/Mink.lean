/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.MinkAux

/-! # Countable Minkowski for restriction norms of order zero

If `F = ∑_j f_j` pointwise on `B × K` (`B ⊆ Q_q` a unit cell, `K` countable) then
`‖F‖_{𝔛^{θ,0,0}(B × K)} ≤ C_θ ∑_j ‖f_j‖_{𝔛^{θ,0,0}(B × K)}`, with `C_θ` the cutoff multiplier constant of the unit cell
cutoff.  The extensions are summed after multiplication by the cutoff and replacement by the continuous
representatives (so that time masses are finite); the sum agrees with `F` almost everywhere on `B`, and the
exceptional null set is repaired by redefinition on `B × K`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Mink
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal

variable {r : ℕ} {V : Type*}

theorem exists_ext_of_lt {θ : ℝ} {B : Set (Fin r → ℝ)} {K : Set V} {f : (Fin r → ℝ) → V → ℂ}
    {c : ℝ≥0∞} (h : XNorm00Restr θ B K f < c) :
    ∃ G : (Fin r → ℝ) → V → ℂ, (∀ t ∈ B, ∀ v ∈ K, G t v = f t v) ∧ XNorm00 θ G < c := by
  unfold XNorm00Restr at h
  obtain ⟨G, hG⟩ := iInf_lt_iff.1 h
  obtain ⟨hag, hn⟩ := iInf_lt_iff.1 hG
  exact ⟨G, hag, hn⟩


/-- **Countable Minkowski for order-zero restriction norms.** -/
theorem XNorm00Restr_tsum_le {ι : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin r → ℝ) {B : Set (Fin r → ℝ)} (hB : B ⊆ cell q) {K : Set V}
    (hK : K.Countable) (f : ι → (Fin r → ℝ) → V → ℂ) (F : (Fin r → ℝ) → V → ℂ)
    (hsum : ∀ t ∈ B, ∀ v ∈ K, HasSum (fun j => f j t v) (F t v)) :
    XNorm00Restr θ B K F ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) * ∑' j, XNorm00Restr θ B K (f j) := by
  classical
  haveI : Countable K := hK.to_subtype
  set cc := cutoffMultiplierConstant θ (cutQ q) with hcc_def
  have hcc : cc ≠ ⊤ := (cutoffMultiplierConstant_lt_top θ (cutQ_hasCompactSupport q) (cutQ_contDiff q)).ne
  have hcc1 : cc + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hcc, ENNReal.one_ne_top⟩
  have hcc1' : cc + 1 ≠ 0 := by simp
  set a : ι → ℝ≥0∞ := fun j => XNorm00Restr θ B K (f j) with ha
  by_cases hS : ∑' j, a j = ⊤
  · rw [hS, ENNReal.mul_top hcc1']; exact le_top
  have hfin : ∀ j, a j ≠ ⊤ := fun j => ENNReal.ne_top_of_tsum_ne_top hS j
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable
    (show ((ε : ℝ≥0∞) / (cc + 1)) ≠ 0 from (ENNReal.div_pos (by exact_mod_cast hε.ne') hcc1).ne') ι
  have hG : ∀ j, ∃ G : (Fin r → ℝ) → V → ℂ, (∀ t ∈ B, ∀ v ∈ K, G t v = f j t v) ∧
      XNorm00 θ G < a j + ε' j := fun j =>
    exists_ext_of_lt (ENNReal.lt_add_right (hfin j) (by simpa using (hε'pos j).ne'))
  choose G hGag hGlt using hG
  have hGtop : ∀ j, XNorm00 θ (G j) < ⊤ := fun j =>
    (hGlt j).trans (ENNReal.add_lt_top.2 ⟨(hfin j).lt_top, ENNReal.coe_lt_top⟩)
  have hslice : ∀ j v, timeFourierNorm θ (fun u => G j u v) < ⊤ := fun j v =>
    (timeFourierNorm_slice_le_mixedFourierNorm00 θ (G j) v).trans_lt
      (by rw [← NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]; exact hGtop j)
  -- the families on the subtype
  set F' : ι → (Fin r → ℝ) → K → ℂ := fun j t v => cutQ q t * Regref.rep (fun u => G j u v.1) t with hF'
  have hκc : Continuous (cutQ q) := (cutQ_contDiff q).continuous
  have hrc : ∀ j v, Continuous fun t => Regref.rep (fun u => G j u v) t := fun j v =>
    (Regref.rep_props hθ (hslice j v)).1
  have hF'c : ∀ j (v : K), Continuous fun t => F' j t v := fun j v => hκc.mul (hrc j v.1)
  have hF'm : ∀ j (v : K), Measurable fun t => F' j t v := fun j v => (hF'c j v).measurable
  have hF'i : ∀ j (v : K), Integrable (fun t => F' j t v) volume := fun j v =>
    (hF'c j v).integrable_of_hasCompactSupport ((cutQ_hasCompactSupport q).mul_right)
  set cκ : ℝ≥0∞ := ∫⁻ t, ‖cutQ q t‖ₑ with hcκ
  have hcκtop : cκ ≠ ⊤ := (cutQ_integrable q).hasFiniteIntegral.ne
  have hmass : ∀ j (v : K), ∫⁻ t, ‖F' j t v‖ₑ ≤ cκ * XNorm00 θ (G j) := by
    intro j v
    calc ∫⁻ t, ‖F' j t v‖ₑ ≤ ∫⁻ t, ‖cutQ q t‖ₑ * XNorm00 θ (G j) := by
          refine lintegral_mono fun t => ?_
          simp only [hF', enorm_mul]
          refine mul_le_mul_right ?_ _
          refine (enorm_rep_le hθ (hslice j v.1) t).trans ?_
          rw [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
          exact timeFourierNorm_slice_le_mixedFourierNorm00 θ (G j) v.1
      _ = cκ * XNorm00 θ (G j) := lintegral_mul_const' _ _ (hGtop j).ne
  have hmassS : ∀ v : K, ∑' j, ∫⁻ t, ‖F' j t v‖ₑ < ⊤ := by
    intro v
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => hmass j v) ?_
    rw [ENNReal.tsum_mul_left]
    refine ENNReal.mul_lt_top hcκtop.lt_top ?_
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => (hGlt j).le) ?_
    rw [ENNReal.tsum_add]
    exact ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hS,
      hε'sum.trans (ENNReal.div_lt_top ENNReal.coe_ne_top hcc1')⟩
  -- the cutoff estimate for each family member
  have hX : ∀ j, XNorm00 θ (F' j) ≤ cc * XNorm00 θ (G j) := by
    intro j
    set G' : (Fin r → ℝ) → K → ℂ := fun t v => G j t v.1 with hG'
    have hG'le : XNorm00 θ G' ≤ XNorm00 θ (G j) := XNorm00_comp_le θ (G j) (fun v : K => v.1)
    have hG'top : mixedFourierNorm00 θ G' < ⊤ := by
      rw [← NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]; exact hG'le.trans_lt (hGtop j)
    have hrep := Layered.mixedFourierNorm00_rep_eq hθ hG'top
    have hF'eq : F' j = fun t v => (fun t (v : K) => Regref.rep (fun u => G' u v) t) t v * cutQ q t := by
      funext t v; simp only [hF', hG', mul_comm]
    rw [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00, hF'eq]
    refine (mixedFourierNorm00_mul_cutoff_le θ (hrep ▸ hG'top) (cutQ_hasCompactSupport q)
      (cutQ_contDiff q)).trans ?_
    rw [hrep, ← NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
    exact mul_le_mul_right hG'le _
  have hMink := SumintSigned.XNorm00_count_integral_le θ F' hF'm hF'i hmassS
  set Gs : (Fin r → ℝ) → K → ℂ := fun t v => ∫ j, F' j t v ∂Measure.count with hGs
  set f₂ : (Fin r → ℝ) → K → ℂ := fun t v => if t ∈ B then F t v.1 else Gs t v with hf₂
  have hf₂ag : ∀ t ∈ B, ∀ (v : V) (hv : v ∈ K), f₂ t ⟨v, hv⟩ = F t v := by
    intro t ht v hv
    simp only [hf₂, ht, if_true]
  have hae : ∀ v : K, ∀ᵐ t, f₂ t v = Gs t v := by
    intro v
    have h1 : ∀ᵐ t, ∀ j, Regref.rep (fun u => G j u v.1) t = G j t v.1 :=
      ae_all_iff.2 fun j => (Regref.rep_props hθ (hslice j v.1)).2.1
    filter_upwards [h1] with t ht
    by_cases htB : t ∈ B
    · simp only [hf₂, htB, if_true]
      have hF'eq : ∀ j, F' j t v = f j t v.1 := by
        intro j
        simp only [hF', ht j, cutQ_eq_one (hB htB), one_mul]
        exact hGag j t htB v.1 v.2
      have hsm := hsum t htB v.1 v.2
      have hnorm : Summable fun j => ‖F' j t v‖ := by
        simp only [hF'eq]
        exact summable_norm_iff.2 hsm.summable
      simp only [hGs]
      rw [SumintSigned.count_integral_eq_tsum _ hnorm]
      simp only [hF'eq]
      exact hsm.tsum_eq.symm
    · simp only [hf₂, htB, if_false]
  have hch := XNorm00_congr_ae θ hae
  have hres := SumintSigned.XNorm00Restr_le_family_extension θ B K K (fun _ h => h) F f₂ hf₂ag
  refine hres.trans ?_
  rw [hch]
  refine hMink.trans ?_
  calc ∑' j, XNorm00 θ (F' j) ≤ ∑' j, cc * (a j + ε' j) :=
        ENNReal.tsum_le_tsum fun j => (hX j).trans (mul_le_mul_right (hGlt j).le _)
    _ = cc * (∑' j, a j + ∑' j, (ε' j : ℝ≥0∞)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ ≤ cc * (∑' j, a j + (ε : ℝ≥0∞) / (cc + 1)) :=
        mul_le_mul_right (add_le_add le_rfl hε'sum.le) _
    _ = cc * ∑' j, a j + cc * ((ε : ℝ≥0∞) / (cc + 1)) := mul_add _ _ _
    _ ≤ (cc + 1) * ∑' j, a j + ε := by
        refine add_le_add (mul_le_mul_left le_self_add _) ?_
        calc cc * ((ε : ℝ≥0∞) / (cc + 1)) ≤ (cc + 1) * ((ε : ℝ≥0∞) / (cc + 1)) :=
              mul_le_mul_left le_self_add _
          _ = ε := ENNReal.mul_div_cancel hcc1' hcc1

end WaveTurbulence.VineEstS3.Mink
