/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsFold.Interp
public import WaveTurbulence.Foundations.Regref.FourierAE
public import WaveTurbulence.Foundations.Sumint.TimeBridge
public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs

/-! # D1b-F FOLD 7: `ProtDefs.FoldInterpolation` (o82 Lemmas 17.1–17.2)

For an extension `g` of `f` (continuous on the closed triangle) with finite `𝔛^{1/4}` norm, the continuous
representative `H = (𝓕𝓕 g)(-·)` (main `Regref.timeFourier_continuous_representative`) equals `f` on the triangle
(`triD ⊆ closure (interior triD)`, a.e. equality and continuity), `E = foldExt H` is an extension of `f` with
`|E| ≤ A |foldCut|` and `‖E‖_{𝔛^{1/8}} ≤ extC ‖g‖_{𝔛^{1/4}}`, and `interp_opt` gives
`‖E‖_{𝔛^η} ≤ C A^τ ‖g‖^{1-τ}`. The infimum over `g` commutes with the continuous monotone `x ↦ c x^{1-τ}`;
translation by `q` reduces the general triangle to `q = 0`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set WaveTurbulence.Fourier
open scoped ENNReal Real

namespace WaveTurbulence.Flower.ProtOpsFold

/-! ## The triangle -/

theorem isClosed_triD : IsClosed triD := by
  simp only [triD, ofPred_and]
  refine (isClosed_le continuous_const (continuous_apply 1)).inter
    ((isClosed_le (continuous_apply 1) (continuous_apply 0)).inter
      (isClosed_le (continuous_apply 0) continuous_const))

theorem isCompact_triD : IsCompact triD := by
  refine (isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset
    isClosed_triD ?_
  intro x hx
  rw [Set.mem_univ_pi]
  obtain ⟨h1, h2, h3⟩ := hx
  exact Fin.forall_fin_two.mpr ⟨⟨by linarith, h3⟩, ⟨h1, by linarith⟩⟩

theorem convex_triD : Convex ℝ triD := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x1, x2, x3⟩ := hx
  obtain ⟨y1, y2, y3⟩ := hy
  simp only [triD, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨by positivity, by nlinarith, by nlinarith⟩

theorem interior_triD_nonempty : (interior triD).Nonempty := by
  refine ⟨![2 / 3, 1 / 3], ?_⟩
  have hsub : {x : Fin 2 → ℝ | 0 < x 1 ∧ x 1 < x 0 ∧ x 0 < 1} ⊆ triD :=
    fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩
  have hU : IsOpen {x : Fin 2 → ℝ | 0 < x 1 ∧ x 1 < x 0 ∧ x 0 < 1} := by
    simp only [ofPred_and]
    exact (isOpen_lt continuous_const (continuous_apply 1)).inter
      ((isOpen_lt (continuous_apply 1) (continuous_apply 0)).inter
        (isOpen_lt (continuous_apply 0) continuous_const))
  refine interior_maximal hsub hU ?_
  simp only [mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem triD_subset_closure_interior : triD ⊆ closure (interior triD) := by
  rw [convex_triD.closure_interior_eq_closure_of_nonempty_interior interior_triD_nonempty]
  exact subset_closure

/-! ## The continuous representative -/

/-- The representative `(𝓕𝓕 g)(-·)` equals `f` on the triangle. -/
theorem rep_eq_on {θ : ℝ} (hθ : 0 ≤ θ) {g f : (Fin 2 → ℝ) → ℂ} (hg : timeFourierNorm θ g < ⊤)
    (hgf : ∀ x ∈ triD, g x = f x) (hf : ContinuousOn f triD) :
    ∀ x ∈ triD, timeFourier (timeFourier g) (-x) = f x := by
  obtain ⟨hc, hae⟩ := Regref.timeFourier_continuous_representative hθ g hg
  have hint : EqOn (fun t => timeFourier (timeFourier g) (-t)) f (interior triD) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_interior hc.continuousOn
      (hf.mono interior_subset)
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem isOpen_interior.measurableSet] with t h1 h2
    exact h1.trans (hgf t (interior_subset h2))
  exact hint.of_subset_closure hc.continuousOn hf interior_subset triD_subset_closure_interior

/-! ## The core estimate -/

/-- The scalar restriction norm on the unit triangle. -/
def restr0 (θ : ℝ) (f : (Fin 2 → ℝ) → ℂ) : ℝ≥0∞ :=
  ⨅ (g : (Fin 2 → ℝ) → ℂ) (_ : ∀ x ∈ triD, g x = f x), timeFourierNorm θ g

/-- `‖foldCut‖₂`. -/
def cutL2 : ℝ := (eLpNorm foldCut 2 volume).toReal

theorem foldCut_memLp : MemLp foldCut 2 volume :=
  foldCut_contDiff.continuous.memLp_of_hasCompactSupport foldCut_compact

/-- **The core estimate**: one extension `g`, fixed `A`. -/
theorem core {η : ℝ} (hη0 : 0 ≤ η) (hη8 : η < 1 / 8) {f g : (Fin 2 → ℝ) → ℂ}
    (hf : ContinuousOn f triD) (hgf : ∀ x ∈ triD, g x = f x) (hg : timeFourierNorm (1 / 4) g < ⊤)
    {A : ℝ} (hA : 0 < A) (hfA : ∀ x ∈ triD, ‖f x‖ ≤ A) :
    restr0 η f ≤ ENNReal.ofReal ((2 * cutL2 + extC.toReal) *
      (A ^ ((1 - 8 * η) / 9) * (timeFourierNorm (1 / 4) g).toReal ^ (1 - (1 - 8 * η) / 9))) := by
  obtain ⟨hHc, hHae⟩ := Regref.timeFourier_continuous_representative (by norm_num : (0 : ℝ) ≤ 1 / 4) g hg
  set H : (Fin 2 → ℝ) → ℂ := fun t => timeFourier (timeFourier g) (-t) with hHdef
  have hgi := integrable_of_timeFourierNorm_lt_top hg
  have hHi : Integrable H := hgi.congr hHae.symm
  have hft : timeFourier H = timeFourier g := by
    funext ξ
    unfold timeFourier VectorFourier.fourierIntegral
    exact integral_congr_ae (hHae.mono fun t ht => by simp only [ht])
  have hHg : timeFourierNorm (1 / 4) H = timeFourierNorm (1 / 4) g := by
    rw [timeFourierNorm_eq_lintegral hHi, timeFourierNorm_eq_lintegral hgi, hft]
  have hHf : ∀ x ∈ triD, H x = f x := rep_eq_on (by norm_num) hg hgf hf
  set E := foldExt H with hEdef
  have hEf : ∀ x ∈ triD, E x = f x := fun x hx => (foldExt_eq H hx).trans (hHf x hx)
  have hEb : ∀ x, ‖E x‖ ≤ A * ‖foldCut x‖ :=
    norm_foldExt_le (fun y hy => by rw [hHf y hy]; exact hfA y hy)
  have hEc : Continuous E := foldExt_continuous hHc
  have hEi : Integrable E :=
    (foldCut_integrable.norm.const_mul A).mono' hEc.aestronglyMeasurable (ae_of_all _ hEb)
  have hbd : ∀ x, ‖E x‖ ≤ ‖(A : ℂ) • foldCut x‖ := fun x => by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]; exact hEb x
  have hE2 : MemLp E 2 volume :=
    (foldCut_memLp.const_smul (A : ℂ)).of_le hEc.aestronglyMeasurable (ae_of_all _ hbd)
  have hL2 : eLpNorm E 2 volume ≤ ENNReal.ofReal (A * cutL2) := by
    refine (eLpNorm_mono hEc.aestronglyMeasurable hbd).trans (le_of_eq ?_)
    change eLpNorm ((A : ℂ) • foldCut) 2 volume = _
    rw [eLpNorm_const_smul, ENNReal.ofReal_mul hA.le, cutL2, ENNReal.ofReal_toReal foldCut_memLp.eLpNorm_ne_top,
      ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
  have hσ : timeFourierNorm (1 / 8) E ≤
      ENNReal.ofReal (extC.toReal * (timeFourierNorm (1 / 4) g).toReal) := by
    refine (foldExt_norm_le hHc (by rw [hHg]; exact hg)).trans (le_of_eq ?_)
    rw [hHg, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal extC_lt_top.ne,
      ENNReal.ofReal_toReal hg.ne]
  calc restr0 η f ≤ timeFourierNorm η E := iInf₂_le E hEf
    _ ≤ _ := interp_opt hη0 hη8 hEi hE2 hA ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        ENNReal.toReal_nonneg hL2 hσ

/-- The constant of `FoldInterpolation`. -/
def foldConst : ℝ := 2 * cutL2 + extC.toReal + 1

theorem foldConst_pos : 0 < foldConst := by
  unfold foldConst cutL2; have := (ENNReal.toReal_nonneg (a := extC)); positivity

/-- **The estimate on the unit triangle.** -/
theorem fold0 {η : ℝ} (hη0 : 0 ≤ η) (hη8 : η < 1 / 8) (f : (Fin 2 → ℝ) → ℂ) (hf : ContinuousOn f triD) :
    restr0 η f ≤ ENNReal.ofReal foldConst * (⨆ (x : Fin 2 → ℝ) (_ : x ∈ triD), ‖f x‖ₑ) ^ ((1 - 8 * η) / 9) *
      restr0 (1 / 4) f ^ (1 - (1 - 8 * η) / 9) := by
  set τ := (1 - 8 * η) / 9 with hτ
  have hτ0 : 0 < τ := by rw [hτ]; linarith
  have hτ1 : 0 < 1 - τ := by rw [hτ]; linarith
  set A' := ⨆ (x : Fin 2 → ℝ) (_ : x ∈ triD), ‖f x‖ₑ with hA'
  obtain ⟨M, hM⟩ := isCompact_triD.exists_bound_of_continuousOn hf
  have hA'top : A' ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := M)) (iSup₂_le fun x hx => ?_)
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hM x hx)
  have hle : ∀ x ∈ triD, ‖f x‖ₑ ≤ A' := fun x hx => le_iSup₂ (f := fun x (_ : x ∈ triD) => ‖f x‖ₑ) x hx
  by_cases hA0 : A' = 0
  · have hz : ∀ x ∈ triD, (fun _ => (0 : ℂ)) x = f x := fun x hx => by
      have := hle x hx; rw [hA0, nonpos_iff_eq_zero, enorm_eq_zero] at this; exact this.symm
    calc restr0 η f ≤ timeFourierNorm η (fun _ => (0 : ℂ)) := iInf₂_le _ hz
      _ = 0 := timeFourierNorm_zero 2 η
      _ ≤ _ := by positivity
  set A := A'.toReal
  have hAA : A' = ENNReal.ofReal A := (ENNReal.ofReal_toReal hA'top).symm
  have hApos : 0 < A := ENNReal.toReal_pos hA0 hA'top
  have hfA : ∀ x ∈ triD, ‖f x‖ ≤ A := fun x hx => by
    have := hle x hx
    rw [hAA, ← ofReal_norm] at this
    exact (ENNReal.ofReal_le_ofReal_iff hApos.le).mp this
  set K := ENNReal.ofReal foldConst * A' ^ τ with hK
  have hK0 : K ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr foldConst_pos).ne' (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hA0)
    hA'top).ne'
  have hKtop : K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg hτ0.le hA'top)
  have hper : ∀ g : {g : (Fin 2 → ℝ) → ℂ // ∀ x ∈ triD, g x = f x},
      restr0 η f ≤ K * timeFourierNorm (1 / 4) g.1 ^ (1 - τ) := by
    rintro ⟨g, hgf⟩
    dsimp only
    by_cases hN : timeFourierNorm (1 / 4) g = ⊤
    · rw [hN, ENNReal.top_rpow_of_pos hτ1, ENNReal.mul_top hK0]; exact le_top
    have hNlt : timeFourierNorm (1 / 4) g < ⊤ := lt_top_iff_ne_top.mpr hN
    refine (core hη0 hη8 hf hgf hNlt hApos hfA).trans ?_
    set b := (timeFourierNorm (1 / 4) g).toReal
    have hbb : timeFourierNorm (1 / 4) g = ENNReal.ofReal b := (ENNReal.ofReal_toReal hN).symm
    have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
    rw [hK, hAA, hbb, ENNReal.ofReal_rpow_of_nonneg hApos.le hτ0.le,
      ENNReal.ofReal_rpow_of_nonneg hb0 hτ1.le, ← ENNReal.ofReal_mul (by unfold foldConst cutL2; positivity),
      ← ENNReal.ofReal_mul (by unfold foldConst cutL2; positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : 2 * cutL2 + extC.toReal ≤ foldConst := by unfold foldConst; linarith
    have h2 : 0 ≤ A ^ τ * b ^ (1 - τ) := by positivity
    nlinarith
  -- the infimum commutes with `x ↦ K x^{1-τ}`
  have hmono : Monotone fun x : ℝ≥0∞ => K * x ^ (1 - τ) := fun x y hxy =>
    mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hxy hτ1.le)
  have hcont : Continuous fun x : ℝ≥0∞ => K * x ^ (1 - τ) :=
    (ENNReal.continuous_const_mul hKtop).comp ENNReal.continuous_rpow_const
  have htop : (fun x : ℝ≥0∞ => K * x ^ (1 - τ)) ⊤ = ⊤ := by
    simp only [ENNReal.top_rpow_of_pos hτ1, ENNReal.mul_top hK0]
  have hcomm : K * (⨅ g : {g : (Fin 2 → ℝ) → ℂ // ∀ x ∈ triD, g x = f x}, timeFourierNorm (1 / 4) g.1) ^ (1 - τ) =
      ⨅ g : {g : (Fin 2 → ℝ) → ℂ // ∀ x ∈ triD, g x = f x}, K * timeFourierNorm (1 / 4) g.1 ^ (1 - τ) :=
    hmono.map_iInf_of_continuousAt hcont.continuousAt htop
      (g := fun g : {g : (Fin 2 → ℝ) → ℂ // ∀ x ∈ triD, g x = f x} => timeFourierNorm (1 / 4) g.1)
  have hr : restr0 (1 / 4) f =
      ⨅ g : {g : (Fin 2 → ℝ) → ℂ // ∀ x ∈ triD, g x = f x}, timeFourierNorm (1 / 4) g.1 := by
    unfold restr0; rw [iInf_subtype']
  rw [hr, hcomm]
  exact le_iInf hper

/-! ## Translation and the target -/

/-- The shift `x ↦ x + (q, q)`. -/
def shift (q : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ := x + fun _ => q

@[simp] theorem shift_apply (q : ℝ) (x : Fin 2 → ℝ) (i : Fin 2) : shift q x i = x i + q := rfl

theorem shift_neg_shift (q : ℝ) (t : Fin 2 → ℝ) : shift q (shift (-q) t) = t := by
  ext i; simp

theorem mem_tri_shift (q : ℝ) (x : Fin 2 → ℝ) :
    (q ≤ shift q x 1 ∧ shift q x 1 ≤ shift q x 0 ∧ shift q x 0 ≤ q + 1) ↔ x ∈ triD := by
  simp only [shift_apply, triD, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith⟩

theorem shift_neg_mem {q : ℝ} {t : Fin 2 → ℝ} (ht : q ≤ t 1 ∧ t 1 ≤ t 0 ∧ t 0 ≤ q + 1) :
    shift (-q) t ∈ triD := by
  rw [← mem_tri_shift q, shift_neg_shift]; exact ht

theorem XNorm00_unit (θ : ℝ) (G : (Fin 2 → ℝ) → Unit → ℂ) :
    XNorm00 θ G = timeFourierNorm θ (fun t => G t ()) :=
  NormBridgeScratch.XNorm00_unit_eq_timeFourierNorm θ (fun t => G t ())

theorem timeFourierNorm_shift (θ q : ℝ) (g : (Fin 2 → ℝ) → ℂ) :
    timeFourierNorm θ (fun t => g (shift q t)) = timeFourierNorm θ g :=
  timeFourierNorm_translate θ g _

theorem restr_translate (θ q : ℝ) (f : (Fin 2 → ℝ) → Unit → ℂ) :
    XNorm00Restr θ {ts : Fin 2 → ℝ | q ≤ ts 1 ∧ ts 1 ≤ ts 0 ∧ ts 0 ≤ q + 1} Set.univ f =
      restr0 θ (fun x => f (shift q x) ()) := by
  unfold XNorm00Restr restr0
  apply le_antisymm
  · refine le_iInf₂ fun g hg => ?_
    refine iInf₂_le_of_le (fun t _ => g (shift (-q) t)) (fun t ht v _ => ?_) (le_of_eq ?_)
    · have hmem : shift (-q) t ∈ triD := shift_neg_mem ht
      show g (shift (-q) t) = f t v
      rw [hg _ hmem]
      show f (shift q (shift (-q) t)) () = f t v
      rw [shift_neg_shift]
    · rw [XNorm00_unit]
      exact timeFourierNorm_shift θ (-q) g
  · refine le_iInf₂ fun G hG => ?_
    refine iInf₂_le_of_le (fun x => G (shift q x) ()) (fun x hx => ?_) (le_of_eq ?_)
    · exact hG _ ((mem_tri_shift q x).mpr hx) () (mem_univ _)
    · rw [XNorm00_unit]
      exact timeFourierNorm_shift θ q (fun t => G t ())

theorem sup_translate (q : ℝ) (f : (Fin 2 → ℝ) → Unit → ℂ) :
    (⨆ (ts : Fin 2 → ℝ) (_ : q ≤ ts 1 ∧ ts 1 ≤ ts 0 ∧ ts 0 ≤ q + 1), ‖f ts ()‖ₑ) =
      ⨆ (x : Fin 2 → ℝ) (_ : x ∈ triD), ‖f (shift q x) ()‖ₑ := by
  apply le_antisymm
  · refine iSup₂_le fun ts hts => ?_
    refine le_iSup₂_of_le (f := fun x (_ : x ∈ triD) => ‖f (shift q x) ()‖ₑ) _ (shift_neg_mem hts)
      (le_of_eq ?_)
    show ‖f ts ()‖ₑ = ‖f (shift q (shift (-q) ts)) ()‖ₑ
    rw [shift_neg_shift]
  · refine iSup₂_le fun x hx => ?_
    exact le_iSup₂_of_le (f := fun ts (_ : q ≤ ts 1 ∧ ts 1 ≤ ts 0 ∧ ts 0 ≤ q + 1) => ‖f ts ()‖ₑ)
      (shift q x) ((mem_tri_shift q x).mpr hx) le_rfl

/-- **`FoldInterpolation`** (o82 Lemmas 17.1–17.2). -/
theorem foldInterpolation : ProtDefs.FoldInterpolation := by
  intro η hη0 hη8
  refine ⟨foldConst, foldConst_pos.le, fun q f hf => ?_⟩
  rw [restr_translate, restr_translate, sup_translate]
  refine fold0 hη0 hη8 _ ?_
  have hsh : Continuous (shift q) := continuous_id.add continuous_const
  exact (hf ()).comp hsh.continuousOn (fun x hx => (mem_tri_shift q x).mpr hx)

end WaveTurbulence.Flower.ProtOpsFold
