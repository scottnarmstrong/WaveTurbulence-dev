/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsFold.Main
public import WaveTurbulence.Foundations.Flower.ProtOpsSlot.Slots
public import WaveTurbulence.Foundations.Flower.ProtPin.Tensor2
public import WaveTurbulence.Foundations.Flower.ProtOps.LinSynth

/-! # D6b: fold interpolation on the protected time boxes, for upper-clock functions

`fold_box`: if `F(ts, k) = G(ts 0)` with `G` continuous (a protected kernel whose lone parent is pinned does not see
its port time), then on every box `timeBoxGt p q'` (`q' ≤ p`)

`‖F(·,k)‖_{X^η} ≤ C · (sup_{[p,p+1]} |G|)^τ · ‖F(·,k)‖_{X^{1/4}(timeBoxGt p p)}^{1-τ}`,  `τ = (1 - 8η)/9`.

* the triangle `{p ≤ ts 1 ≤ ts 0 ≤ p+1}`: D1b-F's `foldInterpolation`; the `X^{1/4}` input on the open triangle is
  transported to the closed one by the continuous representative (main `timeFourier_continuous_representative`);
* `q' = p`: the box lies in the triangle; `q' < p`: the trace at `ts 1 = p` (D1b-S `fixedSlotBound`) tensored with
  the cutoff `cutK 1 q'` (D3's `timeFourierNorm_tensor2_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology WaveTurbulence.Fourier
open scoped ENNReal Classical

namespace WaveTurbulence.Flower.ProtWhole

open WaveTurbulence.Flower.ProtDefs

/-- The closed triangle of `FoldInterpolation`. -/
def triP (p : ℝ) : Set (Fin 2 → ℝ) := {ts | p ≤ ts 1 ∧ ts 1 ≤ ts 0 ∧ ts 0 ≤ p + 1}

/-- Its open interior. -/
def triU (p : ℝ) : Set (Fin 2 → ℝ) := {ts | p < ts 1 ∧ ts 1 < ts 0 ∧ ts 0 < p + 1}

theorem isOpen_triU (p : ℝ) : IsOpen (triU p) := by
  simp only [triU, Set.setOf_and]
  exact (isOpen_lt continuous_const (continuous_apply 1)).inter ((isOpen_lt (continuous_apply 1)
    (continuous_apply 0)).inter (isOpen_lt (continuous_apply 0) continuous_const))

theorem triU_subset_box (p : ℝ) : triU p ⊆ timeBoxGt p p := by
  rintro ts ⟨h1, h2, h3⟩
  exact ⟨⟨⟨by linarith, h3.le⟩, ⟨h1.le, by linarith⟩⟩, h2⟩

theorem triP_subset_closure (p : ℝ) : triP p ⊆ closure (triU p) := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hx
  let c : Fin 2 → ℝ := ![p + 2 / 3, p + 1 / 3]
  let f : ℝ → Fin 2 → ℝ := fun ε => x + ε • (c - x)
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have h0 : f 0 = x := by simp [f]
  refine mem_closure_of_tendsto (f := f) (b := 𝓝[>] (0 : ℝ)) ?_ ?_
  · have := hf.tendsto 0
    rw [h0] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    obtain ⟨he0, he1⟩ := hε
    simp only [triU, Set.mem_setOf_eq, f, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, c,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem triP_subset_of_box (p : ℝ) : timeBoxGt p p ⊆ triP p := by
  rintro ts ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩
  exact ⟨h3, h5.le, h2⟩

/-- The continuous representative of an extension that agrees with `G ∘ (· 0)` on the open triangle agrees with
it on the closed triangle. -/
theorem rep_agrees {θ : ℝ} (hθ : 0 ≤ θ) {p : ℝ} {h : (Fin 2 → ℝ) → ℂ} (hh : timeFourierNorm θ h < ⊤)
    {G : ℝ → ℂ} (hG : Continuous G) (hU : ∀ x ∈ triU p, h x = G (x 0)) :
    ∀ x ∈ triP p, timeFourier (timeFourier h) (-x) = G (x 0) := by
  obtain ⟨hc, hae⟩ := Regref.timeFourier_continuous_representative hθ h hh
  have hGc : Continuous fun x : Fin 2 → ℝ => G (x 0) := hG.comp (continuous_apply 0)
  have hint : EqOn (fun t => timeFourier (timeFourier h) (-t)) (fun x => G (x 0)) (triU p) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ (isOpen_triU p) hc.continuousOn hGc.continuousOn
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem (isOpen_triU p).measurableSet] with t h1 h2
    exact h1.trans (hU t h2)
  exact hint.of_subset_closure hc.continuousOn hGc.continuousOn (fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩)
    (triP_subset_closure p)

/-! ### Outputs: one output versus `Unit` -/

theorem XNorm00_single {r d : ℕ} (θ : ℝ) (h : (Fin r → ℝ) → ℂ) (k : Mom d) :
    XNorm00 θ (fun t (k' : Mom d) => if k' = k then h t else 0) = timeFourierNorm θ h := by
  rw [← NormBridgeScratch.XNorm00_unit_eq_timeFourierNorm]
  unfold XNorm00
  have hint : (∀ v : Mom d, Integrable fun t => (if v = k then h t else 0)) ↔
      ∀ v : Unit, Integrable fun t => (fun t (_ : Unit) => h t) t v := by
    constructor
    · intro hv _; simpa using hv k
    · intro hv v
      by_cases hk : v = k
      · simpa [hk] using hv ()
      · simp [hk]
  by_cases hi : ∀ v : Mom d, Integrable fun t => (if v = k then h t else 0)
  · rw [if_pos hi, if_pos (hint.1 hi)]
    refine lintegral_congr fun lam => ?_
    congr 1
    refine le_antisymm (iSup_le fun v => ?_) (le_iSup_of_le k ?_)
    · by_cases hk : v = k
      · subst hk
        exact le_iSup_of_le () (le_of_eq (by simp [timeFT]))
      · simp [timeFT, hk]
    · exact iSup_le fun _ => le_of_eq (by simp [timeFT])
  · rw [if_neg hi, if_neg (fun h' => hi (hint.2 h'))]

theorem XNorm00_comp_le {r : ℕ} {V : Type*} (θ : ℝ) (E : (Fin r → ℝ) → V → ℂ) (k : V) :
    XNorm00 θ (fun t (_ : Unit) => E t k) ≤ XNorm00 θ E := by
  unfold XNorm00
  by_cases hi : ∀ v, Integrable fun t => E t v
  · rw [if_pos hi, if_pos (fun _ => hi k)]
    refine lintegral_mono fun lam => mul_le_mul_of_nonneg_left (iSup_le fun _ => ?_) zero_le
    exact le_iSup_of_le k (le_of_eq (by simp [timeFT]))
  · rw [if_neg hi]
    exact le_top

theorem XNorm00_const_out {r d : ℕ} (θ : ℝ) (h : (Fin r → ℝ) → ℂ) :
    XNorm00 θ (fun t (_ : Mom d) => h t) = timeFourierNorm θ h := by
  rw [← NormBridgeScratch.XNorm00_unit_eq_timeFourierNorm]
  unfold XNorm00
  have hi : (∀ _ : Mom d, Integrable h) ↔ ∀ _ : Unit, Integrable h :=
    ⟨fun H _ => H 0, fun H _ => H ()⟩
  by_cases hh : Integrable h
  · rw [if_pos (fun _ => hh), if_pos (fun _ => hh)]
    refine lintegral_congr fun lam => ?_
    congr 1
    exact le_antisymm (iSup_le fun _ => le_iSup_of_le () le_rfl) (iSup_le fun _ => le_iSup_of_le 0 le_rfl)
  · rw [if_neg (fun H => hh (H 0)), if_neg (fun H => hh (H ()))]

/-! ### The two transfers -/

/-- The `X^{1/4}` input: the closed triangle from the open box `timeBoxGt p p`. -/
theorem quarter_transfer {d : ℕ} (θ : ℝ) (hθ : 0 ≤ θ) (p : ℝ) (F : (Fin 2 → ℝ) → Mom d → ℂ) (k : Mom d)
    (G : ℝ → ℂ) (hG : Continuous G) (hF : ∀ ts, F ts k = G (ts 0)) :
    XNorm00Restr θ (triP p) univ (fun ts (_ : Unit) => G (ts 0)) ≤ XNorm00Restr θ (timeBoxGt p p) {k} F := by
  unfold XNorm00Restr
  refine le_iInf₂ fun E hE => ?_
  by_cases htop : XNorm00 θ E = ⊤
  · rw [htop]; exact le_top
  set h : (Fin 2 → ℝ) → ℂ := fun t => E t k
  have hle : timeFourierNorm θ h ≤ XNorm00 θ E := by
    rw [← NormBridgeScratch.XNorm00_unit_eq_timeFourierNorm]; exact XNorm00_comp_le θ E k
  have hh : timeFourierNorm θ h < ⊤ := lt_of_le_of_lt hle (lt_top_iff_ne_top.2 htop)
  have hU : ∀ x ∈ triU p, h x = G (x 0) := fun x hx => by
    rw [← hF x]; exact hE x (triU_subset_box p hx) k (Set.mem_singleton k)
  have hrep := rep_agrees hθ hh hG hU
  obtain ⟨-, hae⟩ := Regref.timeFourier_continuous_representative hθ h hh
  refine iInf₂_le_of_le (fun t (_ : Unit) => timeFourier (timeFourier h) (-t)) (fun x hx _ _ => hrep x hx) ?_
  rw [NormBridgeScratch.XNorm00_unit_eq_timeFourierNorm, ProtPin.timeFourierNorm_congr_ae hae]
  exact hle

/-- The `X^η` output: every box `timeBoxGt p q'` from the closed triangle. -/
theorem box_transfer {d : ℕ} (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p q' : ℕ), q' ≤ p → ∀ (F : (Fin 2 → ℝ) → Mom d → ℂ) (k : Mom d) (G : ℝ → ℂ),
      Continuous G → (∀ ts, F ts k = G (ts 0)) →
      XNorm00Restr θ (timeBoxGt p q') {k} F ≤
        ENNReal.ofReal C * XNorm00Restr θ (triP p) univ (fun ts (_ : Unit) => G (ts 0)) := by
  obtain ⟨Ctr, hCtr0, htr⟩ := ProtOpsSlot.fixedSlotBound d 1 θ hθ
  set Cχ : ℝ := max 1 (timeFourierNorm θ (ProtOps.cutK 1 0)).toReal with hCχ
  have hχ : timeFourierNorm θ (ProtOps.cutK 1 0) ≤ ENNReal.ofReal Cχ := by
    rw [← ENNReal.ofReal_toReal (ProtOps.cutK_norm_lt_top 1 0 θ).ne]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hCχ1 : 1 ≤ Cχ := le_max_left _ _
  refine ⟨max 1 (Cχ * Ctr), le_max_of_le_left zero_le_one, fun p q' hq F k G hG hF => ?_⟩
  have hM0 : ENNReal.ofReal (max 1 (Cχ * Ctr)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  conv_rhs => rw [XNorm00Restr, ENNReal.mul_iInf_of_ne hM0 ENNReal.ofReal_ne_top]
  refine le_iInf fun g => ?_
  rw [ENNReal.mul_iInf_of_ne hM0 ENNReal.ofReal_ne_top]
  refine le_iInf fun hg => ?_
  by_cases htop : XNorm00 θ g = ⊤
  · rw [htop, ENNReal.mul_top (by simp)]; exact le_top
  set h : (Fin 2 → ℝ) → ℂ := fun t => g t ()
  have hgh : XNorm00 θ g = timeFourierNorm θ h := NormBridgeScratch.XNorm00_unit_eq_timeFourierNorm θ h
  rcases Nat.eq_or_lt_of_le hq with hpq | hpq
  · -- q' = p: the box lies in the triangle
    subst hpq
    refine iInf₂_le_of_le (fun t k' => if k' = k then h t else 0) (fun ts hts v hv => ?_) ?_
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      beta_reduce
      rw [if_pos rfl, hF]
      exact hg ts (triP_subset_of_box _ hts) () (Set.mem_univ _)
    · rw [XNorm00_single, ← hgh]
      calc XNorm00 θ g = 1 * XNorm00 θ g := (one_mul _).symm
        _ ≤ ENNReal.ofReal (max 1 (Cχ * Ctr)) * XNorm00 θ g := by
            gcongr
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · -- q' < p: trace at `ts 1 = p`, tensored with `cutK 1 q'`
    have hh : timeFourierNorm θ h < ⊤ := by rw [← hgh]; exact lt_top_iff_ne_top.2 htop
    set H : (Fin 2 → ℝ) → ℂ := fun t => timeFourier (timeFourier h) (-t) with hHdef
    obtain ⟨hHc, hae⟩ := Regref.timeFourier_continuous_representative hθ h hh
    have hrep := rep_agrees hθ hh hG (fun x hx => hg x ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩ () (Set.mem_univ _))
    have hHn : timeFourierNorm θ H = XNorm00 θ g := by
      rw [hgh]; exact ProtPin.timeFourierNorm_congr_ae hae
    have htrace := htr (p : ℝ) (p : ℝ) (fun t (_ : Mom d) => H t) {k} (fun _ => hHc)
    rw [NormBridgeScratch.XNorm_zero_eq_XNorm00 θ, XNorm00_const_out, hHn] at htrace
    -- each 1-D extension of the trace gives a 2-D extension of F on the box
    have hstep : XNorm00Restr θ (timeBoxGt p q') {k} F ≤ ENNReal.ofReal Cχ *
        XNormRestr θ 0 0 (Set.pi univ fun _ => Icc (p : ℝ) (p + 1)) {k}
          (fun y (_ : Mom d) => H (Fin.snoc y (p : ℝ))) := by
      have hc0 : ENNReal.ofReal Cχ ≠ 0 := by
        rw [ENNReal.ofReal_ne_zero_iff]; linarith
      unfold XNormRestr
      rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
      refine le_iInf fun g1 => ?_
      rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
      refine le_iInf fun hg1 => ?_
      unfold XNorm00Restr
      refine iInf₂_le_of_le (fun t k' => if k' = k then g1 (fun _ => t 0) k * ProtOps.cutK 1 q' (fun _ => t 1) else 0)
        (fun ts hts v hv => ?_) ?_
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        beta_reduce
        rw [if_pos rfl, hF]
        obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩ := hts
        have hy : (fun _ : Fin 1 => ts 0) ∈ Set.pi univ fun _ => Icc (p : ℝ) (p + 1) :=
          fun _ _ => ⟨h1, h2⟩
        rw [hg1 _ hy v (Set.mem_singleton v), ProtOps.cutK_one (fun _ => ⟨h3, h4⟩), mul_one]
        have hmem : (Fin.snoc (fun _ : Fin 1 => ts 0) (p : ℝ) : Fin 2 → ℝ) ∈ triP p := by
          refine ⟨by simp [Fin.snoc], ?_, ?_⟩ <;> simp [Fin.snoc] <;> linarith
        have := hrep _ hmem
        simp only [hHdef] at this ⊢
        rw [this]
        simp [Fin.snoc]
      · rw [XNorm00_single, mul_comm (ENNReal.ofReal Cχ)]
        refine (ProtPin.timeFourierNorm_tensor2_le hθ (fun y => g1 y k) (ProtOps.cutK 1 q')).trans ?_
        rw [ProtOps.cutK_norm_eq 1 q' θ]
        refine mul_le_mul' ?_ hχ
        rw [← NormBridgeScratch.XNorm00_unit_eq_timeFourierNorm]
        exact (XNorm00_comp_le θ g1 k).trans (le_of_eq (NormBridgeScratch.XNorm_zero_eq_XNorm00 θ g1).symm)
    refine hstep.trans ?_
    calc ENNReal.ofReal Cχ * XNormRestr θ 0 0 (Set.pi univ fun _ => Icc (p : ℝ) (p + 1)) {k}
          (fun y (_ : Mom d) => H (Fin.snoc y (p : ℝ)))
        ≤ ENNReal.ofReal Cχ * (ENNReal.ofReal Ctr * XNorm00 θ g) := mul_le_mul_of_nonneg_left htrace zero_le
      _ = ENNReal.ofReal (Cχ * Ctr) * XNorm00 θ g := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith)]
      _ ≤ ENNReal.ofReal (max 1 (Cχ * Ctr)) * XNorm00 θ g := by
          gcongr
          exact le_max_right _ _

/-! ### The fold on the boxes -/

/-- **Fold interpolation on `timeBoxGt p q'`** for upper-clock functions. -/
theorem fold_box (d : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη8 : η < 1 / 8) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p q' : ℕ), q' ≤ p → ∀ (F : (Fin 2 → ℝ) → Mom d → ℂ) (k : Mom d) (G : ℝ → ℂ),
      Continuous G → (∀ ts, F ts k = G (ts 0)) →
      XNorm00Restr η (timeBoxGt p q') {k} F ≤
        ENNReal.ofReal C * (⨆ (T : ℝ) (_ : T ∈ Icc (p : ℝ) (p + 1)), ‖G T‖ₑ) ^ ((1 - 8 * η) / 9) *
          XNorm00Restr (1 / 4) (timeBoxGt p p) {k} F ^ (1 - (1 - 8 * η) / 9) := by
  obtain ⟨Cf, hCf0, hfold⟩ := ProtOpsFold.foldInterpolation η hη0 hη8
  obtain ⟨Cb, hCb0, hbox⟩ := box_transfer (d := d) η hη0
  refine ⟨Cb * Cf, mul_nonneg hCb0 hCf0, fun p q' hq F k G hG hF => ?_⟩
  have hτ0 : 0 ≤ (1 - 8 * η) / 9 := by linarith
  have hτ1 : 0 ≤ 1 - (1 - 8 * η) / 9 := by linarith
  have hcont : ∀ v : Unit, ContinuousOn (fun ts => (fun ts (_ : Unit) => G (ts 0)) ts v)
      {ts : Fin 2 → ℝ | (p : ℝ) ≤ ts 1 ∧ ts 1 ≤ ts 0 ∧ ts 0 ≤ p + 1} :=
    fun _ => (hG.comp (continuous_apply 0)).continuousOn
  have h1 := hfold (p : ℝ) (fun ts (_ : Unit) => G (ts 0)) hcont
  have hsup : (⨆ (ts : Fin 2 → ℝ) (_ : (p : ℝ) ≤ ts 1 ∧ ts 1 ≤ ts 0 ∧ ts 0 ≤ p + 1),
      ‖(fun ts (_ : Unit) => G (ts 0)) ts ()‖ₑ) ≤ ⨆ (T : ℝ) (_ : T ∈ Icc (p : ℝ) (p + 1)), ‖G T‖ₑ :=
    iSup₂_le fun ts hts => le_iSup₂_of_le (f := fun (T : ℝ) (_ : T ∈ Icc (p : ℝ) (p + 1)) => ‖G T‖ₑ) (ts 0)
      ⟨by linarith [hts.1, hts.2.1], hts.2.2⟩ le_rfl
  have hq4 := quarter_transfer (1 / 4) (by norm_num) (p : ℝ) F k G hG hF
  refine (hbox p q' hq F k G hG hF).trans ?_
  have h1' : XNorm00Restr η (triP p) univ (fun ts (_ : Unit) => G (ts 0)) ≤
      ENNReal.ofReal Cf * (⨆ (T : ℝ) (_ : T ∈ Icc (p : ℝ) (p + 1)), ‖G T‖ₑ) ^ ((1 - 8 * η) / 9) *
        XNorm00Restr (1 / 4) (timeBoxGt p p) {k} F ^ (1 - (1 - 8 * η) / 9) := by
    refine h1.trans ?_
    gcongr
    · exact hq4
  calc ENNReal.ofReal Cb * XNorm00Restr η (triP p) univ (fun ts (_ : Unit) => G (ts 0))
      ≤ ENNReal.ofReal Cb * (ENNReal.ofReal Cf * (⨆ (T : ℝ) (_ : T ∈ Icc (p : ℝ) (p + 1)), ‖G T‖ₑ) ^ ((1 - 8 * η) / 9) *
        XNorm00Restr (1 / 4) (timeBoxGt p p) {k} F ^ (1 - (1 - 8 * η) / 9)) :=
          mul_le_mul_of_nonneg_left h1' zero_le
    _ = _ := by rw [ENNReal.ofReal_mul hCb0]; ring

end WaveTurbulence.Flower.ProtWhole
