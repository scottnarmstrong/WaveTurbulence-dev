/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.TimeFS
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.TimeFS00Main
public import WaveTurbulence.Foundations.Regref.Trace00
public import WaveTurbulence.Foundations.Spine.XNormPointwise
public import WaveTurbulence.Foundations.Stage1.Represents.RepRep2

/-! # B3s MK-SLOTS: protected slots are superpositions (`ProtSlotSupM`, ruling R179)

D0 §5's conversion of an OK protected slot into a `SupM` superposition, in the form repaired by ruling R179
(F-B3s-3: the slot function is continuous in its clocks on the box).

* `rep_eq_of_continuousOn`: the continuous Fourier representative `Regref.rep g` of an extension `g` agrees with a
  function `h` that is only continuous ON `B` (main's `Regref.rep_eq_of_mem_closure_interior` asks for global
  continuity), at every point of `B ⊆ closure (interior B)`.
* `exists_continuous_version`: a near-optimal extension, replaced by its Fourier representative, is a globally
  continuous version of the slot function on `box × out`, with the same restricted norm bound; pointwise values are
  bounded by the restricted norm.
* `superposition_any`: main's `fourier_superposition` (`Λ ≠ 0`) and `fourier_superposition00` (`Λ = 0`) in one form.
* **`protSlotSupM : ProtSlotSupM`.** -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ENNReal Topology
open MeasureTheory Set Filter
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS

namespace WaveTurbulence.Flower.MkSlots

/-- The continuous representative agrees with `h` on `B` when `h` is continuous on `B`, `g = h` on `B` and
`B ⊆ closure (interior B)`. -/
theorem rep_eq_of_continuousOn {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) {B : Set (Fin r → ℝ)}
    {g h : (Fin r → ℝ) → ℂ} (hg : timeFourierNorm θ g < ⊤) (hgh : ∀ t ∈ B, g t = h t)
    (hh : ContinuousOn h B) (hBi : B ⊆ closure (interior B)) {t : Fin r → ℝ} (ht : t ∈ B) :
    Regref.rep g t = h t := by
  obtain ⟨hc, hae, -⟩ := Regref.rep_props hθ hg
  have hint : ∀ x ∈ interior B, Regref.rep g x = h x := by
    have hho : ContinuousOn (fun x => Regref.rep g x - h x) (interior B) :=
      hc.continuousOn.sub (hh.mono interior_subset)
    have hU : IsOpen (interior B ∩ (fun x => Regref.rep g x - h x) ⁻¹' {0}ᶜ) :=
      hho.isOpen_inter_preimage isOpen_interior isOpen_compl_singleton
    have hnull : volume (interior B ∩ (fun x => Regref.rep g x - h x) ⁻¹' {0}ᶜ) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hae)
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff, sub_eq_zero] at hx
      simp only [mem_setOf_eq]
      rw [hgh x (interior_subset hx.1)]
      exact hx.2
    have hemp := (hU.measure_eq_zero_iff volume).1 hnull
    intro x hx
    by_contra hne
    have hmem : x ∈ interior B ∩ (fun x => Regref.rep g x - h x) ⁻¹' {0}ᶜ := by
      refine ⟨hx, ?_⟩
      simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, sub_eq_zero]
      exact hne
    rw [hemp] at hmem
    exact hmem
  haveI hne : (𝓝[interior B] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hBi ht)
  have h1 : Tendsto (Regref.rep g) (𝓝[interior B] t) (𝓝 (Regref.rep g t)) :=
    (hc.tendsto t).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto h (𝓝[interior B] t) (𝓝 (h t)) := (hh t ht).mono interior_subset
  have h3 : Tendsto (Regref.rep g) (𝓝[interior B] t) (𝓝 (h t)) :=
    Tendsto.congr' (eventually_nhdsWithin_of_forall fun x hx => (hint x hx).symm) h2
  exact tendsto_nhds_unique h1 h3

/-- **A continuous version of a slot function** with a restricted norm bound `< b`: the Fourier representative of a
near-optimal extension. It agrees with `F` on `B × K`, has the same bound, and `‖F t k‖ₑ < b` there. -/
theorem exists_continuous_version {r d Λ : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) {B : Set (Fin r → ℝ)} {K : Set (Mom d)}
    {F : (Fin r → ℝ) → Mom d → ℂ} (hBi : B ⊆ closure (interior B))
    (hFc : ∀ k ∈ K, ContinuousOn (fun t => F t k) B) {b : ℝ≥0∞} (hn : XNormRestr θ Λ 0 B K F < b) :
    ∃ h : (Fin r → ℝ) → Mom d → ℂ, (∀ k, Continuous fun t => h t k) ∧
      (∀ t ∈ B, ∀ k ∈ K, h t k = F t k) ∧ XNormRestr θ Λ 0 B K h < b ∧
      ∀ t ∈ B, ∀ k ∈ K, ‖F t k‖ₑ < b := by
  unfold XNormRestr at hn
  obtain ⟨G, hG⟩ := iInf_lt_iff.1 hn
  obtain ⟨hGF, hGb⟩ := iInf_lt_iff.1 hG
  have hslice : ∀ k, timeFourierNorm θ (fun s => G s k) ≤ XNorm θ Λ 0 G := fun k =>
    (timeFourierNorm_slice_le_mixedFourierNorm00 θ G k).trans
      ((NormBridgeScratch.XNorm00_eq_mixedFourierNorm00 θ G).symm.le.trans (LGSpine.XNorm00_le_XNorm θ Λ 0 G))
  have hfin : ∀ k, timeFourierNorm θ (fun s => G s k) < ⊤ := fun k =>
    (hslice k).trans_lt (hGb.trans_le le_top)
  have heq : ∀ t ∈ B, ∀ k ∈ K, Regref.rep (fun s => G s k) t = F t k := fun t ht k hk =>
    rep_eq_of_continuousOn hθ (hfin k) (fun t' ht' => hGF t' ht' k hk) (hFc k hk) hBi ht
  refine ⟨fun t k => Regref.rep (fun s => G s k) t, fun k => (Regref.rep_props hθ (hfin k)).1, heq, ?_, ?_⟩
  · unfold XNormRestr
    refine lt_of_le_of_lt (iInf₂_le G fun t ht k hk => ?_) hGb
    rw [hGF t ht k hk]
    exact (heq t ht k hk).symm
  · intro t ht k hk
    obtain ⟨hc, -, hi, hft, -⟩ := Regref.rep_props hθ (hfin k)
    have h1 := Regref.enorm_le_timeFourierNorm_at hθ (Regref.rep fun s => G s k) t hc.continuousAt
    have h2 : timeFourierNorm θ (Regref.rep fun s => G s k) = timeFourierNorm θ (fun s => G s k) := by
      rw [timeFourierNorm_eq_lintegral hi,
        timeFourierNorm_eq_lintegral (integrable_of_timeFourierNorm_lt_top (hfin k)), hft]
    rw [← heq t ht k hk]
    exact (h1.trans (h2.le.trans (hslice k))).trans_lt hGb

/-- `SNorm 0 0` is the supremum norm. -/
theorem snorm_zero_zero_le_one {d : ℕ} (a : Mom d → ℂ) (h : ∀ v, ‖a v‖ ≤ 1) : SNorm 0 0 a ≤ 1 := by
  unfold SNorm
  rw [if_pos (Or.inl rfl)]
  refine iSup_le fun ρ => iSup_le fun hρ => iSup_le fun k => ?_
  have hρ0 : ρ = fun _ => 0 := by
    funext j
    have := Finset.single_le_sum (fun i _ => Nat.zero_le (ρ i)) (Finset.mem_univ j)
    omega
  subst hρ0
  rw [Induct.iterPartial_zero_index]
  simp only [pow_zero, one_mul]
  exact ENNReal.ofReal_le_one.2 (h k)

/-- `XNorm00Restr ≤ XNormRestr θ 0 0`. -/
theorem xnorm00Restr_le {r d : ℕ} (θ : ℝ) (B : Set (Fin r → ℝ)) (K : Set (Mom d))
    (f : (Fin r → ℝ) → Mom d → ℂ) : XNorm00Restr θ B K f ≤ XNormRestr θ 0 0 B K f := by
  unfold XNorm00Restr XNormRestr
  exact iInf_mono fun G => iInf_mono fun _ => LGSpine.XNorm00_le_XNorm θ 0 0 G

/-- Main's Fourier superposition for every derivative order `Λ` (`Λ = 0` through `fourier_superposition00`). -/
theorem superposition_any {r d : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (Λ : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (B : Set (Fin r → ℝ)) (K : Set (Mom d))
      (f : (Fin r → ℝ) → Mom d → ℂ) (b : ℝ≥0∞), b ≠ ⊤ →
      B ⊆ cell q → B ⊆ closure (interior B) → (∀ k ∈ K, Continuous fun t => f t k) →
      XNormRestr θ Λ 0 B K f < b →
      ∃ (w : (Fin r → ℤ) → ℝ) (a : (Fin r → ℤ) → Mom d → ℂ),
        (∀ m, 0 ≤ w m) ∧ (∀ m, SNorm Λ 0 (a m) ≤ 1) ∧
        (∀ t ∈ B, ∀ k ∈ K, HasSum (fun m => (w m : ℂ) * a m k * fsPhase m t) (f t k)) ∧
        Summable w ∧
        ∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (w m) ≤ C * b := by
  rcases Nat.eq_zero_or_pos Λ with hΛ | hΛ
  · subst hΛ
    obtain ⟨C, hC, h⟩ := RepAnalytic.fourier_superposition00 (r := r) (V := Mom d) hθ
    refine ⟨C, hC, fun q B K f b hb hBc hBi hfc hn => ?_⟩
    obtain ⟨w, a, h1, h2, h3, h4, h5⟩ :=
      h q B K f b hb hBc hBi hfc (lt_of_le_of_lt (xnorm00Restr_le θ B K f) hn)
    exact ⟨w, a, h1, fun m => snorm_zero_zero_le_one (a m) (h2 m), h3, h4, h5⟩
  · exact RepAnalytic.fourier_superposition (r := r) (d := d) hθ (Λ₂ := 0) hΛ.ne'

/-- **`ProtSlotSupM`** (D0 §5, repaired by ruling R179): an OK protected slot whose function is continuous in its
clocks on the box is, on `box × out`, a `SupM` superposition with normalized amplitudes and moment mass
`C · mass`. -/
theorem protSlotSupM : ProtDefs.ProtSlotSupM := by
  intro d θ hθ
  obtain ⟨C, hC, hfs⟩ := superposition_any (r := 2) (d := d) hθ (30 * d)
  refine ⟨2 * C, ENNReal.mul_ne_top (by simp) hC, fun σ hσθ hBc hBi hFc hn => ?_⟩
  rw [hσθ] at hn
  set X := ENNReal.ofReal σ.mass with hX
  by_cases hX0 : X = 0
  · refine ⟨fun _ _ => 0, fun t ht k hk => ?_, Represents.SupM.zero θ _ _ _ (fun _ _ _ => rfl) _⟩
    show (0 : ℂ) = σ.F t k
    by_contra hne
    have hpos : 0 < ‖σ.F t k‖ₑ := enorm_pos.2 fun h0 => hne h0.symm
    rw [hX0] at hn
    obtain ⟨-, -, -, -, hlt⟩ := exists_continuous_version hθ hBi hFc (lt_of_le_of_lt hn hpos)
    exact lt_irrefl _ (hlt t ht k hk)
  · have hXt : X ≠ ⊤ := ENNReal.ofReal_ne_top
    have hlt : XNormRestr θ (30 * d) 0 σ.box σ.out σ.F < 2 * X := by
      calc _ ≤ X := hn
        _ < X + X := ENNReal.lt_add_right hXt hX0
        _ = 2 * X := (two_mul X).symm
    obtain ⟨h, hhc, hhF, hhn, -⟩ := exists_continuous_version hθ hBi hFc hlt
    obtain ⟨w, a, hw0, ha, hsum, hws, hmass⟩ :=
      hfs (fun _ => 0) σ.box σ.out h (2 * X) (ENNReal.mul_ne_top (by simp) hXt) hBc hBi (fun k _ => hhc k) hhn
    have hsm : ∀ t k, Summable fun m => (w m : ℂ) * a m k * fsPhase m t := by
      intro t k
      refine Summable.of_norm_bounded hws fun m => ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 m)]
      have hph : ‖fsPhase m t‖ = 1 := by unfold fsPhase; exact Circle.norm_coe _
      rw [hph, mul_one]
      exact mul_le_of_le_one_right (hw0 m) (Represents.snorm_le_one_pointwise _ (a m) (ha m) k)
    refine ⟨fun t k => ∑' m, (w m : ℂ) * a m k * fsPhase m t, fun t ht k hk => ?_, ?_⟩
    · rw [← hhF t ht k hk]
      exact (hsum t ht k hk).tsum_eq
    · exact ⟨Fin 2 → ℤ, inferInstance, w, id, a, hw0, hws, ha, fun t _ k => (hsm t k).hasSum,
        hmass.trans (le_of_eq (by ring))⟩

end WaveTurbulence.Flower.MkSlots
