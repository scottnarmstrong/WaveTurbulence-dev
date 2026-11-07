/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.ProdFT
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.Cert
public import WaveTurbulence.Foundations.Incoh.DominatedFourierMixture
public import WaveTurbulence.Foundations.Regref.Trace00

/-! # W2-KIND2 Lemma A (6): the abstract gluing step

`glue_core`: let `κ` be a smooth compactly supported cutoff, `φ` a continuous time reparametrisation, and suppose the kernels
`t ↦ κ(t) e^{2πi (ξ₀ φ(t₀) + ξ₁ t₁)}` have `𝔛^{θ₁}`-norm `≤ Ck · ⟨ξ⟩^{θ₀}`.  If `Y = J ∘ (φ × id)` on `B₂`, `κ = 1` on `B₂`, and the points
`(φ(t₀), t₁)`, `t ∈ B₂`, lie in `closure (interior T)`, then `‖Y‖_{𝔛^{θ₁}(B₂)} ≤ Ck ‖J‖_{𝔛^{θ₀}(T)}`.
The extension of `Y` is `κ(t) · rep(G)(φ(t₀), t₁)` for an extension `G` of `J`, written as a mixture of the kernels over the Fourier variable of `G`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open MeasureTheory Set Filter Topology WaveTurbulence.Fourier WaveTurbulence.Incoh
open scoped ENNReal

/-- The character `e^{2πi y}`. -/
noncomputable def eE (y : ℝ) : ℂ := ((Real.fourierChar y : Circle) : ℂ)

theorem norm_eE (y : ℝ) : ‖eE y‖ = 1 := Circle.norm_coe _

theorem continuous_eE : Continuous eE := by
  unfold eE
  exact continuous_subtype_val.comp Real.continuous_fourierChar

theorem eE_pairing (ξ x : Fin 2 → ℝ) :
    ((Real.fourierChar (-(timePairing 2 ξ (-x))) : Circle) : ℂ) = eE (ξ 0 * x 0 + ξ 1 * x 1) := by
  unfold eE
  congr 1
  congr 1
  simp only [timePairing, dotProductBilin, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Fin.sum_univ_two]
  simp
  ring

theorem rep_eq_integral (g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) :
    Regref.rep g x = ∫ ξ, eE (ξ 0 * x 0 + ξ 1 * x 1) * timeFourier g ξ := by
  unfold Regref.rep timeFourier VectorFourier.fourierIntegral
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  rw [eE_pairing]


theorem glue_core {θ0 θ1 : ℝ} (hθ0 : 0 ≤ θ0)
    {κ : (Fin 2 → ℝ) → ℂ} (hκc : HasCompactSupport κ) (hκ : Continuous κ)
    {φ : ℝ → ℝ} (hφ : Continuous φ) {Ck : ℝ≥0∞} (hCk0 : Ck ≠ 0) (hCk : Ck ≠ ⊤)
    (hker : ∀ ξ : Fin 2 → ℝ, timeFourierNorm θ1 (fun t => κ t * eE (ξ 0 * φ (t 0) + ξ 1 * t 1)) ≤
      Ck * ENNReal.ofReal (timeBracket ξ ^ θ0))
    {T B2 : Set (Fin 2 → ℝ)} {J Y : (Fin 2 → ℝ) → ℂ} (hJ : Continuous J)
    (hB : ∀ ts ∈ B2, κ ts = 1 ∧ ![φ (ts 0), ts 1] ∈ closure (interior T) ∧ Y ts = J ![φ (ts 0), ts 1]) :
    XNorm00Restr (V := Unit) θ1 B2 Set.univ (fun ts _ => Y ts) ≤
      Ck * XNorm00Restr (V := Unit) θ0 T Set.univ (fun ts _ => J ts) := by
  unfold XNorm00Restr
  rw [ENNReal.mul_iInf_of_ne hCk0 hCk]
  refine le_iInf fun G => ?_
  rw [ENNReal.mul_iInf_of_ne hCk0 hCk]
  refine le_iInf fun hG => ?_
  by_cases htop : XNorm00 θ0 G = ⊤
  · rw [htop, ENNReal.mul_top hCk0]; exact le_top
  have hfin : mixedFourierNorm00 θ0 G < ⊤ := by
    rw [← NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]; exact lt_top_iff_ne_top.2 htop
  set g : (Fin 2 → ℝ) → ℂ := fun t => G t () with hgdef
  have hgn : timeFourierNorm θ0 g < ⊤ := (timeFourierNorm_slice_le_mixedFourierNorm00 θ0 G ()).trans_lt hfin
  obtain ⟨hrc, hrae, hri, hrft, hrfi⟩ := Regref.rep_props hθ0 hgn
  have hgi : Integrable g := integrable_of_timeFourierNorm_lt_top hgn
  have hGi : Integrable (timeFourier g) := integrable_timeFourier_of_norm_lt_top hθ0 hgn
  have hGc : Continuous (timeFourier g) := timeFourier_continuous hgi
  have hκi : Integrable κ := hκ.integrable_of_hasCompactSupport hκc
  let Kf : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ := fun t ξ => κ t * eE (ξ 0 * φ (t 0) + ξ 1 * t 1)
  have hKc : Continuous (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => Kf z.1 z.2) := by
    refine (hκ.comp continuous_fst).mul (continuous_eE.comp ?_)
    refine Continuous.add (Continuous.mul ((continuous_apply 0).comp continuous_snd)
      (hφ.comp ((continuous_apply 0).comp continuous_fst))) (Continuous.mul ((continuous_apply 1).comp continuous_snd)
      ((continuous_apply 1).comp continuous_fst))
  have hnK : ∀ t ξ, ‖Kf t ξ‖ = ‖κ t‖ := fun t ξ => by simp only [Kf, norm_mul, norm_eE, mul_one]
  have hiK : ∀ ξ, Integrable (fun t => Kf t ξ) := fun ξ => by
    refine hκi.norm.mono' ?_ (Eventually.of_forall fun t => (hnK t ξ).le)
    exact (hKc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hjoint : ∀ v : Unit, Integrable (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => timeFourier g z.2 * Kf z.1 z.2)
      (volume.prod volume) := fun v => by
    have h1 : Integrable (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => ‖κ z.1‖ * ‖timeFourier g z.2‖) (volume.prod volume) :=
      hκi.norm.mul_prod hGi.norm
    refine h1.mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((hGc.comp continuous_snd).mul hKc).aestronglyMeasurable
    · rw [norm_mul, hnK]; rw [mul_comm]
  have hmix := mixedFourierNorm00_integral_dominated_le (V := Unit) (μ := volume) θ1 (fun _ ξ => timeFourier g ξ) Kf
    hKc.stronglyMeasurable hiK hjoint (E := fun ξ => ‖timeFourier g ξ‖ₑ) hGc.measurable.enorm (fun _ _ => le_rfl)
  let H : (Fin 2 → ℝ) → Unit → ℂ := fun t _ => ∫ ξ, timeFourier g ξ * Kf t ξ
  have hHeq : ∀ t, H t () = κ t * Regref.rep g ![φ (t 0), t 1] := by
    intro t
    show ∫ ξ, timeFourier g ξ * Kf t ξ = _
    rw [rep_eq_integral, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [Kf, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hag : ∀ t ∈ B2, ∀ v ∈ (Set.univ : Set Unit), H t v = Y t := by
    intro t ht v _
    obtain ⟨hk1, hcl, hY⟩ := hB t ht
    have hrep : Regref.rep g ![φ (t 0), t 1] = J ![φ (t 0), t 1] :=
      Regref.rep_eq_of_mem_closure_interior hθ0 hgn (fun s hs => hG s hs () (Set.mem_univ _)) hJ hcl
    have := hHeq t
    rw [hk1, hrep, one_mul] at this
    rw [show v = () from Subsingleton.elim _ _, this, hY]
  refine (iInf₂_le H hag).trans ?_
  rw [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00, NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
  refine hmix.trans ?_
  have hGi' : ∀ v : Unit, Integrable (fun t => G t v) := fun v => by
    rw [show v = () from Subsingleton.elim _ _]; exact hgi
  rw [mixedFourierNorm00_eq_lintegral hGi']
  calc ∫⁻ u, ‖timeFourier g u‖ₑ * timeFourierNorm θ1 (fun t => Kf t u)
      ≤ ∫⁻ u, ‖timeFourier g u‖ₑ * (Ck * ENNReal.ofReal (timeBracket u ^ θ0)) :=
        lintegral_mono fun u => mul_le_mul' le_rfl (hker u)
    _ = Ck * ∫⁻ u, timeWeight θ0 u * mixedFourierEnvelope00 G u := by
        rw [← lintegral_const_mul' _ _ hCk]
        refine lintegral_congr fun u => ?_
        simp only [timeWeight, mixedFourierEnvelope00, iSup_unique]
        ring

end WaveTurbulence.VineEstS5C.P4.W2.K2
