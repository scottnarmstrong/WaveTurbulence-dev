/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.Relayer
public import WaveTurbulence.Foundations.Layered.RestrictionCalculus
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.Analysis
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TraceBox
public import WaveTurbulence.Foundations.Stage1.Represents.RepConj2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.ConjNorm
public import WaveTurbulence.Foundations.Sumint.TimeBridge
public import WaveTurbulence.Foundations.XChain.SNormPointwise
public import WaveTurbulence.Foundations.XChain.JbrBounds

/-! # D3 PROT-PIN: scalar restricted time norms

`rn θ B f` is the restricted `X^{θ,0,0}` norm of a scalar time function (`XNorm00Restr` with one output). It is
the per-output currency of D3: the gates give it (with output weights) for the cut pieces, the product, trace and
swap lemmas of main move it through the cut identity, and `LocalOutputExtension` collects it. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ComplexConjugate

namespace WaveTurbulence.Flower.ProtPin

variable {r : ℕ}

/-- The scalar restricted norm. -/
def rn (θ : ℝ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → ℂ) : ℝ≥0∞ :=
  XNorm00Restr θ B (Set.univ : Set Unit) (fun t _ => f t)

theorem XNorm00_const_eq {V : Type*} [Nonempty V] (θ : ℝ) (g : (Fin r → ℝ) → ℂ) :
    XNorm00 θ (fun t (_ : V) => g t) = timeFourierNorm θ g := by
  rw [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
  unfold mixedFourierNorm00 timeFourierNorm mixedFourierEnvelope00
  simp only [ciSup_const]
  by_cases h : Integrable g volume
  · rw [if_pos (fun _ => h), if_pos h]
  · rw [if_neg (fun h' => h (h' (Classical.arbitrary V))), if_neg h]

theorem rn_eq_iInf (θ : ℝ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → ℂ) :
    rn θ B f = ⨅ (g : (Fin r → ℝ) → ℂ) (_ : ∀ t ∈ B, g t = f t), timeFourierNorm θ g := by
  unfold rn XNorm00Restr
  apply le_antisymm
  · refine le_iInf₂ fun g hg => ?_
    refine (iInf₂_le (fun t (_ : Unit) => g t) fun t ht _ _ => hg t ht).trans ?_
    rw [XNorm00_const_eq]
  · refine le_iInf₂ fun G hG => ?_
    refine (iInf₂_le (fun t => G t ()) fun t ht => hG t ht () (mem_univ _)).trans ?_
    rw [← XNorm00_const_eq (V := Unit)]

theorem rn_le (θ : ℝ) {B : Set (Fin r → ℝ)} {f g : (Fin r → ℝ) → ℂ} (hg : ∀ t ∈ B, g t = f t) :
    rn θ B f ≤ timeFourierNorm θ g := by
  rw [rn_eq_iInf]
  exact iInf₂_le g hg

theorem rn_mono_set (θ : ℝ) {B B' : Set (Fin r → ℝ)} (h : B' ⊆ B) (f : (Fin r → ℝ) → ℂ) :
    rn θ B' f ≤ rn θ B f := by
  simp only [rn_eq_iInf]
  exact le_iInf₂ fun g hg => iInf₂_le g fun t ht => hg t (h ht)

theorem rn_congr (θ : ℝ) {B : Set (Fin r → ℝ)} {f f' : (Fin r → ℝ) → ℂ} (h : ∀ t ∈ B, f t = f' t) :
    rn θ B f = rn θ B f' := by
  simp only [rn_eq_iInf]
  refine iInf_congr fun g => iInf_congr_Prop ⟨fun hg t ht => (hg t ht).trans (h t ht),
    fun hg t ht => (hg t ht).trans (h t ht).symm⟩ fun _ => rfl

/-- One output of a vector restricted norm is at most the scalar restricted norm of that output. -/
theorem XNorm00Restr_single_le_rn {d : ℕ} (θ : ℝ) (B : Set (Fin r → ℝ)) (F : (Fin r → ℝ) → Mom d → ℂ)
    (k : Mom d) : XNorm00Restr θ B {k} F ≤ rn θ B (fun t => F t k) := by
  rw [rn_eq_iInf]
  refine le_iInf₂ fun g hg => ?_
  refine (iInf₂_le (fun t (_ : Mom d) => g t) fun t ht v hv => ?_).trans (XNorm00_const_eq θ g).le
  rw [Set.mem_singleton_iff.mp hv]
  exact hg t ht

/-- The gates' norms control every output, with the output weight `⟨k⟩^{Λ₂}`. -/
theorem rn_le_XNormRestr {d : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) (B : Set (Fin r → ℝ)) {K : Set (Mom d)}
    (F : (Fin r → ℝ) → Mom d → ℂ) {k : Mom d} (hk : k ∈ K) :
    ENNReal.ofReal (jbr k ^ Λ₂) * rn θ B (fun t => F t k) ≤ XNormRestr θ Λ₁ Λ₂ B K F := by
  classical
  unfold XNormRestr
  refine le_iInf₂ fun G hG => ?_
  have hrn : rn θ B (fun t => F t k) ≤ timeFourierNorm θ (fun t => G t k) :=
    rn_le θ fun t ht => hG t ht k hk
  refine (mul_le_mul' le_rfl hrn).trans ?_
  unfold XNorm
  by_cases hG' : (∀ k, Integrable fun t => G t k) ∧ (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT G lam))
  · rw [if_pos hG']
    have hz : (∑ _ : Fin d, (0 : ℕ)) ≤ Λ₁ := by simp
    refine le_trans ?_ (le_iSup_of_le (fun _ : Fin d => (0 : ℕ)) (le_iSup_of_le hz le_rfl))
    rw [timeFourierNorm_eq_lintegral (hG'.1 k), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun lam => ?_
    rw [NormBridgeScratch.maxBracketPow_eq_timeWeight, mul_left_comm]
    refine mul_le_mul' le_rfl ?_
    refine le_iSup_of_le k ?_
    rw [Induct.iterPartial_zero_index, NormBridgeScratch.timeFT_eq_timeFourier, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (pow_nonneg (zero_le_one.trans (Induct.one_le_jbr k)) _)]
  · rw [if_neg hG']
    exact le_top

/-! ### Products, traces, swaps -/

theorem rn_eq_mixed (θ : ℝ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → ℂ) :
    rn θ B f = mixedRestrictionNorm00 θ B (Set.univ : Set Unit) (fun t _ => f t) :=
  NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 θ B _ _

/-- **Product** (main's `mixedRestrictionNorm00_mul_le`): the second factor continuous. -/
theorem rn_mul_le {θ : ℝ} (hθ : 0 ≤ θ) {B : Set (Fin r → ℝ)} (hB : ∀ t ∈ B, t ∈ closure (interior B))
    (f g : (Fin r → ℝ) → ℂ) (hg : Continuous g) (hf : rn θ B f < ⊤) (hg' : rn θ B g < ⊤) :
    rn θ B (fun t => f t * g t) ≤ ENNReal.ofReal (2 ^ θ) * rn θ B f * rn θ B g := by
  rw [rn_eq_mixed] at hf hg' ⊢
  rw [rn_eq_mixed, rn_eq_mixed]
  exact Layered.mixedRestrictionNorm00_mul_le hθ hB Set.univ (fun t _ => f t) (fun t _ => g t)
    (fun _ _ => hg) hf hg'

/-- **Trace** (main's `XNorm00Restr_trace_cross`): freeze coordinate `j` at `c`. -/
theorem rn_trace {θ : ℝ} (hθ : 0 ≤ θ) (qt : Fin r → ℝ) {B Bt : Set (Fin r → ℝ)}
    (hBt : ∀ t ∈ Bt, ∀ i, t i ∈ Icc (qt i) (qt i + 1)) (h : (Fin r → ℝ) → ℂ) (hh : Continuous h) (j : Fin r)
    (c : ℝ) (hcl : ∀ t ∈ Bt, Function.update t j c ∈ closure (interior B)) :
    rn θ Bt (fun t => h (Function.update t j c)) ≤ Regref.traceConst (r := r) θ VineEstS3.chiUnit * rn θ B h :=
  VineEstS5C.P4.W13.XNorm00Restr_trace_cross hθ qt hBt (fun t _ => h t) (fun _ _ => hh) j c hcl

theorem traceConst_lt_top (θ : ℝ) : Regref.traceConst (r := r) θ VineEstS3.chiUnit < ⊤ :=
  lt_top_iff_ne_top.mpr (VineEstS3.traceConst_ne_top θ)

/-- The coordinate swap of two times. -/
def swap2 : Equiv.Perm (Fin 2) := Equiv.swap 0 1

theorem rn_swap (θ : ℝ) (B : Set (Fin 2 → ℝ)) (f : (Fin 2 → ℝ) → ℂ) :
    rn θ B (fun t => f (ConjCoh.permT swap2 t)) = rn θ (ConjCoh.permT swap2 ⁻¹' B) f := by
  have h1 := Represents.XNorm00Restr_swapConjV (π := swap2) (fun i => Equiv.swap_apply_self 0 1 i) θ B
    (Set.univ : Set Unit) (fun t _ => conj (f t))
  have h2 := VineEstS5C.P2.XNorm00Restr_conj θ (ConjCoh.permT swap2 ⁻¹' B) (Set.univ : Set Unit)
    (fun t _ => f t)
  unfold rn
  rw [← h2, ← h1]
  unfold Represents.swapConjV
  simp only [RCLike.conj_conj]

/-- **A continuous extension** with almost minimal norm, for a continuous function. -/
theorem exists_cont_ext {θ : ℝ} (hθ : 0 ≤ θ) {B : Set (Fin r → ℝ)} (hB : ∀ t ∈ B, t ∈ closure (interior B))
    {f : (Fin r → ℝ) → ℂ} (hf : Continuous f) (hfin : rn θ B f < ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) (hε' : ε ≠ ⊤) :
    ∃ g : (Fin r → ℝ) → ℂ, Continuous g ∧ (∀ t ∈ B, g t = f t) ∧ timeFourierNorm θ g < ⊤ ∧
      timeFourierNorm θ g ≤ rn θ B f + ε := by
  have hlt : rn θ B f < rn θ B f + ε := ENNReal.lt_add_right hfin.ne hε.ne'
  have hlt' : (⨅ (g : (Fin r → ℝ) → ℂ) (_ : ∀ t ∈ B, g t = f t), timeFourierNorm θ g) < rn θ B f + ε := by
    rw [← rn_eq_iInf]; exact hlt
  obtain ⟨g₀, hg₀⟩ := iInf_lt_iff.mp hlt'
  obtain ⟨hag, hg₀⟩ := iInf_lt_iff.mp hg₀
  have hg₀fin : timeFourierNorm θ g₀ < ⊤ := hg₀.trans (ENNReal.add_lt_top.2 ⟨hfin, lt_top_iff_ne_top.2 hε'⟩)
  obtain ⟨hc, -, hint, hft, -⟩ := Regref.rep_props hθ hg₀fin
  have hnorm : timeFourierNorm θ (Regref.rep g₀) = timeFourierNorm θ g₀ := by
    rw [timeFourierNorm_eq_lintegral hint, timeFourierNorm_eq_lintegral (integrable_of_timeFourierNorm_lt_top hg₀fin),
      hft]
  refine ⟨Regref.rep g₀, hc, fun t ht => Regref.rep_eq_of_mem_closure_interior hθ hg₀fin hag hf (hB t ht),
    hnorm ▸ hg₀fin, hnorm ▸ hg₀.le⟩

end WaveTurbulence.Flower.ProtPin
