/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.MirrorSum
public import WaveTurbulence.Foundations.Flower.ProtPin.RootKink
public import WaveTurbulence.Foundations.Flower.ProtPin.Pointwise
public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.MirrorMain

/-! # D3-MIRROR: the root trace in restricted norms (o104 Lemma 7.1(2), (P8))

For `ts = (T, σ)` in the triangle, `F(T, σ) = Σ'_i c_i ∫_σ^T e^{πiA_i(T-u)} Ks(u, σ) W_i(T, u) du` is the mirror operator
`T'_{A_i}` applied to `H_i(t, u, s) = Ks(u, s) W_i(t, u)`.

* `mirror_unit`, `mirror_shift`: `MirrorOperatorBoundY` (no spectators, one output) on the open triangle `triO p`.
* `mirF A Ks W` (one term), `continuous_mirF`, `mirF_rn_le`: on `triO p`, `rn(mirF) ≲ ‖kerH p gK gW‖ ≲ ‖gK‖ ‖gW‖` for
  extensions `gK`, `gW` of `Ks`, `W` from `timeBoxGt p p` (`kerH`: unit cutoffs in the missing clock, `MirrorTensor`).
* `mirror_ext`: a continuous extension `G` of `F` from the closed triangle `triC p` with
  `‖G‖ ≤ K₁ (K₀ (rn Ks + δ)(Σ|c_i| rn W_i + δ) + δ)` (each term extended continuously from `triO p` and so on its closure,
  the sum under the cutoff `cut2 p`, `tsum_cut_le`).
* **`mirror_tri`** (target (1)): the root trace on `timeBoxGt p p`.
* **`mirror_low`** (target (2)): the lower limit at the layer, on `timeBoxGt p q'`: the trace `σ = p` of `G` (`rn_trace`).
No hypothesis beyond the stated ones is added (`θ ≤ 1/4` is used only as `θ ≤ 1`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPin

/-! ### The mirror operator on the triangle of a layer -/

theorem append_nil3 (ts : Fin (0 + 2) → ℝ) (a u b : ℝ) :
    (Fin.append (fun i : Fin 0 => ts (Fin.castAdd 2 i)) ![a, u, b] : Fin (0 + 3) → ℝ) = ![a, u, b] := by
  funext j
  fin_cases j <;> rfl

/-- `MirrorOperatorBoundY` with no spectators and one output, on the unit triangle. -/
theorem mirror_unit {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (H : (Fin 3 → ℝ) → ℂ),
      rn θ {ts : Fin 2 → ℝ | 0 < ts 1 ∧ ts 1 < ts 0 ∧ ts 0 < 1}
        (fun ts => ∫ u in ts 1..ts 0, rootPh A (ts 0) u * H ![ts 0, u, ts 1]) ≤
        ENNReal.ofReal C * timeFourierNorm θ H := by
  obtain ⟨C, hC, hM⟩ := ProtOpsTerm.mirrorOperatorBoundY 0 0 θ hθ0 hθ1
  refine ⟨C, hC, fun A H => ?_⟩
  have h1 := (rn_le_XNormRestr θ 0 0 _ _ (Set.mem_univ (0 : Mom 0))).trans
    (hM A (fun x _ => H x) Set.univ)
  rw [pow_zero, ENNReal.ofReal_one, one_mul, NormBridgeScratch.XNorm_zero_eq_XNorm00,
    XNorm00_const_eq] at h1
  refine le_trans (le_of_eq (rn_congr θ fun ts _ => ?_)) h1
  show _ = ∫ u in ts 1..ts 0, Complex.exp (((Real.pi * A * (ts 0 - u)) : ℝ) * Complex.I) *
    H (Fin.append (fun i : Fin 0 => ts (Fin.castAdd 2 i)) ![ts 0, u, ts 1])
  simp only [append_nil3]
  rfl

/-- Translation of restricted norms. -/
theorem rn_shift_le {r : ℕ} (θ : ℝ) {B B' : Set (Fin r → ℝ)} {f f' : (Fin r → ℝ) → ℂ} (c : Fin r → ℝ)
    (hB : ∀ t ∈ B', t - c ∈ B) (hf : ∀ t ∈ B', f' t = f (t - c)) : rn θ B' f' ≤ rn θ B f :=
  Regref.XNorm00Restr_shift_le θ c hB fun t ht _ _ => hf t ht

theorem integral_Ioo_eq_interval {g : ℝ → ℂ} {a b : ℝ} (h : a ≤ b) :
    ∫ u in Ioo a b, g u = ∫ u in a..b, g u := by
  rw [intervalIntegral.integral_of_le h, integral_Ioc_eq_integral_Ioo]

/-- **The mirror operator on the open triangle of layer `p`.** -/
theorem mirror_shift {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p A : ℝ) (H : (Fin 3 → ℝ) → ℂ),
      rn θ (triO p) (fun ts => ∫ u in Ioo (ts 1) (ts 0), rootPh A (ts 0) u * H ![ts 0, u, ts 1]) ≤
        ENNReal.ofReal C * timeFourierNorm θ H := by
  obtain ⟨C, hC, hU⟩ := mirror_unit hθ0 hθ1
  refine ⟨C, hC, fun p A H => ?_⟩
  set H' : (Fin 3 → ℝ) → ℂ := fun x => H (x + fun _ => p) with hH'
  have hn : timeFourierNorm θ H' = timeFourierNorm θ H := timeFourierNorm_translate θ H _
  rw [← hn]
  refine le_trans (rn_shift_le θ (fun _ => p) (fun ts hts => ?_) (fun ts hts => ?_)) (hU A H')
  · obtain ⟨h1, h2, h3⟩ := hts
    show 0 < ts 1 - p ∧ ts 1 - p < ts 0 - p ∧ ts 0 - p < 1
    exact ⟨by linarith, by linarith, by linarith⟩
  · show _ = ∫ u in (ts 1 - p)..(ts 0 - p), rootPh A (ts 0 - p) u * H' ![ts 0 - p, u, ts 1 - p]
    rw [integral_Ioo_eq_interval hts.2.1.le, ← intervalIntegral.integral_comp_sub_right
      (fun u => rootPh A (ts 0 - p) u * H' ![ts 0 - p, u, ts 1 - p]) p]
    refine intervalIntegral.integral_congr fun u _ => ?_
    have e : (![ts 0 - p, u - p, ts 1 - p] + fun _ => p : Fin 3 → ℝ) = ![ts 0, u, ts 1] := by
      funext j
      fin_cases j <;> simp
    show rootPh A (ts 0) u * H ![ts 0, u, ts 1] =
      rootPh A (ts 0 - p) (u - p) * H (![ts 0 - p, u - p, ts 1 - p] + fun _ => p)
    rw [e]
    unfold rootPh
    rw [show ts 0 - p - (u - p) = ts 0 - u by ring]

/-! ### One term -/

/-- One term of the root trace. -/
def mirF (A : ℝ) (Ks W : (Fin 2 → ℝ) → ℂ) (ts : Fin 2 → ℝ) : ℂ :=
  ∫ u in Ioo (ts 1) (ts 0), rootPh A (ts 0) u * (Ks ![u, ts 1] * W ![ts 0, u])

theorem continuous_rootPh (A : ℝ) : Continuous (fun z : ℝ × ℝ => rootPh A z.1 z.2) := by
  have h : Continuous (fun z : ℝ × ℝ => Real.pi * A * (z.1 - z.2)) := by fun_prop
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp h).mul continuous_const)

theorem continuous_mirF (A : ℝ) {Ks W : (Fin 2 → ℝ) → ℂ} (hK : Continuous Ks) (hW : Continuous W) :
    Continuous (mirF A Ks W) := by
  set φ : (Fin 2 → ℝ) → ℝ → ℂ := fun ts u => rootPh A (ts 0) u * (Ks ![u, ts 1] * W ![ts 0, u]) with hφ
  have hφc : Continuous (Function.uncurry φ) := by
    have h1 : Continuous (fun z : (Fin 2 → ℝ) × ℝ => rootPh A (z.1 0) z.2) :=
      (continuous_rootPh A).comp (f := fun z : (Fin 2 → ℝ) × ℝ => (z.1 0, z.2)) (by fun_prop)
    have h2 : Continuous (fun z : (Fin 2 → ℝ) × ℝ => Ks ![z.2, z.1 1]) := hK.comp (by fun_prop)
    have h3 : Continuous (fun z : (Fin 2 → ℝ) × ℝ => W ![z.1 0, z.2]) := hW.comp (by fun_prop)
    exact h1.mul (h2.mul h3)
  have hii : ∀ ts (a b : ℝ), IntervalIntegrable (φ ts) volume a b := fun ts a b =>
    (hφc.uncurry_left ts).intervalIntegrable a b
  have e : mirF A Ks W =
      fun ts => (∫ u in (0 : ℝ)..ts 0, φ ts u) - ∫ u in (0 : ℝ)..min (ts 1) (ts 0), φ ts u := by
    funext ts
    rw [intervalIntegral.integral_interval_sub_left (hii ts _ _) (hii ts _ _)]
    unfold mirF
    rcases le_or_gt (ts 1) (ts 0) with h | h
    · rw [min_eq_left h, integral_Ioo_eq_interval h]
    · rw [min_eq_right h.le, intervalIntegral.integral_same, Ioo_eq_empty (not_lt.2 h.le),
        Measure.restrict_empty, integral_zero_measure]
  rw [e]
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hφc (continuous_apply 0)).sub
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hφc
      ((continuous_apply 1).min (continuous_apply 0)))

theorem vec_mem_box {p σ u : ℝ} (h1 : p ≤ σ) (h2 : σ < u) (h3 : u ≤ p + 1) :
    (![u, σ] : Fin 2 → ℝ) ∈ timeBoxGt p p := by
  show ((p ≤ u ∧ u ≤ p + 1) ∧ (p ≤ σ ∧ σ ≤ p + 1)) ∧ σ < u
  exact ⟨⟨⟨by linarith, h3⟩, ⟨h1, by linarith⟩⟩, h2⟩

/-- **One term on the open triangle**, through any two extensions of the factors. -/
theorem mirF_rn_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p A : ℝ) (Ks W gK gW : (Fin 2 → ℝ) → ℂ),
      (∀ x ∈ timeBoxGt p p, gK x = Ks x) → (∀ x ∈ timeBoxGt p p, gW x = W x) → Continuous gW →
      timeFourierNorm θ gK < ⊤ → timeFourierNorm θ gW < ⊤ →
      rn θ (triO p) (mirF A Ks W) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (2 ^ θ) * cutNorm θ ^ 2 * timeFourierNorm θ gK * timeFourierNorm θ gW) := by
  obtain ⟨C, hC, hM⟩ := mirror_shift hθ0 hθ1
  refine ⟨C, hC, fun p A Ks W gK gW hK hW hWc hKn hWn => ?_⟩
  refine le_trans (le_of_eq (rn_congr θ fun ts hts => ?_))
    ((hM p A (kerH p gK gW)).trans (mul_le_mul' le_rfl (kerH_norm_le hθ0 p hWc hKn hWn)))
  obtain ⟨h1, h2, h3⟩ := hts
  unfold mirF
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have hmK : (![u, ts 1] : Fin 2 → ℝ) ∈ timeBoxGt p p := vec_mem_box h1.le hu.1 (by linarith [hu.2])
  have hmW : (![ts 0, u] : Fin 2 → ℝ) ∈ timeBoxGt p p :=
    vec_mem_box (by linarith [hu.1]) hu.2 h3.le
  show rootPh A (ts 0) u * (Ks ![u, ts 1] * W ![ts 0, u]) =
    rootPh A (ts 0) u * ((cut1 p (fun _ => ts 0) * gK ![u, ts 1]) * (gW ![ts 0, u] * cut1 p (fun _ => ts 1)))
  rw [hK _ hmK, hW _ hmW, cut1_eq_one ⟨by linarith, h3.le⟩, cut1_eq_one ⟨h1.le, by linarith⟩]
  ring

/-! ### The extension of the whole sum -/

/-- **A continuous extension of the root trace from the closed triangle.** -/
theorem mirror_ext {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ K₀ K₁ : ℝ≥0∞, K₀ < ⊤ ∧ K₁ < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p : ℝ) (A : ι → ℝ) (c : ι → ℂ)
      (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), Continuous Ks → (∀ i, Continuous (W i)) →
      rn θ (timeBoxGt p p) Ks < ⊤ → (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) →
      (∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) < ⊤ → ∀ δ : ℝ≥0∞, 0 < δ → δ ≠ ⊤ →
      ∃ G : (Fin 2 → ℝ) → ℂ, Continuous G ∧
        (∀ ts ∈ triC p, G ts = ∑' i, c i * mirF (A i) Ks (W i) ts) ∧
        timeFourierNorm θ G ≤ K₁ * (K₀ * (rn θ (timeBoxGt p p) Ks + δ) *
          ((∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) + δ) + δ) := by
  obtain ⟨C, hC, hT⟩ := mirF_rn_le hθ0 hθ1
  set K₀ : ℝ≥0∞ := ENNReal.ofReal C * (ENNReal.ofReal (2 ^ θ) * cutNorm θ ^ 2) with hK₀
  have hK₀t : K₀ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top (cutNorm_lt_top θ)))
  refine ⟨K₀, ENNReal.ofReal (2 ^ θ) * cut2Norm θ, hK₀t,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (cut2Norm_lt_top θ), ?_⟩
  intro ι _ p A c Ks W hKc hWc hKfin hWfin hS δ hδ hδt
  set a := rn θ (timeBoxGt p p) Ks with ha
  set S := ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) with hSdef
  obtain ⟨gK, -, hgK, hgKfin, hgKle⟩ := exists_cont_ext hθ0 (timeBoxGt_cl p) hKc hKfin hδ hδt
  obtain ⟨w, hwpos, hwsum⟩ := ENNReal.exists_pos_sum_of_countable hδ.ne' ι
  set δi : ι → ℝ≥0∞ := fun i => (w i : ℝ≥0∞) / (‖c i‖ₑ + 1) with hδi
  have hδipos : ∀ i, 0 < δi i := fun i =>
    ENNReal.div_pos_iff.2 ⟨by exact_mod_cast (hwpos i).ne', by simp⟩
  have hδitop : ∀ i, δi i ≠ ⊤ := fun i => ENNReal.div_ne_top (by simp) (by simp)
  have hcδ : ∀ i, ‖c i‖ₑ * δi i ≤ (w i : ℝ≥0∞) := fun i => by
    rw [hδi]
    calc ‖c i‖ₑ * ((w i : ℝ≥0∞) / (‖c i‖ₑ + 1)) ≤ (‖c i‖ₑ + 1) * ((w i : ℝ≥0∞) / (‖c i‖ₑ + 1)) :=
          mul_le_mul' le_self_add le_rfl
      _ = (w i : ℝ≥0∞) := ENNReal.mul_div_cancel (by simp) (by simp)
  choose gW hgWc hgW hgWfin hgWle using fun i =>
    exists_cont_ext hθ0 (timeBoxGt_cl p) (hWc i) (hWfin i) (hδipos i) (hδitop i)
  have hTi : ∀ i, rn θ (triO p) (mirF (A i) Ks (W i)) ≤
      K₀ * timeFourierNorm θ gK * timeFourierNorm θ (gW i) := fun i =>
    (hT p (A i) Ks (W i) gK (gW i) hgK (hgW i) (hgWc i) hgKfin (hgWfin i)).trans (le_of_eq (by ring))
  have hTfin : ∀ i, rn θ (triO p) (mirF (A i) Ks (W i)) < ⊤ := fun i =>
    (hTi i).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hK₀t hgKfin) (hgWfin i))
  choose G hGc hG hGfin hGle using fun i =>
    exists_cont_ext hθ0 (triO_cl p) (continuous_mirF (A i) hKc (hWc i)) (hTfin i) (hδipos i) (hδitop i)
  have hGC : ∀ i, ∀ ts ∈ triC p, G i ts = mirF (A i) Ks (W i) ts := fun i ts hts =>
    Set.EqOn.closure (fun x hx => hG i x hx) (hGc i) (continuous_mirF (A i) hKc (hWc i))
      (triC_subset_closure p hts)
  have hGb : ∀ i, ‖c i‖ₑ * timeFourierNorm θ (G i) ≤
      K₀ * (a + δ) * (‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) + w i) + w i := fun i => by
    calc ‖c i‖ₑ * timeFourierNorm θ (G i)
        ≤ ‖c i‖ₑ * (K₀ * timeFourierNorm θ gK * timeFourierNorm θ (gW i) + δi i) :=
          mul_le_mul' le_rfl ((hGle i).trans (add_le_add (hTi i) le_rfl))
      _ ≤ ‖c i‖ₑ * (K₀ * (a + δ) * (rn θ (timeBoxGt p p) (W i) + δi i) + δi i) :=
          mul_le_mul' le_rfl (add_le_add (mul_le_mul' (mul_le_mul' le_rfl hgKle) (hgWle i)) le_rfl)
      _ = K₀ * (a + δ) * (‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) + ‖c i‖ₑ * δi i) + ‖c i‖ₑ * δi i := by ring
      _ ≤ K₀ * (a + δ) * (‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) + w i) + w i :=
          add_le_add (mul_le_mul' le_rfl (add_le_add le_rfl (hcδ i))) (hcδ i)
  have hsumG : ∑' i, ‖c i‖ₑ * timeFourierNorm θ (G i) ≤ K₀ * (a + δ) * (S + δ) + δ := by
    calc ∑' i, ‖c i‖ₑ * timeFourierNorm θ (G i)
        ≤ ∑' i, (K₀ * (a + δ) * (‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) + w i) + w i) :=
          ENNReal.tsum_le_tsum hGb
      _ = K₀ * (a + δ) * (S + ∑' i, (w i : ℝ≥0∞)) + ∑' i, (w i : ℝ≥0∞) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_add]
      _ ≤ K₀ * (a + δ) * (S + δ) + δ :=
          add_le_add (mul_le_mul' le_rfl (add_le_add le_rfl hwsum.le)) hwsum.le
  have hsumfin : ∑' i, ‖c i‖ₑ * timeFourierNorm θ (G i) < ⊤ :=
    hsumG.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top hK₀t
      (ENNReal.add_lt_top.2 ⟨hKfin, lt_top_iff_ne_top.2 hδt⟩))
      (ENNReal.add_lt_top.2 ⟨hS, lt_top_iff_ne_top.2 hδt⟩), lt_top_iff_ne_top.2 hδt⟩)
  obtain ⟨hGcont, hGnorm⟩ := tsum_cut_le hθ0 (continuous_cut2 p) (hasCompactSupport_cut2 p)
    (cut2_norm_lt_top θ p) c G hGc hGfin hsumfin
  refine ⟨_, hGcont, fun ts hts => ?_, ?_⟩
  · simp only [cut2_eq_one hts, one_mul]
    exact tsum_congr fun i => by rw [hGC i ts hts]
  · refine hGnorm.trans ?_
    rw [cut2_norm]
    exact mul_le_mul' le_rfl hsumG

/-! ### The targets -/

theorem rn_zero_of_eq {r : ℕ} (θ : ℝ) {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → ℂ} (h : ∀ t ∈ B, f t = 0) :
    rn θ B f = 0 := by
  refine le_antisymm ((rn_le θ (g := fun _ => (0 : ℂ)) fun t ht => (h t ht).symm).trans ?_) zero_le
  rw [timeFourierNorm_zero]

theorem const_add_one_ne_zero (K : ℝ≥0∞) : K + 1 ≠ 0 :=
  (zero_lt_one.trans_le le_add_self).ne'

open WaveTurbulence.Fourier in
/-- (1) The root trace on the triangle (port layer = object layer). -/
theorem mirror_tri {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p : ℝ) (A : ι → ℝ) (c : ι → ℂ)
      (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), Continuous Ks → (∀ i, Continuous (W i)) →
      rn θ (timeBoxGt p p) Ks < ⊤ → (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) →
      rn θ (timeBoxGt p p) (fun ts => ∑' i, c i * ∫ u in Set.Ioo (ts 1) (ts 0),
          rootPh (A i) (ts 0) u * (Ks ![u, ts 1] * W i ![ts 0, u])) ≤
        C * rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) := by
  obtain ⟨K₀, K₁, hK₀, hK₁, hE⟩ := mirror_ext hθ0 (by linarith)
  refine ⟨K₁ * K₀ + 1, ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top hK₁ hK₀, ENNReal.one_lt_top⟩, ?_⟩
  intro ι _ p A c Ks W hKc hWc hKfin hWfin
  by_cases ha0 : rn θ (timeBoxGt p p) Ks = 0
  · rw [rn_zero_of_eq θ fun ts hts => ?_]
    · exact zero_le
    refine (tsum_congr fun i => ?_).trans tsum_zero
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℂ)) fun u hu => ?_]
    · simp
    have hm := vec_mem_box hts.1.2.1 hu.1 (hu.2.le.trans hts.1.1.2)
    have h0 := enorm_le_rn hθ0 (timeBoxGt_cl p) hKc hm
    rw [ha0, nonpos_iff_eq_zero, enorm_eq_zero] at h0
    simp only [h0, zero_mul, mul_zero]
  by_cases hSt : (∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) = ⊤
  · rw [hSt, ENNReal.mul_top (mul_ne_zero (const_add_one_ne_zero _) ha0)]
    exact le_top
  have key : rn θ (timeBoxGt p p) (fun ts => ∑' i, c i * mirF (A i) Ks (W i) ts) ≤
      K₁ * K₀ * rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) :=
    le_of_slack hK₀.ne hK₁.ne hKfin.ne hSt fun δ hδ hδt => by
      obtain ⟨G, -, hG, hGn⟩ := hE ι p A c Ks W hKc hWc hKfin hWfin (lt_top_iff_ne_top.2 hSt) δ hδ hδt
      exact (rn_le θ fun ts hts => hG ts (timeBoxGt_subset_triC p hts)).trans hGn
  refine key.trans ?_
  gcongr
  exact le_self_add

open WaveTurbulence.Fourier in
/-- (2) The root trace with the lower limit at the layer (port layer below the object layer). -/
theorem mirror_low {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p q' : ℝ) (A : ι → ℝ) (c : ι → ℂ)
      (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), Continuous Ks → (∀ i, Continuous (W i)) →
      rn θ (timeBoxGt p p) Ks < ⊤ → (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) →
      rn θ (timeBoxGt p q') (fun ts => ∑' i, c i * ∫ u in Set.Ioo p (ts 0),
          rootPh (A i) (ts 0) u * (Ks ![u, p] * W i ![ts 0, u])) ≤
        C * rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) := by
  obtain ⟨K₀, K₁, hK₀, hK₁, hE⟩ := mirror_ext hθ0 (by linarith)
  set Ct := Regref.traceConst (r := 2) θ VineEstS3.chiUnit with hCt
  have hCtt : Ct < ⊤ := traceConst_lt_top θ
  refine ⟨Ct * K₁ * K₀ + 1, ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top hCtt hK₁) hK₀,
    ENNReal.one_lt_top⟩, ?_⟩
  intro ι _ p q' A c Ks W hKc hWc hKfin hWfin
  by_cases ha0 : rn θ (timeBoxGt p p) Ks = 0
  · rw [rn_zero_of_eq θ fun ts hts => ?_]
    · exact zero_le
    refine (tsum_congr fun i => ?_).trans tsum_zero
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℂ)) fun u hu => ?_]
    · simp
    have hm := vec_mem_box le_rfl hu.1 (hu.2.le.trans hts.1.1.2)
    have h0 := enorm_le_rn hθ0 (timeBoxGt_cl p) hKc hm
    rw [ha0, nonpos_iff_eq_zero, enorm_eq_zero] at h0
    simp only [h0, zero_mul, mul_zero]
  by_cases hSt : (∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) = ⊤
  · rw [hSt, ENNReal.mul_top (mul_ne_zero (const_add_one_ne_zero _) ha0)]
    exact le_top
  have key : rn θ (timeBoxGt p q') (fun ts => ∑' i, c i * ∫ u in Set.Ioo p (ts 0),
          rootPh (A i) (ts 0) u * (Ks ![u, p] * W i ![ts 0, u])) ≤
      Ct * K₁ * K₀ * rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) :=
    le_of_slack (K₁ := Ct * K₁) hK₀.ne (ENNReal.mul_lt_top hCtt hK₁).ne hKfin.ne hSt fun δ hδ hδt => by
      obtain ⟨G, hGc, hG, hGn⟩ := hE ι p A c Ks W hKc hWc hKfin hWfin (lt_top_iff_ne_top.2 hSt) δ hδ hδt
      have htr := rn_trace hθ0 ![p, q'] (B := Set.univ) (Bt := timeBoxGt p q')
        (fun t ht i => by
          fin_cases i
          · exact ht.1.1
          · exact ht.1.2) G hGc 1 p (fun t _ => by simp)
      have heq : ∀ t ∈ timeBoxGt p q', (∑' i, c i * ∫ u in Set.Ioo p (t 0),
          rootPh (A i) (t 0) u * (Ks ![u, p] * W i ![t 0, u])) = G (Function.update t 1 p) := by
        intro t ht
        have hmem : Function.update t 1 p ∈ triC p := by
          show p ≤ Function.update t 1 p 1 ∧ Function.update t 1 p 1 ≤ Function.update t 1 p 0 ∧
            Function.update t 1 p 0 ≤ p + 1
          simp only [Function.update_self, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne]
          exact ⟨le_rfl, ht.1.1.1, ht.1.1.2⟩
        rw [hG _ hmem]
        refine tsum_congr fun i => ?_
        simp only [mirF, Function.update_self, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne]
      calc rn θ (timeBoxGt p q') (fun ts => ∑' i, c i * ∫ u in Set.Ioo p (ts 0),
            rootPh (A i) (ts 0) u * (Ks ![u, p] * W i ![ts 0, u]))
          = rn θ (timeBoxGt p q') (fun t => G (Function.update t 1 p)) := rn_congr θ heq
        _ ≤ Ct * rn θ Set.univ G := htr
        _ ≤ Ct * timeFourierNorm θ G := mul_le_mul' le_rfl (rn_le θ fun _ _ => rfl)
        _ ≤ Ct * (K₁ * (K₀ * (rn θ (timeBoxGt p p) Ks + δ) *
              ((∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) + δ) + δ)) := mul_le_mul' le_rfl hGn
        _ = Ct * K₁ * (K₀ * (rn θ (timeBoxGt p p) Ks + δ) *
              ((∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) + δ) + δ) := by ring
  refine key.trans ?_
  gcongr
  exact le_self_add

/-! ### The targets, restated verbatim (D3-MIRROR brief) -/

open WaveTurbulence.Fourier in
example {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p : ℝ) (A : ι → ℝ) (c : ι → ℂ)
      (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), Continuous Ks → (∀ i, Continuous (W i)) →
      rn θ (timeBoxGt p p) Ks < ⊤ → (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) →
      rn θ (timeBoxGt p p) (fun ts => ∑' i, c i * ∫ u in Set.Ioo (ts 1) (ts 0),
          rootPh (A i) (ts 0) u * (Ks ![u, ts 1] * W i ![ts 0, u])) ≤
        C * rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) :=
  mirror_tri hθ0 hθ1

open WaveTurbulence.Fourier in
example {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p q' : ℝ) (A : ι → ℝ) (c : ι → ℂ)
      (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), Continuous Ks → (∀ i, Continuous (W i)) →
      rn θ (timeBoxGt p p) Ks < ⊤ → (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) →
      rn θ (timeBoxGt p q') (fun ts => ∑' i, c i * ∫ u in Set.Ioo p (ts 0),
          rootPh (A i) (ts 0) u * (Ks ![u, p] * W i ![ts 0, u])) ≤
        C * rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) :=
  mirror_low hθ0 hθ1

end WaveTurbulence.Flower.ProtPin
