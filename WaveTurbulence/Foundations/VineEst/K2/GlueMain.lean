/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.KernelNorm
public import WaveTurbulence.Foundations.VineEst.K2.Produce

/-! # W2-KIND2 Lemma A (8): the clamp gluing `𝔛^{1-η} → 𝔛^{1-2η}` on two adjacent windows

`clampGlueC`, `clampGlueT`: `ClampGlueC η CA`, `ClampGlueT η CA` with `CA = Ck(η) < ∞` for `0 < η < 1/4`
(TARGET L1917-L1918).  Four cases for the gate level `q` against the windows `w, w+1`: above both (`q + 1 ≤ w`, constant `J(q+1, ·)`),
`q = w` (kink `min(t, w+1)`), `q = w + 1` (kink `max(t, w+1)`), below both (`w + 2 ≤ q`, constant `J(q, ·)`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open MeasureTheory Set Filter Topology WaveTurbulence.Fourier WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.P4.W13
open scoped ENNReal

theorem cut0_zero_of {x : ℝ} (hx : x ≤ -1 ∨ 3 ≤ x) : cut0 x = 0 := by
  unfold cut0
  have : bump0.rOut ≤ dist x 1 := by
    rw [Real.dist_eq]
    show (2 : ℝ) ≤ |x - 1|
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  simp [bump0.zero_of_le_dist this]

theorem cut1_zero_of {x : ℝ} (hx : x ≤ -1 / 2 ∨ 3 / 2 ≤ x) : cut1 x = 0 := by
  unfold cut1
  have h : WaveTurbulence.Layered.chiUnit x = 0 := FS.chiUnit_eq_zero hx
  have h' : WaveTurbulence.VineEstS3.chiUnit x = 0 := h
  simp [h']

/-- The two-variable cutoff. -/
noncomputable def kap (w b : ℝ) (t : Fin 2 → ℝ) : ℂ := cut0 (t 0 - w) * cut1 (t 1 - b)

theorem kap_continuous (w b : ℝ) : Continuous (kap w b) := by
  unfold kap
  have h0 : Continuous cut0 := cut0_contDiff.continuous
  have h1 : Continuous cut1 := cut1_contDiff.continuous
  exact (h0.comp ((continuous_apply 0).sub continuous_const)).mul (h1.comp ((continuous_apply 1).sub continuous_const))

theorem kap_compact (w b : ℝ) : HasCompactSupport (kap w b) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Icc ![w - 1, b - 1 / 2] ![w + 3, b + 3 / 2]) isCompact_Icc ?_
  intro t ht
  by_contra hnot
  apply ht
  unfold kap
  simp only [mem_Icc, Pi.le_def, not_and_or, not_forall, not_le] at hnot
  rcases hnot with ⟨i, hi⟩ | ⟨i, hi⟩
  · fin_cases i
    · simp at hi
      rw [cut0_zero_of (Or.inl (by linarith))]; simp
    · simp at hi
      rw [cut1_zero_of (Or.inl (by linarith))]; simp
  · fin_cases i
    · simp at hi
      rw [cut0_zero_of (Or.inr (by linarith))]; simp
    · simp at hi
      rw [cut1_zero_of (Or.inr (by linarith))]; simp

theorem kap_eq_one {w b : ℝ} {t : Fin 2 → ℝ} (h0 : t 0 ∈ Icc w (w + 2)) (h1 : t 1 ∈ Icc b (b + 1)) : kap w b t = 1 := by
  unfold kap
  rw [cut0_eq_one ⟨by linarith [h0.1], by linarith [h0.2]⟩, cut1_eq_one ⟨by linarith [h1.1], by linarith [h1.2]⟩]
  simp


/-- The reparametrisation of the four cases. -/
noncomputable def phiK (w c0 sa sb : ℝ) (x : ℝ) : ℝ := c0 + sa * min (x - (w + 1)) 0 + sb * max (x - (w + 1)) 0

theorem phiK_continuous (w c0 sa sb : ℝ) : Continuous (phiK w c0 sa sb) := by
  unfold phiK; fun_prop

theorem glue_box {η : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4) :
    ∃ Ck : ℝ, 0 < Ck ∧ ∀ (w b c0 sa sb : ℝ), (sa = 0 ∨ sb = 0) → |sa| ≤ 1 → |sb| ≤ 1 →
      ∀ {T B2 : Set (Fin 2 → ℝ)} {J Y : (Fin 2 → ℝ) → ℂ}, Continuous J → ∀ {X : ℝ},
      XNorm00Restr (V := Unit) (1 - η) T Set.univ (fun ts _ => J ts) ≤ ENNReal.ofReal X →
      (∀ ts ∈ B2, ts 0 ∈ Icc w (w + 2) ∧ ts 1 ∈ Icc b (b + 1) ∧
        ![phiK w c0 sa sb (ts 0), ts 1] ∈ closure (interior T) ∧ Y ts = J ![phiK w c0 sa sb (ts 0), ts 1]) →
      XNorm00Restr (V := Unit) (1 - 2 * η) B2 Set.univ (fun ts _ => Y ts) ≤ ENNReal.ofReal Ck * ENNReal.ofReal X := by
  obtain ⟨Ck, hCk, hK⟩ := kernel_norm (θ := 1 - 2 * η) (δ := η) (by linarith) hη0 (by linarith)
  refine ⟨Ck, hCk, fun w b c0 sa sb hs hsa hsb T B2 J Y hJ X hTX hB => ?_⟩
  have hker : ∀ ξ : Fin 2 → ℝ, timeFourierNorm (1 - 2 * η) (fun t => kap w b t * eE (ξ 0 * phiK w c0 sa sb (t 0) + ξ 1 * t 1)) ≤
      ENNReal.ofReal Ck * ENNReal.ofReal (timeBracket ξ ^ (1 - η)) := by
    intro ξ
    have h := hK w b c0 sa sb ξ hs hsa hsb
    rw [show (1 - 2 * η) + η = 1 - η by ring] at h
    rw [← ENNReal.ofReal_mul hCk.le]
    exact h
  have hCk0 : ENNReal.ofReal Ck ≠ 0 := by simpa using hCk
  refine (glue_core (by linarith) (kap_compact w b) (kap_continuous w b) (phiK_continuous w c0 sa sb) hCk0
    ENNReal.ofReal_ne_top hker hJ (fun ts hts => ?_)).trans (mul_le_mul' le_rfl hTX)
  obtain ⟨h0, h1, h2, h3⟩ := hB ts hts
  exact ⟨kap_eq_one h0 h1, h2, h3⟩


theorem phiK_min (w x : ℝ) : phiK w (w + 1) 1 0 x = min x (w + 1) := by
  unfold phiK
  rcases le_total x (w + 1) with h | h
  · rw [min_eq_left (by linarith : x - (w + 1) ≤ 0), min_eq_left h]; ring
  · rw [min_eq_right (by linarith : 0 ≤ x - (w + 1)), min_eq_right h]; ring

theorem phiK_max (w x : ℝ) : phiK w (w + 1) 0 1 x = max x (w + 1) := by
  unfold phiK
  rcases le_total x (w + 1) with h | h
  · rw [max_eq_right (by linarith : x - (w + 1) ≤ 0), max_eq_right h]; ring
  · rw [max_eq_left (by linarith : 0 ≤ x - (w + 1)), max_eq_left h]; ring

theorem mem_B2_C {w L2 : ℕ} {ts : Fin 2 → ℝ} (h : ts ∈ timeBox (w : ℝ) L2 ∪ timeBox ((w + 1 : ℕ) : ℝ) L2) :
    ts 0 ∈ Icc (w : ℝ) (w + 2) ∧ ts 1 ∈ Icc (L2 : ℝ) (L2 + 1) := by
  push_cast at h
  rcases h with h | h
  · exact ⟨⟨h.1.1, by linarith [h.1.2]⟩, h.2⟩
  · exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩, h.2⟩

theorem mem_B2_T {w L2 : ℕ} {ts : Fin 2 → ℝ} (h : ts ∈ timeBoxGt (w : ℝ) L2 ∪ timeBoxGt ((w + 1 : ℕ) : ℝ) L2) :
    ts 0 ∈ Icc (w : ℝ) (w + 2) ∧ ts 1 ∈ Icc (L2 : ℝ) (L2 + 1) ∧ ts 1 < ts 0 := by
  push_cast at h
  rcases h with h | h
  · exact ⟨⟨h.1.1.1, by linarith [h.1.1.2]⟩, h.1.2, h.2⟩
  · exact ⟨⟨by linarith [h.1.1.1], by linarith [h.1.1.2]⟩, h.1.2, h.2⟩

theorem pt_mem_box {q L2 x s : ℝ} (hx : x ∈ Icc q (q + 1)) (hs : s ∈ Icc L2 (L2 + 1)) :
    ![x, s] ∈ closure (interior (timeBox q L2)) :=
  timeBox_subset_closure_interior _ _ ⟨by simpa using hx, by simpa using hs⟩

theorem clamp2_eq_of {q : ℝ} {Jc : (Fin 2 → ℝ) → ℂ} {ts : Fin 2 → ℝ} {x : ℝ} (hx : x = max (min (ts 0) (q + 1)) q) :
    clamp2J q Jc ts = Jc ![x, ts 1] := by
  unfold clamp2J; rw [hx]

theorem clampGlueC {η : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4) : ∃ CA : ℝ≥0∞, CA ≠ ⊤ ∧ ClampGlueC η CA := by
  obtain ⟨Ck, hCk, hbox⟩ := glue_box hη0 hη4
  refine ⟨ENNReal.ofReal Ck, ENNReal.ofReal_ne_top, ?_⟩
  intro q w L2 hL2q hL2w Jc hJc X hX hJ
  rcases (by omega : q + 1 ≤ w ∨ q = w ∨ q = w + 1 ∨ w + 2 ≤ q) with h | h | h | h
  · -- both windows above the gate: constant J(q+1, ·)
    have hq : (q : ℝ) + 1 ≤ w := by exact_mod_cast h
    refine hbox (w : ℝ) (L2 : ℝ) ((q : ℝ) + 1) 0 0 (Or.inl rfl) (by simp) (by simp) hJc hJ (fun ts hts => ?_)
    obtain ⟨h0, h1⟩ := mem_B2_C hts
    refine ⟨h0, h1, ?_, ?_⟩
    · have : phiK (w : ℝ) ((q : ℝ) + 1) 0 0 (ts 0) = (q : ℝ) + 1 := by simp [phiK]
      rw [this]; exact pt_mem_box ⟨by linarith, le_rfl⟩ h1
    · have : phiK (w : ℝ) ((q : ℝ) + 1) 0 0 (ts 0) = (q : ℝ) + 1 := by simp [phiK]
      rw [this]
      refine clamp2_eq_of ?_
      rw [min_eq_right (by linarith [h0.1]), max_eq_left (by linarith)]
  · subst h
    refine hbox (q : ℝ) (L2 : ℝ) ((q : ℝ) + 1) 1 0 (Or.inr rfl) (by simp) (by simp) hJc hJ (fun ts hts => ?_)
    obtain ⟨h0, h1⟩ := mem_B2_C hts
    have hphi : phiK (q : ℝ) ((q : ℝ) + 1) 1 0 (ts 0) = min (ts 0) ((q : ℝ) + 1) := phiK_min _ _
    refine ⟨h0, h1, ?_, ?_⟩
    · rw [hphi]; exact pt_mem_box ⟨le_min h0.1 (by linarith), min_le_right _ _⟩ h1
    · rw [hphi]
      refine clamp2_eq_of ?_
      rw [max_eq_left (le_min h0.1 (by linarith))]
  · subst h
    refine hbox (w : ℝ) (L2 : ℝ) ((w : ℝ) + 1) 0 1 (Or.inl rfl) (by simp) (by simp) hJc hJ (fun ts hts => ?_)
    obtain ⟨h0, h1⟩ := mem_B2_C hts
    have hphi : phiK (w : ℝ) ((w : ℝ) + 1) 0 1 (ts 0) = max (ts 0) ((w : ℝ) + 1) := phiK_max _ _
    have hq : (((w + 1 : ℕ)) : ℝ) = (w : ℝ) + 1 := by push_cast; ring
    refine ⟨h0, h1, ?_, ?_⟩
    · rw [hq, hphi]; exact pt_mem_box ⟨le_max_right _ _, max_le (by linarith [h0.2]) (by linarith)⟩ h1
    · rw [hq, hphi]
      refine clamp2_eq_of ?_
      rw [min_eq_left (by linarith [h0.2])]
  · have hq : (w : ℝ) + 2 ≤ q := by exact_mod_cast h
    refine hbox (w : ℝ) (L2 : ℝ) (q : ℝ) 0 0 (Or.inl rfl) (by simp) (by simp) hJc hJ (fun ts hts => ?_)
    obtain ⟨h0, h1⟩ := mem_B2_C hts
    have hphi : phiK (w : ℝ) (q : ℝ) 0 0 (ts 0) = (q : ℝ) := by simp [phiK]
    refine ⟨h0, h1, ?_, ?_⟩
    · rw [hphi]; exact pt_mem_box ⟨le_rfl, by linarith⟩ h1
    · rw [hphi]
      refine clamp2_eq_of ?_
      rw [min_eq_left (by linarith [h0.2]), max_eq_right (by linarith [h0.2])]


theorem pt_mem_boxGt {q L2 x s : ℝ} (hq : L2 ≤ q) (hx : x ∈ Icc q (q + 1)) (hs : s ∈ Icc L2 (L2 + 1)) (hsx : s < x) :
    ![x, s] ∈ closure (interior (timeBoxGt q L2)) :=
  timeBoxGt_subset_closure_interior hq ⟨⟨by simpa using hx, by simpa using hs⟩, by simpa using hsx⟩

theorem clampGlueT {η : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4) : ∃ CA : ℝ≥0∞, CA ≠ ⊤ ∧ ClampGlueT η CA := by
  obtain ⟨Ck, hCk, hbox⟩ := glue_box hη0 hη4
  refine ⟨ENNReal.ofReal Ck, ENNReal.ofReal_ne_top, ?_⟩
  intro q w L2 hL2q hL2w Jc hJc X hX hJ
  have hL2q' : (L2 : ℝ) ≤ q := by exact_mod_cast hL2q
  have hL2w' : (L2 : ℝ) ≤ w := by exact_mod_cast hL2w
  rcases (by omega : q + 1 ≤ w ∨ q = w ∨ q = w + 1 ∨ w + 2 ≤ q) with h | h | h | h
  · have hq : (q : ℝ) + 1 ≤ w := by exact_mod_cast h
    refine hbox (w : ℝ) (L2 : ℝ) ((q : ℝ) + 1) 0 0 (Or.inl rfl) (by simp) (by simp) hJc hJ (fun ts hts => ?_)
    obtain ⟨h0, h1, hlt⟩ := mem_B2_T hts
    have hphi : phiK (w : ℝ) ((q : ℝ) + 1) 0 0 (ts 0) = (q : ℝ) + 1 := by simp [phiK]
    refine ⟨h0, h1, ?_, ?_⟩
    · rw [hphi]
      exact gt_trace_mem hL2q' h1.1 h1.2
    · rw [hphi]
      refine clamp2_eq_of ?_
      rw [min_eq_right (by linarith [h0.1]), max_eq_left (by linarith)]
  · subst h
    refine hbox (q : ℝ) (L2 : ℝ) ((q : ℝ) + 1) 1 0 (Or.inr rfl) (by simp) (by simp) hJc hJ (fun ts hts => ?_)
    obtain ⟨h0, h1, hlt⟩ := mem_B2_T hts
    have hphi : phiK (q : ℝ) ((q : ℝ) + 1) 1 0 (ts 0) = min (ts 0) ((q : ℝ) + 1) := phiK_min _ _
    refine ⟨h0, h1, ?_, ?_⟩
    · rw [hphi]
      rcases le_total (ts 0) ((q : ℝ) + 1) with h2 | h2
      · rw [min_eq_left h2]; exact pt_mem_boxGt hL2q' ⟨h0.1, h2⟩ h1 hlt
      · rw [min_eq_right h2]; exact gt_trace_mem hL2q' h1.1 h1.2
    · rw [hphi]
      refine clamp2_eq_of ?_
      rw [max_eq_left (le_min h0.1 (by linarith))]
  · subst h
    refine hbox (w : ℝ) (L2 : ℝ) ((w : ℝ) + 1) 0 1 (Or.inl rfl) (by simp) (by simp) hJc hJ (fun ts hts => ?_)
    obtain ⟨h0, h1, hlt⟩ := mem_B2_T hts
    have hphi : phiK (w : ℝ) ((w : ℝ) + 1) 0 1 (ts 0) = max (ts 0) ((w : ℝ) + 1) := phiK_max _ _
    have hq : (((w + 1 : ℕ)) : ℝ) = (w : ℝ) + 1 := by push_cast; ring
    refine ⟨h0, h1, ?_, ?_⟩
    · rw [hq, hphi]
      rcases le_total (ts 0) ((w : ℝ) + 1) with h2 | h2
      · rw [max_eq_right h2]
        exact gt_trace_mem_q (by linarith) h1.1 h1.2 (by linarith [h1.2])
      · rw [max_eq_left h2]; exact pt_mem_boxGt (by linarith) ⟨h2, by linarith [h0.2]⟩ h1 hlt
    · rw [hq, hphi]
      refine clamp2_eq_of ?_
      rw [min_eq_left (by linarith [h0.2])]
  · have hq : (w : ℝ) + 2 ≤ q := by exact_mod_cast h
    refine hbox (w : ℝ) (L2 : ℝ) (q : ℝ) 0 0 (Or.inl rfl) (by simp) (by simp) hJc hJ (fun ts hts => ?_)
    obtain ⟨h0, h1, hlt⟩ := mem_B2_T hts
    have hphi : phiK (w : ℝ) (q : ℝ) 0 0 (ts 0) = (q : ℝ) := by simp [phiK]
    refine ⟨h0, h1, ?_, ?_⟩
    · rw [hphi]
      exact gt_trace_mem_q hL2q' h1.1 h1.2 (by linarith [h1.2])
    · rw [hphi]
      refine clamp2_eq_of ?_
      rw [min_eq_left (by linarith [h0.2]), max_eq_right (by linarith [h0.2])]

end WaveTurbulence.VineEstS5C.P4.W2.K2
