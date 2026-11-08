/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.MirrorTri
public import WaveTurbulence.Foundations.Flower.ProtOpsSlot.Slots

/-! # D3-MIRROR: the root trace at a fixed port time and its integral (targets (3), (4), for (P4) with a prefix)

`mirror_at`: for `p ≤ s ≤ p + 1`, the function of the upper clock `T ↦ Σ'_i c_i ∫_s^T e^{πiA_i(T-u)} Ks(u, s) W_i(T, u) du`
on the window `T ∈ [s, p+1]` has restricted norm `≲ rn(Ks) Σ_i |c_i| rn(W_i)` (norms on `timeBoxGt p p`), uniformly in
the `A_i`. It is the slice `σ = s` of the continuous extension `G` of `mirror_ext` (the points `(T, s)` lie in the closed
triangle `triC p`), bounded by `FixedSlotBound` (`ProtOpsSlot.fixedSlotBound`, one free time, no spectators, one output:
`slot_unit`) on the window `[p, p+1] ⊇ [s, p+1]`.

`mirror_int` (target (4)): `T ↦ ∫_s^T R(ρ) dρ` (zero for `T ≤ s`) on `win p`, `R` the function of (3). The slice
`ρ ↦ G(ρ, s)` has a continuous extension `E` from `win p` (`slot_unit`, `exists_cont_ext`); `termKink_sum` with one
index, `A = 0` and `h(T, ρ) = χ(T) E(ρ)` (`timeFourierNorm_tensor2_le`) gives the extension of the integral.
No hypothesis is added (`θ ≤ 1/4` is used as `θ ≤ 1` and `θ ≤ 1/2`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPin

theorem snoc_eq_vec (y : Fin 1 → ℝ) (a : ℝ) : (Fin.snoc y a : Fin (1 + 1) → ℝ) = ![y 0, a] := by
  funext j
  fin_cases j <;> rfl

/-- `FixedSlotBound` with one free time, no spectators, one output. -/
theorem slot_unit {θ : ℝ} (hθ0 : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q a : ℝ) (G : (Fin 2 → ℝ) → ℂ), Continuous G →
      rn θ (Set.pi univ fun _ => Icc q (q + 1)) (fun y : Fin 1 → ℝ => G ![y 0, a]) ≤
        ENNReal.ofReal C * timeFourierNorm θ G := by
  obtain ⟨C, hC, hM⟩ := ProtOpsSlot.fixedSlotBound 0 1 θ hθ0
  refine ⟨C, hC, fun q a G hG => ?_⟩
  have h1 := (rn_le_XNormRestr θ 0 0 _ _ (Set.mem_univ (0 : Mom 0))).trans
    (hM q a (fun x _ => G x) Set.univ fun _ => hG)
  rw [pow_zero, ENNReal.ofReal_one, one_mul, NormBridgeScratch.XNorm_zero_eq_XNorm00,
    XNorm00_const_eq] at h1
  refine le_trans (le_of_eq (rn_congr θ fun y _ => ?_)) h1
  show G ![y 0, a] = G (Fin.snoc y a)
  rw [snoc_eq_vec]

open WaveTurbulence.Fourier in
/-- (3) The root trace at a fixed port time `s`, upper clock in `[s, p+1]`. -/
theorem mirror_at {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p s : ℝ), p ≤ s → s ≤ p + 1 → ∀ (A : ι → ℝ) (c : ι → ℂ)
      (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), Continuous Ks → (∀ i, Continuous (W i)) →
      rn θ (timeBoxGt p p) Ks < ⊤ → (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) →
      rn θ {T : Fin 1 → ℝ | T 0 ∈ Set.Icc s (p + 1)} (fun T => ∑' i, c i * ∫ u in Set.Ioo s (T 0),
          rootPh (A i) (T 0) u * (Ks ![u, s] * W i ![T 0, u])) ≤
        C * rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) := by
  obtain ⟨K₀, K₁, hK₀, hK₁, hE⟩ := mirror_ext hθ0 (by linarith)
  obtain ⟨Cs, -, hSl⟩ := slot_unit hθ0
  refine ⟨ENNReal.ofReal Cs * K₁ * K₀ + 1, ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK₁) hK₀, ENNReal.one_lt_top⟩, ?_⟩
  intro ι _ p s hps hsp A c Ks W hKc hWc hKfin hWfin
  by_cases ha0 : rn θ (timeBoxGt p p) Ks = 0
  · rw [rn_zero_of_eq θ fun T hT => ?_]
    · exact zero_le
    refine (tsum_congr fun i => ?_).trans tsum_zero
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℂ)) fun u hu => ?_]
    · simp
    have hm := vec_mem_box hps hu.1 (hu.2.le.trans hT.2)
    have h0 := enorm_le_rn hθ0 (timeBoxGt_cl p) hKc hm
    rw [ha0, nonpos_iff_eq_zero, enorm_eq_zero] at h0
    simp only [h0, zero_mul, mul_zero]
  by_cases hSt : (∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) = ⊤
  · rw [hSt, ENNReal.mul_top (mul_ne_zero (const_add_one_ne_zero _) ha0)]
    exact le_top
  have key : rn θ {T : Fin 1 → ℝ | T 0 ∈ Set.Icc s (p + 1)} (fun T => ∑' i, c i * ∫ u in Set.Ioo s (T 0),
          rootPh (A i) (T 0) u * (Ks ![u, s] * W i ![T 0, u])) ≤
      ENNReal.ofReal Cs * K₁ * K₀ * rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) :=
    le_of_slack (K₁ := ENNReal.ofReal Cs * K₁) hK₀.ne (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK₁).ne
      hKfin.ne hSt fun δ hδ hδt => by
      obtain ⟨G, hGc, hG, hGn⟩ := hE ι p A c Ks W hKc hWc hKfin hWfin (lt_top_iff_ne_top.2 hSt) δ hδ hδt
      have heq : ∀ T ∈ {T : Fin 1 → ℝ | T 0 ∈ Set.Icc s (p + 1)}, (∑' i, c i * ∫ u in Set.Ioo s (T 0),
          rootPh (A i) (T 0) u * (Ks ![u, s] * W i ![T 0, u])) = G ![T 0, s] := by
        intro T hT
        have hmem : (![T 0, s] : Fin 2 → ℝ) ∈ triC p := by
          show p ≤ s ∧ s ≤ T 0 ∧ T 0 ≤ p + 1
          exact ⟨hps, hT.1, hT.2⟩
        rw [hG _ hmem]
        rfl
      have hsub : {T : Fin 1 → ℝ | T 0 ∈ Set.Icc s (p + 1)} ⊆ Set.pi univ fun _ => Icc p (p + 1) :=
        fun T hT j _ => by
          fin_cases j
          exact ⟨hps.trans hT.1, hT.2⟩
      calc rn θ {T : Fin 1 → ℝ | T 0 ∈ Set.Icc s (p + 1)} (fun T => ∑' i, c i * ∫ u in Set.Ioo s (T 0),
            rootPh (A i) (T 0) u * (Ks ![u, s] * W i ![T 0, u]))
          = rn θ {T : Fin 1 → ℝ | T 0 ∈ Set.Icc s (p + 1)} (fun T => G ![T 0, s]) := rn_congr θ heq
        _ ≤ rn θ (Set.pi univ fun _ => Icc p (p + 1)) (fun T : Fin 1 → ℝ => G ![T 0, s]) :=
            rn_mono_set θ hsub _
        _ ≤ ENNReal.ofReal Cs * timeFourierNorm θ G := hSl p s G hGc
        _ ≤ ENNReal.ofReal Cs * (K₁ * (K₀ * (rn θ (timeBoxGt p p) Ks + δ) *
              ((∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) + δ) + δ)) := mul_le_mul' le_rfl hGn
        _ = ENNReal.ofReal Cs * K₁ * (K₀ * (rn θ (timeBoxGt p p) Ks + δ) *
              ((∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) + δ) + δ) := by ring
  refine key.trans ?_
  gcongr
  exact le_self_add

/-! ### The target, restated verbatim (D3-MIRROR, target (3)) -/

open WaveTurbulence.Fourier in
example {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p s : ℝ), p ≤ s → s ≤ p + 1 → ∀ (A : ι → ℝ) (c : ι → ℂ)
      (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), Continuous Ks → (∀ i, Continuous (W i)) →
      rn θ (timeBoxGt p p) Ks < ⊤ → (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) →
      rn θ {T : Fin 1 → ℝ | T 0 ∈ Set.Icc s (p + 1)} (fun T => ∑' i, c i * ∫ u in Set.Ioo s (T 0),
          rootPh (A i) (T 0) u * (Ks ![u, s] * W i ![T 0, u])) ≤
        C * rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) :=
  mirror_at hθ0 hθ1

/-! ### The integrated root trace (target (4)) -/

theorem win_cl (p : ℝ) : ∀ x ∈ win p, x ∈ closure (interior (win p)) := by
  intro x hx
  have e : win p = (Homeomorph.funUnique (Fin 1) ℝ) ⁻¹' Icc p (p + 1) := rfl
  rw [e, ← Homeomorph.preimage_interior, ← Homeomorph.preimage_closure, interior_Icc,
    closure_Ioo (by linarith : p ≠ p + 1)]
  exact hx

theorem tsum_unit_const {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (x : M) :
    (∑' (_ : Unit), x) = x := by
  simp

open WaveTurbulence.Fourier in
/-- (4) The integral in the upper clock of the root trace at a fixed port time `s` (zero below `s`). -/
theorem mirror_int {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p s : ℝ), p ≤ s → s < p + 1 → ∀ (A : ι → ℝ) (c : ι → ℂ)
      (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), Continuous Ks → (∀ i, Continuous (W i)) →
      rn θ (timeBoxGt p p) Ks < ⊤ → (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) →
      rn θ (win p) (fun T => ∫ ρ in Set.Ioo s (T 0), ∑' i, c i * ∫ u in Set.Ioo s ρ,
          rootPh (A i) ρ u * (Ks ![u, s] * W i ![ρ, u])) ≤
        C * rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) := by
  obtain ⟨K₀, K₁, hK₀, hK₁, hE⟩ := mirror_ext hθ0 (by linarith)
  obtain ⟨Cs, -, hSl⟩ := slot_unit hθ0
  obtain ⟨C₀, -, hTK⟩ := termKink_sum hθ0 (by linarith)
  set K₁' : ℝ≥0∞ := ENNReal.ofReal C₀ * cutNorm θ * (ENNReal.ofReal Cs * K₁ + 1) with hK₁'
  have hK₁'t : K₁' < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (cutNorm_lt_top θ))
    (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK₁, ENNReal.one_lt_top⟩)
  refine ⟨K₁' * K₀ + 1, ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top hK₁'t hK₀, ENNReal.one_lt_top⟩, ?_⟩
  intro ι _ p s hps hsp A c Ks W hKc hWc hKfin hWfin
  by_cases ha0 : rn θ (timeBoxGt p p) Ks = 0
  · rw [rn_zero_of_eq θ fun T hT => ?_]
    · exact zero_le
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℂ)) fun ρ hρ => ?_]
    · simp
    show (∑' i, c i * ∫ u in Set.Ioo s ρ, rootPh (A i) ρ u * (Ks ![u, s] * W i ![ρ, u])) = 0
    refine (tsum_congr fun i => ?_).trans tsum_zero
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℂ)) fun u hu => ?_]
    · simp
    have hm := vec_mem_box hps hu.1 ((hu.2.trans hρ.2).le.trans hT.2)
    have h0 := enorm_le_rn hθ0 (timeBoxGt_cl p) hKc hm
    rw [ha0, nonpos_iff_eq_zero, enorm_eq_zero] at h0
    simp only [h0, zero_mul, mul_zero]
  by_cases hSt : (∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) = ⊤
  · rw [hSt, ENNReal.mul_top (mul_ne_zero (const_add_one_ne_zero _) ha0)]
    exact le_top
  have key : rn θ (win p) (fun T => ∫ ρ in Set.Ioo s (T 0), ∑' i, c i * ∫ u in Set.Ioo s ρ,
          rootPh (A i) ρ u * (Ks ![u, s] * W i ![ρ, u])) ≤
      K₁' * K₀ * rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) :=
    le_of_slack hK₀.ne hK₁'t.ne hKfin.ne hSt fun δ hδ hδt => by
      obtain ⟨G, hGc, hG, hGn⟩ := hE ι p A c Ks W hKc hWc hKfin hWfin (lt_top_iff_ne_top.2 hSt) δ hδ hδt
      set Y := K₀ * (rn θ (timeBoxGt p p) Ks + δ) * ((∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) + δ) + δ
        with hY
      have hYt : Y < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top hK₀
        (ENNReal.add_lt_top.2 ⟨hKfin, lt_top_iff_ne_top.2 hδt⟩))
        (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hSt, lt_top_iff_ne_top.2 hδt⟩), lt_top_iff_ne_top.2 hδt⟩
      have hGfin : timeFourierNorm θ G < ⊤ := hGn.trans_lt (ENNReal.mul_lt_top hK₁ hYt)
      -- the slice `σ = s` on the window
      set g₁ : (Fin 1 → ℝ) → ℂ := fun y => G ![y 0, s] with hg₁
      have hg₁c : Continuous g₁ := hGc.comp (by fun_prop)
      have hwin : win p ⊆ Set.pi univ fun _ => Icc p (p + 1) := fun T hT j _ => by
        fin_cases j
        exact hT
      have hsl : rn θ (win p) g₁ ≤ ENNReal.ofReal Cs * timeFourierNorm θ G :=
        (rn_mono_set θ hwin g₁).trans (hSl p s G hGc)
      have hg₁fin : rn θ (win p) g₁ < ⊤ := hsl.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGfin)
      obtain ⟨E, hEc, hE1, hEfin, hEle⟩ := exists_cont_ext hθ0 (win_cl p) hg₁c hg₁fin hδ hδt
      -- the kernel of the terminal operator: `h(T, ρ) = χ(T) E(ρ)`
      set h : (Fin 2 → ℝ) → ℂ := fun x => cut1 p (fun _ => x 0) * E (fun _ => x 1) with hh
      have hhc : Continuous h :=
        ((continuous_cut1 p).comp (continuous_pi fun _ => continuous_apply 0)).mul
          (hEc.comp (continuous_pi fun _ => continuous_apply 1))
      have hhn : timeFourierNorm θ h ≤ cutNorm θ * timeFourierNorm θ E := by
        have := timeFourierNorm_tensor2_le hθ0 (cut1 p) E
        rwa [cut1_norm] at this
      have hhfin : timeFourierNorm θ h < ⊤ := hhn.trans_lt (ENNReal.mul_lt_top (cutNorm_lt_top θ) hEfin)
      obtain ⟨g, hgeq, hgn⟩ := hTK Unit s (fun _ => 0) (fun _ => 1) (fun _ => h) (fun _ => hhc)
        (fun _ => hhfin) (by simpa using hhfin)
      refine (rn_le θ (g := g) fun T hT => ?_).trans ?_
      · have hT1 : |T 0 - s| ≤ 1 := abs_le.2 ⟨by linarith [hT.1, hsp], by linarith [hT.2, hps]⟩
        rw [hgeq T hT1, tsum_unit_const, one_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
        simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul]
        show cut1 p (fun _ => T 0) * E (fun _ => u) = _
        have hu' : (fun _ => u : Fin 1 → ℝ) ∈ win p := ⟨hps.trans hu.1.le, hu.2.le.trans hT.2⟩
        have hmem : (![u, s] : Fin 2 → ℝ) ∈ triC p := by
          show p ≤ s ∧ s ≤ u ∧ u ≤ p + 1
          exact ⟨hps, hu.1.le, hu.2.le.trans hT.2⟩
        rw [cut1_eq_one (y := fun _ => T 0) hT, one_mul, hE1 _ hu']
        show G ![u, s] = _
        rw [hG _ hmem]
        rfl
      · calc timeFourierNorm θ g
            ≤ ENNReal.ofReal C₀ * ∑' (_ : Unit), ‖(1 : ℂ)‖ₑ * timeFourierNorm θ h := hgn
          _ = ENNReal.ofReal C₀ * timeFourierNorm θ h := by simp
          _ ≤ ENNReal.ofReal C₀ * (cutNorm θ * (ENNReal.ofReal Cs * timeFourierNorm θ G + δ)) :=
              mul_le_mul' le_rfl (hhn.trans (mul_le_mul' le_rfl (hEle.trans (add_le_add hsl le_rfl))))
          _ ≤ ENNReal.ofReal C₀ * (cutNorm θ * (ENNReal.ofReal Cs * (K₁ * Y) + Y)) :=
              mul_le_mul' le_rfl (mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hGn) le_add_self))
          _ = K₁' * Y := by rw [hK₁']; ring
  refine key.trans ?_
  gcongr
  exact le_self_add

open WaveTurbulence.Fourier in
example {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p s : ℝ), p ≤ s → s < p + 1 → ∀ (A : ι → ℝ) (c : ι → ℂ)
      (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), Continuous Ks → (∀ i, Continuous (W i)) →
      rn θ (timeBoxGt p p) Ks < ⊤ → (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) →
      rn θ (win p) (fun T => ∫ ρ in Set.Ioo s (T 0), ∑' i, c i * ∫ u in Set.Ioo s ρ,
          rootPh (A i) ρ u * (Ks ![u, s] * W i ![ρ, u])) ≤
        C * rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) :=
  mirror_int hθ0 hθ1

end WaveTurbulence.Flower.ProtPin
