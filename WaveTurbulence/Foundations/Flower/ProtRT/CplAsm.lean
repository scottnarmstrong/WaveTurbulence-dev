/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.CplOn
public import WaveTurbulence.Foundations.Flower.ProtPin.RootPin

/-! # RT-GATE (ii): reductions of the couple clause

* `rt_kernel_up2`: a pinned tree's free branches lie below the pin, so its clock may be changed to any value `≥ s`
  (the R189 box `s ≤ ts j`);
* `rt_rootPins_one`, `rt_rootPins_both`: the pins of one or both roots;
* `rt_tcWt_le`: D3's output weight decays like `⟨k⟩^{-30d}` with the lattice sums `(latC L^d)²` (`tc_tsum_T1E`);
* `rt_ball_wt`: on a lattice ball, `⟨k⟩^{-30d} ≤ 4^d ⟨c₀⟩^{-2d}`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

variable {w : ℕ}

/-- **Below a pinned root**: every free branch of a pinned tree is earlier than the pin. -/
theorem rt_lt_pin {LG : LayeredGarden w} (Rt : Fin w → Prop) (up : GBranch LG.garden.tree → ℝ) (u : ℝ)
    (x : GBranch LG.garden.tree → ℝ) (hx : x ∈ kDomainFix LG up (MkSlotsO.rootPins Rt u))
    (hroot : ∀ b : GBranch LG.garden.tree, b.1.2 = [] → Rt b.1.1 → x b = u) :
    ∀ (n : ℕ) (b : GBranch LG.garden.tree), Rt b.1.1 → b.1.2.length = n + 1 → x b < u := by
  intro n
  induction n with
  | zero =>
    intro b hR hb
    have hne : b.1.2 ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hpar : b.1.2.dropLast ∈ (LG.garden.tree b.1.1).branching := by
      have h := b.2
      rw [← List.dropLast_append_getLast hne] at h
      exact MainCoef.mem_branching_of_append _ _ _ h
    let b0 : GBranch LG.garden.tree := ⟨(b.1.1, b.1.2.dropLast), hpar⟩
    have hchild : b.IsChildOf b0 := ⟨rfl, b.1.2.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    have hfree : (MkSlotsO.rootPins Rt u : GBranch LG.garden.tree → Option ℝ) b = none := by
      unfold MkSlotsO.rootPins; rw [if_neg (fun h => hne h.1)]
    have h1 := (hx b0).2 b hchild (Or.inl hfree)
    have h0 : b0.1.2 = [] := by
      show b.1.2.dropLast = []
      rw [← List.length_eq_zero_iff, List.length_dropLast, hb]
    rw [hroot b0 h0 hR] at h1
    exact h1
  | succ n ih =>
    intro b hR hb
    have hne : b.1.2 ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hpar : b.1.2.dropLast ∈ (LG.garden.tree b.1.1).branching := by
      have h := b.2
      rw [← List.dropLast_append_getLast hne] at h
      exact MainCoef.mem_branching_of_append _ _ _ h
    let b0 : GBranch LG.garden.tree := ⟨(b.1.1, b.1.2.dropLast), hpar⟩
    have hchild : b.IsChildOf b0 := ⟨rfl, b.1.2.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    have hfree : (MkSlotsO.rootPins Rt u : GBranch LG.garden.tree → Option ℝ) b = none := by
      unfold MkSlotsO.rootPins; rw [if_neg (fun h => hne h.1)]
    have h1 := (hx b0).2 b hchild (Or.inl hfree)
    have hl : b0.1.2.length = n + 1 := by
      show b.1.2.dropLast.length = n + 1
      rw [List.length_dropLast, hb]; rfl
    exact h1.trans (ih b0 hR hl)

/-- The time integral: a pinned tree's clock may be changed to any value above the pin. -/
theorem rt_protTime_up2 {LG : LayeredGarden w} (L γ δ : ℝ) {d : ℕ} (Rt : Fin w → Prop) (s' u : ℝ)
    (up up' : GBranch LG.garden.tree → ℝ) (hfr : ∀ b : GBranch LG.garden.tree, ¬ Rt b.1.1 → up b = up' b)
    (hu : ∀ b : GBranch LG.garden.tree, Rt b.1.1 → u ≤ up b ∧ u ≤ up' b) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG up s' (MkSlotsO.rootPins Rt u) K = protTime L γ δ LG up' s' (MkSlotsO.rootPins Rt u) K := by
  unfold protTime
  refine congrArg (fun f : ({b : GBranch LG.garden.tree // MkSlotsO.rootPins Rt u b = none} → ℝ) → ℂ => ∫ τ, f τ)
    (funext fun τ => ?_)
  set x := LG.garden.extendFix (MkSlotsO.rootPins Rt u) τ with hx
  have hroot : ∀ b : GBranch LG.garden.tree, b.1.2 = [] → Rt b.1.1 → x b = u := fun b h0 hR =>
    extendFix_some LG.garden (MkSlotsO.rootPins Rt u) τ (by unfold MkSlotsO.rootPins; rw [if_pos ⟨h0, hR⟩])
  have hnz : ∀ b : GBranch LG.garden.tree, (MkSlotsO.rootPins Rt u) b = none → Rt b.1.1 → b.1.2 ≠ [] := fun b hb hR h0 => by
    unfold MkSlotsO.rootPins at hb; rw [if_pos ⟨h0, hR⟩] at hb; exact absurd hb (by simp)
  have hlt : ∀ (v : GBranch LG.garden.tree → ℝ), x ∈ kDomainFix LG v (MkSlotsO.rootPins Rt u) → ∀ b : GBranch LG.garden.tree,
      (MkSlotsO.rootPins Rt u) b = none → Rt b.1.1 → x b < u := fun v hk b hb hR => by
    have hne := hnz b hb hR
    obtain ⟨n, hn⟩ : ∃ n, b.1.2.length = n + 1 :=
      ⟨b.1.2.length - 1, by have := List.length_pos_of_ne_nil hne; omega⟩
    exact rt_lt_pin Rt v u x hk hroot n b hR hn
  have hiff : ∀ (v v' : GBranch LG.garden.tree → ℝ), (∀ b, ¬ Rt b.1.1 → v b = v' b) →
      (∀ b, Rt b.1.1 → u ≤ v' b) → x ∈ protDom LG v s' (MkSlotsO.rootPins Rt u) → x ∈ protDom LG v' s' (MkSlotsO.rootPins Rt u) := by
    rintro v v' hv hv' ⟨hk, hl⟩
    refine ⟨fun b => ⟨fun hb => ?_, (hk b).2⟩, hl⟩
    obtain ⟨h1, h2, h3, h4⟩ := (hk b).1 hb
    refine ⟨h1, h2, h3, ?_⟩
    by_cases hR : Rt b.1.1
    · exact (hlt v hk b hb hR).trans_le (hv' b hR)
    · rw [← hv b hR]; exact h4
  by_cases hm : x ∈ protDom LG up s' (MkSlotsO.rootPins Rt u)
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem
      (hiff up up' hfr (fun b hR => (hu b hR).2) hm)]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm
      (hiff up' up (fun b hR => (hfr b hR).symm) (fun b hR => (hu b hR).1) h))]


/-- **The clock of a pinned tree may be changed to any value above the pin.** -/
theorem rt_kernel_up2 {LG : LayeredGarden w} (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (Rt : Fin w → Prop) (s' u : ℝ) (up up' : GBranch LG.garden.tree → ℝ)
    (hfr : ∀ b : GBranch LG.garden.tree, ¬ Rt b.1.1 → up b = up' b)
    (hu : ∀ b : GBranch LG.garden.tree, Rt b.1.1 → u ≤ up b ∧ u ≤ up' b) (k : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelProt L γ δ LG H m up s' (MkSlotsO.rootPins Rt u) k nroot nfl =
      kernelProt L γ δ LG H m up' s' (MkSlotsO.rootPins Rt u) k nroot nfl := by
  rw [kernelProt_eq_tsum, kernelProt_eq_tsum]
  congr 1
  refine tsum_congr fun κ => ?_
  unfold protSummand
  rw [rt_protTime_up2 L γ δ Rt s' u up up' hfr hu]

theorem rt_fin2_ne {j t : Fin 2} (h : t ≠ j) : t = t1sw j := by
  fin_cases j <;> fin_cases t <;> simp_all [t1sw]

/-- One pinned root is D2c's `trFix`. -/
theorem rt_rootPins_one {T : Fin 2 → TTree} (Rt : Fin 2 → Prop) (j : Fin 2) (hj : Rt j) (hj' : ¬ Rt (t1sw j))
    (s : ℝ) : (MkSlotsO.rootPins Rt s : GBranch T → Option ℝ) = trFix j s := by
  funext b
  unfold MkSlotsO.rootPins trFix
  by_cases h : b.1.1 = j
  · simp [h, hj, and_comm]
  · have h' := rt_fin2_ne h
    have hn : ¬ Rt b.1.1 := by rw [h']; exact hj'
    simp [h, hn]

theorem rt_rootPins_both {T : Fin 2 → TTree} (Rt : Fin 2 → Prop) (h : ∀ j, Rt j) (s : ℝ) :
    (MkSlotsO.rootPins Rt s : GBranch T → Option ℝ) = MkSlotsO.rootPins (fun _ => True) s := by
  funext b
  unfold MkSlotsO.rootPins
  simp [h]

/-- **D3's output weight decays like `⟨k⟩^{-30d}`.** -/
theorem rt_tcWt_le {d : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L) (k : Mom d) :
    tcWt L k ≤ ENNReal.ofReal ((tcDec d + 1) * (latC d * L ^ d) ^ 2) * ENNReal.ofReal (jbr k ^ (30 * d))⁻¹ := by
  have hJ : 0 < jbr k ^ (30 * d) := pow_pos (jbr_pos k) _
  have h1 := le_mul_inv_of_weighted hJ (tc_tsum_T1E hd hL k)
  have hl0 : 0 ≤ (latC d * L ^ d) ^ 2 := sq_nonneg _
  have htd : 0 ≤ tcDec d * (latC d * L ^ d) ^ 2 := mul_nonneg (tcDec_nonneg d) hl0
  unfold tcWt
  calc (∑' y : T1E d, tcJ (k + latticePoint L y.1.1) * tcJ (k + latticePoint L y.1.2.1) *
        tcJ (k + latticePoint L y.1.2.2)) + tcJ k * ENNReal.ofReal ((latC d * L ^ d) ^ 2)
      ≤ ENNReal.ofReal (tcDec d * (latC d * L ^ d) ^ 2) * ENNReal.ofReal (jbr k ^ (30 * d))⁻¹ +
          ENNReal.ofReal (jbr k ^ (30 * d))⁻¹ * ENNReal.ofReal ((latC d * L ^ d) ^ 2) :=
        add_le_add h1 le_rfl
    _ = ENNReal.ofReal ((tcDec d + 1) * (latC d * L ^ d) ^ 2) * ENNReal.ofReal (jbr k ^ (30 * d))⁻¹ := by
        rw [show (tcDec d + 1) * (latC d * L ^ d) ^ 2 = tcDec d * (latC d * L ^ d) ^ 2 + (latC d * L ^ d) ^ 2 by
          ring, ENNReal.ofReal_add htd hl0]
        ring

/-- **On a lattice ball**, `⟨k⟩^{-30d} ≤ 4^d ⟨c₀⟩^{-2d}`. -/
theorem rt_ball_wt {d : ℕ} {L : ℝ} {b₀ c₀ k : Mom d} (hk : k ∈ latticeBall L b₀ c₀) :
    (jbr k ^ (30 * d))⁻¹ ≤ 4 ^ d * (jbr c₀ ^ (2 * d))⁻¹ := by
  have hk1 : 1 ≤ jbr k := one_le_jbr k
  have hc1 : 0 < jbr c₀ := jbr_pos c₀
  have hd1 : jbr (c₀ - k) ≤ Real.sqrt 2 := by
    unfold jbr
    refine Real.sqrt_le_sqrt ?_
    have : ‖c₀ - k‖ ≤ 1 := by rw [norm_sub_rev]; exact hk.1
    nlinarith [norm_nonneg (c₀ - k)]
  have hc : jbr c₀ ≤ 2 * jbr k := by
    have h := jbr_add_le k (c₀ - k)
    rw [add_sub_cancel] at h
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    calc jbr c₀ ≤ Real.sqrt 2 * jbr k * jbr (c₀ - k) := h
      _ ≤ Real.sqrt 2 * jbr k * Real.sqrt 2 := by gcongr
      _ = 2 * jbr k := by rw [mul_comm (Real.sqrt 2 * jbr k), ← mul_assoc, hs]
  have h30 : jbr k ^ (2 * d) ≤ jbr k ^ (30 * d) := pow_le_pow_right₀ hk1 (by omega)
  have hpos2 : 0 < jbr k ^ (2 * d) := pow_pos (by linarith) _
  have hc2 : jbr c₀ ^ (2 * d) ≤ 4 ^ d * jbr k ^ (2 * d) := by
    calc jbr c₀ ^ (2 * d) ≤ (2 * jbr k) ^ (2 * d) := pow_le_pow_left₀ hc1.le hc _
      _ = 4 ^ d * jbr k ^ (2 * d) := by rw [mul_pow, pow_mul]; norm_num
  calc (jbr k ^ (30 * d))⁻¹ ≤ (jbr k ^ (2 * d))⁻¹ := inv_anti₀ hpos2 h30
    _ ≤ 4 ^ d * (jbr c₀ ^ (2 * d))⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hc1 _), inv_mul_eq_div, div_le_iff₀ hpos2]
        linarith

end WaveTurbulence.Flower.ProtRT
