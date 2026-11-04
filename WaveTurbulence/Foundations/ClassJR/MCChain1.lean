/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCAssemble

/-!
# The bookkeeping of a chain term

For a chain (a Catalan code `c` with pair symbols `P j`) and a set `D` of pairs that carry the
difference `Φ(ε_jα_j + λ_{j,1}) - Φ(ε_jα_j)` (DH21 L1141–L1145), this file provides
* the pair symbols with the differences attached (`chainP`) and their bounds;
* `Mz_mul`: the product of the pair symbols times the differences;
* the variables of the product (`range_fT`, `injective_fT`);
* the bounds of `M = (∏_j 𝒞_j) ⊗ 𝒞_b` in the form used by `srep_assemble` (`chainM_bounds`);
* the shift `s(z)` of the chain variables and its cost (`sV`, `one_add_sV_le`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section ChainP

variable {V : Type} (P : ℕ → PSym V) (σ : ℕ → V) (ε : ℕ → ℤ) (D : Finset ℕ)

/-- **The pair symbols of a chain term**: `𝒞_j`, times the difference for `j ∈ D`. -/
@[expose] noncomputable def chainP (j : ℕ) : PSym V :=
  if j ∈ D then (P j).pd (σ j) (ε j) else P j

variable {P σ ε D}

theorem chainP_of_mem {j : ℕ} (h : j ∈ D) : chainP P σ ε D j = (P j).pd (σ j) (ε j) := by
  simp [chainP, h]

theorem chainP_of_notMem {j : ℕ} (h : j ∉ D) : chainP P σ ε D j = P j := by
  simp [chainP, h]

/-- The pair symbol of a chain term at the variables `α`. -/
theorem chainP_C (α : V → ℝ) (j : ℕ) (lam : ℝ × ℝ) :
    (chainP P σ ε D j).C (α ∘ (chainP P σ ε D j).f) lam =
      (P j).C (α ∘ (P j).f) lam * (if j ∈ D then Dfun (ε j) lam.1 (α (σ j)) else 1) := by
  by_cases h : j ∈ D
  · rw [chainP_of_mem h]
    simp only [h, ↓reduceIte]
    rfl
  · rw [chainP_of_notMem h]
    simp only [h, ↓reduceIte, mul_one]

theorem range_chainP_f (j : ℕ) :
    Set.range (chainP P σ ε D j).f =
      Set.range (P j).f ∪ (if j ∈ D then {σ j} else ∅) := by
  by_cases h : j ∈ D
  · rw [chainP_of_mem h]
    simp only [h, ↓reduceIte, PSym.pd, Set.Sum.elim_range]
    congr 1
    exact Set.range_const
  · rw [chainP_of_notMem h]
    simp only [h, ↓reduceIte, Set.union_empty]

theorem injective_chainP_f {j : ℕ} (hf : Function.Injective (P j).f)
    (hσ : σ j ∉ Set.range (P j).f) : Function.Injective (chainP P σ ε D j).f := by
  by_cases h : j ∈ D
  · rw [chainP_of_mem h]
    refine hf.sumElim (fun _ _ _ => rfl) fun x _ hx => hσ ⟨x, hx⟩
  · rw [chainP_of_notMem h]
    exact hf

/-- **The bounds of the pair symbols of a chain term.** -/
theorem PBound.chainP {θ a b A N : ℝ} {j : ℕ} (h : SRep θ a b A N (P j).C) (ha : 0 < a)
    (hb : 0 ≤ b) (hab : a + b ≤ θ) (hθ1 : θ ≤ 1) (hA : Achi ≤ A) (hε : ε j = 1 ∨ ε j = -1) :
    PBound A ((1 + KPD a b) * N) b (chainP P σ ε D j) := by
  have hA0 : 0 ≤ A := Achi_nonneg.trans hA
  have hK := KPD_nonneg a b
  by_cases hD : j ∈ D
  · rw [chainP_of_mem hD]
    exact (PBound.pd h ha hb hab hθ1 hA (σ j) hε).mono
      (mul_le_mul_of_nonneg_right (by linarith) h.nonneg) hA0
  · rw [chainP_of_notMem hD]
    exact (PBound.of_srep (f := (P j).f) h (by linarith) ha.le hb (by linarith)).mono
      (le_mul_of_one_le_left h.nonneg (by linarith)) hA0

end ChainP

section MzMul

variable {V : Type}

/-- **The product of the pair symbols times functions of the pair frequencies.** -/
theorem Mz_mul (Ĉ d : ℕ → ℝ × ℝ → ℂ) : ∀ (c : LegalCode) (q : ℕ) (z : ZT c),
    Mz (fun j lam => Ĉ j lam * d j lam) c q z =
      Mz Ĉ c q z * ∏ j ∈ Finset.Ico q (q + c.size), d j (Λz c q z j)
  | .nil, q, z => by simp [Mz, LegalCode.size]
  | .node i r, q, z => by
    have hsz : (LegalCode.node i r).size = i.size + r.size + 1 := rfl
    have hi := Mz_mul Ĉ d i (q + 1) z.2.1
    have hr := Mz_mul Ĉ d r (q + i.size + 1) z.2.2
    -- split the product
    have hsplit : Finset.Ico q (q + (LegalCode.node i r).size) =
        insert q (Finset.Ico (q + 1) (q + 1 + i.size) ∪
          Finset.Ico (q + i.size + 1) (q + i.size + 1 + r.size)) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_union, hsz]
      omega
    have hnq : q ∉ Finset.Ico (q + 1) (q + 1 + i.size) ∪
        Finset.Ico (q + i.size + 1) (q + i.size + 1 + r.size) := by
      simp only [Finset.mem_union, Finset.mem_Ico]
      omega
    have hd : Disjoint (Finset.Ico (q + 1) (q + 1 + i.size))
        (Finset.Ico (q + i.size + 1) (q + i.size + 1 + r.size)) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_Ico] at h1 h2
      omega
    rw [hsplit, Finset.prod_insert hnq, Finset.prod_union hd]
    have e1 : ∏ j ∈ Finset.Ico (q + 1) (q + 1 + i.size), d j (Λz (.node i r) q z j) =
        ∏ j ∈ Finset.Ico (q + 1) (q + 1 + i.size), d j (Λz i (q + 1) z.2.1 j) :=
      Finset.prod_congr rfl fun j hj => by
        rw [Λz_node_inner i r q z (by simpa [Finset.mem_Ico] using hj)]
    have e2 : ∏ j ∈ Finset.Ico (q + i.size + 1) (q + i.size + 1 + r.size),
        d j (Λz (.node i r) q z j) =
        ∏ j ∈ Finset.Ico (q + i.size + 1) (q + i.size + 1 + r.size),
          d j (Λz r (q + i.size + 1) z.2.2 j) :=
      Finset.prod_congr rfl fun j hj => by
        rw [Λz_node_rest i r q z (by simpa [Finset.mem_Ico] using hj)]
    rw [e1, e2, Λz_node_q]
    simp only [Mz] at hi hr ⊢
    rw [hi, hr]
    ring

end MzMul

section Ranges

variable {V : Type} (P : ℕ → PSym V)

/-- The variables of the product of the pair symbols. -/
theorem range_fT : ∀ (c : LegalCode) (q : ℕ),
    Set.range (fT P c q) = ⋃ j ∈ Set.Ico q (q + c.size), Set.range (P j).f
  | .nil, q => by
    rw [show (LegalCode.nil).size = 0 from rfl, add_zero, Set.Ico_self]
    simp only [Set.mem_empty_iff_false, Set.iUnion_of_empty, Set.iUnion_empty]
    exact Set.range_eq_empty_iff.2 ⟨fun e => Empty.elim e⟩
  | .node i r, q => by
    have hsz : (LegalCode.node i r).size = i.size + r.size + 1 := rfl
    have hi := range_fT i (q + 1)
    have hr := range_fT r (q + i.size + 1)
    change Set.range (Sum.elim (P q).f (Sum.elim (fT P i (q + 1)) (fT P r (q + i.size + 1)))) = _
    rw [Set.Sum.elim_range, Set.Sum.elim_range, hi, hr]
    ext v
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_Ico, exists_prop]
    constructor
    · rintro (h | ⟨j, hj, h⟩ | ⟨j, hj, h⟩)
      · exact ⟨q, by omega, h⟩
      · exact ⟨j, by omega, h⟩
      · exact ⟨j, by omega, h⟩
    · rintro ⟨j, hj, h⟩
      by_cases hjq : j = q
      · subst hjq; exact Or.inl h
      · by_cases hji : j < q + 1 + i.size
        · exact Or.inr (Or.inl ⟨j, by omega, h⟩)
        · exact Or.inr (Or.inr ⟨j, by omega, h⟩)

/-- The product of the pair symbols has distinct variables if the pairs do. -/
theorem injective_fT : ∀ (c : LegalCode) (q : ℕ),
    (∀ j ∈ Set.Ico q (q + c.size), Function.Injective (P j).f) →
    (∀ j ∈ Set.Ico q (q + c.size), ∀ k ∈ Set.Ico q (q + c.size), j ≠ k →
      Disjoint (Set.range (P j).f) (Set.range (P k).f)) →
    Function.Injective (fT P c q)
  | .nil, _, _, _ => fun e => Empty.elim e
  | .node i r, q, hf, hd => by
    have hsz : (LegalCode.node i r).size = i.size + r.size + 1 := rfl
    have hi := injective_fT i (q + 1)
      (fun j hj => hf j (by simp only [Set.mem_Ico] at hj ⊢; omega))
      (fun j hj k hk => hd j (by simp only [Set.mem_Ico] at hj ⊢; omega) k
        (by simp only [Set.mem_Ico] at hk ⊢; omega))
    have hr := injective_fT r (q + i.size + 1)
      (fun j hj => hf j (by simp only [Set.mem_Ico] at hj ⊢; omega))
      (fun j hj k hk => hd j (by simp only [Set.mem_Ico] at hj ⊢; omega) k
        (by simp only [Set.mem_Ico] at hk ⊢; omega))
    have hq := hf q (by simp only [Set.mem_Ico]; omega)
    change Function.Injective (Sum.elim (P q).f (Sum.elim (fT P i (q + 1))
      (fT P r (q + i.size + 1))))
    have hir : Function.Injective (Sum.elim (fT P i (q + 1)) (fT P r (q + i.size + 1))) := by
      refine hi.sumElim hr fun x y hxy => ?_
      have h1 : fT P i (q + 1) x ∈ Set.range (fT P i (q + 1)) := ⟨x, rfl⟩
      have h2 : fT P i (q + 1) x ∈ Set.range (fT P r (q + i.size + 1)) := ⟨y, hxy.symm⟩
      rw [range_fT] at h1 h2
      simp only [Set.mem_iUnion, Set.mem_Ico, exists_prop] at h1 h2
      obtain ⟨j, hj, hj'⟩ := h1
      obtain ⟨k, hk, hk'⟩ := h2
      exact Set.disjoint_left.1 (hd j (by simp only [Set.mem_Ico]; omega) k
        (by simp only [Set.mem_Ico]; omega) (by omega)) hj' hk'
    refine hq.sumElim hir fun x y hxy => ?_
    have h2 : (P q).f x ∈ Set.range (Sum.elim (fT P i (q + 1)) (fT P r (q + i.size + 1))) :=
      ⟨y, hxy.symm⟩
    rw [Set.Sum.elim_range, range_fT, range_fT] at h2
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_Ico, exists_prop] at h2
    rcases h2 with ⟨k, hk, hk'⟩ | ⟨k, hk, hk'⟩
    · exact Set.disjoint_left.1 (hd q (by simp only [Set.mem_Ico]; omega) k
        (by simp only [Set.mem_Ico]; omega) (by omega)) ⟨x, rfl⟩ hk'
    · exact Set.disjoint_left.1 (hd q (by simp only [Set.mem_Ico]; omega) k
        (by simp only [Set.mem_Ico]; omega) (by omega)) ⟨x, rfl⟩ hk'

end Ranges

section ChainM

variable {V : Type} {c : LegalCode} {ι ιb : Type} [Fintype ι] [Fintype ιb]

theorem one_add_snd_rpow_le_wL {c' θ : ℝ} (hc : 0 ≤ c') (hcθ : c' ≤ θ) (lam : ℝ × ℝ) :
    (1 + ‖lam.2‖ₑ) ^ c' ≤ wL θ lam := by
  rw [← wL_swap]
  exact one_add_rpow_le_wL hc hcθ lam.swap

/-- **The bounds of `M = (∏_j 𝒞_j) ⊗ 𝒞_b`** in the form used by `srep_assemble`: the weight
`⟨λ₂⟩^θ` (resp. `⟨λ₂⟩^a`) falls on the bottom symbol, the variable and pair-frequency weights on
the factor that carries them. -/
theorem chainM_bounds {θ a b A NT Nb : ℝ} {MS : (ι → ℝ) → ZT c → ℂ}
    {Cb : (ιb → ℝ) → ℝ × ℝ → ℂ} (hT : TBound A NT b c 0 MS) (hC : SRep θ a b A Nb Cb)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (haθ : a ≤ θ) (hA : 0 ≤ A) :
    (∀ k, ∫⁻ β, ∫⁻ w, (1 + ‖w.2.2‖ₑ) ^ θ * dnorm k (pprod MS Cb) β w ≤ gev (4 * NT * Nb) A k) ∧
    (∀ i, ∫⁻ β, ∫⁻ w, (1 + ‖w.2.2‖ₑ) ^ a * (1 + ‖β i‖ₑ) ^ b * dnorm 0 (pprod MS Cb) β w ≤
      ENNReal.ofReal (4 * NT * Nb)) ∧
    (∀ j, ∫⁻ β, ∫⁻ w, (1 + ‖w.2.2‖ₑ) ^ a * (1 + ‖(Λz c 0 w.1 j).1‖ₑ) ^ b *
      dnorm 0 (pprod MS Cb) β w ≤ ENNReal.ofReal (4 * NT * Nb)) := by
  have hNT := hT.nonneg
  have hNb := hC.nonneg
  have hc : ENNReal.ofReal NT * ENNReal.ofReal Nb ≤ ENNReal.ofReal (4 * NT * Nb) := by
    rw [← ENNReal.ofReal_mul hNT]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hNT hNb])
  have hwC : ∀ c' : ℝ, Measurable (Function.uncurry fun (_ : ιb → ℝ) (lam : ℝ × ℝ) =>
      ((1 : ℝ≥0∞) + ‖lam.2‖ₑ) ^ c') := fun c' => by
    change Measurable fun y : (ιb → ℝ) × (ℝ × ℝ) => ((1 : ℝ≥0∞) + ‖y.2.2‖ₑ) ^ c'
    fun_prop
  have hCa : ∫⁻ β, ∫⁻ lam, (1 + ‖lam.2‖ₑ) ^ a * dnorm 0 Cb β lam ≤ ENNReal.ofReal Nb :=
    le_trans (lintegral_mono fun β => lintegral_mono fun lam =>
      mul_le_mul' (one_add_snd_rpow_le_wL ha haθ lam) le_rfl) ((hC.norm 0).trans_eq (gev_zero_eq _ _))
  have hT0 := (hT.norm 0).trans_eq (gev_zero_eq NT A)
  refine ⟨fun k => ?_, ?_, fun j => ?_⟩
  · have h := lintegral_pprod_gev_le hT.smooth hT.meas hC.reg.smooth hC.reg.meas
      (wM := fun _ _ => 1) measurable_const (hwC θ) (N₁ := NT) (N₂ := Nb) hNT hNb hA
      (by simpa using hT.norm) (fun j => le_trans (lintegral_mono fun β => lintegral_mono fun lam =>
        mul_le_mul' (one_add_snd_rpow_le_wL hθ le_rfl lam) le_rfl) (hC.norm j)) k
    simp only [one_mul] at h
    exact h
  · rintro (i | i)
    · have hw : Measurable (Function.uncurry fun (β : ι → ℝ) (_ : ZT c) =>
          ((1 : ℝ≥0∞) + ‖β i‖ₑ) ^ b) := by
        change Measurable fun y : (ι → ℝ) × ZT c => ((1 : ℝ≥0∞) + ‖y.1 i‖ₑ) ^ b
        fun_prop
      have h := lintegral_pprod_zero_le hT.smooth hT.meas hC.reg.smooth hC.reg.meas hw (hwC a)
      refine le_trans (le_of_eq (lintegral_congr fun β => lintegral_congr fun w => by ring))
        (h.trans ((mul_le_mul' (hT.wvar i) hCa).trans hc))
    · have hw : Measurable (Function.uncurry fun (β : ιb → ℝ) (lam : ℝ × ℝ) =>
          wL a lam * ((1 : ℝ≥0∞) + ‖β i‖ₑ) ^ b) := by
        change Measurable fun y : (ιb → ℝ) × (ℝ × ℝ) => wL a y.2 * ((1 : ℝ≥0∞) + ‖y.1 i‖ₑ) ^ b
        have := measurable_wL a
        fun_prop
      have h := lintegral_pprod_zero_le hT.smooth hT.meas hC.reg.smooth hC.reg.meas
        (wM := fun _ _ => 1) measurable_const hw
      simp only [one_mul] at h
      have hCw : ∫⁻ β, ∫⁻ lam, wL a lam * (1 + ‖β i‖ₑ) ^ b * dnorm 0 Cb β lam ≤
          ENNReal.ofReal Nb := by
        simpa only [dnorm_zero] using hC.wnorm i
      refine le_trans (lintegral_mono fun β => lintegral_mono fun w => ?_)
        (h.trans ((mul_le_mul' hT0 hCw).trans hc))
      refine mul_le_mul' (mul_le_mul' (one_add_snd_rpow_le_wL ha le_rfl w.2) le_rfl) le_rfl
  · have h := lintegral_pprod_zero_le hT.smooth hT.meas hC.reg.smooth hC.reg.meas
      (measurable_weight_Λz c 0 j b (pr := fun z => z) measurable_id) (hwC a)
    refine le_trans (le_of_eq (lintegral_congr fun β => lintegral_congr fun w => by ring))
      (h.trans ((mul_le_mul' (hT.wfreq j) hCa).trans hc))

end ChainM

section Shift

variable {V : Type} [DecidableEq V] (σ : ℕ → V) (ε : ℕ → ℤ) (c : LegalCode) {ι : Type}

/-- **The shift of the chain variables** (DH21 (kusingI)): `α̃_{σ j} = α_{σ j} + ε_jλ_{j,1}`. -/
@[expose] noncomputable def sV (f : ι → V) (z : ZT c) (i : ι) : ℝ :=
  ∑ j ∈ Finset.Ico 0 (0 + c.size), if σ j = f i then (ε j : ℝ) * (Λz c 0 z j).1 else 0

theorem shiftV_comp (f : ι → V) (z : ZT c) (α : V → ℝ) :
    shiftV σ ε (Λz c 0 z) 0 c.size α ∘ f = α ∘ f + sV σ ε c f z := rfl

variable {σ ε c}

theorem measurable_sV (f : ι → V) : Measurable (sV σ ε c f) := by
  refine Measurable.of_eval fun i => ?_
  change Measurable fun z => ∑ j ∈ Finset.Ico 0 (0 + c.size),
    if σ j = f i then (ε j : ℝ) * (Λz c 0 z j).1 else 0
  refine Finset.measurable_sum _ fun j _ => ?_
  by_cases h : σ j = f i
  · simp only [h, ↓reduceIte]
    exact measurable_const.mul (measurable_fst.comp (continuous_Λz c 0 j).measurable)
  · simp only [h, ↓reduceIte]
    exact measurable_const

/-- The cost of the shift is the weight of the frequency of the pair. -/
theorem one_add_sV_le (hε : ∀ j, ε j = 1 ∨ ε j = -1) (hinj : Set.InjOn σ (Set.Ico 0 c.size))
    {f : ι → V} {i : ι} {j : ℕ} (hj : j ∈ Set.Ico 0 c.size) (hfj : f i = σ j) {b : ℝ}
    (z : ZT c) : (1 + ‖sV σ ε c f z i‖ₑ) ^ b ≤ (1 + ‖(Λz c 0 z j).1‖ₑ) ^ b := by
  have e : sV σ ε c f z i = (ε j : ℝ) * (Λz c 0 z j).1 := by
    unfold sV
    rw [Finset.sum_eq_single j]
    · simp only [hfj, ↓reduceIte]
    · intro k hk hkj
      have hk' : k ∈ Set.Ico 0 c.size := by simpa [Finset.mem_Ico] using hk
      rw [ite_eq_right_iff]
      intro h
      exact absurd (hinj hk' hj (h.trans hfj)) hkj
    · intro h
      exact absurd (by simpa [Finset.mem_Ico] using hj) h
  rw [e, enorm_mul]
  rcases hε j with h | h <;> simp [h]

end Shift

end WaveTurbulence.ClassJR
