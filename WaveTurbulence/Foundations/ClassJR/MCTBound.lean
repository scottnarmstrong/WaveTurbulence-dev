/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCTShift
public import WaveTurbulence.Foundations.ClassJR.MCChain1

/-!
# Weighted and twisted pair symbols (DH21 Proposition 6.10)

After rebasing a tree chain at `s` (`chainT_rebase`), each pair coefficient is evaluated at shifted
times `(u + s, v + s)`, so its symbol carries the phase `e^{πi(λ₁+λ₂)s}` (`tsym`). Fixing the
frequencies `z` of the pairs, the product of these phases is `e^{πiΛ(z)s}` (`Mz_tsym`), with `Λ(z)` the
total frequency of the pairs (`Λsum`). It is absorbed into the frequency `λ₂` of the bottom
coefficient by the shear `λ₂ ↦ λ₂ - Λ(z)`, and the weight `⟨λ₂⟩` of DH23 then also costs `⟨Λ(z)⟩`, paid
by the pair symbols.

This file provides the pair-symbol bounds with such a frequency weight:
* `wsym wp 𝒞 = (1+|λ₁|+|λ₂|)^wp 𝒞`, and `SRep.wsym`: the weighted symbol has the bounds of `𝒞` with the
  exponents lowered by `wp`;
* `MzSW wp`: the product of the pair symbols times `∏_j (1+|λ_j|)^wp`; `tbound_MzSW` gives its bounds
  (the node step `TBound.node` is that of `tbound_MzS`); since `(1+|Λ(z)|)^wp ≤ ∏_j (1+|λ_j|)^wp`
  (`one_add_Λsum_rpow_le`), these are the bounds of the product with the weight `⟨Λ(z)⟩^wp`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section MulLeft

variable {ι Γ : Type*} [Fintype ι]

/-- Derivatives in `α` do not see a factor depending only on the auxiliary variables. -/
theorem dnorm_mul_left (k : ℕ) (g : Γ → ℂ) (a : (ι → ℝ) → Γ → ℂ)
    (ha : ∀ γ, ContDiff ℝ ∞ fun α => a α γ) (α : ι → ℝ) (γ : Γ) :
    dnorm k (fun α γ => g γ * a α γ) α γ = ‖g γ‖ₑ * dnorm k a α γ := by
  have e : lift1 (fun α γ => g γ * a α γ) γ = g γ • lift1 a γ := by
    funext β; simp [lift1, smul_eq_mul]
  unfold dnorm
  rw [e, iteratedFDeriv_const_smul_apply
    ((contDiff_lift1 (ha γ)).of_le (by exact_mod_cast le_top)).contDiffAt, enorm_smul]

end MulLeft

section Weight

variable {ι : Type} [Fintype ι] {θ a b A N : ℝ}

/-- The real weight `(1 + |λ₁| + |λ₂|)^wp`. -/
@[expose] noncomputable def wFr (wp : ℝ) (lam : ℝ × ℝ) : ℝ := (1 + |lam.1| + |lam.2|) ^ wp

theorem wFr_nonneg (wp : ℝ) (lam : ℝ × ℝ) : 0 ≤ wFr wp lam := by
  unfold wFr; positivity

theorem ofReal_wFr {wp : ℝ} (hwp : 0 ≤ wp) (lam : ℝ × ℝ) : ENNReal.ofReal (wFr wp lam) = wL wp lam := by
  unfold wFr wL
  rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) hwp, ENNReal.ofReal_add (by positivity)
    (abs_nonneg _), ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one,
    ← Real.enorm_eq_ofReal_abs, ← Real.enorm_eq_ofReal_abs]

theorem enorm_wFr {wp : ℝ} (hwp : 0 ≤ wp) (lam : ℝ × ℝ) : ‖(wFr wp lam : ℂ)‖ₑ = wL wp lam := by
  rw [← ofReal_wFr hwp, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (wFr_nonneg wp lam)]

theorem wL_mul_wL (x y : ℝ) (lam : ℝ × ℝ) :
    wL x lam * wL y lam = wL (x + y) lam := by
  unfold wL
  rw [ENNReal.rpow_add _ _ (ne_of_gt (lt_of_lt_of_le one_pos (le_self_add.trans le_self_add)))
    (by simp)]

theorem wL_le_of_le {x y : ℝ} (hxy : x ≤ y) (lam : ℝ × ℝ) : wL x lam ≤ wL y lam := by
  unfold wL
  exact ENNReal.rpow_le_rpow_of_exponent_le (le_self_add.trans le_self_add) hxy

/-- **The weighted symbol** `(1+|λ₁|+|λ₂|)^wp 𝒞`. -/
@[expose] noncomputable def wsym (wp : ℝ) (C : (ι → ℝ) → ℝ × ℝ → ℂ) : (ι → ℝ) → ℝ × ℝ → ℂ :=
  fun β lam => (wFr wp lam : ℂ) * C β lam

theorem dnorm_wsym {wp : ℝ} (hwp : 0 ≤ wp) {C : (ι → ℝ) → ℝ × ℝ → ℂ}
    (hC : ∀ γ, ContDiff ℝ ∞ fun β => C β γ) (k : ℕ) (β : ι → ℝ) (lam : ℝ × ℝ) :
    dnorm k (wsym wp C) β lam = wL wp lam * dnorm k C β lam := by
  unfold wsym
  rw [dnorm_mul_left k (fun lam => (wFr wp lam : ℂ)) C hC, enorm_wFr hwp]

theorem measurable_wFr (wp : ℝ) : Measurable (wFr wp) := by unfold wFr; fun_prop

/-- **The bounds of a weighted symbol**: the exponents are lowered by the weight. -/
theorem SRep.weighted {θ' a' wp : ℝ} {C : (ι → ℝ) → ℝ × ℝ → ℂ} (h : SRep θ' a' b A N C) (hwp : 0 ≤ wp)
    (hθ : 0 ≤ θ) (hθwp : θ + wp ≤ θ') (hawp : a + wp ≤ a') :
    SRep θ a b A N (wsym wp C) := by
  have hs : ∀ γ, ContDiff ℝ ∞ fun β => wsym wp C β γ := fun γ =>
    contDiff_const.mul (h.reg.smooth γ)
  have hm : StronglyMeasurable (Function.uncurry (wsym wp C)) := by
    unfold wsym
    exact ((Complex.measurable_ofReal.comp ((measurable_wFr wp).comp measurable_snd)).mul
      h.reg.meas.measurable).stronglyMeasurable
  have hθ' : 0 ≤ θ' := by linarith
  have hw : ∀ k, ∫⁻ β, ∫⁻ lam, wL θ lam * dnorm k (wsym wp C) β lam ≤ gev N A k := fun k => by
    refine le_trans (lintegral_mono fun β => lintegral_mono fun lam => ?_) (h.norm k)
    rw [dnorm_wsym hwp h.reg.smooth, ← mul_assoc, wL_mul_wL]
    exact mul_le_mul' (wL_le_of_le hθwp lam) le_rfl
  refine ⟨h.nonneg, SymReg.of_lintegral hs hm fun k => ?_, hw, fun i => ?_⟩
  · refine ne_top_of_le_ne_top (gev_ne_top N A k) (le_trans ?_ (hw k))
    exact lintegral_mono fun β => lintegral_mono fun lam =>
      le_mul_of_one_le_left zero_le (one_le_wL hθ lam)
  · refine le_trans (lintegral_mono fun β => lintegral_mono fun lam => ?_) (h.wnorm i)
    rw [show ‖wsym wp C β lam‖ₑ = wL wp lam * ‖C β lam‖ₑ by
      simp only [wsym]; rw [enorm_mul, enorm_wFr hwp]]
    calc wL a lam * (1 + ‖β i‖ₑ) ^ b * (wL wp lam * ‖C β lam‖ₑ)
        = (wL a lam * wL wp lam) * (1 + ‖β i‖ₑ) ^ b * ‖C β lam‖ₑ := by ring
      _ ≤ wL a' lam * (1 + ‖β i‖ₑ) ^ b * ‖C β lam‖ₑ := by
          rw [wL_mul_wL]; gcongr; exact wL_le_of_le hawp lam

omit [Fintype ι] in
theorem pdC_wsym (wp : ℝ) (C : (ι → ℝ) → ℝ × ℝ → ℂ) (ε : ℤ) :
    pdC (wsym wp C) ε = wsym wp (pdC C ε) := by
  funext α z
  simp only [pdC, kprod, wsym]
  ring

end Weight

section NodeStep

variable {V : Type}

/-- **The node step of the product bounds** (the node case of `tbound_MzS`, for any pair symbol and
any products over the two blocks). -/
theorem TBound.node {A b : ℝ} (hA : 0 ≤ A) {i r : LegalCode} {q : ℕ} {Pq : PSym V}
    {ιi ιr : Type} [Fintype ιi] [Fintype ιr] {Mi : (ιi → ℝ) → ZT i → ℂ} {Mr : (ιr → ℝ) → ZT r → ℂ}
    {Nq Ni Nr : ℝ} (hq : PBound A Nq b Pq) (hi : TBound A Ni b i (q + 1) Mi)
    (hr : TBound A Nr b r (q + i.size + 1) Mr) :
    TBound A (4 * Nq * (4 * Ni * Nr)) b (.node i r) q (pprod Pq.C (pprod Mi Mr)) := by
    have hNi := hi.nonneg
    have hNr := hr.nonneg
    have hNq := hq.nonneg
    have hirs := contDiff_pprod hi.smooth hr.smooth
    have hirm := measurable_pprod hi.meas hr.meas
    have hirn : ∀ k, ∫⁻ β, ∫⁻ p, dnorm k (pprod (Mi) (Mr)) β p ≤
        gev (4 * Ni * Nr) A k := fun k => by
      have h := lintegral_pprod_gev_le hi.smooth hi.meas hr.smooth hr.meas (wM := fun _ _ => 1)
        measurable_const (wC := fun _ _ => 1) measurable_const (N₁ := Ni) (N₂ := Nr) hNi hNr hA
        (by simpa using hi.norm) (by simpa using hr.norm) k
      simpa using h
    obtain ⟨hir0, hirv⟩ := lintegral_pprod_var_le hi.smooth hi.meas hr.smooth hr.meas
      ((hi.norm 0).trans_eq (gev_zero_eq _ _)) hi.wvar ((hr.norm 0).trans_eq (gev_zero_eq _ _))
      hr.wvar
    have hq0 := (hq.norm 0).trans_eq (gev_zero_eq _ _)
    have hc1 : ENNReal.ofReal (Nq) * (ENNReal.ofReal Ni * ENNReal.ofReal Nr) ≤
        ENNReal.ofReal (4 * Nq * (4 * Ni * Nr)) := by
      rw [← ENNReal.ofReal_mul hNi, ← ENNReal.ofReal_mul hNq]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hNq (mul_nonneg hNi hNr)])
    refine ⟨by positivity, contDiff_pprod hq.smooth hirs, measurable_pprod hq.meas hirm,
      fun k => ?_, ?_, fun j => ?_⟩
    · have h := lintegral_pprod_gev_le hq.smooth hq.meas hirs hirm (wM := fun _ _ => 1)
        measurable_const (wC := fun _ _ => 1) measurable_const (N₁ := Nq) (N₂ := 4 * Ni * Nr)
        hNq (by positivity) hA (by simpa using hq.norm) (by simpa using hirn) k
      simp only [one_mul] at h
      exact h
    · obtain ⟨-, hv⟩ := lintegral_pprod_var_le hq.smooth hq.meas hirs hirm hq0 hq.wvar hir0 hirv
      exact fun i => (hv i).trans hc1
    · by_cases hjq : j = q
      · subst hjq
        have hw : Measurable (Function.uncurry fun (_ : Pq.ι → ℝ) (z : ℝ × ℝ) =>
            ((1 : ℝ≥0∞) + ‖z.1‖ₑ) ^ b) := by
          change Measurable fun x : (Pq.ι → ℝ) × (ℝ × ℝ) => ((1 : ℝ≥0∞) + ‖x.2.1‖ₑ) ^ b
          fun_prop
        have h := lintegral_pprod_zero_le hq.smooth hq.meas hirs hirm hw (wC := fun _ _ => 1)
          measurable_const
        simp only [mul_one, one_mul] at h
        have e : ∀ z : ZT (.node i r), Λz (.node i r) j z j = z.1 := Λz_node_q i r j
        simp_rw [e]
        exact h.trans ((mul_le_mul' hq.wfreq hir0).trans hc1)
      · by_cases hji : j < q + 1 + i.size
        · have e : ∀ z : ZT (.node i r), Λz (.node i r) q z j = Λz i (q + 1) z.2.1 j := fun z => by
            simp [Λz, hjq, hji]
          have h1 := lintegral_pprod_zero_le hi.smooth hi.meas hr.smooth hr.meas
            (wM := fun _ z => ((1 : ℝ≥0∞) + ‖(Λz i (q + 1) z j).1‖ₑ) ^ b)
            (measurable_weight_Λz i (q + 1) j b (pr := fun z => z) measurable_id)
            (wC := fun _ _ => 1) measurable_const
          simp only [mul_one, one_mul] at h1
          have h2 := lintegral_pprod_zero_le hq.smooth hq.meas hirs hirm (wM := fun _ _ => 1)
            measurable_const
            (wC := fun _ p => ((1 : ℝ≥0∞) + ‖(Λz i (q + 1) p.1 j).1‖ₑ) ^ b)
            (measurable_weight_Λz i (q + 1) j b (pr := fun p : ZT i × ZT r => p.1) measurable_fst)
          simp only [one_mul] at h2
          simp_rw [e]
          exact h2.trans ((mul_le_mul' hq0 (h1.trans (mul_le_mul' (hi.wfreq j)
            ((hr.norm 0).trans_eq (gev_zero_eq _ _))))).trans hc1)
        · have e : ∀ z : ZT (.node i r), Λz (.node i r) q z j = Λz r (q + i.size + 1) z.2.2 j :=
            fun z => by simp [Λz, hjq, hji]
          have h1 := lintegral_pprod_zero_le hi.smooth hi.meas hr.smooth hr.meas
            (wM := fun _ _ => 1) measurable_const
            (wC := fun _ z => ((1 : ℝ≥0∞) + ‖(Λz r (q + i.size + 1) z j).1‖ₑ) ^ b)
            (measurable_weight_Λz r (q + i.size + 1) j b (pr := fun z => z) measurable_id)
          simp only [one_mul] at h1
          have h2 := lintegral_pprod_zero_le hq.smooth hq.meas hirs hirm (wM := fun _ _ => 1)
            measurable_const
            (wC := fun _ p => ((1 : ℝ≥0∞) + ‖(Λz r (q + i.size + 1) p.2 j).1‖ₑ) ^ b)
            (measurable_weight_Λz r (q + i.size + 1) j b (pr := fun p : ZT i × ZT r => p.2)
              measurable_snd)
          simp only [one_mul] at h2
          simp_rw [e]
          exact h2.trans ((mul_le_mul' hq0 (h1.trans (mul_le_mul'
            ((hi.norm 0).trans_eq (gev_zero_eq _ _)) (hr.wfreq j)))).trans hc1)

end NodeStep

section Weighted

variable {V : Type} (P : ℕ → PSym V)

/-- The product of the pair weights `∏_j (1 + |λ_j|)^wp`. -/
@[expose] noncomputable def Wprod (wp : ℝ) : (c : LegalCode) → ZT c → ℝ
  | .nil => fun _ => 1
  | .node i r => fun z => wFr wp z.1 * (Wprod wp i z.2.1 * Wprod wp r z.2.2)

theorem Wprod_nonneg (wp : ℝ) : ∀ (c : LegalCode) (z : ZT c), 0 ≤ Wprod wp c z
  | .nil, _ => zero_le_one
  | .node i r, z => mul_nonneg (wFr_nonneg wp z.1)
      (mul_nonneg (Wprod_nonneg wp i z.2.1) (Wprod_nonneg wp r z.2.2))

theorem continuous_Wprod (wp : ℝ) : ∀ c : LegalCode, Continuous (Wprod wp c)
  | .nil => continuous_const
  | .node i r => by
    have hw : Continuous (wFr wp) := by
      unfold wFr
      exact (by fun_prop : Continuous fun lam : ℝ × ℝ => 1 + |lam.1| + |lam.2|).rpow_const
        fun lam => Or.inl (by positivity)
    exact (hw.comp continuous_fst).mul (((continuous_Wprod wp i).comp
      (continuous_fst.comp continuous_snd)).mul ((continuous_Wprod wp r).comp
        (continuous_snd.comp continuous_snd)))

/-- **The product of the pair symbols with the pair weights.** -/
@[expose] noncomputable def MzSW (wp : ℝ) (c : LegalCode) (q : ℕ) : (ιT P c q → ℝ) → ZT c → ℂ :=
  fun β z => (Wprod wp c z : ℂ) * MzS P c q β z

theorem MzSW_node (wp : ℝ) (i r : LegalCode) (q : ℕ) :
    MzSW P wp (.node i r) q = pprod (wsym wp (P q).C)
      (pprod (MzSW P wp i (q + 1)) (MzSW P wp r (q + i.size + 1))) := by
  funext β z
  simp only [MzSW, MzS_node, pprod, kprod, wsym, Wprod]
  push_cast
  ring

/-- **The bounds of the weighted product**, from the bounds of the weighted pair symbols. -/
theorem tbound_MzSW {A b wp : ℝ} (hA : 0 ≤ A) {NP : ℕ → ℝ} : ∀ (c : LegalCode) (q : ℕ),
    (∀ j ∈ Set.Ico q (q + c.size), PBound A (NP j) b ⟨(P j).ι, (P j).f, wsym wp (P j).C⟩) →
    TBound A (NT NP c q) b c q (MzSW P wp c q)
  | .nil, q, _ => by
    have e : MzSW P wp .nil q = MzS P .nil q := by
      funext β z; simp [MzSW, Wprod, MzS]
    rw [e]
    exact tbound_MzS P hA .nil q fun j hj => by simp [LegalCode.size] at hj
  | .node i r, q, hP => by
    have hsz : (LegalCode.node i r).size = i.size + r.size + 1 := rfl
    have hi := tbound_MzSW hA i (q + 1) fun j hj => hP j (by simp only [Set.mem_Ico] at hj ⊢; omega)
    have hr := tbound_MzSW hA r (q + i.size + 1)
      fun j hj => hP j (by simp only [Set.mem_Ico] at hj ⊢; omega)
    have hq := hP q (by simp only [Set.mem_Ico]; omega)
    rw [MzSW_node]
    exact TBound.node hA hq hi hr

theorem dnorm_MzSW {wp : ℝ} {c : LegalCode} {q : ℕ}
    (hs : ∀ z, ContDiff ℝ ∞ fun β => MzS P c q β z) (k : ℕ) (β : ιT P c q → ℝ) (z : ZT c) :
    dnorm k (MzSW P wp c q) β z = ENNReal.ofReal (Wprod wp c z) * dnorm k (MzS P c q) β z := by
  unfold MzSW
  rw [dnorm_mul_left k (fun z => (Wprod wp c z : ℂ)) _ hs, ← ofReal_norm, Complex.norm_real,
    Real.norm_of_nonneg (Wprod_nonneg wp c z)]

/-- **The total frequency of the pairs** `Λ(z) = Σ_j (λ_{j,1} + λ_{j,2})`. -/
@[expose] def Λsum : (c : LegalCode) → ZT c → ℝ
  | .nil => fun _ => 0
  | .node i r => fun z => z.1.1 + z.1.2 + (Λsum i z.2.1 + Λsum r z.2.2)

theorem continuous_Λsum : ∀ c : LegalCode, Continuous (Λsum c)
  | .nil => continuous_const
  | .node i r => by
    have hi := continuous_Λsum i
    have hr := continuous_Λsum r
    show Continuous fun z : (ℝ × ℝ) × (ZT i × ZT r) => z.1.1 + z.1.2 + (Λsum i z.2.1 + Λsum r z.2.2)
    fun_prop

/-- `(1 + |Λ(z)|)^wp ≤ ∏_j (1 + |λ_j|)^wp`. -/
theorem one_add_abs_Λsum_rpow_le {wp : ℝ} (hwp : 0 ≤ wp) : ∀ (c : LegalCode) (z : ZT c),
    (1 + |Λsum c z|) ^ wp ≤ Wprod wp c z
  | .nil, _ => by simp [Λsum, Wprod]
  | .node i r, z => by
    have hi := one_add_abs_Λsum_rpow_le hwp i z.2.1
    have hr := one_add_abs_Λsum_rpow_le hwp r z.2.2
    have h1 : 1 + |Λsum (.node i r) z| ≤
        (1 + |z.1.1| + |z.1.2|) * ((1 + |Λsum i z.2.1|) * (1 + |Λsum r z.2.2|)) := by
      have ha := abs_nonneg z.1.1
      have hb := abs_nonneg z.1.2
      have hc := abs_nonneg (Λsum i z.2.1)
      have hd := abs_nonneg (Λsum r z.2.2)
      have ht : |Λsum (.node i r) z| ≤ |z.1.1| + |z.1.2| + (|Λsum i z.2.1| + |Λsum r z.2.2|) := by
        show |z.1.1 + z.1.2 + (Λsum i z.2.1 + Λsum r z.2.2)| ≤ _
        calc _ ≤ |z.1.1 + z.1.2| + |Λsum i z.2.1 + Λsum r z.2.2| := abs_add_le _ _
          _ ≤ _ := add_le_add (abs_add_le _ _) (abs_add_le _ _)
      nlinarith [mul_nonneg ha hc, mul_nonneg ha hd, mul_nonneg hb hc, mul_nonneg hb hd,
        mul_nonneg hc hd, mul_nonneg (mul_nonneg ha hc) hd, mul_nonneg (mul_nonneg hb hc) hd]
    calc (1 + |Λsum (.node i r) z|) ^ wp
        ≤ ((1 + |z.1.1| + |z.1.2|) * ((1 + |Λsum i z.2.1|) * (1 + |Λsum r z.2.2|))) ^ wp :=
          Real.rpow_le_rpow (by positivity) h1 hwp
      _ = (1 + |z.1.1| + |z.1.2|) ^ wp * ((1 + |Λsum i z.2.1|) ^ wp * (1 + |Λsum r z.2.2|) ^ wp) := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity)]
      _ ≤ wFr wp z.1 * (Wprod wp i z.2.1 * Wprod wp r z.2.2) := by
          unfold wFr
          gcongr
          all_goals exact Wprod_nonneg _ _ _

theorem one_add_enorm_Λsum_rpow_le {wp : ℝ} (hwp : 0 ≤ wp) (c : LegalCode) (z : ZT c) :
    (1 + ‖Λsum c z‖ₑ) ^ wp ≤ ENNReal.ofReal (Wprod wp c z) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (abs_nonneg _),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hwp]
  exact ENNReal.ofReal_le_ofReal (one_add_abs_Λsum_rpow_le hwp c z)

end Weighted

section Twist

variable {ι : Type} [Fintype ι]

/-- **The twisted symbol** `e^{πi(λ₁+λ₂)s} 𝒞(λ)`: the symbol of `(u, v) ↦ F(u + s, v + s)`. -/
@[expose] noncomputable def tsym (s : ℝ) (C : (ι → ℝ) → ℝ × ℝ → ℂ) : (ι → ℝ) → ℝ × ℝ → ℂ :=
  fun β lam => cexp (π * I * ((lam.1 + lam.2) * s)) * C β lam

theorem enorm_cexp_pi_I (x : ℝ) : ‖cexp (π * I * x)‖ₑ = 1 := by
  rw [← ofReal_norm, Complex.norm_exp]
  simp

theorem dnorm_tsym (s : ℝ) {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : ∀ γ, ContDiff ℝ ∞ fun β => C β γ)
    (k : ℕ) (β : ι → ℝ) (lam : ℝ × ℝ) : dnorm k (tsym s C) β lam = dnorm k C β lam := by
  unfold tsym
  rw [dnorm_mul_left k (fun lam : ℝ × ℝ => cexp (π * I * ((lam.1 + lam.2) * s))) C hC]
  rw [show ((lam.1 : ℂ) + lam.2) * s = (((lam.1 + lam.2) * s : ℝ) : ℂ) by push_cast; ring,
    enorm_cexp_pi_I, one_mul]

theorem SymReg.twisted {C : (ι → ℝ) → ℝ × ℝ → ℂ} (h : SymReg C) (s : ℝ) : SymReg (tsym s C) where
  smooth γ := contDiff_const.mul (h.smooth γ)
  meas := by
    unfold ClassJR.tsym
    exact ((by fun_prop : Continuous fun x : (ι → ℝ) × (ℝ × ℝ) =>
      cexp (π * I * ((x.2.1 + x.2.2) * s))).measurable.mul h.meas.measurable).stronglyMeasurable
  dom k := by
    have e : supD k (ClassJR.tsym s C) = supD k C := by
      funext γ
      simp only [supD, dnorm_tsym s h.smooth]
    rw [e]
    exact h.dom k

omit [Fintype ι] in
theorem tsym_mul_e2 (s : ℝ) (C : (ι → ℝ) → ℝ × ℝ → ℂ) (β : ι → ℝ) (lam : ℝ × ℝ) (u v : ℝ) :
    tsym s C β lam * e2 lam u v = C β lam * e2 lam (u + s) (v + s) := by
  unfold tsym e2
  rw [mul_comm (cexp _) (C β lam), mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The phases of the twisted pairs**: `∏_j e^{πi(λ_{j,1}+λ_{j,2})s} = e^{πiΛ(z)s}`. -/
theorem Mz_tsym (s : ℝ) (Ĉ : ℕ → ℝ × ℝ → ℂ) : ∀ (c : LegalCode) (q : ℕ) (z : ZT c),
    Mz (fun j lam => cexp (π * I * ((lam.1 + lam.2) * s)) * Ĉ j lam) c q z =
      cexp (π * I * (Λsum c z * s)) * Mz Ĉ c q z
  | .nil, _, _ => by simp [Mz, Λsum]
  | .node i r, q, z => by
    simp only [Mz]
    rw [Mz_tsym s Ĉ i (q + 1) z.2.1, Mz_tsym s Ĉ r (q + i.size + 1) z.2.2]
    have e : cexp (π * I * (Λsum (.node i r) z * s)) = cexp (π * I * ((z.1.1 + z.1.2) * s)) *
        (cexp (π * I * (Λsum i z.2.1 * s)) * cexp (π * I * (Λsum r z.2.2 * s))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [Λsum]
      push_cast
      ring
    rw [e]
    ring

end Twist

end WaveTurbulence.ClassJR
