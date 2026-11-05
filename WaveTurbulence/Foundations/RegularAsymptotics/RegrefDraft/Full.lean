/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegrefDraft.Couples
public import WaveTurbulence.Foundations.RegularAsymptotics.RegrefDraft.TreeItems

/-!
# RA2 REGREF: the B2.1 anchor `regularAsymptotics` from the named obligations RA1 (TARGET Props 6.6–6.8)

**`regularAsymptotics_of_obligations (hRA1c : RA1Couple) (hRA1t : RA1Tree)`** has exactly the type of the pinned
B2.1 anchor `regularAsymptotics` (`/home/scott/wt-scratch/waveb2-snap-final/WaveB2-Statements.lean`, sha256
`82e42b2b…`; statement text copied verbatim, `check/TypeAudit.lean` compares the elaborated types).

* (1), (3) couples, (4): as in `regularAsymptotics_couples`;
* (2), (3) trees: `tree_item2_le`, `tree_item3_le` (translation for `q' = r`; relayering, freezing `s = r` and the
  **trace** estimates for `q' < r`), costing the trace constant `Ktr θ = 2^θ ‖χ₀ ⊗ χ₀‖_{𝔛^θ}`.

Constants: `η₀ = min(η₀^c, η₀^t, 1)`; `C₁ = max(Ktr η, Ktr (1−η)) · max(C^c, C^t)` (RA1's constants at the input
bound `B₁ + 1`); `ν₀ = 1`; `δ₀ = min(δ₁^c, δ₁^t)`; `C₂ = 1`; `L₀ = max(2, L^c, L^t, e)` at the order exponent
`A(d, 𝔇)`.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.Regref

open TTree WaveTurbulence.Fourier

theorem traceConst_ne_top (θ : ℝ) : traceConst (r := 2) θ chiUnit ≠ ⊤ := by
  unfold traceConst
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (timeFourierNorm_lt_top_of_smooth_compact θ (coordinateCutoff_hasCompactSupport chiUnit_hasCompactSupport)
      (coordinateCutoff_contDiff chiUnit_contDiff)).ne

/-- The real trace constant `Ktr θ = 2^θ ‖χ₀ ⊗ χ₀‖_{𝔛^θ}`. -/
noncomputable def Ktr (θ : ℝ) : ℝ := (traceConst (r := 2) θ chiUnit).toReal

theorem one_le_Ktr {θ : ℝ} (hθ : 0 ≤ θ) : 1 ≤ Ktr θ := by
  have h := one_le_traceConst (r := 2) hθ chiUnit_contDiff (coordinateCutoff_chiUnit (t := fun _ => 0)
    ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩⟩)
  have := ENNReal.toReal_mono (traceConst_ne_top θ) h
  simpa [Ktr] using this

theorem traceConst_mul_ofReal (θ : ℝ) (x : ℝ) :
    traceConst (r := 2) θ chiUnit * ENNReal.ofReal x = ENNReal.ofReal (Ktr θ * x) := by
  rw [Ktr, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (traceConst_ne_top θ)]

theorem bound_mono_K {K C C' δ x : ℝ} (n : ℕ) (hK : 1 ≤ K) (hC : 0 ≤ C) (hCC : K * C ≤ C') (hδ : 0 ≤ δ)
    (hx : 0 ≤ x) : K * (C * (C * δ) ^ n * x) ≤ C' * (C' * δ) ^ n * x := by
  have hC' : C ≤ C' := (le_mul_of_one_le_left hC hK).trans hCC
  have h1 : (C * δ) ^ n ≤ (C' * δ) ^ n :=
    pow_le_pow_left₀ (mul_nonneg hC hδ) (mul_le_mul_of_nonneg_right hC' hδ) n
  have hC'0 : 0 ≤ C' := hC.trans hC'
  calc K * (C * (C * δ) ^ n * x) = (K * C) * (C * δ) ^ n * x := by ring
    _ ≤ C' * (C' * δ) ^ n * x := by gcongr

theorem bound_mono_K' {K C C' : ℝ} (n : ℕ) (hK : 1 ≤ K) (hC : 0 ≤ C) (hCC : K * C ≤ C') :
    K * (C * C ^ n) ≤ C' * C' ^ n := by
  have hC' : C ≤ C' := (le_mul_of_one_le_left hC hK).trans hCC
  have hC'0 : 0 ≤ C' := hC.trans hC'
  calc K * (C * C ^ n) = (K * C) * C ^ n := by ring
    _ ≤ C' * C' ^ n := by gcongr

/-- **B2.1 `regularAsymptotics` at its exact type** (TARGET Props `regref1`–`regref3`, F11, F61, F66), from the
named obligations `RA1Couple`, `RA1Tree` (DH23 Prop 6.1, packet RA1). -/
theorem regularAsymptotics_of_obligations (hRA1c : RA1Couple) (hRA1t : RA1Tree) : WTPrefix fun P =>
    ∀ p : ℕ, p < P.D → ∀ r : ℕ, r ≤ p → ∀ R : Mom P.d → ℝ, InputRemainder P R r →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
      let F : Mom P.d → ℝ := fun k => P.φ (P.δ * r) k + R k
      -- (1) regular couples
      (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a = r) →
        XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
          (fun ts k => KQstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
            Q.app P.δ r F (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      -- (2) regular trees
      (∀ X : RegChain, X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1,
        X.DecodesTree LG.garden → ∀ q' : ℕ, q' ≤ r →
        (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else r) →
        XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q') Set.univ
          (fun ts k => KTstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
            X.app P.δ r F (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      -- (3) the factors
      (∀ Q : RegCpl, Q.wf = true → Q.dominant = true → Q.size = 2 * n →
        XNorm00Restr (V := Unit) (1 - P.η) (timeBox r r) Set.univ
            (fun ts _ => (Q.JB r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
          ∀ Z ∈ specialSets Q.links,
            SNormR (30 * P.d) (30 * P.d) (Q.Mstar F Z (0, []) (1, [])) ≤
              ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      (∀ X : RegChain, X.wf = true → X.dominant = true → X.size = 2 * n → ∀ ζ : ℤˣ,
        ∀ q' : ℕ, q' ≤ r →
        XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q') Set.univ
            (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
          ∀ Z ∈ specialSets (X.treeLinks ζ),
            SNormR (30 * P.d) 0 (X.Nstar F Z ζ (0, [])) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      -- (4) the WKE identity (corrected regref1-5)
      (r = p → (∀ k, R k = 0) → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
        ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.dominant = true ∧ Q.size = 2 * n),
            Q.app P.δ p F t t k =
          (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)) := by
  intro d hd γ hγ
  obtain ⟨ηc, hηc, Hc⟩ := hRA1c d hd γ hγ
  obtain ⟨ηt, hηt, Ht⟩ := hRA1t d hd γ hγ
  refine ⟨min (min ηc ηt) 1, lt_min (lt_min hηc hηt) one_pos, fun η hη φin _ τs _ φ hφ => ?_⟩
  have hη0 : 0 < η := hη.1
  have hηc' : η ∈ Ioc 0 ηc := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hηt' : η ∈ Ioc 0 ηt := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hη1 : η ≤ 1 := hη.2.trans (min_le_right _ _)
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_SNormR_bound_of_continuousOn hφ.1 (40 * d) (40 * d)
  obtain ⟨Cc, hCc, δc, hδc, Hc2⟩ := Hc η hηc' (B₁ + 1)
  obtain ⟨Ct, hCt, δt, hδt, Ht2⟩ := Ht η hηt' (B₁ + 1)
  set K := max (Ktr η) (Ktr (1 - η)) with hKdef
  have hK1 : 1 ≤ K := le_max_of_le_left (one_le_Ktr hη0.le)
  set Cm := max Cc Ct with hCmdef
  have hCm0 : 0 ≤ Cm := le_max_of_le_left (zero_le_one.trans hCc)
  set C₁ := K * Cm with hC₁def
  have hC₁ : 1 ≤ C₁ := one_le_mul_of_one_le_of_one_le hK1 (le_max_of_le_left hCc)
  have hKc : 1 * Cc ≤ C₁ := by
    rw [one_mul]
    exact (le_max_left _ _).trans (le_mul_of_one_le_left hCm0 hK1)
  have hKt2 : Ktr η * Ct ≤ C₁ :=
    mul_le_mul (le_max_left _ _) (le_max_right _ _) (zero_le_one.trans hCt) (zero_le_one.trans hK1)
  have hKt3 : Ktr (1 - η) * Ct ≤ C₁ :=
    mul_le_mul (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCt) (zero_le_one.trans hK1)
  have hKt1 : 1 * Ct ≤ C₁ := by
    rw [one_mul]
    exact (le_max_right _ _).trans (le_mul_of_one_le_left hCm0 hK1)
  refine ⟨C₁, hC₁, 1, one_pos, fun ν _ => ⟨min δc δt, lt_min hδc hδt, fun δ hδ D hD hτ => ?_⟩⟩
  have hδc' : δ ∈ Ioc 0 δc := ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩
  have hδt' : δ ∈ Ioc 0 δt := ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩
  obtain ⟨Lc, Hc3⟩ := Hc2 δ hδc' (ordExp d D)
  obtain ⟨Lt, Ht3⟩ := Ht2 δ hδt' (ordExp d D)
  refine ⟨1, le_rfl, max (max (max 2 Lc) Lt) (Real.exp 1),
    le_max_of_le_left (le_max_of_le_left (le_max_left _ _)), fun L hL => ?_⟩
  intro p hp r hr R hR n hn F
  have hL2 : 2 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLc : Lc ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLt : Lt ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hlog : 1 ≤ Real.log L := one_le_log_of_exp_le ((le_max_right _ _).trans hL)
  have hnA : (n : ℝ) ≤ Real.log L ^ ((ordExp d D : ℕ) : ℝ) :=
    le_logPow_ordExp ⟨d, γ, η, φin, τs, φ, C₁, ν, δ, D, 1, L⟩ (by show 1 ≤ d; omega) hlog p n hn
  have hδr : δ * r ∈ Icc 0 τs := by
    have hδ0 : 0 ≤ δ := hδ.1.le
    refine ⟨by positivity, ?_⟩
    rw [hτ, mul_comm (D : ℝ)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (hr.trans hp.le)) hδ0
  have hF : SNormR (40 * d) (40 * d) F ≤ ENNReal.ofReal (B₁ + 1) :=
    SNormR_F_le ⟨d, γ, η, φin, τs, φ, C₁, ν, δ, D, 1, L⟩ (by show 1 ≤ d; omega) (by linarith) hB₁0 hB₁ hδr hR
  have hFs : ∀ k : Mom d, Summable fun m : Fin d → ℤ => |F (k + latticePoint L m)| := fun k =>
    LGSpine.summable_abs_coset_of_SNormR (by linarith) (by omega : d + 1 ≤ 40 * d) (by linarith) F hF k
  obtain ⟨H1, H3a⟩ := Hc3 L hLc F hF n hnA
  obtain ⟨H2, H3b⟩ := Ht3 L hLt F hF n hnA
  have hx : 0 ≤ L ^ (-(gam1 d γ - Real.sqrt η)) := Real.rpow_nonneg (by linarith) _
  have hδ0 : 0 ≤ δ := hδ.1.le
  refine ⟨fun Q hQ hsz LG hdec hlay => ?_, fun X hX hsz LG hdec q' hq hlay => ?_,
    fun Q hQ hdom hsz => ?_, fun X hX hdom hsz ζ q' hq => ?_, fun hrp hR0 => ?_⟩
  · -- (1): translate layer `r` to layer `0`
    rw [regBound_one]
    refine le_trans ?_ ((H1 Q hQ hsz (layer0 LG) hdec fun _ => rfl).trans (ENNReal.ofReal_le_ofReal ?_))
    · refine XNormRestr_shift_le _ _ _ (fun _ => (r : ℝ)) (fun ts hts => sub_mem_timeBox_self hts)
        fun ts _ k _ => ?_
      simp only [Pi.sub_apply]
      rw [KQstar_shift L γ δ F LG hdec.1 r hlay, app_shift δ r F Q]
    · simpa only [one_mul] using bound_mono_K n le_rfl (zero_le_one.trans hCc) hKc hδ0 hx
  · -- (2): one regular tree
    rw [regBound_one]
    refine (tree_item2_le L γ δ F hFs hdec hq hlay hη0.le (Λ := 30 * d) (by omega)
      (H2 X hX hsz (layer0 LG) hdec fun _ => rfl)).trans ?_
    rw [traceConst_mul_ofReal η]
    exact ENNReal.ofReal_le_ofReal (bound_mono_K n (one_le_Ktr hη0.le) (zero_le_one.trans hCt) hKt2 hδ0 hx)
  · -- (3), couples
    obtain ⟨hJ, hM⟩ := H3a Q hQ hdom hsz
    refine ⟨le_trans ?_ (hJ.trans (ENNReal.ofReal_le_ofReal ?_)), fun Z hZ => (hM Z hZ).trans
      (ENNReal.ofReal_le_ofReal ?_)⟩
    · refine XNorm00Restr_shift_le _ (fun _ => (r : ℝ)) (fun ts hts => sub_mem_timeBox_self hts)
        fun ts _ _ _ => ?_
      simp only [Pi.sub_apply]
      rw [JB_shift (r : ℝ) Q]
    · simpa only [one_mul] using bound_mono_K' n le_rfl (zero_le_one.trans hCc) hKc
    · simpa only [one_mul] using bound_mono_K' n le_rfl (zero_le_one.trans hCc) hKc
  · -- (3), trees
    obtain ⟨hJ, hN⟩ := H3b X hX hdom hsz ζ
    refine ⟨(tree_item3_le X hq (by linarith : (0 : ℝ) ≤ 1 - η) hJ).trans ?_, fun Z hZ => (hN Z hZ).trans
      (ENNReal.ofReal_le_ofReal ?_)⟩
    · rw [traceConst_mul_ofReal (1 - η)]
      exact ENNReal.ofReal_le_ofReal (bound_mono_K' n (one_le_Ktr (by linarith)) (zero_le_one.trans hCt) hKt3)
    · simpa only [one_mul] using bound_mono_K' n le_rfl (zero_le_one.trans hCt) hKt1
  · -- (4): MEXP J6
    subst hrp
    exact Mexp.regularAsymptotics_item4 ⟨d, γ, η, φin, τs, φ, C₁, ν, δ, D, 1, L⟩ (by show 2 ≤ d; omega) r R n hR0

end WaveTurbulence.Regref
