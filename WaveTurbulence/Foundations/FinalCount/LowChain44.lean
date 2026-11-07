/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain43
public import WaveTurbulence.Foundations.FinalCount.LowChain30
public import WaveTurbulence.Foundations.FinalCount.LowChain22
public import WaveTurbulence.Foundations.FinalCount.AsmTopClass3
public import WaveTurbulenceVineParam.VineParamMain
public import WaveTurbulence.Foundations.FinalCount.LowIface3
/-! **FINALCOUNT LOW-CHAIN, session 6 (18): `ll_num`** (the numerics) — the original-class loop-provenance class theorem (R79, treatment A).
`LowLoopClassBound d γ η` from `chain_coverLL` (profile `Ypk`, `gk = rankFactor |B| = loopGain^k`), `hmemAtL_of_shape`, `hendAtL_of_inputs2`
(`CnBound` at the ORIGINAL `R`), `hterm_mainL`, and the numerics of `reg_class_bound'` (with `N⁵`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountG8
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

variable {d : ℕ}

/-- `excessprop1 (3)` for Step D1, uniform in the types (from `UStepD1.excess_new`). -/
theorem ex1D_uniform (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs C₂ : ℝ, 0 ≤ Cs ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η ν : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → 1 ≤ ν →
      ∀ {V D₀ : Type} [DecidableEq V] [Fintype D₀] [DecidableEq D₀] (w : Mom d) (M₀ : Molecule V D₀) (C : CollData M₀)
        (P : Finset V → ℝ),
      Ex1D L γ η δ C₁ w M₀ C P (Cs * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) ν := by
  obtain ⟨Cs, C₂, hCs, hC₂, key⟩ := prop94_vine_newcomp WaveTurbulence.Vine.Param.vineparam hd hγ
  refine ⟨Cs, C₂, hCs, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, key2⟩ := key δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η ν hC₁ hη hη1 hν V D₀ _ _ _ w M₀ C P hP0 hPh hMol0 Adm0 hne hSrc0 hDec0 h h' hs hc hAR hMol hnl
    hνat => ?_⟩
  cases hs with
  | vine K hu hl hd2 htwin hsg hnew hdu hdl =>
    refine ⟨K, rfl, fun hcls hconn => ?_⟩
    have hF : K.post.numComponents = h.s.M.numComponents + 1 := by
      have := vine_F_le_succ K; omega
    have hLe : Real.exp 1 ≤ L := hL₀.trans hL
    have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
    have hnc : ¬ K.post.SameComponent K.fa K.fb := fun hh => by
      have := vine_F_le_of_sc K hh
      omega
    have hsingle : SingleVineVC K := by
      rcases hcls with h1 | hS
      · exact h1
      · exfalso
        obtain ⟨S⟩ := hS
        obtain ⟨G, hG, hr⟩ := hconn ⟨S⟩
        have := doubleShape_F_le K S hG hr
        omega
    set cl := FinalCountG3.Cls.beta with hcl
    have hctx1 := hc.cutSt K.cut_a FinalCountG3.Cls.beta (jcls h.s.M K.C.upper) (by simp) (jcls_ne_eps _ _)
    have hctx2 := hctx1.cutSt K.cut_b .beta (jcls h.s.M K.C.lower) (by simp) (jcls_ne_eps _ _)
    have hAdm' : ∀ κ, AdmS Adm0 h.s κ → AdmS Adm0 (vineSt h.s K cl) (fun x => κ x.1) :=
      fun κ hκ => AdmS.delSt (s := (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ cl cl).cutSt K.C.lower K.fb K.y₁ K.y₂ cl cl)
        (fun a => a ∉ K.C.atoms) K.closed hκ
    have hscale : DecScale h.s.M L w (AdmS Adm0 h.s) (SourceLadderGaps h.s.M L w P) := by
      intro c κ' _ _ hAdm
      obtain ⟨k0, hk0, rfl⟩ := hAdm
      obtain ⟨c0, hc0, hc04⟩ := hDec0 k0 hk0
      exact sourceGaps_state hc hPh hMol0 hc0 hc04 (hSrc0 k0 hk0)
    have hgap : ∀ κ, AdmS Adm0 h.s κ → κ K.x₁ ≠ κ K.x₂ := by
      intro κ hκ
      obtain ⟨k0, hk0, rfl⟩ := hκ
      exact gapAt_ne_of_SG (hsg k0 hk0)
    obtain ⟨ν₀, -, hν₀, hfix⟩ := newCompFixed_exists (d := d) (by omega) K hnc hnl hc.d4 (vc_block_of_new K hnc)
      (hL0.ne') (Adm := AdmS Adm0 h.s) (γ := γ) (δ := δ) (w := w) hgap
    have hfix' := newCompFixed_mono hL0 hδ.1 (hν₀.trans hνat) hfix
    have k3 := key2 L hL C₁ η ν hC₁ hη hη1 hν h.s.M K hMol (fun a ha => hc.d4 a ha) hsingle w (AdmS Adm0 h.s)
      (AdmS Adm0 (vineSt h.s K cl)) hAdm' P hP0 hscale
      (fun S' hS' S hS => hc.hPinh hPh hctx1 S' hS' S hS)
      (fun S' hS' S hS => hctx1.hPinh hPh hctx2 S' hS' S hS) hF hfix'
    -- delete the isolated halves of the degree-`2` joints: a dartless restriction, deviation `1`
    have hC0 : 0 < C₁ := lt_of_lt_of_le one_pos (hC₂.trans hC₁)
    set P₂ : V → Prop := fun a => ¬ (a = K.fa ∧ h.s.M.deg K.C.upper = 2) ∧ ¬ (a = K.fb ∧ h.s.M.deg K.C.lower = 2) with hP₂d
    have hPe : ∀ a, VineKeep K a ↔ (a ∉ K.C.atoms) ∧ P₂ a := fun a => Iff.rfl
    have hVK : PClosed K.cutMol (VineKeep K) := VineKeep.closed K
    have hP₂ : PClosed K.post P₂ := pclosed_restrict_of hPe K.closed hVK
    have hno : ∀ x : PDart K.cutMol (fun a => a ∉ K.C.atoms), P₂ (K.post.atom x) := by
      intro x
      refine ⟨fun ⟨he, hd⟩ => ?_, fun ⟨he, hd⟩ => ?_⟩
      · have : x.1 ∈ K.cutMol.dartsAt K.fa := by rw [mem_dartsAt]; exact he
        rw [vineCut_fa_dartless K hd] at this; exact absurd this (Finset.notMem_empty _)
      · have : x.1 ∈ K.cutMol.dartsAt K.fb := by rw [mem_dartsAt]; exact he
        rw [vineCut_fb_dartless K hd] at this; exact absurd this (Finset.notMem_empty _)
    let Adm' : (PDart K.post P₂ → (Fin d → ℤ)) → Prop :=
      fun κ' => ∃ k0, Adm0 k0 ∧ κ' = fun x => k0 (h.s.down x.1.1)
    have hghost := countA_restrict_dartless K.post P₂ hP₂ hno L γ δ C₁ w hL0 hδ.1 hC0
      (AdmS Adm0 (vineSt h.s K cl)) Adm'
      (fun κ hκ => by
        obtain ⟨k0, hk0, rfl⟩ := hκ
        exact ⟨k0, hk0, rfl⟩) P
      (fun S => zero_le_one.trans (ladderWeight_ge_one L γ δ (P S) hLe hδ.1.le (hP0 S)))
    let I : DartIso (restrictP K.post P₂ hP₂) (vineStG h.s K).M :=
      restrictRestrictIso K.cutMol (fun a => a ∉ K.C.atoms) P₂ (VineKeep K) hPe K.closed hVK
    have hiso := I.countA_eq L γ δ C₁ w Adm' (AdmS Adm0 (vineStG h.s K)) (fun κ' => by
      constructor
      · rintro ⟨k0, hk0, e⟩
        refine ⟨k0, hk0, ?_⟩
        funext x
        have := congrFun e (I.e x)
        exact this
      · rintro ⟨k0, hk0, e⟩
        refine ⟨k0, hk0, ?_⟩
        funext y
        have := congrFun e (I.e.symm y)
        simp only [Equiv.apply_symm_apply] at this
        exact this) P
    have htr := isDeviation_trans' k3 hghost
    rw [mul_one] at htr
    show IsDeviation _ ((vineStG h.s K).M.countA L γ δ C₁ w (AdmS Adm0 (vineStG h.s K)) P) _
    rw [← hiso]
    exact htr


theorem rankFactor_nat_eq {L γ δ C₁ : ℝ} (hL : 0 < L) (k : ℕ) :
    rankFactor d L γ δ C₁ (k : ℤ) = loopGain d γ L δ C₁ ^ k := by
  unfold rankFactor loopGain
  have e : (((k : ℤ)) : ℝ) = (k : ℝ) := by simp
  rw [zpow_natCast, e, Real.rpow_mul_natCast hL.le]; ring

section lowloop
variable {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀]

theorem loopAtoms_deg_le {M : Molecule V D₀} {R : ℕ} (hS : SubHypLoop R M) :
    ∀ b ∈ loopAtoms M, M.unloop.deg b ≤ 2 := by
  intro b hb
  obtain ⟨hbM, z, hz1, hz2⟩ := Finset.mem_filter.1 hb
  exact loop_deg_le M hz1 hz2 (deg_le_four (M := M) (hS.bounds b hbM))

end lowloop


/-- The numerical facts of the LOW class bound at a given `(m, δ, L)`: constants, polylog absorption of `N`, and `N⁵`. -/
structure LLNum (d : ℕ) (γ η δ L : ℝ) (m : ℕ) (CA CN CD : ℝ) : Prop where
  hLe : Real.exp 1 ≤ L
  hlog2 : 2 ≤ Real.log L
  hh2 : 2 / L ≤ L ^ (-γ + η)
  hCA : 0 ≤ CA
  hCN : 0 ≤ CN
  hCD : 0 ≤ CD
  hK2 : 0 ≤ ghostConst d (2 * m) η δ
  hK3 : 0 ≤ max (cAlpha d γ η) (cBeta η (2 * m))
  hK4 : 0 ≤ cBeta η (2 * m)
  hN : ∀ N : ℕ, (N : ℝ) ≤ 4096 * (2 * (1 + Real.log L) ^ (m + 1)) ^ 13 →
    (N : ℝ) * max CA CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) ∧
    (N : ℝ) * CD ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) ∧
    (N : ℝ) ≤ L ^ (η ^ 3 - 4 * η ^ 6) ∧
    (N : ℝ) * ghostConst d (2 * m) η δ ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))) ∧
    (N : ℝ) * max (cAlpha d γ η) (cBeta η (2 * m)) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) ∧
    (N : ℝ) * cBeta η (2 * m) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) ∧
    (N : ℝ) ^ 5 ≤ L ^ ((η ^ 5 - 4 * η ^ 6) / 4)

theorem ll_num {γ η : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hη40 : η ≤ 1 / 40) {CsA CsN CsD : ℝ}
    (hCsA : 0 ≤ CsA) (hCsN : 0 ≤ CsN) (hCsD : 0 ≤ CsD) (m : ℕ) {δ : ℝ} (hδ : δ ∈ Ioc (0 : ℝ) 1) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      LLNum d γ η δ L m ((CsA * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13)) * (1 + δ⁻¹))
        (CsN * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8))
        (CsD * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) := by
  have hη1 : η < 1 := by linarith
  have hεpos : ∀ k : ℝ, 0 ≤ k → k ≤ 100 → 0 < η ^ 3 - 4 * η ^ 6 * k := by
    intro k hk0 hk1
    have hη3 : η ^ 3 ≤ 1 / 64000 := by
      have : η ^ 3 ≤ (1 / 40) ^ 3 := pow_le_pow_left₀ hη.le hη40 3
      linarith
    have h6 : η ^ 6 = η ^ 3 * η ^ 3 := by ring
    have h3 : 0 < η ^ 3 := by positivity
    rw [h6]
    nlinarith [mul_pos h3 h3]
  have hε5 : 0 < (η ^ 5 - 4 * η ^ 6) / 4 := by
    have h5 : 4 * η ^ 6 < η ^ 5 := by
      have : η ^ 6 = η ^ 5 * η := by ring
      rw [this]; nlinarith [pow_pos hη 5]
    linarith
  set CAc : ℝ := (CsA * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13)) * (1 + δ⁻¹) with hCAc
  set KNc : ℝ := CsN * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) with hKNc
  set KDc : ℝ := CsD * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) with hKDc
  have hdel : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.1.le
  have hden1 : 0 ≤ 2 * η - η ^ 3 := by nlinarith [pow_pos hη 3]
  have hden2 : 0 ≤ η ^ 2 - η ^ 3 := by nlinarith [pow_pos hη 3, pow_pos hη 2]
  have hCAc0 : 0 ≤ CAc := by rw [hCAc]; positivity
  have hKNc0 : 0 ≤ KNc := by rw [hKNc]; positivity
  have hKDc0 : 0 ≤ KDc := by rw [hKDc]; positivity
  obtain ⟨L1, hL1, h1⟩ := polylog_absorb (4096 * 2 ^ 13 * (CAc + KNc + KDc)) (13 * (m + 1) + m)
    (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) (hεpos _ (by positivity) (by norm_num))
  obtain ⟨L2, hL2, h2⟩ := polylog_absorb (4096 * 2 ^ 13 * ghostConst d (2 * m) η δ) (13 * (m + 1) + m)
    (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))) (hεpos _ (by positivity) (by norm_num))
  obtain ⟨L3, hL3, h3⟩ := polylog_absorb (4096 * 2 ^ 13 * max (cAlpha d γ η) (cBeta η (2 * m))) (13 * (m + 1) + m)
    (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) (hεpos _ (by positivity) (by norm_num))
  obtain ⟨L4, hL4, h4⟩ := polylog_absorb (4096 * 2 ^ 13 * cBeta η (2 * m)) (13 * (m + 1) + m)
    (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) (hεpos _ (by positivity) (by norm_num))
  obtain ⟨L5, hL5, h5⟩ := polylog_absorb ((4096 * 2 ^ 13) ^ 5) (65 * (m + 1)) ((η ^ 5 - 4 * η ^ 6) / 4) hε5
  obtain ⟨L6, hL6, h6⟩ := polylog_absorb 2 0 (1 - γ) (by linarith)
  obtain ⟨L7, hL7, h7⟩ := polylog_absorb (4096 * 2 ^ 13) (13 * (m + 1)) (η ^ 3 - 4 * η ^ 6)
    (by have := hεpos 1 (by norm_num) (by norm_num); linarith)
  clear_value CAc KNc KDc
  have e2 := Real.exp_pos 2
  refine ⟨L1 + L2 + L3 + L4 + L5 + L6 + L7 + Real.exp 2, ?_, fun L hL => ?_⟩
  · linarith
  have hexp1 : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.2 (by norm_num)
  have hL1' : L1 ≤ L := by linarith
  have hL2' : L2 ≤ L := by linarith
  have hL3' : L3 ≤ L := by linarith
  have hL4' : L4 ≤ L := by linarith
  have hL5' : L5 ≤ L := by linarith
  have hL6' : L6 ≤ L := by linarith
  have hL7' : L7 ≤ L := by linarith
  have hLe2 : Real.exp 2 ≤ L := by linarith
  have hLe : Real.exp 1 ≤ L := le_trans hexp1 hLe2
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) hLe
  have hL0 : 0 < L := by linarith
  have hlog2 : 2 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 2) hLe2
    rwa [Real.log_exp] at this
  have hB1 : 1 ≤ 1 + Real.log L := by linarith
  have hBm : 0 ≤ (1 + Real.log L) ^ m := by positivity
  have hν1 : 1 ≤ (1 + Real.log L) ^ m := one_le_pow₀ hB1
  have hh2 : 2 / L ≤ L ^ (-γ + η) := by
    have h6' := h6 L hL6'
    simp only [pow_zero, mul_one] at h6'
    have h7' : 2 / L ≤ L ^ (-γ) := by
      rw [div_le_iff₀ hL0]
      calc (2 : ℝ) ≤ L ^ (1 - γ) := h6'
        _ = L ^ (-γ) * L := by rw [show 1 - γ = -γ + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
    exact le_trans h7' (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hcAl : 0 ≤ cAlpha d γ η := by
    unfold cAlpha
    have : 0 < 1 - γ := by linarith
    positivity
  have hcBe : 0 ≤ cBeta η (2 * m) := by
    unfold cBeta
    exact mul_nonneg (by norm_num) (pow_nonneg (div_nonneg (by positivity) hden2) _)
  have hK2 : 0 ≤ ghostConst d (2 * m) η δ :=
    (triConst_nonneg d (2 * m) hη hδ.1).trans (ghostConst_ge_triConst d (2 * m) hη hδ.1)
  have hK3 : 0 ≤ max (cAlpha d γ η) (cBeta η (2 * m)) := le_trans hcAl (le_max_left _ _)
  have eN : CsN * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) =
      KNc * (1 + Real.log L) ^ m := by rw [hKNc]; ring
  have eD : CsD * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) =
      KDc * (1 + Real.log L) ^ m := by rw [hKDc]; ring
  have hCN0 : 0 ≤ CsN * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) := by
    rw [eN]; exact mul_nonneg hKNc0 hBm
  have hCD0 : 0 ≤ CsD * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) := by
    rw [eD]; exact mul_nonneg hKDc0 hBm
  refine ⟨hLe, hlog2, hh2, hCAc0, hCN0, hCD0, hK2, hK3, hcBe, fun N hNle => ?_⟩
  have hmaxN : max CAc (CsN * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) ≤
      (CAc + KNc + KDc) * (1 + Real.log L) ^ m := by
    rw [eN]
    apply max_le
    · have h1' := mul_le_mul_of_nonneg_left hν1 hCAc0
      calc CAc = CAc * 1 := by ring
        _ ≤ CAc * (1 + Real.log L) ^ m := h1'
        _ ≤ (CAc + KNc + KDc) * (1 + Real.log L) ^ m := by
          rw [add_mul, add_mul]; linarith [mul_nonneg hKNc0 hBm, mul_nonneg hKDc0 hBm]
    · exact mul_le_mul_of_nonneg_right (by linarith) hBm
  have hmaxD : CsD * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) ≤
      (CAc + KNc + KDc) * (1 + Real.log L) ^ m := by
    rw [eD]
    exact mul_le_mul_of_nonneg_right (by linarith) hBm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (Nmul_aux hB1 m hNle (le_trans hCAc0 (le_max_left _ _)) hmaxN (by positivity)) (h1 L hL1')
  · exact le_trans (Nmul_aux hB1 m hNle hCD0 hmaxD (by positivity)) (h1 L hL1')
  · refine le_trans hNle ?_
    have e : (4096 * (2 * (1 + Real.log L) ^ (m + 1)) ^ 13 : ℝ) = 4096 * 2 ^ 13 * (1 + Real.log L) ^ (13 * (m + 1)) := by ring
    rw [e]; exact h7 L hL7'
  · exact le_trans (Nmul_aux hB1 m hNle hK2 (le_mul_of_one_le_right hK2 hν1) hK2) (h2 L hL2')
  · exact le_trans (Nmul_aux hB1 m hNle hK3 (le_mul_of_one_le_right hK3 hν1) hK3) (h3 L hL3')
  · exact le_trans (Nmul_aux hB1 m hNle hcBe (le_mul_of_one_le_right hcBe hν1) hcBe) (h4 L hL4')
  · have hN4' : (N : ℝ) ^ 5 ≤ (4096 * (2 * (1 + Real.log L) ^ (m + 1)) ^ 13) ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hNle 5
    refine le_trans hN4' ?_
    have e : ((4096 * (2 * (1 + Real.log L) ^ (m + 1)) ^ 13) ^ 5 : ℝ) = (4096 * 2 ^ 13) ^ 5 * (1 + Real.log L) ^ (65 * (m + 1)) := by ring
    rw [e]; exact h5 L hL5'

end WaveTurbulence.FinalCountAsm
