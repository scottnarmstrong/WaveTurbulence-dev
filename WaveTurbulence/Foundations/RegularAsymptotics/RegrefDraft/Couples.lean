/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegrefDraft.Orders
public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.WkeId

/-!
# RA2 REGREF, couples: B2.1 items (1), (3) couple part, (4) from RA1 (TARGET Props `regref1`–`regref3`)

TARGET's proof of `regref1`–`regref3` (L1171–L1173): DH23 Prop 6.1 applies (RA1, here the named obligation
`RA1Couple`, stated in layer `0`), because

* `K*_𝒬` and `(K*_𝒬)_app` are invariant under translating all times by `r` (`KQstar_shift`, `app_shift`, which use
  the telescoping `∑ ζ_𝔫 Ω_𝔫 = 0` of couples, `sum_sign_omega_couple`), and the `𝔛` restriction norms are
  translation invariant (`XNormRestr_shift_le`, `XNorm00Restr_shift_le`);
* the inputs `F_r = φ(δr) + R_r` are real and bounded in `𝔖^{40d,40d}` uniformly (`exists_SNormR_bound_of_continuousOn`,
  `SNormR_input_le`, with `L^{-θ_r} ≤ 1`);
* every order `n ≤ N_{p+1}^4` is polylogarithmic (`le_logPow_ordExp`).

Item (4) is MEXP's `regularAsymptotics_item4` (J6 WKE-ID).

**`regularAsymptotics_couples`** is B2.1 with the conjuncts (1), (3) (couples) and (4), verbatim.
Constants: `C₁ := C` of RA1 for the input bound `B₁ + 1` (`B₁` the `𝔖^{40d,40d}` bound of `φ` on `[0, τ★]`),
`ν₀ := 1`, `δ₀ := δ₁` of RA1, `C₂ := 1`, `L₀ := max (max 2 L₁) e` with `L₁` RA1's `L₀` for the order exponent
`A(d, 𝔇)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Regref

open TTree

theorem sub_mem_timeBox {q q' : ℝ} {ts : Fin 2 → ℝ} (h : ts ∈ timeBox q q') :
    ts - (fun _ => q) ∈ timeBox 0 (q' - q) := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [Pi.sub_apply] <;> linarith

theorem sub_mem_timeBox_self {q : ℝ} {ts : Fin 2 → ℝ} (h : ts ∈ timeBox q q) :
    ts - (fun _ => q) ∈ timeBox 0 0 := by
  simpa using sub_mem_timeBox h

theorem regBound_one (P : WTParams) (n : ℕ) :
    regBound P n 1 = ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(gam1 P.d P.γ - Real.sqrt P.η))) := by
  simp only [regBound, Nat.cast_one, mul_one, gamma1_eq]

theorem one_le_log_of_exp_le {L : ℝ} (h : Real.exp 1 ≤ L) : 1 ≤ Real.log L := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) h

/-- The input bound of RA1 at `F_r = φ(δr) + R_r`. -/
theorem SNormR_F_le (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) {B₁ : ℝ} (hB₁ : 0 ≤ B₁)
    (hφ : ∀ τ ∈ Icc 0 P.τstar, SNormR (40 * P.d) (40 * P.d) (P.φ τ) ≤ ENNReal.ofReal B₁)
    {r : ℕ} (hr : P.δ * r ∈ Icc 0 P.τstar) {R : Mom P.d → ℝ} (hR : InputRemainder P R r) :
    SNormR (40 * P.d) (40 * P.d) (fun k => P.φ (P.δ * r) k + R k) ≤ ENNReal.ofReal (B₁ + 1) := by
  refine SNormR_input_le (by omega) (P.φ (P.δ * r)) hB₁ zero_le_one (hφ _ hr) (hR.trans ?_)
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_one_of_one_le_of_nonpos hL ?_)
  have : 0 ≤ P.theta r := by unfold WTParams.theta; positivity
  linarith

/-- **B2.1 for regular couples** (items (1), (3) couple part, (4); TARGET Props `regref1`–`regref3`), from the named
obligation `RA1Couple` (DH23 Prop 6.1, packet RA1). The statement is B2.1 `regularAsymptotics` with the tree
conjuncts (2), (3b) removed, verbatim otherwise. -/
theorem regularAsymptotics_couples (hRA1 : RA1Couple) : WTPrefix fun P =>
    ∀ p : ℕ, p < P.D → ∀ r : ℕ, r ≤ p → ∀ R : Mom P.d → ℝ, InputRemainder P R r →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
      let F : Mom P.d → ℝ := fun k => P.φ (P.δ * r) k + R k
      -- (1) regular couples
      (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a = r) →
        XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
          (fun ts k => KQstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
            Q.app P.δ r F (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      -- (3) the factors, couples
      (∀ Q : RegCpl, Q.wf = true → Q.dominant = true → Q.size = 2 * n →
        XNorm00Restr (V := Unit) (1 - P.η) (timeBox r r) Set.univ
            (fun ts _ => (Q.JB r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
          ∀ Z ∈ specialSets Q.links,
            SNormR (30 * P.d) (30 * P.d) (Q.Mstar F Z (0, []) (1, [])) ≤
              ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      -- (4) the WKE identity (corrected regref1-5)
      (r = p → (∀ k, R k = 0) → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
        ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.dominant = true ∧ Q.size = 2 * n),
            Q.app P.δ p F t t k =
          (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := hRA1 d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin _ τs _ φ hφ => ?_⟩
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_SNormR_bound_of_continuousOn hφ.1 (40 * d) (40 * d)
  obtain ⟨C, hC1, δ₁, hδ₁, H2⟩ := H η hη (B₁ + 1)
  refine ⟨C, hC1, 1, one_pos, fun ν _ => ⟨δ₁, hδ₁, fun δ hδ D hD hτ => ?_⟩⟩
  obtain ⟨L₁, H3⟩ := H2 δ hδ (ordExp d D)
  refine ⟨1, le_rfl, max (max 2 L₁) (Real.exp 1), le_max_of_le_left (le_max_left _ _), fun L hL => ?_⟩
  intro p hp r hr R hR n hn F
  have hL2 : 2 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hlog : 1 ≤ Real.log L := one_le_log_of_exp_le ((le_max_right _ _).trans hL)
  have hnA : (n : ℝ) ≤ Real.log L ^ ((ordExp d D : ℕ) : ℝ) :=
    le_logPow_ordExp ⟨d, γ, η, φin, τs, φ, C, ν, δ, D, 1, L⟩ (by show 1 ≤ d; omega) hlog p n hn
  have hδr : δ * r ∈ Icc 0 τs := by
    have hδ0 : 0 ≤ δ := hδ.1.le
    refine ⟨by positivity, ?_⟩
    rw [hτ, mul_comm (D : ℝ)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (hr.trans hp.le)) hδ0
  have hF : SNormR (40 * d) (40 * d) F ≤ ENNReal.ofReal (B₁ + 1) :=
    SNormR_F_le ⟨d, γ, η, φin, τs, φ, C, ν, δ, D, 1, L⟩ (by show 1 ≤ d; omega) (by linarith) hB₁0 hB₁ hδr hR
  obtain ⟨H1, H3a⟩ := H3 L ((le_max_right _ _).trans ((le_max_left _ _).trans hL)) F hF n hnA
  refine ⟨fun Q hQ hsz LG hdec hlay => ?_, fun Q hQ hdom hsz => ?_, fun hrp hR0 => ?_⟩
  · -- (1): translate layer `r` to layer `0`
    rw [regBound_one]
    refine le_trans ?_ (H1 Q hQ hsz (layer0 LG) hdec fun _ => rfl)
    refine XNormRestr_shift_le _ _ _ (fun _ => (r : ℝ)) (fun ts hts => sub_mem_timeBox_self hts)
      fun ts _ k _ => ?_
    simp only [Pi.sub_apply]
    rw [KQstar_shift L γ δ F LG hdec.1 r hlay, app_shift δ r F Q]
  · -- (3), couples: translate `𝒥ℬ*`; `ℳ*` does not see the layer
    obtain ⟨hJ, hM⟩ := H3a Q hQ hdom hsz
    refine ⟨le_trans ?_ hJ, hM⟩
    refine XNorm00Restr_shift_le _ (fun _ => (r : ℝ)) (fun ts hts => sub_mem_timeBox_self hts)
      fun ts _ _ _ => ?_
    simp only [Pi.sub_apply]
    rw [JB_shift (r : ℝ) Q]
  · -- (4): MEXP J6
    subst hrp
    exact Mexp.regularAsymptotics_item4 ⟨d, γ, η, φin, τs, φ, C, ν, δ, D, 1, L⟩ (by show 2 ≤ d; omega) r R n hR0

end WaveTurbulence.Regref
