/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceAll1
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.SpaceG

/-! # P4-W2 (R82 step 2): the dispatch of the remainder summands `rA1 … rB3`

Orientation (`FlagXY ε ex ey`: the first spatial argument is `x = k + ex r`, the second `y = k + ey r`; `k` = the momentum of the pair row = ret, `k + ε r` = low):
the `K` row sits at the momentum `k`, so a summand whose factor at `k` is a separated couple uses `pieceRep_SR`, a tree remainder `pieceRep_RmDS`, a couple remainder `pieceRep_RmS`, `pieceRep_RR`, `pieceRep_RP`.
The remainders enter through `RemC` data (`hRQ`, `hRT`: the point functions are the `f` of the `RemC`). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.LGSpine WaveTurbulence.VineEstS4c
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 MeasureTheory
open scoped ENNReal ComplexConjugate
variable {A : ℝ} {P : WTParams}

theorem FlagXY.ex_eq {ε ex ey : ℝ} (h : FlagXY ε ex ey) (hey : ey = 0) : ex = ε := by
  rcases h.2 with ⟨hx, hy⟩ | ⟨_, hx⟩
  · have : ε = 0 := by rw [← hy, hey]
    have := h.1; simp_all
  · exact hx

theorem FlagXY.ey_eq {ε ex ey : ℝ} (h : FlagXY ε ex ey) (hex : ex = 0) : ey = ε := by
  rcases h.2 with ⟨_, hy⟩ | ⟨hy, hx⟩
  · exact hy
  · have : ε = 0 := by rw [← hx, hex]
    have := h.1; simp_all

/-- Translation of a plain spatial multiplier by `a` (`‖a‖ ≤ 1`). -/
theorem snorm_shift_plain {d A W : ℕ} (hd : 1 ≤ d) (hA : A ≠ 0) (c : ℝ) {β : ℝ} (hβ : 0 ≤ β) (M : Mom d → ℝ)
    (h : SNorm A W (cm M) ≤ ENNReal.ofReal β) (a : Mom d) (ha : ‖a‖ ≤ 1) :
    SNorm A W (fun k => (c : ℂ) * (M (k + a) : ℂ)) ≤ ENNReal.ofReal (|c| * ((2 : ℝ) ^ W * (d : ℝ) ^ A * β)) := by
  have hMc : ContDiff ℝ A (cm M) := contDiff_of_SNorm_le' hA (cm M) β h
  have ht := SNorm_translate_le hd hMc hβ h a ha
  refine (WaveTurbulence.VineEstS3.Eng.SNorm_smul_le A W (c : ℂ) _).trans ?_
  rw [ENNReal.ofReal_mul (abs_nonneg c)]
  refine mul_le_mul' (le_of_eq ?_) ht
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]

/-- rA1 with the `K` row separated (`e_y = 0`): `1_{t₀<t₁} conj Q(s₁,t₀,k) RT(t₁,t₀,k + ε r)`. -/
theorem pieceAll_rA1_SR (G : AmbP A P) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (hey : ey = 0) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (RT : β → ℝ → ℝ → Mom P.d → ℂ) (b : β) (i : Fin (S.mQ b))
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CR : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (rt : RemC P 0 BL qL CR)
      (hRT : ∀ s t, ![s, t] ∈ rt.Bc → ∀ k, RT b s t k = rt.f ![s, t] k) (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        slotVal D τ tt t0 < slotVal D τ tt t1 ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.Bc) ∧
        ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ rt.Bc) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1)
        (fun τ tt r k => rA1 S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) RT b i)
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (|cq.c| * CMq)) (C' * ENNReal.ofReal CR) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_SR (A := A) (P := P) G
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl hey t0 s1 t1 β S RT b i BK BL qK qL CJq CMq CR cq rt hRT Bx hG => ?_⟩
  have hex := hfl.ex_eq hey
  have h0 := h D hI hwN vp vb ε (fun _ _ => 1) ![s1, t0] ![t1, t0] (cJ cq.J) (spPlain cq.c cq.M) rt cq.hcell cq.hint cq.hBcB cq.hBci
    (continuousOn_cJ cq.hcont) cq.hJc (supK_plain hwN hwDec G.hd1 vp cq.toSepT) Bx
    (fun τ tt r k => 1 * (cJ cq.J ![slotVal D τ tt s1, slotVal D τ tt t0] * spPlain cq.c cq.M r k *
      rt.f ![slotVal D τ tt t1, slotVal D τ tt t0] (k + ε • r)))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, ⟨_, bq⟩, bt⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bq, by rw [vec2_slot]; exact bt, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, ⟨vq, _⟩, bt⟩ := hg hd
  subst hey
  rw [hex]
  simp only [rA1, if_pos hi, (hRT _ _ bt), cq.hV _ _ vq, conj_sepTerm, spPlain, cJ, zero_smul, add_zero]
  ring

/-- rA1 with the `K` row the tree remainder (`e_x = 0`): `conj Q(s₁,t₀,k + ε r) RT(t₁,t₀,k)`. -/
theorem pieceAll_rA1_RmDS (G : AmbP A P) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (hex : ex = 0) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (RT : β → ℝ → ℝ → Mom P.d → ℂ) (b : β)
      (i : Fin (S.mQ b)) {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CR : ℝ}
      (cq : CertTerm P (30 * P.d) BL qL CJq CMq (S.sQ b i)) (rt : RemC P 0 BK qK CR)
      (hRT : ∀ s t, ![s, t] ∈ rt.Bc → ∀ k, RT b s t k = rt.f ![s, t] k)
      (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        slotVal D τ tt t0 < slotVal D τ tt t1 ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ rt.Bc ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ cq.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1)
        (fun τ tt r k => rA1 S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) RT b i)
        (C * ENNReal.ofReal CR * ENNReal.ofReal (|cq.c| * ((2 : ℝ) ^ (30 * P.d) * (P.d : ℝ) ^ D.wN * CMq))) (C' * ENNReal.ofReal CJq * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_RmDS (A := A) (P := P) G
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl hex t0 s1 t1 β S RT b i BK BL qK qL CJq CMq CR cq rt hRT Bx hG => ?_⟩
  have hey := hfl.ey_eq hex
  have hMq : ⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl vp)) (cutW (fun r k => (cq.c : ℂ) * (cq.M (k + ε • r) : ℂ)) r) ≤
      ENNReal.ofReal (|cq.c| * ((2 : ℝ) ^ (30 * P.d) * (P.d : ℝ) ^ D.wN * CMq)) := by
    refine snorm_cutW_le _ fun r hr => ?_
    rw [show rowOrder D (Sum.inl vp) = 30 * P.d from hwDec]
    exact snorm_shift_plain G.hd1 (by have := G.hd1; omega) cq.c cq.hCM cq.M
      (sn_lo G.hd1 (by omega) le_rfl cq.hM cq.hCM) (ε • r) (norm_smul_unit (le_of_eq hfl.1) hr)
  have h0 := h D hI hwN hwDec vp vb ε (fun _ _ => 1) ![t1, t0] ![s1, t0] (cJ cq.J)
    (cutW (fun r k => (cq.c : ℂ) * (cq.M (k + ε • r) : ℂ))) rt cq.hcell cq.hint cq.hBcB cq.hBci
    (continuousOn_cJ cq.hcont) cq.hJc hMq Bx
    (fun τ tt r k => 1 * (rt.f ![slotVal D τ tt t1, slotVal D τ tt t0] k *
      cutW (fun r k => (cq.c : ℂ) * (cq.M (k + ε • r) : ℂ)) r k * cJ cq.J ![slotVal D τ tt s1, slotVal D τ tt t0]))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bt, ⟨_, bq⟩⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bt, by rw [vec2_slot]; exact bq, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, bt, ⟨vq, _⟩⟩ := hg hd
  subst hex
  rw [hey]
  simp only [rA1, if_pos hi, (hRT _ _ bt), cq.hV _ _ vq, conj_sepTerm, cutW_of_le hr, cJ, zero_smul, add_zero]
  ring

/-- rA2 (any orientation): `conj RQ(s₁,t₀,y) T(t₁,t₀,x)`, `K` the shifted couple remainder (`u = e_y`), the tree factor's spatial part at `x` a weight-`0` multiplier. -/
theorem pieceAll_rA2_RmS (G : AmbP A P) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (RQ : β → ℝ → ℝ → Mom P.d → ℂ) (b : β)
      (j : Fin (S.mT b)) {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CR CJt CMt : ℝ}
      (rq : RemC P (30 * P.d) BK qK CR) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j))
      (hRQ : ∀ s t, ![s, t] ∈ rq.Bc → ∀ k, RQ b s t k = rq.f ![s, t] k)
      (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        slotVal D τ tt t0 < slotVal D τ tt t1 ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ rq.Bc ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1)
        (fun τ tt r k => rA2 S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) RQ b j)
        (C * ENNReal.ofReal CR * ENNReal.ofReal (|ct.c| * ((2 : ℝ) ^ 0 * (P.d : ℝ) ^ D.wN * CMt))) (C' * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_RmS (A := A) (P := P) G
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 β S RQ b j BK BL qK qL CR CJt CMt rq ct hRQ Bx hG => ?_⟩
  have hMt : ∀ r : Mom P.d, ‖r‖ ≤ 1 → SNorm D.wN 0 ((fun r k => (ct.c : ℂ) * (ct.M (k + ex • r) : ℂ)) r) ≤
      ENNReal.ofReal (|ct.c| * ((2 : ℝ) ^ 0 * (P.d : ℝ) ^ D.wN * CMt)) := fun r hr =>
    snorm_shift_plain G.hd1 (by have := G.hd1; omega) ct.c ct.hCM ct.M (sn_lo G.hd1 (by omega) le_rfl ct.hM ct.hCM) (ex • r)
      (norm_smul_unit hfl.abs_ex_le hr)
  have h0 := h D hI hwN hwDec vp vb ε ey (fun _ _ => 1) ![s1, t0] ![t1, t0] ct.J
    (fun r k => (ct.c : ℂ) * (ct.M (k + ex • r) : ℂ)) rq.conj hfl.abs_ey_le ct.hcell ct.hint ct.hBcB ct.hBci ct.hcont ct.hJ hMt Bx
    (fun τ tt r k => 1 * (rq.conj.f ![slotVal D τ tt s1, slotVal D τ tt t0] (k + ey • r) *
      ((ct.c : ℂ) * (ct.M (k + ex • r) : ℂ)) * ct.J ![slotVal D τ tt t1, slotVal D τ tt t0]))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bq, ⟨_, bt⟩⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bq, by rw [vec2_slot]; exact bt, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, bq, ⟨vt, _⟩⟩ := hg hd
  simp only [rA2, if_pos hi, (hRQ _ _ bq), ct.hV _ _ vt, sepTerm, RemC.conj]
  ring

/-- rA3 with `e_y = 0`: `1_{t₀<t₁} conj RQ(s₁,t₀,k) RT(t₁,t₀,k + ε r)`. -/
theorem pieceAll_rA3_RR (G : AmbP A P) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (hey : ey = 0) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (RQ RT : β → ℝ → ℝ → Mom P.d → ℂ) (b : β)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CQ CT : ℝ}
      (rq : RemC P (30 * P.d) BK qK CQ) (rt : RemC P 0 BL qL CT)
      (hRQ : ∀ s t, ![s, t] ∈ rq.Bc → ∀ k, RQ b s t k = rq.f ![s, t] k) (hRT : ∀ s t, ![s, t] ∈ rt.Bc → ∀ k, RT b s t k = rt.f ![s, t] k)
      (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        slotVal D τ tt t0 < slotVal D τ tt t1 ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ rq.Bc ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ rt.Bc) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1)
        (fun τ tt r k => rA3 (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) RQ RT b)
        (C * ENNReal.ofReal CQ) (C' * ENNReal.ofReal CT) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_RR (A := A) (P := P) G
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl hey t0 s1 t1 β RQ RT b BK BL qK qL CQ CT rq rt hRQ hRT Bx hG => ?_⟩
  have hex := hfl.ex_eq hey
  have h0 := h D hI hwN hwDec vp vb ε (fun _ _ => 1) ![s1, t0] ![t1, t0] rq.conj rt Bx
    (fun τ tt r k => 1 * (rq.conj.f ![slotVal D τ tt s1, slotVal D τ tt t0] k *
      rt.f ![slotVal D τ tt t1, slotVal D τ tt t0] (k + ε • r)))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bq, bt⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bq, by rw [vec2_slot]; exact bt, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, bq, bt⟩ := hg hd
  subst hey
  rw [hex]
  simp only [rA3, if_pos hi, (hRQ _ _ bq), (hRT _ _ bt), RemC.conj, zero_smul, add_zero]
  ring

/-- rA3 with `e_x = 0`: `1_{t₀<t₁} conj RQ(s₁,t₀,k + ε r) RT(t₁,t₀,k)` (three-clock product row). -/
theorem pieceAll_rA3_RP (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (hex : ex = 0) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (RQ RT : β → ℝ → ℝ → Mom P.d → ℂ) (b : β)
      (sL : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CQ CT : ℝ}
      (rq : RemC P (30 * P.d) BK qK CQ) (rt : RemC P 0 BL qL CT)
      (hRQ : ∀ s t, ![s, t] ∈ rq.Bc → ∀ k, RQ b s t k = rq.f ![s, t] k) (hRT : ∀ s t, ![s, t] ∈ rt.Bc → ∀ k, RT b s t k = rt.f ![s, t] k)
      (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        slotVal D τ tt t0 < slotVal D τ tt t1 ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ rq.Bc ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ rt.Bc) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1)
        (fun τ tt r k => rA3 (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) RQ RT b)
        (C * ENNReal.ofReal CQ * ENNReal.ofReal CT) (ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_RP (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl hex t0 s1 t1 β RQ RT b sL BK BL qK qL CQ CT rq rt hRQ hRT Bx hG => ?_⟩
  have hey := hfl.ey_eq hex
  have h0 := h D hI hwN hwDec vp vb ε ey (fun _ _ => 1) ![s1, t1, t0] sL rq.conj rt hfl.abs_ey_le Bx
    (fun τ tt r k => 1 * (rq.conj.f ![slotVal D τ tt s1, slotVal D τ tt t0] (k + ey • r) *
      rt.f ![slotVal D τ tt t1, slotVal D τ tt t0] k))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bq, bt⟩ := hg hd
      exact ⟨⟨bq, bt⟩, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, bq, bt⟩ := hg hd
  subst hex
  simp only [rA3, if_pos hi, (hRQ _ _ bq), (hRT _ _ bt), RemC.conj, zero_smul, add_zero]
  ring

/-- rB1 with `e_x = 0`: `1_{t₀<s₁} Q(t₁,t₀,k) conj RT(s₁,t₀,k + ε r)`. -/
theorem pieceAll_rB1_SR (G : AmbP A P) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (hex : ex = 0) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (RT : β → ℝ → ℝ → Mom P.d → ℂ) (b : β)
      (i : Fin (S.mQ b)) {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CR : ℝ}
      (cq : CertTerm P (30 * P.d) BK qK CJq CMq (S.sQ b i)) (rt : RemC P 0 BL qL CR)
      (hRT : ∀ s t, ![s, t] ∈ rt.Bc → ∀ k, RT b s t k = rt.f ![s, t] k)
      (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        slotVal D τ tt t0 < slotVal D τ tt s1 ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.Bc) ∧
        ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ rt.Bc) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1)
        (fun τ tt r k => rB1 S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) RT b i)
        (C * ENNReal.ofReal CJq * ENNReal.ofReal (|cq.c| * CMq)) (C' * ENNReal.ofReal CR) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_SR (A := A) (P := P) G
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl hex t0 s1 t1 β S RT b i BK BL qK qL CJq CMq CR cq rt hRT Bx hG => ?_⟩
  have hey := hfl.ey_eq hex
  have h0 := h D hI hwN vp vb ε (fun _ _ => 1) ![t1, t0] ![s1, t0] cq.J (spPlain cq.c cq.M) rt.conj cq.hcell cq.hint cq.hBcB cq.hBci
    cq.hcont cq.hJ (supK_plain hwN hwDec G.hd1 vp cq.toSepT) Bx
    (fun τ tt r k => 1 * (cq.J ![slotVal D τ tt t1, slotVal D τ tt t0] * spPlain cq.c cq.M r k *
      rt.conj.f ![slotVal D τ tt s1, slotVal D τ tt t0] (k + ε • r)))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, ⟨_, bq⟩, bt⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bq, by rw [vec2_slot]; exact bt, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, ⟨vq, _⟩, bt⟩ := hg hd
  subst hex
  rw [hey]
  simp only [rB1, if_pos hi, (hRT _ _ bt), cq.hV _ _ vq, spPlain, RemC.conj, zero_smul, add_zero, sepTerm]
  ring

/-- rB1 with `e_y = 0`: `1_{t₀<s₁} Q(t₁,t₀,k + ε r) conj RT(s₁,t₀,k)`. -/
theorem pieceAll_rB1_RmDS (G : AmbP A P) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (hey : ey = 0) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (RT : β → ℝ → ℝ → Mom P.d → ℂ) (b : β)
      (i : Fin (S.mQ b)) {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CJq CMq CR : ℝ}
      (cq : CertTerm P (30 * P.d) BL qL CJq CMq (S.sQ b i)) (rt : RemC P 0 BK qK CR)
      (hRT : ∀ s t, ![s, t] ∈ rt.Bc → ∀ k, RT b s t k = rt.f ![s, t] k)
      (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        slotVal D τ tt t0 < slotVal D τ tt s1 ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ rt.Bc ∧
        (![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.V ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ cq.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1)
        (fun τ tt r k => rB1 S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) RT b i)
        (C * ENNReal.ofReal CR * ENNReal.ofReal (|cq.c| * ((2 : ℝ) ^ (30 * P.d) * (P.d : ℝ) ^ D.wN * CMq))) (C' * ENNReal.ofReal CJq * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_RmDS (A := A) (P := P) G
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl hey t0 s1 t1 β S RT b i BK BL qK qL CJq CMq CR cq rt hRT Bx hG => ?_⟩
  have hex := hfl.ex_eq hey
  have hMq : ⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl vp)) (cutW (fun r k => (cq.c : ℂ) * (cq.M (k + ε • r) : ℂ)) r) ≤
      ENNReal.ofReal (|cq.c| * ((2 : ℝ) ^ (30 * P.d) * (P.d : ℝ) ^ D.wN * CMq)) := by
    refine snorm_cutW_le _ fun r hr => ?_
    rw [show rowOrder D (Sum.inl vp) = 30 * P.d from hwDec]
    exact snorm_shift_plain G.hd1 (by have := G.hd1; omega) cq.c cq.hCM cq.M
      (sn_lo G.hd1 (by omega) le_rfl cq.hM cq.hCM) (ε • r) (norm_smul_unit (le_of_eq hfl.1) hr)
  have h0 := h D hI hwN hwDec vp vb ε (fun _ _ => 1) ![s1, t0] ![t1, t0] cq.J
    (cutW (fun r k => (cq.c : ℂ) * (cq.M (k + ε • r) : ℂ))) rt.conj cq.hcell cq.hint cq.hBcB cq.hBci
    cq.hcont cq.hJ hMq Bx
    (fun τ tt r k => 1 * (rt.conj.f ![slotVal D τ tt s1, slotVal D τ tt t0] k *
      cutW (fun r k => (cq.c : ℂ) * (cq.M (k + ε • r) : ℂ)) r k * cq.J ![slotVal D τ tt t1, slotVal D τ tt t0]))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bt, ⟨_, bq⟩⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bt, by rw [vec2_slot]; exact bq, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, bt, ⟨vq, _⟩⟩ := hg hd
  subst hey
  rw [hex]
  simp only [rB1, if_pos hi, (hRT _ _ bt), cq.hV _ _ vq, cutW_of_le hr, RemC.conj, zero_smul, add_zero, sepTerm]
  ring

/-- rB2 (any orientation): `RQ(t₁,t₀,x) conj T(s₁,t₀,y)`, `K` the couple remainder shifted by `u = e_x`, the tree factor at `y` a weight-`0` multiplier. -/
theorem pieceAll_rB2_RmS (G : AmbP A P) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (S : SepTerms β P.d) (RQ : β → ℝ → ℝ → Mom P.d → ℂ) (b : β)
      (j : Fin (S.mT b)) {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CR CJt CMt : ℝ}
      (rq : RemC P (30 * P.d) BK qK CR) (ct : CertTerm P 0 BL qL CJt CMt (S.sT b j))
      (hRQ : ∀ s t, ![s, t] ∈ rq.Bc → ∀ k, RQ b s t k = rq.f ![s, t] k)
      (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        slotVal D τ tt t0 < slotVal D τ tt s1 ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ rq.Bc ∧
        (![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.V ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ ct.Bc)) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1)
        (fun τ tt r k => rB2 S (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) RQ b j)
        (C * ENNReal.ofReal CR * ENNReal.ofReal (|ct.c| * ((2 : ℝ) ^ 0 * (P.d : ℝ) ^ D.wN * CMt))) (C' * ENNReal.ofReal CJt * ENNReal.ofReal 1) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_RmS (A := A) (P := P) G
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 β S RQ b j BK BL qK qL CR CJt CMt rq ct hRQ Bx hG => ?_⟩
  have hMt : ∀ r : Mom P.d, ‖r‖ ≤ 1 → SNorm D.wN 0 ((fun r k => (ct.c : ℂ) * (ct.M (k + ey • r) : ℂ)) r) ≤
      ENNReal.ofReal (|ct.c| * ((2 : ℝ) ^ 0 * (P.d : ℝ) ^ D.wN * CMt)) := fun r hr =>
    snorm_shift_plain G.hd1 (by have := G.hd1; omega) ct.c ct.hCM ct.M (sn_lo G.hd1 (by omega) le_rfl ct.hM ct.hCM) (ey • r)
      (norm_smul_unit hfl.abs_ey_le hr)
  have h0 := h D hI hwN hwDec vp vb ε ex (fun _ _ => 1) ![t1, t0] ![s1, t0] (cJ ct.J)
    (fun r k => (ct.c : ℂ) * (ct.M (k + ey • r) : ℂ)) rq hfl.abs_ex_le ct.hcell ct.hint ct.hBcB ct.hBci
    (continuousOn_cJ ct.hcont) ct.hJc hMt Bx
    (fun τ tt r k => 1 * (rq.f ![slotVal D τ tt t1, slotVal D τ tt t0] (k + ex • r) *
      ((ct.c : ℂ) * (ct.M (k + ey • r) : ℂ)) * cJ ct.J ![slotVal D τ tt s1, slotVal D τ tt t0]))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bq, ⟨_, bt⟩⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bq, by rw [vec2_slot]; exact bt, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, bq, ⟨vt, _⟩⟩ := hg hd
  simp only [rB2, if_pos hi, (hRQ _ _ bq), ct.hV _ _ vt, conj_sepTerm, cJ]
  ring

/-- rB3 with `e_x = 0`: `1_{t₀<s₁} RQ(t₁,t₀,k) conj RT(s₁,t₀,k + ε r)`. -/
theorem pieceAll_rB3_RR (G : AmbP A P) :
    ∃ C C' : ℝ≥0∞, C ≠ ⊤ ∧ C' ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (hex : ex = 0) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (RQ RT : β → ℝ → ℝ → Mom P.d → ℂ) (b : β)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CQ CT : ℝ}
      (rq : RemC P (30 * P.d) BK qK CQ) (rt : RemC P 0 BL qL CT)
      (hRQ : ∀ s t, ![s, t] ∈ rq.Bc → ∀ k, RQ b s t k = rq.f ![s, t] k) (hRT : ∀ s t, ![s, t] ∈ rt.Bc → ∀ k, RT b s t k = rt.f ![s, t] k)
      (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        slotVal D τ tt t0 < slotVal D τ tt s1 ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ rq.Bc ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ rt.Bc) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1)
        (fun τ tt r k => rB3 (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) RQ RT b)
        (C * ENNReal.ofReal CQ) (C' * ENNReal.ofReal CT) Bx := by
  obtain ⟨C, C', hC, hC', h⟩ := pieceRep_RR (A := A) (P := P) G
  refine ⟨C, C', hC, hC', fun D hI hwN hwDec vp vb ε ex ey hfl hex t0 s1 t1 β RQ RT b BK BL qK qL CQ CT rq rt hRQ hRT Bx hG => ?_⟩
  have hey := hfl.ey_eq hex
  have h0 := h D hI hwN hwDec vp vb ε (fun _ _ => 1) ![t1, t0] ![s1, t0] rq rt.conj Bx
    (fun τ tt r k => 1 * (rq.f ![slotVal D τ tt t1, slotVal D τ tt t0] k *
      rt.conj.f ![slotVal D τ tt s1, slotVal D τ tt t0] (k + ε • r)))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bq, bt⟩ := hg hd
      exact ⟨by rw [vec2_slot]; exact bq, by rw [vec2_slot]; exact bt, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, bq, bt⟩ := hg hd
  subst hex
  rw [hey]
  simp only [rB3, if_pos hi, (hRQ _ _ bq), (hRT _ _ bt), RemC.conj, zero_smul, add_zero]
  ring

/-- rB3 with `e_y = 0`: `1_{t₀<s₁} RQ(t₁,t₀,k + ε r) conj RT(s₁,t₀,k)` (three-clock product row). -/
theorem pieceAll_rB3_RP (G : AmbP A P) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * P.d) (hwDec : D.wDec = 30 * P.d)
      (vp vb : D.S.VIdx) (ε ex ey : ℝ) (hfl : FlagXY ε ex ey) (hey : ey = 0) (t0 s1 t1 : WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {β : Type*} (RQ RT : β → ℝ → ℝ → Mom P.d → ℂ) (b : β)
      (sL : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
      {BK BL : Set (Fin 2 → ℝ)} {qK qL : Fin 2 → ℝ} {CQ CT : ℝ}
      (rq : RemC P (30 * P.d) BK qK CQ) (rt : RemC P 0 BL qL CT)
      (hRQ : ∀ s t, ![s, t] ∈ rq.Bc → ∀ k, RQ b s t k = rq.f ![s, t] k) (hRT : ∀ s t, ![s, t] ∈ rt.Bc → ∀ k, RT b s t k = rt.f ![s, t] k)
      (Bx : Set (Fin 3 → ℝ)),
      (∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) →
        slotVal D τ tt t0 < slotVal D τ tt s1 ∧ ![slotVal D τ tt t1, slotVal D τ tt t0] ∈ rq.Bc ∧ ![slotVal D τ tt s1, slotVal D τ tt t0] ∈ rt.Bc) →
      PieceRep (P := P) hI vp vb ε (fun _ _ => 1)
        (fun τ tt r k => rB3 (slotVal D τ tt t0) (slotVal D τ tt s1) (slotVal D τ tt t1) (k + ex • r) (k + ey • r) RQ RT b)
        (C * ENNReal.ofReal CQ * ENNReal.ofReal CT) (ENNReal.ofReal 1) Bx := by
  obtain ⟨C, hC, h⟩ := pieceRep_RP (A := A) (P := P) G
  refine ⟨C, hC, fun D hI hwN hwDec vp vb ε ex ey hfl hey t0 s1 t1 β RQ RT b sL BK BL qK qL CQ CT rq rt hRQ hRT Bx hG => ?_⟩
  have hex := hfl.ex_eq hey
  have h0 := h D hI hwN hwDec vp vb ε ex (fun _ _ => 1) ![t1, s1, t0] sL rq rt.conj hfl.abs_ex_le Bx
    (fun τ tt r k => 1 * (rq.f ![slotVal D τ tt t1, slotVal D τ tt t0] (k + ex • r) *
      rt.conj.f ![slotVal D τ tt s1, slotVal D τ tt t0] k))
    (fun tt htt => by
      filter_upwards [hG tt htt] with τ hg hd
      obtain ⟨_, bq, bt⟩ := hg hd
      exact ⟨⟨bq, bt⟩, fun r k hr => rfl⟩)
  refine h0.congr (fun tt htt => ?_)
  filter_upwards [hG tt htt] with τ hg hd r k hr
  obtain ⟨hi, bq, bt⟩ := hg hd
  subst hey
  simp only [rB3, if_pos hi, (hRQ _ _ bq), (hRT _ _ bt), RemC.conj, zero_smul, add_zero]
  ring

end WaveTurbulence.VineEstS5C.P4.W2
