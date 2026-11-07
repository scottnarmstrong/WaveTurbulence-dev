/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVine.Degenerate

/-! # The `ε`-weighted engine with the Fourier-series constant quantified first (V5)

`DegenVine.clockedBoundEps_of_restr` states `∃ Cfs ≠ ⊤, bound`, after all data.  The proof gives `Cfs = max Ca Cb`
with `Ca, Cb` the constants of `fs_expansion` (depending on `η, d` only).  Here the statement is re-quantified as
`∃ Cfs ≠ ⊤, ∀ data, bound`, which the constant bookkeeping of Step 3 needs; the proof is the one of
`clockedBoundMix_of_restr` (DEGEN-VINE, sha in COPIED-SHA256SUMS) / `clockedBoundEps_of_restr` with the witness
moved to the front.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS2
  WaveTurbulence.DegenVine Finset MeasureTheory
open scoped ENNReal

/-- **`clockedBoundMix_of_restr` with a uniform constant.** -/
theorem clockedBoundMix_unif {A : ℝ} {P : WTParams} (hdb : SumintMixDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d) :
    ∃ Cfs : ℝ≥0∞, Cfs ≠ ⊤ ∧ ∀ {D : SumintDatum P.d} (hI : 0 < D.S.I) (cfs cs : Fin D.S.I → ℤˣ)
      (Mx : CharMix D.S P.d)
      (hno : ∀ i, D.badKind i ≠ 1) (hbad : ∀ i, D.badKind i ≠ 2)
      (hAdm : ∀ (p : D.S.TVar → ℝ) (a b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
        ({ D with param := p, wK := a, wL := b } : SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
      (hM : D.S.M ≤ P.N 1 ^ 4) (cr : ClockedRows D)
      (Bx : Row D → Set (Fin 2 → ℝ)) (qx : Row D → Fin 2 → ℝ) (β : Row D → ℝ≥0∞)
      (hbox : ∀ ρ, Bx ρ ⊆ cell (qx ρ)) (hint : ∀ ρ, Bx ρ ⊆ closure (interior (Bx ρ)))
      (hcont : ∀ ρ k, Continuous fun t => cr.W ρ t k)
      (hres : ∀ ρ, XNormRestr (6 * P.η ^ 6) (30 * P.d) (rowOrder D ρ) (Bx ρ) Set.univ (cr.W ρ) < β ρ)
      (hβ : ∀ ρ, β ρ ≠ ⊤)
      (hclock : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), ∀ ρ, cr.clock τ tt ρ ∈ Bx ρ),
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
          (fun tt E => clockedExprMul Mx cr cfs cs hI P.L P.γ (2 * P.δ) P.η tt E) ≤
        (ccη P.η + 1) * ENNReal.ofReal (Mx.mass * (engineConst P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
            sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
          ∏ ρ, (Cfs * β ρ) := by
  classical
  have hθfs : (0 : ℝ) ≤ 6 * P.η ^ 6 := by positivity
  have hΛ : 30 * P.d ≠ 0 := by omega
  obtain ⟨Ca, hCa, hfa⟩ := fs_expansion (r := 2) (d := P.d) hθfs (Λ₂ := 30 * P.d) hΛ
  obtain ⟨Cb, hCb, hfb⟩ := fs_expansion (r := 2) (d := P.d) hθfs (Λ₂ := 0) hΛ
  set Cm := max Ca Cb with hCm
  have hCmtop : Cm ≠ ⊤ := by
    rw [hCm]; exact ne_of_lt (max_lt hCa.lt_top hCb.lt_top)
  refine ⟨Cm, hCmtop, ?_⟩
  intro D hI cfs cs Mx hno hbad hAdm hM cr Bx qx β hbox hint hcont hres hβ hclock
  have hrow : ∀ ρ : Row D, ∃ c : (Fin 2 → ℤ) → Mom P.d → ℂ,
      (∀ t ∈ Bx ρ, ∀ k, HasSum (fun m : Fin 2 → ℤ => c m k * fsPhase m t) (cr.W ρ t k)) ∧
      ∑' m : Fin 2 → ℤ, maxBracketPow (6 * P.η ^ 6) (half m) * SNorm (30 * P.d) (rowOrder D ρ) (c m) ≤
        Cm * β ρ := by
    intro ρ
    cases ρ with
    | inl v =>
      obtain ⟨c, h1, h2⟩ := hfa (qx (Sum.inl v)) (Bx (Sum.inl v)) Set.univ (cr.W (Sum.inl v)) (β (Sum.inl v))
        (hbox _) (hint _) (fun k _ => hcont _ k) (hres _)
      exact ⟨c, fun t ht k => h1 t ht k (Set.mem_univ k),
        h2.trans (mul_le_mul_left (le_max_left _ _) _)⟩
    | inr v =>
      obtain ⟨c, h1, h2⟩ := hfb (qx (Sum.inr v)) (Bx (Sum.inr v)) Set.univ (cr.W (Sum.inr v)) (β (Sum.inr v))
        (hbox _) (hint _) (fun k _ => hcont _ k) (hres _)
      exact ⟨c, fun t ht k => h1 t ht k (Set.mem_univ k),
        h2.trans (mul_le_mul_left (le_max_right _ _) _)⟩
  choose c hc hcb using hrow
  let M : ClockedModes D (6 * P.η ^ 6) :=
    { c := c, b := fun ρ => Cm * β ρ,
      b_ne_top := fun ρ => ENNReal.mul_ne_top hCmtop (hβ ρ),
      fs_bound := hcb }
  exact clockedBoundMix hdb hL hη0 hη1 hC1 hδ hd1 hI cfs cs Mx hno hbad hAdm hM cr M
    (fun tt htt τ hτ ρ k => hc ρ _ (hclock tt htt τ hτ ρ) k)

/-- **`clockedBoundEps_of_restr` with a uniform constant.** -/
theorem clockedBoundEps_unif {A : ℝ} {P : WTParams} (hdb : SumintMixDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d) :
    ∃ Cfs : ℝ≥0∞, Cfs ≠ ⊤ ∧ ∀ {ι : Type} [Fintype ι] {D : SumintDatum P.d} (hI : 0 < D.S.I)
      (cfs cs : Fin D.S.I → ℤˣ) (l₁ l₂ l₃ : ι → Row D ⊕ Fin 4)
      (hno : ∀ i, D.badKind i ≠ 1) (hbad : ∀ i, D.badKind i ≠ 2)
      (hAdm : ∀ (p : D.S.TVar → ℝ) (a b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
        ({ D with param := p, wK := a, wL := b } : SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
      (hM : D.S.M ≤ P.N 1 ^ 4) (cr : ClockedRows D)
      (Bx : Row D → Set (Fin 2 → ℝ)) (qx : Row D → Fin 2 → ℝ) (β : Row D → ℝ≥0∞)
      (hbox : ∀ ρ, Bx ρ ⊆ cell (qx ρ)) (hint : ∀ ρ, Bx ρ ⊆ closure (interior (Bx ρ)))
      (hcont : ∀ ρ k, Continuous fun t => cr.W ρ t k)
      (hres : ∀ ρ, XNormRestr (6 * P.η ^ 6) (30 * P.d) (rowOrder D ρ) (Bx ρ) Set.univ (cr.W ρ) < β ρ)
      (hβ : ∀ ρ, β ρ ≠ ⊤)
      (hclock : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), ∀ ρ, cr.clock τ tt ρ ∈ Bx ρ),
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
          (fun tt E => clockedExprEps l₁ l₂ l₃ cr cfs cs hI P.L P.γ (2 * P.δ) P.η tt E) ≤
        (ccη P.η + 1) * ENNReal.ofReal ((3 : ℝ) ^ Fintype.card ι *
            (engineConst P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
              ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
          ∏ ρ, (Cfs * β ρ) := by
  classical
  obtain ⟨Cfs, hC, hb⟩ := clockedBoundMix_unif hdb hL hη0 hη1 hC1 hδ hd1
  refine ⟨Cfs, hC, ?_⟩
  intro ι _ D hI cfs cs l₁ l₂ l₃ hno hbad hAdm hM cr Bx qx β hbox hint hcont hres hβ hclock
  obtain ⟨N, hmass, hval⟩ := exists_eps_mix (ι := ι) (S := D.S) (L := P.L) hL.ne'
    (fun i => labelRef D (l₁ i)) (fun i => labelRef D (l₂ i)) (fun i => labelRef D (l₃ i)) D.wBar
  have hb' := hb hI cfs cs N hno hbad hAdm hM cr Bx qx β hbox hint hcont hres hβ hclock
  refine (XNorm00Restr_mono_of_eq _ _ _ _ _ ?_).trans (hb'.trans_eq ?_)
  · intro tt htt E hE
    unfold clockedExprEps clockedExprMul
    refine tsum_congr fun x => ?_
    congr 1
    rw [hval E (fun k => (hE.1 k).1) x]
    simp only [epsOf, labelRef_val]
  · rw [hmass]

/-- The Fourier-series constant, an explicit function of `(d, η)` only. -/
noncomputable def CfsOf (d : ℕ) (η : ℝ) : ℝ≥0∞ := by
  classical
  exact if h : 1 ≤ d then
    max (Classical.choose (fs_expansion (r := 2) (d := d) (θ := 6 * η ^ 6) (by positivity) (Λ₂ := 30 * d)
      (by omega : 30 * d ≠ 0)))
      (Classical.choose (fs_expansion (r := 2) (d := d) (θ := 6 * η ^ 6) (by positivity) (Λ₂ := 0)
      (by omega : 30 * d ≠ 0)))
  else 0

theorem CfsOf_ne_top (d : ℕ) (η : ℝ) : CfsOf d η ≠ ⊤ := by
  unfold CfsOf
  split_ifs with h
  · exact ne_of_lt (max_lt (Classical.choose_spec (fs_expansion (r := 2) (d := d) (θ := 6 * η ^ 6) (by positivity)
      (Λ₂ := 30 * d) (by omega : 30 * d ≠ 0))).1.lt_top
      (Classical.choose_spec (fs_expansion (r := 2) (d := d) (θ := 6 * η ^ 6) (by positivity) (Λ₂ := 0)
      (by omega : 30 * d ≠ 0))).1.lt_top)
  · exact ENNReal.zero_ne_top

/-- **`clockedBoundMix_of_restr` with a uniform constant.** -/
theorem clockedBoundMix_cfs {A : ℝ} {P : WTParams} (hdb : SumintMixDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d) :
    ∀ {D : SumintDatum P.d} (hI : 0 < D.S.I) (cfs cs : Fin D.S.I → ℤˣ)
      (Mx : CharMix D.S P.d)
      (hno : ∀ i, D.badKind i ≠ 1) (hbad : ∀ i, D.badKind i ≠ 2)
      (hAdm : ∀ (p : D.S.TVar → ℝ) (a b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
        ({ D with param := p, wK := a, wL := b } : SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
      (hM : D.S.M ≤ P.N 1 ^ 4) (cr : ClockedRows D)
      (Bx : Row D → Set (Fin 2 → ℝ)) (qx : Row D → Fin 2 → ℝ) (β : Row D → ℝ≥0∞)
      (hbox : ∀ ρ, Bx ρ ⊆ cell (qx ρ)) (hint : ∀ ρ, Bx ρ ⊆ closure (interior (Bx ρ)))
      (hcont : ∀ ρ k, Continuous fun t => cr.W ρ t k)
      (hres : ∀ ρ, XNormRestr (6 * P.η ^ 6) (30 * P.d) (rowOrder D ρ) (Bx ρ) Set.univ (cr.W ρ) < β ρ)
      (hβ : ∀ ρ, β ρ ≠ ⊤)
      (hclock : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), ∀ ρ, cr.clock τ tt ρ ∈ Bx ρ),
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
          (fun tt E => clockedExprMul Mx cr cfs cs hI P.L P.γ (2 * P.δ) P.η tt E) ≤
        (ccη P.η + 1) * ENNReal.ofReal (Mx.mass * (engineConst P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
            sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
          ∏ ρ, (CfsOf P.d P.η * β ρ) := by
  classical
  have hθfs : (0 : ℝ) ≤ 6 * P.η ^ 6 := by positivity
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hCm : CfsOf P.d P.η = max (Classical.choose (fs_expansion (r := 2) (d := P.d) hθfs (Λ₂ := 30 * P.d) hΛ))
      (Classical.choose (fs_expansion (r := 2) (d := P.d) hθfs (Λ₂ := 0) hΛ)) := by
    unfold CfsOf; rw [dif_pos hd1]
  obtain ⟨hCa, hfa⟩ := Classical.choose_spec (fs_expansion (r := 2) (d := P.d) hθfs (Λ₂ := 30 * P.d) hΛ)
  obtain ⟨hCb, hfb⟩ := Classical.choose_spec (fs_expansion (r := 2) (d := P.d) hθfs (Λ₂ := 0) hΛ)
  set Ca := Classical.choose (fs_expansion (r := 2) (d := P.d) hθfs (Λ₂ := 30 * P.d) hΛ)
  set Cb := Classical.choose (fs_expansion (r := 2) (d := P.d) hθfs (Λ₂ := 0) hΛ)
  set Cm := CfsOf P.d P.η with hCmd
  have hCmtop : Cm ≠ ⊤ := CfsOf_ne_top _ _
  have hCaCm : Ca ≤ Cm := by rw [hCm]; exact le_max_left _ _
  have hCbCm : Cb ≤ Cm := by rw [hCm]; exact le_max_right _ _
  intro D hI cfs cs Mx hno hbad hAdm hM cr Bx qx β hbox hint hcont hres hβ hclock
  have hrow : ∀ ρ : Row D, ∃ c : (Fin 2 → ℤ) → Mom P.d → ℂ,
      (∀ t ∈ Bx ρ, ∀ k, HasSum (fun m : Fin 2 → ℤ => c m k * fsPhase m t) (cr.W ρ t k)) ∧
      ∑' m : Fin 2 → ℤ, maxBracketPow (6 * P.η ^ 6) (half m) * SNorm (30 * P.d) (rowOrder D ρ) (c m) ≤
        Cm * β ρ := by
    intro ρ
    cases ρ with
    | inl v =>
      obtain ⟨c, h1, h2⟩ := hfa (qx (Sum.inl v)) (Bx (Sum.inl v)) Set.univ (cr.W (Sum.inl v)) (β (Sum.inl v))
        (hbox _) (hint _) (fun k _ => hcont _ k) (hres _)
      exact ⟨c, fun t ht k => h1 t ht k (Set.mem_univ k),
        h2.trans (mul_le_mul_left hCaCm _)⟩
    | inr v =>
      obtain ⟨c, h1, h2⟩ := hfb (qx (Sum.inr v)) (Bx (Sum.inr v)) Set.univ (cr.W (Sum.inr v)) (β (Sum.inr v))
        (hbox _) (hint _) (fun k _ => hcont _ k) (hres _)
      exact ⟨c, fun t ht k => h1 t ht k (Set.mem_univ k),
        h2.trans (mul_le_mul_left hCbCm _)⟩
  choose c hc hcb using hrow
  let M : ClockedModes D (6 * P.η ^ 6) :=
    { c := c, b := fun ρ => Cm * β ρ,
      b_ne_top := fun ρ => ENNReal.mul_ne_top hCmtop (hβ ρ),
      fs_bound := hcb }
  exact clockedBoundMix hdb hL hη0 hη1 hC1 hδ hd1 hI cfs cs Mx hno hbad hAdm hM cr M
    (fun tt htt τ hτ ρ k => hc ρ _ (hclock tt htt τ hτ ρ) k)

/-- **`clockedBoundEps_of_restr` with the explicit constant `CfsOf`.** -/
theorem clockedBoundEps_cfs {A : ℝ} {P : WTParams} (hdb : SumintMixDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    {ι : Type} [Fintype ι] {D : SumintDatum P.d} (hI : 0 < D.S.I)
    (cfs cs : Fin D.S.I → ℤˣ) (l₁ l₂ l₃ : ι → Row D ⊕ Fin 4)
    (hno : ∀ i, D.badKind i ≠ 1) (hbad : ∀ i, D.badKind i ≠ 2)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (cr : ClockedRows D)
    (Bx : Row D → Set (Fin 2 → ℝ)) (qx : Row D → Fin 2 → ℝ) (β : Row D → ℝ≥0∞)
    (hbox : ∀ ρ, Bx ρ ⊆ cell (qx ρ)) (hint : ∀ ρ, Bx ρ ⊆ closure (interior (Bx ρ)))
    (hcont : ∀ ρ k, Continuous fun t => cr.W ρ t k)
    (hres : ∀ ρ, XNormRestr (6 * P.η ^ 6) (30 * P.d) (rowOrder D ρ) (Bx ρ) Set.univ (cr.W ρ) < β ρ)
    (hβ : ∀ ρ, β ρ ≠ ⊤)
    (hclock : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), ∀ ρ, cr.clock τ tt ρ ∈ Bx ρ) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
          (fun tt E => clockedExprEps l₁ l₂ l₃ cr cfs cs hI P.L P.γ (2 * P.δ) P.η tt E) ≤
        (ccη P.η + 1) * ENNReal.ofReal ((3 : ℝ) ^ Fintype.card ι *
            (engineConst P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
              ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
          ∏ ρ, (CfsOf P.d P.η * β ρ) := by
  classical
  obtain ⟨N, hmass, hval⟩ := exists_eps_mix (ι := ι) (S := D.S) (L := P.L) hL.ne'
    (fun i => labelRef D (l₁ i)) (fun i => labelRef D (l₂ i)) (fun i => labelRef D (l₃ i)) D.wBar
  have hb' := clockedBoundMix_cfs hdb hL hη0 hη1 hC1 hδ hd1 hI cfs cs N hno hbad hAdm hM cr Bx qx β hbox hint hcont
    hres hβ hclock
  refine (XNorm00Restr_mono_of_eq _ _ _ _ _ ?_).trans (hb'.trans_eq ?_)
  · intro tt htt E hE
    unfold clockedExprEps clockedExprMul
    refine tsum_congr fun x => ?_
    congr 1
    rw [hval E (fun k => (hE.1 k).1) x]
    simp only [epsOf, labelRef_val]
  · rw [hmass]

end WaveTurbulence.VineEstS3.Eng
