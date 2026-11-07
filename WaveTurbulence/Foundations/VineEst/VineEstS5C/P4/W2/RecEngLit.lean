/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecCert
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.EngineRHS
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TraceBox

/-! # P4-W2 (session 18, step 4d): `engine_literal`, the certificate size in the literal form

`prod_Rb_le`: the product of the row sizes with the exceptional rows replaced by `bnd` is bounded by `Kc^{#recs} ∏ N ∏ Loss` when `bnd k ≤ Kc N N Loss`.
`q ≤ certBeta P D mass Rb` plus the row bound `hrows` gives `‖c^M ζ‖ₑ q ≤ ofReal (Λ ((Nₛ √δ)^{n₂} L^{..} lf))` (`engine_rhs` with the mass `tcSq · mass`; `tcSq η` is the squared trace constant).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5C.P4.W13
open scoped ENNReal

theorem prod_Rb_le {ι κ : Type*} [Fintype ι] [DecidableEq ι] (N Rb : ι → ℝ≥0∞) (S : Finset κ) (e1 e2 : κ → ι)
    (hinj1 : Set.InjOn e1 ↑S) (hinj2 : Set.InjOn e2 ↑S) (hdisj : ∀ k ∈ S, ∀ k' ∈ S, e1 k ≠ e2 k') (bnd Loss : κ → ℝ≥0∞) (Kc : ℝ≥0∞)
    (hn : ∀ ρ, ρ ∉ (S.image e1 ∪ S.image e2) → Rb ρ = N ρ) (h1 : ∀ k ∈ S, Rb (e1 k) = bnd k) (h2 : ∀ k ∈ S, Rb (e2 k) = 1)
    (hb : ∀ k ∈ S, bnd k ≤ Kc * (N (e1 k) * N (e2 k)) * Loss k) :
    ∏ ρ, Rb ρ ≤ Kc ^ S.card * (∏ ρ, N ρ) * ∏ k ∈ S, Loss k := by
  classical
  have hd : Disjoint (S.image e1) (S.image e2) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k', hk', h⟩ := Finset.mem_image.mp hx'
    exact hdisj k hk k' hk' h.symm
  have hexR : ∏ ρ ∈ S.image e1 ∪ S.image e2, Rb ρ = ∏ k ∈ S, bnd k := by
    rw [Finset.prod_union hd, Finset.prod_image hinj1, Finset.prod_image hinj2, Finset.prod_congr rfl h1, Finset.prod_congr rfl h2,
      Finset.prod_const_one, mul_one]
  have hexN : ∏ ρ ∈ S.image e1 ∪ S.image e2, N ρ = ∏ k ∈ S, (N (e1 k) * N (e2 k)) := by
    rw [Finset.prod_union hd, Finset.prod_image hinj1, Finset.prod_image hinj2, Finset.prod_mul_distrib]
  have hsd : ∏ ρ ∈ Finset.univ \ (S.image e1 ∪ S.image e2), Rb ρ = ∏ ρ ∈ Finset.univ \ (S.image e1 ∪ S.image e2), N ρ :=
    Finset.prod_congr rfl fun ρ hρ => hn ρ (Finset.mem_sdiff.mp hρ).2
  have hbound : ∏ k ∈ S, bnd k ≤ Kc ^ S.card * (∏ k ∈ S, (N (e1 k) * N (e2 k))) * ∏ k ∈ S, Loss k := by
    calc ∏ k ∈ S, bnd k ≤ ∏ k ∈ S, (Kc * (N (e1 k) * N (e2 k)) * Loss k) := Finset.prod_le_prod' hb
      _ = Kc ^ S.card * (∏ k ∈ S, (N (e1 k) * N (e2 k))) * ∏ k ∈ S, Loss k := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]
  calc ∏ ρ, Rb ρ = (∏ ρ ∈ Finset.univ \ (S.image e1 ∪ S.image e2), Rb ρ) * ∏ ρ ∈ S.image e1 ∪ S.image e2, Rb ρ :=
        (Finset.prod_sdiff (Finset.subset_univ _)).symm
    _ ≤ (∏ ρ ∈ Finset.univ \ (S.image e1 ∪ S.image e2), N ρ) * (Kc ^ S.card * (∏ k ∈ S, (N (e1 k) * N (e2 k))) * ∏ k ∈ S, Loss k) := by
        rw [hsd, hexR]; exact mul_le_mul' le_rfl hbound
    _ = Kc ^ S.card * ((∏ ρ ∈ Finset.univ \ (S.image e1 ∪ S.image e2), N ρ) * ∏ ρ ∈ S.image e1 ∪ S.image e2, N ρ) * ∏ k ∈ S, Loss k := by
        rw [hexN]; ring
    _ = Kc ^ S.card * (∏ ρ, N ρ) * ∏ k ∈ S, Loss k := by
        rw [Finset.prod_sdiff (Finset.subset_univ _)]

/-- The trace constant squared as a real. -/
noncomputable def tcSq (η : ℝ) : ℝ :=
  (Regref.traceConst (r := 3) (2 * η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2).toReal

theorem tcSq_eq (η : ℝ) :
    Regref.traceConst (r := 3) (2 * η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 = ENNReal.ofReal (tcSq η) := by
  unfold tcSq
  rw [ENNReal.ofReal_toReal]
  exact ENNReal.pow_ne_top (WaveTurbulence.VineEstS3.traceConst_ne_top _)

/-- **The engine bound of a certificate size**: from `q ≤ certBeta P D mass Rb` and the row bound `hrows` to the literal form (`engine_rhs` with the mass `tcSq · mass`). -/
theorem engine_literal {P : WTParams} {D : SumintPar.SumintDatum P.d} (q : ℝ≥0∞) (mass : ℝ) (Rb : Row D → ℝ≥0∞)
    (hq : q ≤ certBeta P D mass Rb) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    {M Sn n2 bb M0s M1s : ℕ} {Λ Km Kr lf : ℝ}
    (hM : D.S.M = M) (hM1 : 1 ≤ M) (hn2 : M + 2 * Sn = n2)
    (hb : (Finset.univ.filter fun i => D.S.nor i = false).card = bb)
    (hnum : M0s + M1s ≤ D.M₀ + D.M₁)
    (hmass0 : 0 ≤ mass) (hmass : tcSq P.η * mass ≤ Km ^ (M + 1)) (hKm : 1 ≤ Km)
    (hpar : maxPar D ^ (P.η ^ 6) ≤ Λ)
    (hrows : ∏ ρ, Rb ρ ≤ ENNReal.ofReal (Kr ^ (2 * M) * (2 * P.C₁ ^ 2 * P.δ) ^ Sn *
      P.L ^ (-(weightExp P.d P.γ P.η) * (D.M₁ : ℝ)) * lf))
    (hKr : 1 ≤ Kr) (hlf : 0 ≤ lf) (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hC : 1 ≤ P.C₁) (hη0 : 0 < P.η) (hη1 : P.η ≤ 1) :
    ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ M * ζ‖ₑ * q ≤
    ENNReal.ofReal (Λ * ((engNs P.η P.C₁ Km Kr * Real.sqrt P.δ) ^ n2 *
      P.L ^ (-(P.η ^ 8 * ((M0s + M1s : ℕ) : ℝ)) - P.η ^ 2 * (bb : ℝ) + P.η ^ 7) * lf)) := by
  have hT0 : 0 ≤ tcSq P.η := ENNReal.toReal_nonneg
  refine le_trans (mul_le_mul' le_rfl hq) ?_
  have key := engine_rhs (D := D) (tcSq P.η * mass) Rb ζ hζ hM hM1 hn2 hb hnum (mul_nonneg hT0 hmass0) hmass hKm hpar hrows hKr hlf hL hδ hC hη0 hη1
  refine le_trans (le_of_eq ?_) key
  unfold certBeta
  rw [tcSq_eq P.η]
  congr 1
  simp only [mul_assoc, ENNReal.ofReal_mul hT0]
  ring

end WaveTurbulence.VineEstS5C.P4.W2
