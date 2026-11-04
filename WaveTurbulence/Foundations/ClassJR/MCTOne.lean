/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCTTerm
public import WaveTurbulence.Foundations.ClassJR.MCChainOne
public import WaveTurbulence.Foundations.ClassJR.MCOne

/-!
# A rebased tree chain, for fixed masks (DH21 Proposition 6.10)

The rebased chain of a regular tree (`chainT_rebase`) has pair coefficients
`∫ 𝒞_j(λ) e^{πi(λ₁(u+s) + λ₂(v+s))}` at the shifted times and bottom `1`. As for the chains of
Proposition 5.1 (`MCRep.chainOne`), Lemma 5.10 and Lemma G expand it over `Y' ⊆ Y ⊆ adj` with the
factors `∏_{j∈Y'} Φ(ζ_{σ j}α_{σ j})`, and every term is a coefficient representation in `(τ, s)`
(`MCRep.treeOne`): the twists of the pairs go into the bottom frequency (`treeTerm`).

The pairs are taken with the exponents `(θ', a', b)` of a couple coefficient and the difference
exponent `δ`; the terms have the exponents `(θ, a, b)` when `δ + θ ≤ θ'`, `δ + a ≤ a'` and
`a' + b ≤ θ'`. The pairs pay the weight `⟨Λ(z)⟩^θ` of the Gevrey bounds (family `wsym θ`, no
variable weight) and `⟨Λ(z)⟩^a` of the weighted bounds (family `wsym a`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Weighted0

variable {ι : Type} [Fintype ι] {b A N : ℝ}

/-- **A weighted symbol without variable weights**: the per-variable bounds come from the Gevrey bound
`k = 0`. -/
theorem SRep.weighted0 {θ' a' wp θ'' a'' : ℝ} {C : (ι → ℝ) → ℝ × ℝ → ℂ}
    (h : SRep θ' a' b A N C) (hwp : 0 ≤ wp) (hθ : 0 ≤ θ'') (hθwp : θ'' + wp ≤ θ')
    (hawp : a'' + wp ≤ θ') : SRep θ'' a'' 0 A N (wsym wp C) := by
  have hs : ∀ γ, ContDiff ℝ ∞ fun β => wsym wp C β γ := fun γ =>
    contDiff_const.mul (h.reg.smooth γ)
  have hm : StronglyMeasurable (Function.uncurry (wsym wp C)) := by
    unfold wsym
    exact ((Complex.measurable_ofReal.comp ((measurable_wFr wp).comp measurable_snd)).mul
      h.reg.meas.measurable).stronglyMeasurable
  have hw : ∀ k, ∫⁻ β, ∫⁻ lam, wL θ'' lam * dnorm k (wsym wp C) β lam ≤ gev N A k := fun k => by
    refine le_trans (lintegral_mono fun β => lintegral_mono fun lam => ?_) (h.norm k)
    rw [dnorm_wsym hwp h.reg.smooth, ← mul_assoc, wL_mul_wL]
    exact mul_le_mul' (wL_le_of_le hθwp lam) le_rfl
  refine ⟨h.nonneg, SymReg.of_lintegral hs hm fun k => ?_, hw, fun i => ?_⟩
  · refine ne_top_of_le_ne_top (gev_ne_top N A k) (le_trans ?_ (hw k))
    exact lintegral_mono fun β => lintegral_mono fun lam =>
      le_mul_of_one_le_left zero_le (one_le_wL hθ lam)
  · refine le_trans (lintegral_mono fun β => lintegral_mono fun lam => ?_)
      ((h.norm 0).trans_eq (gev_zero_eq N A))
    rw [ENNReal.rpow_zero, mul_one, ← dnorm_zero, dnorm_wsym hwp h.reg.smooth, ← mul_assoc,
      wL_mul_wL]
    exact mul_le_mul' (wL_le_of_le hawp lam) le_rfl

end Weighted0

section WChainP

variable {V : Type}

/-- The weighted pair symbols. -/
@[expose] noncomputable def wP (P : ℕ → PSym V) (wp : ℝ) : ℕ → PSym V :=
  fun j => ⟨(P j).ι, (P j).f, wsym wp (P j).C⟩

/-- Weighting commutes with attaching the differences. -/
theorem wsym_chainP (P : ℕ → PSym V) (σ : ℕ → V) (ε : ℕ → ℤ) (D : Finset ℕ) (wp : ℝ) (j : ℕ) :
    (⟨(chainP P σ ε D j).ι, (chainP P σ ε D j).f, wsym wp (chainP P σ ε D j).C⟩ : PSym V) =
      chainP (wP P wp) σ ε D j := by
  by_cases hj : j ∈ D
  · rw [chainP_of_mem (P := P) hj, chainP_of_mem (P := wP P wp) hj]
    simp only [PSym.pd, wP]
    rw [pdC_wsym]
    rfl
  · rw [chainP_of_notMem (P := P) hj, chainP_of_notMem (P := wP P wp) hj]
    rfl

end WChainP

section Piece

variable {V : Type} [DecidableEq V] {σ : ℕ → V} {ε : ℕ → ℤ} {P : ℕ → PSym V}
  {S : ℕ → Set V} {c : LegalCode}

/-- The constant of the pair symbols of a tree chain (three families). -/
@[expose] noncomputable def KPT (a' b δ : ℝ) : ℝ := KPD a' b + KPD δ 0 + KPD δ b

theorem KPT_nonneg (a' b δ : ℝ) : 0 ≤ KPT a' b δ := by
  have := KPD_nonneg a' b; have := KPD_nonneg δ 0; have := KPD_nonneg δ b
  unfold KPT; positivity

/-- **The constant of a term of a rebased tree chain** with bottom coefficient. -/
@[expose] noncomputable def Ntree (θ a b a' δ : ℝ) (c : LegalCode) (N : ℕ → ℝ) (Nb : ℝ) : ℝ :=
  4 * (4 * NT (fun j => (1 + KPT a' b δ) * N j) c 0 * Nb) * (KH θ a b * C510 θ ^ c.size)

/-- **A term of a rebased tree chain, from a Lemma G piece** (DH21 Proposition 6.10). -/
theorem treeOne_piece {θ a b A θ' a' δ : ℝ} (hθ0 : 0 ≤ θ) (ha : 0 < a) (hb : 0 ≤ b)
    (hab : a + b ≤ θ) (hA : A1 ≤ A) (ha' : 0 < a') (hab' : a' + b ≤ θ') (hθ'1 : θ' ≤ 1)
    (hδ : 0 < δ) (hδθ : δ + θ ≤ θ') (hδa : δ + a ≤ a') (hδb : δ + b ≤ 1)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) (hinj : Set.InjOn σ (Set.Ico 0 c.size)) {N : ℕ → ℝ}
    (hP : ∀ j ∈ Set.Ico 0 c.size, Function.Injective (P j).f ∧ Set.range (P j).f = S j ∧
      SRep θ' a' b A (N j) (P j).C)
    (hSS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, j ≠ k → Disjoint (S j) (S k))
    {Sb : Set V} (hSb : ∀ j ∈ Set.Ico 0 c.size, Disjoint (S j) Sb)
    (hσS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, σ k ∉ S j)
    (hσb : ∀ k ∈ Set.Ico 0 c.size, σ k ∉ Sb)
    {ιb : Type} [Fintype ιb] {fb : ιb → V} {Cb : (ιb → ℝ) → ℝ × ℝ → ℂ} {Nb : ℝ}
    (hfb : Function.Injective fb) (hrb : Set.range fb = Sb) (hCb : SRep θ a b A Nb Cb)
    {Y Y' : Finset ℕ} (hY : Y ⊆ adjSet c 0) (hY' : Y' ⊆ Y)
    {Gp : ZT c → ℝ → (V → ℝ) → ℝ → ℂ} {NH : ℝ} (hNH : NH ≤ KH θ a b * C510 θ ^ c.size)
    (hL : LGPiece θ a b A NH (σ '' (Set.Ico 0 (0 + c.size) \ (↑Y ∩ ↑(adjSet c 0)))) Gp) :
    MCRep θ a b A (Ntree θ a b a' δ c N Nb)
        ((⋃ j ∈ Set.Ico 0 c.size, S j) ∪ Sb ∪ σ '' (Set.Ico 0 c.size \ ↑Y'))
        (fun α t s => ∫ w, gTerm σ ε (twistP P s) fb Cb c Gp Y Y' α t s w) ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → Integrable (gTerm σ ε (twistP P s) fb Cb c Gp Y Y' α t s) := by
  classical
  have hA0 : 0 ≤ A := A1_nonneg.trans hA
  have haθ : a ≤ θ := by linarith
  have hAchi : Achi ≤ A := Achi_le_A1.trans hA
  have hYI : Y ⊆ Finset.Ico 0 (0 + c.size) := fun j hj => by
    have := mem_adjSet c 0 j (hY hj)
    simp only [Finset.mem_Ico]; omega
  have hD : Y \ Y' ⊆ Finset.Ico 0 (0 + c.size) := Finset.sdiff_subset.trans hYI
  have hKP := KPT_nonneg a' b δ
  have hr : ∀ j, j ∈ Set.Ico 0 (0 + c.size) → j ∈ Set.Ico 0 c.size := fun j hj => by
    simpa using hj
  have hmono : ∀ j ∈ Set.Ico 0 c.size, ∀ {K : ℝ}, 0 ≤ K → K ≤ KPT a' b δ →
      (1 + K) * N j ≤ (1 + KPT a' b δ) * N j := fun j hj K _ hK =>
    mul_le_mul_of_nonneg_right (by linarith) (hP j hj).2.2.nonneg
  have hK1 := KPD_nonneg a' b
  have hK2 := KPD_nonneg δ 0
  have hK3 := KPD_nonneg δ b
  -- the three families of pair bounds
  have hT := tbound_MzS (chainP P σ ε (Y \ Y')) hA0 (NP := fun j => (1 + KPT a' b δ) * N j) c 0
    fun j hj => (PBound.chainP (hP j (hr j hj)).2.2 ha' hb hab' hθ'1 hAchi (hε j)).mono
      (hmono j (hr j hj) hK1 (by unfold KPT; linarith)) hA0
  have hTθ := tbound_MzSW (chainP P σ ε (Y \ Y')) hA0 (b := 0) (wp := θ)
    (NP := fun j => (1 + KPT a' b δ) * N j) c 0 fun j hj => by
      rw [wsym_chainP]
      exact (PBound.chainP (P := wP P θ)
        ((hP j (hr j hj)).2.2.weighted0 hθ0 hδ.le (by linarith) (by linarith)) hδ le_rfl
        (by linarith) (by linarith) hAchi (hε j)).mono
        (hmono j (hr j hj) hK2 (by unfold KPT; linarith)) hA0
  have hTa := tbound_MzSW (chainP P σ ε (Y \ Y')) hA0 (b := b) (wp := a)
    (NP := fun j => (1 + KPT a' b δ) * N j) c 0 fun j hj => by
      rw [wsym_chainP]
      exact (PBound.chainP (P := wP P a)
        ((hP j (hr j hj)).2.2.weighted ha.le (by linarith) (by linarith) (by linarith)) hδ hb
        le_rfl hδb hAchi (hε j)).mono (hmono j (hr j hj) hK3 (by unfold KPT; linarith)) hA0
  obtain ⟨ιH, hιH, fH, Ξ, hΞ, hΞs, bfr, H, hfH, hrH, hbfr, hHF, hHm, hGp⟩ := hL
  have hvar : σ '' (Set.Ico 0 (0 + c.size) \ (↑Y ∩ ↑(adjSet c 0))) =
      σ '' (Set.Ico 0 c.size \ ↑Y) := by
    rw [zero_add, Set.inter_eq_left.2 (Finset.coe_subset.2 hY)]
  rw [hvar] at hrH
  have hjH : ∀ i, ∃ j, j ∈ Set.Ico 0 c.size ∧ fH i = σ j := fun i => by
    have : fH i ∈ Set.range fH := ⟨i, rfl⟩
    rw [hrH] at this
    obtain ⟨j, hj, hji⟩ := this
    exact ⟨j, hj.1, hji.symm⟩
  choose jH hjH using hjH
  have hK := KH_nonneg θ a b
  have hC5 : 0 ≤ C510 θ ^ c.size := by
    unfold C510; positivity
  obtain ⟨hS, hid⟩ := treeTerm hθ0 ha.le haθ hb hA0 hε hinj hD hT hTθ hTa hCb hbfr
    (NH := KH θ a b * C510 θ ^ c.size) (mul_nonneg hK hC5)
    (fun p L0 => (hHF p L0).mono hNH hA0) hHm hjH hGp
  obtain ⟨hfi, hfr⟩ := fTerm_spec (ε := ε) (fun j hj => (hP j hj).1) (fun j hj => (hP j hj).2.1)
    hSS hSb hσS hσb hinj hY' hYI hfb hrb hfH hrH
  refine ⟨⟨_, inferInstance, fTerm (σ := σ) (ε := ε) P c (Y \ Y') fb fH, _, hfi, hfr, hS.nonneg,
    hS.reg, hS.norm, hS.wnorm, fun α t s ht _ => (hid s α t ht).2⟩,
    fun α t s ht => (hid s α t ht).1⟩

end Piece

section Main

variable {V : Type} [DecidableEq V]

/-- **A rebased tree chain, for fixed masks** (DH21 Proposition 6.10, with Proposition 5.1, Case 2,
L1121–L1150). For pair symbols `𝒞_j` with the exponents `(θ', a', b)`, the chain integral with the pair
coefficients at the shifted times `(u + s, v + s)` and bottom `1` is a sum over `Y' ⊆ Y ⊆ adj` of the
factors `∏_{j∈Y'} Φ(ζ_{σ j}α_{σ j})` times coefficient representations in `(τ, s)` in the remaining
variables, with the exponents `(θ, a, b)`. -/
theorem MCRep.treeOne {θ a b A θ' a' δ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b)
    (hab1 : a + b < 1) (hab : a + b ≤ θ) (hA : A1 ≤ A) (ha' : 0 < a') (hab' : a' + b ≤ θ')
    (hθ'1 : θ' ≤ 1) (hδ : 0 < δ) (hδθ : δ + θ ≤ θ') (hδa : δ + a ≤ a') (hδb : δ + b ≤ 1)
    {σ : ℕ → V} {ε : ℕ → ℤ} (hε : ∀ j, ε j = 1 ∨ ε j = -1) {ζ : V → ℤ} {c : LegalCode}
    (hζ : ∀ j ∈ Set.Ico 0 c.size, ζ (σ j) = ε j) (hc : c ≠ .nil)
    (hinj : Set.InjOn σ (Set.Ico 0 c.size))
    {S : ℕ → Set V} {N : ℕ → ℝ} {P : ℕ → PSym V} (hPreg : ∀ j, SymReg (P j).C)
    (hP : ∀ j ∈ Set.Ico 0 c.size, Function.Injective (P j).f ∧ Set.range (P j).f = S j ∧
      SRep θ' a' b A (N j) (P j).C)
    (hSS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, j ≠ k → Disjoint (S j) (S k))
    (hσS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, σ k ∉ S j) :
    ∃ T : Finset ℕ → Finset ℕ → Bool → (V → ℝ) → ℝ → ℝ → ℂ,
      (∀ Y ⊆ adjSet c 0, ∀ Y' ⊆ Y, ∀ pc, MCRep θ a b A (Ntree θ a b a' δ c N (N1 θ))
        ((⋃ j ∈ Set.Ico 0 c.size, S j) ∪ ∅ ∪ σ '' (Set.Ico 0 c.size \ ↑Y')) (T Y Y' pc)) ∧
      ∀ α τ s, τ ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
        chainT σ ε c 0 (fun j β u v => ∫ lam, (P j).C (β ∘ (P j).f) lam * e2 lam (u + s) (v + s)) α τ
            (fun _ => 1) =
          ∑ Y ∈ (adjSet c 0).powerset, ∑ Y' ∈ Y.powerset,
            (∏ j ∈ Y', PhiZ ζ (σ j) (α (σ j))) * (T Y Y' true α τ s + T Y Y' false α τ s) := by
  classical
  have hinj0 : Set.InjOn σ (Set.Ico 0 (0 + c.size)) := by rwa [zero_add]
  -- the bottom symbol
  obtain ⟨ιb, hιb, fb, Cb, hfb, hrb, hCb, heb⟩ :=
    (MCRep.one (V := V) (a := a) (b := b) (A := A) hθ0 hθ1.le).exists_srep
  -- Lemma 5.10 and Lemma G
  have hJR : ∀ Y : Finset ℕ, ∃ (GJ GR : ZT c → ℝ → (V → ℝ) → ℝ → ℂ) (NJ NR : ℝ),
      0 ≤ NJ ∧ 0 ≤ NR ∧ NJ + NR ≤ C510 θ ^ c.size ∧
      LGPiece θ a b A (12 * CE * Ir 2 * NJ)
        (σ '' (Set.Ico 0 (0 + c.size) \ (↑Y ∩ ↑(adjSet c 0)))) GJ ∧
      (LGPiece θ a b A (KRs θ a b * NR)
          (σ '' (Set.Ico 0 (0 + c.size) \ (↑Y ∩ ↑(adjSet c 0)))) GR ∨
        ∀ (p : ZT c) (L0 : ℝ) (α : V → ℝ), ∀ t ∈ Icc (0 : ℝ) 1, GR p L0 α t = 0) ∧
      ∀ (p : ZT c) (L0 : ℝ) (α : V → ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
        volterra (tildeP σ ε (μZ c) Y c 0 p α) (fun s => cexp (π * I * (L0 * s))) t =
          GJ p L0 α t + GR p L0 α t := by
    intro Y
    have hM := (lemma510 hθ0 hθ1 (A0_le_A1.trans hA) hε (measurable_μZ c) hc hinj0).2.2 Y
    exact hM.lgpieces hθ0 hθ1 ha.le hb hab1 hab hA
  choose GJ GR NJ NR hNJ hNR hNJR hLJ hLR hGJR using hJR
  have hK := KH_nonneg θ a b
  have hJb : ∀ Y, 12 * CE * Ir 2 * NJ Y ≤ KH θ a b * C510 θ ^ c.size := fun Y =>
    mul_le_mul (le_max_left _ _) (by linarith [hNR Y, hNJR Y]) (hNJ Y) hK
  have hRb : ∀ Y, KRs θ a b * NR Y ≤ KH θ a b * C510 θ ^ c.size := fun Y =>
    mul_le_mul (le_max_right _ _) (by linarith [hNJ Y, hNJR Y]) (hNR Y) hK
  have hSb : ∀ j ∈ Set.Ico 0 c.size, Disjoint (S j) (∅ : Set V) := fun _ _ => Set.disjoint_empty _
  have hσb : ∀ k ∈ Set.Ico 0 c.size, σ k ∉ (∅ : Set V) := fun _ _ => Set.notMem_empty _
  -- the pieces
  have hpJ := fun Y (hY : Y ⊆ adjSet c 0) Y' (hY' : Y' ⊆ Y) =>
    treeOne_piece (ε := ε) (N := N) hθ0 ha hb hab hA ha' hab' hθ'1 hδ hδθ hδa hδb hε hinj hP
      hSS hSb hσS hσb hfb hrb hCb hY hY' (hJb Y) (hLJ Y)
  have hpR : ∀ Y, Y ⊆ adjSet c 0 → ∀ Y', Y' ⊆ Y →
      MCRep θ a b A (Ntree θ a b a' δ c N (N1 θ))
        ((⋃ j ∈ Set.Ico 0 c.size, S j) ∪ ∅ ∪ σ '' (Set.Ico 0 c.size \ ↑Y'))
        (fun α t s => ∫ w, gTerm σ ε (twistP P s) fb Cb c (GR Y) Y Y' α t s w) ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → Integrable (gTerm σ ε (twistP P s) fb Cb c (GR Y) Y Y' α t s) := by
    intro Y hY Y' hY'
    rcases hLR Y with hL | hz
    · exact treeOne_piece (ε := ε) (N := N) hθ0 ha hb hab hA ha' hab' hθ'1 hδ hδθ hδa hδb hε
        hinj hP hSS hSb hσS hσb hfb hrb hCb hY hY' (hRb Y) hL
    · obtain ⟨ι, hι, f, C, hf, hr, hN0, -⟩ := (hpJ Y hY Y' hY').1
      refine ⟨(MCRep.zero_of_range hf hr hN0).congr fun α t s ht _ => ?_, fun α t s ht => ?_⟩
      · simp only [gTerm_eq_zero (hz) Y Y' α ht s, integral_zero]
      · rw [gTerm_eq_zero hz Y Y' α ht s]
        exact integrable_zero _ _ _
  refine ⟨fun Y Y' pc α t s =>
      ∫ w, gTerm σ ε (twistP P s) fb Cb c (if pc then GJ Y else GR Y) Y Y' α t s w, ?_, ?_⟩
  · intro Y hY Y' hY' pc
    cases pc
    · simpa using (hpR Y hY Y' hY').1
    · simpa using (hpJ Y hY Y' hY').1
  · intro α τ s hτ hs
    have hR : ∀ j ∈ Set.Ico 0 c.size, ∀ β u v, u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 →
        (∫ lam, (P j).C (β ∘ (P j).f) lam * e2 lam (u + s) (v + s)) =
          ∫ lam, (twistP P s j).C (β ∘ (twistP P s j).f) lam * e2 lam u v := fun j _ β u v _ _ => by
      refine integral_congr_ae (Eventually.of_forall fun lam => ?_)
      exact (tsym_mul_e2 s (P j).C (β ∘ (P j).f) lam u v).symm
    rw [chainT_bottom_expand (P := twistP P s) hε hζ hc hinj (fun j => (hPreg j).twisted s) hR
      hCb.reg heb (GJ := GJ) (GR := GR) (fun Y _ => hGJR Y) α hτ hs fun Y hY Y' hY' =>
        ⟨(hpJ Y (Finset.mem_powerset.1 hY) Y' (Finset.mem_powerset.1 hY')).2 α τ s hτ,
          (hpR Y (Finset.mem_powerset.1 hY) Y' (Finset.mem_powerset.1 hY')).2 α τ s hτ⟩]
    simp

end Main

end WaveTurbulence.ClassJR
