/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Arith2
/-! **L6E GHOST, part 6: the leaves of the repaired charged triangle bound** (M1-R2 Theorem 6.1 (b)–(d), §10.1).

Copies of main's G2-GHOST leaves (`leaf_B2_beta`, `leaf_B2_alpha`, `leaf_P5_alpha2`, `final_B2`) without
`8η ≤ 2γ - 1`:
* `leaf_B2_beta_low`, `leaf_B2_alpha_low` (the latter with the ghost-label slab, REF-M1R2 R2);
* `final_B2_low`: the two-block tail (one new `α`-atom, one ghost);
* `TRpair`: the transversality of the gaps of two triangle atoms (the (f′) class TR, `sin² ∠ ≥ L^{-12η}`);
* `PairOK`: (T-crit-free) or (T-TR) for one pair of `α`-ghosts;
* `leaf_P5_two_low`: three singleton blocks with two `α`-ghosts, transfer exponent `ν ∈ {0, 1}`: the bound carries
  `L^{5ην}`; `ν = 0` needs `PairOK` (crit-free: one slab; TR: two slabs), `ν = 1` needs nothing (NC). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCount.TriData

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The constant of the repaired charged triangle bound (depends on `d, c, η, δ` only). -/
noncomputable def ghostConstLow (d c : ℕ) (η δ : ℝ) : ℝ := ghostConst d c η δ + constB2 d c η + constTR d c η δ

theorem ghostConst_le_low (d c : ℕ) {η δ : ℝ} (hδ : 0 < δ) : ghostConst d c η δ ≤ ghostConstLow d c η δ := by
  unfold ghostConstLow; linarith [constB2_nonneg d c η, constTR_nonneg d c η δ hδ]

theorem constB2_le_low (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) : constB2 d c η ≤ ghostConstLow d c η δ := by
  unfold ghostConstLow
  have := ghostConst_ge_triConst d c hη hδ
  have := triConst_nonneg d c hη hδ
  linarith [constTR_nonneg d c η δ hδ]

theorem constTR_le_low (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) : constTR d c η δ ≤ ghostConstLow d c η δ := by
  unfold ghostConstLow
  have := ghostConst_ge_triConst d c hη hδ
  have := triConst_nonneg d c hη hδ
  linarith [constB2_nonneg d c η]

theorem ghostConstLow_ge_S2 (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) ≤ ghostConstLow d c η δ :=
  (ghostConst_ge_S2 d c hη hδ).trans (ghostConst_le_low d c hδ)

theorem ghostConstLow_ge_S4 (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) ≤ ghostConstLow d c η δ :=
  (ghostConst_ge_S4 d c hη hδ).trans (ghostConst_le_low d c hδ)

theorem one_le_rpow_transfer {L η : ℝ} (hL : 1 ≤ L) (hη : 0 < η) (ν : ℕ) : 1 ≤ L ^ (5 * η * (ν : ℝ)) :=
  Real.one_le_rpow hL (by positivity)

/-- `K X ≤ K' X L^{5ην}` from `K ≤ K'`, `0 ≤ X`. -/
theorem le_mul_transfer {K K' X L η : ℝ} (hK : K ≤ K') (hK0 : 0 ≤ K) (hX : 0 ≤ X) (hL : 1 ≤ L) (hη : 0 < η)
    (ν : ℕ) : K * X ≤ K' * X * L ^ (5 * η * (ν : ℝ)) := by
  have h1 := one_le_rpow_transfer hL hη ν
  calc K * X ≤ K' * X := mul_le_mul_of_nonneg_right hK hX
    _ = K' * X * 1 := by ring
    _ ≤ K' * X * L ^ (5 * η * (ν : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (le_trans hK0 hK) hX)

namespace Tri
variable {M : Molecule V D} (T : TriData M)

/-- Leaf: two blocks (one new `α`-atom `(R, κ)`, one `β`-ghost) without `8η ≤ 2γ - 1`. -/
theorem leaf_B2_beta_low {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (R : ℝ) (κ : ℕ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R))
    (hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ))
    (hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (T.tripleSet L γ δ w Adm c β k0).encard ≤
        ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) *
          (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal ((3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        excessRHS L γ η [(R, κ)] 0 0)) := by
  refine T.tri_dev_of_arith H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ 2 hN hk _ ?_
  have h := arith_B2_beta_low d (na := (M.atoms.card : ℝ)) c κ H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 H.hL H.hδ0 H.hδ1
    H.hC (Nat.cast_nonneg _) hn hRl hRu hρ
  unfold slabR
  exact h

/-- Leaf: two blocks (one new `α`-atom `(R, κ)`, one `α`-ghost `(Q_g, κ_g)`), the **ghost-label slab**. -/
theorem leaf_B2_alpha_low {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (R : ℝ) (κ : ℕ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R))
    (Qg : ℝ) (κg : ℕ) (hQl : L⁻¹ ≤ Qg) (hQu : Qg ≤ L ^ (-γ + η))
    (hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ))
    (hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (T.tripleSet L γ δ w Adm c β k0).encard ≤
        (((⌊2 * slabR M L γ δ / (Qg / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) *
          (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (constB2 d c η *
        (excessRHS L γ η [(R, κ)] 0 1 / (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg)))) := by
  refine T.tri_dev_of_arith H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ 2 hN hk _ ?_
  have h := arith_B2_alpha_low d (na := (M.atoms.card : ℝ)) c κ κg H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 H.hL H.hδ0
    H.hδ1 H.hC (Nat.cast_nonneg _) hn hRl hRu hρ hQl hQu
  unfold slabR
  exact h

/-- **The two-block tail without `8η ≤ 2γ - 1`** (copy of main's `final_B2`): one new `α`-atom `(R, κ)`, one ghost at
`s`. The count is supplied in both forms: the ghost-label slab when the ghost is `α`, main's count when it is `β`. -/
theorem final_B2_low {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (R : ℝ) (κ : ℕ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R))
    (hlab : T.alphaLabels R₀ R₁ κ₀ κ₁ = [(R, κ)])
    (hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ))
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j) (s : Fin 3)
    (hs : ∀ j, gh j ↔ j = s)
    (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (hQl : ∀ j, ag j → L⁻¹ ≤ Qg j) (hQu : ∀ j, ag j → Qg j ≤ L ^ (-γ + η))
    (hNa : ag s → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (T.tripleSet L γ δ w Adm c β k0).encard ≤
        (((⌊2 * slabR M L γ δ / (Qg s / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) *
          (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞))
    (hNb : ¬ ag s → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (T.tripleSet L γ δ w Adm c β k0).encard ≤
        ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) *
          (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (ghostConstLow d c η δ *
        (excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
          ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
          (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
            ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) /
          ghostCharge L γ η ag Qg kg))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hR0 : 0 ≤ R := (inv_pos.2 hL0).le.trans hRl
  have hfgh : Finset.univ.filter gh = {s} := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]; exact hs j
  have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 1 := by omega
  by_cases hags : ag s
  · have hfa : Finset.univ.filter ag = {s} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact (hs j).1 (hag j h)
      · rintro rfl; exact hags
    have hgbf : (Finset.univ.filter fun j => gh j ∧ ¬ ag j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _ h
      have := (hs j).1 h.1
      subst this; exact h.2 hags
    have hch : ghostCharge L γ η ag Qg kg = L ^ ((γ + 3 * η) / 2 - (kg s : ℝ) * η) * Qg s := by
      unfold ghostCharge; rw [hfa]; simp
    have leaf := leaf_B2_alpha_low T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R κ hRl hRu ρ hρ (Qg s) (kg s)
      (hQl s hags) (hQu s hags) hk (hNa hags)
    refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal ?_)
    have hex : excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
        ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
        (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
          ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) = excessRHS L γ η [(R, κ)] 0 1 := by
      rw [hlab, hgbf, hfgh]
      congr 1
      all_goals (try simp only [List.length_singleton, Finset.card_empty, Finset.card_singleton])
      all_goals omega
    rw [hex, hch]
    have hT : 0 < L ^ ((γ + 3 * η) / 2 - (kg s : ℝ) * η) * Qg s :=
      mul_pos (Real.rpow_pos_of_pos hL0 _) (lt_of_lt_of_le (inv_pos.2 hL0) (hQl s hags))
    refine excess_mono_const (constB2_le_low d c H.hη H.hδ0) (div_nonneg ?_ hT.le)
    exact excessRHS_nonneg L γ η hL0 _ (by simpa using hR0) _ _
  · have hfa : Finset.univ.filter ag = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _ h
      have := (hs j).1 (hag j h)
      subst this; exact hags h
    have hgbf : (Finset.univ.filter fun j => gh j ∧ ¬ ag j) = {s} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact (hs j).1 h.1
      · rintro rfl; exact ⟨(hs j).2 rfl, hags⟩
    have hch : ghostCharge L γ η ag Qg kg = 1 := by
      unfold ghostCharge; rw [hfa]; simp
    have leaf := leaf_B2_beta_low T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R κ hRl hRu ρ hρ hk (hNb hags)
    refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal ?_)
    have hex : excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
        ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
        (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
          ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) = excessRHS L γ η [(R, κ)] 0 0 := by
      rw [hlab, hgbf, hfgh]
      congr 1
      all_goals (try simp only [List.length_singleton, Finset.card_singleton])
      all_goals omega
    rw [hex, hch, div_one]
    exact excess_mono_const (ghostConstLow_ge_S4 d c H.hη H.hδ0)
      (excessRHS_nonneg L γ η hL0 _ (by simpa using hR0) _ _)

end Tri

/-- **The class TR of a pair of triangle atoms** (M1-R2 §6 (f′), §10.1 (T-TR)): on the admissible set, the gaps at
`j₁`, `j₂` make an angle `θ` with `sin² θ ≥ θ₀² = L^{-12η}` (Gram form). -/
def TRpair {M : Molecule V D} (T : TriData M) (L η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (j₁ j₂ : Fin 3) : Prop :=
  ∀ κ', Adm κ' →
    L ^ (-12 * η) * (‖Molecule.gapAt L w κ' (T.a j₁) (T.b j₁)‖ ^ 2 * ‖Molecule.gapAt L w κ' (T.a j₂) (T.b j₂)‖ ^ 2) ≤
      ‖Molecule.gapAt L w κ' (T.a j₁) (T.b j₁)‖ ^ 2 * ‖Molecule.gapAt L w κ' (T.a j₂) (T.b j₂)‖ ^ 2 -
        inner ℝ (Molecule.gapAt L w κ' (T.a j₁) (T.b j₁)) (Molecule.gapAt L w κ' (T.a j₂) (T.b j₂)) ^ 2

/-- **(T-crit-free) or (T-TR)** for a pair of `α`-ghosts with labels `(Q₁, κ₁)`, `(Q₂, κ₂)` at `j₁`, `j₂`
(M1-R2 §10.1): a `κ = 50` ghost, or a label below `L^{-γ₀-4η}`, or transverse gaps. -/
def PairOK {M : Molecule V D} (T : TriData M) (L γ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (j₁ j₂ : Fin 3) (Q₁ Q₂ : ℝ) (κ₁ κ₂ : ℕ) : Prop :=
  κ₁ = 50 ∨ κ₂ = 50 ∨ min Q₁ Q₂ < L ^ (-(min γ (1 - γ)) - 4 * η) ∨ TRpair T L η w Adm j₁ j₂

namespace Tri
variable {M : Molecule V D} (T : TriData M)

theorem rpow_neg6_sq {L η : ℝ} (hL : 0 < L) : (L ^ (-6 * η)) ^ 2 = L ^ (-12 * η) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; congr 1; push_cast; ring

/-- **Leaf: three singleton blocks with two `α`-ghosts `x ≠ y`, transfer exponent `ν`** (Theorem 6.1 (b)–(d)). -/
theorem leaf_P5_two_low {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hα0 : ¬ T.IsA0) (hα1 : ¬ T.IsA1) (x y : Fin 3) (Qx Qy : ℝ) (κx κy gb : ℕ) (hgb : gb ≤ 1)
    (hQxl : L⁻¹ ≤ Qx) (hQxu : Qx ≤ L ^ (-γ + η)) (hQyl : L⁻¹ ≤ Qy) (hQyu : Qy ≤ L ^ (-γ + η))
    (hlowx : ∀ κ', Adm κ' → Qx / 2 ≤ ‖Molecule.gapAt L w κ' (T.a x) (T.b x)‖)
    (hlowy : ∀ κ', Adm κ' → Qy / 2 ≤ ‖Molecule.gapAt L w κ' (T.a y) (T.b y)‖)
    (ν : ℕ) (hν : ν = 0 ∨ ν = 1) (hok : ν = 0 → PairOK T L γ η w Adm x y Qx Qy κx κy) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (ghostConstLow d c η δ *
        (excessRHS L γ η [] (-(gb : ℤ)) (1 - 2 * (gb : ℤ)) /
          ((L ^ ((γ + 3 * η) / 2 - (κx : ℝ) * η) * Qx) * (L ^ ((γ + 3 * η) / 2 - (κy : ℝ) * η) * Qy))) *
        L ^ (5 * η * (ν : ℝ)))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans H.hL
  have hQx0 : 0 < Qx := lt_of_lt_of_le (inv_pos.2 hL0) hQxl
  have hQy0 : 0 < Qy := lt_of_lt_of_le (inv_pos.2 hL0) hQyl
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((1 : ℕ) : ℤ) := by
    rw [T.deltaF_eq]; simp [hα0, hα1]
  have hE0 : 0 ≤ excessRHS L γ η [] (-(gb : ℤ)) (1 - 2 * (gb : ℤ)) := excessRHS_nonneg L γ η hL0 [] (by simp) _ _
  have hTx : 0 < L ^ ((γ + 3 * η) / 2 - (κx : ℝ) * η) * Qx := by positivity
  have hTy : 0 < L ^ ((γ + 3 * η) / 2 - (κy : ℝ) * η) * Qy := by positivity
  have hX0 : 0 ≤ excessRHS L γ η [] (-(gb : ℤ)) (1 - 2 * (gb : ℤ)) /
      ((L ^ ((γ + 3 * η) / 2 - (κx : ℝ) * η) * Qx) * (L ^ ((γ + 3 * η) / 2 - (κy : ℝ) * η) * Qy)) := by positivity
  have hK2 := ghostConstLow_ge_S2 d c H.hη H.hδ0
  have hK20 : 0 ≤ 9 * (d : ℝ) * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by
    have := H.hδ0; positivity
  -- the one-slab count along the ghost `j` of label `Q`
  have hN1 : ∀ (j : Fin 3) (Q : ℝ), 0 < Q → (∀ κ', Adm κ' → Q / 2 ≤ ‖Molecule.gapAt L w κ' (T.a j) (T.b j)‖) →
      ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        (((⌊2 * (2 * slabR M L γ δ) / (Q / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℕ∞) := by
    intro j Q hQ hl c' β k0 _
    exact T.card_P5_nu L γ δ hL0 H.hδ0 w Adm c' β k0 (T.hbeta0 hα0) (T.hbeta1 hα1) j (Q / 2) (by positivity)
      (fun κ hκ => hl κ hκ.2.2)
  rcases hν with rfl | rfl
  · have hok' := hok rfl
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    rcases hok' with hκ | hκ | hmin | htr
    · -- a `κ = 50` ghost: one slab (that of `y`)
      have dev := T.tri_dev_of_arith H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ 1 (hN1 y Qy hQy0 hlowy) hk _
        (by
          have h := arith_P5_alpha2_kappa d (na := (M.atoms.card : ℝ)) c κx κy gb hgb H.hd H.hγ0 H.hγ1 H.hη H.hη1
            H.hη2 H.hL H.hδ0 H.hδ1 H.hC (Nat.cast_nonneg _) hn hQxl hQxu hQyl hQyu rfl (Or.inl hκ)
          unfold slabR; exact h)
      exact isDeviation_mono dev (ENNReal.ofReal_le_ofReal (excess_mono_const hK2 hX0))
    · have dev := T.tri_dev_of_arith H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ 1 (hN1 y Qy hQy0 hlowy) hk _
        (by
          have h := arith_P5_alpha2_kappa d (na := (M.atoms.card : ℝ)) c κx κy gb hgb H.hd H.hγ0 H.hγ1 H.hη H.hη1
            H.hη2 H.hL H.hδ0 H.hδ1 H.hC (Nat.cast_nonneg _) hn hQxl hQxu hQyl hQyu rfl (Or.inr hκ)
          unfold slabR; exact h)
      exact isDeviation_mono dev (ENNReal.ofReal_le_ofReal (excess_mono_const hK2 hX0))
    · -- a small label: the slab of the other ghost
      rcases le_total Qx Qy with hxy | hxy
      · have hc : Qx ≤ L ^ (-min γ (1 - γ) - 4 * η) := by rw [min_eq_left hxy] at hmin; exact hmin.le
        have dev := T.tri_dev_of_arith H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ 1 (hN1 y Qy hQy0 hlowy) hk _
          (by
            have h := arith_P5_alpha2_label d (na := (M.atoms.card : ℝ)) c κx κy gb hgb H.hd H.hγ0 H.hγ1 H.hη H.hη1
              H.hη2 H.hL H.hδ0 H.hδ1 H.hC (Nat.cast_nonneg _) hn hQxl hc hQyl hQyu rfl
            unfold slabR; exact h)
        exact isDeviation_mono dev (ENNReal.ofReal_le_ofReal (excess_mono_const hK2 hX0))
      · have hc : Qy ≤ L ^ (-min γ (1 - γ) - 4 * η) := by rw [min_eq_right hxy] at hmin; exact hmin.le
        have dev := T.tri_dev_of_arith H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ 1 (hN1 x Qx hQx0 hlowx) hk _
          (by
            have h := arith_P5_alpha2_label d (na := (M.atoms.card : ℝ)) c κy κx gb hgb H.hd H.hγ0 H.hγ1 H.hη H.hη1
              H.hη2 H.hL H.hδ0 H.hδ1 H.hC (Nat.cast_nonneg _) hn hQyl hc hQxl hQxu rfl
            unfold slabR; exact h)
        refine isDeviation_mono dev (ENNReal.ofReal_le_ofReal ?_)
        rw [mul_comm (L ^ ((γ + 3 * η) / 2 - (κy : ℝ) * η) * Qy)]
        exact excess_mono_const hK2 hX0
    · -- transverse: two slabs
      have hθ1 : L ^ (-6 * η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith [H.hη])
      have hN : ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
          (T.tripleSet L γ δ w Adm c' β k0).encard ≤
            ((⌊twoSlabX d ⌊2 * L⌋₊ (2 * slabR M L γ δ) (Qx / 2 * L) (Qy / 2 * L) (L ^ (-6 * η))⌋₊ : ℕ) : ℕ∞) := by
        intro c' β k0 _
        refine card_P5_two T L γ δ hL0 H.hδ0 w Adm c' β k0 (T.hbeta0 hα0) (T.hbeta1 hα1) x y (Qx / 2) (Qy / 2)
          (L ^ (-6 * η)) (by positivity) (by positivity) (by positivity) hθ1 (fun κ hκ => hlowx κ hκ.2.2)
          (fun κ hκ => hlowy κ hκ.2.2) (fun κ hκ => ?_)
        rw [rpow_neg6_sq hL0]
        exact htr κ hκ.2.2
      have dev := T.tri_dev_of_arith H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ 1 hN hk _
        (by
          have h := arith_P5_alpha2_TR d (na := (M.atoms.card : ℝ)) c κx κy gb hgb H.hd H.hγ0 H.hγ1 H.hη H.hη1
            H.hη2 H.hL H.hδ0 H.hδ1 H.hC (Nat.cast_nonneg _) hn hQxl hQxu hQyl hQyu
          unfold slabR; exact h)
      exact isDeviation_mono dev (ENNReal.ofReal_le_ofReal
        (excess_mono_const (constTR_le_low d c H.hη H.hδ0) hX0))
  · -- near-collinear: one slab and the transfer `L^{5η}`
    simp only [Nat.cast_one, mul_one]
    have dev := T.tri_dev_of_arith H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ 1 (hN1 y Qy hQy0 hlowy) hk _
      (by
        have h := arith_P5_alpha2_NC d (na := (M.atoms.card : ℝ)) c κx κy gb hgb H.hd H.hγ0 H.hγ1 H.hη H.hη1
          H.hη2 H.hL H.hδ0 H.hδ1 H.hC (Nat.cast_nonneg _) hn hQxl hQxu hQyl hQyu rfl
        unfold slabR; exact h)
    refine isDeviation_mono dev (ENNReal.ofReal_le_ofReal ?_)
    have e : excessRHS L γ η [] (-(gb : ℤ)) (1 - 2 * (gb : ℤ)) * L ^ (5 * η) /
        ((L ^ ((γ + 3 * η) / 2 - (κx : ℝ) * η) * Qx) * (L ^ ((γ + 3 * η) / 2 - (κy : ℝ) * η) * Qy)) =
        excessRHS L γ η [] (-(gb : ℤ)) (1 - 2 * (gb : ℤ)) /
        ((L ^ ((γ + 3 * η) / 2 - (κx : ℝ) * η) * Qx) * (L ^ ((γ + 3 * η) / 2 - (κy : ℝ) * η) * Qy)) * L ^ (5 * η) := by
      ring
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (excess_mono_const hK2 hX0) (by positivity)

end Tri
end WaveTurbulence.GammaLow.FinalCount.Ghost
