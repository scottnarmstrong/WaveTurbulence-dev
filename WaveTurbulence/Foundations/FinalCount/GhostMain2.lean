/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GhostMain1
/-! G2-GHOST part 8: the leaves of the charged triangle bound (one lemma per count shape / ghost type). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace TriData
variable {M : Molecule V D} (T : TriData M)

/-- Leaf: two blocks (one new `α`-atom `(R, κ)`, one `β`-ghost): `ΔF = ΔV_β = 0`. -/
theorem leaf_B2_beta {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hH : 8 * η ≤ 2 * γ - 1)
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
  have h := arith_B2_beta d (na := (M.atoms.card : ℝ)) c κ H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 hH H.hL H.hδ0 H.hδ1
    H.hC (Nat.cast_nonneg _) hn hRl hRu hρ
  unfold slabR
  exact h

/-- Leaf: two blocks (one new `α`-atom `(R, κ)`, one `α`-ghost `(Q_g, κ_g)`): `ΔF = 0`, `ΔV_β = 1`. -/
theorem leaf_B2_alpha {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hH : 8 * η ≤ 2 * γ - 1)
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
        ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) *
          (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal ((3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        (excessRHS L γ η [(R, κ)] 0 1 / (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg)))) := by
  refine T.tri_dev_of_arith H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ 2 hN hk _ ?_
  have h := arith_B2_alpha d (na := (M.atoms.card : ℝ)) c κ κg H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 hH H.hL H.hδ0
    H.hδ1 H.hC (Nat.cast_nonneg _) hn hRl hRu hρ hQl hQu
  unfold slabR
  exact h

/-- Leaf: three singleton blocks, `g ≤ 3` of them `β`-ghosts (no `α`-ghost): `ΔF = 2 - g`, `ΔV_β = 3 - 2g`. -/
theorem leaf_P5_beta {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (hα0 : ¬ T.IsA0) (hα1 : ¬ T.IsA1) (g : ℕ) (hg : g ≤ 3) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal ((3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / (η ^ 2 / 2)) ^ (c + 12)) *
        excessRHS L γ η [] (2 - (g : ℤ)) (3 - 2 * (g : ℤ)))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((1 : ℕ) : ℤ) := by
    rw [T.deltaF_eq]; simp [hα0, hα1]
  have hN : ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ) : ℕ∞) := by
    intro c' β k0 _
    have h := T.card_ββ L γ δ hL0 H.hδ0 w Adm c' β k0 (T.hbeta0 hα0) (T.hbeta1 hα1)
      (fun κ hκ => hnz κ hκ.2.2 0)
    exact encard_le_min _ _ h.1 h.2
  refine T.tri_dev_of_arith H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ 1 hN hk _ ?_
  have h := arith_P5_beta d (na := (M.atoms.card : ℝ)) c g hg H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hL H.hδ0 H.hδ1
    H.hC (Nat.cast_nonneg _) hn
  unfold slabR
  exact h

/-- Leaf: three singleton blocks, one `α`-ghost `(Q, κg)` at `k` and `gb ≤ 2` `β`-ghosts. -/
theorem leaf_P5_alpha1 {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hα0 : ¬ T.IsA0) (hα1 : ¬ T.IsA1) (k : Fin 3) (Q : ℝ) (κg gb : ℕ) (hgb : gb ≤ 2)
    (hQl : L⁻¹ ≤ Q) (hQu : Q ≤ L ^ (-γ + η))
    (hlow : ∀ κ', Adm κ' → Q / 2 ≤ ‖Molecule.gapAt L w κ' (T.a k) (T.b k)‖) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal ((9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        (excessRHS L γ η [] (1 - (gb : ℤ)) (2 - 2 * (gb : ℤ)) /
          (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Q)))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hQ0 : 0 < Q := lt_of_lt_of_le (inv_pos.2 hL0) hQl
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((1 : ℕ) : ℤ) := by
    rw [T.deltaF_eq]; simp [hα0, hα1]
  have hN : ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        (((⌊2 * (2 * slabR M L γ δ) / (Q / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℕ∞) := by
    intro c' β k0 _
    exact T.card_P5_nu L γ δ hL0 H.hδ0 w Adm c' β k0 (T.hbeta0 hα0) (T.hbeta1 hα1) k (Q / 2) (by positivity)
      (fun κ hκ => hlow κ hκ.2.2)
  refine T.tri_dev_of_arith H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ 1 hN hk _ ?_
  have h := arith_P5_alpha1 d (na := (M.atoms.card : ℝ)) c κg gb hgb H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 H.hL H.hδ0
    H.hδ1 H.hC (Nat.cast_nonneg _) hn hQl hQu rfl
  unfold slabR
  exact h

/-- Leaf: three singleton blocks, two `α`-ghosts (labels `Q₁`, `Q₂`; the slab is that of the gap at `k`, of
size `≥ Q₂/2`) and `gb ≤ 1` `β`-ghosts. -/
theorem leaf_P5_alpha2 {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hH : 8 * η ≤ 2 * γ - 1)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hα0 : ¬ T.IsA0) (hα1 : ¬ T.IsA1) (k : Fin 3) (Q₁ Q₂ : ℝ) (κ₁ κ₂ gb : ℕ) (hgb : gb ≤ 1)
    (hQ₁l : L⁻¹ ≤ Q₁) (hQ₁u : Q₁ ≤ L ^ (-γ + η)) (hQ₂l : L⁻¹ ≤ Q₂) (hQ₂u : Q₂ ≤ L ^ (-γ + η))
    (hlow : ∀ κ', Adm κ' → Q₂ / 2 ≤ ‖Molecule.gapAt L w κ' (T.a k) (T.b k)‖) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal ((9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        (excessRHS L γ η [] (-(gb : ℤ)) (1 - 2 * (gb : ℤ)) /
          ((L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂))))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hQ0 : 0 < Q₂ := lt_of_lt_of_le (inv_pos.2 hL0) hQ₂l
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((1 : ℕ) : ℤ) := by
    rw [T.deltaF_eq]; simp [hα0, hα1]
  have hN : ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        (((⌊2 * (2 * slabR M L γ δ) / (Q₂ / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℕ∞) := by
    intro c' β k0 _
    exact T.card_P5_nu L γ δ hL0 H.hδ0 w Adm c' β k0 (T.hbeta0 hα0) (T.hbeta1 hα1) k (Q₂ / 2) (by positivity)
      (fun κ hκ => hlow κ hκ.2.2)
  refine T.tri_dev_of_arith H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ 1 hN hk _ ?_
  have h := arith_P5_alpha2 d (na := (M.atoms.card : ℝ)) c κ₁ κ₂ gb hgb H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 hH H.hL
    H.hδ0 H.hδ1 H.hC (Nat.cast_nonneg _) hn hQ₁l hQ₁u hQ₂l hQ₂u rfl
  unfold slabR
  exact h

end TriData
end WaveTurbulence.FinalCount
