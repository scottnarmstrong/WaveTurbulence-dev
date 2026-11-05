/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.CoupleStep

/-!
# Auxiliary facts for the induction over the same-layer blocks

* `appendChain_linksAt`, `chainNodesSet_append_left`, `chainNodesSet_append_right`;
* `layer_drop_ne`: the first pair after the top block is in another layer;
* `takeLayer_ne_nil`, `two_le_size_of_ne_nil`;
* the constant absorptions `absorb_tree_err`, `absorb_tree_app`, `absorb_base_err`, `absorb_base_app`,
  `absorb_step`.
-/

@[expose] public section

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {w : ℕ}

theorem appendChain_linksAt (X Y : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    (appendChain X Y).linksAt ζ a = X.linksAt ζ a ++ Y.linksAt ζ (addrExt a X.lonePath) := by
  cases X with
  | nil => simp [appendChain, RegChain.linksAt, RegChain.lonePath, addrExt]
  | pair m r g i s =>
    simp only [appendChain, RegChain.linksAt, appendChain_linksAt s, slotSign_lone,
      RegChain.lonePath, addrExt_append, List.append_assoc, List.cons_append]
termination_by structural X

theorem chainNodesSet_append_left (X Y : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    chainNodesSet X ζ a ⊆ chainNodesSet (appendChain X Y) ζ a := by
  intro z hz
  unfold chainNodesSet at hz ⊢
  rw [appendChain_linksAt, appendChain_pairsAt, pairEndpoints_append, pairEndpoints_append]
  simp only [Finset.mem_union] at hz ⊢
  tauto

theorem chainNodesSet_append_right (X Y : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    chainNodesSet Y ζ (addrExt a X.lonePath) ⊆ chainNodesSet (appendChain X Y) ζ a := by
  intro z hz
  unfold chainNodesSet at hz ⊢
  rw [appendChain_linksAt, appendChain_pairsAt, pairEndpoints_append, pairEndpoints_append]
  simp only [Finset.mem_union] at hz ⊢
  tauto

theorem layer_drop_ne (LG : LayeredGarden w) (u : ℕ) :
    ∀ (X : RegChain) (a : Fin w × Path), dropLayer LG a u X ≠ .nil →
      layerAt LG (addrExt a (takeLayer LG a u X).lonePath) ≠ u
  | .nil, _, h => absurd rfl h
  | .pair m Qr Qg inner rest, a, h => by
    unfold dropLayer at h
    unfold takeLayer
    split_ifs with ha
    · rw [ite_eq_left ha] at h
      have ih := layer_drop_ne LG u rest (nextAddr a m inner) h
      show layerAt LG (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone] ++
        (takeLayer LG (nextAddr a m inner) u rest).lonePath)) ≠ u
      rw [← addrExt_append]
      exact ih
    · show layerAt LG (addrExt a []) ≠ u
      simpa [addrExt] using ha

theorem takeLayer_ne_nil (LG : LayeredGarden w) :
    ∀ (X : RegChain) (a : Fin w × Path), X ≠ .nil → takeLayer LG a (layerAt LG a) X ≠ .nil
  | .nil, _, h => absurd rfl h
  | .pair m Qr Qg inner rest, a, _ => by
    unfold takeLayer
    rw [ite_eq_left rfl]
    exact fun h => RegChain.noConfusion h

theorem two_le_size_of_ne_nil : ∀ (X : RegChain), X ≠ .nil → 2 ≤ X.size
  | .nil, h => absurd rfl h
  | .pair _ _ _ _ _, _ => by simp only [RegChain.size]; omega

/-! ### Constants -/

section Constants

variable {C δ Λ β : ℝ}

theorem absorb_tree_err (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hΛ : 0 ≤ Λ) (hβ : 0 ≤ β) {n : ℕ} (hn : 1 ≤ n) :
    C * (C * δ) ^ n * Λ * β ≤ (2 * C ^ 4) ^ n * δ ^ n * Λ * β := by
  have hC0 : 0 ≤ C := by linarith
  have h1 : C ^ (n + 1) ≤ C ^ (4 * n) := pow_le_pow_right₀ hC (by omega)
  have h2 : (C ^ 4) ^ n ≤ (2 * C ^ 4) ^ n := pow_le_pow_left₀ (by positivity) (by linarith [pow_nonneg hC0 4]) n
  calc C * (C * δ) ^ n * Λ * β = C ^ (n + 1) * δ ^ n * Λ * β := by ring
    _ ≤ C ^ (4 * n) * δ ^ n * Λ * β := by gcongr
    _ = (C ^ 4) ^ n * δ ^ n * Λ * β := by rw [pow_mul]
    _ ≤ (2 * C ^ 4) ^ n * δ ^ n * Λ * β := by gcongr

theorem absorb_tree_app (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) {n : ℕ} (hn : 1 ≤ n) :
    δ ^ n * 2 ^ n * (C * C ^ n) * (C * C ^ n * β) ≤ (2 * C ^ 4) ^ n * δ ^ n * β := by
  have h1 : C ^ (2 * n + 2) ≤ C ^ (4 * n) := pow_le_pow_right₀ hC (by omega)
  calc δ ^ n * 2 ^ n * (C * C ^ n) * (C * C ^ n * β) = 2 ^ n * C ^ (2 * n + 2) * δ ^ n * β := by ring
    _ ≤ 2 ^ n * C ^ (4 * n) * δ ^ n * β := by gcongr
    _ = (2 * C ^ 4) ^ n * δ ^ n * β := by rw [mul_pow, pow_mul]

theorem absorb_base_err (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hΛ : 0 ≤ Λ) (hβ : 0 ≤ β) {K : ℝ} (hK : 0 ≤ K) (m : ℕ) :
    K * (C * (C * δ) ^ m * Λ * β) ≤ 3 ^ (m + 1) * (K * C ^ 2) * (2 * C ^ 4) ^ m * δ ^ m * Λ * β := by
  have hC0 : 0 ≤ C := by linarith
  have h1 : C ^ (m + 1) ≤ C ^ 2 * C ^ (4 * m) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hC (by omega)
  have h3 : (1 : ℝ) ≤ 3 ^ (m + 1) := one_le_pow₀ (by norm_num)
  have h2 : (C ^ 4) ^ m ≤ (2 * C ^ 4) ^ m := pow_le_pow_left₀ (by positivity) (by linarith [pow_nonneg hC0 4]) m
  calc K * (C * (C * δ) ^ m * Λ * β) = K * C ^ (m + 1) * δ ^ m * Λ * β := by ring
    _ ≤ K * (C ^ 2 * C ^ (4 * m)) * δ ^ m * Λ * β := by gcongr
    _ = 1 * (K * C ^ 2) * (C ^ 4) ^ m * δ ^ m * Λ * β := by rw [pow_mul]; ring
    _ ≤ 3 ^ (m + 1) * (K * C ^ 2) * (2 * C ^ 4) ^ m * δ ^ m * Λ * β := by gcongr

theorem absorb_base_app (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) {K : ℝ} (hK : 0 ≤ K) (m : ℕ) :
    δ ^ m * 2 ^ m * (C * C ^ m * β) * (K * (C * C ^ m)) ≤ (K * C ^ 2) * (2 * C ^ 4) ^ m * δ ^ m * β := by
  have h1 : C ^ (2 * m) ≤ C ^ (4 * m) := pow_le_pow_right₀ hC (by omega)
  calc δ ^ m * 2 ^ m * (C * C ^ m * β) * (K * (C * C ^ m)) =
      (K * C ^ 2) * (2 ^ m * C ^ (2 * m)) * δ ^ m * β := by ring
    _ ≤ (K * C ^ 2) * (2 ^ m * C ^ (4 * m)) * δ ^ m * β := by gcongr
    _ = (K * C ^ 2) * (2 * C ^ 4) ^ m * δ ^ m * β := by rw [mul_pow, pow_mul]

/-- **The recursion of the step** absorbs into the normalized bounds. -/
theorem absorb_step {D₀ M₀ ε α E₂ A₂ β₁ β₂ : ℝ} (hD : 0 ≤ D₀) (hM : 0 ≤ M₀) (hδ : 0 ≤ δ) (hΛ0 : 0 ≤ Λ)
    (hΛ1 : Λ ≤ 1) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) {n m₂ : ℕ} (_hε0 : 0 ≤ ε) (_hα0 : 0 ≤ α)
    (hε : ε ≤ D₀ ^ n * δ ^ n * Λ * β₁) (hα : α ≤ D₀ ^ n * δ ^ n * β₁)
    (hE₂ : E₂ ≤ 3 ^ (m₂ + 1) * M₀ * D₀ ^ m₂ * δ ^ m₂ * Λ * β₂) (hA₂ : A₂ ≤ M₀ * D₀ ^ m₂ * δ ^ m₂ * β₂)
    (hE₂0 : 0 ≤ E₂) (hA₂0 : 0 ≤ A₂) (hn : 1 ≤ n) :
    ε * (E₂ + A₂) + α * E₂ ≤ 3 ^ (n + m₂ + 1) * M₀ * D₀ ^ (n + m₂) * δ ^ (n + m₂) * Λ * (β₁ * β₂) ∧
      α * A₂ ≤ M₀ * D₀ ^ (n + m₂) * δ ^ (n + m₂) * (β₁ * β₂) := by
  set U : ℝ := M₀ * D₀ ^ (n + m₂) * δ ^ (n + m₂) * (β₁ * β₂) with hU
  have hU0 : 0 ≤ U := by positivity
  have h3 : (2 : ℝ) * 3 ^ (m₂ + 1) + 1 ≤ 3 ^ (n + m₂ + 1) := by
    have h1 : (1 : ℝ) ≤ 3 ^ (m₂ + 1) := one_le_pow₀ (by norm_num)
    have h2 : (3 : ℝ) ^ (m₂ + 2) ≤ 3 ^ (n + m₂ + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : (3 : ℝ) ^ (m₂ + 2) = 3 * 3 ^ (m₂ + 1) := by ring
    linarith
  constructor
  · calc ε * (E₂ + A₂) + α * E₂
        ≤ (D₀ ^ n * δ ^ n * Λ * β₁) * (3 ^ (m₂ + 1) * M₀ * D₀ ^ m₂ * δ ^ m₂ * Λ * β₂ +
            M₀ * D₀ ^ m₂ * δ ^ m₂ * β₂) + (D₀ ^ n * δ ^ n * β₁) * (3 ^ (m₂ + 1) * M₀ * D₀ ^ m₂ * δ ^ m₂ * Λ * β₂) := by
          gcongr
      _ = U * Λ * (3 ^ (m₂ + 1) * Λ + 1 + 3 ^ (m₂ + 1)) := by rw [hU]; ring
      _ ≤ U * Λ * (3 ^ (m₂ + 1) * 1 + 1 + 3 ^ (m₂ + 1)) := by gcongr
      _ ≤ U * Λ * 3 ^ (n + m₂ + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = _ := by rw [hU]; ring
  · calc α * A₂ ≤ (D₀ ^ n * δ ^ n * β₁) * (M₀ * D₀ ^ m₂ * δ ^ m₂ * β₂) := by gcongr
      _ = U := by rw [hU]; ring

end Constants

end WaveTurbulence.PL234
