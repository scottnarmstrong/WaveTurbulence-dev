/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.SysDraft.DuhNode

/-!
# The Duhamel identity for `ℒ_j` / `a^tr` (scratch, snapshot 5)

Assembled from the root splitting `treeTerm_node` (O-TR1, `Duh-Node`), the integrability
`intervalIntegrable_treeTriple` (O-TR2, `Duh-Meas`) and `treeRecursion_of` (`Sys-TreeRec`):

* `treeRecursion`: for `t ≥ p` and summable data,
  `𝒥_{K+1}(t) = ∑_{N₁+N₂+N₃=K} ∫_p^t 𝒞₊(𝒥_{N₁}, 𝒥̄_{N₂}, 𝒥_{N₃})`;
* `intervalIntegrable_treeTermN_triple`: the `𝒥`-only slot integrands are interval integrable;
* **`duhamel_iff_Lop'`** (glue list): for `t ≥ p`, `A = a^tr + b` satisfies
  `A(t) = a(p) + ∫_p^t 𝒞₊(A, Ā, A)` iff `b(t) = ℒ₀ b(t) + ℒ₁ b(t) + ℒ₂ b(t) + ℒ₃ b(t)`.
  Its hypotheses: summable data, and integrability of the slot integrands that contain `b`.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

variable (L γ δ : ℝ) {d : ℕ}

/-- **The tree recursion** (T (defjt), (defjn)). -/
theorem treeRecursion (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖) {t : ℝ}
    (ht : (p : ℝ) ≤ t) (n : Fin d → ℤ) : TreeRecursion L γ δ p aP t n :=
  treeRecursion_of L γ δ p haP t n (fun l m r => treeTerm_node l m r L γ δ p haP ht n)
    fun l m r => intervalIntegrable_treeTriple L γ δ p l m r haP t n

/-- The `𝒥`-only integrands `s ↦ 𝒞₊(𝒥_{N₁}, 𝒥̄_{N₂}, 𝒥_{N₃})(s)_n` are interval integrable. -/
theorem intervalIntegrable_treeTermN_triple (p N₁ N₂ N₃ : ℕ) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) (t : ℝ) (n : Fin d → ℤ) :
    IntervalIntegrable (fun s => aNonlin L γ δ 1 s (treeTermN L γ δ p N₁ aP s)
      (fun k => (starRingEnd ℂ) (treeTermN L γ δ p N₂ aP s k)) (treeTermN L γ δ p N₃ aP s) n)
      volume p t := by
  have hexp : (fun s => aNonlin L γ δ 1 s (treeTermN L γ δ p N₁ aP s)
      (fun k => (starRingEnd ℂ) (treeTermN L γ δ p N₂ aP s k)) (treeTermN L γ δ p N₃ aP s) n) =
      fun s => ∑ l ∈ treesOfOrder N₁, ∑ m ∈ treesOfOrder N₂, ∑ r ∈ treesOfOrder N₃,
        aNonlin L γ δ 1 s (treeTerm L γ δ p l aP s)
          (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m aP s k)) (treeTerm L γ δ p r aP s) n := by
    funext s
    have h1 : treeTermN L γ δ p N₁ aP s = fun k => ∑ l ∈ treesOfOrder N₁, treeTerm L γ δ p l aP s k :=
      funext fun k => treeTermN_eq_sum L γ δ p _ aP s k
    have h2 : (fun k => (starRingEnd ℂ) (treeTermN L γ δ p N₂ aP s k)) =
        fun k => ∑ m ∈ treesOfOrder N₂, (starRingEnd ℂ) (treeTerm L γ δ p m aP s k) :=
      funext fun k => by rw [treeTermN_eq_sum, map_sum]
    have h3 : treeTermN L γ δ p N₃ aP s = fun k => ∑ r ∈ treesOfOrder N₃, treeTerm L γ δ p r aP s k :=
      funext fun k => treeTermN_eq_sum L γ δ p _ aP s k
    rw [h1, h2, h3]
    exact aNonlin_sum L γ δ 1 s _ _ _ (fun l => treeTerm L γ δ p l aP s)
      (fun m k => (starRingEnd ℂ) (treeTerm L γ δ p m aP s k)) (fun r => treeTerm L γ δ p r aP s)
      (fun l => summable_norm_treeTerm L γ δ p l haP s)
      (fun m => by simpa using summable_norm_treeTerm L γ δ p m haP s)
      (fun r => summable_norm_treeTerm L γ δ p r haP s) n
  have hsum : ∀ {ι : Type} (S : Finset ι) (F : ι → ℝ → ℂ),
      (∀ i ∈ S, IntervalIntegrable (F i) volume p t) →
        IntervalIntegrable (fun s => ∑ i ∈ S, F i s) volume p t := by
    intro ι S F hF
    have h := IntervalIntegrable.sum S hF
    convert h using 1
    funext s
    simp [Finset.sum_apply]
  rw [hexp]
  exact hsum _ _ fun l _ => hsum _ _ fun m _ => hsum _ _ fun r _ =>
    intervalIntegrable_treeTriple L γ δ p l m r haP t n

/-- **The Duhamel identity for `ℒ_j`/`a^tr`** (glue list; T (eqnbk1.5)). Let `t ≥ p`, let `a(p)` and
the values of `b` have summable norms, and let the slot integrands containing `b` be interval
integrable on `[p, t]`. Then `A = a^tr + b` satisfies `A(t) = a(p) + ∫_p^t 𝒞₊(A, Ā, A)` iff
`b(t) = ∑_{j ≤ 3} ℒ_j b(t)`. -/
theorem duhamel_iff_Lop' (p Ntr : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun m => ‖aP m‖)
    {b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ} (hb : ∀ s, Summable fun m => ‖b s m‖) {t : ℝ}
    (ht : (p : ℝ) ≤ t) (n : Fin d → ℤ)
    (hint : ∀ x : Slot Ntr × Slot Ntr × Slot Ntr, slotCountB x ≠ 0 → IntervalIntegrable
      (fun s => aNonlin L γ δ 1 s (slotVal L γ δ p Ntr aP b x.1 s)
        (fun m => (starRingEnd ℂ) (slotVal L γ δ p Ntr aP b x.2.1 s m))
        (slotVal L γ δ p Ntr aP b x.2.2 s) n) volume p t) :
    (aTr L γ δ p Ntr aP t n + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b t n =
        aP n + ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s
          (fun m => aTr L γ δ p Ntr aP s m + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m)
          (fun m => (starRingEnd ℂ)
            (aTr L γ δ p Ntr aP s m + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m))
          (fun m => aTr L γ δ p Ntr aP s m + Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m)
          n) ↔
      Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b t n =
        ∑ j ∈ range 4, Lop L γ δ p Ntr aP j b t n := by
  refine duhamel_iff_Lop L γ δ p Ntr haP hb t n (fun x => ?_) (treeRecursion L γ δ p haP ht n)
  by_cases hx : slotCountB x = 0
  · obtain ⟨a, a', a'', rfl⟩ := slotCountB_eq_zero hx
    exact intervalIntegrable_treeTermN_triple L γ δ p a a' a'' haP t n
  · exact hint x hx

end WaveTurbulence.SysAPI
