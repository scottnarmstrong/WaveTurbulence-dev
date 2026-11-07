/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.MexpDraft.RegCancel

/-!
# DH23 Prop 6.3 for B2's leading terms

**`regcancel`**: for `r ≤ s ≤ t` and every `n`,
`∑_{n₁+n₂=n} ∑_{𝒬 ∈ domCodes n₁} ∑_{𝒯 ∈ domTrees n₂} (K_𝒬)_app(t,s,k) · conj((K*_𝒯)_app(t,s,k))` is real
(`RegCpl.app`, `RegChain.app` with sign `+`; F61 weights).

The pairs are grouped by joint class (`jsh`). On a class the factor `2^{-2n} δ^n ζ* ℳ*ℳ*` is constant and real, and
the class sums of `sw(Z) conj(sw(Z*)) 𝒥ℬ*𝒥ℬ*` vanish unless `Z = Z* = ∅` (`GJ_eq_zero`). In that case every factor is
real.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set Filter intervalIntegral Finset ComplexConjugate
open scoped Classical

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.Cancel

variable {d : ℕ}

theorem sum_tree_app_eq (δ r : ℝ) (F : Mom d → ℝ) (b : ℕ) (t s : ℝ) (k : Mom d) :
    ∑ X ∈ domTrees b, X.app δ r F 1 t s k = ∑ f ∈ EDT b, gtree δ r F t s k f := by
  rw [Finset.sum_congr rfl fun X hX => tree_app_eq_sum δ r F hX t s k, sum_domTrees_specialSets]

theorem cn_add (δ : ℝ) (a b : ℕ) : cn δ (a + b) = cn δ a * cn δ b := by
  simp only [cn, mul_add, pow_add]; ring

/-- The pair sums over `antidiagonal n` are the sums over `PS n`. -/
theorem sum_antidiag_pairs {M : Type*} [AddCommMonoid M] (n : ℕ) (G : ECpl → EChain → M) :
    ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ e ∈ ED ab.1, ∑ f ∈ EDT ab.2, G e f = ∑ q ∈ PS n, G q.1 q.2 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun q : ECpl × EChain => (q.1.hsize, q.2.hsize))
    (t := Finset.HasAntidiagonal.antidiagonal n) (fun q hq => by
      rw [mem_PS] at hq; rw [Finset.HasAntidiagonal.mem_antidiagonal]; exact hq.2.2)]
  refine Finset.sum_congr rfl fun ab hab => ?_
  rw [← Finset.sum_product']
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ⟨e, f⟩
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
  simp only [Finset.mem_product, mem_ED, mem_EDT, Finset.mem_filter, mem_PS, Prod.ext_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3, by omega⟩, h2, h4⟩
  · rintro ⟨⟨h1, h3, -⟩, h2, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩

/-- **DH23 Prop 6.3** (`regcpltreecancel`, L940): the sum over dominant couples `𝒬` and dominant trees `𝒯` of
sign `+` of total order `2n` of `(K_𝒬)_app(t,s,k) conj((K*_𝒯)_app(t,s,k))` is real, for `r ≤ s ≤ t`. -/
theorem regcancel (δ r : ℝ) (F : Mom d → ℝ) (n : ℕ) {s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) (k : Mom d) :
    (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ Q ∈ domCodes ab.1, ∑ X ∈ domTrees ab.2,
      Q.app δ r F t s k * conj (X.app δ r F 1 t s k)).im = 0 := by
  -- to enhanced pairs
  have h1 : ∀ ab : ℕ × ℕ, ∑ Q ∈ domCodes ab.1, ∑ X ∈ domTrees ab.2,
      Q.app δ r F t s k * conj (X.app δ r F 1 t s k) =
      ∑ e ∈ ED ab.1, ∑ f ∈ EDT ab.2, gfun δ r F t s k e * conj (gtree δ r F t s k f) := by
    intro ab
    simp only [← Finset.mul_sum, ← map_sum, ← Finset.sum_mul]
    rw [sum_app_eq, sum_tree_app_eq]
  simp only [h1]
  rw [sum_antidiag_pairs n (fun e f => gfun δ r F t s k e * conj (gtree δ r F t s k f))]
  -- the class factor
  set Φ : Shape → ℂ := fun X => ((cn δ n : ℝ) : ℂ) * (X.netSign : ℂ) * (Mshape F X k : ℂ) with hΦ
  have hG : ∀ q ∈ PS n, gfun δ r F t s k q.1 * conj (gtree δ r F t s k q.2) =
      Φ (jsh q.1 q.2) * (q.1.sw * conj (q.2.sw 1) * (Jt r q.1 q.2 t s : ℂ)) := by
    intro q hq
    rw [mem_PS] at hq
    simp only [gfun, gtree, hΦ, map_mul, Complex.conj_ofReal, map_intCast, jsh,
      netSign_prependT, mshape_prependT, Jt, ← hq.2.2, cn_add]
    push_cast
    ring
  rw [Finset.sum_congr rfl hG]
  -- split by `|Z| + |Z*|`
  have hsplit : ∀ q : ECpl × EChain, Φ (jsh q.1 q.2) * (q.1.sw * conj (q.2.sw 1) * (Jt r q.1 q.2 t s : ℂ)) =
      (if (jsh q.1 q.2).zcount ≠ 0 then
        Φ (jsh q.1 q.2) * (q.1.sw * conj (q.2.sw 1) * (Jt r q.1 q.2 t s : ℂ)) else 0) +
      (if (jsh q.1 q.2).zcount = 0 then
        Φ (jsh q.1 q.2) * (q.1.sw * conj (q.2.sw 1) * (Jt r q.1 q.2 t s : ℂ)) else 0) := by
    intro q; by_cases h : (jsh q.1 q.2).zcount = 0 <;> simp [h]
  rw [Finset.sum_congr rfl fun q _ => hsplit q, Finset.sum_add_distrib]
  have hz : ∑ q ∈ PS n, (if (jsh q.1 q.2).zcount ≠ 0 then
      Φ (jsh q.1 q.2) * (q.1.sw * conj (q.2.sw 1) * (Jt r q.1 q.2 t s : ℂ)) else 0) = 0 := by
    refine sum_class_eq_zero_gen (PS n) (fun q => jsh q.1 q.2) (fun X => X.zcount ≠ 0)
      (fun X Y h hX => by rwa [← h.zcount_eq]) _ fun q₀ _ h0 => ?_
    have hc := GJ_eq_zero r n (jsh q₀.1 q₀.2) h0 s t hrs hst
    calc ∑ q ∈ PS n, (if Shape.Equiv (jsh q.1 q.2) (jsh q₀.1 q₀.2) then
          Φ (jsh q.1 q.2) * (q.1.sw * conj (q.2.sw 1) * (Jt r q.1 q.2 t s : ℂ)) else 0)
        = Φ (jsh q₀.1 q₀.2) * GJ r n (jsh q₀.1 q₀.2) t s := by
          rw [GJ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          split_ifs with h
          · simp only [hΦ, h.netSign_eq, mshape_congr F h]
          · simp
      _ = 0 := by rw [hc, mul_zero]
  rw [hz, zero_add, Complex.im_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  split_ifs with h
  · rw [jsh, zcount_prependT, Nat.add_eq_zero_iff] at h
    rw [ECpl.sw_eq_one _ h.2, EChain.sw_eq_one _ 1 h.1]
    simp [hΦ]
  · simp

end WaveTurbulence.Mexp
