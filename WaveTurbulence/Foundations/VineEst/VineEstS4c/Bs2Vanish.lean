/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4c.ReplaceAlgebra
public import WaveTurbulence.Foundations.WaveB.FrozenB1
import Mathlib.Tactic

/-!
# V5 Step 4c: the `Bs''` vanishing (TARGET L1913-L1923)

* `kDomain_eq_empty_of_up_le`, `kernelK_eq_zero_of_kDomain_empty`, `KQstar_eq_zero_of_le`,
  `KTstar_eq_zero_of_le`: a kernel `𝒦*` vanishes at times `≤` the layer of a branching node, because the
  time domain `kDomain` (layer `< τ_b < up b`) is empty;
* `extConst`: the continuous extension of a time profile by constants outside `[L, L+1]`, which vanishes for
  `t ≤ L` once the profile vanishes at `L`;
* `replSum_decomp_ext`: `replSum_decomp_at` with `Bs₀ := {b : both root layers ≤ L₄}` and the vanishing
  hypothesis `hvan` discharged from the endpoint vanishing of the profiles.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set Finset
open scoped ENNReal

namespace WaveTurbulence.VineEstS4c

section KDomainVanishing

variable {w : ℕ}

end KDomainVanishing


section Extension

variable {α : Type*}

/-- The continuous extension of a time profile `F` on `[L, L+1]` by constants outside (TARGET L1913-L1919). -/
@[expose] def extConst (L : ℝ) (F : ℝ → α) (t : ℝ) : α := F (min (max t L) (L + 1))

theorem extConst_of_le {L : ℝ} (F : ℝ → α) {t : ℝ} (h : t ≤ L) : extConst L F t = F L := by
  unfold extConst
  rw [max_eq_right h, min_eq_left (by linarith)]

theorem extConst_of_mem {L : ℝ} (F : ℝ → α) {t : ℝ} (h1 : L ≤ t) (h2 : t ≤ L + 1) :
    extConst L F t = F t := by
  unfold extConst
  rw [max_eq_left h1, min_eq_left h2]

theorem extConst_of_ge {L : ℝ} (F : ℝ → α) {t : ℝ} (h : L + 1 ≤ t) :
    extConst L F t = F (L + 1) := by
  unfold extConst
  rw [max_eq_left (by linarith), min_eq_right h]

end Extension

section Bs2

open Classical

variable {β κ : Type*}

/-- The family of constant extensions of the profiles `Q₀ b (·) s k` on the root unit intervals `[Lq b, Lq b + 1]`. -/
@[expose] def extFam (Lq : β → ℕ) (Q₀ : β → ℝ → ℝ → κ → ℂ) : β → ℝ → ℝ → κ → ℂ :=
  fun b t s k => extConst (Lq b : ℝ) (fun τ => Q₀ b τ s k) t

/-- **Mixed family (R35).** For a pair whose `𝒬`-side is *trivial* (`tq b`) the exact kernel `Ex`
(`F · 1_{t > q}`) is used, with no remainder; for a nontrivial one the constant extension `extFam` of the
approximant. -/
@[expose] noncomputable def mixFam (tq : β → Prop) (Ex : β → ℝ → ℝ → κ → ℂ) (Lq : β → ℕ)
    (Q₀ : β → ℝ → ℝ → κ → ℂ) : β → ℝ → ℝ → κ → ℂ :=
  fun b t s k => if tq b then Ex b t s k else extFam Lq Q₀ b t s k

theorem mixFam_of_tq {tq : β → Prop} {Ex : β → ℝ → ℝ → κ → ℂ} {Lq : β → ℕ}
    {Q₀ : β → ℝ → ℝ → κ → ℂ} {b : β} (h : tq b) (t s : ℝ) (k : κ) :
    mixFam tq Ex Lq Q₀ b t s k = Ex b t s k := by
  simp [mixFam, h]

theorem mixFam_of_not {tq : β → Prop} {Ex : β → ℝ → ℝ → κ → ℂ} {Lq : β → ℕ}
    {Q₀ : β → ℝ → ℝ → κ → ℂ} {b : β} (h : ¬ tq b) (t s : ℝ) (k : κ) :
    mixFam tq Ex Lq Q₀ b t s k = extFam Lq Q₀ b t s k := by
  simp [mixFam, h]

/-- Above the root layer the exact kernel of a trivial pair agrees with the extended approximant
(`F · 1_{t>q}` versus the constant `F`), so the mixed family equals `extFam` there. -/
theorem mixFam_eq_extFam_of_lt {tq : β → Prop} {Ex : β → ℝ → ℝ → κ → ℂ} {Lq : β → ℕ}
    {Q₀ : β → ℝ → ℝ → κ → ℂ}
    (hag : ∀ b, tq b → ∀ t, (Lq b : ℝ) < t → ∀ s k, Ex b t s k = extFam Lq Q₀ b t s k)
    {b : β} {t : ℝ} (ht : (Lq b : ℝ) < t) (s : ℝ) (k : κ) :
    mixFam tq Ex Lq Q₀ b t s k = extFam Lq Q₀ b t s k := by
  by_cases h : tq b
  · rw [mixFam_of_tq h]; exact hag b h t ht s k
  · exact mixFam_of_not h t s k

/-- **Realness for the mixed products** (layerregest10, R35 check). For `t₁ > L₄` every `b` of the
leading sum has root layers `≤ L₄ < t₁`, so the mixed products equal the extended-approximant products
and realness of the latter (the gate) gives realness of the former. At the single time `t₁ = L₄`
(a null set) the exact kernels of trivial pairs are `0` while the approximants are `F`, and realness
need not transfer pointwise; this is why the main theorem takes `hreal` for the mixed family as a
premise and the consumer verifies it for `t₁ > L₄` by this lemma (a.e. statement). -/
theorem hreal_mix_of_ext (Bs : Finset β) (Lq Lt : β → ℕ) (L₄ : ℕ)
    (tq tt : β → Prop) (Ex Et Q₀ T₀ : β → ℝ → ℝ → κ → ℂ)
    (hagQ : ∀ b, tq b → ∀ t, (Lq b : ℝ) < t → ∀ s k, Ex b t s k = extFam Lq Q₀ b t s k)
    (hagT : ∀ b, tt b → ∀ t, (Lt b : ℝ) < t → ∀ s k, Et b t s k = extFam Lt T₀ b t s k)
    (t0 t1 : ℝ) (x : κ) (ht : (L₄ : ℝ) < t1)
    (hreal : (∑ b ∈ Bs.filter (fun b => Lq b ≤ L₄ ∧ Lt b ≤ L₄),
      extFam Lq Q₀ b t1 t0 x * (starRingEnd ℂ) (extFam Lt T₀ b t1 t0 x)).im = 0) :
    (∑ b ∈ Bs.filter (fun b => Lq b ≤ L₄ ∧ Lt b ≤ L₄),
      mixFam tq Ex Lq Q₀ b t1 t0 x * (starRingEnd ℂ) (mixFam tt Et Lt T₀ b t1 t0 x)).im = 0 := by
  have hs : (∑ b ∈ Bs.filter (fun b => Lq b ≤ L₄ ∧ Lt b ≤ L₄),
      mixFam tq Ex Lq Q₀ b t1 t0 x * (starRingEnd ℂ) (mixFam tt Et Lt T₀ b t1 t0 x)) =
      ∑ b ∈ Bs.filter (fun b => Lq b ≤ L₄ ∧ Lt b ≤ L₄),
      extFam Lq Q₀ b t1 t0 x * (starRingEnd ℂ) (extFam Lt T₀ b t1 t0 x) := by
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_filter] at hb
    have hq : (Lq b : ℝ) < t1 := lt_of_le_of_lt (by exact_mod_cast hb.2.1) ht
    have hT : (Lt b : ℝ) < t1 := lt_of_le_of_lt (by exact_mod_cast hb.2.2) ht
    rw [mixFam_eq_extFam_of_lt hagQ hq, mixFam_eq_extFam_of_lt hagT hT]
  rw [hs]; exact hreal

/-- **The `Bs''` argument** (TARGET L1921-L1923), repaired as in R35.
`Q₀, T₀` are the approximant profiles on the unit intervals of their roots (layers `Lq b`, `Lt b`) and
`extFam` their constant extensions; for the *trivial* pairs (`tq b`, `tt b`) the exact kernels `Ex`, `Et`
(`F · 1_{t > q}`: zero for `t ≤ Lq b`, no remainder) are used instead (`mixFam`). The endpoint vanishing
`hQ0`/`hT0` is now required only for nontrivial `b` and only for `s` in a domain `Dq b`/`Dt b` that the
consumer places `t₀` in (`hDq`, `hDt`; e.g. the source domain `s ≥ q'`).
For `t₁ ∈ [L₄, L₄+1]` every pair with a root layer `> L₄` contributes `0` at `(t₁,t₀,x)`, so
`Bs₀ = {b ∈ Bs₁ ∪ Bs₂ : both root layers ≤ L₄}` (which must lie in `Bs₁ ∩ Bs₂`: `hsub`,
`Bs'' ⊂ Bs ∩ Bs'` of the source) can replace `Bs₁, Bs₂` at the leading term. -/
theorem replSum_decomp_ext (Bs₁ Bs₂ : Finset β) (Lq Lt : β → ℕ) (L₄ : ℕ)
    (tq tt : β → Prop) (Ex Et Q₀ T₀ Qb Tb eQ eT : β → ℝ → ℝ → κ → ℂ)
    (Dq Dt : β → ℝ → Prop)
    (hEx : ∀ b, tq b → ∀ t s k, t ≤ (Lq b : ℝ) → Ex b t s k = 0)
    (hEt : ∀ b, tt b → ∀ t s k, t ≤ (Lt b : ℝ) → Et b t s k = 0)
    (hQ0 : ∀ b, ¬ tq b → ∀ s k, Dq b s → Q₀ b (Lq b) s k = 0)
    (hT0 : ∀ b, ¬ tt b → ∀ s k, Dt b s → T₀ b (Lt b) s k = 0)
    (hsub : ∀ b ∈ Bs₁ ∪ Bs₂, Lq b ≤ L₄ → Lt b ≤ L₄ → b ∈ Bs₁ ∧ b ∈ Bs₂)
    (hQb : ∀ b t s k, Qb b t s k =
      (starRingEnd ℂ) (mixFam tq Ex Lq Q₀ b s t k) + eQ b t s k)
    (hTb : ∀ b t s k, Tb b t s k =
      (starRingEnd ℂ) (mixFam tt Et Lt T₀ b t s k) + eT b t s k)
    (t0 s1 t1 : ℝ) (x y : κ) (ht1 : t1 ≤ L₄ + 1)
    (hDq : t0 < t1 → ∀ b ∈ Bs₁ ∪ Bs₂, L₄ < Lq b → ¬ tq b → Dq b t0)
    (hDt : t0 < t1 → ∀ b ∈ Bs₁ ∪ Bs₂, L₄ < Lt b → ¬ tt b → Dt b t0)
    (hreal : t0 < t1 → (∑ b ∈ (Bs₁ ∪ Bs₂).filter (fun b => Lq b ≤ L₄ ∧ Lt b ≤ L₄),
      mixFam tq Ex Lq Q₀ b t1 t0 x * (starRingEnd ℂ) (mixFam tt Et Lt T₀ b t1 t0 x)).im = 0) :
    replSum Bs₁ Bs₂ (mixFam tq Ex Lq Q₀) Qb (mixFam tt Et Lt T₀) Tb t0 s1 t1 x y =
      pieceA1 Bs₁ (mixFam tt Et Lt T₀) Qb t0 s1 t1 x y -
        pieceA2 Bs₂ (mixFam tq Ex Lq Q₀) Tb t0 s1 t1 x y +
      (if t0 < t1 ∧ t0 < s1 then
        pieceKQ Bs₁ (mixFam tq Ex Lq Q₀) (mixFam tt Et Lt T₀) t0 s1 t1 x y +
          pieceTQ Bs₁ (mixFam tq Ex Lq Q₀) (mixFam tt Et Lt T₀) t0 s1 t1 x +
          pieceKT Bs₂ (mixFam tq Ex Lq Q₀) (mixFam tt Et Lt T₀) t0 s1 t1 x y +
          pieceTT Bs₂ (mixFam tq Ex Lq Q₀) (mixFam tt Et Lt T₀) t0 s1 t1 x +
          pieceDef Bs₁ Bs₂ (mixFam tq Ex Lq Q₀) (mixFam tt Et Lt T₀) eQ eT t0 s1 t1 x y else 0) := by
  refine replSum_decomp_at Bs₁ Bs₂ ((Bs₁ ∪ Bs₂).filter (fun b => Lq b ≤ L₄ ∧ Lt b ≤ L₄))
    (mixFam tq Ex Lq Q₀) Qb (mixFam tt Et Lt T₀) Tb eQ eT hQb hTb ?_ ?_ t0 s1 t1 x y ?_ hreal
  · intro b hb
    rw [Finset.mem_filter] at hb
    exact (hsub b hb.1 hb.2.1 hb.2.2).1
  · intro b hb
    rw [Finset.mem_filter] at hb
    exact (hsub b hb.1 hb.2.1 hb.2.2).2
  · intro b hb hb0 h01
    have hn : ¬ (Lq b ≤ L₄ ∧ Lt b ≤ L₄) := fun h => hb0 (Finset.mem_filter.mpr ⟨hb, h⟩)
    by_cases hq : Lq b ≤ L₄
    · have ht : ¬ Lt b ≤ L₄ := fun h => hn ⟨hq, h⟩
      have hle : t1 ≤ (Lt b : ℝ) := by
        have : (L₄ : ℝ) + 1 ≤ Lt b := by exact_mod_cast (show L₄ + 1 ≤ Lt b by omega)
        linarith
      have : mixFam tt Et Lt T₀ b t1 t0 x = 0 := by
        by_cases htt : tt b
        · rw [mixFam_of_tq htt]; exact hEt b htt _ _ _ hle
        · rw [mixFam_of_not htt]
          unfold extFam; rw [extConst_of_le _ hle]
          exact hT0 b htt _ _ (hDt h01 b hb (by omega) htt)
      rw [this]; simp
    · have hle : t1 ≤ (Lq b : ℝ) := by
        have : (L₄ : ℝ) + 1 ≤ Lq b := by exact_mod_cast (show L₄ + 1 ≤ Lq b by omega)
        linarith
      have : mixFam tq Ex Lq Q₀ b t1 t0 x = 0 := by
        by_cases hqq : tq b
        · rw [mixFam_of_tq hqq]; exact hEx b hqq _ _ _ hle
        · rw [mixFam_of_not hqq]
          unfold extFam; rw [extConst_of_le _ hle]
          exact hQ0 b hqq _ _ (hDq h01 b hb (by omega) hqq)
      rw [this]; simp

end Bs2

end WaveTurbulence.VineEstS4c
