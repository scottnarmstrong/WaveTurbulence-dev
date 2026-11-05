/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.WkeAssemble
public import WaveTurbulence.Foundations.RegularAsymptotics.CancelDraft.ZetaBridge

/-!
# DH23 Prop 6.2 (`regcpltreesum`, L936–L938) / DH21 Props 7.9–7.10: `∑ (K*_𝒬)_app(t,t,k) = 𝒰_n(t,k)`

The leading terms of B2 (`RegCpl.app`, with the F61 weight) summed over the well-formed dominant couple codes of
order `2n` are the WKE Taylor terms (B1 `wkeTaylorTerm`, T (wketaylor2)):

* `app_eq_sum`, `sum_app_eq`: the sum over codes and special subsets is a sum over enhanced codes `ED n`;
* `sum_zcount_ne_zero`: the enhanced codes with `Z ≠ ∅` contribute nothing (Prop 7.8: `ζ*`, `ℳ*` are constant
  on classes and the class sums vanish);
* the rest is `U_n(t, k)` (`sw = 1` when `Z = ∅`), which is `𝒰_n(t, k)` (`U_eq_wkeTaylorTerm`);
* **`wke_identity`** for Schwartz inputs, `d ≥ 2`, `t ≥ p`; **`regularAsymptotics_item4`**: B2.1 item (4) in its
  own form.
-/

@[expose] public section

open MeasureTheory Set Filter intervalIntegral Finset
open scoped SchwartzMap Classical

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.Cancel WaveTurbulence.WKE

variable {d : ℕ}

mutual
/-- With `Z = ∅` the special weight is `1`. -/
theorem ECpl.sw_eq_one : (e : ECpl) → e.shape.zcount = 0 → e.sw = 1
  | .triv, _ => rfl
  | .type1 _ Q₁ Q₂ Q₃, h => by
    simp only [ECpl.shape, Shape.zcount, Nat.add_eq_zero_iff] at h
    simp only [ECpl.sw, ECpl.sw_eq_one Q₁ h.1.1, ECpl.sw_eq_one Q₂ h.1.2, ECpl.sw_eq_one Q₃ h.2, mul_one]
  | .type2 Xp Xm Qlp, h => by
    simp only [ECpl.shape, Shape.zcount, Tuples.zcount_append, Nat.add_eq_zero_iff] at h
    simp only [ECpl.sw, EChain.sw_eq_one Xp 1 h.1.1, EChain.sw_eq_one Xm (-1) h.1.2,
      ECpl.sw_eq_one Qlp h.2, mul_one]

theorem EChain.sw_eq_one : (X : EChain) → (ε : ℤˣ) → X.tuples.zcount = 0 → X.sw ε = 1
  | .nil, _, _ => rfl
  | .pair m I Qr Qg rest, ε, h => by
    obtain ⟨rfl, h₁, h₂, hr⟩ := Tuples.zcount_cons_eq_zero h
    simp only [EChain.sw, wt, Bool.false_eq_true, ↓reduceIte, ECpl.sw_eq_one Qr h₁,
      ECpl.sw_eq_one Qg h₂, EChain.sw_eq_one rest ε hr, mul_one]
end

/-- The summand of the leading terms on an enhanced code: `2^{-2n} δ^n ζ*(e) sw(e) 𝒥ℬ*_e(t,s) ℳ*_e(k)`. -/
noncomputable def gfun (δ p : ℝ) (F : Mom d → ℝ) (t s : ℝ) (k : Mom d) (e : ECpl) : ℂ :=
  ((cn δ e.hsize : ℝ) : ℂ) * (e.shape.netSign : ℂ) * e.sw * (e.JB p t s : ℂ) * (Mshape F e.shape k : ℂ)

/-- **B2's leading term of a dominant code**, summed over its enhanced codes. -/
theorem app_eq_sum (δ p : ℝ) (F : Mom d → ℝ) {n : ℕ} {Q : RegCpl} (hQ : Q ∈ domCodes n)
    (t s : ℝ) (k : Mom d) :
    Q.app δ p F t s k = ∑ Z ∈ specialSets Q.links, gfun δ p F t s k (enh Z Q rt₀ rt₁) := by
  obtain ⟨-, hd, hs⟩ := mem_domCodes.1 hQ
  simp only [RegCpl.app, hd, ↓reduceIte, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Z hZ => ?_
  have hh : (enh Z Q rt₀ rt₁).hsize = n := by have := hsize_enh Z hd rt₀ rt₁; omega
  have hns : ((cplShape0 Q).netSign : ℂ) = ((enh Z Q rt₀ rt₁).shape.netSign : ℂ) := by
    rw [ECpl.netSign_shape, code_enh Z Q hd]
  have hJB : Q.JB p t s = (enh Z Q rt₀ rt₁).JB p t s := by rw [ECpl.JB, code_enh Z Q hd]
  rw [specialWeight_eq_sw hd hZ, mstar_eq_mshape F Z Q hd, ← shape_enh, zetaOfTrees_eq_netSign Q hd,
    hns, hJB, gfun, hh, hs, cn, Nat.mul_div_cancel_left n (by norm_num : 0 < 2)]
  push_cast
  ring

theorem sum_app_eq (δ p : ℝ) (F : Mom d → ℝ) (n : ℕ) (t s : ℝ) (k : Mom d) :
    ∑ Q ∈ domCodes n, Q.app δ p F t s k = ∑ e ∈ ED n, gfun δ p F t s k e := by
  rw [Finset.sum_congr rfl fun Q hQ => app_eq_sum δ p F hQ t s k, sum_domCodes_specialSets]

/-- **The enhanced codes with `Z ≠ ∅` contribute nothing** (DH21 Prop 7.8 with Prop 7.7). -/
theorem sum_zcount_ne_zero (δ p : ℝ) (F : Mom d → ℝ) (n : ℕ) {t : ℝ} (hpt : p ≤ t) (k : Mom d) :
    ∑ e ∈ ED n, (if e.shape.zcount ≠ 0 then gfun δ p F t t k e else 0) = 0 := by
  refine sum_class_eq_zero (ED n) (fun X => X.zcount ≠ 0) (fun X Y h hX => by rwa [← h.zcount_eq])
    _ fun e₀ he₀ h0 => ?_
  have hc := classSum_eq_zero p n e₀.shape h0 t hpt
  calc ∑ e ∈ ED n, (if Shape.Equiv e.shape e₀.shape then gfun δ p F t t k e else 0)
      = ∑ e ∈ ED n, ((cn δ n : ℝ) : ℂ) * (e₀.shape.netSign : ℂ) * (Mshape F e₀.shape k : ℂ) *
          (if Shape.Equiv e.shape e₀.shape then e.sw * (e.JB p t t : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [mem_ED] at he
        split_ifs with h
        · rw [gfun, he.2, h.netSign_eq, mshape_congr F h]; ring
        · simp
    _ = 0 := by rw [← Finset.mul_sum, ← classSum, hc, mul_zero]

/-- **DH23 Prop 6.2 / DH21 Props 7.9–7.10, B2.1 item (4) (regref1-5 corrected)**: for Schwartz input `F`,
`d ≥ 2` and `t ≥ p`, the leading terms of the well-formed dominant couple codes of order `2n` sum to the WKE
Taylor term `𝒰^{(p)}_n(t, k)`. -/
theorem wke_identity (hd : 2 ≤ d) (F : 𝓢(Mom d, ℝ)) (δ p : ℝ) (n : ℕ) {t : ℝ} (hpt : p ≤ t)
    (k : Mom d) :
    ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.dominant = true ∧ Q.size = 2 * n), Q.app δ p F t t k =
      (wkeTaylorTerm F δ p n t k : ℂ) := by
  rw [finsum_domCodes, sum_app_eq]
  have hsplit : ∀ e : ECpl, gfun δ p F t t k e = (if e.shape.zcount = 0 then gfun δ p F t t k e else 0) +
      (if e.shape.zcount ≠ 0 then gfun δ p F t t k e else 0) := by
    intro e; by_cases h : e.shape.zcount = 0 <;> simp [h]
  rw [Finset.sum_congr rfl fun e _ => hsplit e, Finset.sum_add_distrib, sum_zcount_ne_zero δ p F n hpt,
    add_zero, ← U_eq_wkeTaylorTerm δ p hd F n hpt, U_apply]
  push_cast
  refine Finset.sum_congr rfl fun e he => ?_
  rw [mem_ED] at he
  simp only [gfun, beta]
  split_ifs with h
  · rw [ECpl.sw_eq_one e h, MS_eq hd F _ h]; push_cast; ring
  · simp

/-- **B2.1 item (4)** in the form of `regularAsymptotics` (with `d ≥ 2`, which (Π) gives): for `r = p`,
`R_p = 0`, `F = φ(δp) + R_p` and `t ∈ [p, p+1]`, `∑ᶠ_{𝒬 dominant, n(𝒬)=2n} (K*_𝒬)_app(t,t,k) = 𝒰^{(p)}_n(t,k)`. -/
theorem regularAsymptotics_item4 (P : WTParams) (hd : 2 ≤ P.d) (p : ℕ) (R : Mom P.d → ℝ) (n : ℕ) :
    let F : Mom P.d → ℝ := fun k => P.φ (P.δ * p) k + R k
    (∀ k, R k = 0) → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
      ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.dominant = true ∧ Q.size = 2 * n),
          Q.app P.δ p F t t k =
        (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ) := by
  intro F hR t ht k
  have hF : F = ⇑(P.φ (P.δ * p)) := by funext k; simp [F, hR k]
  rw [hF]
  exact wke_identity hd (P.φ (P.δ * p)) P.δ p n ht.1 k

end WaveTurbulence.Mexp
