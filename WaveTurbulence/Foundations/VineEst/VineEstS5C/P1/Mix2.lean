/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P1.Mix

/-! # P1: `hQ0`, `hT0` (R35-repaired endpoint vanishing) and `hreal` (from `RealityAll` via `carrier_sum_eq`) -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P1
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.ConjCoh TTree
  WaveTurbulence.VineEstS4c

section
variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} {J : Set ι} {d : ℕ} [Fintype ι] [DecidableEq ι]
  (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)

/-- **`hQ0`** (R35 repair): for a state of `Zp(A)` whose carrier-side couple has root layer `> L₄`, the root-layer instance
vanishes at `t = Lq` (for every `s`): by `ZpLayers` the root layer exceeds `L₂`, so the couple is of type 2 with nonempty `+`
chain and the leading `∫_{Lr}^{t}` vanishes. -/
theorem zp_hQ0 (hZ : ZpSurj p kind pstar J A sp0 hA) (hL : ZpLayers p kind J A sp0 hA) (κ : KPar d) {b : ST w ι pstar J}
    (hb : b ∈ zpFinset p kind pstar J A sp0 hA) (hgt : zpQ4 A pstar < zpLq b) (s : ℝ) (k : Mom d) :
    zpQ0 κ A b (zpLq b : ℝ) s k = 0 := by
  obtain ⟨h2, hle, hp⟩ := hL.pair b hb
  have hc := (hZ.coherent b hb).1
  rw [h2] at hc hle
  exact couple_root_vanish κ.δ κ.F hle hp hc (lt_of_le_of_lt hL.le hgt) s k

/-- **`hT0`** (R35 repair), the tree analogue. -/
theorem zp_hT0 (hZ : ZpSurj p kind pstar J A sp0 hA) (hL : ZpLayers p kind J A sp0 hA) (κ : KPar d) {b : ST w ι pstar J}
    (hb : b ∈ zpFinset p kind pstar J A sp0 hA) (hgt : zpQ4 A pstar < zpLt b) (s : ℝ) (k : Mom d) :
    zpT0 κ A b (zpLt b : ℝ) s k = 0 := by
  obtain ⟨h2, hle⟩ := hL.branch b hb
  have hc := (hZ.coherent b hb).2
  rw [h2] at hc hle
  exact tree_root_vanish κ.δ κ.F hle hc (lt_of_le_of_lt hL.le hgt) s k

/-- On the carrier (II-b states with roots `≤ L₄`) the extension families are the source approximants at `(L₄, L₂)`
on the unit window `t ∈ [L₄, L₄+1]` (TARGET (i)). -/
theorem zp_ext_eq_source (hZ : ZpSurj p kind pstar J A sp0 hA) (hL : ZpLayers p kind J A sp0 hA) (κ : KPar d)
    {b : ST w ι pstar J} (hb : b ∈ zpMinusFin p kind pstar J A sp0 hA) {t : ℝ} (h1 : (zpQ4 A pstar : ℝ) ≤ t)
    (h2 : t ≤ zpQ4 A pstar + 1) (s : ℝ) (k : Mom d) :
    extFam zpLq (zpQ0 κ A) b t s k = SourceApp.couple κ.δ κ.F (zpObjC b.1 pstar) (zpCodeC b.1 pstar)
        (zpQ4 A pstar) (zpQ2 A pstar) t s k ∧
      extFam zpLt (zpT0 κ A) b t s k = SourceApp.tree κ.δ κ.F (zpObjT b.1 pstar) (zpCodeT b.1 pstar)
        (zpQ4 A pstar) (zpQ2 A pstar) t s k := by
  have hm : b ∈ zpSet p kind pstar J A sp0 hA (-1) := by rw [← coe_zpMinusFin p kind A sp0 hA]; exact hb
  obtain ⟨hcQ, hcT, -⟩ := hZ.carrier.mapsTo hm
  exact ⟨(couple_eq_ext κ.δ κ.F hL.le hL.le_p hcQ s k h1 h2).symm, (tree_eq_ext κ.δ κ.F hL.le hcT s k h1 h2).symm⟩

open Classical in
/-- **`hreal`** for the mixed families: from `RealityAll` (PL234 `reality_all`), `carrier_sum_eq` and the extension lemma.
Valid for `t₁ ∈ (L₄, L₄+1]`, `t₀ ∈ [L₂, L₂+1]`, `t₀ < t₁` (R35: only a.e.; at `t₁ = L₄` the exact trivial kernels vanish). -/
theorem zp_hreal (hR : RealityAll) (hZ : ZpSurj p kind pstar J A sp0 hA) (hL : ZpLayers p kind J A sp0 hA) (κ : KPar d)
    {t0 t1 : ℝ} (x : Mom d) (h1 : (zpQ4 A pstar : ℝ) < t1) (h1' : t1 ≤ zpQ4 A pstar + 1)
    (h0 : (zpQ2 A pstar : ℝ) ≤ t0) (h0' : t0 ≤ zpQ2 A pstar + 1) (hlt : t0 < t1) :
    (∑ b ∈ (zpBsU p kind J A sp0 hA).filter (fun b => zpLq b ≤ zpQ4 A pstar ∧ zpLt b ≤ zpQ4 A pstar),
      zpQfam κ A b t1 t0 x * (starRingEnd ℂ) (zpTfam κ A b t1 t0 x)).im = 0 := by
  have hext : (∑ b ∈ (zpBsU p kind J A sp0 hA).filter
        (fun b => zpLq b ≤ zpQ4 A pstar ∧ zpLt b ≤ zpQ4 A pstar),
      extFam zpLq (zpQ0 κ A) b t1 t0 x * (starRingEnd ℂ) (extFam zpLt (zpT0 κ A) b t1 t0 x)).im = 0 := by
    rw [zp_filter_eq A sp0 hA]
    have hr := hR κ.δ κ.F hL.le hL.le_p (zpN A pstar) (zpTop p A pstar) ![t1, t0]
      ⟨⟨⟨h1.le, h1'⟩, ⟨h0, h0'⟩⟩, by simpa using hlt⟩ x
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hr
    have hcs := carrier_sum_eq p A sp0 hA hZ.carrier
      (fun Q X LQ LX => SourceApp.couple κ.δ κ.F LQ Q (zpQ4 A pstar) (zpQ2 A pstar) t1 t0 x *
        star (SourceApp.tree κ.δ κ.F LX X (zpQ4 A pstar) (zpQ2 A pstar) t1 t0 x))
    beta_reduce at hcs
    rw [hcs] at hr
    have hsum : (∑ b ∈ zpMinusFin p kind pstar J A sp0 hA,
        extFam zpLq (zpQ0 κ A) b t1 t0 x * (starRingEnd ℂ) (extFam zpLt (zpT0 κ A) b t1 t0 x)) =
        ∑ b ∈ zpMinusFin p kind pstar J A sp0 hA,
          SourceApp.couple κ.δ κ.F (zpCarrierOf b.1 pstar).2.2.1 (zpCarrierOf b.1 pstar).1 (zpQ4 A pstar)
            (zpQ2 A pstar) t1 t0 x *
          star (SourceApp.tree κ.δ κ.F (zpCarrierOf b.1 pstar).2.2.2 (zpCarrierOf b.1 pstar).2.1 (zpQ4 A pstar)
            (zpQ2 A pstar) t1 t0 x) := by
      refine Finset.sum_congr rfl fun b hb => ?_
      have := zp_ext_eq_source A sp0 hA hZ hL κ hb h1.le h1' t0 x
      rw [this.1, this.2]
      rfl
    rw [hsum]
    exact hr
  refine hreal_mix_of_ext (zpBsU p kind J A sp0 hA) zpLq zpLt (zpQ4 A pstar) zpTrQ zpTrT
    (zpEx κ A) (zpEt κ A) (zpQ0 κ A) (zpT0 κ A) ?_ ?_ t0 t1 x h1 hext
  · intro b hb t ht s k
    simp [zpEx, ht]
  · intro b hb t ht s k
    simp [zpEt, ht]

end
end WaveTurbulence.VineEstS5C.P1
