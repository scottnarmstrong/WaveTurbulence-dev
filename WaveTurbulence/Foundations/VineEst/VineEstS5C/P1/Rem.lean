/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P1.Decomp

/-! # P1 helper for P2: the remainders are the gate remainders `K* - SourceApp` in the native window

`zp_Qf_eq_srcQ`, `zp_Tf_eq_srcT`: on the native unit window `t ∈ [q, q+1]` (`q` the first parent layer of the carrier-side object,
`zpQQ` for couples, `zpBranchQ` for trees) the approximant `Qf`/`Tf` (constant extension of the root-layer instance) is the source
approximant `srcQ`/`srcT` at the native parameters, away from the single time `t = Lr` of a trivial object (R35: there the
exact trivial kernel is `F · 1_{t > Lr}`).  `zp_remQ_eq`, `zp_remT_eq`: hence `remQ`, `remT` are exactly the gate remainders
`KQstar - SourceApp.couple`, `KTstar - SourceApp.tree` bounded by `CoherentGateH` (`GateH.lean`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P1
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.ConjCoh TTree
  WaveTurbulence.VineEstS4c

section
variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} {J : Set ι} {d : ℕ} [Fintype ι] [DecidableEq ι]
  (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)

theorem zp_Qf_eq_srcQ (hZ : ZpSurj p kind pstar J A sp0 hA) (hL : ZpLayers p kind J A sp0 hA) (κ : KPar d)
    {b : ST w ι pstar J} (hb : b ∈ zpFinset p kind pstar J A sp0 hA) {t : ℝ}
    (h1 : ((zpQQ b.1 pstar).1 : ℝ) ≤ t) (h2 : t ≤ (zpQQ b.1 pstar).1 + 1)
    (hne : (zpLq b : ℝ) < t ∨ ¬ zpTrQ b) (s : ℝ) (k : Mom d) :
    zpQfam κ A b t s k = srcQ κ b t s k := by
  obtain ⟨h2', hle, hp⟩ := hL.pair b hb
  have hc := (hZ.coherent b hb).1
  rw [h2'] at hc hle
  have hext := couple_eq_ext κ.δ κ.F hle hp hc s k h1 h2
  have hq : zpQfam κ A b t s k = extFam zpLq (zpQ0 κ A) b t s k := by
    unfold zpQfam
    rcases hne with hlt | hn
    · exact mixFam_eq_extFam_of_lt (fun b _ t ht s k => by simp [zpEx, ht]) hlt s k
    · exact mixFam_of_not hn t s k
  rw [hq]
  unfold srcQ
  rw [h2']
  exact hext.symm

theorem zp_Tf_eq_srcT (hZ : ZpSurj p kind pstar J A sp0 hA) (hL : ZpLayers p kind J A sp0 hA) (κ : KPar d)
    {b : ST w ι pstar J} (hb : b ∈ zpFinset p kind pstar J A sp0 hA) {t : ℝ}
    (h1 : ((zpBranchQ b.1 pstar).1 : ℝ) ≤ t) (h2 : t ≤ (zpBranchQ b.1 pstar).1 + 1)
    (hne : (zpLt b : ℝ) < t ∨ ¬ zpTrT b) (s : ℝ) (k : Mom d) :
    zpTfam κ A b t s k = srcT κ b t s k := by
  obtain ⟨h2', hle⟩ := hL.branch b hb
  have hc := (hZ.coherent b hb).2
  rw [h2'] at hc hle
  have hext := tree_eq_ext κ.δ κ.F hle hc s k h1 h2
  have hq : zpTfam κ A b t s k = extFam zpLt (zpT0 κ A) b t s k := by
    unfold zpTfam
    rcases hne with hlt | hn
    · exact mixFam_eq_extFam_of_lt (fun b _ t ht s k => by simp [zpEt, ht]) hlt s k
    · exact mixFam_of_not hn t s k
  rw [hq]
  unfold srcT
  rw [h2']
  exact hext.symm

/-- **The couple remainder in the native window is the gate remainder `K* - SourceApp`.** -/
theorem zp_remQ_eq (hZ : ZpSurj p kind pstar J A sp0 hA) (hL : ZpLayers p kind J A sp0 hA) (κ : KPar d)
    {b : ST w ι pstar J} (hb : b ∈ zpFinset p kind pstar J A sp0 hA) {t : ℝ}
    (h1 : ((zpQQ b.1 pstar).1 : ℝ) ≤ t) (h2 : t ≤ (zpQQ b.1 pstar).1 + 1)
    (hne : (zpLq b : ℝ) < t ∨ ¬ zpTrQ b) (s : ℝ) (k : Mom d) :
    remQ κ (zpQfam κ A) b t s k = KQstar κ.L κ.γ κ.δ κ.F (zpObjC b.1 pstar) t s k - srcQ κ b t s k := by
  unfold remQ
  rw [zp_Qf_eq_srcQ A sp0 hA hZ hL κ hb h1 h2 hne]

/-- **The tree remainder in the native window is the gate remainder `K* - SourceApp`.** -/
theorem zp_remT_eq (hZ : ZpSurj p kind pstar J A sp0 hA) (hL : ZpLayers p kind J A sp0 hA) (κ : KPar d)
    {b : ST w ι pstar J} (hb : b ∈ zpFinset p kind pstar J A sp0 hA) {t : ℝ}
    (h1 : ((zpBranchQ b.1 pstar).1 : ℝ) ≤ t) (h2 : t ≤ (zpBranchQ b.1 pstar).1 + 1)
    (hne : (zpLt b : ℝ) < t ∨ ¬ zpTrT b) (s : ℝ) (k : Mom d) :
    remT κ (zpTfam κ A) b t s k = KTstar κ.L κ.γ κ.δ κ.F (zpObjT b.1 pstar) t s k - srcT κ b t s k := by
  unfold remT
  rw [zp_Tf_eq_srcT A sp0 hA hZ hL κ hb h1 h2 hne]

end
end WaveTurbulence.VineEstS5C.P1
