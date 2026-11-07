/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelBundle

/-! # The bundle `psiSB` as the signed sum (replaceterm1) (V5 Step 4d part C, WP-B step 1)

`rowVal_dict`: for a state of lower-joint sign `νG` in the class of a state of sign `νA`, the signed exceptional factor
(`epsOf`, the clock and momentum slots exchanged iff twisted) is `νA` times `1_{t0<t1} Q(t0,s1,y) T(t1,t0,x)` (`νG = 1`,
Vine II-a) or `-νA` times `1_{t0<s1} Q(t1,t0,x) T(s1,t0,y)` (`νG = -1`, II-b), with the dictionary
`(t1,s1) = (cb,cr)`, `(x,y) = (low,ret)` for `νA = 1` and `(cr,cb)`, `(ret,low)` for `νA = -1` (`cb`, `cr` the clocks of the
parent of the lower joint and of the partner of the retained leaf).
`psiSB_eq_dict`: `psiSB = frame * νA * (∑_{II-a} a - ∑_{II-b} b)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

/-- The dictionary of the clocks `(t1, s1)` of TARGET (replaceterm1) in terms of the sign of `A`. -/
def dictT1 (νA : ℤˣ) (cb cr : ℝ) : ℝ := if νA = 1 then cb else cr
def dictS1 (νA : ℤˣ) (cb cr : ℝ) : ℝ := if νA = 1 then cr else cb
/-- The dictionary of the momenta `(x, y)`. -/
def dictX {d : ℕ} (νA : ℤˣ) (low ret : Mom d) : Mom d := if νA = 1 then low else ret
def dictY {d : ℕ} (νA : ℤˣ) (low ret : Mom d) : Mom d := if νA = 1 then ret else low

/-- The II-a term `1_{t0<t1} Q(t0,s1,y) T(t1,t0,x)` of a state. -/
noncomputable def termA {d : ℕ} (rq rt : ℝ → ℝ → Mom d → ℂ) (t0 s1 t1 : ℝ) (x y : Mom d) : ℂ :=
  open Classical in (if t0 < t1 then 1 else 0) * (rq t0 s1 y * rt t1 t0 x)

/-- The II-b term `1_{t0<s1} Q(t1,t0,x) T(s1,t0,y)` of a state. -/
noncomputable def termB {d : ℕ} (rq rt : ℝ → ℝ → Mom d → ℂ) (t0 s1 t1 : ℝ) (x y : Mom d) : ℂ :=
  open Classical in (if t0 < s1 then 1 else 0) * (rq t1 t0 x * rt s1 t0 y)

theorem rowVal_dict {d : ℕ} (νA νG : ℤˣ) (rq rt : ℝ → ℝ → Mom d → ℂ) (t0 cb cr : ℝ) (low ret : Mom d) :
    (if νG ≠ νA then (-1 : ℂ) else 1) *
      rowVal νG rq rt t0 (if νG ≠ νA then cr else cb) (if νG ≠ νA then cb else cr)
        (if νG ≠ νA then low else ret) (if νG ≠ νA then ret else low) =
    ((νA : ℤˣ) : ℂ) * (if νG = 1 then termA rq rt t0 (dictS1 νA cb cr) (dictT1 νA cb cr) (dictX νA low ret) (dictY νA low ret)
      else - termB rq rt t0 (dictS1 νA cb cr) (dictT1 νA cb cr) (dictX νA low ret) (dictY νA low ret)) := by
  classical
  rcases Int.units_eq_one_or νA with rfl | rfl <;> rcases Int.units_eq_one_or νG with rfl | rfl <;>
    simp [rowVal, termA, termB, dictS1, dictT1, dictX, dictY] <;> split_ifs <;> simp

section Bundle
variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} {J : Set ι} {d : ℕ} [Fintype ι] [DecidableEq ι]

/-- The frame of `A` (ordinary rows of the S-block), independent of the state `G` of the class. -/
noncomputable def bundleFrame (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ) : ℂ :=
  spartFrame A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base sp.sb.U sp.sb.a sp.sb.b
    (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) x u

/-- The clocks and momenta of the bundle: `(t0, s1, t1, x, y)` of (replaceterm1). -/
noncomputable def bundleVars (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ) : ℝ × ℝ × ℝ × Mom d × Mom d :=
  (u sp.sb.b,
    dictS1 (nuOf A pstar) (u (qbOf (A.family.placement pstar))) (u (qrOf (A.family.placement pstar))),
    dictT1 (nuOf A pstar) (u (qbOf (A.family.placement pstar))) (u (qrOf (A.family.placement pstar))),
    dictX (nuOf A pstar) (κ.base + latticePoint κ.L (x (A.family.placement pstar).lower.toNode))
      (κ.base + latticePoint κ.L (x (A.family.placement pstar).retained.toNode)),
    dictY (nuOf A pstar) (κ.base + latticePoint κ.L (x (A.family.placement pstar).lower.toNode))
      (κ.base + latticePoint κ.L (x (A.family.placement pstar).retained.toNode)))

open Classical in
/-- **The bundle is the signed sum of (replaceterm1).** -/
theorem psiSB_eq_dict (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ) :
    psiSB (p := p) (kind := kind) κ A sp0 hA x u = bundleFrame κ A sp0 x u * (((nuOf A pstar : ℤˣ) : ℂ) *
      ((∑ G ∈ (zpFinset p kind pstar J A sp0 hA).filter (fun G => nuOf G.1 pstar = 1),
          termA (rowQ κ G.1 pstar) (rowT κ G.1 pstar) (bundleVars κ A sp0 x u).1 (bundleVars κ A sp0 x u).2.1
            (bundleVars κ A sp0 x u).2.2.1 (bundleVars κ A sp0 x u).2.2.2.1 (bundleVars κ A sp0 x u).2.2.2.2) -
        ∑ G ∈ (zpFinset p kind pstar J A sp0 hA).filter (fun G => nuOf G.1 pstar ≠ 1),
          termB (rowQ κ G.1 pstar) (rowT κ G.1 pstar) (bundleVars κ A sp0 x u).1 (bundleVars κ A sp0 x u).2.1
            (bundleVars κ A sp0 x u).2.2.1 (bundleVars κ A sp0 x u).2.2.2.1 (bundleVars κ A sp0 x u).2.2.2.2)) := by
  have key : ∀ G ∈ zpFinset p kind pstar J A sp0 hA, epsOf A pstar G.1 *
      bundleKernel κ A sp0 (decide (twAt A G.1 pstar)) (nuOf G.1 pstar) (rowQ κ G.1 pstar) (rowT κ G.1 pstar) x u =
      bundleFrame κ A sp0 x u * (((nuOf A pstar : ℤˣ) : ℂ) *
        (if nuOf G.1 pstar = 1 then termA (rowQ κ G.1 pstar) (rowT κ G.1 pstar) (bundleVars κ A sp0 x u).1
            (bundleVars κ A sp0 x u).2.1 (bundleVars κ A sp0 x u).2.2.1 (bundleVars κ A sp0 x u).2.2.2.1
            (bundleVars κ A sp0 x u).2.2.2.2
          else - termB (rowQ κ G.1 pstar) (rowT κ G.1 pstar) (bundleVars κ A sp0 x u).1
            (bundleVars κ A sp0 x u).2.1 (bundleVars κ A sp0 x u).2.2.1 (bundleVars κ A sp0 x u).2.2.2.1
            (bundleVars κ A sp0 x u).2.2.2.2)) := by
    intro G _
    have hd := rowVal_dict (nuOf A pstar) (nuOf G.1 pstar) (rowQ κ G.1 pstar) (rowT κ G.1 pstar) (u sp0.sb.b)
      (u (qbOf (A.family.placement pstar))) (u (qrOf (A.family.placement pstar)))
      (κ.base + latticePoint κ.L (x (A.family.placement pstar).lower.toNode))
      (κ.base + latticePoint κ.L (x (A.family.placement pstar).retained.toNode))
    unfold epsOf bundleKernel bundleFrame bundleVars
    have e : twAt A G.1 pstar ↔ nuOf G.1 pstar ≠ nuOf A pstar := Iff.rfl
    simp only [e, decide_eq_true_eq]
    rw [mul_left_comm, mul_comm (spartFrame ..), ← hd]
    ring
  rw [psiSB, Finset.sum_congr rfl key, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 2
  rw [Finset.sum_ite, Finset.sum_neg_distrib, sub_eq_add_neg]

end Bundle
end WaveTurbulence.VineEstS5C
