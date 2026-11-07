/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcFam
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcSrc

/-! # P4-W2 (session 7, step 3k): the exceptional factor of a record as a bundle summand

`stepX_eq`: for an operative member of a level, the exceptional factor `stepX .. c` of a summand `c` of the bundle family, at the restricted decoration `rA RS (f x)` and the clock `u`, is
`ν · bundlePtG (CaseA A) S bs₁ bs₂ (bsA) (bsB) (remQ ..) (remT ..) t₀ s₁ t₁ x y (cast c)` with `t₀ = u b`, `s₁ = dictS1 ν (u qb) (u qr)`, `t₁ = dictT1 ν (u qb) (u qr)` and
`x = dictX ν low ret`, `y = dictY ν low ret` (the outer decoration, `exc_vars`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot

variable {w d : ℕ} {G : Garden w}
variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (hR : RealityAll) (SFF : SepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

open Classical in
theorem stepX_eq (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (c : (bundleFamOf B RD hG layer hLayer hR SFF lv pstar hk).Ch)
    (f : (GNode G.tree → (Fin d → ℤ)) → (GNode G.tree → (Fin d → ℤ)))
    (hf : ∀ x, ∀ y ∈ clRealizationNodes G lv.c.U, f x y = x y) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    stepX B RD hG layer hLayer hR SFF lv pstar hk c (rA (lv.split B RD hG layer hLayer pstar hk).RS (f x)) u =
      ((nuOf (lv.state B RD hG layer hLayer) pstar : ℤˣ) : ℂ) *
        bundlePtG (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) (SFF lv pstar hk hop).S
          (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then
            bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
            else bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
          (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then
            bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
            else bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
          (bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
          (bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
          (remQ κ0 (zpQfam κ0 (lv.state B RD hG layer hLayer))) (remT κ0 (zpTfam κ0 (lv.state B RD hG layer hLayer)))
          (u (lv.split B RD hG layer hLayer pstar hk).sb.b)
          (dictS1 (nuOf (lv.state B RD hG layer hLayer) pstar)
            (u (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar)))
            (u (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))))
          (dictT1 (nuOf (lv.state B RD hG layer hLayer) pstar)
            (u (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar)))
            (u (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))))
          (dictX (nuOf (lv.state B RD hG layer hLayer) pstar)
            (κ0.base + latticePoint κ0.L (x ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode))
            (κ0.base + latticePoint κ0.L (x ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode)))
          (dictY (nuOf (lv.state B RD hG layer hLayer) pstar)
            (κ0.base + latticePoint κ0.L (x ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode))
            (κ0.base + latticePoint κ0.L (x ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode)))
          (cast (congrArg BundleExp.Ch (bundleFamOf_eq_of_op B RD hG layer hLayer hR SFF lv pstar hk hop)) c) := by
  unfold stepX
  rw [dif_pos hop]
  have hv := exc_vars B RD hG layer hLayer lv pstar hk κ0 f hf x u
  erw [hv]
  rfl

end WaveTurbulence.VineEstS5C.P4.W2
