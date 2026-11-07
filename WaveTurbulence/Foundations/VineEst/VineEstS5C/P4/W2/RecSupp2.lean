/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSupp
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBot

/-! # P4-W2 (session 18, step 1b): `supp_step`, `supp_bot`

`SuppConcl` for the exceptional factor of a step record and of a bottom record: a nonzero value forces the order conditions of the summand (`bundlePtG_eq_zero_of_not_excOrd`), and `suppConcl_of_core`
turns them into the statement about clocks.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open scoped ENNReal

variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar P.d}

section
variable {hprime : IsPrimeGarden G} (hR : RealityAll) (SFF : SepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

open Classical VineParamContract in
theorem supp_step (hM9 : VINEPARAM) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar) (c : (bundleFamOf B RD hG layer hLayer hR SFF lv pstar hk).Ch)
    (hreal : ∀ y ∈ clRealizationNodes G lv.c.U, y ∈ clRealizationNodes G U)
    (X : (GNode G.tree → (Fin P.d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
    (f : (GNode G.tree → (Fin P.d → ℤ)) → (GNode G.tree → (Fin P.d → ℤ)))
    (hf : ∀ x, ∀ y ∈ clRealizationNodes G lv.c.U, f x y = x y)
    (hrX : ∀ x u, X x u = stepX B RD hG layer hLayer hR SFF lv pstar hk c (rA (lv.split B RD hG layer hLayer pstar hk).RS (f x)) u) :
    SuppConcl B hM9 X (lv.split B RD hG layer hLayer pstar hk).sb.b
      (ordBad (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) (castCh B RD hG layer hLayer hR SFF lv pstar hk hop c))
          (recSlots hM9 B (lv.split B RD hG layer hLayer pstar hk).sb.b
            (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
            (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar)) ∨
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
          qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∧
          recKind (castCh B RD hG layer hLayer hR SFF lv pstar hk hop c) = 0))
      (ordPairs (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) (castCh B RD hG layer hLayer hR SFF lv pstar hk hop c))
          (recSlots hM9 B (lv.split B RD hG layer hLayer pstar hk).sb.b
            (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
            (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar))) := by
  obtain ⟨-, -, hqbU, hqrU⟩ := step_mem B RD hG layer hLayer lv pstar hk hreal
  refine suppConcl_of_core B hM9 hG _ (castCh B RD hG layer hLayer hR SFF lv pstar hk hop c) lv pstar _ ?_ hqbU hqrU X ?_
  · exact split_sb_b B RD hG layer hLayer lv pstar hk
  · intro x u hne
    by_contra hno
    apply hne
    rw [hrX, stepX_eq B RD hG layer hLayer hR SFF lv pstar hk hop c f hf]
    show ((nuOf (lv.state B RD hG layer hLayer) pstar : ℤˣ) : ℂ) * bundlePtG _ _ _ _ _ _ _ _ _ _ _ _ _
      (castCh B RD hG layer hLayer hR SFF lv pstar hk hop c) = 0
    exact mul_eq_zero_of_right _ (bundlePtG_eq_zero_of_not_excOrd _ _ _ _ _ _ _ _ _ _ _ _ _ _ hno)

end

section
variable {hprime' : IsPrimeGarden G} (hR : RealityAll) (BSFF : BotSepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0)

open Classical VineParamContract in
theorem supp_bot (hM9 : VINEPARAM) (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (c : (bundleBotFamOf B RD hG layer hLayer hprime' hR BSFF lv pstar h0 hop hmax).Ch)
    (hreal : ∀ y ∈ clRealizationNodes G lv.c.U, y ∈ clRealizationNodes G U)
    (X : (GNode G.tree → (Fin P.d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
    (f : (GNode G.tree → (Fin P.d → ℤ)) → (GNode G.tree → (Fin P.d → ℤ)))
    (hrX : ∀ x u, X x u = botX B RD hG layer hLayer hR hprime' BSFF lv pstar h0 hop hmax c (f x) u) :
    SuppConcl B hM9 X lv.c.b
      (ordBad (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) c)
          (recSlots hM9 B lv.c.b
            (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
            (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar)) ∨
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
          qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∧ recKind c = 0))
      (ordPairs (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) c)
          (recSlots hM9 B lv.c.b
            (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
            (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar))) := by
  set A := lv.state B RD hG layer hLayer with hA
  have hlowc : lv.c.b = (A.family.placement pstar).lower := Lvl.bottom_hb0 B RD hG layer hLayer lv pstar h0
  have key : ∀ v : GBranch G.tree, v ∈ lv.c.U → v ∈ U := fun v hv =>
    (branch_mem_clRealizationNodes v).mp (hreal _ ((branch_mem_clRealizationNodes v).mpr hv))
  have hqbU : qbOf (A.family.placement pstar) ∈ U := key _ (bot_qbOf_mem A lv.c hlowc)
  have hqrU : qrOf (A.family.placement pstar) ∈ U := key _ (bot_qrOf_mem A lv.c hlowc)
  refine suppConcl_of_core B hM9 hG _ c lv pstar _ ?_ hqbU hqrU X ?_
  · exact hlowc.trans (start_lower B RD hG layer hLayer (lv.e pstar))
  · intro x u hne
    by_contra hno
    apply hne
    rw [hrX, botX_eq B RD hG layer hLayer hR BSFF lv pstar h0 hop hmax c]
    exact mul_eq_zero_of_right _ (bundlePtG_eq_zero_of_not_excOrd _ _ _ _ _ _ _ _ _ _ _ _ _ _ hno)

end

end WaveTurbulence.VineEstS5C.P4.W2
