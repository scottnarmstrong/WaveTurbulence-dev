/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelAbs
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelLoc2

/-! # The induction for `hAbs` (V5 Step 4d part C)

`AbsLeaves`: the two leaf obligations (the S-side bound of the bundle `psiSB`, the base bound of `psiBase`).  `Lvl.absFuel`: under them
every level's summand `psiFuel` has a uniform `UAbs` bound and is jointly measurable.  `Lvl.hAbs_of_leaves`: the hypothesis `hAbs` of
`Lvl.classSum_flat`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The leaf obligations of `hAbs`: the S-side bound and measurability of the bundle at every split of every level, and the base bound and
measurability of the native summand of every level. -/
structure AbsLeaves (κ0 : KPar d) (hprime : IsPrimeGarden G) : Prop where
  sb : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), ∃ CS : ℝ, 0 ≤ CS ∧
    SAbs (lv.split B RD hG layer hLayer pstar hk).RS κ0.L κ0.base
      (psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime) CS
  sbm : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) x,
    Measurable (psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x)
  base : ∀ lv : Lvl B, ∃ C : ℝ, 0 ≤ C ∧ UAbs lv.region κ0.L κ0.base (lv.psiBase B RD hG layer hLayer κ0) C
  basem : ∀ lv : Lvl B, MeasT (lv.psiBase B RD hG layer hLayer κ0)
  bot : ∀ (lv : Lvl B) (pstar : lv.ι), (lv.e pstar).1.val = 0 →
    (∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j)) →
    ∃ C : ℝ, 0 ≤ C ∧ UAbs lv.region κ0.L κ0.base
      (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar) C
  botm : ∀ (lv : Lvl B) (pstar : lv.ι), (lv.e pstar).1.val = 0 →
    (∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j)) →
    MeasT (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar)

open Classical in
theorem Lvl.stepHyp (κ0 : KPar d) (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (m : ℕ)
    {CS CT : ℝ}
    (hS : SAbs (lv.split B RD hG layer hLayer pstar hk).RS κ0.L κ0.base
      (psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime) CS)
    (hmS : ∀ x, Measurable (psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x))
    (hT : UAbs (lv.next B RD hG layer hLayer pstar hk).region κ0.L κ0.base
      (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk)) CT)
    (hCT : 0 ≤ CT)
    (hTm : MeasT (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk))) :
    StepHyp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
      (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk))
      (CS := CS) (CT := CT) (lv.next B RD hG layer hLayer pstar hk).region where
  hlocS := fun x u u' hu => psiSB_congr (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x hu
  hlocT := fun x t' u u' hu =>
    Lvl.psiFuel_congr (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk) x t' hu
  hmS := hmS
  hm := hTm
  hS := hS
  hT := hT
  hCT := hCT


open Classical in
theorem Lvl.uAbs_step (κ0 : KPar d) (hL : κ0.L ≠ 0) (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι)
    (hk : 1 ≤ (lv.e pstar).1.val) (m : ℕ) {CS CT : ℝ}
    (H : StepHyp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
      (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk))
      (CS := CS) (CT := CT) (lv.next B RD hG layer hLayer pstar hk).region) :
    UAbs lv.region κ0.L κ0.base (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
      (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk))) (CS * CT) :=
  StepHyp.uAbs (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
    (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk)) lv.region hL H

open Classical in
theorem Lvl.measT_step (κ0 : KPar d) (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι)
    (hk : 1 ≤ (lv.e pstar).1.val) (m : ℕ)
    (hmS : ∀ x, Measurable (psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x))
    (hTm : MeasT (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk))) :
    MeasT (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
      (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk))) :=
  measT_psiStepSp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime _ hmS hTm

open Classical in
/-- Every level's summand has a uniform `UAbs` bound and is jointly measurable. -/
theorem Lvl.absFuel (κ0 : KPar d) (hL : κ0.L ≠ 0) (hprime : IsPrimeGarden G)
    (hl : AbsLeaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime) :
    ∀ (m : ℕ) (lv : Lvl B), (∃ C : ℝ, 0 ≤ C ∧
      UAbs lv.region κ0.L κ0.base (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv) C) ∧
      MeasT (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv) := by
  intro m
  induction m with
  | zero => intro lv; exact ⟨hl.base lv, hl.basem lv⟩
  | succ m ih =>
    intro lv
    by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
    · set pstar := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hpstar
      by_cases hk : 1 ≤ (lv.e pstar).1.val
      · have hfu : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv =
            Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
              (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk)) := by
          rw [Lvl.psiFuel, dif_pos hop]
          exact dif_pos hk
        rw [hfu]
        obtain ⟨⟨CT, hCT, hT⟩, hTm⟩ := ih (lv.next B RD hG layer hLayer pstar hk)
        obtain ⟨CS, hCS, hS⟩ := hl.sb lv pstar hk
        have H := Lvl.stepHyp (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime lv pstar hk m hS (hl.sbm lv pstar hk) hT hCT hTm
        refine ⟨⟨CS * CT, mul_nonneg hCS hCT, ?_⟩, ?_⟩
        · exact Lvl.uAbs_step (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hprime lv pstar hk m H
        · exact Lvl.measT_step (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime lv pstar hk m (hl.sbm lv pstar hk) hTm
      · have hfu : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar := by
          rw [Lvl.psiFuel, dif_pos hop]
          exact dif_neg hk
        rw [hfu]
        obtain ⟨hpop, hpmax⟩ := Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)
        have h0 : (lv.e pstar).1.val = 0 := by omega
        have hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
          intro j hjp
          refine ⟨fun op => hjp ?_⟩
          have h1 : (lv.e j).1.val ≤ (lv.e pstar).1.val := hpmax j ⟨op⟩
          have h2 : (lv.e j).1.val = (lv.e pstar).1.val := by omega
          exact lv.he (Subtype.ext (Fin.ext h2))
        exact ⟨hl.bot lv pstar h0 hup, hl.botm lv pstar h0 hup⟩
    · have hfu : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv = lv.psiBase B RD hG layer hLayer κ0 := by
        simp only [Lvl.psiFuel, hop, dite_false]
      rw [hfu]; exact ⟨hl.base lv, hl.basem lv⟩

open Classical in
/-- The hypothesis `hAbs` of `Lvl.classSum_flat` from the leaf obligations. -/
theorem Lvl.hAbs_of_leaves (κ0 : KPar d) (hL : κ0.L ≠ 0) (hprime : IsPrimeGarden G)
    (hl : AbsLeaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime) :
    ∀ (m : ℕ) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (t0 t1 t2 : ℝ) (e f g h : Mom d),
      GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS
        (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
        (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
          (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk))) := by
  intro m lv pstar hk t0 t1 t2 e f g h
  obtain ⟨⟨CT, hCT, hT⟩, hTm⟩ := Lvl.absFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hprime hl m (lv.next B RD hG layer hLayer pstar hk)
  obtain ⟨CS, hCS, hS⟩ := hl.sb lv pstar hk
  have H := Lvl.stepHyp (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime lv pstar hk m hS (hl.sbm lv pstar hk) hT hCT hTm
  exact StepHyp.glueAbsConv (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
    (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk)) hL H t0 t1 t2 e f g h

end WaveTurbulence.VineEstS5C
