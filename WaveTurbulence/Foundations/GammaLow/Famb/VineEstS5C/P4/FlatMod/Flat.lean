/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.BotSum
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelAbs3
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Flat
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelAbs3
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.FlatMod.FlatBase
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Flat` (sha256 0102ed8e6b4a0097…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # FLAT-MOD (R60), the modulated induction over the core vines

**`Lvl.classSumM_eq_flatM`** (F-W2-FLAT): for every level, the modulated class sum `Lvl.classSumM` (the member kernels with the
modulation `e^{πiλτ_b}` of `Cont.twistedRecenteredModC`) is `c ζ lkRaw (modPsi b λ (psiFuel ..))`: the flat identity of
`Lvl.classSum_eq_flat` with the modulation carried as the factor `e^{πiλ u_b}` of the summand (`b` the lower joint of the chain).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C
open WaveTurbulence.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
  WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont

section Glue
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b0 c : GBranch G.tree}

end Glue

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem LvlΓ.b_mem (lv : LvlΓ B) : b ∈ lv.c.U := by
  have := lv.c.block.2.2.1
  rw [lv.hcb] at this
  exact this

/-- **4d-B2 at a level, modulated.** -/
theorem LvlΓ.classSumM_bottom (lam : ℝ) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    LvlΓ.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (modPsi b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar))
          ![t0, t1, t2] ![e, f, g, h] := by
  refine (classSumM_bottom_state (p := p) (kind := kind) κ0 lam (lv.state B RD hG layer hLayer) lv.c hprime
    (LvlΓ.bottom_hb0 B RD hG layer hLayer lv pstar h0) hup hL hF t0 t1 t2 e f g h).trans ?_
  exact congrArg (fun z => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region * z)
    (lkRaw_modPsi lv.region lv.hcb lam κ0.L κ0.base _ ![t0, t1, t2] ![e, f, g, h]).symm

/-- **One level, flat form, modulated.** -/
theorem LvlΓ.classSumM_flat_step (lam : ℝ) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
      IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (Ψ' : PsiT G d)
    (hIH : ∀ (t0 t1 t2 : ℝ) (e f g h : Mom d),
      (lv.next B RD hG layer hLayer pstar hk).classSumM (p := p) (kind := kind) B RD hG layer hLayer lam κ0 t0 t1 t2 e f g h =
        (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (lv.next B RD hG layer hLayer pstar hk).region *
          clLocalZeta (lv.next B RD hG layer hLayer pstar hk).region *
          lkRaw (lv.next B RD hG layer hLayer pstar hk).region κ0.L κ0.base (modPsi b lam Ψ') ![t0, t1, t2] ![e, f, g, h])
    (hlocS : ∀ x (u u' : GBranch G.tree → ℝ), (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).sb.U, u v = u' v) →
      psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u =
        psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u')
    (hlocT : ∀ x t' (u u' : GBranch G.tree → ℝ), (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).tb.U, u v = u' v) →
      Ψ' x t' u = Ψ' x t' u')
    (t0 t1 t2 : ℝ) (e f g h : Mom d)
    (hAbs : GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS
      (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
      (LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ')) :
    LvlΓ.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (modPsi b lam (LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ'))
          ![t0, t1, t2] ![e, f, g, h] := by
  have hcomm : psiStepSp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
      (modPsi b lam Ψ') =
      modPsi b lam (LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ') := by
    funext x t u
    simp only [LvlΓ.psiStep, psiStepSp, modPsi]
    ring
  have hbT : b ∈ (lv.split B RD hG layer hLayer pstar hk).tb.U :=
    LvlΓ.b_mem B (lv.next B RD hG layer hLayer pstar hk)
  rw [LvlΓ.classSumM_nested (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hL hF hprime lv pstar hk hA0 t0 t1 t2 e f g h]
  have := flat_merge (p := p) (kind := kind) κ0 hL (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
    (modPsi b lam Ψ')
    (fun t E F' => (lv.next B RD hG layer hLayer pstar hk).classSumM (p := p) (kind := kind) B RD hG layer hLayer lam κ0 t t1 t2 E F' g h)
    (lv.next B RD hG layer hLayer pstar hk).region lv.region t0 t1 t2 e f g h
    (fun t E F' => hIH t t1 t2 E F' g h) hlocS
    (fun x t' u u' hu => by
      unfold modPsi
      rw [hu b hbT, hlocT x t' u u' hu])
    (by
      rw [hcomm]
      exact glueAbsConv_modPsi _ _ _ κ0.L κ0.base t0 t1 t2 e f g h _ hAbs b lam)
  rw [this, hcomm]
  rfl

open Classical in
/-- **The modulated induction over the core vines** (modulated `Lvl.classSum_flat`). -/
theorem LvlΓ.classSumM_flat (lam : ℝ) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G)
    (hlocS : ∀ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) x (u u' : GBranch G.tree → ℝ),
      (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).sb.U, u v = u' v) →
      psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u =
        psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u')
    (hlocPsi : ∀ (m : ℕ) (lv : LvlΓ B) x t (u u' : GBranch G.tree → ℝ), (∀ v ∈ lv.c.U, u v = u' v) →
      LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u =
        LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u')
    (hAbs : ∀ (m : ℕ) (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (t0 t1 t2 : ℝ) (e f g h : Mom d),
      GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS
        (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
        (LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
          (LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk)))) :
    ∀ (m : ℕ) (lv : LvlΓ B), Fintype.card lv.ι ≤ m → ∀ (t0 t1 t2 : ℝ) (e f g h : Mom d),
      LvlΓ.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
        (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
          lkRaw lv.region κ0.L κ0.base
            (modPsi b lam (LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv))
            ![t0, t1, t2] ![e, f, g, h] := by
  intro m
  induction m with
  | zero =>
    intro lv hc t0 t1 t2 e f g h
    have hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
      intro j
      have : Fintype.card lv.ι = 0 := Nat.le_zero.mp hc
      exact ((Fintype.card_eq_zero_iff.mp this).false j).elim
    have hnop : ¬ ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j := fun ⟨j, hj⟩ => (hno j).false hj.some
    rw [LvlΓ.classSumM_base (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hprime lv hno]
    simp only [LvlΓ.psiFuel, hnop, dite_false]
  | succ m ih =>
    intro lv hc t0 t1 t2 e f g h
    by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
    · obtain ⟨hpop, hpmax⟩ := Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)
      set pstar := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hpstar
      by_cases hk : 1 ≤ (lv.e pstar).1.val
      swap
      · have h0 : (lv.e pstar).1.val = 0 := by omega
        have hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
          intro j hjp
          refine ⟨fun op => hjp ?_⟩
          have h1 := hpmax j ⟨op⟩
          have h2 : (lv.e j).1.val = (lv.e pstar).1.val := by omega
          exact lv.he (Subtype.ext (Fin.ext h2))
        have hstep : LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1 + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar := by
          rw [LvlΓ.psiFuel, dif_pos hop]
          exact dif_neg hk
        rw [hstep]
        exact LvlΓ.classSumM_bottom (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hL hF hprime lv pstar h0 hup t0 t1 t2 e f g h
      have hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
          IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
        intro j hj hjp
        refine ⟨fun op => ?_⟩
        have h1 := hpmax j ⟨op⟩
        have h2 : (lv.e j).1.val = (lv.e pstar).1.val := le_antisymm h1 (not_lt.mp hj)
        exact hjp (lv.he (Subtype.ext (Fin.ext h2)))
      have hcard : Fintype.card (lv.next B RD hG layer hLayer pstar hk).ι ≤ m := by
        have := LvlΓ.card_next_lt B RD hG layer hLayer lv pstar hk
        omega
      have hIH := fun t0 t1 t2 e f g h => ih (lv.next B RD hG layer hLayer pstar hk) hcard t0 t1 t2 e f g h
      have hstep : LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1 + 1) lv =
          LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
            (LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) (lv.next B RD hG layer hLayer pstar hk)) := by
        rw [LvlΓ.psiFuel, dif_pos hop]
        exact dif_pos hk
      rw [hstep]
      exact LvlΓ.classSumM_flat_step (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hL hF hprime lv pstar hk hA0 _ hIH
        (hlocS lv pstar hk) (fun x t' u u' hu => hlocPsi (m + 1) (lv.next B RD hG layer hLayer pstar hk) x t' u u' hu)
        t0 t1 t2 e f g h (hAbs (m + 1) lv pstar hk t0 t1 t2 e f g h)
    · have hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) :=
        fun j => ⟨fun op => hop ⟨j, ⟨op⟩⟩⟩
      rw [LvlΓ.classSumM_base (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hprime lv hno]
      simp only [LvlΓ.psiFuel, hop, dite_false]

/-- **FLAT-MOD (F-W2-FLAT)**: the flat identity for the modulated kernel.  Every level's modulated class sum is `c ζ lkRaw` of
`e^{πiλ u_b} · psiFuel`. -/
theorem LvlΓ.classSumM_eq_flatM (lam : ℝ) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (hprime : IsPrimeGarden G)
    (lv : LvlΓ B) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    LvlΓ.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (modPsi b lam (LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card lv.ι + 1) lv))
          ![t0, t1, t2] ![e, f, g, h] :=
  LvlΓ.classSumM_flat (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hL hF hprime
    (fun lv pstar hk x u u' hu => psiSB_congr (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime x hu)
    (fun m lv x t u u' hu => LvlΓ.psiFuel_congr (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t hu)
    (LvlΓ.hAbs_of_leaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hprime (LvlΓ.absLeaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hF hprime))
    (Fintype.card lv.ι) lv le_rfl t0 t1 t2 e f g h

end WaveTurbulence.GammaLow.Famb.VineEstS5C
