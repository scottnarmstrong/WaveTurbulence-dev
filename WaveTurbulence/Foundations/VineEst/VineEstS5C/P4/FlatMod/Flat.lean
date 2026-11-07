/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.BotSum
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelAbs3

/-! # FLAT-MOD (R60), the modulated induction over the core vines

**`Lvl.classSumM_eq_flatM`** (F-W2-FLAT): for every level, the modulated class sum `Lvl.classSumM` (the member kernels with the
modulation `e^{πiλτ_b}` of `Cont.twistedRecenteredModC`) is `c ζ lkRaw (modPsi b λ (psiFuel ..))`: the flat identity of
`Lvl.classSum_eq_flat` with the modulation carried as the factor `e^{πiλ u_b}` of the summand (`b` the lower joint of the chain).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
  WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont

section Glue
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b0 c : GBranch G.tree}

theorem glueAbsConv_modPsi (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b0) (RT : CLRegionData G T b0 c)
    (L : ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f g h : Mom d) (ΨU : PsiT G d)
    (hΨ : GlueAbsConv RU RS RT L base t0 t1 t2 e f g h ΨU) (b : GBranch G.tree) (lam : ℝ) :
    GlueAbsConv RU RS RT L base t0 t1 t2 e f g h (modPsi b lam ΨU) := by
  have hm : Measurable fun τ : CLInternalTime RU =>
      Complex.exp (((Real.pi * lam * clLocalClock RU ![t0, t1, t2] τ b : ℝ) : ℂ) * Complex.I) :=
    Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (measurable_const.mul (measurable_clLocalClock RU _ b))).mul measurable_const)
  have hf : ∀ p τ, fGlue RU RS RT L base t0 t1 t2 e f g h (modPsi b lam ΨU) p τ =
      Complex.exp (((Real.pi * lam * clLocalClock RU ![t0, t1, t2] τ b : ℝ) : ℂ) * Complex.I) *
        fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ := fun p τ => rfl
  refine ⟨fun p => ?_, ?_⟩
  · have : fGlue RU RS RT L base t0 t1 t2 e f g h (modPsi b lam ΨU) p = fun τ =>
        Complex.exp (((Real.pi * lam * clLocalClock RU ![t0, t1, t2] τ b : ℝ) : ℂ) * Complex.I) *
          fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ := funext (hf p)
    rw [this]
    exact (hΨ.1 p).bdd_mul (c := 1) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => (Complex.norm_exp_ofReal_mul_I _).le)
  · refine hΨ.2.congr fun p => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    beta_reduce
    rw [hf p τ, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

end Glue

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem Lvl.b_mem (lv : Lvl B) : b ∈ lv.c.U := by
  have := lv.c.block.2.2.1
  rw [lv.hcb] at this
  exact this

/-- **4d-B2 at a level, modulated.** -/
theorem Lvl.classSumM_bottom (lam : ℝ) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    Lvl.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (modPsi b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar))
          ![t0, t1, t2] ![e, f, g, h] := by
  refine (classSumM_bottom_state (p := p) (kind := kind) κ0 lam (lv.state B RD hG layer hLayer) lv.c hprime
    (Lvl.bottom_hb0 B RD hG layer hLayer lv pstar h0) hup hL hF t0 t1 t2 e f g h).trans ?_
  exact congrArg (fun z => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region * z)
    (lkRaw_modPsi lv.region lv.hcb lam κ0.L κ0.base _ ![t0, t1, t2] ![e, f, g, h]).symm

/-- **One level, flat form, modulated.** -/
theorem Lvl.classSumM_flat_step (lam : ℝ) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
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
      (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ')) :
    Lvl.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (modPsi b lam (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ'))
          ![t0, t1, t2] ![e, f, g, h] := by
  have hcomm : psiStepSp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
      (modPsi b lam Ψ') =
      modPsi b lam (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ') := by
    funext x t u
    simp only [Lvl.psiStep, psiStepSp, modPsi]
    ring
  have hbT : b ∈ (lv.split B RD hG layer hLayer pstar hk).tb.U :=
    Lvl.b_mem B (lv.next B RD hG layer hLayer pstar hk)
  rw [Lvl.classSumM_nested (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hL hF hprime lv pstar hk hA0 t0 t1 t2 e f g h]
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
theorem Lvl.classSumM_flat (lam : ℝ) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G)
    (hlocS : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) x (u u' : GBranch G.tree → ℝ),
      (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).sb.U, u v = u' v) →
      psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u =
        psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u')
    (hlocPsi : ∀ (m : ℕ) (lv : Lvl B) x t (u u' : GBranch G.tree → ℝ), (∀ v ∈ lv.c.U, u v = u' v) →
      Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u =
        Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u')
    (hAbs : ∀ (m : ℕ) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (t0 t1 t2 : ℝ) (e f g h : Mom d),
      GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS
        (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
        (Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
          (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk)))) :
    ∀ (m : ℕ) (lv : Lvl B), Fintype.card lv.ι ≤ m → ∀ (t0 t1 t2 : ℝ) (e f g h : Mom d),
      Lvl.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
        (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
          lkRaw lv.region κ0.L κ0.base
            (modPsi b lam (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv))
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
    rw [Lvl.classSumM_base (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hprime lv hno]
    simp only [Lvl.psiFuel, hnop, dite_false]
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
        have hstep : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1 + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar := by
          rw [Lvl.psiFuel, dif_pos hop]
          exact dif_neg hk
        rw [hstep]
        exact Lvl.classSumM_bottom (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hL hF hprime lv pstar h0 hup t0 t1 t2 e f g h
      have hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
          IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
        intro j hj hjp
        refine ⟨fun op => ?_⟩
        have h1 := hpmax j ⟨op⟩
        have h2 : (lv.e j).1.val = (lv.e pstar).1.val := le_antisymm h1 (not_lt.mp hj)
        exact hjp (lv.he (Subtype.ext (Fin.ext h2)))
      have hcard : Fintype.card (lv.next B RD hG layer hLayer pstar hk).ι ≤ m := by
        have := Lvl.card_next_lt B RD hG layer hLayer lv pstar hk
        omega
      have hIH := fun t0 t1 t2 e f g h => ih (lv.next B RD hG layer hLayer pstar hk) hcard t0 t1 t2 e f g h
      have hstep : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1 + 1) lv =
          Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
            (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) (lv.next B RD hG layer hLayer pstar hk)) := by
        rw [Lvl.psiFuel, dif_pos hop]
        exact dif_pos hk
      rw [hstep]
      exact Lvl.classSumM_flat_step (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hL hF hprime lv pstar hk hA0 _ hIH
        (hlocS lv pstar hk) (fun x t' u u' hu => hlocPsi (m + 1) (lv.next B RD hG layer hLayer pstar hk) x t' u u' hu)
        t0 t1 t2 e f g h (hAbs (m + 1) lv pstar hk t0 t1 t2 e f g h)
    · have hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) :=
        fun j => ⟨fun op => hop ⟨j, ⟨op⟩⟩⟩
      rw [Lvl.classSumM_base (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hprime lv hno]
      simp only [Lvl.psiFuel, hop, dite_false]

/-- **FLAT-MOD (F-W2-FLAT)**: the flat identity for the modulated kernel.  Every level's modulated class sum is `c ζ lkRaw` of
`e^{πiλ u_b} · psiFuel`. -/
theorem Lvl.classSumM_eq_flatM (lam : ℝ) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (hprime : IsPrimeGarden G)
    (lv : Lvl B) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    Lvl.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (modPsi b lam (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card lv.ι + 1) lv))
          ![t0, t1, t2] ![e, f, g, h] :=
  Lvl.classSumM_flat (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hL hF hprime
    (fun lv pstar hk x u u' hu => psiSB_congr (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime x hu)
    (fun m lv x t u u' hu => Lvl.psiFuel_congr (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t hu)
    (Lvl.hAbs_of_leaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hprime (Lvl.absLeaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hF hprime))
    (Fintype.card lv.ι) lv le_rfl t0 t1 t2 e f g h

/-- λ = 0 reduces to `Lvl.classSum`: `classSumM 0 = classSum` (via `Cont.twistedRecenteredModC_zero`'s kernel identity). -/
theorem Lvl.classSumM_zero (κ0 : KPar d) (lv : Lvl B) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    Lvl.classSumM (p := p) (kind := kind) B RD hG layer hLayer 0 lv κ0 t0 t1 t2 e f g h =
      lv.classSum (p := p) (kind := kind) B RD hG layer hLayer κ0 t0 t1 t2 e f g h := by
  unfold Lvl.classSumM Lvl.classSum
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold twistedLocalKernelM twistedLocalKernel clLocalKernelModC clLocalKernel lowModC
  simp

end WaveTurbulence.VineEstS5C
