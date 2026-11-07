/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Mix

/-! # BOT-DECOMP: the bottom bundle `psiBot` as the signed sum of (replaceterm1) (mirror of `BundleAlg`, `bundle_eq_repl`)

`psiBot = botFrame * bFac * νA * (∑_{II-a} termA - ∑_{II-b} termB)` (`psiBot_eq_dict`), and, with approximants and remainders,
`psiBot = botFrame * bFac * νA * (replSum + remA-rows - remB-rows)` (`psiBot_eq_repl`).  The only differences with `psiSB`: the frame is that of the whole
chain region (`c0.U`, `c0.a`, `c0.b`), `t₀` is the clock `u c0.b` of the lower joint of `pstar` (`c0.b = lower`), and the factor `bFac` of the atom `b` multiplies.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine
  WaveTurbulence.ConjCoh TTree WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C

set_option linter.unusedSectionVars false

section
variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {d : ℕ} [Fintype ι] [DecidableEq ι]

/-- The frame of the chain region `c0` of `A` (ordinary rows of the region), independent of the state of the class. -/
noncomputable def botFrame (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) (pstar : ι)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ) : ℂ :=
  spartFrame A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base c0.U c0.a c0.b
    (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) x u

/-- The clocks and momenta of the bottom bundle: `(t₀, s₁, t₁, x, y)` of (replaceterm1), with `t₀ = u c0.b`. -/
noncomputable def botVars (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) (pstar : ι)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ) : ℝ × ℝ × ℝ × Mom d × Mom d :=
  (u c0.b,
    dictS1 (nuOf A pstar) (u (qbOf (A.family.placement pstar))) (u (qrOf (A.family.placement pstar))),
    dictT1 (nuOf A pstar) (u (qbOf (A.family.placement pstar))) (u (qrOf (A.family.placement pstar))),
    dictX (nuOf A pstar) (κ.base + latticePoint κ.L (x (A.family.placement pstar).lower.toNode))
      (κ.base + latticePoint κ.L (x (A.family.placement pstar).retained.toNode)),
    dictY (nuOf A pstar) (κ.base + latticePoint κ.L (x (A.family.placement pstar).lower.toNode))
      (κ.base + latticePoint κ.L (x (A.family.placement pstar).retained.toNode)))

open Classical in
/-- **The bottom bundle is the signed sum of (replaceterm1).** -/
theorem psiBot_eq_dict (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) (pstar : ι)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch A.skeleton.tree → ℝ) :
    psiBot p kind κ A c0 pstar x t u = botFrame κ A c0 pstar x u * bFac (botR A c0) κ.L κ.γ κ.δ κ.base x t u *
      (((nuOf A pstar : ℤˣ) : ℂ) *
      ((∑ G ∈ (canonFinsetK p kind A c0).filter (fun G => nuOf G.1 pstar = 1),
          termA (rowQ κ G.1 pstar) (rowT κ G.1 pstar) (botVars κ A c0 pstar x u).1 (botVars κ A c0 pstar x u).2.1
            (botVars κ A c0 pstar x u).2.2.1 (botVars κ A c0 pstar x u).2.2.2.1 (botVars κ A c0 pstar x u).2.2.2.2) -
        ∑ G ∈ (canonFinsetK p kind A c0).filter (fun G => nuOf G.1 pstar ≠ 1),
          termB (rowQ κ G.1 pstar) (rowT κ G.1 pstar) (botVars κ A c0 pstar x u).1 (botVars κ A c0 pstar x u).2.1
            (botVars κ A c0 pstar x u).2.2.1 (botVars κ A c0 pstar x u).2.2.2.1 (botVars κ A c0 pstar x u).2.2.2.2)) := by
  have key : ∀ G ∈ canonFinsetK p kind A c0, stBot κ A c0 pstar G.1 x t u =
      botFrame κ A c0 pstar x u * bFac (botR A c0) κ.L κ.γ κ.δ κ.base x t u * (((nuOf A pstar : ℤˣ) : ℂ) *
        (if nuOf G.1 pstar = 1 then termA (rowQ κ G.1 pstar) (rowT κ G.1 pstar) (botVars κ A c0 pstar x u).1
            (botVars κ A c0 pstar x u).2.1 (botVars κ A c0 pstar x u).2.2.1 (botVars κ A c0 pstar x u).2.2.2.1
            (botVars κ A c0 pstar x u).2.2.2.2
          else - termB (rowQ κ G.1 pstar) (rowT κ G.1 pstar) (botVars κ A c0 pstar x u).1
            (botVars κ A c0 pstar x u).2.1 (botVars κ A c0 pstar x u).2.2.1 (botVars κ A c0 pstar x u).2.2.2.1
            (botVars κ A c0 pstar x u).2.2.2.2)) := by
    intro G _
    have hd := rowVal_dict (nuOf A pstar) (nuOf G.1 pstar) (rowQ κ G.1 pstar) (rowT κ G.1 pstar) (u c0.b)
      (u (qbOf (A.family.placement pstar))) (u (qrOf (A.family.placement pstar)))
      (κ.base + latticePoint κ.L (x (A.family.placement pstar).lower.toNode))
      (κ.base + latticePoint κ.L (x (A.family.placement pstar).retained.toNode))
    unfold stBot epsOf botKernel botFrame botVars
    have e : twAt A G.1 pstar ↔ nuOf G.1 pstar ≠ nuOf A pstar := Iff.rfl
    simp only [e, decide_eq_true_eq]
    rw [← hd]
    ring
  unfold psiBot
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 2
  rw [Finset.sum_ite, Finset.sum_neg_distrib, sub_eq_add_neg]

variable (p kind) in
open Classical in
/-- **The bottom bundle in the pairing form** (TARGET (replaceterm1) with the remainder rows):
`psiBot = frame * bFac * νA * (replSum approximants + ∑ remA - ∑ remB)`. -/
theorem psiBot_eq_repl (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) (pstar : ι)
    (Qf Tf : BT w ι → ℝ → ℝ → Mom d → ℂ) (τ : BT w ι → BT w ι)
    (hbij : Set.BijOn τ (botSet p kind pstar A c0 (-1)) (botSet p kind pstar A c0 1))
    (hrel : ∀ G ∈ botSet p kind pstar A c0 (-1),
      IsConjugateCouple (sigStar G.1 pstar).2.1 (sigStar (τ G).1 pstar).2.1 ∧
      IsConjugateTree (sigStar G.1 pstar).2.2 (sigStar (τ G).1 pstar).2.2)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch A.skeleton.tree → ℝ) :
    psiBot p kind κ A c0 pstar x t u = botFrame κ A c0 pstar x u * bFac (botR A c0) κ.L κ.γ κ.δ κ.base x t u *
      (((nuOf A pstar : ℤˣ) : ℂ) *
      (replSum (botA p kind pstar A c0) (botB p kind pstar A c0) (Qf) (cswap (Qf)) (Tf) (cconj (Tf))
          (botVars κ A c0 pstar x u).1 (botVars κ A c0 pstar x u).2.1 (botVars κ A c0 pstar x u).2.2.1
          (botVars κ A c0 pstar x u).2.2.2.1 (botVars κ A c0 pstar x u).2.2.2.2 +
        (∑ b ∈ botA p kind pstar A c0, remA (Qf) (Tf) (botRemQ pstar κ Qf) (botRemT pstar κ Tf) b
            (botVars κ A c0 pstar x u).1 (botVars κ A c0 pstar x u).2.1 (botVars κ A c0 pstar x u).2.2.1
            (botVars κ A c0 pstar x u).2.2.2.1 (botVars κ A c0 pstar x u).2.2.2.2 -
          ∑ b ∈ botB p kind pstar A c0, remB (Qf) (Tf) (botRemQ pstar κ Qf) (botRemT pstar κ Tf) b
            (botVars κ A c0 pstar x u).1 (botVars κ A c0 pstar x u).2.1 (botVars κ A c0 pstar x u).2.2.1
            (botVars κ A c0 pstar x u).2.2.2.1 (botVars κ A c0 pstar x u).2.2.2.2))) := by
  rw [psiBot_eq_dict]
  congr 2
  rw [← sum_botA_reindex p kind pstar A c0 τ hbij, ← exact_eq_repl_add_rem]
  congr 1
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hb' := Finset.mem_filter.mp hb
    have hr1 : (nuOf b.1 pstar = 1) ∨ (nuOf b.1 pstar ≠ 1 ∧
        IsConjugateCouple (sigStar b.1 pstar).2.1 (sigStar (τ b).1 pstar).2.1) := by
      rcases hb'.2 with ⟨hn, hr⟩ | ⟨hn, _⟩
      · exact Or.inr ⟨hn, (hrel b ⟨hb'.1, (units_ne_one_iff _).mp hn, hr⟩).1⟩
      · exact Or.inl hn
    have hr2 : (nuOf b.1 pstar = 1) ∨ (nuOf b.1 pstar ≠ 1 ∧
        IsConjugateTree (sigStar b.1 pstar).2.2 (sigStar (τ b).1 pstar).2.2) := by
      rcases hb'.2 with ⟨hn, hr⟩ | ⟨hn, _⟩
      · exact Or.inr ⟨hn, (hrel b ⟨hb'.1, (units_ne_one_iff _).mp hn, hr⟩).2⟩
      · exact Or.inl hn
    have e1 : rowQ κ (botSigma pstar τ b).1 pstar =
        fun t s k => cswap (Qf) b t s k + (starRingEnd ℂ) (botRemQ pstar κ Qf b s t k) :=
      funext fun t => funext fun s => funext fun k => botRowQ_A pstar κ Qf τ hr1 t s k
    have e2 : rowT κ (botSigma pstar τ b).1 pstar = fun t s k => Tf b t s k + botRemT pstar κ Tf b t s k :=
      funext fun t => funext fun s => funext fun k => botRowT_A pstar κ Tf τ hr2 t s k
    rw [e1, e2]
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hb' : b ∈ botB p kind pstar A c0 := hb
    have hn : nuOf b.1 pstar ≠ 1 := (Finset.mem_filter.mp hb').2
    have e1 : rowQ κ b.1 pstar = fun t s k => Qf b t s k + botRemQ pstar κ Qf b t s k :=
      funext fun t => funext fun s => funext fun k => botRowQ_B pstar κ Qf b hn t s k
    have e2 : rowT κ b.1 pstar = fun t s k => cconj (Tf) b t s k + (starRingEnd ℂ) (botRemT pstar κ Tf b t s k) :=
      funext fun t => funext fun s => funext fun k => botRowT_B pstar κ Tf b hn t s k
    rw [e1, e2]

end
end WaveTurbulence.VineEstS5C.P4.Bot
