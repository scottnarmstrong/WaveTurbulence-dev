/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Win

/-! # BOT-DECOMP: the expansion of `psiBot` into the pieces (a)-(c) and the remainder rows (mirror of `P4.BundleExp`)

`BotSepFam`: the separated expansions of the approximant families `botQfam`, `botTfam` at the two time points of the bottom bundle (input from P2's gates, as `P4.SepFam`).
`BotWin`: the window of the expansion (`botFrame = 0 ∨ (window ∧ PtOK)`); `botWin_holds`: it holds wherever the exterior clock `u c0.a` is in its layer window.
`botTerm c`: the summand `c ∈ Ch` as a function of the decoration, the exterior times `t` and the clocks `u` (carrying the factor `bFac` of the atom `b`);
`psiBot_eq_sum_terms`: `psiBot = ∑_c botTerm c` on the window.  `card_botCh`: the number of summands.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine
  WaveTurbulence.ConjCoh TTree WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C
open scoped ComplexConjugate

set_option linter.unusedSectionVars false

section
variable {w : ℕ} {ι : Type*} {d : ℕ} [Fintype ι] [DecidableEq ι] (p : ℕ) (kind : Bool) (pstar : ι)
  (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)

/-- The separated expansions of the approximants of the bottom bundle (input from P2/the gates). -/
structure BotSepFam (κ : KPar d) where
  S : SepTerms (BT w ι) d
  PtOK : ℝ → ℝ → ℝ → Prop
  hQ : ∀ t0 s1 t1, PtOK t0 s1 t1 → ∀ b, (b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) →
    (∀ k, botQfam pstar κ A b s1 t0 k = ∑ i, S.sQ b i s1 t0 k) ∧ ∀ k, botQfam pstar κ A b t1 t0 k = ∑ i, S.sQ b i t1 t0 k
  hT : ∀ t0 s1 t1, PtOK t0 s1 t1 → ∀ b, (b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) →
    (∀ k, botTfam pstar κ A b s1 t0 k = ∑ j, S.sT b j s1 t0 k) ∧ ∀ k, botTfam pstar κ A b t1 t0 k = ∑ j, S.sT b j t1 t0 k
  dom : ∀ (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ),
    DomF (layOf A) c0.U c0.a c0.b u →
    (layOf A c0.a : ℝ) < u c0.a → u c0.a < layOf A c0.a + 1 →
    PtOK (botVars κ A c0 pstar x u).1 (botVars κ A c0 pstar x u).2.1 (botVars κ A c0 pstar x u).2.2.1

variable {p kind pstar A c0}

theorem psiBot_eq_zero_of_botFrame (κ : KPar d) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    (u : GBranch A.skeleton.tree → ℝ) (h : botFrame κ A c0 pstar x u = 0) : psiBot p kind κ A c0 pstar x t u = 0 := by
  rw [psiBot_eq_dict, h, zero_mul, zero_mul]

variable (p kind pstar A c0)
open Classical in
/-- The window of the bottom bundle (see the module docstring). -/
def BotWin (κ : KPar d) (SF : BotSepFam p kind pstar A c0 κ)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ) : Prop :=
  botFrame κ A c0 pstar x u = 0 ∨
    ((if CaseA (pstar := pstar) A then
        (zpQ4 A pstar : ℝ) < (botVars κ A c0 pstar x u).2.2.1 ∧ (botVars κ A c0 pstar x u).2.2.1 ≤ zpQ4 A pstar + 1
      else
        (zpQ4 A pstar : ℝ) < (botVars κ A c0 pstar x u).2.1 ∧ (botVars κ A c0 pstar x u).2.1 ≤ zpQ4 A pstar + 1) ∧
      (zpQ2 A pstar : ℝ) ≤ (botVars κ A c0 pstar x u).1 ∧ (botVars κ A c0 pstar x u).1 ≤ zpQ2 A pstar + 1 ∧
      SF.PtOK (botVars κ A c0 pstar x u).1 (botVars κ A c0 pstar x u).2.1 (botVars κ A c0 pstar x u).2.2.1)

variable {p kind pstar A c0}

/-- **`BotWin` holds** wherever the exterior clock is in its window. -/
theorem botWin_holds (κ : KPar d) (SF : BotSepFam p kind pstar A c0 κ) (hb0 : c0.b = (A.family.placement pstar).lower)
    (hr : RetParent (pstar := pstar) A) (hq2 : zpQ2 A pstar ≤ layOf A (qrOf (A.family.placement pstar)))
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ)
    (hext : (layOf A c0.a : ℝ) < u c0.a ∧ u c0.a < layOf A c0.a + 1) :
    BotWin p kind pstar A c0 κ SF x u := by
  classical
  by_cases hf : botFrame κ A c0 pstar x u = 0
  · exact Or.inl hf
  · right
    have hD := domF_of_botFrame_ne A c0 κ x u hf
    have hP := SF.dom x u hD hext.1 hext.2
    by_cases hca : CaseA (pstar := pstar) A
    · obtain ⟨a1, a2, a3, a4⟩ := bot_window_caseA A c0 hb0 κ hr hq2 hca x u hD hext
      exact ⟨by rw [if_pos hca]; exact ⟨a1, a2⟩, a3, a4, hP⟩
    · have hM : CaseM (pstar := pstar) A := (caseA_or_caseM A).resolve_left hca
      obtain ⟨a1, a2, a3, a4⟩ := bot_window_caseM A c0 hb0 κ hr hq2 hM x u hD hext
      exact ⟨by rw [if_neg hca]; exact ⟨a1, a2⟩, a3, a4, hP⟩

variable (p kind pstar A c0)
open Classical in
/-- The summand `c` of the bottom bundle at the point `(t₀, s₁, t₁, x, y)`: the pieces (mirrored and conjugated in case M) and the remainder rows. -/
noncomputable def botPt (κ : KPar d) (SF : BotSepFam p kind pstar A c0 κ) (bs₁ bs₂ : Finset (BT w ι))
    (t0 s1 t1 : ℝ) (x y : Mom d) : Ch SF.S bs₁ bs₂ (botA p kind pstar A c0) (botB p kind pstar A c0) → ℂ :=
  Sum.elim (fun c => if CaseA (pstar := pstar) A then ptP SF.S bs₁ bs₂ t0 s1 t1 x y c
      else -(starRingEnd ℂ) (ptP SF.S bs₁ bs₂ t0 t1 s1 y x c))
    (fun c => ptR SF.S (botRemQ pstar κ (botQfam pstar κ A)) (botRemT pstar κ (botTfam pstar κ A))
      (botA p kind pstar A c0) (botB p kind pstar A c0) t0 s1 t1 x y c)

/-- The summand `c` of the bottom bundle as a function of the decoration, the exterior times and the clocks. -/
noncomputable def botTerm (κ : KPar d) (SF : BotSepFam p kind pstar A c0 κ) (bs₁ bs₂ : Finset (BT w ι))
    (c : Ch SF.S bs₁ bs₂ (botA p kind pstar A c0) (botB p kind pstar A c0))
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch A.skeleton.tree → ℝ) : ℂ :=
  botFrame κ A c0 pstar x u * bFac (botR A c0) κ.L κ.γ κ.δ κ.base x t u * ((nuOf A pstar : ℤˣ) : ℂ) *
    botPt p kind pstar A c0 κ SF bs₁ bs₂ (botVars κ A c0 pstar x u).1 (botVars κ A c0 pstar x u).2.1 (botVars κ A c0 pstar x u).2.2.1
      (botVars κ A c0 pstar x u).2.2.2.1 (botVars κ A c0 pstar x u).2.2.2.2 c

variable {p kind pstar A c0}

open Classical in
/-- **The bottom bundle is the sum of its summands** on the window. -/
theorem psiBot_eq_sum_terms (hR : P1.RealityAll) (hZ : BotSurj p kind pstar A c0) (hL : BotLayers p kind pstar A c0) (κ : KPar d)
    (SF : BotSepFam p kind pstar A c0 κ) (bs₁ bs₂ : Finset (BT w ι))
    (hc : (CaseA (pstar := pstar) A → bs₁ = botA p kind pstar A c0 ∧ bs₂ = botB p kind pstar A c0) ∧
      (¬ CaseA (pstar := pstar) A → bs₁ = botB p kind pstar A c0 ∧ bs₂ = botA p kind pstar A c0))
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch A.skeleton.tree → ℝ)
    (hW : BotWin p kind pstar A c0 κ SF x u) :
    psiBot p kind κ A c0 pstar x t u = ∑ c, botTerm p kind pstar A c0 κ SF bs₁ bs₂ c x t u := by
  classical
  have hsum : ∑ c, botTerm p kind pstar A c0 κ SF bs₁ bs₂ c x t u =
      botFrame κ A c0 pstar x u * bFac (botR A c0) κ.L κ.γ κ.δ κ.base x t u * (((nuOf A pstar : ℤˣ) : ℂ) *
      ∑ c, botPt p kind pstar A c0 κ SF bs₁ bs₂ (botVars κ A c0 pstar x u).1 (botVars κ A c0 pstar x u).2.1
        (botVars κ A c0 pstar x u).2.2.1 (botVars κ A c0 pstar x u).2.2.2.1 (botVars κ A c0 pstar x u).2.2.2.2 c) := by
    unfold botTerm
    rw [← Finset.mul_sum]; ring
  rcases hW with hf | ⟨hwin, h0, h0', hP⟩
  · rw [psiBot_eq_zero_of_botFrame κ x t u hf, hsum, hf, zero_mul, zero_mul]
  · generalize hv : botVars κ A c0 pstar x u = v at hP hwin h0 h0'
    have hq := SF.hQ _ _ _ hP
    have hT := SF.hT _ _ _ hP
    by_cases hca : CaseA (pstar := pstar) A
    · obtain ⟨e1, e2⟩ := hc.1 hca
      subst e1 e2
      rw [if_pos hca] at hwin
      rw [← hv] at hwin h0 h0'
      rw [bundle_decomp_bot hR hZ hL κ x t u hwin.1 hwin.2 h0 h0', hsum, hv]
      congr 2
      rw [Fintype.sum_sum_type]
      simp only [botPt, Sum.elim_inl, Sum.elim_inr, if_pos hca]
      rw [sum_ptP_eq SF.S (botQfam pstar κ A) (botTfam pstar κ A) (botA p kind pstar A c0) (botB p kind pstar A c0)
          v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 (fun b hb => hq b hb) (fun b hb => hT b hb),
        sum_ptR_eq SF.S (botQfam pstar κ A) (botTfam pstar κ A) (botRemQ pstar κ (botQfam pstar κ A))
          (botRemT pstar κ (botTfam pstar κ A)) (botA p kind pstar A c0) (botB p kind pstar A c0)
          v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 (fun b hb => hq b hb) (fun b hb => hT b hb)]
      rfl
    · obtain ⟨e1, e2⟩ := hc.2 hca
      subst e1 e2
      rw [if_neg hca] at hwin
      rw [← hv] at hwin h0 h0'
      rw [bundle_decomp_bot_mirror hR hZ hL κ x t u hwin.1 hwin.2 h0 h0', hsum, hv]
      congr 2
      rw [Fintype.sum_sum_type]
      simp only [botPt, Sum.elim_inl, Sum.elim_inr, if_neg hca, Finset.sum_neg_distrib, ← map_sum]
      rw [sum_ptP_eq SF.S (botQfam pstar κ A) (botTfam pstar κ A) (botB p kind pstar A c0) (botA p kind pstar A c0)
          v.1 v.2.2.1 v.2.1 v.2.2.2.2 v.2.2.2.1
          (fun b hb => ⟨(hq b hb.symm).2, (hq b hb.symm).1⟩) (fun b hb => ⟨(hT b hb.symm).2, (hT b hb.symm).1⟩),
        sum_ptR_eq SF.S (botQfam pstar κ A) (botTfam pstar κ A) (botRemQ pstar κ (botQfam pstar κ A))
          (botRemT pstar κ (botTfam pstar κ A)) (botA p kind pstar A c0) (botB p kind pstar A c0)
          v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 (fun b hb => hq b hb) (fun b hb => hT b hb)]
      rfl

open Classical in
/-- **The number of summands of the bottom bundle** (independent of the static case split):
`3 (∑_{botA} mQ mT + ∑_{botB} mQ mT) + ∑_{botA} (mQ + mT + 1) + ∑_{botB} (mQ + mT + 1)`. -/
theorem card_botCh (κ : KPar d) (SF : BotSepFam p kind pstar A c0 κ) :
    Fintype.card (Ch SF.S
        (if CaseA (pstar := pstar) A then botA p kind pstar A c0 else botB p kind pstar A c0)
        (if CaseA (pstar := pstar) A then botB p kind pstar A c0 else botA p kind pstar A c0)
        (botA p kind pstar A c0) (botB p kind pstar A c0)) =
      3 * ((∑ b ∈ botA p kind pstar A c0, SF.S.mQ b * SF.S.mT b) + ∑ b ∈ botB p kind pstar A c0, SF.S.mQ b * SF.S.mT b) +
        ((∑ b ∈ botA p kind pstar A c0, (SF.S.mQ b + SF.S.mT b + 1)) +
          ∑ b ∈ botB p kind pstar A c0, (SF.S.mQ b + SF.S.mT b + 1)) := by
  classical
  rw [card_ch]
  split_ifs <;> ring

end
end WaveTurbulence.VineEstS5C.P4.Bot
