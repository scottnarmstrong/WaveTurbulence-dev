/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.GlueLvl
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Unroll
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Family

/-! # P4-W2 (N1 with the bottom bundle expanded): every term of `Lvl.termsB` has a row form

BOT-DECOMP (R60) expands the bottom bundle `psiBot` into the summands `BX.term c = botFrame · bFac · ν · botPt c`.  This module discharges the
former named input `hbot` of `rowForm_terms`:

* **`rowForm_bot`**: on a CL region `R = (U, a, b)`, `x t u ↦ spartFrame(U, a, b, p₀) x u · bFac R x t u · X x u` has a row form: the frame
  rows at the ordinary pairs and branches, the whole exceptional factor `X` at `p₀`, the weight `1` at `b`; the time condition is
  `DomF(U, a, b) ∧ bTimeOK R` (the boundary-child conditions `t' < u_b`, `t'' < u_b` of `bFac`); the sign and the phase of `b` (in `bFac`)
  complete those of `U ∖ {b}` (in the frame).
* `BotFrameShape BX`: every bottom summand is `botFrame · bFac · X`; **`botFrameShape_bundleBotFamOf`** (BOT-DECOMP's family).
* **`rowForm_termsB`**: by `Lvl.termsB_induction`, every term of `Lvl.termsB` has a row form on its level's region (no named input).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot

variable {w d : ℕ} {G : Garden w}

open Classical in
/-- **The row form of a bottom summand** (frame of the whole region, `b`-factor, exceptional factor `X`). -/
theorem rowForm_bot (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (p0 : SourcePair G) (hp0 : p0 ∈ clRegionalPairs hG U) (hb : b ∈ U.erase a)
    (X : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) :
    RowForm hG R L γ δ base
      (fun x t u => spartFrame D hG L γ δ F layer hLayer base U a b p0 x u * bFac R L γ δ base x t u * X x u)
      (fun t u => DomF (fun v => layer (D.coreBranch hG v).toNode) U a b u ∧ bTimeOK R t u)
      (fun p _ u x => if p = p0 then X x u else qRow D hG L γ δ F layer hLayer base (u a) x u p)
      (fun v _ u x => if v = b then 1 else tRow D hG L γ δ F layer hLayer base (u a) x u v) := by
  intro β' κ t u
  generalize clExtendIndices R κ.1 = x
  have hbU : b ∈ U := Finset.mem_of_mem_erase hb
  have heps : (clRegionalEpsilon G U x : ℂ) = (clRegionalEpsilon G (U.erase b) x : ℂ) * (epsBranch x b : ℂ) := by
    unfold clRegionalEpsilon
    rw [← Finset.prod_erase_mul _ _ hbU]
    push_cast
    ring
  have hph : clRegionalPhase G U L γ δ (cosetDecoration G L base x) u =
      clRegionalPhase G (U.erase b) L γ δ (cosetDecoration G L base x) u *
        phaseAtom L γ δ (G.sign b.toNode) (omegaNode G (cosetDecoration G L base x) b) (u b) := by
    unfold clRegionalPhase
    rw [← Finset.prod_erase_mul _ _ hbU]
  have hQ : ∏ p ∈ clRegionalPairs hG U, (if p = p0 then X x u else qRow D hG L γ δ F layer hLayer base (u a) x u p) =
      X x u * ∏ p ∈ (clRegionalPairs hG U).erase p0, qRow D hG L γ δ F layer hLayer base (u a) x u p := by
    rw [← Finset.mul_prod_erase _ _ hp0]
    simp only [ite_true]
    refine congrArg _ (Finset.prod_congr rfl fun p hp => ?_)
    simp only [Finset.ne_of_mem_erase hp, ite_false]
  have hT : ∏ v ∈ U.erase a, (if v = b then 1 else tRow D hG L γ δ F layer hLayer base (u a) x u v) =
      ∏ v ∈ (U.erase a).erase b, tRow D hG L γ δ F layer hLayer base (u a) x u v := by
    rw [← Finset.mul_prod_erase _ _ hb]
    simp only [ite_true, one_mul]
    refine Finset.prod_congr rfl fun v hv => ?_
    simp only [Finset.ne_of_mem_erase hv, ite_false]
  dsimp only
  rw [heps, hph, hQ, hT]
  unfold spartFrame bFac
  by_cases h1 : DomF (fun v => layer (D.coreBranch hG v).toNode) U a b u <;>
    by_cases h2 : bTimeOK R t u <;> simp only [h1, h2, ite_true, ite_false, and_true, and_false] <;> ring

variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (BX : BotExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0)

/-- At the bottom operative members every bottom summand is the frame times the `b`-factor times an exceptional factor. -/
def BotFrameShape : Prop :=
  ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
    ∃ X : (BX lv pstar h0 hop hmax).Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ,
      ∀ (c : (BX lv pstar h0 hop hmax).Ch) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ),
        (BX lv pstar h0 hop hmax).term c x t u =
          botFrame κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u *
            bFac (botR (lv.state B RD hG layer hLayer) lv.c) κ0.L κ0.γ κ0.δ κ0.base x t u * X c x u

open Classical in
/-- **BOT-DECOMP's bottom family has the frame shape** (`botTerm = botFrame · bFac · ν · botPt`). -/
theorem botFrameShape_bundleBotFamOf (hR : RealityAll) (SFF : BotSepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0) :
    BotFrameShape B RD hG layer hLayer (bundleBotFamOf B RD hG layer hLayer hprime hR SFF) := by
  intro lv pstar h0 hop hmax
  refine ⟨fun c x u => ((nuOf (lv.state B RD hG layer hLayer) pstar : ℤˣ) : ℂ) *
    botPt p kind pstar (lv.state B RD hG layer hLayer) lv.c κ0 (SFF lv pstar h0 hop hmax) _ _
      (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).1
      (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).2.1
      (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).2.2.1
      (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).2.2.2.1
      (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).2.2.2.2 c, fun c x t u => ?_⟩
  rw [bundleBotFamOf_term]
  unfold botTerm
  ring

/-- **The row form of every term with the bottom bundle expanded** (N1; no named input). -/
theorem rowForm_termsB (hL : κ0.L ≠ 0) (hX : FrameShape B RD hG layer hLayer BE) (hXB : BotFrameShape B RD hG layer hLayer BX) :
    ∀ (m : ℕ) (lv : Lvl B), ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX m lv,
      ∃ Dm Qw Tw, RowForm hG lv.region κ0.L κ0.γ κ0.δ κ0.base ψ Dm Qw Tw := by
  refine Lvl.termsB_induction B RD hG layer hLayer BE BX
    (fun lv ψ => ∃ Dm Qw Tw, RowForm hG lv.region κ0.L κ0.γ κ0.δ κ0.base ψ Dm Qw Tw) ?_ ?_ ?_
  · intro lv
    exact ⟨_, _, _, rowForm_psiNat (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain lv.region
      κ0.L κ0.γ κ0.δ κ0.F (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer))
      κ0.base⟩
  · intro lv pstar h0 hop hmax c
    obtain ⟨X, hXe⟩ := hXB lv pstar h0 hop hmax
    set A := lv.state B RD hG layer hLayer with hA
    have hSlow := chain_slow lv.c pstar (Lvl.bottom_hb0 B RD hG layer hLayer lv pstar h0)
    have hbot := rowForm_bot A.data A.plain κ0.L κ0.γ κ0.δ κ0.F (stateLayer A) (stateLayer_isLayering A) κ0.base
      (botR A lv.c) (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) hSlow.p0_mem hSlow.b_mem_erase
      (fun x u => X c x u)
    have hfun : (fun (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) =>
        (BX lv pstar h0 hop hmax).term c x t u) =
        fun (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) =>
          spartFrame A.data A.plain κ0.L κ0.γ κ0.δ κ0.F (stateLayer A) (stateLayer_isLayering A) κ0.base lv.c.U lv.c.a lv.c.b
            (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) x u *
            bFac (botR A lv.c) κ0.L κ0.γ κ0.δ κ0.base x t u * X c x u := by
      funext x t u
      rw [hXe c]
      rfl
    have hfin := rowForm_idx hG rfl rfl rfl (botR A lv.c) lv.region _ _ _ _ _ _ _ _ hbot
    exact ⟨_, _, _, Eq.mpr (congrArg (fun f => RowForm hG lv.region κ0.L κ0.γ κ0.δ κ0.base f _ _ _) hfun) hfin⟩
  · intro lv pstar hk hop _ c Ψ' ⟨Dm', Qw', Tw', hΨ⟩
    obtain ⟨X, hXe⟩ := hX lv pstar hk hop
    set A := lv.state B RD hG layer hLayer with hA
    set sp := lv.split B RD hG layer hLayer pstar hk with hsp
    have hT' : RowForm hG sp.RT κ0.L κ0.γ κ0.δ κ0.base Ψ' Dm' Qw' Tw' :=
      rowForm_idx hG rfl (lv.split B RD hG layer hLayer pstar hk).joint.symm rfl _ _ _ _ _ _ _ _ _ _ hΨ
    have hstep := rowForm_step sp.sb.block sp.hT sp.hi sp.hU A.data A.plain κ0.L κ0.γ κ0.δ hL κ0.F (stateLayer A)
      (stateLayer_isLayering A) κ0.base sp.RU sp.RS sp.RT (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)
      (SplitAt.slow sp).p0_mem (SplitAt.slow sp).b_mem_erase (fun x u => X c x u) Ψ' hT'
    have hfun : (fun (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) =>
        (BE lv pstar hk).term c (rA sp.RS x) u * Ψ' (rB sp.RT x) ![u sp.sb.b, t 1, t 2] u) =
        fun (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) =>
          spartFrame A.data A.plain κ0.L κ0.γ κ0.δ κ0.F (stateLayer A) (stateLayer_isLayering A) κ0.base sp.sb.U
            sp.sb.a sp.sb.b (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) (rA sp.RS x) u *
              X c (rA sp.RS x) u * Ψ' (rB sp.RT x) ![u sp.sb.b, t 1, t 2] u := by
      funext x t u
      rw [hXe c]
      rfl
    have hfin := rowForm_idx hG sp.union.symm sp.sa sp.tbb sp.RU lv.region _ _ _ _ _ _ _ _ hstep
    exact ⟨_, _, _, Eq.mpr (congrArg (fun f => RowForm hG lv.region κ0.L κ0.γ κ0.δ κ0.base f _ _ _) hfun) hfin⟩

end WaveTurbulence.VineEstS5C.P4.W2
