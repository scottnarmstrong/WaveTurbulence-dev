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
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
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

end WaveTurbulence.VineEstS5C.P4.W2
