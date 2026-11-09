/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcRec
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcInd
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RowNE
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcInd` (sha256 eaf0d401aabd9987…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (a): `rowFormNE_termsB` (the induction over the levels)

See `ExcRec` for the statement.  Generic in the bundle families `BE`, `BX` and in the explicit exceptional factors `XE`, `XB` with
`FrameShapeX`, `BotFrameShapeX` (for P4's `bundleFamOf` and BOT-DECOMP's `bundleBotFamOf`: module `ExcFam`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot

variable {w d : ℕ} {G : Garden w}

section LvlΓ
variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem lay_lvlΓ (lv : LvlΓ B) :
    (fun v : GBranch (lv.state B RD hG layer hLayer).skeleton.tree => stateLayer (lv.state B RD hG layer hLayer)
      ((lv.state B RD hG layer hLayer).data.coreBranch (lv.state B RD hG layer hLayer).plain v).toNode) =
      layC RD hG layer := by
  have h := stateLayer_lvlΓ B RD hG layer hLayer lv
  funext v
  change stateLayer (lv.state B RD hG layer hLayer) (RD.coreBranch hG v).toNode = layer (RD.coreBranch hG v).toNode
  rw [h]

variable {κ0 : KPar d}

theorem rowFormNE_lvlΓ (lv : LvlΓ B) {U' : Finset (GBranch G.tree)} {a' b' : GBranch G.tree} (R' : CLRegionData G U' a' b')
    (ψ : PsiT G d) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop) (Pex : Finset (SourcePair G)) (Bex : Finset (GBranch G.tree))
    (Xq : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (base : Mom d) :
    RowFormNE (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain L γ δ F
        (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) R' base ψ Dm Pex Bex Xq ↔
      RowFormNE RD hG L γ δ F layer hLayer R' base ψ Dm Pex Bex Xq := by
  unfold RowFormNE
  rw [qRow_lvlΓ B RD hG layer hLayer lv L γ δ F base, tRow_lvlΓ B RD hG layer hLayer lv L γ δ F base]
  exact Iff.rfl

variable {hprime : IsPrimeGarden G}
variable (BE : BundleExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (BX : BotExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0)

/-- The frame shape with an explicit exceptional factor: at operative members every bundle summand is the frame times `XE`. -/
def FrameShapeXΓ
    (XE : ∀ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), (BE lv pstar hk).Ch →
      (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) : Prop :=
  ∀ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar →
    ∀ (c : (BE lv pstar hk).Ch) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ),
      (BE lv pstar hk).term c x u =
        bundleFrame κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u * XE lv pstar hk c x u

/-- The bottom frame shape with an explicit exceptional factor. -/
def BotFrameShapeXΓ
    (XB : ∀ (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      (BX lv pstar h0 hop hmax).Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) : Prop :=
  ∀ (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (c : (BX lv pstar h0 hop hmax).Ch) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ),
    (BX lv pstar h0 hop hmax).term c x t u =
      botFrame κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u *
        bFac (botR (lv.state B RD hG layer hLayer) lv.c) κ0.L κ0.γ κ0.δ κ0.base x t u * XB lv pstar h0 hop hmax c x u

variable
  (XE : ∀ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), (BE lv pstar hk).Ch →
      (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
  (XB : ∀ (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      (BX lv pstar h0 hop hmax).Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)

/-- **A record comes from an operative member** of a level `lv'` whose realization nodes lie in those of `V`. -/
def ExcOfΓ (V : Finset (GBranch G.tree)) (r : ExcRec G d) : Prop :=
  (∃ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (_ : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (c : (BE lv pstar hk).Ch) (f : (GNode G.tree → (Fin d → ℤ)) → (GNode G.tree → (Fin d → ℤ))),
      (∀ y ∈ clRealizationNodes G lv.c.U, y ∈ clRealizationNodes G V) ∧
      (∀ x, ∀ y ∈ clRealizationNodes G lv.c.U, f x y = x y) ∧
      r.p0 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
        ((lv.state B RD hG layer hLayer).family.placement pstar).retained ∧
      r.bj = (lv.split B RD hG layer hLayer pstar hk).sb.b ∧ r.blk = (lv.e pstar).1.val ∧
      ∀ x u, r.X x u = XE lv pstar hk c (rA (lv.split B RD hG layer hLayer pstar hk).RS (f x)) u) ∨
    (∃ (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
      (c : (BX lv pstar h0 hop hmax).Ch) (f : (GNode G.tree → (Fin d → ℤ)) → (GNode G.tree → (Fin d → ℤ))),
      (∀ y ∈ clRealizationNodes G lv.c.U, y ∈ clRealizationNodes G V) ∧
      (∀ x, ∀ y ∈ clRealizationNodes G lv.c.U, f x y = x y) ∧
      r.p0 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
        ((lv.state B RD hG layer hLayer).family.placement pstar).retained ∧
      r.bj = lv.c.b ∧ r.blk = 0 ∧ ∀ x u, r.X x u = XB lv pstar h0 hop hmax c (f x) u)

/-- The statement proved by the induction over the levels. -/
def QNEΓ (lv : LvlΓ B) (ψ : PsiT G d) : Prop :=
  ∃ (recs : List (ExcRec G d)) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop),
    (∀ r ∈ recs, ExcOfΓ B RD hG layer hLayer BE BX XE XB lv.c.U r ∧ r.p0 ∈ clRegionalPairs hG lv.c.U ∧
      r.bj ∈ lv.c.U.erase lv.c.a) ∧
    (recs.map ExcRec.p0).Nodup ∧ (recs.map ExcRec.bj).Nodup ∧
    (∀ t u, u lv.c.a = t 0 → (Dm t u ↔ DomX lv.region (layC RD hG layer) (bexOf recs) (t 0) (t 1) (t 2) u)) ∧
    RowFormNE RD hG κ0.L κ0.γ κ0.δ κ0.F layer hLayer lv.region κ0.base ψ Dm (pexOf recs) (bexOf recs) (xqOf recs)

theorem qne_baseΓ (lv : LvlΓ B) :
    QNEΓ B RD hG layer hLayer BE BX XE XB lv (lv.psiBase B RD hG layer hLayer κ0) := by
  classical
  refine ⟨[], ClDom lv.region (layC RD hG layer), by simp, by simp, by simp, ?_, ?_⟩
  · intro t u _
    rw [bexOf_nil]
    exact (domX_empty lv.region (layC RD hG layer) t u).symm
  · rw [pexOf_nil, bexOf_nil]
    have h := rowForm_psiNat (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain lv.region
      κ0.L κ0.γ κ0.δ κ0.F (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer))
      κ0.base
    have hl := lay_lvlΓ B RD hG layer hLayer lv
    rw [hl] at h
    refine (rowFormNE_lvlΓ B RD hG layer hLayer lv lv.region _ _ _ _ _ κ0.L κ0.γ κ0.δ κ0.F κ0.base).mp ?_
    unfold RowFormNE
    exact rowForm_congr hG lv.region κ0.L κ0.γ κ0.δ κ0.base _ _ h (fun p _ t u x => (if_neg (Finset.notMem_empty p)).symm) (fun v _ t u x => (if_neg (Finset.notMem_empty v)).symm)

end LvlΓ

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
