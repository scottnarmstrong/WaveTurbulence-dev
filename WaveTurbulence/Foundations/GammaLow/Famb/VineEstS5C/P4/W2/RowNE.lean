/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.GlueBot
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.WinChain
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowNE
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Bot.Unroll
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.WinChain
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowNE` (sha256 63e18b3adf28aac2…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (N1 → N2(b)): the native-except row form of every term

`RowFormNE RD … R ψ Dm Pex Bex Xq`: the row form of `ψ` on `R = (U, a, b)` whose weights are the NATIVE rows of the start data `RD`
(`qRow`/`tRow` with the layering `layer`, read at the exterior top clock `t 0`) at every pair outside `Pex` and every interior branch outside
`Bex`, the exceptional factor `Xq p` at the exceptional pairs `p ∈ Pex`, and `1` at the exceptional branches `v ∈ Bex`.

* `qRow_top`, `tRow_top`: the native rows of a region do not depend on the top clock (`cl_realization_parent`: realization nodes other than
  `a` are not roots).  `qRow_restrict`, `tRow_restrict`: they read the decoration only on the realization nodes.
* `stateLayer_lvl`: the layering of every level state is `layer` (`restrictState` keeps the data `RD`); `psiBase_eq`.
* `rowForm_congr`: the row form depends on the row weights only at the pairs and interior branches of the region.
* **`rowFormNE_termsB`**: every term of `Lvl.termsB` (BOT-DECOMP) has a native-except row form on its level's region, with `Pex ⊆` the
  pairs and `Bex ⊆` the interior branches; `Pex`, `Bex` collect the exceptional pair `p₀` and the lower joint `b` of every operative level
  (the split levels and the bottom level).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot

variable {w d : ℕ} {G : Garden w}

section Rows
variable (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
  {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

end Rows

section LvlΓ
variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The layering of every level state is the start layering. -/
theorem stateLayer_lvlΓ (lv : LvlΓ B) : stateLayer (lv.state B RD hG layer hLayer) = layer :=
  layeredReconstruction_inj RD hG (l₁ := stateLayer (lv.state B RD hG layer hLayer)) (l₂ := layer)
    (h₁ := stateLayer_isLayering (lv.state B RD hG layer hLayer)) (h₂ := hLayer) (stateLayer_spec (lv.state B RD hG layer hLayer))

theorem qRow_lvlΓ (lv : LvlΓ B) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) :
    qRow (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain L γ δ F
      (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) base =
    qRow RD hG L γ δ F layer hLayer base := by
  have h := stateLayer_lvlΓ B RD hG layer hLayer lv
  change qRow RD hG L γ δ F (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) base = _
  generalize stateLayer_isLayering (lv.state B RD hG layer hLayer) = hl
  revert hl
  rw [h]
  intro hl
  rfl

theorem tRow_lvlΓ (lv : LvlΓ B) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) :
    tRow (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain L γ δ F
      (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) base =
    tRow RD hG L γ δ F layer hLayer base := by
  have h := stateLayer_lvlΓ B RD hG layer hLayer lv
  change tRow RD hG L γ δ F (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) base = _
  generalize stateLayer_isLayering (lv.state B RD hG layer hLayer) = hl
  revert hl
  rw [h]
  intro hl
  rfl

end LvlΓ

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
