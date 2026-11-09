/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcMom2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcFam
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BadCount
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseA
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeo
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W13.BadCount
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.ExcFam
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeo` (sha256 6ce64bfa5e6ce76b…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (b1): the geometry of an exceptional record

For a record coming from the operative member `pstar` of a level `lv` (first disjunct of `ExcOf`), with the split `sp = lv.split ..` and the
placement `P`:

* `split_sb_b`: the lower joint of the upper block `sp.sb` is the lower joint `(assemblyPieceAt B i).lower` of the piece `i = (lv.e pstar).1`;
* `clock_lower_piece`: its clock is the sumint clock `t₀ⁱ = τ (.inl ⟨i, 0⟩)`;
* `brSlot`, `brSlot_spec`: the clock of ANY branch of the region is `τ` of a sumint clock, or the exterior clock `t 0` (the top joint);
* `exc_low_ret_eps`: `low = ret + ε r` with `|ε| = 1` and `r = E₀ - E₁` (momentum conservation at the lower joint);
* `rA_lower`, `rA_retained`, `exc_vars`: `bundleVars` at `rA RS (f x)` is `bundleVars`-like data of the OUTER decoration `x`;
* `lower_real_c`, `retained_real_c`: the lower joint and the retained leaf lie in the realization of `lv.c.U`.
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
open VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13

variable {w d : ℕ}

section Gap

end Gap

section Clock
variable {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)

open Classical in
/-- The slot (sumint clock or exterior clock) of a branch of the region. -/
noncomputable def brSlotΓ (v : GBranch G.tree) : (assemblyShapeΓ hM9 B).TVar ⊕ Fin 3 :=
  if h : v ∈ clInteriorBranches R then Sum.inl (branchSlotΓ hM9 B ⟨v, h⟩) else Sum.inr 0

/-- **The clock of any branch of the region** is the sumint clock of its slot, or the exterior clock `t 0` (for the top joint). -/
theorem brSlot_specΓ {v : GBranch G.tree} (hv : v ∈ U) (tt : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) :
    clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) v = Sum.elim τ tt (brSlotΓ hM9 B v) := by
  classical
  by_cases hva : v = a
  · subst hva
    have hn : v ∉ clInteriorBranches R := fun h => (Finset.mem_erase.mp h).1 rfl
    simp only [brSlotΓ, dif_neg hn, Sum.elim_inr]
    exact clLocalClock_upper R tt _
  · have hi : v ∈ clInteriorBranches R := Finset.mem_erase.mpr ⟨hva, hv⟩
    simp only [brSlotΓ, dif_pos hi, Sum.elim_inl]
    exact branchSlot_specΓ hM9 B ⟨v, hi⟩ tt τ

end Clock

section Split
variable {ι : Type*} {pstar : ι} {J : Set ι}

end Split

section Vars
variable {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **`bundleVars` at the restricted decoration** `rA RS (f x)` is the data of the outer decoration `x`: the lower joint and the retained leaf carry the
outer labels. -/
theorem exc_varsΓ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (κ0 : KPar d)
    (f : (GNode G.tree → (Fin d → ℤ)) → (GNode G.tree → (Fin d → ℤ)))
    (hf : ∀ x, ∀ y ∈ clRealizationNodes G lv.c.U, f x y = x y) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    bundleVars κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk)
        (rA (lv.split B RD hG layer hLayer pstar hk).RS (f x)) u =
      (u (lv.split B RD hG layer hLayer pstar hk).sb.b,
        dictS1 (nuOf (lv.state B RD hG layer hLayer) pstar)
          (u (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar)))
          (u (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))),
        dictT1 (nuOf (lv.state B RD hG layer hLayer) pstar)
          (u (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar)))
          (u (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))),
        dictX (nuOf (lv.state B RD hG layer hLayer) pstar)
          (κ0.base + latticePoint κ0.L (x ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode))
          (κ0.base + latticePoint κ0.L (x ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode)),
        dictY (nuOf (lv.state B RD hG layer hLayer) pstar)
          (κ0.base + latticePoint κ0.L (x ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode))
          (κ0.base + latticePoint κ0.L (x ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode))) := by
  set sp := lv.split B RD hG layer hLayer pstar hk
  have h1 : rA sp.RS (f x) ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode =
      x ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode :=
    (rA_lower sp (f x)).trans (hf x _ (lower_real_c sp))
  have h2 : rA sp.RS (f x) ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode =
      x ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode :=
    (rA_retained sp (f x)).trans (hf x _ (retained_real_c sp))
  unfold bundleVars
  rw [h1, h2]
  rfl

theorem split_sb_bΓ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) :
    (lv.split B RD hG layer hLayer pstar hk).sb.b = (assemblyPieceAtΓ B (lv.e pstar).1).lower := by
  have h1 := (lv.split B RD hG layer hLayer pstar hk).joint
  have h2 := (lv.split B RD hG layer hLayer pstar hk).bk
  have h3 := start_lowerΓ B RD hG layer hLayer (lv.e pstar)
  rw [h1, h2]
  exact h3

end Vars

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
