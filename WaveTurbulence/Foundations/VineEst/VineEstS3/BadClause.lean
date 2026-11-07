/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseD
public import WaveTurbulence.Foundations.VineEst.VineEstS3.AdmissibleAssembly
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3At

/-! # `BadClause` of the canonical bad kinds (TARGET Step 3, L1841-L1847)

`canonBadKind i = 0` if clause (a) holds for the vine `i` and `3` otherwise.  `badClause_canon`: with the case premise
`CoreVinesNoTwist`, `BadClause` holds for the `step3D` datum with this bad kind: clause (a) by definition, clause (d) by
`bad_d` (non-core and layer-ineligible vines satisfy (a), `aClause_typeII`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.Twist VineParamContract TTree RegRed
  WaveTurbulence.Reg.Skeleton
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
variable (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
variable (hLayer : IsLayering (RD.garden hG) layer)

open Classical in
/-- The bad kind of the vine `i`: `0` if clause (a) holds, `3` otherwise. -/
noncomputable def canonBadKind (i : Fin (assemblyShape hM9 B).I) : Fin 4 :=
  if AClause hM9 B RD hG layer i then 0 else 3

theorem canonBadKind_cases (i : Fin (assemblyShape hM9 B).I) :
    canonBadKind hM9 B RD hG layer i = 0 ∨ canonBadKind hM9 B RD hG layer i = 3 := by
  unfold canonBadKind
  split_ifs <;> simp

include hLayer in
theorem badClause_canon (hno : CoreVinesNoTwist B RD hG layer hLayer) (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom d)
    (wBar : Mom d) :
    BadClause (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) qOut centre wBar) := by
  classical
  intro i hnor
  refine ⟨fun h0 => ?_, fun h2 => ?_, fun h3 => ?_⟩
  · have : AClause hM9 B RD hG layer i := by
      by_contra hn
      have : canonBadKind hM9 B RD hG layer i = 3 := by unfold canonBadKind; rw [if_neg hn]
      have h0' : canonBadKind hM9 B RD hG layer i = 0 := h0
      rw [this] at h0'
      exact absurd h0' (by decide)
    exact this
  · have h2' : canonBadKind hM9 B RD hG layer i = 2 := h2
    rcases canonBadKind_cases hM9 B RD hG layer i with h | h <;> rw [h] at h2' <;> exact absurd h2' (by decide)
  · have h3' : canonBadKind hM9 B RD hG layer i = 3 := h3
    have hnA : ¬ AClause hM9 B RD hG layer i := by
      intro hA
      have : canonBadKind hM9 B RD hG layer i = 0 := by unfold canonBadKind; rw [if_pos hA]
      rw [this] at h3'
      exact absurd h3' (by decide)
    have hbad : (assemblyPieceAt B i).vineType.IsBad = true := by
      have : (assemblyShape hM9 B).nor i = false := hnor
      simpa [assemblyShape, shapeFamily] using this
    obtain ⟨⟨i', j⟩, hi, hj⟩ := bad_d hM9 B RD hG layer hLayer hno i hbad hnA
    have hi' : i' = i := hi
    subst hi'
    exact ⟨j, hj⟩

end WaveTurbulence.VineEstS3
