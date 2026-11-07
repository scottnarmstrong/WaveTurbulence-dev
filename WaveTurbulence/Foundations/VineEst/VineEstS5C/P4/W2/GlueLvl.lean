/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Glue
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Terms
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Family

/-! # P4-W2 (N1): every unrolled term has a row form on its level's region

`rowForm_idx`: the row form does not depend on the region data of a fixed `(U, a, b)`.  `FrameShape BE X`: at operative members, every
summand of the bundle expansion is the frame `bundleFrame` (= `spartFrame` of the S-block at the exceptional pair `p₀`) times an
exceptional factor `X` (true for P4's `bundleFamOf`: `bundleTerm = bundleFrame · ν · bundlePt`, `frameShape_bundleExpOf`).
**`rowForm_terms`**: by `Lvl.terms_induction` and `rowForm_step`, every unrolled term of a level has a row form on the region of the level;
the terms ending in the bottom bundle `psiBot` are covered through the named input `hbot` (owner BOT-DECOMP, R60).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1

variable {w d : ℕ} {G : Garden w}

/-- The row form is independent of the region data of a fixed `(U, a, b)`. -/
theorem rowForm_idx (hG : G.IsPlain) {U U' : Finset (GBranch G.tree)} {a a' b b' : GBranch G.tree} (hU : U = U') (ha : a = a')
    (hb : b = b') (R : CLRegionData G U a b) (R' : CLRegionData G U' a' b') (L γ δ : ℝ) (base : Mom d) (ψ : PsiT G d)
    (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop)
    (Qw : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ)
    (Tw : GBranch G.tree → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ)
    (h : RowForm hG R L γ δ base ψ Dm Qw Tw) : RowForm hG R' L γ δ base ψ Dm Qw Tw := by
  subst hU ha hb
  rw [regionData_subsingleton R' R]
  exact h

variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

/-- At operative members every bundle summand is the frame times an exceptional factor. -/
def FrameShape : Prop :=
  ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar →
    ∃ X : (BE lv pstar hk).Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ,
      ∀ (c : (BE lv pstar hk).Ch) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ),
        (BE lv pstar hk).term c x u =
          bundleFrame κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u * X c x u

/-- **The glue identity for every unrolled term (N1).**  Every term of `Lvl.terms m lv` has a row form on the region of `lv`, given the
row forms of the bottom bundles (`hbot`, BOT-DECOMP). -/
theorem rowForm_terms (hL : κ0.L ≠ 0) (hX : FrameShape B RD hG layer hLayer BE)
    (hbot : ∀ (lv : Lvl B) (pstar : lv.ι), lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar →
      (∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) → (lv.e pstar).1.val = 0 →
      ∃ Dm Qw Tw, RowForm hG lv.region κ0.L κ0.γ κ0.δ κ0.base
        (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar) Dm Qw Tw) :
    ∀ (m : ℕ) (lv : Lvl B), ∀ ψ ∈ Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer BE m lv,
      ∃ Dm Qw Tw, RowForm hG lv.region κ0.L κ0.γ κ0.δ κ0.base ψ Dm Qw Tw := by
  refine Lvl.terms_induction B RD hG layer hLayer BE
    (fun lv ψ => ∃ Dm Qw Tw, RowForm hG lv.region κ0.L κ0.γ κ0.δ κ0.base ψ Dm Qw Tw) ?_ hbot ?_
  · intro lv
    exact ⟨_, _, _, rowForm_psiNat (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain lv.region
      κ0.L κ0.γ κ0.δ κ0.F (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer))
      κ0.base⟩
  · intro lv pstar hk hop _ c Ψ' ⟨Dm', Qw', Tw', hΨ⟩
    obtain ⟨X, hXe⟩ := hX lv pstar hk hop
    set A := lv.state B RD hG layer hLayer with hA
    set sp := lv.split B RD hG layer hLayer pstar hk with hsp
    have hT' : RowForm hG sp.RT κ0.L κ0.γ κ0.δ κ0.base Ψ' Dm' Qw' Tw' :=
      rowForm_idx hG rfl (lv.split B RD hG layer hLayer pstar hk).joint.symm rfl _ _ _ _ _ _ _ _ _ _ hΨ
    have hstep := rowForm_step sp.sb.block sp.hT sp.hi sp.hU A.data A.plain κ0.L κ0.γ κ0.δ hL κ0.F (stateLayer A)
      (stateLayer_isLayering A) κ0.base sp.RU sp.RS sp.RT (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)
      (SplitAt.slow sp).p0_mem (SplitAt.slow sp).b_mem_erase (fun x u => X c x u) Ψ' hT'
    have hfun : (fun (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) => (BE lv pstar hk).term c (rA sp.RS x) u * Ψ' (rB sp.RT x) ![u sp.sb.b, t 1, t 2] u) =
        fun (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) => spartFrame A.data A.plain κ0.L κ0.γ κ0.δ κ0.F (stateLayer A) (stateLayer_isLayering A) κ0.base sp.sb.U
          sp.sb.a sp.sb.b (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) (rA sp.RS x) u *
            X c (rA sp.RS x) u * Ψ' (rB sp.RT x) ![u sp.sb.b, t 1, t 2] u := by
      funext x t u
      rw [hXe c]
      rfl
    have hfin := rowForm_idx hG sp.union.symm sp.sa sp.tbb sp.RU lv.region _ _ _ _ _ _ _ _ hstep
    exact ⟨_, _, _, Eq.mpr (congrArg (fun f => RowForm hG lv.region κ0.L κ0.γ κ0.δ κ0.base f _ _ _) hfun) hfin⟩

open Classical in
/-- **P4's bundle family has the frame shape** (`bundleTerm = bundleFrame · (ν · bundlePt)`). -/
theorem frameShape_bundleFamOf (hR : RealityAll) (SFF : SepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime) :
    FrameShape B RD hG layer hLayer (bundleFamOf B RD hG layer hLayer hR SFF) := by
  intro lv pstar hk hop
  unfold bundleFamOf
  rw [dif_pos hop]
  refine ⟨fun c x u => ((nuOf (lv.state B RD hG layer hLayer) pstar : ℤˣ) : ℂ) *
    bundlePt p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} κ0 (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime (SFF lv pstar hk hop) _ _
      (bundleVars κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u).1
      (bundleVars κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u).2.1
      (bundleVars κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u).2.2.1
      (bundleVars κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u).2.2.2.1
      (bundleVars κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u).2.2.2.2 c,
    fun c x u => ?_⟩
  simp only [bundleExpOf, bundleTerm]
  ring

end WaveTurbulence.VineEstS5C.P4.W2
