/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot7

/-! # V5 Step 4d-B2: the bottom vine, part 8 (the decoration bijection of the whole chain region)

`decEquiv h L base β : CLLocalDecoration RS L base β ≃ CLLocalDecoration RS' L base β`, `κ ↦ twistNodeLabels G P κ`: the local decorations
of the chain region of a garden and of its unit twist at the bottom piece, with the same four boundary momenta `β = (e, f, g, h)`
(the lower joint and the retained leaf exchange their labels; the labels at the boundary children are unchanged).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')
include h

theorem stw_paired_of_free {d : ℕ} {x : GNode G.tree → (Fin d → ℤ)} (hx : FreeDec RS x) : PairedAt P x :=
  hx.2.2 P.retained h.retained_internal

theorem stw_pulled_of_free {d : ℕ} {x' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ)} (hx : FreeDec RS' x') :
    x' (naiveNodeEquiv G P P.retained.toNode) = x' (naiveNodeEquiv G P (G.pair P.retained).toNode) := by
  have := hx.2.2 (eL P P.retained) h.retained_internal'
  have e : (unitTwistGarden G P).pair (eL P P.retained) = eL P (G.pair P.retained) :=
    unitTwistGarden_pair G P P.retained
  rw [e] at this
  rw [naiveNodeEquiv_leaf, naiveNodeEquiv_leaf]
  exact this

/-- **The extended decorations of the whole chain region correspond under the twist.** -/
@[expose] noncomputable def extCLEquiv {d : ℕ} (L : ℝ) (base : Mom d) (β : Fin 4 → Mom d) :
    ExtCL RS L base β ≃ ExtCL RS' L base β where
  toFun x := ⟨twistNodeLabels G P x.1, (stw_freeDec_iff P h x.1 (stw_paired_of_free P h x.2.1)).mp x.2.1,
    (stw_bdAt_iff P h L base β x.1 (stw_paired_of_free P h x.2.1)).mp x.2.2⟩
  invFun x' := ⟨untwistNodeLabels G P x'.1, by
    have e := twist_untwist_local x'.1 (stw_pulled_of_free P h x'.2.1)
    have hp := untwist_paired x'.1
    refine ⟨(stw_freeDec_iff P h _ hp).mpr ?_, (stw_bdAt_iff P h L base β _ hp).mpr ?_⟩
    · rw [e]; exact x'.2.1
    · rw [e]; exact x'.2.2⟩
  left_inv x := Subtype.ext (untwist_twistNodeLabels G P x.1 (stw_paired_of_free P h x.2.1))
  right_inv x' := Subtype.ext (twist_untwist_local x'.1 (stw_pulled_of_free P h x'.2.1))

/-- **The local decorations of the chain region and of its twist correspond.** -/
@[expose] noncomputable def decEquiv {d : ℕ} (L : ℝ) (base : Mom d) (β : Fin 4 → Mom d) :
    CLLocalDecoration RS L base β ≃ CLLocalDecoration RS' L base β :=
  (clExtEquiv RS L base β).trans ((extCLEquiv P h L base β).trans (clExtEquiv RS' L base β).symm)

theorem decEquiv_val {d : ℕ} (L : ℝ) (base : Mom d) (β : Fin 4 → Mom d) (κ : CLLocalDecoration RS L base β) :
    clExtendIndices RS' (decEquiv P h L base β κ).1 = twistNodeLabels G P (clExtendIndices RS κ.1) := by
  have e : clExtEquiv RS' L base β (decEquiv P h L base β κ) = extCLEquiv P h L base β (clExtEquiv RS L base β κ) := by
    unfold decEquiv
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  have := congrArg Subtype.val e
  exact this

end WaveTurbulence.VineEstS5B2
