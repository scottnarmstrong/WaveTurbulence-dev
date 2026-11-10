/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelClk

/-! # B3s-HELPER4 (δ) S2 (3): the residual selection clauses of `ClassPieceOK`

For the piece `classPiece P mkF a prot nProt (fixOf J pat t s mkF a) filt ind lb` of B4's hypothesis (W:Stage1MKGate/Hyp)
with `nProt = |Π(a)|`, residual selected atoms `selR = selROf J kSel mkF a`, and any filter `filt` that is the
normalized selected filter `(Rs j, chiDN)` (ruling R179) at the residual selected atoms:

* `chiDNS`: the selected filter as a `SchwartzMap` (`chiDNS_apply : chiDNS u = chiDN u`, D7-2's
  `exists_schwartz_chiDN`), `norm_chiDNS_le_one`;
* **`classPiece_sel_spec`**, **`classPiece_sel_inj`**, **`classPiece_sel_card`**, **`classPiece_sel_lb`**: the clauses
  `sel_spec`, `sel_inj`, `sel_card`, `sel_lb` (ruling R187) of `ClassPieceOK`, for any lower bounds `lb` of the piece
  (`sel_lb`: when `lb` sits only in `dParent` trees);
* `classPiece_selFilt_ok`: the `filt_ok` facts of `PieceRestB3s` at a residual selected atom (not a hinge,
  radius `≥ 1`, sup `≤ 1`, `filterB ≤ cθ` when `cθ ≥ filterB chiDN`);
* `selMassMK_selROf`: the image of the residual atoms in the trees (the set `U` of `selMassMK`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.Flower.Stage1MKGate WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Flower.MkSlots

namespace WaveTurbulence.Flower.MkSlotsS

/-- The normalized selected filter `chiDN = chiD / chiDNorm` as a Schwartz function (ruling R179). -/
def chiDNS : SchwartzMap ℝ ℂ := Classical.choose WaveTurbulence.Flower.SelRes.exists_schwartz_chiDN

theorem chiDNS_apply (u : ℝ) : chiDNS u = (chiDN u : ℂ) :=
  (Classical.choose_spec WaveTurbulence.Flower.SelRes.exists_schwartz_chiDN).1 u

theorem norm_chiDNS_le_one (u : ℝ) : ‖chiDNS u‖ ≤ 1 :=
  (Classical.choose_spec WaveTurbulence.Flower.SelRes.exists_schwartz_chiDN).2.1 u

section Piece

variable (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (kSel : Fin (2 * R) → Option ℕ) (mkF : Stage1Mk.MarkFn (2 * R)) (a : PrescribedPrimeGarden (2 * R))
  (prot : Finset (GBranch (stA mkF a).G.tree))
  (filt : GBranch (stA mkF a).G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
  (ind : (GNode (stA mkF a).G.tree → Mom P.d) → ℝ) (lb : GBranch (stA mkF a).G.tree → Option ℝ)
  (Rs : Fin (2 * R) → ℝ)

/-- **`ClassPieceOK.sel_spec`** for the residual selected atoms. -/
theorem classPiece_sel_spec (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
    (hfilt : ∀ c ∈ selROf J kSel mkF a, filt c = some (Rs c.1.1, chiDNS)) :
    ∀ v ∈ selROf J kSel mkF a, (kSel v.1.1).isSome ∧
      (classPiece P mkF a prot (protI a.layered J pat t s kSel).card (fixOf J pat t s mkF a) filt ind
        lb).fix v = none ∧
      ∃ ψ : SchwartzMap ℝ ℂ,
        (classPiece P mkF a prot (protI a.layered J pat t s kSel).card (fixOf J pat t s mkF a) filt ind
        lb).filt v =
          some (Rs v.1.1, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ) :=
  fun v hv => ⟨selROf_kSel hv, selROf_fixOf hplain hv, chiDNS, hfilt v hv, chiDNS_apply⟩

/-- **`ClassPieceOK.sel_inj`**. -/
theorem classPiece_sel_inj : ∀ v ∈ selROf J kSel mkF a, ∀ v' ∈ selROf J kSel mkF a, v.1.1 = v'.1.1 → v = v' :=
  fun _ hv _ hv' h => selROf_inj hv hv' h

/-- **`ClassPieceOK.sel_card`** (`nProt = |Π(a)|`). -/
theorem classPiece_sel_card :
    (selROf J kSel mkF a).card ≤
      (classPiece P mkF a prot (protI a.layered J pat t s kSel).card (fixOf J pat t s mkF a) filt ind
        lb).nProt :=
  selROf_card_le pat t s

/-- **`PieceRestB3s.filt_ok` at a residual selected atom** (with `L ≤ Rs j`, `1 ≤ L`, `filterB chiDN ≤ cθ`). -/
theorem classPiece_selFilt_ok (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG),
      markI J pat t s kSel B ⊆ mkF B)
    (hL : 1 ≤ P.L) (hRs : ∀ j, P.L ≤ Rs j) (cθ : ℝ) (hcθ : filterB ⇑chiDNS ≤ cθ)
    {c : GBranch (stA mkF a).G.tree} (hc : c ∈ selROf J kSel mkF a) :
    c ∉ (classPiece P mkF a prot (protI a.layered J pat t s kSel).card (fixOf J pat t s mkF a) filt ind
        lb).Cs.hinges ∧
      1 ≤ (Rs c.1.1, chiDNS).1 ∧ (∀ u, ‖(Rs c.1.1, chiDNS).2 u‖ ≤ 1) ∧ filterB ⇑(Rs c.1.1, chiDNS).2 ≤ cθ :=
  ⟨selROf_not_hinge pat t s hsub hc, hL.trans (hRs _), norm_chiDNS_le_one, hcθ⟩

end Piece

end WaveTurbulence.Flower.MkSlotsS
