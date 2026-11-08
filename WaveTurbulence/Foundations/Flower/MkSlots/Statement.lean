/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Hyp

/-! # B3s MK-SLOTS: the milestone statements

`MarkedClassRepresentsMKα` is B4's pre-R185 `MarkedClassRepresentsMK` (Hyp.lean body without `J.card = R`) with the
milestone-α hypotheses inserted: plain patterns, no depth selection, no stem filter. It lacks `J.card = R` (finding
F-B3s-8, ruling R185), so it is superseded by `MarkedClassRepresentsMKαJ` (IntPlan.lean), the α instance of the
corrected `MarkedClassRepresentsMK`; the old specialization bridge from Hyp.lean was dropped with R185. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.Flower.Stage1MKGate

namespace WaveTurbulence.Flower.MkSlots

/-- **Milestone α** of B3s: `MarkedClassRepresentsMK` for plain patterns, no stem filter, no depth selection. -/
def MarkedClassRepresentsMKα (cP cθ : ℝ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ),
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t,
  (∀ j, pat j = FixPat.plain) → (∀ j, kSel j = none) →
  ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    (∀ j, σ j = none) →
    1 ≤ b → (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) → (∀ j, P.L ≤ Rs j) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∀ (mkF : Stage1Mk.MarkFn (2 * R)), FineMarking J pat t s kSel σ mkF →
  ∀ π : PcA R p (objKind (2 * R)) A mkF,
    (¬ StemDep σ kSel ∨ ∀ a : PrescribedPrimeGarden (2 * R),
      Related (p := p) (kind := objKind (2 * R)) (repPt π) a mkF → CleanPt J a) →
  ∃ (prot : Finset (GBranch (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree))
    (fix : GBranch (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree → Option ℝ)
    (filt : GBranch (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree →
      Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree → Mom P.d) →
      ℝ)
    (selR : Finset (GBranch (stSt (repPt π).prime.skeleton (repPt π).totalSigma (classMk mkF (repPt π))).G.tree)),
    ClassPieceOK (classPiece P mkF (repPt π) prot (protI (repPt π).layered J pat t s kSel).card fix filt ind) selR
      N cP cθ t b roots kSel Rs (classValue P p J pat kSel t s A roots h Rf σ Rs dag mkF π)

end WaveTurbulence.Flower.MkSlots
