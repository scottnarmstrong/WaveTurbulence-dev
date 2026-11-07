/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepPr1
public import WaveTurbulence.Foundations.Stage1.Represents.RepFinal2
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the vine-free `RepresentsInt` for VINE-A's successor producer (R83)

`represents_noVineN`, `NoVineRepresentsAtN`, `noVine_prefixN`: `RepNoVine5`, `RepFinal1`, `RepFinal2` restated for
`NormalizedSplice.stage1PieceOf` with the successor `gapSpecification`/`selOf`.  The analytic core
`represents_noVine_core` is generic in the piece and the selection, so only the transport of the gap data changes
(`splicedGapIndicator_eq_selOf` of VINE-A).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed Set WaveTurbulence.VineA

variable {w : ℕ} {S : Garden w}

noncomputable def gsCastN (σ : Prescription S) (h : unitBlocks S σ = []) :
    (v : GBranch S.tree) → Option (LocalGapSpecification S v) :=
  (stSt_G_eq_of_unitBlocks_empty σ h) ▸ NormalizedSplice.gapSpecification S σ

theorem heq_gapSpecN (σ : Prescription S) (h : unitBlocks S σ = []) :
    HEq (NormalizedSplice.gapSpecification S σ) (gsCastN σ h) :=
  heq_cast_gapSpec (stSt S σ).G (stSt_G_eq_of_unitBlocks_empty σ h) _

open scoped Classical in
theorem gapIndicator_noVineN (hM : S.molecule.IsMolecule) (hp : S.IsPlain) (σ : Prescription S)
    (h : unitBlocks S σ = []) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (zS : GenDecoration S d roots 0)
    (D : SplicedKernelData (stSt S σ).G d) (hD : D.gapSpecification = NormalizedSplice.gapSpecification S σ) :
    splicedGapIndicator (stSt S σ).G D L γ η base (fun n => zS.1 (nodeCast σ h n)) =
      if NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base zS.1 then 1 else 0 :=
  NormalizedSplice.splicedGapIndicator_eq_selOf (G := S) hM σ L γ η base _ zS.1
    (spliced_molecule_decoration S hp hL base roots zS)
    (fun v _ hv => gardenSource_eq_zero_of_deg_four S hp _ v hv) _
    (bondIndex_nodeCast σ h zS.1) D hD

open scoped Classical in
theorem hgsp_noVineN (hM : S.molecule.IsMolecule) (hp : S.IsPlain) (σ : Prescription S)
    (h : unitBlocks S σ = []) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) :
    ∀ D' : SplicedKernelData S d, D'.gapSpecification = gsCastN σ h → ∀ z : GenDecoration S d roots 0,
      splicedGapIndicator S D' L γ η base z.1 =
        if NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base z.1
          then 1 else 0 := by
  intro D' hD' z
  have e := stSt_G_eq_of_unitBlocks_empty σ h
  rw [transport_gapIndicator (stSt S σ).G e D']
  have hD'' := transport_gapSpec (stSt S σ).G e (NormalizedSplice.gapSpecification S σ) D' hD'
  have := gapIndicator_noVineN hM hp σ h hL γ η base roots z (e.symm ▸ D') hD''
  convert this using 2
  funext n
  exact congrArg (fun x => z.1 x) (cast_node_eq (stSt S σ).G e n)

variable {R : ℕ}

open scoped Classical in
theorem represents_noVineN (Pg : WTParams) (E : GateEnv Pg) :
    ∃ Cmin : ℝ, 1 ≤ Cmin ∧ Cmin = CminF Pg.d Pg.η Pg.C₁ ∧ ∀ (C : ℝ), Cmin ≤ C →
      ∀ {R : ℕ} {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
        (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (p : ℕ),
        p < Pg.D → D.size ≤ Pg.N (p + 1) ^ 4 →
        IsCanonGC (p + 1) (RegRed.layeredReconstruction D hS layer hLayer) →
        ∀ (tt : Fin (2 * R) → ℝ), (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
        ∀ (F : LeafFamily { Pg with C₁ := C } (2 * R)),
        F.Controlled (RegRed.layeredReconstruction D hS layer hLayer) →
        ∀ (base : Mom Pg.d) (roots : Fin (2 * R) → (Fin Pg.d → ℤ)) (σ : Prescription S),
        unitBlocks S σ = [] → S.molecule.IsMolecule →
        ∀ (n : ℕ) (s : ℝ), F.size (RegRed.layeredReconstruction D hS layer hLayer) ≤ s →
        n - S.order = D.size →
        Stage1Piece.RepresentsInt (P := { Pg with C₁ := C })
          (NormalizedSplice.stage1PieceOf Pg.d hS (RegRed.layeredReconstruction D hS layer hLayer)
            (D.garden_decodes hS) σ)
          n tt base roots s
          (F.valueSel tt base roots (RegRed.layeredReconstruction D hS layer hLayer)
            (fun κ => NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ)
              Pg.L Pg.γ Pg.η base (collapseGenDecoration D hS κ).1)) := by
  obtain ⟨Cmin, hC1, hCe, hcore⟩ := represents_noVine_core Pg E
  refine ⟨Cmin, hC1, hCe, fun C hC R S D hS layer hLayer p hp hN hcan tt htt F hctrl base roots σ hσ hM n s hs
    hnrest => ?_⟩
  have hL : Pg.L ≠ 0 := by have := E.hL1; positivity
  refine hcore C hC D hS layer hLayer p hp hN hcan tt htt F hctrl base roots (gsCastN σ hσ)
    (fun z => NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) Pg.L Pg.γ Pg.η base z.1)
    (hgsp_noVineN hM hS σ hσ hL Pg.γ Pg.η base roots)
    (NormalizedSplice.stage1PieceOf Pg.d hS (RegRed.layeredReconstruction D hS layer hLayer)
      (D.garden_decodes hS) σ)
    (stSt_G_eq_of_unitBlocks_empty σ hσ)
    (stSt_hinges_eq_empty σ hσ) ?_ (heq_gapSpecN σ hσ) ?_ ?_ n s hs hnrest
  · have e : RegRed.coreLayer (RegRed.layeredReconstruction D hS layer hLayer) D hS (D.garden_decodes hS) =
        fun b => layer (D.coreBranch hS b).toNode := rfl
    show HEq ((stSt S σ).layer (RegRed.coreLayer (RegRed.layeredReconstruction D hS layer hLayer) D hS
      (D.garden_decodes hS))) _
    rw [e]
    exact heq_layer σ hσ _
  · exact bskOf_noVine σ hσ
  · show gskOf _ S σ _ = _
    rw [gskOf_noVine _ σ hσ, gregOf_eq_sum_slotIncoh D hS layer hLayer]

/-- `RepresentsInt` of every vine-free successor piece, at the parameter record `P`. -/
def NoVineRepresentsAtN (P : WTParams) : Prop :=
  ∀ (R : ℕ) (S : Garden (2 * R)) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (p : ℕ),
    p < P.D → D.size ≤ P.N (p + 1) ^ 4 →
    IsCanonGC (p + 1) (RegRed.layeredReconstruction D hS layer hLayer) →
    ∀ (tt : Fin (2 * R) → ℝ), (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
    ∀ (F : LeafFamily P (2 * R)), F.Controlled (RegRed.layeredReconstruction D hS layer hLayer) →
    ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (σ : Prescription S),
    unitBlocks S σ = [] → S.molecule.IsMolecule →
    ∀ (n : ℕ) (s : ℝ), F.size (RegRed.layeredReconstruction D hS layer hLayer) ≤ s →
    n - S.order = D.size →
    Stage1Piece.RepresentsInt (P := P)
      (NormalizedSplice.stage1PieceOf P.d hS (RegRed.layeredReconstruction D hS layer hLayer)
        (D.garden_decodes hS) σ)
      n tt base roots s
      (F.valueSel tt base roots (RegRed.layeredReconstruction D hS layer hLayer)
        (fun κ => NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) P.L P.γ P.η base
          (collapseGenDecoration D hS κ).1))

theorem noVineRepresentsAtN_of_gate (Pg : WTParams) (E : GateEnv Pg) (C : ℝ)
    (hC : CminF Pg.d Pg.η Pg.C₁ ≤ C) : NoVineRepresentsAtN { Pg with C₁ := C } := by
  obtain ⟨Cmin, hC1, hCe, hmain⟩ := represents_noVineN Pg E
  intro R S D hS layer hLayer p hp hN hcan tt htt F hctrl base roots σ hσ hM n s hs hnrest
  rw [N_bumpC1] at hN
  exact hmain C (hCe ▸ hC) D hS layer hLayer p hp hN hcan tt htt F hctrl base roots σ hσ hM n s hs hnrest

end WaveTurbulence.Represents
