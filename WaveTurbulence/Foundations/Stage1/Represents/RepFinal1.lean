/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepNoVine5
public import WaveTurbulence.Foundations.Stage1.Represents.RepFinal0
public import WaveTurbulence.Foundations.Spine.IncoherentConstantMonotonicity
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the vine-free `RepresentsInt` at the `WTPrefix` level (finding F-CONST)

`NoVineRepresentsAt P`: for every vine-free piece `stage1PieceOf` at the parameter record `P`, `RepresentsInt`
holds (`represents_noVine` at the piece constant `C = P.C₁`).  `noVine_prefix`: it holds on the `WTPrefix` of the
two leafwise gates.  The piece constant is chosen AFTER the gate constant: the gates are used at `Pg` and the piece
at `{Pg with C₁ := C}` with `C ≥ CminF d η Pg.C₁`, a function of `d`, `η` and the gate constant only; the later
parameters `ν, δ, D, C₂, L` are unchanged.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed Set

/-- `RepresentsInt` of every vine-free Stage 1 piece, at the parameter record `P`. -/
def NoVineRepresentsAt (P : WTParams) : Prop :=
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
      (stage1PieceOf P.d hS (RegRed.layeredReconstruction D hS layer hLayer) (D.garden_decodes hS) σ)
      n tt base roots s
      (F.valueSel tt base roots (RegRed.layeredReconstruction D hS layer hLayer)
        (fun κ => selOf (GroupPrescription.ofPrescription σ) P.L P.γ P.η base
          (collapseGenDecoration D hS κ).1))

theorem N_bumpC1 (P : WTParams) (C : ℝ) (p : ℕ) : ({P with C₁ := C} : WTParams).N p = P.N p := by
  simpa using N_largeConstants P C P.C₂ p

theorem noVineRepresentsAt_of_gate (Pg : WTParams) (E : GateEnv Pg) (C : ℝ)
    (hC : CminF Pg.d Pg.η Pg.C₁ ≤ C) : NoVineRepresentsAt { Pg with C₁ := C } := by
  obtain ⟨Cmin, hC1, hCe, hmain⟩ := represents_noVine Pg E
  intro R S D hS layer hLayer p hp hN hcan tt htt F hctrl base roots σ hσ hM n s hs hnrest
  rw [N_bumpC1] at hN
  exact hmain C (hCe ▸ hC) D hS layer hLayer p hp hN hcan tt htt F hctrl base roots σ hσ hM n s hs hnrest

end WaveTurbulence.Represents
