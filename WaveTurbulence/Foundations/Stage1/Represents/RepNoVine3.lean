/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSlots2
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the vine-free core of `Represents` (abstract piece)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed
  WaveTurbulence.RepAnalytic WaveTurbulence.PL2330 WaveTurbulence.RegRedLeaf
open scoped ENNReal

/-- The explicit minimal constant of `represents_noVine_core` (depends only on `d`, `η`, the gate constant). -/
noncomputable def CminF (d : ℕ) (η c₁ : ℝ) : ℝ :=
  max (max 1 (2 * c₁ ^ 2 * (1 + cLeib d (30 * d)))) (Cchi d * (nodeBallCard d : ℝ) * Kslot d η ^ 2)

open scoped Classical in
theorem represents_noVine_core (Pg : WTParams) (E : GateEnv Pg) :
    ∃ Cmin : ℝ, 1 ≤ Cmin ∧ Cmin = CminF Pg.d Pg.η Pg.C₁ ∧ ∀ (C : ℝ), Cmin ≤ C →
      ∀ {R : ℕ} {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
        (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (p : ℕ),
        p < Pg.D → D.size ≤ Pg.N (p + 1) ^ 4 →
        IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer) →
        ∀ (tt : Fin (2 * R) → ℝ), (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
        ∀ (F : LeafFamily { Pg with C₁ := C } (2 * R)),
        F.Controlled (layeredReconstruction D hS layer hLayer) →
        ∀ (base : Mom Pg.d) (roots : Fin (2 * R) → (Fin Pg.d → ℤ))
          (gs : (v : GBranch S.tree) → Option (LocalGapSpecification S v))
          (selSk : GenDecoration S Pg.d roots 0 → Prop),
        (∀ D' : SplicedKernelData S Pg.d, D'.gapSpecification = gs → ∀ z : GenDecoration S Pg.d roots 0,
          splicedGapIndicator S D' Pg.L Pg.γ Pg.η base z.1 = if selSk z then 1 else 0) →
        ∀ (π : Stage1Piece { Pg with C₁ := C } R), π.Gsb = S → π.Cs.hinges = ∅ →
        HEq π.layer (fun b => layer (D.coreBranch hS b).toNode) → HEq π.gapSpecification gs →
        π.bsk = 0 → π.gsk = ∑ s, slotIncoh D hS layer hLayer s →
        ∀ (n : ℕ) (s : ℝ), F.size (layeredReconstruction D hS layer hLayer) ≤ s →
        n - S.order = D.size →
        π.RepresentsInt n tt base roots s
          (F.valueSel tt base roots (layeredReconstruction D hS layer hLayer)
            (fun κ => selSk (collapseGenDecoration D hS κ))) := by
  obtain ⟨K, hK1, hKe, hslot⟩ := slots_exist Pg E
  refine ⟨max (max 1 (2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d))))
      (Cchi Pg.d * (nodeBallCard Pg.d : ℝ) * K ^ 2), le_max_of_le_left (le_max_left _ _), by rw [CminF, hKe], ?_⟩
  intro C hC R S D hS layer hLayer p hp hN hcan tt htt F hctrl base roots gs selSk hgsp π hG hh hlay hgs
    hbsk hgsk n s hs hnrest
  have hC1 : 2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
  have hC2 : Cchi Pg.d * (nodeBallCard Pg.d : ℝ) * K ^ 2 ≤ C := le_trans (le_max_right _ _) hC
  have hx0 : 0 ≤ C * Real.sqrt Pg.δ := by
    have : 0 ≤ C := by nlinarith [E.hC1, cLeib_nonneg Pg.d (30 * Pg.d)]
    exact mul_nonneg this (Real.sqrt_nonneg _)
  refine representsInt_of_slots (P := { Pg with C₁ := C }) E.hd1 E.hL1 D hS layer hLayer F hctrl tt base roots
    gs selSk hgsp π hG hh hlay hgs K hK1 hC2 hx0 n s hs hbsk hnrest ?_
  intro i
  obtain ⟨Rep, hFn, hμ⟩ := hslot C hC1 D hS layer hLayer p hp hN hcan tt htt
    (F.H (layeredReconstruction D hS layer hLayer) i) (F.B (layeredReconstruction D hS layer hLayer) i)
    (hctrl i)
  refine ⟨Rep, hFn, slotSize D, slotIncoh D hS layer hLayer, slotLeaf D hS layer hLayer
    (F.B (layeredReconstruction D hS layer hLayer) i), ?_, hμ, prod_slotLeaf D hS layer hLayer _,
    sum_slotSize D, hgsk.symm⟩
  intro s
  cases s with
  | inl p' => exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  | inr b => exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _

end WaveTurbulence.Represents
