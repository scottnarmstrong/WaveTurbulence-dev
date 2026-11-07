/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemFar1
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P1.Ext

/-! # P4-W2 (session 8, R-SUPPLY): the exact kernels vanish below the root layer

`root_branching_cpl`, `root_branching_tree`: a coherent carrier whose root layer exceeds `q'` has a branching root (type 2 with a nonempty `+` chain: `plug_pair_eq`).
`KQstar_zero_below_root`, `KTstar_zero_below_root`: then the exact kernel vanishes for `t ≤ Lr` (the time domain is empty: the root time lies in `(Lr, Lr + 1)` and below `t`). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.PL234 TTree WaveTurbulence.Reg WaveTurbulence.Links
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1

theorem kDomain_eq_empty {w : ℕ} (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (b0 : GBranch LG.garden.tree) (h : up b0 ≤ (LG.layer b0.toNode : ℝ)) : kDomain LG up s = ∅ := by
  ext τ
  simp only [kDomain, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hτ
  obtain ⟨a1, a2, -⟩ := hτ b0
  linarith [(hτ b0).2.2.2.1]

theorem kernelK_eq_zero_of_empty {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (h : kDomain LG up s = ∅) : kernelK L γ δ F LG up s k₀ nroot nfl = 0 := by
  unfold kernelK phaseIntegral
  simp [h]


theorem root_branching_cpl {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2} (hqq : q' ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentCoupleAt p q q' Q LG) (hgt : q' < cplRootLayer LG) :
    ([] : Path) ∈ (LG.garden.tree 0).branching := by
  cases Q with
  | triv =>
    have := layers_type1 hqq hcoh rfl (GNode.root LG.garden.tree 0)
    exact absurd this (Nat.ne_of_gt hgt)
  | type1 c Q₁ Q₂ Q₃ =>
    have := layers_type1 hqq hcoh rfl (GNode.root LG.garden.tree 0)
    exact absurd this (Nat.ne_of_gt hgt)
  | type2 Xp Xm Qlp =>
    obtain ⟨-, hnil⟩ := type2_root hqq hqp hcoh
    have hne : layerAt LG ((0 : Fin 2), []) ≠ q' := by rw [← cplRootLayer_eq]; exact Nat.ne_of_gt hgt
    have hX := hnil hne
    cases Xp with
    | nil => exact absurd rfl hX
    | pair m Qr Qg inner rest =>
      have F := cohFacts_of_coherent hqq hqp hcoh
      have e : LG.garden.tree 0 = (RegChain.pair m Qr Qg inner rest).plug 1 Qlp.trees.1 := F.emb.tree
      rw [e, plug_pair_eq]
      simp [TTree.branching, node3]

theorem root_branching_tree {p q q' : ℕ} {X : RegChain} {LG : LayeredGarden 1} (hqq : q' ≤ q)
    (hcoh : IsCoherentTreeAt p q q' X LG) (hgt : q' < treeRootLayer LG) :
    ([] : Path) ∈ (LG.garden.tree 0).branching := by
  obtain ⟨-, -, hnil⟩ := tree_root_bounds hqq hcoh
  have hne : layerAt LG ((0 : Fin 1), []) ≠ q' := by rw [← treeRootLayer_eq]; exact Nat.ne_of_gt hgt
  have hX := hnil hne
  cases X with
  | nil => exact absurd rfl hX
  | pair m Qr Qg inner rest =>
    have e : LG.garden.tree 0 = (RegChain.pair m Qr Qg inner rest).plug (LG.garden.sig 0) .leaf := hcoh.2.1.1
    rw [e, plug_pair_eq]
    simp [TTree.branching, node3]


theorem KQstar_zero_below_root {d p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (hqq : q' ≤ q) (hqp : q ≤ p) (hcoh : IsCoherentCoupleAt p q q' Q LG) (hgt : q' < cplRootLayer LG) {t : ℝ}
    (ht : t ≤ (cplRootLayer LG : ℝ)) (s : ℝ) (k : Mom d) : KQstar L γ δ F LG t s k = 0 := by
  unfold KQstar
  refine kernelK_eq_zero_of_empty L γ δ F LG _ _ _ _ _ (kDomain_eq_empty LG _ _
    (⟨((0 : Fin 2), ([] : Path)), root_branching_cpl hqq hqp hcoh hgt⟩ : GBranch LG.garden.tree) ?_)
  show t ≤ (cplRootLayer LG : ℝ)
  exact ht

theorem KTstar_zero_below_root {d p q q' : ℕ} {X : RegChain} {LG : LayeredGarden 1} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (hqq : q' ≤ q) (hcoh : IsCoherentTreeAt p q q' X LG) (hgt : q' < treeRootLayer LG) {t : ℝ}
    (ht : t ≤ (treeRootLayer LG : ℝ)) (s : ℝ) (k : Mom d) : KTstar L γ δ F LG t s k = 0 := by
  unfold KTstar
  refine kernelK_eq_zero_of_empty L γ δ F LG _ _ _ _ _ (kDomain_eq_empty LG _ _
    (⟨((0 : Fin 1), ([] : Path)), root_branching_tree hqq hcoh hgt⟩ : GBranch LG.garden.tree) ?_)
  show t ≤ (treeRootLayer LG : ℝ)
  exact ht

end WaveTurbulence.VineEstS5C.P4.W2
