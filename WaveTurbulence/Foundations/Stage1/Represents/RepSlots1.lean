/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepLeaf1
public import WaveTurbulence.Foundations.RegStruct.FiniteCodes
import Mathlib.Tactic

/-!
# S2 REPRESENTS: small structural facts for the slot gates
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed

theorem cpl_two_le (Q : RegCpl) (hwf : Q.wf = true) (hne : Q ≠ RegCpl.triv) : 2 ≤ Q.size := by
  cases Q with
  | triv => exact absurd rfl hne
  | type1 c Q₁ Q₂ Q₃ => simp only [RegCpl.size]; omega
  | type2 Xp Xm Qlp =>
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hwf
    have h := hwf.2
    simp only [RegCpl.size]
    by_cases hp : Xp.isNil = false
    · have := chain_size_pos_of_not_isNil hp; omega
    · have hm : Xm.isNil = false := by
        simpa [Bool.not_eq_false, hp] using h
      have := chain_size_pos_of_not_isNil hm; omega

theorem chain_two_le (X : RegChain) (hne : X ≠ RegChain.nil) : 2 ≤ X.size := by
  apply chain_size_pos_of_not_isNil
  cases X with
  | nil => exact absurd rfl hne
  | pair => rfl

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

theorem clkLayer_le (p : ℕ) (hp : ∀ ν, layer ν ≤ p) (y : ClkSrc S) :
    clkLayer p (fun b => layer (D.coreBranch hS b).toNode) y ≤ p := by
  rcases y with j | b
  · exact le_rfl
  · exact hp _

include hLayer in
theorem tree_q'_le_q (p : ℕ) (hp : ∀ ν, layer ν ≤ p) (b : GBranch S.tree) :
    clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inr b) 1) ≤
      clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inr b) 0) := by
  have hE := LFTwist.reconstruction_chainEmb D hS (D.garden_decodes hS) b
  have hnode := hE.node
  have hcl0 : argSrc hS (.inr b) 0 = clkOfNode S b.toNode := by simp [argSrc]
  have hcl1 : argSrc hS (.inr b) 1 = .inr b := by simp [argSrc]
  rw [hcl0, hcl1]
  have hcore : (D.corePosition b).2 ∈
      ((layeredReconstruction D hS layer hLayer).garden.tree (D.corePosition b).1).nodes :=
    (D.coreBranch hS b).toNode.2
  have h1 : Links.layerAt (layeredReconstruction D hS layer hLayer) (D.corePosition b) ≤
      Links.layerAt (layeredReconstruction D hS layer hLayer) (inflatedPosition S D.tree b.toNode) := by
    refine Links.layerAt_le_of_under (layeredReconstruction D hS layer hLayer) hnode hcore ?_
    exact ⟨rfl, List.prefix_append _ _⟩
  have h2 := Links.layerAt_le_parAt (layeredReconstruction D hS layer hLayer) (p := p) (fun a => hp _) hnode
  have h3 := Links.parAt_of_mem (layeredReconstruction D hS layer hLayer) p hnode
  rw [h3] at h2
  have h4 := parentLayer_inflated D hS layer hLayer p b.toNode ⟨_, hnode⟩ rfl
  have h5 : Links.layerAt (layeredReconstruction D hS layer hLayer) (D.corePosition b) =
      layer (D.coreBranch hS b).toNode :=
    Links.layerAt_node (layeredReconstruction D hS layer hLayer) (D.coreBranch hS b).toNode
  show layer (D.coreBranch hS b).toNode ≤ _
  rw [← h5, ← h4]
  exact h1.trans h2

end WaveTurbulence.Represents
