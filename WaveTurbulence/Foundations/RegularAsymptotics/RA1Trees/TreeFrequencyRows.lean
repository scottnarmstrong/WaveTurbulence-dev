/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.InputProductIdentity
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.NodeValueBound

/-! # Uniform frequency pullback bounds from the actual tree momentum rows -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Incoh IncohInst

/-- Test the actual tree decoration on a unit coordinate; no matrix norm is assumed. -/
theorem norm_treeNodeRow_le {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (a : GNode G.tree) (c : MomentumCoordinate (X.treeLinks (G.sig 0)).length) :
    ‖treeNodeRow hX a c‖ ≤ 1+(X.size:ℝ) := by
  let t : Fin (X.treeLinks (G.sig 0)).length → ℤ × ℤ := fun j =>
    (momentumUnitRow c (some (j,0)), momentumUnitRow c (some (j,1)))
  have hunit (z : MomentumCoordinate (X.treeLinks (G.sig 0)).length) :
      ‖momentumUnitRow c z‖ ≤ (1:ℝ) := by
    unfold momentumUnitRow
    split <;> norm_num
  have ht (j : Fin (X.treeLinks (G.sig 0)).length) :
      ‖(t j).1‖ ≤ (1:ℝ) ∧ ‖(t j).2‖ ≤ (1:ℝ) := ⟨hunit _, hunit _⟩
  have hpar (z : Fin 1 × TTree.Path) :
      ‖(treeParamFun X (G.sig 0) t z).1‖ ≤ (1:ℝ) ∧
      ‖(treeParamFun X (G.sig 0) t z).2‖ ≤ (1:ℝ) := by
    unfold treeParamFun
    split
    · exact ht _
    · simp
  have hh := norm_chainVal_le (treeParamFun X (G.sig 0) t) 1 zero_le_one hpar
    X (G.sig 0) (0,[]) (momentumUnitRow c none) 0 (le_refl 0)
    (fun _ => momentumUnitRow c none) (fun _ => by simp) a.val
  have he : treeNodeRow hX a c =
      (treeDecOfParams hX (momentumUnitRow c none) t).val a := by
    have hrow := treeNodeRow_eval hX a (momentumUnitRow c)
    change (∑ j, treeNodeRow hX a j • momentumUnitRow c j) = _ at hrow
    simpa [momentumUnitRow, smul_eq_mul, t] using hrow
  rw [he]
  change ‖chainVal (treeParamFun X (G.sig 0) t) X (G.sig 0) (0,[])
    (momentumUnitRow c none) (fun _ => momentumUnitRow c none) a.val‖ ≤ _
  exact hh.trans (by simpa only [mul_one, add_zero] using add_le_add (hunit none) (le_refl (X.size:ℝ)))

end WaveTurbulence.RegAsymp
