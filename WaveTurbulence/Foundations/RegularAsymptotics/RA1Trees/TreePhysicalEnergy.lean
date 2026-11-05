/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.ActualTreeProfile
public import WaveTurbulence.Foundations.IncohInst.TemporalSourceIdentity

/-! # The selected source tree energy has exactly the physical NT scale 2δ -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links IncohInst MainCoef

/-- Energy at the actual selected branch, with its original root and integer coset. -/
theorem tree_alphaOmega_chosen {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (L γ δ : ℝ) (k : Mom d)
    (p : Fin (X.treeLinks (G.sig 0)).length × Fin 2 → Fin d → ℤ)
    (j : Fin (X.treeLinks (G.sig 0)).length) :
    liftT (alphaOmegaT L γ δ G
      (cosetDecoration G L k (treeDecOfParams hX (0 : Fin d → ℤ)
        (fun i => (p (i,0),p (i,1)))).val)) (treeChosenAddress X (G.sig 0) j) =
      (2*δ*L^(2*γ))*inner ℝ (latticePoint L (p (j,0)))
        (latticePoint L (p (j,1))) := by
  rw [← tree_decOfParams_eq_coset hX L k]
  have he : ((0:Fin 1), (treeChosenAddress X (G.sig 0) j).2) =
      (treeChosenBranch hX j).val := by
    apply Prod.ext (Subsingleton.elim _ _)
    simp [treeChosenAddress, treeChosenBranch, treeChosen]
  unfold liftT alphaOmegaT
  rw [he, dite_eq_left (treeChosenBranch hX j).property]
  erw [omegaNode_eq (treeDecOfParams hX k _).property.1,
    tree_xNode_decOfParams, tree_yNode_decOfParams]
  ring

end WaveTurbulence.RegAsymp
