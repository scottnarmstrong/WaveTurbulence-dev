/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LatticeCoordinates
public import WaveTurbulence.Foundations.WeylSums.ThreeVectorReduction

/-! # The exact phase in the regular-couple integer coordinates

DH23 (newsum1): Omega=2<x,y>. In particular the factor two does NOT
supply a compensating F61 sign.
-/

public section
namespace WaveTurbulence.RegAsymp
open Links

/-- Translation by the fixed root momentum preserves every source
conservation equation, including paired-leaf equalities. -/
theorem isDecoration_coset {d w : ℕ} {G : Garden w}
    {κ : GNode G.tree → (Fin d → ℤ)} (hκ : IsDecoration G κ) (L : ℝ) (k : Mom d) :
    IsDecoration G (cosetDecoration G L k κ) := by
  constructor
  · intro b
    simp only [cosetDecoration]
    rw [hκ.1 b,WeylSums.latticePoint_add_eq,WeylSums.latticePoint_sub_eq]
    abel
  · intro ℓ
    simp only [cosetDecoration,hκ.2 ℓ]

theorem xNode_coset {d w : ℕ} (G : Garden w) (κ : GNode G.tree → (Fin d → ℤ))
    (L : ℝ) (k : Mom d) (b : GBranch G.tree) :
    xNode (cosetDecoration G L k κ) b = latticePoint L (xNode κ b) := by
  simp only [xNode,cosetDecoration,WeylSums.latticePoint_sub_eq]
  abel

theorem yNode_coset {d w : ℕ} (G : Garden w) (κ : GNode G.tree → (Fin d → ℤ))
    (L : ℝ) (k : Mom d) (b : GBranch G.tree) :
    yNode (cosetDecoration G L k κ) b = latticePoint L (yNode κ b) := by
  simp only [yNode,cosetDecoration,WeylSums.latticePoint_sub_eq]
  abel

/-- The actual selected phase is exactly twice the Euclidean dot product
of its prescribed independent lattice variables, uniformly in root k. -/
theorem chosen_energy_integerLinkEquiv {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) (d : ℕ)
    (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ))
    (L : ℝ) (k : Mom d) (j : Fin Q.links.length) :
    omegaNode G (cosetDecoration G L k ((integerLinkEquiv hQ hG d).symm θ).val)
      (chosenBranch hQ j) = 2 * inner ℝ (latticePoint L (θ j).1) (latticePoint L (θ j).2) := by
  let κ := ((integerLinkEquiv hQ hG d).symm θ)
  have hp := integerLinkEquiv_symm_params hQ hG d θ
  have hx : xNode κ.val (chosenBranch hQ j) = (θ j).1 := by
    have h := congrArg Prod.fst (congrFun hp j)
    change xv (extend κ.val) (chosenBranch hQ j).val = (θ j).1 at h
    rwa [xv_extend] at h
  have hy : yNode κ.val (chosenBranch hQ j) = (θ j).2 := by
    have h := congrArg Prod.snd (congrFun hp j)
    change yv (extend κ.val) (chosenBranch hQ j).val = (θ j).2 at h
    rwa [yv_extend] at h
  rw [omegaNode_eq (isDecoration_coset κ.property.1 L k),xNode_coset,yNode_coset,hx,hy]

end WaveTurbulence.RegAsymp
