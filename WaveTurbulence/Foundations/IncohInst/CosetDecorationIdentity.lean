/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.DecorationEquivalences
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Frozen.Defs.LatticePoint

/-! # The C2 real link decoration is exactly B1's original lattice coset decoration -/

public section
noncomputable section
namespace WaveTurbulence.IncohInst
open Links

/-- The frozen lattice embedding is an additive homomorphism at every real scale. -/
@[expose] def latticePointHom (d : ℕ) (L : ℝ) : (Fin d → ℤ) →+ Mom d where
  toFun := latticePoint L
  map_zero' := by ext j; simp [latticePoint]
  map_add' a b := by ext j; simp [latticePoint, Int.cast_add, add_div]

/-- Exact couple coset identity, retaining the original root momentum. -/
theorem couple_decOfParams_eq_coset {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    {d : ℕ} (L : ℝ) (k : Mom d) (p : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) :
    (decOfParams hQ k (fun j => (latticePoint L (p j).1, latticePoint L (p j).2))).1 =
      cosetDecoration G L k (decOfParams hQ (0 : Fin d → ℤ) p).1 := by
  funext a
  obtain ⟨A, B, hAB⟩ := node_linear hQ a
  rw [hAB]
  change k + _ = k + latticePointHom d L ((decOfParams hQ (0 : Fin d → ℤ) p).1 a)
  rw [hAB, zero_add, map_sum]
  simp only [map_add, map_zsmul]
  rfl

/-- Exact paired-tree coset identity; in particular the lone leaf still equals the root. -/
theorem tree_decOfParams_eq_coset {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {d : ℕ} (L : ℝ) (k : Mom d)
    (p : Fin (X.treeLinks (G.sig 0)).length → (Fin d → ℤ) × (Fin d → ℤ)) :
    (treeDecOfParams hX k (fun j => (latticePoint L (p j).1, latticePoint L (p j).2))).1 =
      cosetDecoration G L k (treeDecOfParams hX (0 : Fin d → ℤ) p).1 := by
  funext a
  obtain ⟨A, B, hAB⟩ := tree_node_linear hX a
  rw [hAB]
  change k + _ = k + latticePointHom d L ((treeDecOfParams hX (0 : Fin d → ℤ) p).1 a)
  rw [hAB, zero_add, map_sum]
  simp only [map_add, map_zsmul]
  rfl

end WaveTurbulence.IncohInst
