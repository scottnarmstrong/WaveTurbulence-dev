/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DartRelabelingNormalizedCount
import Mathlib.Tactic

/-! # Exact normalized-count equality under explicit admissibility reindexing -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem linkCountA_relabel_eq (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x,N.atom (f x) = M.atom x)
    (hm : ∀ x,N.mate (f x) = f (M.mate x)) (ho : ∀ x,N.out (f x) = M.out x)
    {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d) (P : Finset V → ℝ)
    (A : (D → (Fin d → ℤ)) → Prop) :
    appbLinkCountA M L γ δ C1 w A P =
      appbLinkCountA N L γ δ C1 w (fun ζ => A (ζ ∘ f)) P := by
  apply le_antisymm
  · apply linkCountA_le_of_dart_relabeling M N f hA ha hm ho
    intro κ hκ
    simpa only [relabelLabels,Function.comp_def,Equiv.symm_apply_apply] using hκ
  · have ha' (y : E) : M.atom (f.symm y) = N.atom y := by
      simpa only [f.apply_symm_apply] using (ha (f.symm y)).symm
    have hm' (y : E) : M.mate (f.symm y) = f.symm (N.mate y) :=
      (relabel_inverse_mate M N f hm y).symm
    have ho' (y : E) : M.out (f.symm y) = N.out y := by
      simpa only [f.apply_symm_apply] using (ho (f.symm y)).symm
    apply linkCountA_le_of_dart_relabeling N M f.symm hA.symm ha' hm' ho'
    intro ζ hζ
    exact hζ

end WaveTurbulence.Mole.AppbAlgorithm
