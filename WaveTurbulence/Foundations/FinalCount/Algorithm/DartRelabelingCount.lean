/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DartRelabeling
public import WaveTurbulence.Foundations.FinalCount.AppBFiniteCounts
import Mathlib.Tactic

/-! # The actual unrestricted-charge count transports under dart equivalence -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

noncomputable def relabelCountParameters (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hm : ∀ x,N.mate (f x) = f (M.mate x)) {d : ℕ} (p : AppbCountParameters M d) :
    AppbCountParameters N d where
  momentum := p.momentum
  energy := p.energy
  center := p.center ∘ f.symm
  center_mate := by
    intro y
    change p.center (f.symm (N.mate y)) = p.center (f.symm y)
    rw [relabel_inverse_mate M N f hm]
    exact p.center_mate _

/-- Admissibility is transported explicitly. This includes correlated
conditions and all zero/infinite cardinality cases, without division. -/
theorem countE_le_of_dart_relabeling (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x,N.atom (f x) = M.atom x)
    (hm : ∀ x,N.mate (f x) = f (M.mate x)) (ho : ∀ x,N.out (f x) = M.out x)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (A : (D → (Fin d → ℤ)) → Prop) (B : (E → (Fin d → ℤ)) → Prop)
    (hAB : ∀ κ,A κ → B (relabelLabels f κ)) :
    appbCountE M L γ δ w A ≤ appbCountE N L γ δ w B := by
  classical
  rw [appbCountE_eq_iSup]
  apply iSup_le
  intro p
  let pN := relabelCountParameters M N f hm p
  have hmap : Set.MapsTo (relabelLabels f) (p.decorations L γ δ w A) (pN.decorations L γ δ w B) := by
    intro κ hκ
    exact ⟨isDecoration_relabel M N f hA ha hm ho L w p.momentum κ hκ.1,
      isRestricted_relabel M N f hA ha ho L γ δ w p.energy p.center κ hκ.2.1,hAB κ hκ.2.2⟩
  have hh := Set.encard_le_encard_of_injOn hmap (relabelLabels_injective f).injOn
  apply hh.trans
  rw [appbCountE_eq_iSup]
  exact le_iSup (fun p : AppbCountParameters N d => (p.decorations L γ δ w B).encard) pN

end WaveTurbulence.Mole.AppbAlgorithm
