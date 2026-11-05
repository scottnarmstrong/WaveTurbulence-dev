/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CollapsedTwistForest

/-! # Transporting an actual garden pairing through a leaf bijection

This general constructor records the sign multipliers explicitly. A
multiplier constant on each paired pair preserves the garden axioms.
The unit-twist producer must prove these premises from the actual surgery.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (F : Fin w → TTree) (sig : Fin w → ℤˣ)

/-- Transport the actual pairing and marks, with an explicit pair-invariant sign multiplier. -/
@[expose] noncomputable def transportGardenPairing (e : GLeaf G.tree ≃ GLeaf F)
    (ε : GLeaf G.tree → ℤˣ) (hε : ∀ l, ε (G.pair l) = ε l)
    (hsign : ∀ l, nodeSign sig (e l).1 = ε l * G.sign l.toNode) : Garden w where
  sig := sig
  tree := F
  pair l := e (G.pair (e.symm l))
  mark l := G.mark (e.symm l)
  pair_pair l := by simp only [Equiv.symm_apply_apply,G.pair_pair,Equiv.apply_symm_apply]
  pair_eq_iff l := by
    constructor
    · intro he
      have hh : G.pair (e.symm l) = e.symm l := by
        have hh := congrArg e.symm he
        simpa only [Equiv.symm_apply_apply] using hh
      exact (G.pair_eq_iff _).mp hh
    · intro hm
      rw [(G.pair_eq_iff _).mpr hm,Equiv.apply_symm_apply]
  pair_sign l hl := by
    let old := e.symm l
    have hne : G.pair old ≠ old := by
      intro he
      apply hl
      change e (G.pair old) = l
      rw [he]
      exact e.apply_symm_apply l
    have hs := G.pair_sign old hne
    have h1 := hsign (G.pair old)
    have h2 := hsign old
    change nodeSign sig (e (G.pair old)).1 = -nodeSign sig l.1
    rw [h1,hε]
    change ε old * nodeSign G.sig (G.pair old).1 = -nodeSign sig l.1
    rw [hs]
    have hh : nodeSign sig l.1 = ε old * nodeSign G.sig old.1 := by
      simpa only [old,Equiv.apply_symm_apply,Garden.sign,GLeaf.toNode] using h2
    rw [hh,mul_neg]

/-- Actual pairing conjugacy in the transported garden. -/
theorem transportGardenPairing_pair (e : GLeaf G.tree ≃ GLeaf F)
    (ε : GLeaf G.tree → ℤˣ) (hε : ∀ l, ε (G.pair l) = ε l)
    (hsign : ∀ l, nodeSign sig (e l).1 = ε l * G.sign l.toNode) (l : GLeaf G.tree) :
    (transportGardenPairing G F sig e ε hε hsign).pair (e l) = e (G.pair l) := by
  change e (G.pair (e.symm (e l))) = _
  rw [Equiv.symm_apply_apply]

/-- Plainness is preserved by the concrete pairing transport. -/
theorem transportGardenPairing_plain (e : GLeaf G.tree ≃ GLeaf F)
    (ε : GLeaf G.tree → ℤˣ) (hε : ∀ l, ε (G.pair l) = ε l)
    (hsign : ∀ l, nodeSign sig (e l).1 = ε l * G.sign l.toNode) (hplain : G.IsPlain) :
    (transportGardenPairing G F sig e ε hε hsign).IsPlain := by
  intro l
  exact hplain (e.symm l)

end WaveTurbulence.Twist
