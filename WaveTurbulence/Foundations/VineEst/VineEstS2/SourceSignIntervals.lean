/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.ColorIntervalCharge
public import WaveTurbulence.Foundations.WaveB.Lemmas

/-! # The two-color charge bound on actual tree ancestors -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree

def signColor (ζ : ℤˣ) : Bool := decide ((ζ : ℤ) = 1)

theorem signColor_injective : Function.Injective signColor := by
  intro x y he
  rcases Int.units_eq_one_or x with rfl | rfl
  · rcases Int.units_eq_one_or y with rfl | rfl
    · rfl
    · exact Bool.noConfusion (show true = false from he)
  · rcases Int.units_eq_one_or y with rfl | rfl
    · exact Bool.noConfusion (show false = true from he)
    · rfl

theorem ancestors_comparable {w : ℕ} {tree : Fin w → TTree} {a b x : GNode tree}
    (ha : a.IsDesc x) (hb : b.IsDesc x) : a.IsDesc b ∨ b.IsDesc a := by
  have he : a.1.1 = b.1.1 := ha.1.trans hb.1.symm
  rcases List.prefix_or_prefix_of_prefix ha.2 hb.2 with h | h
  · exact Or.inl ⟨he,h⟩
  · exact Or.inr ⟨he.symm,h⟩

/-- At most two actual source branches can start sign-skipping intervals
covering a fixed branch. Restricting to heavy-child paths preserves this bound. -/
theorem card_sourceSignInterval_starts_le_two {w : ℕ} {tree : Fin w → TTree}
    (sig : Fin w → ℤˣ) (v : GBranch tree) (S : Finset (GBranch tree))
    (hS : ∀ u ∈ S, ColorInterval (fun a b : GBranch tree => a.toNode.IsDesc b.toNode)
      (fun a => signColor (nodeSign sig a.1)) u v) : S.card ≤ 2 := by
  classical
  apply card_colorInterval_starts_le_two _ _ v S ?_ hS
  intro a b ha hb
  exact ancestors_comparable ha hb

end WaveTurbulence.VineEstS2
