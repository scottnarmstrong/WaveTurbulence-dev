/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepNode3
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the assembled superposition of the skeleton integrand (definitions)

The index is `Ξ = (∀ s, Λ_s) × (GBranch → ℤ^d)`: a mode of every replacement slot and a node centre assignment.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

/-- The assembled index. -/
abbrev XiT (fam : SlotFam S d) : Type := (∀ s, fam.Λ s) × (GBranch S.tree → Fin d → ℤ)

/-- The normalised amplitude of slot `s` at the assembled mode (tree slots carry the node partition of unity). -/
noncomputable def ampS (fam : SlotFam S d) (Cχ : ℝ) (ξ : XiT fam) :
    ∀ s : ReplacementSlot S, Mom d → ℂ
  | Sum.inl p => fam.a (Sum.inl p) (ξ.1 (Sum.inl p))
  | Sum.inr b => fun k => fam.a (Sum.inr b) (ξ.1 (Sum.inr b)) k * (chiC d (ξ.2 b) k / (Cχ : ℂ))

/-- The unit-ball centre of slot `s` at the assembled mode. -/
noncomputable def cenS (fam : SlotFam S d) (ξ : XiT fam) : ReplacementSlot S → Mom d
  | Sum.inl p => latPt d (fam.n (Sum.inl p) (ξ.1 (Sum.inl p)))
  | Sum.inr b => latPt d (ξ.2 b)

/-- The total frequency at the clock source `y`. -/
noncomputable def modeFreq (fam : SlotFam S d) (hS : S.IsPlain) (ξ : XiT fam) (y : ClkSrc S) : ℝ :=
  ∑ s, ∑ i, if argSrc hS s i = y then (fam.m s (ξ.1 s) i : ℝ) else 0

open scoped Classical in
/-- The constant integer momentum of a slot without bond. -/
noncomputable def kconstInt (hS : S.IsPlain) {d : ℕ} (roots : Fin w → Fin d → ℤ) (s : ReplacementSlot S) :
    Fin d → ℤ :=
  Classical.epsilon fun v => ∀ z : GNode S.tree → Fin d → ℤ,
    (∀ ℓ : GLeaf S.tree, z ℓ.toNode = z (S.pair ℓ).toNode) → (∀ j, z (GNode.root S.tree j) = roots j) →
      z (slotNode hS s) = v

theorem exists_const_of_not_hasBond (hS : S.IsPlain) {d : ℕ} (roots : Fin w → Fin d → ℤ)
    (s : ReplacementSlot S) (hs : ¬ hasBond hS s) :
    ∃ v : Fin d → ℤ, ∀ z : GNode S.tree → Fin d → ℤ,
      (∀ ℓ : GLeaf S.tree, z ℓ.toNode = z (S.pair ℓ).toNode) → (∀ j, z (GNode.root S.tree j) = roots j) →
        z (slotNode hS s) = v := by
  rcases s with p | b
  · simp only [hasBond, not_and_or, not_not] at hs
    rcases hs with h1 | h2
    · refine ⟨roots (p.firstLeaf hS).1.1, fun z _ hr => ?_⟩
      have : (p.firstLeaf hS).toNode = GNode.root S.tree (p.firstLeaf hS).1.1 :=
        Subtype.ext (Prod.ext rfl h1)
      show z (p.firstLeaf hS).toNode = _
      rw [this, hr]
    · refine ⟨roots (p.secondLeaf hS).1.1, fun z hz hr => ?_⟩
      have h3 : (p.secondLeaf hS).toNode = GNode.root S.tree (p.secondLeaf hS).1.1 :=
        Subtype.ext (Prod.ext rfl h2)
      show z (p.firstLeaf hS).toNode = _
      have := hz (p.secondLeaf hS)
      rw [pair_second] at this
      rw [← this, h3, hr]
  · simp only [hasBond, not_not] at hs
    refine ⟨roots b.1.1, fun z _ hr => ?_⟩
    have : b.toNode = GNode.root S.tree b.1.1 := Subtype.ext (Prod.ext rfl hs)
    show z b.toNode = _
    rw [this, hr]

theorem kconstInt_spec (hS : S.IsPlain) {d : ℕ} (roots : Fin w → Fin d → ℤ) (s : ReplacementSlot S)
    (hs : ¬ hasBond hS s) (z : GNode S.tree → Fin d → ℤ)
    (hz : ∀ ℓ : GLeaf S.tree, z ℓ.toNode = z (S.pair ℓ).toNode)
    (hr : ∀ j, z (GNode.root S.tree j) = roots j) : z (slotNode hS s) = kconstInt hS roots s := by
  classical
  exact Classical.epsilon_spec (exists_const_of_not_hasBond hS roots s hs) z hz hr

end WaveTurbulence.Represents
