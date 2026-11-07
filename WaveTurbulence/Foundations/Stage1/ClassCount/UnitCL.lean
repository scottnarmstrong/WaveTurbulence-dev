/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitChain2
public import WaveTurbulence.Foundations.Molecule.BlockTypes
public import WaveTurbulence.Foundations.Molecule.BlockParent
import Mathlib.Tactic

/-!
# CLASSCOUNT: every ingredient of a (CL) vine chain is a (CL) vine, oriented from the upper to the lower joint

`ing_cl`: if `U` is a chain with `CLParentPattern G U a b` then each ingredient `A` with joints `x, y` (in chain order)
has `CLParentPattern G A x y`.  The proof peels off the last vine `T` (joints `b, c`): the parent of `c` lies in `T`
(`group_split` on the parent dart), so `block_parent_patterns` leaves only the pattern `CL(b, c)`; then the parent of the
joint `b` is not in `T`, hence in `S`, which gives `CL(S, a, b)` for the induction hypothesis.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole

variable {w : ℕ} {G : Garden w}

theorem intPar_of_union (hM : G.molecule.IsMolecule) {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hU : G.molecule.IsBlock (S ∪ T) a c)
    (hi : S ∩ T = {b}) (hbc : b ≠ c) (h : InternalParent G (S ∪ T) c) : InternalParent G T c := by
  obtain ⟨hne, hp⟩ := h
  have hcT : c ∈ T := hT.2.2.1
  let x : GardenDart G := Sum.inl (⟨c, hne⟩, false)
  have hxa : G.molecule.atom x = c := rfl
  have hxm : G.molecule.atom (G.molecule.mate x) = GNode.parent c.toNode hne := rfl
  have hx : G.molecule.InGroup (S ∪ T) x := by
    refine ⟨?_, ?_⟩
    · rw [hxa]; exact Finset.mem_union_right _ hcT
    · rw [hxm]; exact hp
  rcases group_split G.molecule hM hS hT hU hi x hx with h | h
  · exfalso
    have : c ∈ S ∩ T := Finset.mem_inter.mpr ⟨by have := h.1.1; rwa [hxa] at this, hcT⟩
    rw [hi, Finset.mem_singleton] at this
    exact hbc this.symm
  · refine ⟨hne, ?_⟩
    have := h.1.2
    rwa [hxm] at this

theorem cl_split (hM : G.molecule.IsMolecule) {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hU : G.molecule.IsBlock (S ∪ T) a c)
    (hi : S ∩ T = {b}) (hbc : b ≠ c) (hCL : CLParentPattern G (S ∪ T) a c) :
    CLParentPattern G T b c ∧ CLParentPattern G S a b := by
  have hcT := intPar_of_union hM hS hT hU hi hbc hCL.2
  have hTCL : CLParentPattern G T b c := by
    rcases block_parent_patterns G hT with h | h | h
    · exact h
    · exact absurd hcT h.1
    · exact absurd hcT h.2
  refine ⟨hTCL, ?_, ?_⟩
  · intro hpa
    exact hCL.1 ⟨hpa.1, Finset.mem_union_left _ hpa.2⟩
  · have hab : a ≠ b := hS.2.2.2.1
    have hbS : b ∈ S := hS.2.2.1
    have hdU : G.molecule.degIn (S ∪ T) b = 4 :=
      hU.2.2.2.2.2.2.2.2.1 b (Finset.mem_union_left _ hbS) hab.symm hbc
    obtain ⟨hne, hp⟩ := full_internal_has_parent G hdU
    refine ⟨hne, ?_⟩
    rcases Finset.mem_union.mp hp with h | h
    · exact h
    · exact absurd ⟨hne, h⟩ hTCL.1

/-- **Every ingredient of a (CL) chain is (CL), oriented in the chain order.** -/
theorem ing_cl (hM : G.molecule.IsMolecule) {U A : Finset (GBranch G.tree)} {a b x y : GBranch G.tree} {n : ℕ}
    (h : Vine.ChainIngredient G.molecule U a b n A x y) :
    G.molecule.IsBlock U a b → CLParentPattern G U a b → CLParentPattern G A x y := by
  induction h with
  | single hv => intro _ hCL; exact hCL
  | @append_left S T A a b c x y n hI hT hi hne ih =>
    intro hU hCL
    obtain ⟨Y, hY⟩ := hT
    have hSpec := Vine.chainIngredient_spec hI
    have hBS := chain_prefix_isBlock G.molecule hM hSpec.1 hY hi hU
    have hbc : b ≠ c := hY.1.2.2.2.1
    exact ih hBS (cl_split hM hBS hY.1 hU hi hbc hCL).2
  | @append_last S T a b c n hS hT hi hne =>
    intro hU hCL
    obtain ⟨Y, hY⟩ := hT
    have hBS := chain_prefix_isBlock G.molecule hM hS hY hi hU
    have hbc : b ≠ c := hY.1.2.2.2.1
    exact (cl_split hM hBS hY.1 hU hi hbc hCL).1

end WaveTurbulence.ClassCount
