/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Low
public import WaveTurbulence.Foundations.GammaLow.FinalCount.NamedInputs
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.Main
public import WaveTurbulence.Foundations.Molecule.ConnectedGeometryBridge
public import WaveTurbulence.Foundations.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.FinalCount.AsmVN13
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.VCMember
public import WaveTurbulence.Foundations.TVine.Struct.SubObjBridge
/-! # H: the low-family API of the ported run (packet L6, item H; hand-written)

Every module of `H/` (the port of main's stage-2 run over the fixed low family `Src.γL`, PLAN-L6 §3c–3d) imports this
module. In the low range a family member is a vine of type (I) or (II) or a T-vine (`Src.isSomeVine_low_iff`), so
main's proofs that destructure `∃ X : VineType, M.IsVine X S a b` and use only the block part `hX.1` go through
`Src.IsSomeVine.blk`, whose first component is the block. A drawn vine of another type is a member through N2
Lemma 5.2, proved by L3D (`TVine.Struct.Drawn.drawnTVine`); `isSomeVine_of_isVine'` uses it directly. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.Src
open Finset

universe u v

section api
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V}
  {a b : V}

/-- The low family over `γL` is the enlarged family. -/
theorem isSomeVine_γL_iff : IsSomeVine γL M S a b ↔ M.IsVineEnl S a b := isSomeVine_low_iff γL_le

theorem IsSomeVine.block {γ : ℝ} (h : IsSomeVine γ M S a b) : M.IsBlock S a b := isBlock_of_isSomeVine h

/-- The two joints of a family member are distinct members of its atom set. -/
theorem IsSomeVine.ends {γ : ℝ} (h : IsSomeVine γ M S a b) : a ∈ S ∧ b ∈ S ∧ a ≠ b :=
  ⟨h.block.2.1, h.block.2.2.1, h.block.2.2.2.1⟩

/-- The atomic group of a family member is connected. -/
theorem IsSomeVine.connected {γ : ℝ} (h : IsSomeVine γ M S a b) : M.GroupConnected S :=
  h.block.2.2.2.2.2.2.2.2.2

/-- Connectivity of a family member in its induced molecule (main's `Vine.GroupConnected`; main's
`isVine_connected` for the drawn types). -/
theorem IsSomeVine.vconnected {γ : ℝ} (h : IsSomeVine γ M S a b) : Vine.GroupConnected M S :=
  (Molecpl.connected_to_induced M ⟨a, h.ends.1⟩ h.connected).2

/-- Blocks are symmetric in their joints. -/
theorem isBlock_swap' (h : M.IsBlock S a b) : M.IsBlock S b a :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.1.symm, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    fun v hv h1 h2 => h.2.2.2.2.2.2.2.2.1 v hv h2 h1, h.2.2.2.2.2.2.2.2.2⟩

/-- T-vines are symmetric in their joints (L4's bridge `TVine.Core.isTVine_iff` and L3D's `isTVineU_swap`). -/
theorem isTVine_swap (h : M.IsTVine S a b) : M.IsTVine S b a := by
  rw [TVine.Core.isTVine_iff M] at h ⊢
  exact ⟨isBlock_swap' h.1, TVine.Struct.Drawn.isTVineU_swap h.2⟩

theorem isSomeVine_of_I (h : M.IsVine .I S a b) : IsSomeVine γL M S a b := isSomeVine_γL_iff.mpr (Or.inl h)

theorem isSomeVine_of_II (h : M.IsVine .II S a b) : IsSomeVine γL M S a b :=
  isSomeVine_γL_iff.mpr (Or.inr (Or.inl h))

theorem isSomeVine_of_T (h : M.IsTVine S a b) : IsSomeVine γL M S a b :=
  isSomeVine_γL_iff.mpr (Or.inr (Or.inr h))

/-- Case analysis of a family member: type (I), type (II), or a T-vine. -/
theorem IsSomeVine.cases (h : IsSomeVine γL M S a b) :
    M.IsVine .I S a b ∨ M.IsVine .II S a b ∨ M.IsTVine S a b := isSomeVine_γL_iff.mp h

/-- Family members over `γL` are symmetric in their joints (main's `isVine_swap` at (I), (II); `isTVine_swap`). -/
theorem IsSomeVine.swap (h : IsSomeVine γL M S a b) : IsSomeVine γL M S b a := by
  rcases h.cases with h | h | h
  · exact isSomeVine_of_I (FinalCountAsm.isVine_swap h)
  · exact isSomeVine_of_II (FinalCountAsm.isVine_swap h)
  · exact isSomeVine_of_T (isTVine_swap h)

/-- N2 Thm 1.15 (F1) at the molecule level (L3's `TVine.Struct.f1_mol`), in L3D's input shape. -/
theorem tvineF1 : TVine.Struct.Drawn.VC.TVineF1Input.{u, v} := fun _ _ _ _ hT => TVine.Struct.f1_mol hT

/-- A family member stays connected after deleting any one atom (main's `isVine_erase_connected`; L3D's
`member_erase_connected` with (F1) by L3). -/
theorem IsSomeVine.erase_connected {γ : ℝ} (h : IsSomeVine γ M S a b) (z : V) : Vine.GroupConnected M (S.erase z) :=
  TVine.Struct.Drawn.VC.member_erase_connected tvineF1 h z

/-- The interior of a family member is connected (main's `isVine_interior_connected`; L3D, (F1) by L3). -/
theorem IsSomeVine.interior_connected {γ : ℝ} (h : IsSomeVine γ M S a b) : Vine.GroupConnected M (S \ {a, b}) :=
  TVine.Struct.Drawn.VC.member_interior_connected tvineF1 h

end api

/-- **The named inputs of the ported run, on molecules with atom type `V` and dart type `D`** (a `Prop` class, so that
instance resolution threads them). It is the merge point of the layers' input classes at the gate (PLAN-L6 §3f) and
currently has no fields: N2 Lemma 5.2 is proved (L3D) and is used directly. -/
class HInputs (V : Type u) (D : Type v) : Prop

instance (V : Type u) (D : Type v) : HInputs V D := ⟨⟩

section inputs
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V}
  {a b : V}

end inputs

end WaveTurbulence.GammaLow.FinalCount.Src
