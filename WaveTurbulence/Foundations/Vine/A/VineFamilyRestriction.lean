/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFamilyReindex
/-! Restrict actual LF families to injectively selected coordinates. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 Twist LFTwist
variable {w p : ℕ} {kind : Bool} {G : Garden w} {ι κ : Type*}

/-- A subfamily keeps all original geometry, including chosen placements. -/
def familyRestrict (F : CoreFamily G ι) (e : κ → ι) (he : Function.Injective e) : CoreFamily G κ where
  kind j := F.kind (e j)
  atoms j := F.atoms (e j)
  upper j := F.upper (e j)
  placement j := F.placement (e j)
  core j := F.core (e j)
  designated j := F.designated (e j)
  separated j k hjk := F.separated (e j) (e k) (he.ne hjk)

/-- Restriction leaves the actual reconstructed garden and replacements unchanged. -/
def stateRestrict (A : FamilyReconstruction w ι) (e : κ → ι) (he : Function.Injective e) :
    FamilyReconstruction w κ :=
  ⟨A.skeleton, familyRestrict A.family e he, A.plain, A.data, A.layered, A.decodes⟩

/-- Restriction transports all exact placement fields through an active subfamily twist. -/
theorem nextPlacement_restrict (F : CoreFamily G ι) (e : κ → ι) (he : Function.Injective e) (i j : κ) :
    (familyRestrict F e he).nextPlacement i j = F.nextPlacement (e i) (e j) := by
  apply CorePlacement.ext_data
  · rw [CoreFamily.nextPlacement_lower, CoreFamily.nextPlacement_lower]
    rfl
  · rw [CoreFamily.nextPlacement_retained, CoreFamily.nextPlacement_retained]
    rfl
  · rw [CoreFamily.nextPlacement_keep, CoreFamily.nextPlacement_keep]
    rfl

/-- A subfamily twist is the restriction of the same full-family twist. -/
theorem familyRestrict_twist (F : CoreFamily G ι) (e : κ → ι) (he : Function.Injective e) (i : κ) :
    (familyRestrict F e he).twist i = familyRestrict (F.twist (e i)) e he := by
  apply CoreFamily.ext_data
  · rfl
  · rfl
  · rfl
  · exact funext (nextPlacement_restrict F e he i)

/-- Both LF skeleton choices commute with restriction. -/
theorem nextFamily_restrict (A : FamilyReconstruction w ι) (e : κ → ι) (he : Function.Injective e)
    (i : κ) (ε : Bool) :
    (stateRestrict A e he).nextFamily i ε = familyRestrict (A.nextFamily (e i) ε) e he := by
  cases ε
  · rfl
  · exact familyRestrict_twist A.family e he i

/-- Every actual subfamily operation is an operation of its full family. -/
def operationLiftAt {A : FamilyReconstruction w ι} (e : κ → ι) (he : Function.Injective e) (i : κ)
    (op : FamilyOperation (p := p) (kind := kind) (stateRestrict A e he) i) :
    FamilyOperation (p := p) (kind := kind) A (e i) where
  canonical := op.canonical
  eligible := op.eligible
  treeCoherent := op.treeCoherent
  coupleCoherent := op.coupleCoherent
  choice := op.choice
  construction := op.construction

/-- Lifting an operation retains its entire actual subfamily output. -/
theorem operationLiftAt_output {A : FamilyReconstruction w ι} (e : κ → ι) (he : Function.Injective e) (i : κ)
    (op : FamilyOperation (p := p) (kind := kind) (stateRestrict A e he) i) :
    stateRestrict (operationLiftAt e he i op).output e he = op.output := by
  apply familyReconstruction_ext
  · rfl
  · exact heq_of_eq (nextFamily_restrict A e he i op.choice).symm
  · rfl
  · rfl

end WaveTurbulence.VineA
