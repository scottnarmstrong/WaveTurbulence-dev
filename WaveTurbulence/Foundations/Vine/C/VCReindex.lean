/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp7Comb

/-! # VINE-C: restricting an LF state to the members of one unit

For an injective `e : κ → ι`, `famComap F e he` is the sub-family of the members `e k` of a core family `F`, and
`stComap A e he` the state `A` with its family restricted (same skeleton, data and layered garden).  An LF operation at the
member `e k` of `A` is literally an operation at `k` of `stComap A e he` (`opComap`, `opLift`, all fields are shared), and
the outputs correspond (`opComap_output`): restriction commutes with the transport of the family by a unit twist
(`famComap_twist`).  Batches over `N.map e` correspond to batches over `N` (`batch_comap`, `batch_lift`), and the member
signatures of V5 (`sigStar`) are read through the restriction (`sigStar_comap`, by `rfl`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineC
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 TTree

variable {w : ℕ} {ι κ : Type*}

/-- The sub-family of the members in the image of an injective map. -/
@[expose] def famComap {G : Garden w} (F : CoreFamily G ι) (e : κ → ι) (he : Function.Injective e) :
    CoreFamily G κ where
  kind k := F.kind (e k)
  atoms k := F.atoms (e k)
  upper k := F.upper (e k)
  placement k := F.placement (e k)
  core k := F.core (e k)
  designated k := F.designated (e k)
  separated k k' h := F.separated (e k) (e k') (he.ne h)

theorem coreFamily_ext {G : Garden w} {F F' : CoreFamily G κ} (hk : F.kind = F'.kind) (ha : F.atoms = F'.atoms)
    (hu : F.upper = F'.upper) (hp : F.placement = F'.placement) : F = F' := by
  cases F; cases F'
  dsimp only at hk ha hu hp
  subst hk ha hu hp
  rfl

theorem famComap_nextPlacement {G : Garden w} (F : CoreFamily G ι) (e : κ → ι) (he : Function.Injective e) (k j : κ) :
    F.nextPlacement (e k) (e j) = (famComap F e he).nextPlacement k j := by
  classical
  by_cases hjk : j = k
  · subst hjk
    unfold CoreFamily.nextPlacement
    rw [dite_eq_left rfl, dite_eq_left rfl]
    rfl
  · have hne : e j ≠ e k := he.ne hjk
    unfold CoreFamily.nextPlacement
    rw [dite_eq_right hne, dite_eq_right hjk]
    rfl

/-- Restriction commutes with the transport of the family by a unit twist at a member of the image. -/
theorem famComap_twist {G : Garden w} (F : CoreFamily G ι) (e : κ → ι) (he : Function.Injective e) (k : κ) :
    famComap (F.twist (e k)) e he = (famComap F e he).twist k :=
  coreFamily_ext rfl rfl rfl (funext fun j => famComap_nextPlacement F e he k j)

/-- The state with its family restricted to the members in the image of `e`. -/
@[expose] def stComap (A : FamilyReconstruction w ι) (e : κ → ι) (he : Function.Injective e) :
    FamilyReconstruction w κ where
  skeleton := A.skeleton
  family := famComap A.family e he
  plain := A.plain
  data := A.data
  layered := A.layered
  decodes := A.decodes

section Ops
variable {p : ℕ} {kind : Bool} (e : κ → ι) (he : Function.Injective e)

/-- An operation at a member of the image is an operation of the restricted state. -/
@[expose] def opComap {A : FamilyReconstruction w ι} {k : κ} (op : FamilyOperation (p := p) (kind := kind) A (e k)) :
    FamilyOperation (p := p) (kind := kind) (stComap A e he) k :=
  ⟨op.canonical, op.eligible, op.treeCoherent, op.coupleCoherent, op.choice, op.construction⟩

/-- An operation of the restricted state is an operation at the corresponding member. -/
@[expose] def opLift {A : FamilyReconstruction w ι} {k : κ} (op : FamilyOperation (p := p) (kind := kind) (stComap A e he) k) :
    FamilyOperation (p := p) (kind := kind) A (e k) :=
  ⟨op.canonical, op.eligible, op.treeCoherent, op.coupleCoherent, op.choice, op.construction⟩

theorem nextFamily_comap (A : FamilyReconstruction w ι) (k : κ) (ε : Bool) :
    famComap (A.nextFamily (e k) ε) e he = (stComap A e he).nextFamily k ε := by
  cases ε
  · rfl
  · exact famComap_twist A.family e he k

/-- **The outputs correspond.** -/
theorem opComap_output {A : FamilyReconstruction w ι} {k : κ} (op : FamilyOperation (p := p) (kind := kind) A (e k)) :
    (opComap e he op).output = stComap op.output e he := by
  obtain ⟨c, el, tc, cc, ε, con⟩ := op
  show FamilyReconstruction.mk _ ((stComap A e he).nextFamily k ε) _ _ _ _ =
    FamilyReconstruction.mk _ (famComap (A.nextFamily (e k) ε) e he) _ _ _ _
  rw [nextFamily_comap e he A k ε]
  rfl

theorem opLift_output {A : FamilyReconstruction w ι} {k : κ}
    (op : FamilyOperation (p := p) (kind := kind) (stComap A e he) k) :
    op.output = stComap (opLift e he op).output e he :=
  opComap_output e he (opLift e he op)

/-- A batch of the restricted state lifts to a batch over `N.map e`. -/
theorem batch_lift {N : List κ} {X' Y' : FamilyReconstruction w κ} (h : FamilyBatch p kind N X' Y') :
    ∀ {X : FamilyReconstruction w ι}, stComap X e he = X' →
      ∃ Y, FamilyBatch p kind (N.map e) X Y ∧ stComap Y e he = Y' := by
  induction h with
  | nil A =>
    intro X hX
    exact ⟨X, .nil X, hX⟩
  | skip i h ih =>
    intro X hX
    obtain ⟨Y, hY, hY'⟩ := ih hX
    exact ⟨Y, .skip (e i) hY, hY'⟩
  | @apply L A B i op h ih =>
    intro X hX
    subst hX
    obtain ⟨Y, hY, hY'⟩ := ih (opLift_output e he op).symm
    exact ⟨Y, .apply (opLift e he op) hY, hY'⟩

end Ops

end WaveTurbulence.VineC
