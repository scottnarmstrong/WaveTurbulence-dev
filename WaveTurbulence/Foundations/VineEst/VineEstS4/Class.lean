/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Kernel

/-! # The twist class of a vine chain and its sections (V5 Step 4a)

`ClassSectionK p kind A c Z`: `Z` is a finite set of (state, chain region) pairs, each reached from `(A, c)` by a
once-per-member LF batch over all core members (`Reach`), whose layered gardens are pairwise distinct and exactly the
class `A.allCoreOutputs` (M7; S1's `congruent_layered_iff`).  `exists_classSection` shows sections exist (so the
statement `VineEstFull` is not vacuous); with no available operation the only section is the start (`BaseCase`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The state of `(G, RD, layer)` with the core family of the pieces of the chain. -/
@[expose] noncomputable def startState (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) :
    FamilyReconstruction w (assemblySourceFamily B).CoreIndex where
  skeleton := G
  family := (assemblySourceFamily B).coreFamily
  plain := hG
  data := RD
  layered := layeredReconstruction RD hG layer hLayer
  decodes := RD.garden_decodes hG

/-- The chain region of the assembly, as a region of the start state. -/
@[expose] noncomputable def chainStart (B : CLChainAssembly G R n) : ChainAt G (assemblySourceFamily B).coreFamily where
  U := U
  a := a
  b := b
  block := B.isBlock
  cl := R.parentPattern
  atoms_sub := fun i => assemblyPiece_subset B i.1
  lower_ne := fun i => by
    have h1 := ((assemblySourceFamily B).corePlacement_at i).1
    change ((assemblySourceFamily B).corePlacement i).lower ≠ a
    rw [h1]
    exact (Finset.mem_erase.mp (lower_mem_interior B i.1)).1

/-- A set of representatives, one per garden of the twist class. -/
@[expose] def ClassSectionK (p : ℕ) (kind : Bool) {ι : Type*} [Fintype ι] (A : FamilyReconstruction w ι)
    (c : ChainAt A.skeleton A.family)
    (Z : Finset (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family)) : Prop :=
  (∀ x ∈ Z, ∃ M : List ι, M.Perm Finset.univ.toList ∧ Reach p kind M A c x.1 x.2) ∧
  Set.InjOn (fun x => x.1.layered) (Z : Set (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family)) ∧
  (fun x => x.1.layered) '' (Z : Set (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family)) =
    A.allCoreOutputs (p := p) (kind := kind)

section Finite
variable {ι : Type*} {p : ℕ} {kind : Bool}

theorem batch_eq_of_not_canonical {L : List ι} {A B : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B) (hc : ¬ CanonicalObject p kind A.layered) : B = A := by
  induction h with
  | nil => rfl
  | skip i h ih => exact ih hc
  | apply op h ih => exact absurd op.canonical hc

theorem allCoreOutputs_finite [Fintype ι] (A : FamilyReconstruction w ι) :
    (A.allCoreOutputs (p := p) (kind := kind)).Finite := by
  by_cases hc : CanonicalObject p kind A.layered
  · exact A.outputs_finite _ hc
  · refine (Set.finite_singleton A.layered).subset ?_
    rintro LH ⟨M, B, _, hB, rfl⟩
    rw [batch_eq_of_not_canonical hB hc]
    rfl

end Finite

/-- Sections exist: choose one batch witness per garden of the (finite) class. -/
theorem exists_classSection (p : ℕ) (kind : Bool) {ι : Type*} [Fintype ι] (A : FamilyReconstruction w ι)
    (c : ChainAt A.skeleton A.family) : ∃ Z, ClassSectionK p kind A c Z := by
  classical
  have hfin := allCoreOutputs_finite (p := p) (kind := kind) A
  have hex : ∀ LH ∈ A.allCoreOutputs (p := p) (kind := kind), ∃ x : (Σ Bs : FamilyReconstruction w ι,
      ChainAt Bs.skeleton Bs.family), x.1.layered = LH ∧ ∃ M : List ι, M.Perm Finset.univ.toList ∧
        Reach p kind M A c x.1 x.2 := by
    rintro LH ⟨M, B, hM, hB, rfl⟩
    obtain ⟨c', hc'⟩ := batch_reach hB c
    exact ⟨⟨B, c'⟩, rfl, M, hM, hc'⟩
  haveI : Nonempty (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family) := ⟨⟨A, c⟩⟩
  choose! f hf using hex
  refine ⟨hfin.toFinset.image f, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨LH, hLH, rfl⟩ := Finset.mem_image.mp hx
    exact (hf LH (hfin.mem_toFinset.mp hLH)).2
  · intro x hx y hy hxy
    obtain ⟨LH, hLH, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨LH', hLH', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    have h1 := (hf LH (hfin.mem_toFinset.mp hLH)).1
    have h2 := (hf LH' (hfin.mem_toFinset.mp hLH')).1
    have : LH = LH' := h1.symm.trans (hxy.trans h2)
    rw [this]
  · ext LH
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨LH', hLH', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      have h := hf LH' (hfin.mem_toFinset.mp hLH')
      show (f LH').1.layered ∈ _
      rw [h.1]
      exact hfin.mem_toFinset.mp hLH'
    · intro hLH
      exact ⟨f LH, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨LH, hfin.mem_toFinset.mpr hLH, rfl⟩),
        (hf LH hLH).1⟩

end WaveTurbulence.VineEstS4
