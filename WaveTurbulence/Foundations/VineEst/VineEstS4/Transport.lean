/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.InnerCL
public import WaveTurbulence.Foundations.Molecule.LFTwist.FamilyBatch

/-! # Transport of the chain region along an LF batch (V5 Step 4a)

`ChainAt S F` is a connected CL region `(U, a, b)` of the skeleton `S` containing every atom set of the core family `F`
with all lower joints below `a`.  A unit twist transports it (`ChainAt.next`): `U` by `twistedAtoms`, the joints by
`coreBranchEquiv`; the CL pattern is `clParentPattern_twistedAtoms_chain` and the invariants are carried by the
transport of the family (`CoreFamily.twist`).  `Reach` is `FamilyBatch` with this region carried along.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist TTree

variable {w : ℕ} {ι : Type*}

theorem internalPositions_mono (G : Garden w) {S T : Finset (GBranch G.tree)} (h : S ⊆ T) (v : GBranch G.tree)
    {i : Fin 4} (hi : i ∈ Mole.internalPositions G S v) : i ∈ Mole.internalPositions G T v := by
  obtain ⟨x, hx, hg, hp⟩ := (Mole.mem_internalPositions G).mp hi
  exact (Mole.mem_internalPositions G).mpr ⟨x, hx, ⟨h hg.1, h hg.2⟩, hp⟩

/-- A connected CL region of the skeleton `S` that contains the whole core family `F` (below its upper joint). -/
structure ChainAt (S : Garden w) (F : CoreFamily S ι) where
  U : Finset (GBranch S.tree)
  a : GBranch S.tree
  b : GBranch S.tree
  block : S.molecule.IsBlock U a b
  cl : Mole.CLParentPattern S U a b
  atoms_sub : ∀ j, F.atoms j ⊆ U
  lower_ne : ∀ j, (F.placement j).lower ≠ a

/-- The family after one operation (skip: unchanged; twist: transported). -/
@[expose] noncomputable def nextFam {S : Garden w} (F : CoreFamily S ι) (i : ι) :
    (ε : Bool) → CoreFamily (chosenSkeleton S (F.placement i) ε) ι
  | false => F
  | true => F.twist i

theorem nextFamily_eq (A : FamilyReconstruction w ι) (i : ι) (ε : Bool) :
    A.nextFamily i ε = nextFam A.family i ε := by
  cases ε <;> rfl

/-- Transport of the region along the operation `ε` at member `i`. -/
@[expose] noncomputable def ChainAt.next {S : Garden w} {F : CoreFamily S ι} (c : ChainAt S F) (i : ι) :
    (ε : Bool) → ChainAt (chosenSkeleton S (F.placement i) ε) (nextFam F i ε)
  | false => c
  | true =>
    { U := twistedAtoms S (F.placement i) c.U
      a := coreBranchEquiv S (F.placement i) c.a
      b := coreBranchEquiv S (F.placement i) c.b
      block := isBlock_twistedAtoms S (F.placement i) c.block
      cl := clParentPattern_twistedAtoms_chain S (F.placement i) c.block c.cl (c.lower_ne i).symm
        (internalPositions_mono S (c.atoms_sub i) _ (((F.designated i).2 (F.placement i).keep).mpr rfl))
      atoms_sub := fun j x hx => by
        obtain ⟨v, rfl⟩ := (coreBranchEquiv S (F.placement i)).surjective x
        exact (mem_twistedAtoms S (F.placement i) c.U v).mpr
          (c.atoms_sub j ((mem_twistedAtoms S (F.placement i) (F.atoms j) v).mp hx))
      lower_ne := fun j he => by
        have he' : (F.nextPlacement i j).lower = coreBranchEquiv S (F.placement i) c.a := he
        rw [F.nextPlacement_lower] at he'
        exact c.lower_ne j ((coreBranchEquiv S (F.placement i)).injective he') }


/-- The transport along the operation of a state, with the family as carried by `FamilyReconstruction.nextFamily`. -/
@[expose] noncomputable def ChainAt.nextA (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) (i : ι)
    (ε : Bool) : ChainAt (chosenSkeleton A.skeleton (A.family.placement i) ε) (A.nextFamily i ε) :=
  (nextFamily_eq A i ε).symm ▸ c.next i ε

/-- `FamilyBatch` with the chain region carried along (skip and untwisted operations keep it; a twist transports it). -/
inductive Reach (p : ℕ) (kind : Bool) :
    List ι → (A : FamilyReconstruction w ι) → ChainAt A.skeleton A.family →
      (B : FamilyReconstruction w ι) → ChainAt B.skeleton B.family → Prop
  | nil (A c) : Reach p kind [] A c A c
  | skip {L A c B c'} (i : ι) (h : Reach p kind L A c B c') : Reach p kind (i :: L) A c B c'
  | apply {L A c B c'} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i)
      (h : Reach p kind L op.output (ChainAt.nextA A c i op.choice) B c') : Reach p kind (i :: L) A c B c'

namespace Reach
variable {p : ℕ} {kind : Bool}

theorem batch {L : List ι} {A B : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family}
    {c' : ChainAt B.skeleton B.family} (h : Reach p kind L A c B c') :
    FamilyBatch p kind L A B := by
  induction h with
  | nil A c => exact .nil A
  | skip i h ih => exact .skip i ih
  | apply op h ih => exact .apply op ih

end Reach

/-- Every batch carries any chain region along. -/
theorem batch_reach {p : ℕ} {kind : Bool} {L : List ι} {A B : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B) (c : ChainAt A.skeleton A.family) :
    ∃ c' : ChainAt B.skeleton B.family, Reach p kind L A c B c' := by
  induction h with
  | nil A => exact ⟨c, .nil A c⟩
  | skip i h ih => obtain ⟨c', hc⟩ := ih c; exact ⟨c', .skip i hc⟩
  | apply op h ih => obtain ⟨c', hc⟩ := ih (ChainAt.nextA _ c _ op.choice); exact ⟨c', .apply op hc⟩

end WaveTurbulence.VineEstS4
