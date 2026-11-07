/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.Molecule.TwistPrime
/-! VINE-A2: a composed actual molecule isomorphism for every LF batch,
and preservation of prime skeletons. Both canonical object kinds are retained. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.LFTwist
open WaveTurbulence.Reg.Skeleton

/-- Identity on actual atom and dart carriers. -/
def molIsoRefl {w : ℕ} (G : Garden w) : MolIso G.molecule G.molecule where
  e := Equiv.refl _
  d := Equiv.refl _
  atoms_iff _ := Iff.rfl
  atom_comm _ := rfl
  mate_comm _ := rfl
  out_comm _ := rfl

/-- Compose actual molecule isomorphisms, retaining the atom/dart maps. -/
def molIsoTrans {w : ℕ} {G H K : Garden w} (F : MolIso G.molecule H.molecule)
    (J : MolIso H.molecule K.molecule) : MolIso G.molecule K.molecule where
  e := F.e.trans J.e
  d := F.d.trans J.d
  atoms_iff v := (J.atoms_iff (F.e v)).trans (F.atoms_iff v)
  atom_comm x := (J.atom_comm (F.d x)).trans (congrArg J.e (F.atom_comm x))
  mate_comm x := (J.mate_comm (F.d x)).trans (congrArg J.d (F.mate_comm x))
  out_comm x := (J.out_comm (F.d x)).trans (F.out_comm x)

/-- Both permitted skeleton choices give the literal S1 atom/dart transport. -/
noncomputable def chosenMolIso {w : ℕ} (G : Garden w) (P : CorePlacement G) (ε : Bool) :
    MolIso G.molecule (chosenSkeleton G P ε).molecule := by
  cases ε
  · exact molIsoRefl G
  · exact
      { e := coreBranchEquiv G P
        d := twistDartEquiv G P
        atoms_iff := fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩
        atom_comm := twistDartEquiv_atom G P
        mate_comm := twistDartEquiv_mate G P
        out_comm := twistDartEquiv_out G P }

/-- The operation's output skeleton is exactly its chosen skeleton. -/
noncomputable def operationMolIso {w p : ℕ} {kind : Bool} {ι : Type*}
    {A : FamilyReconstruction w ι} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i) :
    MolIso A.skeleton.molecule op.output.skeleton.molecule :=
  chosenMolIso A.skeleton (A.family.placement i) op.choice

/-- A molecule isomorphism accompanied by an actual once-per-member LF trace.
This records composition, rather than choosing an arbitrary endpoint isomorphism. -/
inductive BatchIso (p : ℕ) (kind : Bool) {w : ℕ} {ι : Type*} :
    (L : List ι) → (A B : FamilyReconstruction w ι) →
      MolIso A.skeleton.molecule B.skeleton.molecule → Prop
  | nil (A) : BatchIso p kind [] A A (molIsoRefl A.skeleton)
  | skip {L A B F} (i : ι) (h : BatchIso p kind L A B F) : BatchIso p kind (i :: L) A B F
  | apply {L A B i} (op : FamilyOperation (p := p) (kind := kind) A i)
      {F : MolIso op.output.skeleton.molecule B.skeleton.molecule}
      (h : BatchIso p kind L op.output B F) :
      BatchIso p kind (i :: L) A B (molIsoTrans (operationMolIso op) F)

/-- Every actual LF batch has a composed molecule transport witness. -/
theorem batchIso_exists {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} (h : FamilyBatch p kind L A B) :
    ∃ F, BatchIso p kind L A B F := by
  induction h with
  | nil A => exact ⟨_, .nil A⟩
  | skip i _ ih => obtain ⟨F, hF⟩ := ih; exact ⟨F, .skip i hF⟩
  | apply op _ ih => obtain ⟨F, hF⟩ := ih; exact ⟨_, .apply op hF⟩

noncomputable def batchMolIso {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} (h : FamilyBatch p kind L A B) :
    MolIso A.skeleton.molecule B.skeleton.molecule := (batchIso_exists h).choose

theorem batchMolIso_spec {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} (h : FamilyBatch p kind L A B) :
    BatchIso p kind L A B (batchMolIso h) := (batchIso_exists h).choose_spec

/-- Prime skeletons remain prime after an admissible operation. -/
theorem operation_prime {w p : ℕ} {kind : Bool} {ι : Type*}
    {A : FamilyReconstruction w ι} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i)
    (hp : IsPrimeGarden A.skeleton) : IsPrimeGarden op.output.skeleton := by
  change IsPrimeGarden (chosenSkeleton A.skeleton (A.family.placement i) op.choice)
  cases h : op.choice
  · exact hp
  · exact (unitTwist_prime A.skeleton (A.family.placement i) (A.family.core i) (A.family.designated i)).mpr hp

/-- Every LF batch maps a canonical prime representative to another prime representative. -/
theorem batch_prime {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} (h : FamilyBatch p kind L A B)
    (hp : IsPrimeGarden A.skeleton) : IsPrimeGarden B.skeleton := by
  induction h with
  | nil => exact hp
  | skip _ _ ih => exact ih hp
  | apply op _ ih => exact ih (operation_prime op hp)

end WaveTurbulence.VineA
