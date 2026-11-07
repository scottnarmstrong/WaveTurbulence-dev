/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSingleSplice
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvIso
/-! VINE-A4 fallback infrastructure: two actual splice maps with identical
merge classes have canonically isomorphic quotient molecules, using old names. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1

/-- An injective carrier is canonically identified with another copy of the same range. -/
noncomputable def equivOfSameRange {A B C : Type*} (f : A → C) (g : B → C)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hr : ∀ x, (∃ a, f a = x) ↔ ∃ b, g b = x) : A ≃ B := by
  let F : A → B := fun a => ((hr (f a)).mp ⟨a, rfl⟩).choose
  let J : B → A := fun b => ((hr (g b)).mpr ⟨b, rfl⟩).choose
  have hF : ∀ a, g (F a) = f a := fun a => ((hr (f a)).mp ⟨a, rfl⟩).choose_spec
  have hJ : ∀ b, f (J b) = g b := fun b => ((hr (g b)).mpr ⟨b, rfl⟩).choose_spec
  exact ⟨F, J, fun a => hf ((hJ (F a)).trans (hF a)), fun b => hg ((hF (J b)).trans (hJ b))⟩

theorem equivOfSameRange_comm {A B C : Type*} (f : A → C) (g : B → C)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hr : ∀ x, (∃ a, f a = x) ↔ ∃ b, g b = x) (a : A) :
    g (equivOfSameRange f g hf hg hr a) = f a := ((hr (f a)).mp ⟨a, rfl⟩).choose_spec

variable {w : ℕ} {G H K : Garden w} {cls : GBranch G.tree → Option (GBranch G.tree)}

/-- The literal branch-name bijection between two realizations of the same merge quotient. -/
noncomputable def spliceBranchEquiv (M : SpMap G H cls) (N : SpMap G K cls) : GBranch H.tree ≃ GBranch K.tree :=
  equivOfSameRange M.ob N.ob M.ob_inj N.ob_inj (fun v => (M.ob_range v).trans (N.ob_range v).symm)

theorem spliceBranchEquiv_comm (M : SpMap G H cls) (N : SpMap G K cls) (v : GBranch H.tree) :
    N.ob (spliceBranchEquiv M N v) = M.ob v :=
  equivOfSameRange_comm M.ob N.ob M.ob_inj N.ob_inj _ v

/-- The corresponding literal original-dart bijection. -/
noncomputable def spliceDartEquiv (M : SpMap G H cls) (N : SpMap G K cls) : GardenDart H ≃ GardenDart K :=
  equivOfSameRange M.od N.od M.od_inj N.od_inj (fun x => (M.od_range x).trans (N.od_range x).symm)

theorem spliceDartEquiv_comm (M : SpMap G H cls) (N : SpMap G K cls) (x : GardenDart H) :
    N.od (spliceDartEquiv M N x) = M.od x :=
  equivOfSameRange_comm M.od N.od M.od_inj N.od_inj _ x

/-- Every molecular incidence agrees under the old-name quotient identification. -/
noncomputable def spliceMolIso (M : SpMap G H cls) (N : SpMap G K cls) : MolIso H.molecule K.molecule where
  e := spliceBranchEquiv M N
  d := spliceDartEquiv M N
  atoms_iff := fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩
  atom_comm x := by
    apply N.ob_inj
    rw [N.ob_atom, spliceDartEquiv_comm, spliceBranchEquiv_comm, M.ob_atom]
  mate_comm x := by
    apply N.od_inj
    rw [N.od_mate, spliceDartEquiv_comm, spliceDartEquiv_comm, M.od_mate]
  out_comm x := by
    rw [← N.od_out, spliceDartEquiv_comm, M.od_out]

/-- It also preserves roots, using the actual splice-map root clauses. -/
theorem spliceBranchEquiv_root (M : SpMap G H cls) (N : SpMap G K cls) (v : GBranch H.tree) :
    (spliceBranchEquiv M N v).1.2 = [] ↔ v.1.2 = [] := by
  rw [← N.ob_root, spliceBranchEquiv_comm, M.ob_root]

end WaveTurbulence.VineA
