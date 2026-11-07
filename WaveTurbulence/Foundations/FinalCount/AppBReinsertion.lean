/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBDeletionDegrees
public import WaveTurbulence.Foundations.FinalCount.AppBAddEraseIso
import Mathlib.Tactic

/-! # DH23 3S3-3G and 3D3-3G: literal bond reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Survivor membership follows from the actual embedding and label set. -/
theorem vertex_mem_post (a : ℕ) (ha : a ∈ P.vertices) (hkeep : a ∉ P.removed) :
    r.vertex a ∈ r.post.atoms := by
  exact mem_sdiff.mpr ⟨r.vertex_mem a ha,fun h => hkeep ((r.vertex_mem_removed_iff a ha).mp h)⟩

/-- Delete the atomic group and add a directed bond from the surviving
label a to b. The reverse direction is obtained by exchanging a,b. -/
def postWithBond (a b : ℕ) := addBond r.post (r.vertex a) (r.vertex b)

/-- The new physical bond label is exactly the old boundary bond label,
not an independently chosen momentum. Both new darts get the same value. -/
def reinsertedLabels {K : Type*} (κ : D → K) (i : Fin P.edges.length) :
    Degen.RetainedDart M r.removedAtoms ⊕ Bool → K :=
  Sum.elim (fun x => κ x.val) (fun _ => κ (r.edge i).val)

/-- The output direction is the old boundary direction at a, as specified
in both 3S3-3G and 3D3-3G. -/
def directedPostWithBond (a b : ℕ) (i : Fin P.edges.length) :=
  if M.atom (r.edge i).val = r.vertex a then r.postWithBond a b else r.postWithBond b a

/-- No atom is introduced or lost during reinsertion between survivors. -/
theorem postWithBond_atoms (a b : ℕ) (ha : a ∈ P.vertices) (hb : b ∈ P.vertices)
    (hka : a ∉ P.removed) (hkb : b ∉ P.removed) :
    (r.postWithBond a b).atoms = r.post.atoms := by
  change insert (r.vertex a) (insert (r.vertex b) r.post.atoms) = _
  simp only [insert_eq_of_mem (r.vertex_mem_post b hb hkb),insert_eq_of_mem (r.vertex_mem_post a ha hka)]

/-- The exact new bond count, with one added outgoing representative. -/
theorem postWithBond_bonds (a b : ℕ) :
    (r.postWithBond a b).bonds.card = r.post.bonds.card + 1 :=
  addBond_card_bonds r.post _ _

/-- Both endpoint degree changes are actual incidence changes. -/
theorem postWithBond_degree (a b : ℕ) (v : V) :
    (r.postWithBond a b).deg v = r.post.deg v +
      (if r.vertex a = v then 1 else 0) + (if r.vertex b = v then 1 else 0) :=
  addBond_deg r.post _ _ _

/-- Both darts of the new bond satisfy the original bond-label equality. -/
theorem reinsertedLabels_mate {K : Type*} (κ : D → K) (i : Fin P.edges.length)
    (a b : ℕ) (hκ : ∀ x, κ (M.mate x) = κ x) :
    ∀ x, r.reinsertedLabels κ i ((r.postWithBond a b).mate x) = r.reinsertedLabels κ i x := by
  rintro (x|t)
  · exact hκ x.val
  · rfl

end AppbRealization
end WaveTurbulence.Mole
