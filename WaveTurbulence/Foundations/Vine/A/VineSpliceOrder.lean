/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceQuotient
/-! VINE-A4: disjoint unit enumerations have the same merge quotient.
The resulting actual molecule isomorphism fixes every surviving original name.
This does not yet assert equality of ordered gardens or invariance of splicedKernel. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G H K : Garden w}

/-- S2a's merge labels depend only on the disjoint units, not their enumeration. -/
theorem spliceFold_cls_same_units (l m : List (CLBlock G))
    (hl : l.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    (hm : m.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    (hmem : ∀ u, u ∈ l ↔ u ∈ m) : (spliceFold G l).cls = (spliceFold G m).cls := by
  classical
  funext v
  by_cases h : ∃ u ∈ l, v ∈ u.atoms
  · obtain ⟨u, hu, hv⟩ := h
    rw [spliceFold_cls_mem l hl hu hv, spliceFold_cls_mem m hm ((hmem u).mp hu) hv]
  · have hn : ∀ u ∈ l, v ∉ u.atoms := fun u hu hv => h ⟨u, hu, hv⟩
    have hn' : ∀ u ∈ m, v ∉ u.atoms := fun u hu => hn u ((hmem u).mpr hu)
    rw [spliceFold_cls_notMem l hl hn, spliceFold_cls_notMem m hm hn']

/-- Equal class functions give an old-name-fixing quotient isomorphism. -/
theorem spliceMolIso_exists_of_cls_eq
    {cls cls' : GBranch G.tree → Option (GBranch G.tree)}
    (M : SpMap G H cls) (N : SpMap G K cls') (hc : cls = cls') :
    ∃ F : MolIso H.molecule K.molecule,
      (∀ v, N.ob (F.e v) = M.ob v) ∧ (∀ x, N.od (F.d x) = M.od x) := by
  subst cls'
  exact ⟨spliceMolIso M N, spliceBranchEquiv_comm M N, spliceDartEquiv_comm M N⟩

/-- In particular any two disjoint enumerations of the same units have isomorphic molecules. -/
theorem spliceFold_same_units_molIso (l m : List (CLBlock G))
    (hl : l.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    (hm : m.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    (hmem : ∀ u, u ∈ l ↔ u ∈ m) :
    ∃ F : MolIso (spliceFold G l).G.molecule (spliceFold G m).G.molecule,
      (∀ v, (spliceFold G m).M.ob (F.e v) = (spliceFold G l).M.ob v) ∧
      (∀ x, (spliceFold G m).M.od (F.d x) = (spliceFold G l).M.od x) :=
  spliceMolIso_exists_of_cls_eq (spliceFold G l).M (spliceFold G m).M
    (spliceFold_cls_same_units l m hl hm hmem)

end WaveTurbulence.VineA
