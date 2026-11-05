/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.GardenDirectedIso

/-! # Transporting actual atomic groups and internal incidences under a twist -/

public section
namespace WaveTurbulence.Twist
open TTree Finset
variable {w : ℕ} (G H : Garden w) (f : GardenDirectedIso G H)

/-- The same atomic group in the concrete twisted garden. -/
@[expose] noncomputable def isoAtoms (S : Finset (GBranch G.tree)) :
    Finset (GBranch H.tree) := S.image f.branches

/-- Group membership is preserved by the actual branch bijection. -/
theorem mem_isoAtoms (S : Finset (GBranch G.tree)) (v : GBranch G.tree) :
    f.branches v ∈ isoAtoms G H f S ↔ v ∈ S := by
  change f.branches v ∈ S.image f.branches ↔ v ∈ S
  constructor
  · intro h
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp h
    exact f.branches.injective he ▸ hu
  · intro hv
    exact Finset.mem_image.mpr ⟨v,hv,rfl⟩

/-- The actual dart bijection preserves internal-group membership. -/
theorem inGroup_isoAtoms (S : Finset (GBranch G.tree)) (x : GardenDart G) :
    H.molecule.InGroup (isoAtoms G H f S) (f.darts x) ↔
      G.molecule.InGroup S x := by
  have ha := f.atom_comm x
  have hb := (congrArg H.molecule.atom (f.mate_comm x)).trans
    (f.atom_comm (G.molecule.mate x))
  constructor
  · intro h
    exact ⟨(mem_isoAtoms G H f S _).mp (ha ▸ h.1),(mem_isoAtoms G H f S _).mp (hb ▸ h.2)⟩
  · intro h
    exact ⟨ha.symm ▸ (mem_isoAtoms G H f S _).mpr h.1,hb.symm ▸ (mem_isoAtoms G H f S _).mpr h.2⟩

/-- Membership in any internally oriented incidence set is preserved. -/
theorem iso_internal_filter_mem (S : Finset (GBranch G.tree)) (v : GBranch G.tree)
    (p : Bool → Prop) [DecidablePred p] (x : GardenDart G) :
    f.darts x ∈ (H.molecule.dartsAt (f.branches v)).filter
        (fun y => H.molecule.InGroup (isoAtoms G H f S) y ∧ p (H.molecule.out y)) ↔
      x ∈ (G.molecule.dartsAt v).filter (fun y => G.molecule.InGroup S y ∧ p (G.molecule.out y)) := by
  constructor
  · intro h
    obtain ⟨hat,hgroup,hp⟩ := Finset.mem_filter.mp h
    have hat := (Mole.mem_dartsAt H.molecule _ _).mp hat
    have ha := f.branches.injective ((f.atom_comm x).symm.trans hat)
    exact Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt G.molecule v x).mpr ha,
      (inGroup_isoAtoms G H f S x).mp hgroup,(f.out_comm x) ▸ hp⟩
  · intro h
    obtain ⟨hat,hgroup,hp⟩ := Finset.mem_filter.mp h
    have ha := (Mole.mem_dartsAt G.molecule v x).mp hat
    exact Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt H.molecule _ _).mpr
      ((f.atom_comm x).trans (congrArg f.branches ha)),
      (inGroup_isoAtoms G H f S x).mpr hgroup,(f.out_comm x).symm ▸ hp⟩

/-- All internal oriented incidence counts are unchanged. -/
theorem iso_internal_filter_card (S : Finset (GBranch G.tree)) (v : GBranch G.tree)
    (p : Bool → Prop) [DecidablePred p] :
    ((H.molecule.dartsAt (f.branches v)).filter
      (fun y => H.molecule.InGroup (isoAtoms G H f S) y ∧ p (H.molecule.out y))).card =
    ((G.molecule.dartsAt v).filter (fun y => G.molecule.InGroup S y ∧ p (G.molecule.out y))).card := by
  symm
  apply card_bij (fun x _hx => f.darts x)
  · intro x hx
    exact (iso_internal_filter_mem G H f S v p x).mpr hx
  · intro x _hx y _hy he
    exact f.darts.injective he
  · intro y hy
    obtain ⟨x,rfl⟩ := f.darts.surjective y
    exact ⟨x,(iso_internal_filter_mem G H f S v p x).mp hy,rfl⟩

/-- Internal total degrees are unchanged. -/
theorem iso_degIn (S : Finset (GBranch G.tree)) (v : GBranch G.tree) :
    H.molecule.degIn (isoAtoms G H f S) (f.branches v) = G.molecule.degIn S v := by
  simpa only [Molecule.degIn,and_true] using iso_internal_filter_card G H f S v (fun _ => True)

/-- Internal out-degrees are unchanged. -/
theorem iso_outIn (S : Finset (GBranch G.tree)) (v : GBranch G.tree) :
    H.molecule.outIn (isoAtoms G H f S) (f.branches v) = G.molecule.outIn S v :=
  iso_internal_filter_card G H f S v (fun b => b = true)

/-- Internal in-degrees are unchanged. -/
theorem iso_inIn (S : Finset (GBranch G.tree)) (v : GBranch G.tree) :
    H.molecule.inIn (isoAtoms G H f S) (f.branches v) = G.molecule.inIn S v :=
  iso_internal_filter_card G H f S v (fun b => b = false)

end WaveTurbulence.Twist
