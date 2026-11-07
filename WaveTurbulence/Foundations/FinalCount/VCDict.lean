/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulenceVineParam.Contract
public import WaveTurbulence.Foundations.FinalCount.Prop94Statement
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
/-! # VINE-COUNT part 4: the dictionary between the removed vine `K.vc` (the restriction of the doubly cut molecule)
and the atomic group `K.C.atoms` of `M`.

For an actual block `S = K.C.atoms` with joints `a, b` (the removed object), the darts of `K.vc` are exactly the
darts of `M` with both ends in `S` (the group darts); the atoms of `K.vc` are exactly `S`; bond multiplicities and
directions between atoms of `S` agree. Consequently every ladder of `K.vc` is a ladder of `M` inside `S`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem containsDart_inGroup {M : Molecule V D} {C : Object M} {x : D} (h : C.ContainsDart x) :
    M.InGroup C.atoms x := by
  unfold Object.ContainsDart at h
  split at h
  · exact h
  · exact h.2.2

/-- The number of bonds from `t` to the atoms of `Z ⊆ S` is at most the internal degree of `t`. -/
theorem sum_bondsBetween_le_degIn (M : Molecule V D) {S Z : Finset V} {t : V} (ht : t ∈ S) (hZ : Z ⊆ S)
    (htZ : t ∉ Z) : ∑ z ∈ Z, M.bondsBetween t z ≤ M.degIn S t := by
  calc ∑ z ∈ Z, M.bondsBetween t z
      = ∑ z ∈ Z, ((M.dartsAt t).filter (fun x => M.atom (M.mate x) = z)).card :=
        Finset.sum_congr rfl fun z hz =>
          Mole.bondsBetween_eq_card_darts M (fun h => htZ (h ▸ hz))
    _ = (Z.biUnion fun z => (M.dartsAt t).filter (fun x => M.atom (M.mate x) = z)).card := by
        rw [Finset.card_biUnion]
        intro z _ z' _ hzz'
        exact Finset.disjoint_left.mpr fun x hx hx' =>
          hzz' ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hx').2)
    _ ≤ M.degIn S t := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.mp hx
        obtain ⟨hxd, hxm⟩ := Finset.mem_filter.mp hxz
        refine Finset.mem_filter.mpr ⟨hxd, ?_, ?_⟩
        · rw [(mem_dartsAt M t x).mp hxd]; exact ht
        · rw [hxm]; exact hZ hz

theorem degIn_le_deg (M : Molecule V D) (S : Finset V) (t : V) : M.degIn S t ≤ M.deg t :=
  Finset.card_le_card (Finset.filter_subset _ _)

section
variable {M : Molecule V D} (K : VineCut M)

theorem x₁_inGroup : M.InGroup K.C.atoms K.x₁ := containsDart_inGroup K.in_a.1
theorem x₂_inGroup : M.InGroup K.C.atoms K.x₂ := containsDart_inGroup K.in_a.2
theorem y₁_inGroup : M.InGroup K.C.atoms K.y₁ := containsDart_inGroup K.in_b.1
theorem y₂_inGroup : M.InGroup K.C.atoms K.y₂ := containsDart_inGroup K.in_b.2

theorem x₁_atom : M.atom K.x₁ = K.C.upper := K.cut_a.2.2.1
theorem x₂_atom : M.atom K.x₂ = K.C.upper := K.cut_a.2.2.2.1
theorem x₁_out : M.out K.x₁ = false := K.cut_a.2.2.2.2.2.1
theorem x₂_out : M.out K.x₂ = true := K.cut_a.2.2.2.2.2.2

theorem y_atoms_aux {x : D} (h : K.m1.atom x = K.C.lower) : M.atom x = K.C.lower := by
  have h1 : K.m1.atom x = if M.atom x = K.C.upper ∧ x ≠ K.x₁ ∧ x ≠ K.x₂ then K.fa else M.atom x :=
    cut_atom M K.C.upper K.fa K.x₁ K.x₂ x
  rw [h1] at h
  split_ifs at h with hh
  · exact absurd h K.fa_ne_b
  · exact h

theorem y₁_atom : M.atom K.y₁ = K.C.lower := (y_atoms_aux K) K.cut_b.2.2.1
theorem y₂_atom : M.atom K.y₂ = K.C.lower := (y_atoms_aux K) K.cut_b.2.2.2.1
theorem y₁_out : M.out K.y₁ = false := K.cut_b.2.2.2.2.2.1
theorem y₂_out : M.out K.y₂ = true := K.cut_b.2.2.2.2.2.2

variable (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower)
include hB

theorem grp_at_a_out {x : D} (hx : M.atom x = K.C.upper) (hg : M.InGroup K.C.atoms x) (ho : M.out x = true) :
    x = K.x₂ := by
  obtain ⟨-, -, -, -, ho1, -⟩ := hB
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp ho1
  have h1 : x ∈ (M.dartsAt K.C.upper).filter (fun x => M.InGroup K.C.atoms x ∧ M.out x = true) :=
    Finset.mem_filter.mpr ⟨(mem_dartsAt M _ _).mpr hx, hg, ho⟩
  have h2 : K.x₂ ∈ (M.dartsAt K.C.upper).filter (fun x => M.InGroup K.C.atoms x ∧ M.out x = true) :=
    Finset.mem_filter.mpr ⟨(mem_dartsAt M _ _).mpr (x₂_atom K), (x₂_inGroup K), (x₂_out K)⟩
  rw [hy, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

theorem grp_at_a_in {x : D} (hx : M.atom x = K.C.upper) (hg : M.InGroup K.C.atoms x) (ho : M.out x = false) :
    x = K.x₁ := by
  obtain ⟨-, -, -, -, -, hi1, -⟩ := hB
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hi1
  have h1 : x ∈ (M.dartsAt K.C.upper).filter (fun x => M.InGroup K.C.atoms x ∧ M.out x = false) :=
    Finset.mem_filter.mpr ⟨(mem_dartsAt M _ _).mpr hx, hg, ho⟩
  have h2 : K.x₁ ∈ (M.dartsAt K.C.upper).filter (fun x => M.InGroup K.C.atoms x ∧ M.out x = false) :=
    Finset.mem_filter.mpr ⟨(mem_dartsAt M _ _).mpr (x₁_atom K), (x₁_inGroup K), (x₁_out K)⟩
  rw [hy, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

theorem grp_at_b_out {x : D} (hx : M.atom x = K.C.lower) (hg : M.InGroup K.C.atoms x) (ho : M.out x = true) :
    x = K.y₂ := by
  obtain ⟨-, -, -, -, -, -, ho1, -⟩ := hB
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp ho1
  have h1 : x ∈ (M.dartsAt K.C.lower).filter (fun x => M.InGroup K.C.atoms x ∧ M.out x = true) :=
    Finset.mem_filter.mpr ⟨(mem_dartsAt M _ _).mpr hx, hg, ho⟩
  have h2 : K.y₂ ∈ (M.dartsAt K.C.lower).filter (fun x => M.InGroup K.C.atoms x ∧ M.out x = true) :=
    Finset.mem_filter.mpr ⟨(mem_dartsAt M _ _).mpr (y₂_atom K), (y₂_inGroup K), (y₂_out K)⟩
  rw [hy, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

theorem grp_at_b_in {x : D} (hx : M.atom x = K.C.lower) (hg : M.InGroup K.C.atoms x) (ho : M.out x = false) :
    x = K.y₁ := by
  obtain ⟨-, -, -, -, -, -, -, hi2, -⟩ := hB
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hi2
  have h1 : x ∈ (M.dartsAt K.C.lower).filter (fun x => M.InGroup K.C.atoms x ∧ M.out x = false) :=
    Finset.mem_filter.mpr ⟨(mem_dartsAt M _ _).mpr hx, hg, ho⟩
  have h2 : K.y₁ ∈ (M.dartsAt K.C.lower).filter (fun x => M.InGroup K.C.atoms x ∧ M.out x = false) :=
    Finset.mem_filter.mpr ⟨(mem_dartsAt M _ _).mpr (y₁_atom K), (y₁_inGroup K), (y₁_out K)⟩
  rw [hy, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

/-- Group darts keep their atom under the two cuts. -/
theorem cutMol_atom_of_inGroup {x : D} (hg : M.InGroup K.C.atoms x) : K.cutMol.atom x = M.atom x := by
  have hm1 : K.m1.atom x = M.atom x := by
    rw [show K.m1.atom x = _ from cut_atom M K.C.upper K.fa K.x₁ K.x₂ x]
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    cases ho : M.out x
    · exact h2 (grp_at_a_in K hB h1 hg ho)
    · exact h3 (grp_at_a_out K hB h1 hg ho)
  rw [show K.cutMol.atom x = _ from cut_atom K.m1 K.C.lower K.fb K.y₁ K.y₂ x, if_neg, hm1]
  rintro ⟨h1, h2, h3⟩
  rw [hm1] at h1
  cases ho : M.out x
  · exact h2 (grp_at_b_in K hB h1 hg ho)
  · exact h3 (grp_at_b_out K hB h1 hg ho)

theorem cutMol_atom_cases (x : D) :
    K.cutMol.atom x = K.fb ∨ K.cutMol.atom x = K.fa ∨ K.cutMol.atom x = M.atom x := by
  rw [show K.cutMol.atom x = _ from cut_atom K.m1 K.C.lower K.fb K.y₁ K.y₂ x]
  by_cases h : K.m1.atom x = K.C.lower ∧ x ≠ K.y₁ ∧ x ≠ K.y₂
  · exact Or.inl (if_pos h)
  · rw [if_neg h]
    rw [show K.m1.atom x = _ from cut_atom M K.C.upper K.fa K.x₁ K.x₂ x]
    by_cases h' : M.atom x = K.C.upper ∧ x ≠ K.x₁ ∧ x ≠ K.x₂
    · exact Or.inr (Or.inl (if_pos h'))
    · exact Or.inr (Or.inr (if_neg h'))

theorem fa_notMem_S : K.fa ∉ K.C.atoms := fun h => K.fa_fresh (hB.1 h)
theorem fb_notMem_S : K.fb ∉ K.C.atoms := fun h => K.fb_fresh (hB.1 h)

/-- The darts of `K.vc` are the group darts of `M`. -/
theorem vc_dart_iff (x : D) : (¬ (K.cutMol.atom x ∉ K.C.atoms)) ↔ M.InGroup K.C.atoms x := by
  constructor
  · intro hx
    have hx' : K.cutMol.atom x ∈ K.C.atoms := not_not.mp hx
    have hm := (PClosed.neg K.cutMol (fun a => a ∉ K.C.atoms) K.closed) x hx
    have hm' : K.cutMol.atom (K.cutMol.mate x) ∈ K.C.atoms := not_not.mp hm
    have key : ∀ y : D, K.cutMol.atom y ∈ K.C.atoms → M.atom y ∈ K.C.atoms := by
      intro y hy
      rcases cutMol_atom_cases K hB y with h | h | h
      · exact absurd (h ▸ hy) (fb_notMem_S K hB)
      · exact absurd (h ▸ hy) (fa_notMem_S K hB)
      · exact h ▸ hy
    exact ⟨key x hx', key (M.mate x) hm'⟩
  · intro hg
    rw [cutMol_atom_of_inGroup K hB hg]
    exact not_not.mpr hg.1


theorem inGroup_mate {x : D} (h : M.InGroup K.C.atoms x) : M.InGroup K.C.atoms (M.mate x) :=
  ⟨h.2, by rw [M.mate_mate]; exact h.1⟩

/-- The atoms of the removed vine are exactly the atoms of the removed object. -/
theorem mem_vc_atoms (z : V) : z ∈ K.vc.atoms ↔ z ∈ K.C.atoms := by
  show z ∈ K.cutMol.atoms.filter _ ↔ _
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩; exact not_not.mp h
  · intro h
    refine ⟨?_, not_not.mpr h⟩
    show z ∈ insert K.fb (insert K.fa M.atoms)
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hB.1 h))

theorem vc_atom_eq (x : PDart K.cutMol (fun a => ¬ (a ∉ K.C.atoms))) : K.vc.atom x = M.atom x.1 :=
  cutMol_atom_of_inGroup K hB ((vc_dart_iff K hB x.1).mp x.2)

theorem vc_ends_eq (x : PDart K.cutMol (fun a => ¬ (a ∉ K.C.atoms))) : K.vc.ends x = M.ends x.1 := by
  have hg := (vc_dart_iff K hB x.1).mp x.2
  have h1 : K.vc.atom x = M.atom x.1 := vc_atom_eq K hB x
  have h2 : K.vc.atom (K.vc.mate x) = M.atom (M.mate x.1) :=
    cutMol_atom_of_inGroup K hB (inGroup_mate K hB hg)
  show s(K.vc.atom x, K.vc.atom (K.vc.mate x)) = s(M.atom x.1, M.atom (M.mate x.1))
  rw [h1, h2]

theorem vc_bondsBetween_eq {u v : V} (hu : u ∈ K.C.atoms) (hv : v ∈ K.C.atoms) :
    K.vc.bondsBetween u v = M.bondsBetween u v := by
  unfold Molecule.bondsBetween
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · have : K.vc.out x = true := (Finset.mem_filter.mp hx1).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩
    · rw [← vc_ends_eq K hB x]; exact hx2
  · intro x _ y _ h
    exact Subtype.ext h
  · intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    have he : (M.atom y = u ∧ M.atom (M.mate y) = v) ∨ (M.atom y = v ∧ M.atom (M.mate y) = u) :=
      Sym2.eq_iff.mp hy2
    have hg : M.InGroup K.C.atoms y := by
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1 ▸ hu, h2 ▸ hv⟩
      · exact ⟨h1 ▸ hv, h2 ▸ hu⟩
    have hy' : ¬ (K.cutMol.atom y ∉ K.C.atoms) := (vc_dart_iff K hB y).mpr hg
    refine ⟨⟨y, hy'⟩, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy1).2⟩
    · rw [vc_ends_eq K hB]; exact hy2

theorem vc_directed_iff {u v : V} (hu : u ∈ K.C.atoms) (hv : v ∈ K.C.atoms) :
    K.vc.Directed u v ↔ M.Directed u v := by
  constructor
  · rintro ⟨x, hx1, hx2, hx3⟩
    have h1 : K.vc.atom x = M.atom x.1 := vc_atom_eq K hB x
    have h2 : K.vc.atom (K.vc.mate x) = M.atom (M.mate x.1) :=
      cutMol_atom_of_inGroup K hB (inGroup_mate K hB ((vc_dart_iff K hB x.1).mp x.2))
    exact ⟨x.1, hx1, h1 ▸ hx2, h2 ▸ hx3⟩
  · rintro ⟨x, hx1, hx2, hx3⟩
    have hg : M.InGroup K.C.atoms x := ⟨hx2 ▸ hu, hx3 ▸ hv⟩
    have hy' : ¬ (K.cutMol.atom x ∉ K.C.atoms) := (vc_dart_iff K hB x).mpr hg
    refine ⟨⟨x, hy'⟩, hx1, ?_, ?_⟩
    · rw [vc_atom_eq K hB]; exact hx2
    · have : K.vc.atom (K.vc.mate ⟨x, hy'⟩) = M.atom (M.mate x) :=
        cutMol_atom_of_inGroup K hB (inGroup_mate K hB hg)
      rw [this]; exact hx3

/-- Every ladder of the removed vine is a ladder of `M` inside the object. -/
theorem vc_isLadder {m : ℕ} {u v : Fin (m + 1) → V} (h : K.vc.IsLadder u v) :
    M.IsLadder u v ∧ ∀ j, u j ∈ K.C.atoms ∧ v j ∈ K.C.atoms := by
  obtain ⟨hm, hinj, hat, hrung, hrail⟩ := h
  have hS : ∀ j, u j ∈ K.C.atoms ∧ v j ∈ K.C.atoms := fun j =>
    ⟨(mem_vc_atoms K hB _).mp (hat j).1, (mem_vc_atoms K hB _).mp (hat j).2⟩
  refine ⟨⟨hm, hinj, fun j => ⟨hB.1 (hS j).1, hB.1 (hS j).2⟩, fun j => ?_, fun j => ?_⟩, hS⟩
  · rw [← vc_bondsBetween_eq K hB (hS j).1 (hS j).2]; exact hrung j
  · obtain ⟨r1, r2, r3⟩ := hrail j
    refine ⟨?_, ?_, ?_⟩
    · rw [← vc_bondsBetween_eq K hB (hS _).1 (hS _).1]; exact r1
    · rw [← vc_bondsBetween_eq K hB (hS _).2 (hS _).2]; exact r2
    · rw [← vc_directed_iff K hB (hS _).1 (hS _).1, ← vc_directed_iff K hB (hS _).2 (hS _).2]; exact r3


theorem vc_deg_le (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (z : V) (hz : z ∈ K.vc.atoms) : K.vc.deg z ≤ 4 := by
  have hzS : z ∈ K.C.atoms := (mem_vc_atoms K hB z).mp hz
  have hle : K.vc.deg z ≤ M.deg z := by
    unfold Molecule.deg
    apply Finset.card_le_card_of_injOn (fun y : PDart K.cutMol (fun a => ¬ (a ∉ K.C.atoms)) => y.1)
    · intro y hy
      have : K.vc.atom y = z := (mem_dartsAt K.vc z y).mp hy
      rw [vc_atom_eq K hB y] at this
      exact (mem_dartsAt M z y.1).mpr this
    · intro y _ y' _ h
      exact Subtype.ext h
  exact hle.trans (hM z (hB.1 hzS))

theorem vc_ladders_disjoint (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) :
    (K.vc.maximalLadders : Set (Finset V)).PairwiseDisjoint id :=
  LadderDisjoint.maximalLadders_pairwiseDisjoint_of_degree_le_four K.vc (vc_deg_le K hB hM)

end
end WaveTurbulence.VineCount
