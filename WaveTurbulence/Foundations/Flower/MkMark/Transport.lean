/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.Prot

/-! # B2b MK-MARK: transport of `Π₀` off a replaced region (o75 Lemma 2⁺(a), garden level)

Two gardens `LG`, `LG'` correspond off regions `R`, `R'` of addresses (`OutIso`): an address map `f` sending the
nodes outside `R` to nodes outside `R'`, preserving the tree index, roots, leaves, ordered children, the boundary
(a child or the parent lying in the region), and the tree of the partner of a leaf. The regions contain no roots
and their leaves are paired inside their own tree (`RegionOK`), so they contain no capped flower.

**`prot_transport`.** If `Π₀(LG)` avoids `R`, then `Π₀(LG')` avoids `R'`, and `f` maps `Π₀(LG) ∖ R` onto
`Π₀(LG') ∖ R'`. This is the protected-set half of o75 Lemma 2⁺(a): a twist at an unmarked vine replaces only
objects inside the near region of the lower joint, which contains no protected vertex. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-- A correspondence of two gardens off two regions of addresses. -/
structure OutIso (LG LG' : LayeredGarden w) (R R' : Set (Address w)) where
  f : Address w → Address w
  node : ∀ z, NodeAt LG z → z ∉ R → NodeAt LG' (f z) ∧ f z ∉ R'
  tree : ∀ z, NodeAt LG z → z ∉ R → (f z).1 = z.1
  root : ∀ z, NodeAt LG z → z ∉ R → ((f z).2 = [] ↔ z.2 = [])
  leaf : ∀ z, NodeAt LG z → z ∉ R → (LeafAt LG' (f z) ↔ LeafAt LG z)
  child : ∀ z (i : Fin 3), NodeAt LG z → z ∉ R → NodeAt LG (addrExt z [i]) → addrExt z [i] ∉ R →
    f (addrExt z [i]) = addrExt (f z) [i]
  childR : ∀ z (i : Fin 3), NodeAt LG z → z ∉ R →
    (NodeAt LG (addrExt z [i]) ∧ addrExt z [i] ∈ R ↔ NodeAt LG' (addrExt (f z) [i]) ∧ addrExt (f z) [i] ∈ R')
  parentR : ∀ z, NodeAt LG z → z ∉ R → z.2 ≠ [] →
    ((z.1, z.2.dropLast) ∈ R ↔ ((f z).1, (f z).2.dropLast) ∈ R')
  pairTree : ∀ z (h : LeafAt LG z) (h' : LeafAt LG' (f z)), z ∉ R →
    (LG'.garden.pair ⟨f z, h'⟩).1.1 = (LG.garden.pair ⟨z, h⟩).1.1

/-- A region without roots whose leaves are paired inside their own tree. -/
structure RegionOK (LG : LayeredGarden w) (R : Set (Address w)) : Prop where
  root : ∀ z ∈ R, NodeAt LG z → z.2 ≠ []
  pair : ∀ z (h : LeafAt LG z), z ∈ R → (LG.garden.pair ⟨z, h⟩).1.1 = z.1

/-- Address form of membership in `Π₀`. -/
def ProtAt (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (z : Address w) : Prop :=
  NodeAt LG z ∧ ∃ σ : Address w, NearAt z σ ∧ SeedAt LG J pat σ

theorem mem_protI0_iff_protAt {LG : LayeredGarden w} {J : Finset (Fin w)} (pat : Fin w → FixPat) (t s : ℝ)
    (a : GNode LG.garden.tree) : a ∈ protI0 LG J pat t s ↔ ProtAt LG J pat a.1 :=
  (mem_protI0_iff pat t s a).trans ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩

/-- No protected address in the region. -/
def NoProtIn (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (R : Set (Address w)) : Prop :=
  ∀ z ∈ R, ¬ ProtAt LG J pat z

/-- No seed in the region. -/
def NoSeedIn (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (R : Set (Address w)) : Prop :=
  ∀ z ∈ R, ¬ SeedAt LG J pat z

/-! ## Basic node facts -/

section Basic
variable {LG : LayeredGarden w}

theorem nodeAt_of_leafAt {z : Address w} (h : LeafAt LG z) : NodeAt LG z :=
  (TTree.mem_nodes_iff _ _).mpr (Or.inl h)

theorem nodeAt_of_branchAt {z : Address w} (h : BranchAt LG z) : NodeAt LG z :=
  (TTree.mem_nodes_iff _ _).mpr (Or.inr h)

theorem nodeAt_child {z : Address w} (h : BranchAt LG z) (i : Fin 3) : NodeAt LG (addrExt z [i]) :=
  (GBranch.child (⟨z, h⟩ : GBranch LG.garden.tree) i).2

theorem branchAt_of_child {z : Address w} {i : Fin 3} (h : NodeAt LG (addrExt z [i])) : BranchAt LG z :=
  TTree.branching_of_append_mem _ h

theorem not_branchAt_of_leafAt {z : Address w} (h : LeafAt LG z) : ¬ BranchAt LG z :=
  TTree.not_mem_branching_of_mem_leaves _ h

theorem branchAt_iff_not_leafAt {z : Address w} (h : NodeAt LG z) : BranchAt LG z ↔ ¬ LeafAt LG z := by
  constructor
  · intro hb hl
    exact not_branchAt_of_leafAt hl hb
  · intro hl
    rcases (TTree.mem_nodes_iff _ _).mp h with h' | h'
    · exact absurd h' hl
    · exact h'

/-- A non-root address is the child of its parent. -/
theorem addrExt_parent {z : Address w} (h : z.2 ≠ []) : z = addrExt (z.1, z.2.dropLast) [z.2.getLast h] := by
  refine Prod.ext rfl ?_
  show z.2 = z.2.dropLast ++ [z.2.getLast h]
  exact (List.dropLast_append_getLast h).symm

theorem addrExt_inj {y y' : Address w} {i i' : Fin 3} (h : addrExt y [i] = addrExt y' [i']) :
    y = y' ∧ i = i' := by
  simp only [addrExt, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := List.append_inj' h2 rfl
  simp only [List.cons.injEq, and_true] at h3
  exact ⟨Prod.ext h1 h3.1, h3.2⟩

theorem nearAt_refl (z : Address w) : NearAt z z := ⟨rfl, Or.inl rfl⟩

/-- A child is near its parent. -/
theorem nearAt_child_parent (z : Address w) (i : Fin 3) : NearAt (addrExt z [i]) z :=
  ⟨rfl, Or.inr (Or.inr ⟨by simp [addrExt], by simp [addrExt]⟩)⟩

/-- A parent is near its child. -/
theorem nearAt_parent_child (z : Address w) (i : Fin 3) : NearAt z (addrExt z [i]) :=
  ⟨rfl, Or.inr (Or.inl ⟨by simp [addrExt], by simp [addrExt]⟩)⟩

/-- The three cases of `NearAt`, as addresses. -/
theorem nearAt_cases {z σ : Address w} (h : NearAt z σ) :
    z = σ ∨ (∃ i : Fin 3, σ = addrExt z [i]) ∨ (∃ i : Fin 3, z = addrExt σ [i]) := by
  obtain ⟨h1, h2 | ⟨hn, h2⟩ | ⟨hn, h2⟩⟩ := h
  · exact Or.inl (Prod.ext h1 h2)
  · refine Or.inr (Or.inl ⟨σ.2.getLast hn, Prod.ext h1.symm ?_⟩)
    show σ.2 = z.2 ++ [σ.2.getLast hn]
    rw [h2]
    exact (List.dropLast_append_getLast hn).symm
  · refine Or.inr (Or.inr ⟨z.2.getLast hn, Prod.ext h1 ?_⟩)
    show z.2 = σ.2 ++ [z.2.getLast hn]
    rw [← h2]
    exact (List.dropLast_append_getLast hn).symm

theorem seed_protAt {J : Finset (Fin w)} {pat : Fin w → FixPat} {z : Address w}
    (h : SeedAt LG J pat z) : ProtAt LG J pat z := ⟨h.1, z, nearAt_refl z, h⟩

theorem capParent_seed {J : Finset (Fin w)} {pat : Fin w → FixPat} {z : Address w}
    (h : CapParentAt LG J z) : SeedAt LG J pat z :=
  ⟨nodeAt_of_branchAt h.1, Or.inr ⟨h.1, Or.inl h⟩⟩

end Basic

/-! ## Transport lemmas for one correspondence -/

section One
variable {LG LG' : LayeredGarden w} {R R' : Set (Address w)} (I : OutIso LG LG' R R')
  {J : Finset (Fin w)} {pat : Fin w → FixPat}

theorem OutIso.branch {z : Address w} (hn : NodeAt LG z) (hR : z ∉ R) :
    BranchAt LG' (I.f z) ↔ BranchAt LG z := by
  rw [branchAt_iff_not_leafAt (I.node z hn hR).1, branchAt_iff_not_leafAt hn, I.leaf z hn hR]

/-- Capped flowers off the region correspond. -/
theorem OutIso.capFlower {z : Address w} (hn : NodeAt LG z) (hR : z ∉ R) :
    CapFlowerAt LG' J (I.f z) ↔ CapFlowerAt LG J z := by
  constructor
  · rintro ⟨h', hJ, hp⟩
    have h := (I.leaf z hn hR).mp h'
    refine ⟨h, by rw [← I.tree z hn hR]; exact hJ, ?_⟩
    rw [← I.pairTree z h h' hR]
    exact hp
  · rintro ⟨h, hJ, hp⟩
    have h' := (I.leaf z hn hR).mpr h
    refine ⟨h', by rw [I.tree z hn hR]; exact hJ, ?_⟩
    rw [I.pairTree z h h' hR]
    exact hp

/-- A capped flower is not in a good region. -/
theorem not_capFlower_of_region {L : LayeredGarden w} {Q : Set (Address w)} (hQ : RegionOK L Q)
    {z : Address w} (hz : z ∈ Q) : ¬ CapFlowerAt L J z := by
  rintro ⟨h, hJ, hp⟩
  rw [hQ.pair z h hz] at hp
  exact hJ hp

/-- Capped-flower parents off the region correspond. -/
theorem OutIso.capParent (hR : RegionOK LG R) (hR' : RegionOK LG' R') {z : Address w} (hn : NodeAt LG z)
    (hz : z ∉ R) : CapParentAt LG' J (I.f z) ↔ CapParentAt LG J z := by
  constructor
  · rintro ⟨hb', i, hc'⟩
    have hb := (I.branch hn hz).mp hb'
    have hcn := nodeAt_child hb i
    have hcR : addrExt z [i] ∉ R := by
      intro hc
      have := (I.childR z i hn hz).mp ⟨hcn, hc⟩
      exact not_capFlower_of_region hR' this.2 hc'
    refine ⟨hb, i, ?_⟩
    rw [← I.capFlower hcn hcR, I.child z i hn hz hcn hcR]
    exact hc'
  · rintro ⟨hb, i, hc⟩
    have hcn := nodeAt_child hb i
    have hcR : addrExt z [i] ∉ R := fun h => not_capFlower_of_region hR h hc
    refine ⟨(I.branch hn hz).mpr hb, i, ?_⟩
    rw [← I.child z i hn hz hcn hcR, I.capFlower hcn hcR]
    exact hc

/-- Seeds off the region correspond, when neither region contains a seed or protected address. -/
theorem OutIso.seed (hR : RegionOK LG R) (hR' : RegionOK LG' R') (hp : NoProtIn LG J pat R)
    (hs' : NoSeedIn LG' J pat R') {z : Address w} (hn : NodeAt LG z) (hz : z ∉ R) :
    SeedAt LG' J pat (I.f z) ↔ SeedAt LG J pat z := by
  have hnode := (I.node z hn hz).1
  have ht := I.tree z hn hz
  have hcp : ∀ y, NodeAt LG y → y ∉ R → (CapParentAt LG' J (I.f y) ↔ CapParentAt LG J y) :=
    fun y hy hyR => I.capParent hR hR' hy hyR
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hn, ?_⟩
    rcases h with ⟨hJ, hr⟩ | ⟨hb', hf'⟩
    · exact Or.inl ⟨by rw [← ht]; exact hJ, (I.root z hn hz).mp hr⟩
    · have hb := (I.branch hn hz).mp hb'
      refine Or.inr ⟨hb, ?_⟩
      unfold FixSomeAt at hf' ⊢
      rw [ht] at hf'
      rcases hf' with hc | hf'
      · exact Or.inl ((hcp z hn hz).mp hc)
      · right
        cases hpat : pat z.1 with
        | plain => rw [hpat] at hf'; exact hf'
        | dRoot => rw [hpat] at hf'; exact (I.root z hn hz).mp hf'
        | dParent =>
          rw [hpat] at hf'
          obtain ⟨i, hi⟩ := hf'
          have hcn := nodeAt_child hb i
          have hcR : addrExt z [i] ∉ R := by
            intro hc
            have h2 := (I.childR z i hn hz).mp ⟨hcn, hc⟩
            exact hs' _ h2.2 (capParent_seed hi)
          refine ⟨i, ?_⟩
          rw [← hcp _ hcn hcR, I.child z i hn hz hcn hcR]
          exact hi
        | dChild i =>
          rw [hpat] at hf'
          obtain ⟨y', hy', he⟩ := hf'
          have hne : z.2 ≠ [] := by
            intro h0
            have := (I.root z hn hz).mpr h0
            rw [he] at this
            simp [addrExt] at this
          set y : Address w := (z.1, z.2.dropLast) with hy
          have hzy : z = addrExt y [z.2.getLast hne] := addrExt_parent hne
          have hyb : BranchAt LG y := branchAt_of_child (z := y) (i := z.2.getLast hne) (by rw [← hzy]; exact hn)
          have hyn := nodeAt_of_branchAt hyb
          have hyR : y ∉ R := by
            intro hyR
            have h2 := (I.parentR z hn hz hne).mp hyR
            have e : ((I.f z).1, (I.f z).2.dropLast) = y' := by
              rw [he]
              simp [addrExt]
            rw [e] at h2
            exact hs' _ h2 (capParent_seed hy')
          have hfz : I.f z = addrExt (I.f y) [z.2.getLast hne] := by
            conv_lhs => rw [hzy]
            exact I.child y _ hyn hyR (by rw [← hzy]; exact hn) (by rw [← hzy]; exact hz)
          obtain ⟨e1, e2⟩ := addrExt_inj (he.symm.trans hfz)
          refine ⟨y, (hcp y hyn hyR).mp (e1 ▸ hy'), ?_⟩
          calc z = addrExt y [z.2.getLast hne] := hzy
            _ = addrExt y [i] := by rw [e2]
  · rintro ⟨-, h⟩
    refine ⟨hnode, ?_⟩
    rcases h with ⟨hJ, hr⟩ | ⟨hb, hf⟩
    · exact Or.inl ⟨by rw [ht]; exact hJ, (I.root z hn hz).mpr hr⟩
    · refine Or.inr ⟨(I.branch hn hz).mpr hb, ?_⟩
      unfold FixSomeAt at hf ⊢
      rw [ht]
      rcases hf with hc | hf
      · exact Or.inl ((hcp z hn hz).mpr hc)
      · right
        cases hpat : pat z.1 with
        | plain => rw [hpat] at hf; exact hf
        | dRoot => rw [hpat] at hf; exact (I.root z hn hz).mpr hf
        | dParent =>
          rw [hpat] at hf
          obtain ⟨i, hi⟩ := hf
          have hcn := nodeAt_child hb i
          have hcR : addrExt z [i] ∉ R := fun hc => hp _ hc (seed_protAt (capParent_seed hi))
          refine ⟨i, ?_⟩
          rw [← I.child z i hn hz hcn hcR]
          exact (hcp _ hcn hcR).mpr hi
        | dChild i =>
          rw [hpat] at hf
          obtain ⟨y, hy, he⟩ := hf
          have hyn := nodeAt_of_branchAt hy.1
          have hyR : y ∉ R := fun h => hp _ h (seed_protAt (capParent_seed hy))
          have hzn : NodeAt LG (addrExt y [i]) := by rw [← he]; exact hn
          have hzR : addrExt y [i] ∉ R := by rw [← he]; exact hz
          refine ⟨I.f y, (hcp y hyn hyR).mpr hy, ?_⟩
          rw [he]
          exact I.child y i hyn hyR hzn hzR

/-- Protected addresses off the region correspond (one direction). -/
theorem OutIso.prot (hR : RegionOK LG R) (hR' : RegionOK LG' R') (hp : NoProtIn LG J pat R)
    (hs' : NoSeedIn LG' J pat R') {z : Address w} (hn : NodeAt LG z) (hz : z ∉ R) :
    ProtAt LG J pat z → ProtAt LG' J pat (I.f z) := by
  rintro ⟨-, σ, hnear, hσ⟩
  have hσR : σ ∉ R := fun h => hp _ h (seed_protAt hσ)
  have hσn := hσ.1
  have hfσ := (I.seed hR hR' hp hs' hσn hσR).mpr hσ
  refine ⟨(I.node z hn hz).1, ?_⟩
  rcases nearAt_cases hnear with he | ⟨i, he⟩ | ⟨i, he⟩
  · subst he
    exact ⟨I.f z, nearAt_refl _, hfσ⟩
  · have e : I.f σ = addrExt (I.f z) [i] := by
      rw [he]
      exact I.child z i hn hz (he ▸ hσn) (he ▸ hσR)
    refine ⟨I.f σ, ?_, hfσ⟩
    rw [e]
    exact nearAt_parent_child _ _
  · have e : I.f z = addrExt (I.f σ) [i] := by
      rw [he]
      exact I.child σ i hσn hσR (he ▸ hn) (he ▸ hz)
    refine ⟨I.f σ, ?_, hfσ⟩
    rw [e]
    exact nearAt_child_parent _ _

end One

/-! ## The two-sided transport -/

section Two
variable {LG LG' : LayeredGarden w} {R R' : Set (Address w)} {J : Finset (Fin w)} {pat : Fin w → FixPat}

/-- The region `R'` contains no capped-flower parent. -/
theorem noCapParent' (I' : OutIso LG' LG R' R) (hR : RegionOK LG R) (hR' : RegionOK LG' R') (hp : NoProtIn LG J pat R) :
    ∀ y' ∈ R', ¬ CapParentAt LG' J y' := by
  rintro y' hy' ⟨hb', i, hc'⟩
  set c' := addrExt y' [i]
  have hcn' := nodeAt_child hb' i
  have hcR' : c' ∉ R' := fun h => not_capFlower_of_region hR' h hc'
  have hne : c'.2 ≠ [] := by simp [c', addrExt]
  have hpar : (c'.1, c'.2.dropLast) = y' := by simp [c', addrExt]
  have hcR := (I'.parentR c' hcn' hcR' hne).mp (by rw [hpar]; exact hy')
  obtain ⟨hcn, hcRR⟩ := I'.node c' hcn' hcR'
  have hcf : CapFlowerAt LG J (I'.f c') := (I'.capFlower hcn' hcR').mpr hc'
  have hne2 : (I'.f c').2 ≠ [] := fun h => hne ((I'.root c' hcn' hcR').mp h)
  have hz := addrExt_parent hne2
  have hyb : BranchAt LG ((I'.f c').1, (I'.f c').2.dropLast) :=
    branchAt_of_child (i := (I'.f c').2.getLast hne2) (by rw [← hz]; exact hcn)
  have hcap : CapParentAt LG J ((I'.f c').1, (I'.f c').2.dropLast) :=
    ⟨hyb, (I'.f c').2.getLast hne2, by rw [← hz]; exact hcf⟩
  exact hp _ hcR (seed_protAt (capParent_seed hcap))

/-- The region `R'` contains no seed. -/
theorem noSeed' (I' : OutIso LG' LG R' R) (hR : RegionOK LG R) (hR' : RegionOK LG' R') (hp : NoProtIn LG J pat R) :
    NoSeedIn LG' J pat R' := by
  rintro y' hy' ⟨hn', h⟩
  have hncp := noCapParent' I' hR hR' hp
  rcases h with ⟨-, hr⟩ | ⟨hb', hf'⟩
  · exact hR'.root y' hy' hn' hr
  · unfold FixSomeAt at hf'
    rcases hf' with hc | hf'
    · exact hncp y' hy' hc
    · cases hpat : pat y'.1 with
      | plain => rw [hpat] at hf'; exact hf'
      | dRoot => rw [hpat] at hf'; exact hR'.root y' hy' hn' hf'
      | dParent =>
        rw [hpat] at hf'
        obtain ⟨i, hi⟩ := hf'
        set c' := addrExt y' [i]
        have hcn' := nodeAt_child hb' i
        have hcR' : c' ∉ R' := fun h => hncp _ h hi
        have hne : c'.2 ≠ [] := by simp [c', addrExt]
        have hpar : (c'.1, c'.2.dropLast) = y' := by simp [c', addrExt]
        have hcR := (I'.parentR c' hcn' hcR' hne).mp (by rw [hpar]; exact hy')
        obtain ⟨hcn, -⟩ := I'.node c' hcn' hcR'
        have hcap : CapParentAt LG J (I'.f c') := (I'.capParent hR' hR hcn' hcR').mpr hi
        have hne2 : (I'.f c').2 ≠ [] := fun h => hne ((I'.root c' hcn' hcR').mp h)
        have hz := addrExt_parent hne2
        refine hp _ hcR ⟨nodeAt_of_branchAt (branchAt_of_child (i := (I'.f c').2.getLast hne2)
          (by rw [← hz]; exact hcn)), I'.f c', ?_, capParent_seed hcap⟩
        conv_rhs => rw [hz]
        exact nearAt_parent_child _ _
      | dChild i =>
        rw [hpat] at hf'
        obtain ⟨y'', hy'', he⟩ := hf'
        have hyn' := nodeAt_of_branchAt hy''.1
        have hyR' : y'' ∉ R' := fun h => hncp _ h hy''
        have hc := (I'.childR y'' i hyn' hyR').mp ⟨by rw [← he]; exact hn', by rw [← he]; exact hy'⟩
        have hcap : CapParentAt LG J (I'.f y'') := (I'.capParent hR' hR hyn' hyR').mpr hy''
        exact hp _ hc.2 ⟨hc.1, I'.f y'', nearAt_child_parent _ _, capParent_seed hcap⟩

/-- **Lemma 2⁺(a) on gardens.** If `Π₀(LG)` avoids `R`, then `Π₀(LG')` avoids `R'` and the correspondence maps
`Π₀(LG) ∖ R` onto `Π₀(LG') ∖ R'`. -/
theorem prot_transport (I : OutIso LG LG' R R') (I' : OutIso LG' LG R' R) (hinv : ∀ z', NodeAt LG' z' → z' ∉ R' → I.f (I'.f z') = z')
    (hinv' : ∀ z, NodeAt LG z → z ∉ R → I'.f (I.f z) = z) (hR : RegionOK LG R) (hR' : RegionOK LG' R') (hp : NoProtIn LG J pat R) :
    NoProtIn LG' J pat R' ∧
      ∀ z, NodeAt LG z → z ∉ R → (ProtAt LG' J pat (I.f z) ↔ ProtAt LG J pat z) := by
  have hs' := noSeed' I' hR hR' hp
  -- seeds of LG' off R' pull back
  have hpull : ∀ σ', NodeAt LG' σ' → σ' ∉ R' → SeedAt LG' J pat σ' → SeedAt LG J pat (I'.f σ') := by
    intro σ' hn' hR'σ hσ'
    obtain ⟨hn, hRσ⟩ := I'.node σ' hn' hR'σ
    have e := hinv σ' hn' hR'σ
    exact (I.seed hR hR' hp hs' hn hRσ).mp (by rw [e]; exact hσ')
  have hp' : NoProtIn LG' J pat R' := by
    rintro z' hz' ⟨hn', σ', hnear, hσ'⟩
    have hσR' : σ' ∉ R' := fun h => hs' _ h hσ'
    have hσn' := hσ'.1
    have hσ := hpull σ' hσn' hσR' hσ'
    rcases nearAt_cases hnear with he | ⟨i, he⟩ | ⟨i, he⟩
    · subst he
      exact hσR' hz'
    · -- `z'` is the parent of `σ'`
      have hne : σ'.2 ≠ [] := by rw [he]; simp [addrExt]
      have hpar : (σ'.1, σ'.2.dropLast) = z' := by rw [he]; simp [addrExt]
      have hR2 := (I'.parentR σ' hσn' hσR' hne).mp (by rw [hpar]; exact hz')
      obtain ⟨hσn, -⟩ := I'.node σ' hσn' hσR'
      have hne2 : (I'.f σ').2 ≠ [] := fun h => hne ((I'.root σ' hσn' hσR').mp h)
      have hz := addrExt_parent hne2
      refine hp _ hR2 ⟨nodeAt_of_branchAt (branchAt_of_child (i := (I'.f σ').2.getLast hne2)
        (by rw [← hz]; exact hσn)), I'.f σ', ?_, hσ⟩
      conv_rhs => rw [hz]
      exact nearAt_parent_child _ _
    · -- `z'` is a child of `σ'`
      have hc := (I'.childR σ' i hσn' hσR').mp ⟨by rw [← he]; exact hn', by rw [← he]; exact hz'⟩
      exact hp _ hc.2 ⟨hc.1, I'.f σ', nearAt_child_parent _ _, hσ⟩
  refine ⟨hp', fun z hn hz => ⟨fun h' => ?_, fun h => I.prot hR hR' hp hs' hn hz h⟩⟩
  -- backwards: use `I'` at `I.f z`
  obtain ⟨hn', hz'⟩ := I.node z hn hz
  have hs : NoSeedIn LG J pat R := fun y hy hsy => hp y hy (seed_protAt hsy)
  have h2 := I'.prot hR' hR hp' hs hn' hz' h'
  rwa [hinv' z hn hz] at h2

end Two

end WaveTurbulence.Flower.MkMark
