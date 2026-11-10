/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.DV
public import WaveTurbulence.Foundations.Molecule.VineRemoval
/-! # H-DS: the removal clause of TARGET `subsetvc` from N3 Cor 1.16′(3) (packet L6-HDS; hand-written)

Main proves the simultaneous-removal clause of TARGET Lemma `subsetvc` (L2431–L2434) by explicit paths in the drawn
templates, in the vocabulary `RemovalPiece`, `remainingAtoms`, `removeBlocks` (main's `Molecule/VineRemoval.lean`). For
the low family the clause is N3 Cor 1.16′(3) (`Src.DSInputs.cor116`), stated by L3 for a family of objects
(`Struct.remAtoms`, `Struct.remAdj`, sources' semantics). This module is the bridge:
* `Realizes O P`: the removal piece `P` removes the object `O` (same atoms, joints, and darts = `O.ContainsDart`);
* `interior_containsDart`: in a molecule, every dart at an interior atom of an object is a dart of the object (degree `4`
  inside, at most `4` overall), so a bond kept by the removal has kept end atoms;
* `removal_connected_of_objects`: removing a family of pairwise disjoint proper objects from a vine of the low family
  leaves the remaining atoms connected in `removeBlocks`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H.DS
open Finset WaveTurbulence.Vine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- The removal piece `P` is the removal of the object `O`: same atoms, joints and removed darts. -/
def Realizes (O : Src.Object Src.γL M) (P : RemovalPiece V D) : Prop :=
  O.atoms = P.atoms ∧ O.upper = P.left ∧ O.lower = P.right ∧ ∀ x, x ∈ P.darts ↔ O.ContainsDart x

theorem inGroup_mate {S : Finset V} {x : D} : M.InGroup S (M.mate x) ↔ M.InGroup S x := by
  unfold Molecule.InGroup
  rw [M.mate_mate]
  exact and_comm

theorem containsDart_mate (O : Src.Object Src.γL M) {x : D} : O.ContainsDart (M.mate x) ↔ O.ContainsDart x := by
  unfold Src.Object.ContainsDart
  rcases O with ⟨A, u, l, sh⟩
  cases sh with
  | vc h => exact inGroup_mate
  | hyper R =>
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun h => h2 (by rw [h]), fun h => h1 (by rw [h, M.mate_mate]), inGroup_mate.mp h3⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun h => h2 (by rw [← h, M.mate_mate]), fun h => h1 ?_, inGroup_mate.mpr h3⟩
      have := congrArg M.mate h
      rwa [M.mate_mate, M.mate_mate] at this

/-- In a molecule every dart at an interior atom of an object is a dart of the object. -/
theorem interior_containsDart (hM : M.IsMolecule) (O : Src.Object Src.γL M) {v : V} (hv : v ∈ O.atoms)
    (hvu : v ≠ O.upper) (hvl : v ≠ O.lower) {x : D} (hx : M.atom x = v) : O.ContainsDart x := by
  have hvm : v ∈ M.atoms := hx ▸ M.atom_mem x
  have hle : M.deg v ≤ 4 := Mole.deg_le_four M hM hvm
  have h4 : M.degIn O.atoms v = 4 := by
    rcases O with ⟨A, u, l, sh⟩
    cases sh with
    | vc h => exact h.1.2.2.2.2.2.2.2.2.1 v hv hvu hvl
    | hyper R => exact (Mole.hyperBlock_degrees M ⟨R.added, R.ends_eq, R.adjoint.1⟩).2.2 v hv hvu hvl
  have hin : M.InGroup O.atoms x := by
    have hsub : (M.dartsAt v).filter (fun y => M.InGroup O.atoms y) ⊆ M.dartsAt v := filter_subset _ _
    have heq : (M.dartsAt v).filter (fun y => M.InGroup O.atoms y) = M.dartsAt v := by
      apply eq_of_subset_of_card_le hsub
      unfold Molecule.degIn at h4
      unfold Molecule.deg at hle
      omega
    have hxm : x ∈ M.dartsAt v := by
      unfold Molecule.dartsAt
      simp [hx]
    rw [← heq] at hxm
    exact (mem_filter.mp hxm).2
  rcases O with ⟨A, u, l, sh⟩
  cases sh with
  | vc h => exact hin
  | hyper R =>
    have hends := R.ends_eq
    unfold Molecule.ends at hends
    refine ⟨?_, ?_, hin⟩
    · intro he
      rw [← he] at hends
      rcases Sym2.eq_iff.mp hends with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hvu (by rw [← hx]; exact h1)
      · exact hvl (by rw [← hx]; exact h1)
    · intro he
      rcases Sym2.eq_iff.mp hends with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact hvl (by rw [← hx, he]; exact h2)
      · exact hvu (by rw [← hx, he]; exact h2)

/-- A list of realized removal pieces as an indexed family of objects without repetition. -/
theorem exists_family (ps : List (RemovalPiece V D)) (hO : ∀ P ∈ ps, ∃ O : Src.Object Src.γL M, Realizes O P) :
    ∃ (n : ℕ) (U : Fin n → Src.Object Src.γL M) (g : Fin n → RemovalPiece V D),
      (∀ i, g i ∈ ps) ∧ (∀ P ∈ ps, ∃ i, g i = P) ∧ Function.Injective g ∧ ∀ i, Realizes (U i) (g i) := by
  classical
  have hmem : ∀ i : Fin ps.dedup.length, ps.dedup.get i ∈ ps := fun i => List.mem_dedup.mp (List.get_mem _ i)
  refine ⟨ps.dedup.length, fun i => Classical.choose (hO (ps.dedup.get i) (hmem i)), ps.dedup.get, hmem,
    fun P hP => List.mem_iff_get.mp (List.mem_dedup.mpr hP), fun i j h => (List.nodup_dedup ps).get_inj_iff.mp h,
    fun i => Classical.choose_spec (hO (ps.dedup.get i) (hmem i))⟩

theorem remAtoms_iff {S : Finset V} {ps : List (RemovalPiece V D)} {n : ℕ} {U : Fin n → Src.Object Src.γL M}
    {g : Fin n → RemovalPiece V D} (hmem : ∀ i, g i ∈ ps) (hget : ∀ P ∈ ps, ∃ i, g i = P)
    (hU : ∀ i, Realizes (U i) (g i)) (v : V) :
    v ∈ TVine.Struct.remAtoms S U ↔ v ∈ remainingAtoms S ps := by
  have key : ∀ i, (v ∈ (U i).atoms \ {(U i).upper, (U i).lower} ↔ v ∈ (g i).interior) := by
    intro i
    unfold RemovalPiece.interior
    rw [(hU i).1, (hU i).2.1, (hU i).2.2.1]
  unfold TVine.Struct.remAtoms remainingAtoms
  rw [mem_sdiff, mem_filter, mem_biUnion]
  constructor
  · rintro ⟨hvS, hv⟩
    refine ⟨hvS, fun P hP hvP => hv ?_⟩
    obtain ⟨i, rfl⟩ := hget P hP
    exact ⟨i, mem_univ _, (key i).mpr hvP⟩
  · rintro ⟨hvS, hv⟩
    refine ⟨hvS, ?_⟩
    rintro ⟨i, -, hvi⟩
    exact hv _ (hmem i) ((key i).mp hvi)

/-- A dart of the group `S` contained in none of the objects is kept by the removal. -/
theorem keepDart_of_objects (hM : M.IsMolecule) {S : Finset V} {ps : List (RemovalPiece V D)} {n : ℕ}
    {U : Fin n → Src.Object Src.γL M} {g : Fin n → RemovalPiece V D} (hmem : ∀ i, g i ∈ ps)
    (hget : ∀ P ∈ ps, ∃ i, g i = P) (hU : ∀ i, Realizes (U i) (g i)) {x : D} (hxS : M.InGroup S x)
    (hxU : ∀ i, ¬(U i).ContainsDart x) : KeepDart M S ps x := by
  have hremv : ∀ y, M.InGroup S y → (∀ i, ¬(U i).ContainsDart y) → M.atom y ∈ remainingAtoms S ps := by
    intro y hyS hyU
    refine (remAtoms_iff hmem hget hU _).mp ?_
    unfold TVine.Struct.remAtoms
    rw [mem_sdiff, mem_biUnion]
    refine ⟨hyS.1, ?_⟩
    rintro ⟨i, -, hi⟩
    rw [mem_sdiff, mem_insert, mem_singleton, not_or] at hi
    exact hyU i (interior_containsDart hM (U i) hi.1 hi.2.1 hi.2.2 rfl)
  refine ⟨hremv x hxS hxU,
    hremv (M.mate x) (inGroup_mate.mpr hxS) (fun i h => hxU i ((containsDart_mate (U i)).mp h)), ?_⟩
  intro P hP
  obtain ⟨i, rfl⟩ := hget P hP
  exact ⟨fun h => hxU i (((hU i).2.2.2 x).mp h),
    fun h => hxU i ((containsDart_mate (U i)).mp (((hU i).2.2.2 _).mp h))⟩

section bridge

/-- **TARGET `subsetvc` removal clause in a single vine of the low family (N3 Cor 1.16′(3)).** Removing a family of
pairwise disjoint proper objects (each removal piece removes an object) from a vine of the low family leaves the
remaining atoms connected. -/
theorem removal_connected_of_objects (hM : M.IsMolecule) {S : Finset V} {a b : V}
    (hV : Src.IsSomeVine Src.γL M S a b) (ps : List (RemovalPiece V D))
    (hO : ∀ P ∈ ps, ∃ O : Src.Object Src.γL M, Realizes O P)
    (hsub : ∀ P ∈ ps, P.atoms ⊂ S)
    (hdis : ∀ P ∈ ps, ∀ Q ∈ ps, P ≠ Q → Disjoint P.atoms Q.atoms) :
    ∀ u ∈ remainingAtoms S ps, ∀ v ∈ remainingAtoms S ps, (removeBlocks M S ps).SameComponent u v := by
  obtain ⟨n, U, g, hmem, hget, hinj, hU⟩ := exists_family ps hO
  have hcor := (Src.DSInputs.cor116 (V := V) (D := D) M Src.γL Src.γL_le S a b
    (Src.isSomeVine_γL_iff.mp hV)).2 n U
    (fun i => by rw [(hU i).1]; exact hsub _ (hmem i))
    (fun i j hij => by
      rw [(hU i).1, (hU j).1]
      exact hdis _ (hmem i) _ (hmem j) (fun h => hij (hinj h)))
  intro u hu v hv
  have h := hcor u ((remAtoms_iff hmem hget hU u).mpr hu) v ((remAtoms_iff hmem hget hU v).mpr hv)
  apply Relation.EqvGen.mono _ u v h
  intro p q hpq
  obtain ⟨x, hxS, hxU, hxp, hxq⟩ := hpq
  exact ⟨⟨x, keepDart_of_objects hM hmem hget hU hxS hxU⟩, hxp, hxq⟩

/-- **N3 Lemma P in the removal vocabulary.** In a vine of the low family with `σ(a, b) = 1` and joint bond `f`, removing
a family of pairwise disjoint objects avoiding the joints leaves the remaining atoms connected by kept bonds other
than `f`. -/
theorem removal_connected_avoiding (hM : M.IsMolecule) {S : Finset V} {a b : V}
    (hV : Src.IsSomeVine Src.γL M S a b) (hσ : M.sigma a b = 1) {f : D} (hf : M.ends f = s(a, b))
    (ps : List (RemovalPiece V D)) (hO : ∀ P ∈ ps, ∃ O : Src.Object Src.γL M, Realizes O P)
    (hsub : ∀ P ∈ ps, P.atoms ⊆ S) (hj : ∀ P ∈ ps, a ∉ P.atoms ∧ b ∉ P.atoms)
    (hdis : ∀ P ∈ ps, ∀ Q ∈ ps, P ≠ Q → Disjoint P.atoms Q.atoms) :
    ∀ u ∈ remainingAtoms S ps, ∀ v ∈ remainingAtoms S ps,
      Relation.EqvGen (fun p q => ∃ x : D, KeepDart M S ps x ∧ x ≠ f ∧ x ≠ M.mate f ∧ M.atom x = p ∧
        M.atom (M.mate x) = q) u v := by
  obtain ⟨n, U, g, hmem, hget, hinj, hU⟩ := exists_family ps hO
  have hdisU : ∀ i j, i ≠ j → Disjoint (U i).atoms (U j).atoms := fun i j hij => by
    rw [(hU i).1, (hU j).1]
    exact hdis _ (hmem i) _ (hmem j) (fun h => hij (hinj h))
  have hcor := (Src.DSInputs.cor116 (V := V) (D := D) M Src.γL Src.γL_le S a b
    (Src.isSomeVine_γL_iff.mp hV)).2 n U
    (fun i => by
      rw [(hU i).1]
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub _ (hmem i), fun h => (hj _ (hmem i)).1 (h ▸ hV.block.2.1)⟩)
    hdisU
  have hP := (Src.DSInputs.lemmaP (V := V) (D := D)) M Src.γL S a b (Src.isSomeVine_γL_iff.mp hV) hσ f hf n U
    (fun i => by rw [(hU i).1]; exact hsub _ (hmem i))
    (fun i => by rw [(hU i).1]; exact hj _ (hmem i)) hdisU hcor
  intro u hu v hv
  apply Relation.EqvGen.mono _ u v (hP u ((remAtoms_iff hmem hget hU u).mpr hu) v ((remAtoms_iff hmem hget hU v).mpr hv))
  intro p q hpq
  obtain ⟨x, hxf, hxmf, hxS, hxU, hxp, hxq⟩ := hpq
  exact ⟨x, keepDart_of_objects hM hmem hget hU hxS hxU, hxf, hxmf, hxp, hxq⟩

end bridge

/-! ### The joint bond and lifting of removal paths -/

/-- With `σ(a, b) = 1` some bond joins `a` and `b`. -/
theorem exists_joint_bond {a b : V} (hσ : M.sigma a b = 1) : ∃ f : D, M.ends f = s(a, b) := by
  unfold Molecule.sigma Molecule.bondsBetween at hσ
  obtain ⟨f, hf⟩ := Finset.card_pos.mp (by omega : 0 < (M.bonds.filter fun x => M.ends x = s(a, b)).card)
  exact ⟨f, (mem_filter.mp hf).2⟩

/-- With `σ(a, b) = 1` and `a, b` the joints of a block, the darts of the group `{a, b}` are those of the joint bond. -/
theorem pair_group_darts {S : Finset V} {a b : V} (hS : M.IsBlock S a b) (hσ : M.sigma a b = 1) {f : D}
    (hf : M.ends f = s(a, b)) {x : D} (hx : M.InGroup {a, b} x) : x = f ∨ x = M.mate f := by
  have hp := pair_degree_one hS hσ
  have hone : ∀ c, c = a ∨ c = b → ∀ y z : D, M.atom y = c → M.atom z = c → M.InGroup {a, b} y →
      M.InGroup {a, b} z → y = z := by
    intro c hc y z hy hz hgy hgz
    have hcard : ((M.dartsAt c).filter fun w => M.InGroup {a, b} w).card ≤ 1 := by
      rcases hc with rfl | rfl
      · have := hp.1
        unfold Molecule.degIn at this
        omega
      · have := hp.2
        unfold Molecule.degIn at this
        omega
    exact Finset.card_le_one.mp hcard y (mem_filter.mpr ⟨by simp [Molecule.dartsAt, hy], hgy⟩) z
      (mem_filter.mpr ⟨by simp [Molecule.dartsAt, hz], hgz⟩)
  have hfab : (M.atom f = a ∧ M.atom (M.mate f) = b) ∨ (M.atom f = b ∧ M.atom (M.mate f) = a) := Sym2.eq_iff.mp hf
  have hgf : M.InGroup {a, b} f := by
    rcases hfab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by simp [h1], by simp [h2]⟩
    · exact ⟨by simp [h1], by simp [h2]⟩
  have hgmf : M.InGroup {a, b} (M.mate f) := inGroup_mate.mpr hgf
  have hxc : M.atom x = a ∨ M.atom x = b := by simpa using hx.1
  rcases hfab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hxc with hxa | hxb
  · exact Or.inl (hone a (Or.inl rfl) x f hxa h1 hx hgf)
  · exact Or.inr (hone b (Or.inr rfl) x (M.mate f) hxb h2 hx hgmf)
  · exact Or.inr (hone a (Or.inl rfl) x (M.mate f) hxa h2 hx hgmf)
  · exact Or.inl (hone b (Or.inr rfl) x f hxb h1 hx hgf)

/-- A removal path avoiding the bond `f` lifts along an inclusion of the kept darts other than `f`. -/
theorem avoiding_lift {S S' : Finset V} {ps ps' : List (RemovalPiece V D)} {f : D}
    (hk : ∀ x, KeepDart M S ps x → x ≠ f → x ≠ M.mate f → KeepDart M S' ps' x) {u v : V}
    (h : Relation.EqvGen (fun p q => ∃ x : D, KeepDart M S ps x ∧ x ≠ f ∧ x ≠ M.mate f ∧ M.atom x = p ∧
        M.atom (M.mate x) = q) u v) : (removeBlocks M S' ps').SameComponent u v := by
  apply Relation.EqvGen.mono _ u v h
  intro p q hpq
  obtain ⟨x, hx, hxf, hxmf, hxp, hxq⟩ := hpq
  exact ⟨⟨x, hk x hx hxf hxmf⟩, hxp, hxq⟩

/-- With `σ(a, b) = 1` some dart goes from `a` to `b`. -/
theorem exists_joint_dart {a b : V} (hσ : M.sigma a b = 1) : ∃ z : D, M.atom z = a ∧ M.atom (M.mate z) = b := by
  obtain ⟨f, hf⟩ := exists_joint_bond (M := M) hσ
  rcases Sym2.eq_iff.mp hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨f, h1, h2⟩
  · exact ⟨M.mate f, h2, by rw [M.mate_mate]; exact h1⟩

end WaveTurbulence.GammaLow.FinalCount.H.DS
