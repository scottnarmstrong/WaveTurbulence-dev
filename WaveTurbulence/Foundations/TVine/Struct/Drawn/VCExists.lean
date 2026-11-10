/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Drawn.VCObjects
public import WaveTurbulence.Foundations.FinalCount.S1OverlapMain
public import WaveTurbulence.Foundations.Spine.SourceThreeBlockExclusion
public import WaveTurbulence.Foundations.Molecule.VineNestedBlockRecognition
public import WaveTurbulence.Foundations.Molecule.VineBlockJoints
public import WaveTurbulence.Foundations.TVine.Struct.Statement

/-!
# Lemma 8.1′ (TARGET `vinechainlem` with DV′; packet L3D)

TARGET `vinechainlem` (L1930–L1933; DH23 Lemma 8.1) over the family `𝒱_γ` with `DV` replaced by `DV′` (N2 N6,
`research-gamma-half-2/NOTES.md` L978–L983; REFEREED, REF2 item 1 and N2's correction E2/N6): for every molecule there
is a unique collection of disjoint atomic groups, each an HV, VC, HVC or DV′, such that every vine-like object is
contained in one of them.

The proof is main's (`FinalCount/S1OverlapMain`, `S1Exists`, `S1Vinechain`, `Spine/SourceDoubleVinePartner`; sha256 in
`COPIED-SHA256SUMS`), as N2 N6 says ("DH23's proof of Lemma 8.1 then holds verbatim"):
* two distinct overlapping maximal vine-like sets are two single members of `𝒱_γ` with the same joints, meeting
  exactly in them, with `σ = 1` (`ov`; main: "two type-V vines"; here `member_of_chain_sigma`);
* a third maximal set meeting one of them is the other one (`partner`; "a third maximal object meeting one of them
  would raise both joints to degree 4, giving a saturated component": main's `no_three_joint_blocks`);
* the collection: isolated maximal vine-like sets and the DV′ unions of overlapping pairs.
Uniqueness is L5a's `GammaLow.Fama.partition_unique` (main `S1Unique`, family-free).

The only named input is N2 Theorem 1.15 (F1) for T-vines (`TVineF1Input`, owner L3).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.Drawn.VC

open Finset WaveTurbulence.GammaLow.FinalCount WaveTurbulence.GammaLow.Fama

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {γ : ℝ}

/-! ## The overlap dichotomy (main `S1OverlapMain`), with `DV′` -/

theorem overlap_dichotomy (hF1 : TVineF1Input.{u, v}) (hM : M.IsMolecule) {P Q : Src.Object γ M}
    (hne : (P.atoms ∩ Q.atoms).Nonempty) (hPQ : ¬ P.atoms ⊆ Q.atoms) (hQP : ¬ Q.atoms ⊆ P.atoms) :
    (∃ W : Src.Object γ M, P.atoms ∪ Q.atoms ⊆ W.atoms) ∨
    (∃ a b, Src.IsSomeVine γ M P.atoms a b ∧ Src.IsSomeVine γ M Q.atoms a b ∧ P.atoms ∩ Q.atoms = {a, b} ∧
      M.sigma a b = 1) := by
  obtain ⟨⟨RA⟩, hdA, hiA⟩ := object_overlap_premises hF1 P
  obtain ⟨⟨RB⟩, hdB, hiB⟩ := object_overlap_premises hF1 Q
  obtain ⟨hA, hB, hcase⟩ := Mole.molecule_overlap_classification M hM RA RB hne hPQ hQP hdA hdB hiA hiB
  obtain ⟨nP, hcP⟩ := chain_of_isBlock P hA
  obtain ⟨nQ, hcQ⟩ := chain_of_isBlock Q hB
  rcases hcase with ⟨hj, hint, hsA, hsB⟩ | ⟨hj, _, a, b, c, hjA, hjB, hab, hac, hbc, hint, _⟩ |
      ⟨hdis, ⟨T⟩⟩
  · -- scenario (a): two single members of `𝒱_γ` with the same joints and `σ = 1`
    right
    have hvP := member_of_chain_sigma hM hcP hA hsA
    have hvQ := member_of_chain_sigma hM hcQ hB hsB
    refine ⟨P.upper, P.lower, hvP, ?_, hint, hsA⟩
    rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2] at hvQ; exact hvQ
    · rw [← h1, ← h2] at hvQ; exact isSomeVine_swap hvQ
  · -- scenario (b): one common joint
    left
    have hcP' : Src.Chain γ M P.atoms a c nP := chain_orient hcP hjA
    have hcQ' : Src.Chain γ M Q.atoms c b nQ :=
      chain_orient hcQ (show ({Q.upper, Q.lower} : Finset V) = {c, b} by rw [hjB, Finset.pair_comm])
    have hbP : M.IsBlock P.atoms a c := block_orient hA hjA
    have hbQ : M.IsBlock Q.atoms c b := block_orient hB (by rw [hjB, Finset.pair_comm])
    obtain ⟨W, hW, _, _⟩ := exists_object_union hM hcP' hcQ' hint hbP hbQ
    exact ⟨W, hW.symm ▸ Finset.Subset.refl _⟩
  · -- scenario (c): three concatenated blocks
    left
    have hcP' : Src.Chain γ M P.atoms T.p0 T.p2 nP := chain_orient hcP T.left_joints
    have hcQ' : Src.Chain γ M Q.atoms T.p1 T.p3 nQ := chain_orient hcQ T.right_joints
    have hbP : M.IsBlock P.atoms T.p0 T.p2 := block_orient hA T.left_joints
    have hbQ : M.IsBlock Q.atoms T.p1 T.p3 := block_orient hB T.right_joints
    have hQeq : Q.atoms = T.C1 ∪ T.C2 := T.right_union
    have hbQ' : M.IsBlock (T.C1 ∪ T.C2) T.p1 T.p3 := hQeq ▸ hbQ
    have h1ne : T.p1 ≠ T.p2 := T.block1.2.2.2.1
    have h2ne : T.p2 ≠ T.p3 := T.block2.2.2.2.1
    have hp1 : T.p1 ∈ T.C1 := T.block1.2.1
    have hp3 : T.p3 ∈ T.C2 := T.block2.2.2.1
    have HL : ∀ x : D, M.atom x ∈ T.C1 → M.atom x ≠ T.p2 → M.InGroup Q.atoms x →
        M.InGroup T.C1 x := by
      intro x hx hx2 hg
      exact LGSpine.block_union_darts_in_left T.block1 T.block2 T.right_inter hbQ' hx hx2 rfl (hQeq ▸ hg)
    obtain ⟨n0, n1, _, hc2⟩ := chain_split hF1 hcQ' hQeq T.right_inter hp1 hp3 h1ne (Ne.symm h2ne) HL
    have hint : P.atoms ∩ T.C2 = {T.p2} := by
      have hmem : ∀ x, x ∈ P.atoms ↔ x ∈ T.C0 ∨ x ∈ T.C1 := by
        intro x
        exact (Eq.to_iff (congrArg (fun s => x ∈ s) T.left_union)).trans mem_union
      ext x
      constructor
      · intro hx
        obtain ⟨hxP, hx2⟩ := mem_inter.mp hx
        rcases (hmem x).mp hxP with h0 | h1
        · exact absurd hx2 (Finset.disjoint_left.mp T.exterior_disjoint h0)
        · have : x ∈ T.C1 ∩ T.C2 := mem_inter.mpr ⟨h1, hx2⟩
          rw [T.right_inter] at this
          exact this
      · intro hx
        have hx' := mem_singleton.mp hx
        rw [hx']
        have : T.p2 ∈ T.C1 ∩ T.C2 := by rw [T.right_inter]; exact mem_singleton_self _
        exact mem_inter.mpr ⟨(hmem _).mpr (Or.inr (mem_inter.mp this).1), (mem_inter.mp this).2⟩
    obtain ⟨W, hW, _, _⟩ := exists_object_union hM hcP' hc2 hint hbP T.block2
    refine ⟨W, ?_⟩
    rw [hW]
    apply Finset.union_subset subset_union_left
    intro x hx
    have hx' : x ∈ T.C1 ∪ T.C2 := hQeq ▸ hx
    rcases mem_union.mp hx' with h1 | h2
    · have hxP : x ∈ P.atoms := by rw [T.left_union]; exact mem_union_right _ h1
      exact mem_union_left _ hxP
    · exact mem_union_right _ h2

/-! ## Partner uniqueness (main `SourceDoubleVinePartner`), with `σ = 1` members -/

/-- At a joint of a member with `σ = 1`, the pair of joints carries exactly one incidence. -/
theorem degIn_pair_of_sigma {S : Finset V} {a b : V} (h : Src.IsSomeVine γ M S a b) (hσ : M.sigma a b = 1) :
    M.degIn {a, b} a = 1 := by
  have hB := member_block h
  have hnl : ¬ M.Adj a a := Vine.connected_degree_two_no_loop M (member_connected h) hB.2.1 hB.2.2.1
    hB.2.2.2.1 (Mole.block_joint_degrees M hB).1
  unfold Molecule.degIn
  have heq : (M.dartsAt a).filter (M.InGroup {a, b}) =
      (M.dartsAt a).filter (fun x => M.atom (M.mate x) = b) := by
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨hx, -, h2⟩
      refine ⟨hx, ?_⟩
      rcases mem_insert.mp h2 with h | h
      · exact absurd ⟨x, (Mole.mem_dartsAt M a x).mp hx, h⟩ hnl
      · exact mem_singleton.mp h
    · rintro ⟨hx, h⟩
      refine ⟨hx, ?_, ?_⟩
      · rw [(Mole.mem_dartsAt M a x).mp hx]; exact mem_insert_self _ _
      · rw [h]; exact mem_insert_of_mem (mem_singleton_self _)
  rw [heq, ← Mole.bondsBetween_eq_card_darts M hB.2.2.2.1]
  exact hσ

/-- Three distinct `σ = 1` members of `𝒱_γ` at the same joints would saturate a component. -/
theorem partner_unique (hF1 : TVineF1Input.{u, v}) (hM : M.IsMolecule) {S T U : Finset V} {a b : V}
    (hS : Src.IsSomeVine γ M S a b) (hT : Src.IsSomeVine γ M T a b) (hU : Src.IsSomeVine γ M U a b)
    (hσ : M.sigma a b = 1) (hST : S ∩ T = {a, b}) (hSU : S ∩ U = {a, b}) : T = U := by
  have hTB := member_block hT
  have hUB := member_block hU
  by_cases hTU : T ⊆ U
  · exact Vine.nested_blocks_both_joints_eq M hTB hUB (member_connected hU) hTU hTB.2.1 hTB.2.2.1
  · have hInt := Mole.block_same_joints_intersection M hM hTB hUB hTU (member_interior_connected hF1 hT)
    have hpa := degIn_pair_of_sigma hS hσ
    have hpb : M.degIn {b, a} b = 1 := degIn_pair_of_sigma (isSomeVine_swap hS) (by rwa [sigma_comm])
    rw [Finset.pair_comm] at hpb
    exact (LGSpine.no_three_joint_blocks M hM (member_block hS) hTB hUB hST hSU hInt (by
      intro w hw
      rcases mem_insert.mp hw with rfl | hw
      · exact hpa
      · exact (mem_singleton.mp hw).symm ▸ hpb)).elim

theorem partner_unique_unordered (hF1 : TVineF1Input.{u, v}) (hM : M.IsMolecule) {S T U : Finset V}
    {a b c e : V} (hS : Src.IsSomeVine γ M S a b) (hT : Src.IsSomeVine γ M T a b)
    (hS' : Src.IsSomeVine γ M S c e) (hU : Src.IsSomeVine γ M U c e) (hσ : M.sigma a b = 1)
    (hST : S ∩ T = {a, b}) (hSU : S ∩ U = {c, e}) : T = U := by
  have hj := Vine.block_joints_unique M (member_block hS) (member_block hS')
  have hj' : ({a, b} : Set V) = {c, e} := by
    simpa only [Finset.coe_pair] using congrArg (fun s : Finset V => (s : Set V)) hj
  rcases Set.pair_eq_pair_iff.mp hj' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact partner_unique hF1 hM hS hT hU hσ hST hSU
  · exact partner_unique hF1 hM hS hT (isSomeVine_swap hU) hσ hST (by rw [Finset.pair_comm]; exact hSU)

/-! ## Existence (main `S1Exists`, `S1Vinechain`) -/

/-- The maximal vine-like atom sets. -/
def maxVL (γ : ℝ) (M : Molecule V D) : Set (Finset V) :=
  {S | IsVineLikeSetG γ M S ∧ ∀ T, IsVineLikeSetG γ M T → S ⊆ T → T = S}

/-- The collection of `vinechainlem′`: isolated maximal vine-like sets, and the DV′ unions of two intersecting
maximal vine-like sets. -/
def stage1Collection (γ : ℝ) (M : Molecule V D) : Set (Finset V) :=
  {X | (X ∈ maxVL γ M ∧ ∀ T ∈ maxVL γ M, T ≠ X → Disjoint X T) ∨
    ∃ S ∈ maxVL γ M, ∃ T ∈ maxVL γ M, S ≠ T ∧ ¬ Disjoint S T ∧ X = S ∪ T}

section existence

variable (hF1 : TVineF1Input.{u, v}) (hM : M.IsMolecule)
include hF1 hM

theorem ov {S T : Finset V} (hS : S ∈ maxVL γ M) (hT : T ∈ maxVL γ M) (hne : S ≠ T) (hn : ¬ Disjoint S T) :
    ∃ a b, Src.IsSomeVine γ M S a b ∧ Src.IsSomeVine γ M T a b ∧ S ∩ T = {a, b} ∧ M.sigma a b = 1 := by
  obtain ⟨P, hP⟩ := object_of_isVineLikeSet hS.1
  obtain ⟨Q, hQ⟩ := object_of_isVineLikeSet hT.1
  have hnST : ¬ S ⊆ T := fun h => hne (hS.2 T hT.1 h).symm
  have hnTS : ¬ T ⊆ S := fun h => hne (hT.2 S hS.1 h)
  have hnon : (P.atoms ∩ Q.atoms).Nonempty := by
    rw [hP, hQ]; exact Finset.not_disjoint_iff_nonempty_inter.mp hn
  rcases overlap_dichotomy hF1 hM hnon (by rwa [hP, hQ]) (by rwa [hP, hQ]) with ⟨W, hW⟩ | ⟨a, b, h1, h2, h3, h4⟩
  · exfalso
    have hWvl := isVineLikeSet_of_object W
    have hSW : S ⊆ W.atoms := by rw [← hP]; exact subset_union_left.trans hW
    have hTW : T ⊆ W.atoms := by rw [← hQ]; exact subset_union_right.trans hW
    have hWS := hS.2 _ hWvl hSW
    exact hnTS (hWS ▸ hTW)
  · exact ⟨a, b, hP ▸ h1, hQ ▸ h2, by rw [← hP, ← hQ]; exact h3, h4⟩

theorem partner {S T U : Finset V} (hS : S ∈ maxVL γ M) (hT : T ∈ maxVL γ M)
    (hU : U ∈ maxVL γ M) (hne : S ≠ T) (hn : ¬ Disjoint S T) (hUS : ¬ Disjoint U S) :
    U = S ∨ U = T := by
  by_cases hUeq : U = S
  · exact Or.inl hUeq
  · right
    obtain ⟨a, b, hSa, hTa, hSTab, hσ⟩ := ov hF1 hM hS hT hne hn
    obtain ⟨c, e, hSc, hUc, hSUce, -⟩ := ov hF1 hM hS hU (Ne.symm hUeq) (fun h => hUS h.symm)
    exact (partner_unique_unordered hF1 hM hSa hTa hSc hUc hσ hSTab hSUce).symm

theorem pair_eq {S T S' T' : Finset V} (hS : S ∈ maxVL γ M) (hT : T ∈ maxVL γ M)
    (hS' : S' ∈ maxVL γ M) (hT' : T' ∈ maxVL γ M) (hne : S ≠ T) (hn : ¬ Disjoint S T)
    (hne' : S' ≠ T') (hn' : ¬ Disjoint S' T') (hSS' : ¬ Disjoint S S') : S ∪ T = S' ∪ T' := by
  rcases partner hF1 hM hS hT hS' hne hn (fun h => hSS' h.symm) with h | h
  · subst h
    have hn'' : ¬ Disjoint T' S' := fun h => hn' h.symm
    rcases partner hF1 hM hS' hT hT' hne hn hn'' with h2 | h2
    · exact absurd h2.symm hne'
    · rw [h2]
  · subst h
    have hn'' : ¬ Disjoint T' S' := fun h => hn' h.symm
    rcases partner hF1 hM hS' hS hT' (Ne.symm hne) (fun h => hn h.symm) hn'' with h2 | h2
    · exact absurd h2.symm hne'
    · rw [h2, union_comm]

theorem stage1Collection_isGroup {X : Finset V} (hX : X ∈ stage1Collection γ M) : IsStage1GroupG γ M X := by
  rcases hX with ⟨hX, _⟩ | ⟨S, hS, T, hT, hne, hn, rfl⟩
  · exact isStage1Group_of_vineLike hX.1
  · obtain ⟨a, b, h1, h2, h3, h4⟩ := ov hF1 hM hS hT hne hn
    exact ⟨a, b, Or.inr (Or.inr (Or.inr ⟨h4, S, T, h1, h2, h3, rfl⟩))⟩

theorem iso_pair_false {X S' T' : Finset V} (hXi : ∀ T ∈ maxVL γ M, T ≠ X → Disjoint X T)
    (hS' : S' ∈ maxVL γ M) (hT' : T' ∈ maxVL γ M) (hne' : S' ≠ T') (hn' : ¬ Disjoint S' T') {z : V}
    (hzX : z ∈ X) (hz : z ∈ S' ∪ T') : False := by
  rcases mem_union.mp hz with h | h
  · by_cases hXS : S' = X
    · subst hXS
      exact hn' (hXi T' hT' (Ne.symm hne'))
    · exact Finset.disjoint_left.mp (hXi S' hS' hXS) hzX h
  · by_cases hXT : T' = X
    · subst hXT
      exact hn' (hXi S' hS' hne').symm
    · exact Finset.disjoint_left.mp (hXi T' hT' hXT) hzX h

theorem stage1Collection_disjoint : (stage1Collection γ M).Pairwise (fun S T => Disjoint S T) := by
  intro X hX Y hY hXY
  by_contra hnd
  obtain ⟨z, hzX, hzY⟩ := Finset.not_disjoint_iff.mp hnd
  rcases hX with ⟨hXm, hXi⟩ | ⟨S, hS, T, hT, hne, hn, rfl⟩ <;>
    rcases hY with ⟨hYm, hYi⟩ | ⟨S', hS', T', hT', hne', hn', rfl⟩
  · exact Finset.disjoint_left.mp (hXi Y hYm (Ne.symm hXY)) hzX hzY
  · exact iso_pair_false hF1 hM hXi hS' hT' hne' hn' hzX hzY
  · exact iso_pair_false hF1 hM hYi hS hT hne hn hzY hzX
  · apply hXY
    rcases mem_union.mp hzX with h1 | h1 <;> rcases mem_union.mp hzY with h2 | h2
    · exact pair_eq hF1 hM hS hT hS' hT' hne hn hne' hn' (fun h => Finset.disjoint_left.mp h h1 h2)
    · exact (pair_eq hF1 hM hS hT hT' hS' hne hn (Ne.symm hne') (fun h => hn' h.symm)
        (fun h => Finset.disjoint_left.mp h h1 h2)).trans (union_comm _ _)
    · exact (union_comm _ _).trans (pair_eq hF1 hM hT hS hS' hT' (Ne.symm hne) (fun h => hn h.symm) hne' hn'
        (fun h => Finset.disjoint_left.mp h h1 h2))
    · exact (union_comm _ _).trans ((pair_eq hF1 hM hT hS hT' hS' (Ne.symm hne) (fun h => hn h.symm)
        (Ne.symm hne') (fun h => hn' h.symm) (fun h => Finset.disjoint_left.mp h h1 h2)).trans
        (union_comm _ _))

end existence

theorem object_atoms_subset (P : Src.Object γ M) : P.atoms ⊆ M.atoms := by
  rcases P with ⟨S, a, b, shape⟩
  cases shape with
  | vc h => exact h.1.1
  | hyper R => exact R.adjoint.1.1

theorem isVineLikeSet_subset_atoms {S : Finset V} (h : IsVineLikeSetG γ M S) : S ⊆ M.atoms := by
  obtain ⟨P, rfl⟩ := object_of_isVineLikeSet h
  exact object_atoms_subset P

theorem exists_maxVL_above {S0 : Finset V} (h : IsVineLikeSetG γ M S0) : ∃ T ∈ maxVL γ M, S0 ⊆ T := by
  classical
  let s : Finset (Finset V) := M.atoms.powerset.filter (fun T => IsVineLikeSetG γ M T ∧ S0 ⊆ T)
  have hne : s.Nonempty :=
    ⟨S0, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (isVineLikeSet_subset_atoms h), h, subset_rfl⟩⟩
  obtain ⟨m, hmmax⟩ := Finset.exists_maximal hne
  have hm := hmmax.1
  have hm' := Finset.mem_filter.mp hm
  refine ⟨m, ⟨hm'.2.1, fun T' hT' hmT' => ?_⟩, hm'.2.2⟩
  have hTs : T' ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (isVineLikeSet_subset_atoms hT'),
    hT', hm'.2.2.trans hmT'⟩
  exact Finset.Subset.antisymm (hmmax.2 hTs hmT') hmT'

theorem stage1Collection_isPartition (hF1 : TVineF1Input.{u, v}) (hM : M.IsMolecule) :
    IsSourceVinePartitionG γ M (stage1Collection γ M) := by
  refine ⟨fun S hS => stage1Collection_isGroup hF1 hM hS, stage1Collection_disjoint hF1 hM, fun P => ?_⟩
  obtain ⟨X, hX, hPX⟩ := exists_maxVL_above (isVineLikeSet_of_object P)
  by_cases hiso : ∀ T ∈ maxVL γ M, T ≠ X → Disjoint X T
  · exact ⟨X, Or.inl ⟨hX, hiso⟩, hPX⟩
  · push Not at hiso
    obtain ⟨T, hT, hTX, hnd⟩ := hiso
    exact ⟨X ∪ T, Or.inr ⟨X, hX, T, hT, Ne.symm hTX, hnd, rfl⟩, hPX.trans subset_union_left⟩

/-- **Lemma 8.1′ (TARGET `vinechainlem` with `𝒱_γ` and `DV′`).** For every `γ` and every molecule there is a unique
collection of disjoint atomic groups, each an HV, VC, HVC or DV′ of `𝒱_γ`, such that every vine-like object is a
subset of one of them. (Conditional on N2 Thm 1.15 (F1), `TVineF1Input`.) -/
theorem vinechainlemPrime (hF1 : TVineF1Input.{u, v}) (γ : ℝ) (hM : M.IsMolecule) :
    ∃! C : Set (Finset V), IsSourceVinePartitionG γ M C :=
  ⟨stage1Collection γ M, stage1Collection_isPartition hF1 hM,
    fun _ hC => partition_unique hC (stage1Collection_isPartition hF1 hM)⟩

end WaveTurbulence.TVine.Struct.Drawn.VC

namespace WaveTurbulence.TVine.Struct.Drawn

universe u v

/-- **Lemma 8.1′**, as L5a's named input `GammaLow.Fama.VinechainlemPrimeInput` (universe `0`). -/
theorem vinechainlemPrimeInput (hF1 : VC.TVineF1Input.{0, 0}) : GammaLow.Fama.VinechainlemPrimeInput := by
  intro γ _ V D _ _ _ M hM
  exact VC.vinechainlemPrime hF1 γ hM

end WaveTurbulence.TVine.Struct.Drawn
