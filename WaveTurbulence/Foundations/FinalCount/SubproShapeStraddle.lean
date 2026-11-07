/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproShapeRem
public import WaveTurbulence.Foundations.FinalCount.SubproC2Disj
public import WaveTurbulence.Foundations.Spine.SourceContainerAbsorb
public import WaveTurbulence.Foundations.Spine.SourceDiamondClosed
public import WaveTurbulence.Foundations.Spine.SourceDiamondVine
public import WaveTurbulence.Foundations.Spine.SourceDiamondContradiction
public import WaveTurbulence.Foundations.Spine.SourceUnionEligible
public import WaveTurbulence.Foundations.Spine.MoleculeOverlapClassification
public import WaveTurbulence.Foundations.Spine.MoleculeOverlapCrossings
import Mathlib.Tactic

/-!
# S4-SHAPE: how a collected SG object can meet a host

A host `Q` (LG/ZG vine-like object) of a collected SG object `U` and another collected SG object `O`: if `O` is neither inside `Q`
nor disjoint from it, the overlap classification (TARGET `disjointlem`) leaves two cases.
* **one shared joint** `c`: `O ∩ Q = {c}`, and `c` is a joint of both;
* **two shared joints** (a diamond): `O ∩ Q` is the pair of common joints, and `O`, `Q` are two type-V vines, i.e. `O ∪ Q` is a DV.
The interleaved case is excluded by gap separation (lg-spine-u `sg_block_absorbed_by_container`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem straddle_object_host {M : Molecule V D} (hM : M.IsMolecule) {L γ η : ℝ} {w : Mom d} {c0 : V → Mom d}
    {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c0 κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c0 v = 0)
    (Q O : Object M) (hQk : Q.HasGapKind L γ η w κ .LG ∨ Q.HasGapKind L γ η w κ .ZG)
    (hOsg : O.HasGapKind L γ η w κ .SG) (hne : (O.atoms ∩ Q.atoms).Nonempty)
    (hOQ : ¬ O.atoms ⊆ Q.atoms) (hQO : ¬ Q.atoms ⊆ O.atoms) :
    (∃ h, Q.shape = .vc h) ∧ (∃ h, O.shape = .vc h) ∧
    ((∃ c, O.atoms ∩ Q.atoms = {c} ∧ (c = O.upper ∨ c = O.lower)) ∨
      (O.atoms ∩ Q.atoms = {Q.upper, Q.lower} ∧
        ({O.upper, O.lower} : Finset V) = {Q.upper, Q.lower} ∧
        ∃ a b, M.IsVine .V O.atoms a b ∧ M.IsVine .V Q.atoms a b ∧ ({a, b} : Finset V) = {Q.upper, Q.lower})) := by
  obtain ⟨⟨RA⟩, hdA, hiA⟩ := object_overlap_premises O
  obtain ⟨⟨RB⟩, hdB, hiB⟩ := object_overlap_premises Q
  obtain ⟨hAblk, hBblk, hcl⟩ := Mole.molecule_overlap_classification M hM RA RB hne hOQ hQO hdA hdB hiA hiB
  have hOvc : ∃ h, O.shape = .vc h :=
    (object_shape_cases O).resolve_right (by
      rintro ⟨R, hR⟩
      have h1 := object_hyper_degIn O ⟨R, hR⟩ (Or.inl rfl)
      have h2 := (Mole.block_joint_degrees M hAblk).1
      omega)
  have hQvc : ∃ h, Q.shape = .vc h :=
    (object_shape_cases Q).resolve_right (by
      rintro ⟨R, hR⟩
      have h1 := object_hyper_degIn Q ⟨R, hR⟩ (Or.inl rfl)
      have h2 := (Mole.block_joint_degrees M hBblk).1
      omega)
  refine ⟨hQvc, hOvc, ?_⟩
  rcases hcl with ⟨h1, hint, hs1, hs2⟩ | ⟨hjne, hjnd, a, b, c, h2, h3, hab, hac, hbc, h5, _⟩ | ⟨hdisj, ⟨T⟩⟩
  · right
    have hPB := object_vc_block O hOvc
    have hQB := object_vc_block Q hQvc
    have hQj : (Q.upper = O.upper ∧ Q.lower = O.lower) ∨ (Q.upper = O.lower ∧ Q.lower = O.upper) := by
      have := Mole.finset_pair_eq_pair_iff.mp h1
      rcases this with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨e1.symm, e2.symm⟩
      · exact Or.inr ⟨e2.symm, e1.symm⟩
    have hQB' : M.IsBlock Q.atoms O.upper O.lower := by
      rcases hQj with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2]; exact hQB
      · rw [← e1, ← e2]; exact Mole.block_swap_joints _ hQB
    obtain ⟨z, hza, hzb, hzP, hzQ⟩ := diamond_shared_bond hM hPB hQB' hint
    have haQ : O.upper ∈ Q.atoms := by
      have : O.upper ∈ O.atoms ∩ Q.atoms := by rw [hint]; simp
      exact (mem_inter.mp this).2
    have hbQ : O.lower ∈ Q.atoms := by
      have : O.lower ∈ O.atoms ∩ Q.atoms := by rw [hint]; simp
      exact (mem_inter.mp this).2
    have haP : O.upper ∈ O.atoms := hPB.2.1
    have hbP : O.lower ∈ O.atoms := hPB.2.2.1
    obtain ⟨nP, hPch⟩ := object_vc_chain O hOvc
    obtain ⟨nQ, hQch⟩ := object_vc_chain Q hQvc
    have hQch' : SourceVine.Chain M Q.atoms O.upper O.lower nQ := by
      rcases hQj with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2]; exact hQch
      · rw [← e1, ← e2]; exact chain_swap hQch
    obtain ⟨XP, hXP⟩ := chain_single_of_joint_bond hM hPch.toVine hPB hza hzb hzP
    obtain ⟨XQ, hXQ⟩ := chain_single_of_joint_bond hM hQch'.toVine hQB' hza hzb hzQ
    have hXPV : XP = .V := by
      rcases vine_typeIV_of_joint_bond hXP hza hzb with h | h
      · exfalso; subst h
        apply hOQ
        rw [Vine.typeI_atoms hXP]
        intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · exact haQ
        · rw [mem_singleton.mp hv]; exact hbQ
      · exact h
    have hXQV : XQ = .V := by
      rcases vine_typeIV_of_joint_bond hXQ hza hzb with h | h
      · exfalso; subst h
        apply hQO
        rw [Vine.typeI_atoms hXQ]
        intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · exact haP
        · rw [mem_singleton.mp hv]; exact hbP
      · exact h
    subst hXPV hXQV
    refine ⟨by rw [hint, h1], h1, O.upper, O.lower, hXP, hXQ, ?_⟩
    rw [h1]
  · left
    have hc : c ∈ ({O.upper, O.lower} : Finset V) := by rw [h2]; simp
    refine ⟨c, h5, ?_⟩
    simpa using hc
  · exfalso
    have hp2C : T.p2 ∈ T.C1 ∩ T.C2 := (Finset.ext_iff.mp T.right_inter T.p2).mpr (by simp)
    have hp2Q : T.p2 ∈ Q.atoms :=
      (Finset.ext_iff.mp T.right_union T.p2).mpr (mem_union_left _ (mem_inter.mp hp2C).1)
    have hp2O : T.p2 ∈ ({O.upper, O.lower} : Finset V) :=
      (Finset.ext_iff.mp T.left_joints T.p2).mpr (by simp)
    have hnj : T.p2 ∉ ({Q.upper, Q.lower} : Finset V) := by
      intro h
      have := (Finset.ext_iff.mp T.right_joints T.p2).mp h
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h
      · exact T.block1.2.2.2.1 h.symm
      · exact T.block2.2.2.2.1 h
    have hp2nj : T.p2 ≠ Q.upper ∧ T.p2 ≠ Q.lower := ⟨fun h => hnj (by simp [h]), fun h => hnj (by simp [h])⟩
    have hOB := object_vc_block O hOvc
    have hQB := object_vc_block Q hQvc
    have hp2Oa : T.p2 ∈ O.atoms := by
      simp only [mem_insert, mem_singleton] at hp2O
      rcases hp2O with h | h
      · rw [h]; exact hOB.2.1
      · rw [h]; exact hOB.2.2.1
    have hκ1 : ∀ x, κ (M.mate x) = κ x := hκ.1
    have hcons : ∀ v ∈ M.atoms, M.deg v = 4 →
        ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L w κ x = 0 :=
      fun v hv hd => (hκ.2 v hv).trans (hc0 v hv hd)
    obtain ⟨rO, hrO, hkO⟩ := (object_vc_hasGapKind_iff O hOvc L γ η w κ .SG).mp hOsg
    have hgapc : ∃ r, M.IsBlockGap L w κ O.atoms T.p2 r ∧ Molecule.gapKind L γ η r = .SG := by
      simp only [mem_insert, mem_singleton] at hp2O
      rcases hp2O with h | h
      · exact ⟨rO, by rw [h]; exact hrO, hkO⟩
      · obtain ⟨r', hr', hk'⟩ := source_block_lower_SG_gap M hM hOB L γ η w κ hκ1 hcons hrO hkO
        exact ⟨r', by rw [h]; exact hr', hk'⟩
    obtain ⟨rc, hrc, hkc⟩ := hgapc
    obtain ⟨rQ, hrQ, hkQ⟩ : ∃ r, M.IsBlockGap L w κ Q.atoms Q.upper r ∧
        (Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG) := by
      rcases hQk with h | h
      · obtain ⟨r, hr, hk⟩ := (object_vc_hasGapKind_iff Q hQvc L γ η w κ .LG).mp h
        exact ⟨r, hr, Or.inl hk⟩
      · obtain ⟨r, hr, hk⟩ := (object_vc_hasGapKind_iff Q hQvc L γ η w κ .ZG).mp h
        exact ⟨r, hr, Or.inr hk⟩
    have hsub := sg_block_absorbed_by_container hM L γ η w c0 κ hκ hc0 O Q hOB hQB hp2Oa
      (by simpa using hp2O) hp2Q hp2nj hrc hkc hrQ hkQ hQO
    exact hOQ hsub

end WaveTurbulence.Subpro
