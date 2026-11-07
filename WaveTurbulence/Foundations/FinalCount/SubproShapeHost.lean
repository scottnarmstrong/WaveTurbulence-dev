/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproShapeStraddle
public import WaveTurbulence.Foundations.FinalCount.SubproDisjFinal
import Mathlib.Tactic

/-!
# S4-SHAPE: hosts with no straddling collected object

`Harmless M S O`: the collected object `O` removes no atom of `S` and kills no dart joining two distinct atoms of `S`
(so its removal does not change the graph induced on `S`). `Clean M S O`: `O` lies inside `S` or is harmless for `S`.
`good_host_of_object_host`: a host `Q` of `U ∈ C₂` (LG/ZG object) either has only clean members of `C₂`, or the one-joint /
two-joint overlap classification yields a DV `S' = O ∪ Q` (with `O ∈ C₂`) all of whose `C₂`-neighbours are clean.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.FinalCountG3 Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The removal of `O` neither removes an atom of `S` nor kills a non-loop dart between atoms of `S`. -/
def Harmless (M : Molecule V D) (S : Finset V) (O : Object M) : Prop :=
  Disjoint (O.atoms \ {O.upper, O.lower}) S ∧
    ∀ y, M.atom y ∈ S → M.atom (M.mate y) ∈ S → M.InGroup O.atoms y → M.atom y = M.atom (M.mate y)

/-- `O` lies in `S`, or does not interfere with `S`. -/
def Clean (M : Molecule V D) (S : Finset V) (O : Object M) : Prop := O.atoms ⊆ S ∨ Harmless M S O

theorem harmless_of_disjoint {M : Molecule V D} {S : Finset V} {O : Object M} (h : Disjoint O.atoms S) :
    Harmless M S O := by
  refine ⟨Finset.disjoint_of_subset_left sdiff_subset h, ?_⟩
  intro y hy _ hg
  exact (Finset.disjoint_left.mp h hg.1 hy).elim

theorem harmless_of_inter_singleton {M : Molecule V D} {S : Finset V} {O : Object M} {c : V}
    (h : O.atoms ∩ S = {c}) (hj : c = O.upper ∨ c = O.lower) : Harmless M S O := by
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hv hvS
    have : v ∈ O.atoms ∩ S := mem_inter.mpr ⟨(mem_sdiff.mp hv).1, hvS⟩
    rw [h] at this
    have hvc := mem_singleton.mp this
    apply (mem_sdiff.mp hv).2
    rw [hvc]
    rcases hj with hj | hj <;> simp [hj]
  · intro y h1 h2 hg
    have e1 : M.atom y ∈ O.atoms ∩ S := mem_inter.mpr ⟨hg.1, h1⟩
    have e2 : M.atom (M.mate y) ∈ O.atoms ∩ S := mem_inter.mpr ⟨hg.2, h2⟩
    rw [h] at e1 e2
    rw [mem_singleton.mp e1, mem_singleton.mp e2]

/-- The universe's `houter` clause for the atom set `S`: a DV, or a vine-like object with an LG or ZG gap. -/
def HostOuter (M : Molecule V D) (L γ η : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (S : Finset V) : Prop :=
  ∃ a b : V, Vine.IsDV M S a b ∨ ∃ C : Vine.VineLikeObject M S a b, ∃ r : Mom d, C.IsGap L w κ r ∧
    (Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG)

theorem hostOuter_of_object {M : Molecule V D} {L γ η : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} (Q : Object M)
    (hQk : Q.HasGapKind L γ η w κ .LG ∨ Q.HasGapKind L γ η w κ .ZG) : HostOuter M L γ η w κ Q.atoms := by
  refine ⟨Q.upper, Q.lower, Or.inr ⟨Q.shape.toVine, ?_⟩⟩
  rcases hQk with ⟨r, hr, hk⟩ | ⟨r, hr, hk⟩
  · exact ⟨r, (Q.shape.toVine_isGap L w κ r).mpr hr, Or.inl hk⟩
  · exact ⟨r, (Q.shape.toVine_isGap L w κ r).mpr hr, Or.inr hk⟩

/-- **Host selection at an object host.** `U ∈ C₂` lies in an LG/ZG object `Q` disjoint from `C₁` and the hinges. Either `Q`, or the
DV `O ∪ Q` formed with a member `O` of `C₂` sharing both joints of `Q`, is a host that no member of `C₂` straddles. -/
theorem good_host_of_object_host {M : Molecule V D} (hM : M.IsMolecule) {L γ η : ℝ} {w : Mom d} {c0 : V → Mom d}
    {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c0 κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c0 v = 0)
    (C : CollData M) (Unsel : Set (Object M))
    (hd22 : ∀ O ∈ C.C2Of L γ η w κ Unsel, ∀ O' ∈ C.C2Of L γ η w κ Unsel, O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms)
    {U : Object M} (hU : U ∈ C.C2Of L γ η w κ Unsel) {Q : Object M}
    (hQk : Q.HasGapKind L γ η w κ .LG ∨ Q.HasGapKind L γ η w κ .ZG) (hUQ : U.atoms ⊆ Q.atoms)
    (hQh : Disjoint Q.atoms C.hinges) (hQC : ∀ i, Disjoint Q.atoms (C.collection i).atoms) :
    ∃ S : Finset V, U.atoms ⊆ S ∧ HostOuter M L γ η w κ S ∧ Disjoint S C.hinges ∧
      (∀ i, Disjoint S (C.collection i).atoms) ∧ ∀ O ∈ C.C2Of L γ η w κ Unsel, Clean M S O := by
  classical
  by_cases hbad : ∃ O ∈ C.C2Of L γ η w κ Unsel, ¬ O.atoms ⊆ Q.atoms ∧ ¬ Harmless M Q.atoms O
  swap
  · push Not at hbad
    exact ⟨Q.atoms, hUQ, hostOuter_of_object Q hQk, hQh, hQC, fun O hO => by
      by_cases h : O.atoms ⊆ Q.atoms
      · exact Or.inl h
      · exact Or.inr (hbad O hO h)⟩
  obtain ⟨O, hO, hnsub, hnh⟩ := hbad
  have hdis : ¬ Disjoint O.atoms Q.atoms := fun h => hnh (harmless_of_disjoint h)
  have hne : (O.atoms ∩ Q.atoms).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hdis
  have hOsg : O.HasGapKind L γ η w κ .SG := hO.1.1.1
  have hQO : ¬ Q.atoms ⊆ O.atoms := by
    intro h
    rcases hd22 U hU O hO with he | hd
    · exact hnsub (he ▸ hUQ)
    · exact Finset.disjoint_left.mp hd (object_mem_of_joint U (Or.inl rfl)) (h (hUQ (object_mem_of_joint U (Or.inl rfl))))
  obtain ⟨hQvc, hOvc, hcase⟩ := straddle_object_host hM hκ hc0 Q O hQk hOsg hne hnsub hQO
  rcases hcase with ⟨c, hc, hcj⟩ | ⟨hint, hjeq, a, b, hVO, hVQ, hab⟩
  · exact (hnh (harmless_of_inter_singleton hc hcj)).elim
  · have hOdis := c2Of_disjoint_c1_hinges C hO
    have hDV : Vine.IsDV M (O.atoms ∪ Q.atoms) a b :=
      ⟨O.atoms, Q.atoms, hVO, hVQ, by rw [hint, hab], rfl⟩
    refine ⟨O.atoms ∪ Q.atoms, hUQ.trans subset_union_right, ⟨a, b, Or.inl hDV⟩, ?_, ?_, ?_⟩
    · exact Finset.disjoint_union_left.mpr ⟨hOdis.2, hQh⟩
    · exact fun i => Finset.disjoint_union_left.mpr ⟨hOdis.1 i, hQC i⟩
    · intro O' hO'
      by_cases hsub : O'.atoms ⊆ O.atoms ∪ Q.atoms
      · exact Or.inl hsub
      right
      by_cases hd' : Disjoint O'.atoms (O.atoms ∪ Q.atoms)
      · exact harmless_of_disjoint hd'
      exfalso
      have hd1 : Disjoint O'.atoms O.atoms := by
        rcases hd22 O' hO' O hO with he | hd
        · exact (hsub (he ▸ subset_union_left)).elim
        · exact hd
      have hne' : (O'.atoms ∩ Q.atoms).Nonempty := by
        obtain ⟨v, hv⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hd'
        rcases mem_union.mp (mem_inter.mp hv).2 with h | h
        · exact (Finset.disjoint_left.mp hd1 (mem_inter.mp hv).1 h).elim
        · exact ⟨v, mem_inter.mpr ⟨(mem_inter.mp hv).1, h⟩⟩
      have hnot : ¬ O'.atoms ⊆ Q.atoms := fun h => hsub (h.trans subset_union_right)
      obtain ⟨⟨RA⟩, _, _⟩ := object_overlap_premises O'
      obtain ⟨⟨RB⟩, _, _⟩ := object_overlap_premises Q
      obtain ⟨z, hz, hzj⟩ := Mole.overlap_contains_joint M hM RA RB hne' hnot
      have hzO : z ∈ O.atoms := by
        have : z ∈ O.atoms ∩ Q.atoms := by
          rw [hint]; rcases hzj with h | h <;> simp [h]
        exact (mem_inter.mp this).1
      exact Finset.disjoint_left.mp hd1 (mem_inter.mp hz).1 hzO

/-- **A DV with a collected vine is a host that no member of `C₂` straddles.** `A ∪ B` is a double vine (two type-V vines with the same
joints `a, b`) one of whose vines is the atom set of a member `O` of `C₂`. Every member of `C₂` lies in `A ∪ B` or does not meet it
in a way that matters. -/
theorem clean_of_dv_collected {M : Molecule V D} (hM : M.IsMolecule) {L γ η : ℝ} {w : Mom d}
    {κ : D → (Fin d → ℤ)} (C : CollData M) (Unsel : Set (Object M))
    (hd22 : ∀ O ∈ C.C2Of L γ η w κ Unsel, ∀ O' ∈ C.C2Of L γ η w κ Unsel, O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms)
    {A B : Finset V} {a b : V} (hB : M.IsVine .V B a b) (_hA : M.IsVine .V A a b) (hAB : A ∩ B = {a, b})
    {O : Object M} (hO : O ∈ C.C2Of L γ η w κ Unsel) (hOA : O.atoms = A) :
    ∀ O' ∈ C.C2Of L γ η w κ Unsel, Clean M (A ∪ B) O' := by
  classical
  intro O' hO'
  by_cases hsub : O'.atoms ⊆ A ∪ B
  · exact Or.inl hsub
  right
  by_cases hd' : Disjoint O'.atoms (A ∪ B)
  · exact harmless_of_disjoint hd'
  exfalso
  have hd1 : Disjoint O'.atoms A := by
    rcases hd22 O' hO' O hO with he | hd
    · exact (hsub (by rw [he, hOA]; exact subset_union_left)).elim
    · rwa [hOA] at hd
  have hne' : (O'.atoms ∩ B).Nonempty := by
    obtain ⟨v, hv⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hd'
    rcases mem_union.mp (mem_inter.mp hv).2 with h | h
    · exact (Finset.disjoint_left.mp hd1 (mem_inter.mp hv).1 h).elim
    · exact ⟨v, mem_inter.mpr ⟨(mem_inter.mp hv).1, h⟩⟩
  have hnot : ¬ O'.atoms ⊆ B := fun h => hsub (h.trans subset_union_right)
  obtain ⟨⟨RA⟩, _, _⟩ := object_overlap_premises O'
  obtain ⟨⟨RB⟩, _, _⟩ := object_overlap_premises (Object.ofVine hB)
  obtain ⟨z, hz, hzj⟩ := Mole.overlap_contains_joint M hM RA RB hne' hnot
  have hzA : z ∈ A := by
    have : z ∈ A ∩ B := by
      rw [hAB]; rcases hzj with h | h <;> simp [Object.ofVine, h]
    exact (mem_inter.mp this).1
  exact Finset.disjoint_left.mp hd1 (mem_inter.mp hz).1 hzA

/-- Reduction of a double-vine host witness: `U` also has a DV host with a vine that is the atom set of a member of `C₂`, or an LG/ZG
object host, disjoint from `C₁` and the hinges. -/
def DVWitnessReduction {M : Molecule V D} (L γ η : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (C : CollData M)
    (Unsel : Set (Object M)) (U : Object M) : Prop :=
  ∀ (A B : Finset V) (a b : V), M.IsVine .V A a b → M.IsVine .V B a b → A ∩ B = {a, b} → U.atoms ⊆ A ∪ B →
    Disjoint (A ∪ B) C.hinges → (∀ i, Disjoint (A ∪ B) (C.collection i).atoms) →
    (∃ (A' B' : Finset V) (a' b' : V), M.IsVine .V A' a' b' ∧ M.IsVine .V B' a' b' ∧ A' ∩ B' = {a', b'} ∧
      U.atoms ⊆ A' ∪ B' ∧ Disjoint (A' ∪ B') C.hinges ∧ (∀ i, Disjoint (A' ∪ B') (C.collection i).atoms) ∧
      ∃ O ∈ C.C2Of L γ η w κ Unsel, O.atoms = A' ∨ O.atoms = B') ∨
      ∃ Q : Object M, (Q.HasGapKind L γ η w κ .LG ∨ Q.HasGapKind L γ η w κ .ZG) ∧ U.atoms ⊆ Q.atoms ∧
        Disjoint Q.atoms C.hinges ∧ ∀ i, Disjoint Q.atoms (C.collection i).atoms

/-- **A good host exists** for `U ∈ C₂`: an atom set `S ⊇ U` that is a DV or an LG/ZG vine-like object, disjoint from `C₁` and the
hinges, and such that every member of `C₂` lies in `S` or is harmless for it (removes no atom of `S` and kills no non-loop dart
between atoms of `S`). Unconditional when G3's host witness of `U` is an object; for a DV witness it uses the named reduction
`DVWitnessReduction`. -/
theorem exists_good_host {M : Molecule V D} (hM : M.IsMolecule) {L γ η : ℝ} {w : Mom d} {c0 : V → Mom d}
    {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c0 κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c0 v = 0)
    (C : CollData M) (Unsel : Set (Object M))
    (hd22 : ∀ O ∈ C.C2Of L γ η w κ Unsel, ∀ O' ∈ C.C2Of L γ η w κ Unsel, O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms)
    {U : Object M} (hU : U ∈ C.C2Of L γ η w κ Unsel) (hDV : DVWitnessReduction L γ η w κ C Unsel U) :
    ∃ S : Finset V, U.atoms ⊆ S ∧ HostOuter M L γ η w κ S ∧ Disjoint S C.hinges ∧
      (∀ i, Disjoint S (C.collection i).atoms) ∧ ∀ O ∈ C.C2Of L γ η w κ Unsel, Clean M S O := by
  classical
  have hhost : C.Host L γ η w κ U := hU.1.1.2.2.2
  rcases hhost with ⟨S, a, b, hSDV, hUS, hSh, hSC⟩ | ⟨Q, hUQ, hQk, hQh, hQC⟩
  · obtain ⟨A, B, hA, hB, hAB, rfl⟩ := hSDV
    rcases hDV A B a b hA hB hAB hUS hSh hSC with
      ⟨A', B', a', b', hA', hB', hAB', hUS', hSh', hSC', O, hO, hOA | hOB⟩ | ⟨Q, hQk, hUQ, hQh, hQC⟩
    · refine ⟨A' ∪ B', hUS', ⟨a', b', Or.inl ⟨A', B', hA', hB', hAB', rfl⟩⟩, hSh', hSC', ?_⟩
      exact clean_of_dv_collected hM C Unsel hd22 hB' hA' hAB' hO hOA
    · refine ⟨A' ∪ B', hUS', ⟨a', b', Or.inl ⟨A', B', hA', hB', hAB', rfl⟩⟩, hSh', hSC', ?_⟩
      have := clean_of_dv_collected hM C Unsel hd22 hA' hB' (by rw [Finset.inter_comm]; exact hAB') hO hOB
      rwa [Finset.union_comm] at this
    · exact good_host_of_object_host hM hκ hc0 C Unsel hd22 hU hQk hUQ hQh hQC
  · exact good_host_of_object_host hM hκ hc0 C Unsel hd22 hU hQk hUQ hQh hQC

end WaveTurbulence.Subpro
