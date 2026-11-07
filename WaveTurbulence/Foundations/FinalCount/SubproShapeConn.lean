/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproShapeHost
public import WaveTurbulence.Foundations.FinalCount.AsmDesig
import Mathlib.Tactic

/-!
# S4-SHAPE: the host stays connected after the removal of the collected objects it contains

`host_removal_connected`: inside a host `S` (`HostOuter`: a DV or an LG/ZG vine-like object), remove simultaneously the removal
pieces of collected members of `C₂` lying in `S` (ordinary members as `ordPiece`, hyper members as arbitrary `AdjointPiece`s of their
atoms, i.e. any designation). The joints of `U` are remaining atoms and are connected in the remaining molecule of `S`; when
`ordPiece M U` is one of the pieces, the connection avoids the interior of `U`. This is the
universe's `subsetvc_simultaneous_removal_connected`, extended to the two-double-bond pieces (`removal_connected_dc`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.FinalCountG3 Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The removal piece of an ordinary collected object: its atoms, its joints, all its internal darts. -/
def ordPiece (M : Molecule V D) (O : Object M) : RemovalPiece V D :=
  ⟨O.atoms, O.upper, O.lower, univ.filter (M.InGroup O.atoms)⟩

theorem doubleChain_one_isSomeVine {M : Molecule V D} {S : Finset V} {a b : V} (h : DoubleChain M S a b 1) :
    Vine.IsSomeVine M S a b := by
  cases h with
  | single h => exact ⟨.I, h⟩
  | append h _ _ _ => cases h

theorem host_removal_connected {M : Molecule V D} (hM : M.IsMolecule) {L γ η : ℝ} {w : Mom d} {c0 : V → Mom d}
    {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c0 κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c0 v = 0)
    (C : CollData M) (Unsel : Set (Object M))
    (hd22 : ∀ O ∈ C.C2Of L γ η w κ Unsel, ∀ O' ∈ C.C2Of L γ η w κ Unsel, O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms)
    (hsh : ∀ O ∈ C.C2Of L γ η w κ Unsel, (∃ h, O.shape = .vc h) →
      DoubleChain M O.atoms O.upper O.lower 1 ∨ DoubleChain M O.atoms O.upper O.lower 2 ∨
        M.IsVine .V O.atoms O.upper O.lower)
    {U : Object M} (hU : U ∈ C.C2Of L γ η w κ Unsel) (hUvc : ∃ h, U.shape = .vc h)
    {S : Finset V} (hUS : U.atoms ⊆ S) (hS : HostOuter M L γ η w κ S)
    (ps : List (RemovalPiece V D)) (qs : List (AdjointPiece M))
    (hps : ∀ P ∈ ps, ∃ O ∈ C.C2Of L γ η w κ Unsel, (∃ h, O.shape = .vc h) ∧ O.atoms ⊆ S ∧ P = ordPiece M O)
    (hqs : ∀ A ∈ qs, ∃ O ∈ C.C2Of L γ η w κ Unsel, (∃ R, O.shape = .hyper R) ∧ O.atoms ⊆ S ∧ A.atoms = O.atoms)
    (hdis : ∀ P ∈ ps, ∀ Q ∈ ps, P ≠ Q → Disjoint P.atoms Q.atoms)
    (hQdis : ∀ P ∈ qs, ∀ Q ∈ qs, P ≠ Q → Disjoint P.atoms Q.atoms) :
    U.upper ∈ remainingAtoms S (ps ++ qs.map AdjointPiece.toRemoval) ∧
      U.lower ∈ remainingAtoms S (ps ++ qs.map AdjointPiece.toRemoval) ∧
      (removeBlocks M S (ps ++ qs.map AdjointPiece.toRemoval)).SameComponent U.upper U.lower := by
  classical
  unfold HostOuter at hS
  obtain ⟨a, b, houter⟩ := hS
  -- an ordinary member and a hyper member of `C₂` have disjoint atom sets
  have hcross : ∀ P ∈ ps, ∀ Q ∈ qs, Disjoint P.atoms Q.atoms := by
    intro P hP Q hQ
    obtain ⟨O, hO, hOvc, -, rfl⟩ := hps P hP
    obtain ⟨O', hO', hO'h, -, hQa⟩ := hqs Q hQ
    show Disjoint O.atoms Q.atoms
    rw [hQa]
    rcases hd22 O hO O' hO' with he | hd
    · exfalso
      have hj := FinalCountAsm.object_joints_eq O O' he
      have h1 := object_hyper_degIn O' hO'h (Or.inl rfl)
      have h2 := (Mole.block_joint_degrees M (object_vc_block O hOvc))
      have hu : O'.upper ∈ ({O.upper, O.lower} : Finset V) := by rw [hj]; simp
      simp only [mem_insert, mem_singleton] at hu
      rw [← he] at h1
      rcases hu with hu | hu
      · rw [hu] at h1; omega
      · rw [hu] at h1; omega
    · exact hd
  -- the joints of `U` survive
  have hjoint : ∀ v, (v = U.upper ∨ v = U.lower) →
      v ∈ remainingAtoms S (ps ++ qs.map AdjointPiece.toRemoval) := by
    intro v hv
    unfold remainingAtoms
    rw [mem_filter]
    refine ⟨hUS (object_mem_of_joint U hv), ?_⟩
    intro P hP hint
    unfold RemovalPiece.interior at hint
    have hvP : v ∈ P.atoms := (mem_sdiff.mp hint).1
    rcases List.mem_append.mp hP with hP | hP
    · obtain ⟨O, hO, hOvc, -, rfl⟩ := hps P hP
      rcases hd22 U hU O hO with he | hd
      · have hj := FinalCountAsm.object_joints_eq U O he
        apply (mem_sdiff.mp hint).2
        have : v ∈ ({U.upper, U.lower} : Finset V) := by simpa using hv
        rw [hj] at this
        exact this
      · exact Finset.disjoint_left.mp hd (object_mem_of_joint U hv) hvP
    · obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hP
      obtain ⟨O, hO, hOh, -, hAa⟩ := hqs A hA
      have hvO : v ∈ O.atoms := by rw [← hAa]; exact hvP
      rcases hd22 U hU O hO with he | hd
      · exfalso
        have hj := FinalCountAsm.object_joints_eq U O he
        have h1 := object_hyper_degIn O hOh (Or.inl rfl)
        have h2 := Mole.block_joint_degrees M (object_vc_block U hUvc)
        have hu : O.upper ∈ ({U.upper, U.lower} : Finset V) := by rw [hj]; simp
        simp only [mem_insert, mem_singleton] at hu
        rw [← he] at h1
        rcases hu with hu | hu
        · rw [hu] at h1; omega
        · rw [hu] at h1; omega
      · exact Finset.disjoint_left.mp hd (object_mem_of_joint U hv) hvO
  refine ⟨hjoint _ (Or.inl rfl), hjoint _ (Or.inr rfl), ?_⟩
  refine removal_connected_dc M hM ps qs ?_ ?_ ?_ hdis ?_ hQdis hcross L γ η w c0 κ hκ hc0 ?_ houter
    U.upper (hjoint _ (Or.inl rfl)) U.lower (hjoint _ (Or.inr rfl))
  · intro P hP
    obtain ⟨O, hO, hOvc, -, rfl⟩ := hps P hP
    rcases hsh O hO hOvc with h | h | h
    · exact Or.inl (doubleChain_one_isSomeVine h)
    · exact Or.inr ⟨object_vc_block O hOvc, h⟩
    · exact Or.inl ⟨.V, h⟩
  · intro P hP
    obtain ⟨O, -, -, hOS, rfl⟩ := hps P hP
    exact hOS
  · intro P hP
    obtain ⟨O, -, -, -, rfl⟩ := hps P hP
    rfl
  · intro Q hQ
    obtain ⟨O, -, -, hOS, hQa⟩ := hqs Q hQ
    rw [hQa]; exact hOS
  · intro P hP
    obtain ⟨O, hO, hOvc, -, rfl⟩ := hps P hP
    obtain ⟨r, hr, hk⟩ := (object_vc_hasGapKind_iff O hOvc L γ η w κ .SG).mp hO.1.1.1
    exact ⟨r, hr, hk⟩

end WaveTurbulence.Subpro
