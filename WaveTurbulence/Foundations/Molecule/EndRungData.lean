/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.RungRows
public import WaveTurbulence.Foundations.Molecule.CurrentBlockBridge

/-!
# Actual incidence data adjacent to a type-II vine joint

TARGET molecpl (2). The fields retain actual darts in the current
molecule, not an abstract graph drawing. Four-incidence rows encode the
double bond and both rail bonds, including the one-rung Q-block.
-/

public section
namespace WaveTurbulence.Molecpl
open Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The actual two interior rung atoms adjoining a specified lower joint. -/
structure EndRungData (M : Molecule V D) (S : Finset V) (a b : V) where
  left : V
  right : V
  nextLeft : V
  nextRight : V
  left_mem : left ∈ S
  right_mem : right ∈ S
  nextLeft_mem : nextLeft ∈ S
  nextRight_mem : nextRight ∈ S
  distinct : left ≠ right
  left_ne_upper : left ≠ a
  left_ne_lower : left ≠ b
  right_ne_upper : right ≠ a
  right_ne_lower : right ≠ b
  nextLeft_ne_left : nextLeft ≠ left
  nextLeft_ne_right : nextLeft ≠ right
  nextRight_ne_left : nextRight ≠ left
  nextRight_ne_right : nextRight ≠ right
  left_row : FourIncidences M left ![right,right,b,nextLeft]
  right_row : FourIncidences M right ![left,left,b,nextRight]

/-- Full internal rung rows cannot be either degree-two joint. -/
theorem fourIncidences_ne_joints {M : Molecule V D} (hM : M.IsMolecule)
    {S : Finset V} {a b c : V} (hB : M.IsBlock S a b) {vs : Fin 4 → V}
    (R : FourIncidences M c vs) (hc : c ∈ S) (hv : ∀ i, vs i ∈ S) : c ≠ a ∧ c ≠ b := by
  have hd := fourIncidences_internal_degree hM R hc hv
  have hj := Mole.block_joint_degrees M hB
  constructor
  · intro he
    rw [he,hj.1] at hd
    omega
  · intro he
    rw [he,hj.2] at hd
    omega

/-- The next rail nodes at the first rung are distinct from both rung atoms. -/
theorem first_next_disjoint {M : Molecule V D} (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) {n : ℕ} (hn : 1 ≤ n)
    (Q : FullRungSequence M n) (hmem : ∀ i, Q.u i ∈ S ∧ Q.v i ∈ S)
    (hu : Q.u (n+1) = a) (hv : Q.v (n+1) = a) :
    Q.u 2 ≠ Q.u 1 ∧ Q.u 2 ≠ Q.v 1 ∧ Q.v 2 ≠ Q.u 1 ∧ Q.v 2 ≠ Q.v 1 := by
  by_cases htwo : 2 ≤ n
  · exact fullRungSequence_pair_disjoint Q (by omega) htwo le_rfl hn (by omega)
  have he : n=1 := by omega
  subst n
  have ru := Q.upper 1 le_rfl le_rfl
  have rv := Q.lower 1 le_rfl le_rfl
  have hru : ∀ i : Fin 4, (![Q.v 1,Q.v 1,Q.u (1-1),Q.u (1+1)] : Fin 4 → V) i ∈ S := by
    intro i; fin_cases i
    · exact (hmem 1).2
    · exact (hmem 1).2
    · exact (hmem 0).1
    · exact (hmem 2).1
  have hrv : ∀ i : Fin 4, (![Q.u 1,Q.u 1,Q.v (1-1),Q.v (1+1)] : Fin 4 → V) i ∈ S := by
    intro i; fin_cases i
    · exact (hmem 1).1
    · exact (hmem 1).1
    · exact (hmem 0).2
    · exact (hmem 2).2
  have hnu := (fourIncidences_ne_joints hM hB ru (hmem 1).1 hru).1
  have hnv := (fourIncidences_ne_joints hM hB rv (hmem 1).2 hrv).1
  rw [hu,hv]
  exact ⟨hnu.symm,hnv.symm,hnu.symm,hnv.symm⟩

/-- The next rail nodes at the last rung are distinct from both rung atoms. -/
theorem last_next_disjoint {M : Molecule V D} (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) {n : ℕ} (hn : 1 ≤ n)
    (Q : FullRungSequence M n) (hmem : ∀ i, Q.u i ∈ S ∧ Q.v i ∈ S)
    (hu : Q.u 0 = a) (hv : Q.v 0 = a) :
    Q.u (n-1) ≠ Q.u n ∧ Q.u (n-1) ≠ Q.v n ∧ Q.v (n-1) ≠ Q.u n ∧ Q.v (n-1) ≠ Q.v n := by
  by_cases htwo : 2 ≤ n
  · exact fullRungSequence_pair_disjoint Q (by omega) (by omega) hn le_rfl (by omega)
  have he : n=1 := by omega
  subst n
  have ru := Q.upper 1 le_rfl le_rfl
  have rv := Q.lower 1 le_rfl le_rfl
  have hru : ∀ i : Fin 4, (![Q.v 1,Q.v 1,Q.u (1-1),Q.u (1+1)] : Fin 4 → V) i ∈ S := by
    intro i; fin_cases i
    · exact (hmem 1).2
    · exact (hmem 1).2
    · exact (hmem 0).1
    · exact (hmem 2).1
  have hrv : ∀ i : Fin 4, (![Q.u 1,Q.u 1,Q.v (1-1),Q.v (1+1)] : Fin 4 → V) i ∈ S := by
    intro i; fin_cases i
    · exact (hmem 1).1
    · exact (hmem 1).1
    · exact (hmem 0).2
    · exact (hmem 2).2
  have hnu := (fourIncidences_ne_joints hM hB ru (hmem 1).1 hru).1
  have hnv := (fourIncidences_ne_joints hM hB rv (hmem 1).2 hrv).1
  change Q.u 0 ≠ Q.u 1 ∧ Q.u 0 ≠ Q.v 1 ∧ Q.v 0 ≠ Q.u 1 ∧ Q.v 0 ≠ Q.v 1
  rw [hu,hv]
  exact ⟨hnu.symm,hnv.symm,hnu.symm,hnv.symm⟩

/-- The first rung supplies actual source end-rung data, without a two-rung restriction. -/
theorem endRung_at_first {M : Molecule V D} (hM : M.IsMolecule) {S : Finset V} {a b : V}
    (hB : M.IsBlock S a b) {n : ℕ} (hn : 1 ≤ n) (Q : FullRungSequence M n)
    (hmem : ∀ i, Q.u i ∈ S ∧ Q.v i ∈ S) (hu : Q.u 0 = b) (hv : Q.v 0 = b)
    (hua : Q.u (n+1) = a) (hva : Q.v (n+1) = a) :
    Nonempty (EndRungData M S a b) := by
  have ru : FourIncidences M (Q.u 1) ![Q.v 1,Q.v 1,b,Q.u 2] := by
    simpa only [Nat.sub_self,hu] using Q.upper 1 le_rfl hn
  have rv : FourIncidences M (Q.v 1) ![Q.u 1,Q.u 1,b,Q.v 2] := by
    simpa only [Nat.sub_self,hv] using Q.lower 1 le_rfl hn
  have hru : ∀ i : Fin 4, (![Q.v 1,Q.v 1,b,Q.u 2] : Fin 4 → V) i ∈ S := by
    intro i
    fin_cases i
    · exact (hmem 1).2
    · exact (hmem 1).2
    · exact hB.2.2.1
    · exact (hmem 2).1
  have hrv : ∀ i : Fin 4, (![Q.u 1,Q.u 1,b,Q.v 2] : Fin 4 → V) i ∈ S := by
    intro i
    fin_cases i
    · exact (hmem 1).1
    · exact (hmem 1).1
    · exact hB.2.2.1
    · exact (hmem 2).2
  have hnu := fourIncidences_ne_joints hM hB ru (hmem 1).1 hru
  have hnv := fourIncidences_ne_joints hM hB rv (hmem 1).2 hrv
  obtain ⟨h1,h2,h3,h4⟩ := first_next_disjoint hM hB hn Q hmem hua hva
  exact ⟨⟨Q.u 1,Q.v 1,Q.u 2,Q.v 2,(hmem 1).1,(hmem 1).2,(hmem 2).1,(hmem 2).2,
    fullRungSequence_rung_ne Q le_rfl hn,hnu.1,hnu.2,hnv.1,hnv.2,h1,h2,h3,h4,ru,rv⟩⟩

/-- The final rung also supplies the same source data, by reversing the two rail slots. -/
theorem endRung_at_last {M : Molecule V D} (hM : M.IsMolecule) {S : Finset V} {a b : V}
    (hB : M.IsBlock S a b) {n : ℕ} (hn : 1 ≤ n) (Q : FullRungSequence M n)
    (hmem : ∀ i, Q.u i ∈ S ∧ Q.v i ∈ S) (hu : Q.u (n+1) = b) (hv : Q.v (n+1) = b)
    (hua : Q.u 0 = a) (hva : Q.v 0 = a) :
    Nonempty (EndRungData M S a b) := by
  have ru : FourIncidences M (Q.u n) ![Q.v n,Q.v n,b,Q.u (n-1)] := by
    have hh := FourIncidences.swapRails (Q.upper n hn le_rfl)
    simpa only [hu] using hh
  have rv : FourIncidences M (Q.v n) ![Q.u n,Q.u n,b,Q.v (n-1)] := by
    have hh := FourIncidences.swapRails (Q.lower n hn le_rfl)
    simpa only [hv] using hh
  have hru : ∀ i : Fin 4, (![Q.v n,Q.v n,b,Q.u (n-1)] : Fin 4 → V) i ∈ S := by
    intro i
    fin_cases i
    · exact (hmem n).2
    · exact (hmem n).2
    · exact hB.2.2.1
    · exact (hmem (n-1)).1
  have hrv : ∀ i : Fin 4, (![Q.u n,Q.u n,b,Q.v (n-1)] : Fin 4 → V) i ∈ S := by
    intro i
    fin_cases i
    · exact (hmem n).1
    · exact (hmem n).1
    · exact hB.2.2.1
    · exact (hmem (n-1)).2
  have hnu := fourIncidences_ne_joints hM hB ru (hmem n).1 hru
  have hnv := fourIncidences_ne_joints hM hB rv (hmem n).2 hrv
  obtain ⟨h1,h2,h3,h4⟩ := last_next_disjoint hM hB hn Q hmem hua hva
  exact ⟨⟨Q.u n,Q.v n,Q.u (n-1),Q.v (n-1),(hmem n).1,(hmem n).2,
    (hmem (n-1)).1,(hmem (n-1)).2,fullRungSequence_rung_ne Q hn le_rfl,
    hnu.1,hnu.2,hnv.1,hnv.2,h1,h2,h3,h4,ru,rv⟩⟩

end WaveTurbulence.Molecpl
