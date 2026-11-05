/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.EndRungData
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween

/-! # Exact bond multiplicities at the lower type-II joint

TARGET molecpl (2): complete incidence rows determine the doubled rung
bond. The distinct rail neighbors exclude a hidden third parallel bond.
-/

public section
namespace WaveTurbulence.Molecpl
open Finset Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A complete four-dart row with two distinct remaining neighbors has exactly two bonds to d. -/
theorem fourIncidences_double_count {M : Molecule V D} (hM : M.IsMolecule)
    {c d a b : V} (R : FourIncidences M c ![d,d,a,b]) (hcd : c ≠ d)
    (had : a ≠ d) (hbd : b ≠ d) : M.bondsBetween c d = 2 := by
  rw [Mole.bondsBetween_eq_card_darts M hcd, ← Vine.fourIncidences_image M hM R]
  rw [Finset.filter_image]
  have he : (univ.filter (fun i : Fin 4 => M.atom (M.mate (R.dart i)) = d)) = {0,1} := by
    ext i
    fin_cases i <;> simp [R.neighbor_eq,had,hbd]
  rw [he]
  have hne : R.dart 0 ≠ R.dart 1 := R.injective.ne (by decide)
  simp [hne]

/-- The two actual interior atoms next to the joint are joined by exactly two bonds. -/
theorem EndRungData.double_count {M : Molecule V D} (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (R : EndRungData M S a b) :
    M.bondsBetween R.left R.right = 2 :=
  fourIncidences_double_count hM R.left_row R.distinct R.right_ne_lower.symm R.nextLeft_ne_right

end WaveTurbulence.Molecpl
