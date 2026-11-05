/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperVIICapRegion
public import WaveTurbulence.Foundations.Molecule.VineCapEndpointLabels
import Mathlib.Tactic

/-! # Primitive cap incidence data constructed from an actual type-VII hyper-block subset -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- The exact side labels, including both original far ports, prove
injectivity of every actual triangle and rung atom in the cap family. -/
theorem typeVII_side_family_distinct {M : Molecule V D} {S : Finset V} {a b : V}
    (R : VineRealization M .VII S a b) (kr kc : ℕ)
    (D : SideLadderData M (R.coreAtom (4 : Fin 11)).1 (R.coreAtom (5 : Fin 11)).1
      (R.coreAtom (6 : Fin 11)).1 (R.coreAtom (7 : Fin 11)).1 (R.coreAtom (8 : Fin 11)).1 kc)
    (hlabels : ∀ i,1 ≤ i → i ≤ kc → R.f (D.ladder.u i)=11+2*kr+(i-1) ∧
      R.f (D.ladder.v i)=11+2*kr+kc+(i-1)) :
    Function.Injective (capAtomFamily (R.coreAtom (4 : Fin 11)).1
      (R.coreAtom (5 : Fin 11)).1 (R.coreAtom (6 : Fin 11)).1 D.ladder.u D.ladder.v (kc+1)) := by
  have hf (i : CapIndex (kc+1)) :
      R.f (capAtomFamily (R.coreAtom (4 : Fin 11)).1 (R.coreAtom (5 : Fin 11)).1
        (R.coreAtom (6 : Fin 11)).1 D.ladder.u D.ladder.v (kc+1) i)=
      capEndpointLabel (11+2*kr) kc i := by
    cases i with
    | inl i =>
      fin_cases i
      · exact R.label_coreAtom (4 : Fin 11)
      · exact R.label_coreAtom (5 : Fin 11)
      · exact R.label_coreAtom (6 : Fin 11)
    | inr i =>
      cases i with
      | inl i =>
        simp only [capAtomFamily,capEndpointLabel]
        by_cases he : i.1=kc
        · rw [ite_eq_left he,he,D.end_upper]
          exact R.label_coreAtom (7 : Fin 11)
        · rw [ite_eq_right he]
          have hh := (hlabels (i.1+1) (by omega) (by omega)).1
          simpa only [Nat.add_sub_cancel] using hh
      | inr i =>
        simp only [capAtomFamily,capEndpointLabel]
        by_cases he : i.1=kc
        · rw [ite_eq_left he,he,D.end_lower]
          exact R.label_coreAtom (8 : Fin 11)
        · rw [ite_eq_right he]
          have hh := (hlabels (i.1+1) (by omega) (by omega)).2
          simpa only [Nat.add_sub_cancel] using hh
  intro i j he
  apply capEndpointLabel_injective (11+2*kr) kc (by omega)
  have hh := congrArg R.f he
  rwa [hf i,hf j] at hh

/-- TARGET subsetvc, source cap construction in type VII: every contained
actual hyper-block supplies primitive cap-prefix incidence data. No cap
realization, finite mask, prefix or vertex-distinctness premise is assumed. -/
theorem typeVII_hyper_cap_data (M : Molecule V D) (hM : M.IsMolecule)
    {S A : Finset V} {a b x y : V} (hV : M.IsVine .VII S a b)
    (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) :
    ∃ n r,Nonempty (CapPrefixData M A n r) := by
  obtain ⟨hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
  obtain ⟨kr,kc,kg,r,_hks,hr,D,_hmem,hlabels,hA⟩ :=
    typeVII_hyper_cap_region M hM R hS hAS hH
  exact ⟨kc,r,⟨{
    center := (R.coreAtom (4 : Fin 11)).1
    upper := (R.coreAtom (5 : Fin 11)).1
    lower := (R.coreAtom (6 : Fin 11)).1
    farUpper := (R.coreAtom (7 : Fin 11)).1
    farLower := (R.coreAtom (8 : Fin 11)).1
    side := D
    r_le := hr
    distinct := typeVII_side_family_distinct R kr kc D hlabels
    atoms_eq := hA }⟩⟩

end WaveTurbulence.Vine
