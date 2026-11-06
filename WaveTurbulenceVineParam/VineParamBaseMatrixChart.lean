/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamBaseBundlePartition
public import WaveTurbulenceVineParam.VineParamEnergyCertificates
public import WaveTurbulenceVineParam.VineParamConservationFiber
import Mathlib.Tactic

/-! # Integral matrix charts tied to the pinned base-template conservation rows

This is certificate data, not an assumed parametrization theorem. Concrete
producers supply it for every normalized orientation. The free coordinates
are followed by the joint gap and all interior divergences.
-/

public section
namespace WaveTurbulence.Vine.Param

theorem base_gap_lt (X : VineType) :
    X.template.n-1<X.template.bonds.length := by cases X <;> decide

theorem base_free_lt (X : VineType) (i : Fin (X.template.n-1)) :
    i.1<X.template.bonds.length := lt_trans i.2 (base_gap_lt X)

theorem base_internal_lt (X : VineType) (v : Fin (X.template.n-2)) :
    X.template.n+v.1<X.template.bonds.length := by
  cases X <;> dsimp [VineType.template] at v ⊢ <;> omega

theorem base_vertex_lt (X : VineType) (v : Fin (X.template.n-2)) :
    v.1+2<X.template.n := by
  have hn : 2 ≤ X.template.n := by cases X <;> decide
  have := v.2
  omega

theorem base_atom_pos (X : VineType) : 0<X.template.n := by cases X <;> decide
theorem base_bond_pos (X : VineType) : 0<X.template.bonds.length := by cases X <;> decide

/-- Full integer encoder/inverse, with their exact directed source rows.
The phase identities are checked separately on the reduced decoder. -/
structure BaseMatrixChart (X : VineType) (p : Fin (baseProfileCount X)) where
  ends : Fin X.template.bonds.length → Fin X.template.n × Fin X.template.n
  ends_profile : List.ofFn (fun i => ((ends i).1.1,(ends i).2.1))=normalizedBaseEnds X p
  underlying_template :
    ((List.ofFn (fun i => s((ends i).1.1,(ends i).2.1))) : Multiset (Sym2 ℕ))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ))
  forward_counts : ∀ i : Fin (baseBundles X).length,
    (List.ofFn (fun j => ((ends j).1.1,(ends j).2.1))).count (baseBundlePair X i)=
      (baseProfileCounts X p)[i.1]'(by rw [baseProfileCounts_length]; exact i.2)
  forward : Matrix (Fin X.template.bonds.length) (Fin X.template.bonds.length) ℤ
  inverse : Matrix (Fin X.template.bonds.length) (Fin X.template.bonds.length) ℤ
  forward_inverse : forward*inverse=1
  inverse_forward : inverse*forward=1
  reference_column : ∀ j,inverse j ⟨0,base_bond_pos X⟩=1
  free_bounds : ∀ j,∀ i : Fin (X.template.n-1),
    inverse j ⟨i.1,base_free_lt X i⟩ ∈ ({-1,0,1} : Finset ℤ)
  gap_row : ∀ j,forward ⟨X.template.n-1,base_gap_lt X⟩ j=
    -energySign ends ⟨0,base_atom_pos X⟩ j
  internal_rows : ∀ v : Fin (X.template.n-2),∀ j,
    forward ⟨X.template.n+v.1,base_internal_lt X v⟩ j=
      -energySign ends ⟨v.1+2,base_vertex_lt X v⟩ j

end WaveTurbulence.Vine.Param
