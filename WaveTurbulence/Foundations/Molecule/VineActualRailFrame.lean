/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRailFrame
public import WaveTurbulence.Foundations.Molecule.VineSingleRailCounts
public import WaveTurbulence.Foundations.Molecule.VineRungSequences
import Mathlib.Tactic

/-! # Actual full rail frames with independently separated fresh atoms -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*}

/-- Primitive coordinate data of two rails. Their final old ports may
coincide, but each individual rail has two distinct old endpoints. -/
structure RailLabelFrame {M : Molecule V D} {n : ℕ} (Q : FullRungSequence M n) where
  f : V → ℕ
  N : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  ha : a<N
  hb : b<N
  hc : c<N
  hd : d<N
  hab : a ≠ b
  hcd : c ≠ d
  upper : ∀ i : Fin (n+2),f (Q.u i.1)=railAtom N a b n i.1
  lower : ∀ i : Fin (n+2),f (Q.v i.1)=railAtom (N+n) c d n i.1

namespace RailLabelFrame
variable {M : Molecule V D} {n : ℕ} {Q : FullRungSequence M n} (F : RailLabelFrame Q)

include F

/-- Each complete upper rail is injective on its available coordinates. -/
theorem upper_injective : Function.Injective (fun i : Fin (n+2) => Q.u i.1) := by
  intro i j he
  apply railAtom_full_injective F.N F.a F.b n F.ha F.hb F.hab
  have hh := congrArg F.f he
  simpa only [F.upper] using hh

/-- Each complete lower rail is injective on its available coordinates. -/
theorem lower_injective : Function.Injective (fun i : Fin (n+2) => Q.v i.1) := by
  intro i j he
  apply railAtom_full_injective (F.N+n) F.c F.d n (by have := F.hc; omega)
    (by have := F.hd; omega) F.hcd
  have hh := congrArg F.f he
  simpa only [F.lower] using hh

/-- A fresh upper atom differs from every lower-rail atom. -/
theorem upper_cross (i j : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (hj : j<n+2) :
    Q.u i ≠ Q.v j := by
  intro he
  have hh := congrArg F.f he
  rw [F.upper ⟨i,by omega⟩,F.lower ⟨j,hj⟩] at hh
  exact railAtom_fresh_upper_cross F.N F.a F.b F.c F.d n i j
    F.ha F.hb F.hc F.hd hi hin hh

/-- A fresh lower atom differs from every upper-rail atom. -/
theorem lower_cross (i j : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (hj : j<n+2) :
    Q.v i ≠ Q.u j := by
  intro he
  have hh := congrArg F.f he
  rw [F.lower ⟨i,by omega⟩,F.upper ⟨j,hj⟩] at hh
  exact railAtom_fresh_lower_cross F.N F.a F.b F.c F.d n i j
    F.ha F.hb F.hc F.hd hi hin hh

variable [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every actual upper predecessor rail bond is single, including those
adjacent to a joint port. -/
theorem upper_prev_pair_degree (hM : M.IsMolecule) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    M.degIn {Q.u i,Q.u (i-1)} (Q.u i)=1 := by
  have hne (j k : ℕ) (hj : j<n+2) (hk : k<n+2) (hjk : j ≠ k) : Q.u j ≠ Q.u k := by
    intro he
    exact hjk (congrArg Fin.val (F.upper_injective (a₁ := ⟨j,hj⟩) (a₂ := ⟨k,hk⟩) he))
  exact four_row_single_pair_degree M hM (Q.upper i hi hin)
    (hne i (i-1) (by omega) (by omega) (by omega))
    (F.lower_cross i i hi hin (by omega))
    (F.lower_cross i (i-1) hi hin (by omega))
    (hne (i+1) i (by omega) (by omega) (by omega))
    (hne (i+1) (i-1) (by omega) (by omega) (by omega))

/-- The analogous lower predecessor rail bond is single. -/
theorem lower_prev_pair_degree (hM : M.IsMolecule) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    M.degIn {Q.v i,Q.v (i-1)} (Q.v i)=1 := by
  have hne (j k : ℕ) (hj : j<n+2) (hk : k<n+2) (hjk : j ≠ k) : Q.v j ≠ Q.v k := by
    intro he
    exact hjk (congrArg Fin.val (F.lower_injective (a₁ := ⟨j,hj⟩) (a₂ := ⟨k,hk⟩) he))
  exact four_row_single_pair_degree M hM (Q.lower i hi hin)
    (hne i (i-1) (by omega) (by omega) (by omega))
    (F.upper_cross i i hi hin (by omega))
    (F.upper_cross i (i-1) hi hin (by omega))
    (hne (i+1) i (by omega) (by omega) (by omega))
    (hne (i+1) (i-1) (by omega) (by omega) (by omega))

/-- Every actual upper successor rail bond is single, including those
adjacent to a joint port. -/
theorem upper_next_pair_degree (hM : M.IsMolecule) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    M.degIn {Q.u i,Q.u (i+1)} (Q.u i)=1 := by
  have hne (j k : ℕ) (hj : j<n+2) (hk : k<n+2) (hjk : j ≠ k) : Q.u j ≠ Q.u k := by
    intro he
    exact hjk (congrArg Fin.val (F.upper_injective (a₁ := ⟨j,hj⟩) (a₂ := ⟨k,hk⟩) he))
  exact four_row_single_next_pair_degree M hM (Q.upper i hi hin)
    (hne i (i+1) (by omega) (by omega) (by omega))
    (F.lower_cross i i hi hin (by omega))
    (F.lower_cross i (i+1) hi hin (by omega))
    (hne (i-1) i (by omega) (by omega) (by omega))
    (hne (i-1) (i+1) (by omega) (by omega) (by omega))

/-- The analogous lower successor rail bond is single. -/
theorem lower_next_pair_degree (hM : M.IsMolecule) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    M.degIn {Q.v i,Q.v (i+1)} (Q.v i)=1 := by
  have hne (j k : ℕ) (hj : j<n+2) (hk : k<n+2) (hjk : j ≠ k) : Q.v j ≠ Q.v k := by
    intro he
    exact hjk (congrArg Fin.val (F.lower_injective (a₁ := ⟨j,hj⟩) (a₂ := ⟨k,hk⟩) he))
  exact four_row_single_next_pair_degree M hM (Q.lower i hi hin)
    (hne i (i+1) (by omega) (by omega) (by omega))
    (F.upper_cross i i hi hin (by omega))
    (F.upper_cross i (i+1) hi hin (by omega))
    (hne (i-1) i (by omega) (by omega) (by omega))
    (hne (i-1) (i+1) (by omega) (by omega) (by omega))

end RailLabelFrame
end WaveTurbulence.Vine
