/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproShapeConn
public import WaveTurbulence.Foundations.FinalCount.SubproShapeDV
public import WaveTurbulence.Foundations.FinalCount.SubproShapeC1
import Mathlib.Tactic

/-!
# S4-SHAPE, packaged result: the host connectivity of a collected object at the level of `M₀`

`host_conn_final`: for `U ∈ C₂` of ordinary shape with three atoms (given G3's `UnselOK`), there is a host `S ⊇ U` (a DV or an LG/ZG vine-like object, disjoint from `C₁` and
the hinges) such that every collected object is inside `S` or harmless for `S`, and, whatever collected objects inside `S` have been
removed (ordinary ones by `ordPiece`, hyper ones with any designation), the joints of `U` are connected in the remaining molecule
of `S` (`removeBlocks`), both being remaining atoms.
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

theorem host_conn_final {M : Molecule V D} (hM : M.IsMolecule) {L γ η : ℝ} {w : Mom d} {c0 : V → Mom d}
    {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c0 κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c0 v = 0)
    (C : CollData M) (Unsel : Set (Object M))
    (hd22 : ∀ O ∈ C.C2Of L γ η w κ Unsel, ∀ O' ∈ C.C2Of L γ η w κ Unsel, O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms)
    (hsh : ∀ O ∈ C.C2Of L γ η w κ Unsel, (∃ h, O.shape = .vc h) →
      DoubleChain M O.atoms O.upper O.lower 1 ∨ DoubleChain M O.atoms O.upper O.lower 2 ∨
        M.IsVine .V O.atoms O.upper O.lower)
    {U : Object M} (hU : U ∈ C.C2Of L γ η w κ Unsel) (hUvc : ∃ h, U.shape = .vc h)
    (hUO : C.UnselOK L γ η w κ Unsel) (hU3 : U.atoms.card = 3) :
    ∃ S : Finset V, U.atoms ⊆ S ∧ Disjoint S C.hinges ∧ (∀ i, Harmless M S (C.collection i)) ∧
      (∀ O ∈ C.C2Of L γ η w κ Unsel, Clean M S O) ∧
      ∀ (ps : List (RemovalPiece V D)) (qs : List (AdjointPiece M)),
        (∀ P ∈ ps, ∃ O ∈ C.C2Of L γ η w κ Unsel, (∃ h, O.shape = .vc h) ∧ O.atoms ⊆ S ∧ P = ordPiece M O) →
        (∀ A ∈ qs, ∃ O ∈ C.C2Of L γ η w κ Unsel, (∃ R, O.shape = .hyper R) ∧ O.atoms ⊆ S ∧ A.atoms = O.atoms) →
        (∀ P ∈ ps, ∀ Q ∈ ps, P ≠ Q → Disjoint P.atoms Q.atoms) →
        (∀ P ∈ qs, ∀ Q ∈ qs, P ≠ Q → Disjoint P.atoms Q.atoms) →
        U.upper ∈ remainingAtoms S (ps ++ qs.map AdjointPiece.toRemoval) ∧
          U.lower ∈ remainingAtoms S (ps ++ qs.map AdjointPiece.toRemoval) ∧
          (removeBlocks M S (ps ++ qs.map AdjointPiece.toRemoval)).SameComponent U.upper U.lower := by
  obtain ⟨S, hUS, hS, hSh, hSC, hclean⟩ := exists_good_host hM hκ hc0 C Unsel hd22 hU (dvWitnessReduction_of_unselOK hM C Unsel hUO hU (by omega))
  exact ⟨S, hUS, hSh, fun i => harmless_of_disjoint (hSC i).symm, hclean,
    fun ps qs hps hqs hdis hQdis =>
      host_removal_connected hM hκ hc0 C Unsel hd22 hsh hU hUvc hUS hS ps qs hps hqs hdis hQdis⟩

/-- `host_conn_final`, with the connectivity as a chain of kept darts of `M` (the form that is lifted to the state): the joints of `U`
are joined by a chain of bonds of `M` between atoms of `S` that are not interior atoms of a removed piece, no dart of which is
killed by a removed piece. -/
theorem host_conn_final_keepAdj {M : Molecule V D} (hM : M.IsMolecule) {L γ η : ℝ} {w : Mom d} {c0 : V → Mom d}
    {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c0 κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c0 v = 0)
    (C : CollData M) (Unsel : Set (Object M))
    (hd22 : ∀ O ∈ C.C2Of L γ η w κ Unsel, ∀ O' ∈ C.C2Of L γ η w κ Unsel, O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms)
    (hsh : ∀ O ∈ C.C2Of L γ η w κ Unsel, (∃ h, O.shape = .vc h) →
      DoubleChain M O.atoms O.upper O.lower 1 ∨ DoubleChain M O.atoms O.upper O.lower 2 ∨
        M.IsVine .V O.atoms O.upper O.lower)
    {U : Object M} (hU : U ∈ C.C2Of L γ η w κ Unsel) (hUvc : ∃ h, U.shape = .vc h)
    (hUO : C.UnselOK L γ η w κ Unsel) (hU3 : U.atoms.card = 3) :
    ∃ S : Finset V, U.atoms ⊆ S ∧ Disjoint S C.hinges ∧ (∀ i, Harmless M S (C.collection i)) ∧
      (∀ O ∈ C.C2Of L γ η w κ Unsel, Clean M S O) ∧
      ∀ (ps : List (RemovalPiece V D)) (qs : List (AdjointPiece M)),
        (∀ P ∈ ps, ∃ O ∈ C.C2Of L γ η w κ Unsel, (∃ h, O.shape = .vc h) ∧ O.atoms ⊆ S ∧ P = ordPiece M O) →
        (∀ A ∈ qs, ∃ O ∈ C.C2Of L γ η w κ Unsel, (∃ R, O.shape = .hyper R) ∧ O.atoms ⊆ S ∧ A.atoms = O.atoms) →
        (∀ P ∈ ps, ∀ Q ∈ ps, P ≠ Q → Disjoint P.atoms Q.atoms) →
        (∀ P ∈ qs, ∀ Q ∈ qs, P ≠ Q → Disjoint P.atoms Q.atoms) →
        Relation.EqvGen (KeepAdj M S (ps ++ qs.map AdjointPiece.toRemoval)) U.upper U.lower := by
  obtain ⟨S, hUS, hSh, hH, hclean, h⟩ := host_conn_final hM hκ hc0 C Unsel hd22 hsh hU hUvc hUO hU3
  exact ⟨S, hUS, hSh, hH, hclean, fun ps qs a b c e =>
    (sameComponent_iff_eqvGen M S _ _ _).mp (h ps qs a b c e).2.2⟩

end WaveTurbulence.Subpro
