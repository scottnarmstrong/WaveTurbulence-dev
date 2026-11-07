/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitCode1
public import WaveTurbulence.Foundations.LayerCnt.VineSlots
public import WaveTurbulence.Foundations.FinalCount.RedSpliceData
public import WaveTurbulence.Foundations.Molecule.VineCoherenceIndependent
import Mathlib.Tactic

/-!
# CLASSCOUNT: bookkeeping for vines (`m`, the realization-independent incoherency index)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The cardinality of a vine is `n(template) + 2 Σ k`. -/
theorem vine_card_eq {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b) :
    S.card = X.template.n + 2 * R.k.sum := by
  have h1 : S.card = (X.expand R.k).n := by
    rw [← Finset.card_range (X.expand R.k).n, ← R.image_eq, Finset.card_image_of_injOn R.injOn]
  rw [h1, expand_n X R.k R.length_eq]

theorem vine_card_m {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V} (hV : M.IsVine X S a b) :
    ∃ m : ℕ, (X.IsBad = true → S.card = 2 * m + 2) ∧ (X.IsBad = false → S.card = 2 * m + 5) := by
  obtain ⟨-, ⟨R⟩⟩ := isVine_iff_realization.mp hV
  have h := vine_card_eq R
  cases X <;> simp only [VineType.template, VineType.IsBad] at h ⊢
  · exact ⟨R.k.sum, fun _ => by omega, fun h' => by simp at h'⟩
  · exact ⟨R.k.sum + 1, fun _ => by omega, fun h' => by simp at h'⟩
  · exact ⟨R.k.sum + 2, fun h' => by simp at h', fun _ => by omega⟩
  · exact ⟨R.k.sum + 2, fun h' => by simp at h', fun _ => by omega⟩
  · exact ⟨R.k.sum + 2, fun h' => by simp at h', fun _ => by omega⟩
  · exact ⟨R.k.sum + 5, fun h' => by simp at h', fun _ => by omega⟩
  · exact ⟨R.k.sum + 3, fun h' => by simp at h', fun _ => by omega⟩
  · exact ⟨R.k.sum + 3, fun h' => by simp at h', fun _ => by omega⟩

/-- The joints of a realization may be swapped. -/
def vineRealizationSwap {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) : VineRealization M X S b a :=
  { R with joints_eq := by rw [Finset.pair_comm]; exact R.joints_eq }

theorem realizedIncoherencyIndex_swap {L : Type*} [DecidableEq L] {M : Molecule V D} {X : VineType} {S : Finset V}
    {a b : V} (R : VineRealization M X S a b) (layer : V → L) :
    realizedIncoherencyIndex (vineRealizationSwap R) layer = realizedIncoherencyIndex R layer := rfl

theorem realizedIncoherencyIndex_any {L : Type*} [DecidableEq L] {M : Molecule V D} (hM : M.IsMolecule)
    {X Y : VineType} {S : Finset V} {a b a' b' : V} (R : VineRealization M X S a b)
    (R' : VineRealization M Y S a' b') (hB : M.IsBlock S a b) (hB' : M.IsBlock S a' b') (layer : V → L) :
    realizedIncoherencyIndex R' layer = realizedIncoherencyIndex R layer := by
  have hj := Vine.block_joints_unique M hB hB'
  rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2
    exact (realizedIncoherencyIndex_eq M hM R R' hB layer).symm
  · subst h1; subst h2
    exact (realizedIncoherencyIndex_eq M hM (vineRealizationSwap R) R' (Mole.block_swap_joints M hB) layer).symm

/-- `vineIncoh` is the realized incoherency index of any realization. -/
theorem vineIncoh_eq {w : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule) {X : VineType}
    {T : Finset (GBranch G.tree)} {x y : GBranch G.tree} (hV : G.molecule.IsVine X T x y)
    (R : VineRealization G.molecule X T x y) (layer0 : GBranch G.tree → ℕ) :
    RedSplice.vineIncoh G layer0 T = realizedIncoherencyIndex R layer0 := by
  classical
  unfold RedSplice.vineIncoh
  have hex : ∃ X p q, G.molecule.IsVine X T p q := ⟨X, x, y, hV⟩
  rw [dif_pos hex]
  exact realizedIncoherencyIndex_any hM R _ hV.1 hex.choose_spec.choose_spec.choose_spec.1 layer0

end WaveTurbulence.ClassCount
