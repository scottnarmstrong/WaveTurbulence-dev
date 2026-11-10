/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
/-! # The low family is independent of `γ` (packet L6, item H/I)

For every `γ ≤ 1/2`, `𝒱_γ` is the enlarged family (`IsVineGamma γ = IsVineEnl`, ruling D11). So the stage-2 run in the
low range can be written once, for the fixed parameter `γL := 1/2` (PLAN-L6 §3c), and every `𝒱_γ` object, collection
and counting choice with `γ ≤ 1/2` is recast to the `γL` ones without changing any data (atoms, joints, the designated
bond of a hyper object). The recasts are mutually inverse and preserve every predicate of the carrier. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.Src
open Finset

/-- The fixed parameter of the low family. -/
noncomputable abbrev γL : ℝ := 1 / 2

theorem γL_le : γL ≤ 1 / 2 := le_rfl

section objects
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- For `γ ≤ 1/2`, a `𝒱_γ` vine is a vine of the enlarged family. -/
theorem isSomeVine_low_iff {γ : ℝ} (hγ : γ ≤ 1 / 2) {M : Molecule V D} {S : Finset V} {a b : V} :
    IsSomeVine γ M S a b ↔ M.IsVineEnl S a b :=
  ⟨fun h => h.elim (fun h => h.2) (fun h => absurd h.1 (not_lt.mpr hγ)), fun h => Or.inl ⟨hγ, h⟩⟩

theorem isSomeVine_recast {γ γ' : ℝ} (hγ : γ ≤ 1 / 2) (hγ' : γ' ≤ 1 / 2) {M : Molecule V D} {S : Finset V}
    {a b : V} (h : IsSomeVine γ M S a b) : IsSomeVine γ' M S a b :=
  (isSomeVine_low_iff hγ').mpr ((isSomeVine_low_iff hγ).mp h)

theorem Chain.recast {γ γ' : ℝ} (hγ : γ ≤ 1 / 2) (hγ' : γ' ≤ 1 / 2) {M : Molecule V D} {S : Finset V} {a b : V}
    {n : ℕ} (h : Chain γ M S a b n) : Chain γ' M S a b n := by
  induction h with
  | single h => exact Chain.single (isSomeVine_recast hγ hγ' h)
  | append _ h hST hac ih => exact Chain.append ih (isSomeVine_recast hγ hγ' h) hST hac

theorem IsVC.recast {γ γ' : ℝ} (hγ : γ ≤ 1 / 2) (hγ' : γ' ≤ 1 / 2) {M : Molecule V D} {S : Finset V} {a b : V}
    (h : IsVC γ M S a b) : IsVC γ' M S a b :=
  ⟨h.1, h.2.elim fun n hn => ⟨n, hn.recast hγ hγ'⟩⟩

theorem isDV_recast {γ γ' : ℝ} (hγ : γ ≤ 1 / 2) (hγ' : γ' ≤ 1 / 2) {M : Molecule V D} {S : Finset V} {a b : V}
    (h : IsDV γ M S a b) : IsDV γ' M S a b := by
  obtain ⟨hσ, A, B, hA, hB, hAB, hS⟩ := h
  exact ⟨hσ, A, B, isSomeVine_recast hγ hγ' hA, isSomeVine_recast hγ hγ' hB, hAB, hS⟩

/-- Recast of a hyper realization (same designated bond). -/
def HyperLikeRealization.recast {γ γ' : ℝ} (hγ : γ ≤ 1 / 2) (hγ' : γ' ≤ 1 / 2) {M : Molecule V D} {S : Finset V}
    {a b : V} (R : HyperLikeRealization γ M S a b) : HyperLikeRealization γ' M S a b :=
  ⟨R.added, R.ends_eq, R.adjoint.recast hγ hγ'⟩

/-- Recast of a vine-like object shape. -/
def VineLikeObject.recast {γ γ' : ℝ} (hγ : γ ≤ 1 / 2) (hγ' : γ' ≤ 1 / 2) {M : Molecule V D} {S : Finset V}
    {a b : V} : VineLikeObject γ M S a b → VineLikeObject γ' M S a b
  | .vc h => .vc (h.recast hγ hγ')
  | .hyper R => .hyper (R.recast hγ hγ')

/-- **Recast of an object** between two parameters of the low range (same atoms, joints and designation). -/
def Object.recast {γ γ' : ℝ} (hγ : γ ≤ 1 / 2) (hγ' : γ' ≤ 1 / 2) {M : Molecule V D} (U : Object γ M) :
    Object γ' M :=
  ⟨U.atoms, U.upper, U.lower, U.shape.recast hγ hγ'⟩

variable {γ γ' : ℝ} (hγ : γ ≤ 1 / 2) (hγ' : γ' ≤ 1 / 2) {M : Molecule V D}

@[simp] theorem Object.recast_atoms (U : Object γ M) : (U.recast hγ hγ').atoms = U.atoms := rfl
@[simp] theorem Object.recast_upper (U : Object γ M) : (U.recast hγ hγ').upper = U.upper := rfl
@[simp] theorem Object.recast_lower (U : Object γ M) : (U.recast hγ hγ').lower = U.lower := rfl

@[simp] theorem Object.recast_recast (U : Object γ M) : (U.recast hγ hγ').recast hγ' hγ = U := by
  obtain ⟨A, a, b, sh⟩ := U
  cases sh <;> rfl

@[simp] theorem Object.recast_containsDart (U : Object γ M) (x : D) :
    (U.recast hγ hγ').ContainsDart x ↔ U.ContainsDart x := by
  obtain ⟨A, a, b, sh⟩ := U
  cases sh <;> rfl

@[simp] theorem Object.recast_hasGapKind {d : ℕ} (U : Object γ M) (L g η : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (k : Molecule.GapKind) :
    (U.recast hγ hγ').HasGapKind L g η w κ k ↔ U.HasGapKind L g η w κ k := by
  obtain ⟨A, a, b, sh⟩ := U
  cases sh <;> rfl

@[simp] theorem Object.recast_isContained (U U' : Object γ M) :
    (U.recast hγ hγ').IsContained (U'.recast hγ hγ') ↔ U.IsContained U' := by
  obtain ⟨A, a, b, sh⟩ := U
  obtain ⟨A', a', b', sh'⟩ := U'
  cases sh <;> cases sh' <;> rfl

theorem allowedCollectionObject_recast {w : ℕ} {G : Garden w} (U : Object γ G.molecule) :
    AllowedCollectionObject γ' G (U.recast hγ hγ') ↔ AllowedCollectionObject γ G U := by
  obtain ⟨A, a, b, sh⟩ := U
  cases sh with
  | vc h =>
    show (IsSomeVine γ' _ A a b ∧ _) ↔ (IsSomeVine γ _ A a b ∧ _)
    rw [isSomeVine_low_iff hγ', isSomeVine_low_iff hγ]
    exact Iff.rfl
  | hyper R =>
    show IsSomeVine γ' _ A a b ↔ IsSomeVine γ _ A a b
    rw [isSomeVine_low_iff hγ', isSomeVine_low_iff hγ]
    exact Iff.rfl

end objects

end WaveTurbulence.GammaLow.FinalCount.Src
