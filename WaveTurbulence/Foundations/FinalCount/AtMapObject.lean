/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AtMapVine
public import WaveTurbulence.Foundations.Spine.SourceCountingObjects
import Mathlib.Tactic

/-! # ATOM-TRANSPORT, part 3: hyper realizations, vine-like objects, `Object`, gap kinds

`hlrMap`, `vlMap`, `objMap` carry a hyper realization, a vine-like object and an `Object` of `M` to the
corresponding one of `mapAtoms M ι` (same darts, atoms and joints through `ι`).  Each is bijective
(`hlrMapEquiv`, `vlMapEquiv`, `objMapEquiv`), so every object of `mapAtoms M ι` is the image of exactly one
object of `M`; `IsGap`, `HasGapKind`, `IsContained`, `ContainsDart`, `IsInterior` correspond. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.AtomTransport
open WaveTurbulence WaveTurbulence.MoleProp WaveTurbulence.LGSpine.SourceVine

variable {V W D : Type*} [DecidableEq V] [DecidableEq W] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) (ι : V ↪ W)

theorem mapAtoms_isBlockGap {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (S : Finset V) (a : V)
    (r : Mom d) :
    (mapAtoms M ι).IsBlockGap L w κ (S.map ι) (ι a) r ↔ M.IsBlockGap L w κ S a r := by
  unfold Molecule.IsBlockGap
  simp only [mapAtoms_atom, mapAtoms_out, ι.injective.eq_iff, mapAtoms_inGroup]

/-! ### Hyper realizations -/

section Hyper
variable {M ι} {S : Finset V} {a b : V}

/-- A hyper realization of `M` is one of `mapAtoms M ι` (same deleted bond). -/
def hlrMap (R : HyperLikeRealization M S a b) :
    HyperLikeRealization (mapAtoms M ι) (S.map ι) (ι a) (ι b) :=
  ⟨R.added, (mapAtoms_ends_iff M ι R.added a b).mpr R.ends_eq,
    (mapAtoms_isVC (M.eraseBond R.added) ι S a b).mpr R.adjoint⟩

/-- The pullback of a hyper realization of `mapAtoms M ι` on the image of a group. -/
def hlrComap (R : HyperLikeRealization (mapAtoms M ι) (S.map ι) (ι a) (ι b)) :
    HyperLikeRealization M S a b :=
  ⟨R.added, (mapAtoms_ends_iff M ι R.added a b).mp R.ends_eq,
    (mapAtoms_isVC (M.eraseBond R.added) ι S a b).mp R.adjoint⟩

@[simp] theorem hlrMap_added (R : HyperLikeRealization M S a b) : (hlrMap (ι := ι) R).added = R.added := rfl
@[simp] theorem hlrComap_added (R : HyperLikeRealization (mapAtoms M ι) (S.map ι) (ι a) (ι b)) :
    (hlrComap R).added = R.added := rfl

theorem hlrComap_hlrMap (R : HyperLikeRealization M S a b) : hlrComap (hlrMap (ι := ι) R) = R := rfl
theorem hlrMap_hlrComap (R : HyperLikeRealization (mapAtoms M ι) (S.map ι) (ι a) (ι b)) :
    hlrMap (hlrComap R) = R := rfl

/-- Hyper realizations of `M` on `(S, a, b)` and of `mapAtoms M ι` on `(S.map ι, ι a, ι b)` are in bijection. -/
def hlrMapEquiv (M : Molecule V D) (ι : V ↪ W) (S : Finset V) (a b : V) :
    HyperLikeRealization M S a b ≃ HyperLikeRealization (mapAtoms M ι) (S.map ι) (ι a) (ι b) where
  toFun := hlrMap
  invFun := hlrComap
  left_inv := hlrComap_hlrMap
  right_inv := hlrMap_hlrComap

/-- Every hyper realization on an arbitrary group of `mapAtoms M ι` comes from one of `M`. -/
theorem exists_hlr_of_mapAtoms {S' : Finset W} {a' b' : W} (R' : HyperLikeRealization (mapAtoms M ι) S' a' b') :
    ∃ (S : Finset V) (a b : V), S' = S.map ι ∧ a' = ι a ∧ b' = ι b ∧
      ∃ R : HyperLikeRealization M S a b, hlrMap (ι := ι) R ≍ R' := by
  obtain ⟨S, a, b, rfl, rfl, rfl, h⟩ := exists_isVC_of_mapAtoms (M.eraseBond R'.added) ι R'.adjoint
  exact ⟨S, a, b, rfl, rfl, rfl, hlrComap R', heq_of_eq (hlrMap_hlrComap R')⟩

theorem hlr_isGap_iff (R : HyperLikeRealization M S a b) {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (r : Mom d) : (hlrMap (ι := ι) R).IsGap L w κ r ↔ R.IsGap L w κ r := by
  unfold HyperLikeRealization.IsGap
  exact mapAtoms_isBlockGap (M.eraseBond R.added) ι L w (fun x => κ x.1) S a r

theorem hlr_isContained_iff {A : Finset V} {x y : V} (P : HyperLikeRealization M A x y)
    (R : HyperLikeRealization M S a b) :
    (hlrMap (ι := ι) P).IsContained (hlrMap (ι := ι) R) ↔ P.IsContained R := by
  unfold HyperLikeRealization.IsContained
  simp only [Finset.map_subset_map, hlrMap_added, mapAtoms_mate, Finset.map_inj]

theorem mapAtoms_isHV (S : Finset V) (a b : V) :
    IsHV (mapAtoms M ι) (S.map ι) (ι a) (ι b) ↔ IsHV M S a b := by
  unfold IsHV
  refine exists_congr fun e => and_congr (mapAtoms_ends_iff M ι e a b) ?_
  exact mapAtoms_isSomeVine (M.eraseBond e) ι S a b

theorem mapAtoms_isHVC (S : Finset V) (a b : V) :
    IsHVC (mapAtoms M ι) (S.map ι) (ι a) (ι b) ↔ IsHVC M S a b := by
  unfold IsHVC
  refine exists_congr fun e => and_congr (mapAtoms_ends_iff M ι e a b) ?_
  exact and_congr (mapAtoms_isBlock (M.eraseBond e) ι S a b)
    (exists_congr fun n => and_congr Iff.rfl (mapAtoms_chain (M.eraseBond e) ι S a b n))

end Hyper

/-! ### Vine-like objects -/

section VL
variable {M ι} {S : Finset V} {a b : V}

/-- A vine-like object of `M` as one of `mapAtoms M ι`. -/
def vlMap : VineLikeObject M S a b → VineLikeObject (mapAtoms M ι) (S.map ι) (ι a) (ι b)
  | .vc h => .vc ((mapAtoms_isVC M ι S a b).mpr h)
  | .hyper R => .hyper (hlrMap R)

theorem vlMap_injective : Function.Injective (vlMap (M := M) (ι := ι) (S := S) (a := a) (b := b)) := by
  intro P Q h
  cases P with
  | vc h1 =>
    cases Q with
    | vc h2 => rfl
    | hyper R => exact absurd h (by simp [vlMap])
  | hyper R1 =>
    cases Q with
    | vc h2 => exact absurd h (by simp [vlMap])
    | hyper R2 =>
      simp only [vlMap, VineLikeObject.hyper.injEq] at h
      rw [← hlrComap_hlrMap (ι := ι) R1, ← hlrComap_hlrMap (ι := ι) R2, h]

theorem vlMap_surjective : Function.Surjective (vlMap (M := M) (ι := ι) (S := S) (a := a) (b := b)) := by
  intro P'
  cases P' with
  | vc h => exact ⟨.vc ((mapAtoms_isVC M ι S a b).mp h), rfl⟩
  | hyper R => exact ⟨.hyper (hlrComap R), by simp [vlMap, hlrMap_hlrComap]⟩

theorem vl_isGap_iff (C : VineLikeObject M S a b) {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (r : Mom d) : (vlMap (ι := ι) C).IsGap L w κ r ↔ C.IsGap L w κ r := by
  cases C with
  | vc h => exact mapAtoms_isBlockGap M ι L w κ S a r
  | hyper R => exact hlr_isGap_iff R L w κ r

theorem vl_isContained_iff {A : Finset V} {x y : V} (P : VineLikeObject M A x y) (C : VineLikeObject M S a b) :
    (vlMap (ι := ι) P).IsContained (vlMap (ι := ι) C) ↔ P.IsContained C := by
  cases P with
  | vc h1 =>
    cases C with
    | vc h2 => simp [vlMap, VineLikeObject.IsContained, Finset.map_subset_map]
    | hyper R => simp [vlMap, VineLikeObject.IsContained, Finset.map_subset_map]
  | hyper R1 =>
    cases C with
    | vc h2 => simp [vlMap, VineLikeObject.IsContained, Finset.map_subset_map]
    | hyper R2 =>
      simp only [vlMap, VineLikeObject.IsContained]
      exact hlr_isContained_iff R1 R2

end VL

/-! ### Objects -/

section Obj
variable {M ι}

/-- An object of `M` as an object of `mapAtoms M ι`. -/
def objMap (O : Object M) : Object (mapAtoms M ι) :=
  ⟨O.atoms.map ι, ι O.upper, ι O.lower, vlMap O.shape⟩

@[simp] theorem objMap_atoms (O : Object M) : (objMap (ι := ι) O).atoms = O.atoms.map ι := rfl
@[simp] theorem objMap_upper (O : Object M) : (objMap (ι := ι) O).upper = ι O.upper := rfl
@[simp] theorem objMap_lower (O : Object M) : (objMap (ι := ι) O).lower = ι O.lower := rfl

theorem objMap_injective : Function.Injective (objMap (M := M) (ι := ι)) := by
  rintro ⟨S, a, b, P⟩ ⟨S2, a2, b2, Q⟩ h
  have h1 : S.map ι = S2.map ι := congrArg Object.atoms h
  have h2 : ι a = ι a2 := congrArg Object.upper h
  have h3 : ι b = ι b2 := congrArg Object.lower h
  rw [Finset.map_inj] at h1
  rw [ι.injective.eq_iff] at h2 h3
  subst h1 h2 h3
  have : P = Q := vlMap_injective (eq_of_heq (by
    have := Object.mk.inj h
    exact this.2.2.2))
  rw [this]

theorem objMap_surjective : Function.Surjective (objMap (M := M) (ι := ι)) := by
  rintro ⟨S', a', b', sh⟩
  cases sh with
  | vc h =>
    obtain ⟨S, a, b, rfl, rfl, rfl, h0⟩ := exists_isVC_of_mapAtoms M ι h
    exact ⟨⟨S, a, b, .vc h0⟩, rfl⟩
  | hyper R' =>
    obtain ⟨S, a, b, rfl, rfl, rfl, R, hR⟩ := exists_hlr_of_mapAtoms R'
    exact ⟨⟨S, a, b, .hyper R⟩, by
      change (⟨_, _, _, VineLikeObject.hyper (hlrMap R)⟩ : Object (mapAtoms M ι)) = _
      rw [eq_of_heq hR]⟩

/-- Objects of `M` and of `mapAtoms M ι` are in bijection. -/
noncomputable def objMapEquiv (M : Molecule V D) (ι : V ↪ W) : Object M ≃ Object (mapAtoms M ι) :=
  Equiv.ofBijective objMap ⟨objMap_injective, objMap_surjective⟩

theorem objMap_hasGapKind_iff (O : Object M) {d : ℕ} (L γ η : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (kind : Molecule.GapKind) :
    (objMap (ι := ι) O).HasGapKind L γ η w κ kind ↔ O.HasGapKind L γ η w κ kind := by
  unfold Object.HasGapKind
  exact exists_congr fun r => and_congr_left fun _ => vl_isGap_iff O.shape L w κ r

theorem objMap_isContained_iff (P Q : Object M) :
    (objMap (ι := ι) P).IsContained (objMap (ι := ι) Q) ↔ P.IsContained Q := by
  unfold Object.IsContained
  exact vl_isContained_iff P.shape Q.shape

theorem objMap_containsDart_iff (O : Object M) (x : D) :
    (objMap (ι := ι) O).ContainsDart x ↔ O.ContainsDart x := by
  obtain ⟨S, a, b, sh⟩ := O
  cases sh with
  | vc h => simp [objMap, vlMap, Object.ContainsDart, mapAtoms_inGroup]
  | hyper R => simp [objMap, vlMap, Object.ContainsDart, mapAtoms_inGroup]

theorem objMap_isInterior_iff (O : Object M) (v : V) :
    (objMap (ι := ι) O).IsInterior (ι v) ↔ O.IsInterior v := by
  simp [Object.IsInterior, Finset.mem_map' ι, ι.injective.ne_iff]

/-- Every atom of an object of `mapAtoms M ι` lies in the image of `ι`. -/
theorem object_atoms_range (O' : Object (mapAtoms M ι)) {v : W} (hv : v ∈ O'.atoms) : ∃ a, ι a = v := by
  obtain ⟨O, rfl⟩ := objMap_surjective (M := M) (ι := ι) O'
  obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hv
  exact ⟨a, rfl⟩

end Obj

end WaveTurbulence.AtomTransport
