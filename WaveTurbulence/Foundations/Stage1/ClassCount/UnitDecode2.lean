/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode1
public import WaveTurbulence.Foundations.Molecule.VineRealizationGroups
import Mathlib.Tactic

/-!
# CLASSCOUNT: a single vine ingredient is an ingredient code

For a vine realization `R` (`isVine_iff_realization`) the directed bonds of the group `S`, relabelled by
`ingPosOf 0 n swap ∘ R.f`, are the arcs `ingArcs c (ingPosOf 0 n swap)` of an ingredient code `c` with type `X`,
rung vector `R.k` and `swap = decide (R.f a = 1)`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The directed arcs (as ordered pairs of labels) of the bonds of `M` inside the group `S`. -/
noncomputable def groupArcs (M : Molecule V D) (S : Finset V) (lab : V → ℕ) : Multiset (ℕ × ℕ) := by
  classical
  exact ((Finset.univ.filter fun x => M.out x = true ∧ M.InGroup S x).val).map
    (fun x => (lab (M.atom x), lab (M.atom (M.mate x))))

theorem vine_decode (M : Molecule V D) {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (p : ℕ) :
    ∃ c : IngCode, c.Wf ∧ c.X = X ∧ c.k = R.k ∧ c.swap = decide (R.f a = 1) ∧
      groupArcs M S (fun v => ingPosOf p c.size c.swap (R.f v)) =
        ((ingArcs c (ingPosOf p c.size c.swap) : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  classical
  set P : Multiset (ℕ × ℕ) := ((Finset.univ.filter fun x => M.out x = true ∧ M.InGroup S x).val).map
    (fun x => (R.f (M.atom x), R.f (M.atom (M.mate x)))) with hP
  have hP' : P.map (fun p => s(p.1, p.2)) =
      (((X.expand R.k).bonds.map (fun p => s(p.1, p.2)) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) := by
    have h := R.bonds_eq
    unfold Molecule.groupBonds at h
    rw [Multiset.map_map] at h
    rw [hP, Multiset.map_map]
    simp only [Multiset.map_map, Function.comp_def, Molecule.ends, Sym2.map_mk] at h ⊢
    rw [h]
  obtain ⟨o, ho, hoP⟩ := exists_orientation (X.expand R.k).bonds P hP'
  let c : IngCode := ⟨X, R.k, decide (R.f a = 1), o⟩
  refine ⟨c, ⟨R.length_eq, by simpa [c] using ho⟩, rfl, rfl, rfl, ?_⟩
  unfold groupArcs
  have hmap : ∀ (pos : ℕ → ℕ),
      ((Finset.univ.filter fun x => M.out x = true ∧ M.InGroup S x).val).map
        (fun x => (pos (R.f (M.atom x)), pos (R.f (M.atom (M.mate x))))) =
      P.map (fun p => (pos p.1, pos p.2)) := by
    intro pos; rw [hP, Multiset.map_map]; rfl
  rw [show (fun x => ((fun v => ingPosOf p c.size c.swap (R.f v)) (M.atom x),
      (fun v => ingPosOf p c.size c.swap (R.f v)) (M.atom (M.mate x)))) =
      fun x => (ingPosOf p c.size c.swap (R.f (M.atom x)), ingPosOf p c.size c.swap (R.f (M.atom (M.mate x))))
      from rfl, hmap, ← hoP]
  unfold ingArcs
  rw [Multiset.map_coe, List.map_map]
  congr 1
  refine List.map_congr_left (fun q _ => ?_)
  simp only [Function.comp_def, orient]
  split_ifs <;> rfl

end WaveTurbulence.ClassCount
