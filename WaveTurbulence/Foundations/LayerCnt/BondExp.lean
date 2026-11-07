/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Peak
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-! # The bond exponent `Σ_ℓ |𝔏_v − 𝔏_{v'}|` and its dart-sum bound (TARGET layerlad, `sumofexp0`)

`bondExp M S f = ∑_{bonds ℓ with both atoms in S} |f v − f v'|`, so the product in TARGET (`sumofexp0`) is
`C_0 ^ bondExp`. Each bond is counted by its outgoing dart. Counting all darts at atoms of `S` gives twice the
exponent (plus the bonds leaving `S`), which is easier to bound atom by atom.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem dst_comm (x y : ℕ) : dst x y = dst y x := by unfold dst; omega

/-- The bonds `ℓ` with both endpoints in `S` (each bond represented by its outgoing dart). -/
@[expose] def bondsIn (S : Finset V) : Finset D :=
  M.bonds.filter fun x => M.atom x ∈ S ∧ M.atom (M.mate x) ∈ S

/-- `∑_ℓ |𝔏_v − 𝔏_{v'}|` over the bonds `ℓ` joining atoms `v, v' ∈ S`. -/
@[expose] def bondExp (S : Finset V) (f : V → ℕ) : ℕ :=
  ∑ x ∈ bondsIn M S, dst (f (M.atom x)) (f (M.atom (M.mate x)))

/-- The same sum over all darts at atoms of `S` (the other endpoint is unrestricted). -/
@[expose] def dartExp (S : Finset V) (f : V → ℕ) : ℕ :=
  ∑ a ∈ S, ∑ x ∈ M.dartsAt a, dst (f a) (f (M.atom (M.mate x)))

theorem two_mul_bondExp_le (S : Finset V) (f : V → ℕ) : 2 * bondExp M S f ≤ dartExp M S f := by
  classical
  set g : D → ℕ := fun x => dst (f (M.atom x)) (f (M.atom (M.mate x))) with hg
  set T : Finset D := univ.filter (fun x => M.atom x ∈ S ∧ M.atom (M.mate x) ∈ S) with hT
  have hgm : ∀ x, g (M.mate x) = g x := by
    intro x; simp only [hg, M.mate_mate]; exact dst_comm _ _
  have h1 : ∑ x ∈ T, g x = ∑ x ∈ T.filter (fun x => M.out x = true), g x +
      ∑ x ∈ T.filter (fun x => ¬ M.out x = true), g x :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h2 : ∑ x ∈ T.filter (fun x => ¬ M.out x = true), g x =
      ∑ x ∈ T.filter (fun x => M.out x = true), g x := by
    apply Finset.sum_nbij' (fun x => M.mate x) (fun x => M.mate x)
    · intro x hx
      simp only [hT, mem_filter, mem_univ, true_and] at hx ⊢
      refine ⟨⟨hx.1.2, by rw [M.mate_mate]; exact hx.1.1⟩, ?_⟩
      rw [M.out_mate]; simpa using hx.2
    · intro x hx
      simp only [hT, mem_filter, mem_univ, true_and] at hx ⊢
      refine ⟨⟨hx.1.2, by rw [M.mate_mate]; exact hx.1.1⟩, ?_⟩
      rw [M.out_mate, hx.2]; simp
    · intro x _; exact M.mate_mate x
    · intro x _; exact M.mate_mate x
    · intro x _; exact (hgm x).symm
  have h3 : bondExp M S f = ∑ x ∈ T.filter (fun x => M.out x = true), g x := by
    unfold bondExp bondsIn Molecule.bonds
    apply Finset.sum_congr
    · ext x; simp [hT, and_comm, and_assoc]
    · intro x _; rfl
  have h4 : ∑ x ∈ T, g x ≤ ∑ x ∈ univ.filter (fun x => M.atom x ∈ S), g x := by
    apply Finset.sum_le_sum_of_subset
    intro x hx; simp only [hT, mem_filter, mem_univ, true_and] at hx ⊢; exact hx.1
  have h5 : ∑ x ∈ univ.filter (fun x => M.atom x ∈ S), g x = dartExp M S f := by
    unfold dartExp
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun x => M.atom x ∈ S)) (t := S)
      (g := fun x => M.atom x) (fun x hx => (mem_filter.mp hx).2)]
    apply Finset.sum_congr rfl
    intro a ha
    have : (univ.filter (fun x => M.atom x ∈ S)).filter (fun x => M.atom x = a) = M.dartsAt a := by
      ext x; simp only [mem_filter, mem_univ, true_and, Molecule.dartsAt]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ ha, h⟩
    rw [this]
    apply Finset.sum_congr rfl
    intro x hx
    have := (Mole.mem_dartsAt M a x).mp hx
    simp only [hg, this]
  omega

end WaveTurbulence.LayerCnt
