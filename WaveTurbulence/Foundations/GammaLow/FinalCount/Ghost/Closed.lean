/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ex2G
/-! **L6E GHOST, part 10: Lemma 2.1 in its closed-set form** (M1-R2 NOTES §2, Lemma 2.1; REF-M1R2 §4.1 and repair R1).

*Statement (REF-M1R2 R1).* Let `S` be a set of atoms of a molecule, all with charge `c_v = 0`, whose only boundary darts
(darts at `S` whose mate is outside `S`) are `p ≠ q`, with opposite orientations. Then in every `(c_v)`-decoration the
two bonds of `p` and `q` carry the same momentum. At the outside atom `z` holding `mate p` and `mate q` (the third atom
of a triangle whose two other atoms are the ghosts `x`, `y`), the gap along `(mate p, mate q)` is `0`: the triangle is
not eligible (R29: SG at `v₁`, `v₂`, nonzero gap at `v₃`).

* `sum_darts_boundary`: `∑_{a ∈ S} ∑_{x at a} g x = ∑_{boundary darts} g x` for `g` odd under `mate`;
* `closedSet_kappa_eq` / `closedSet_zero_gap`: the conclusion on the molecule (applied to `M_sb = M₀`, where
  `c_v = 0` at every degree-4 atom, TARGET Def `defdecmol` L1308);
* `closedSet_zero_gap_down`: the same for the inherited decoration `κ₀ ∘ down` of a run state;
* `TriData.not_eligible_of_closedSet`: the contradiction with main's `hnz` (nonzero triangle gaps). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- **Flux through the boundary.** For `g` odd under `mate`, the sum over the darts of `S` is the sum over its
boundary darts (internal bonds cancel). -/
theorem sum_darts_boundary {E : Type*} [AddCommGroup E] (M : Molecule V D) (S : Finset V) (g : D → E)
    (hg : ∀ x, g (M.mate x) = -g x) :
    ∑ a ∈ S, ∑ x ∈ M.dartsAt a, g x =
      ∑ x ∈ Finset.univ.filter (fun x => M.atom x ∈ S ∧ M.atom (M.mate x) ∉ S), g x := by
  have h1 : ∑ a ∈ S, ∑ x ∈ M.dartsAt a, g x = ∑ x ∈ Finset.univ.filter (fun x => M.atom x ∈ S), g x := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun x => M.atom x ∈ S))
      (t := S) (g := M.atom) (fun x hx => (Finset.mem_filter.mp hx).2)]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ ha, h⟩
    · intro h; exact h.2
  rw [h1, ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun x => M.atom x ∈ S))
    (fun x => M.atom (M.mate x) ∈ S)]
  have hint : ∑ x ∈ (Finset.univ.filter (fun x => M.atom x ∈ S)).filter (fun x => M.atom (M.mate x) ∈ S), g x = 0 := by
    refine Finset.sum_involution (fun x _ => M.mate x) ?_ ?_ ?_ ?_
    · intro x _; rw [hg x]; simp
    · intro x _ _ h; exact M.mate_ne x h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hx.2, by rw [M.mate_mate]; exact hx.1⟩
    · intro x _; exact M.mate_mate x
  rw [hint, zero_add]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end WaveTurbulence.GammaLow.FinalCount.Ghost
