/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.BridgeY
import Mathlib.Tactic

/-! # Bridge, part 2: a T-route of the closure makes the case-(4) component a T-vine (packet L6, `C4TBridge`)

* `isDoubledTriangle_of_isT`: main's `IsT` (three atoms, pairwise two bonds, six bonds) is D11's doubled triangle.
* `yrouteT_graph`: a route of complete (Y2) sequences to `T` (main's `YRouteT`, under `RegCore`) is a D11 `Y2Step` path
  of bond multigraphs to a doubled triangle.
* `isClosure_closureTwo`: for two β-chains (`σ = 0`), main's `closureTwo` is D11's closure `IsClosure M.atoms b b'`.
* `isBlock_of_case4`: the component is a block with joints `b, b'`.
* `isTVine_of_two`: hence `M.IsTVine M.atoms b b'` (M2 §4.8 (A2)). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount
universe u v
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp4 WaveTurbulence.TVine

section general
variable {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem filter_ends_disjoint (N : Molecule V D) {e e' : Sym2 V} (h : e ≠ e') :
    Disjoint (N.bonds.filter fun x => N.ends x = e) (N.bonds.filter fun x => N.ends x = e') :=
  Finset.disjoint_filter.mpr fun x _ h1 h2 => h (h1.symm.trans h2)

/-- **`IsT` is the doubled triangle.** -/
theorem isDoubledTriangle_of_isT {N : Molecule V D} (h : IsT N) : IsDoubledTriangle (molGraph N) := by
  obtain ⟨e, f, g, hef, hfg, heg, hat, h1, h2, h3, h6⟩ := h
  refine ⟨e, f, g, hef, heg, hfg, hat, fun x => ?_⟩
  by_cases hx : x = s(e, f) ∨ x = s(f, g) ∨ x = s(e, g)
  · rw [if_pos hx]
    rcases hx with rfl | rfl | rfl
    exacts [h1, h2, h3]
  · rw [if_neg hx]
    push Not at hx
    obtain ⟨hx1, hx2, hx3⟩ := hx
    have d12 : s(e, f) ≠ s(f, g) := by
      intro h; rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
      exacts [hef h, heg h]
    have d13 : s(e, f) ≠ s(e, g) := by
      intro h; rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
      exacts [hfg h, heg h]
    have d23 : s(f, g) ≠ s(e, g) := by
      intro h; rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
      exacts [hef h.symm, hfg h]
    set F := fun y : Sym2 V => N.bonds.filter fun z => N.ends z = y with hF
    have hsub : F s(e, f) ∪ F s(f, g) ∪ F s(e, g) ∪ F x ⊆ N.bonds := by
      intro z hz
      simp only [hF, mem_union, mem_filter] at hz
      rcases hz with ((h | h) | h) | h <;> exact h.1
    have hcard := card_le_card hsub
    rw [card_union_of_disjoint, card_union_of_disjoint, card_union_of_disjoint] at hcard
    · change (molGraph N).mult s(e, f) + (molGraph N).mult s(f, g) + (molGraph N).mult s(e, g) +
        (molGraph N).mult x ≤ N.bonds.card at hcard
      rw [molGraph_mult, molGraph_mult, molGraph_mult, h1, h2, h3, h6] at hcard
      change (molGraph N).mult x = 0
      omega
    · exact filter_ends_disjoint N d12
    · exact disjoint_union_left.mpr ⟨filter_ends_disjoint N d13, filter_ends_disjoint N d23⟩
    · exact disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨filter_ends_disjoint N hx1.symm,
        filter_ends_disjoint N hx2.symm⟩, filter_ends_disjoint N hx3.symm⟩

theorem inGroup_atoms (N : Molecule V D) (x : D) : N.InGroup N.atoms x := ⟨N.atom_mem _, N.atom_mem _⟩

theorem adj_of_bondsBetween_pos {N : Molecule V D} {p q : V} (h : 0 < N.bondsBetween p q) : N.Adj p q := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  have he := (mem_filter.mp hx).2
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨x, h1, h2⟩
  · exact ⟨N.mate x, h2, by rw [N.mate_mate]; exact h1⟩

end general

/-- **A T-route gives a D11 path to a doubled triangle.** -/
theorem yrouteT_graph {k : ℕ} {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]
    {N : Molecule V D} (h : YRouteT k N) :
    RegCore N → ∃ G', Relation.ReflTransGen Y2Step (molGraph N) G' ∧ IsDoubledTriangle G' := by
  induction h with
  | done M hT => exact fun _ => ⟨molGraph M, Relation.ReflTransGen.refl, isDoubledTriangle_of_isT hT⟩
  | y2 k M hcap C E _ _ ih =>
    intro hR
    obtain ⟨G', h1, h2⟩ := ih (hR.post E)
    exact ⟨G', (y2seq_reflTransGen C E hcap hR.loop).trans h1, h2⟩

end WaveTurbulence.GammaLow.FinalCount
