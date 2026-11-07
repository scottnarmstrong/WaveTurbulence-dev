/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm2a
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 2b: at most `R` imperfect components** (each imperfect component has `Σ contrib ≥ 2`, `Σ_all = 2R`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*}

theorem compDegSum_even (N : Molecule V D₀) [Fintype D₀] [DecidableEq D₀] (a : V) :
    Even (∑ v ∈ N.atoms.filter (fun v => N.SameComponent a v), N.deg v) := by
  have h1 : ∑ v ∈ N.atoms.filter (fun v => N.SameComponent a v), N.deg v = ∑ v ∈ (compMol N a).atoms, (compMol N a).deg v := by
    have : (compMol N a).atoms = N.atoms.filter (fun v => N.SameComponent a v) := by
      ext b; rw [mem_compMol]; simp [Finset.mem_filter]
    rw [this]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv' := Finset.mem_filter.1 hv
    exact (restrictP_deg N (compP N a) (compP_closed N a) hv'.2).symm
  rw [h1, sum_deg_eq (compMol N a), card_darts_eq_two_bonds (compMol N a)]
  exact even_two_mul _

theorem Good.imperfect_card_le {s : St.{u} V D₀} {R : ℕ} (hg : Good R s) [Fintype D₀] [DecidableEq D₀] {Rs : Finset V}
    (hR : CompRep s.M Rs) :
    (Rs.filter (fun a => ∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ contrib s b ≠ 0)).card ≤ R := by
  set S : V → ℤ := fun a => ∑ v ∈ s.M.atoms.filter (fun v => s.M.SameComponent a v), contrib s v with hS
  have hsum : ∑ a ∈ Rs, S a = 2 * R := by
    rw [← hg.sum_contrib, hR.sum_atoms (fun v => contrib s v)]
  have hnn : ∀ a, 0 ≤ S a := fun a => Finset.sum_nonneg fun v hv => hg.contrib_nonneg (Finset.mem_filter.1 hv).1
  have heven : ∀ a, Even (S a) := by
    intro a
    have e1 : S a = ∑ v ∈ s.M.atoms.filter (fun v => s.M.SameComponent a v), (s.cls v).base -
        ∑ v ∈ s.M.atoms.filter (fun v => s.M.SameComponent a v), (s.M.deg v : ℤ) := by
      rw [hS]; simp only [contrib]; rw [Finset.sum_sub_distrib]
    rw [e1]
    refine Even.sub (Finset.even_sum _ fun v _ => Cls.even_base _) ?_
    have := compDegSum_even s.M a
    obtain ⟨k, hk⟩ := this
    exact ⟨k, by exact_mod_cast hk⟩
  have himp : ∀ a ∈ Rs.filter (fun a => ∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ contrib s b ≠ 0), 2 ≤ S a := by
    intro a ha
    obtain ⟨-, b, hb, hsc, hne⟩ := Finset.mem_filter.1 ha
    have hpos : 0 < S a := by
      have hbS : contrib s b ≤ S a :=
        Finset.single_le_sum (f := fun v => contrib s v) (fun v hv => hg.contrib_nonneg (Finset.mem_filter.1 hv).1)
          (Finset.mem_filter.2 ⟨hb, hsc⟩)
      have := hg.contrib_nonneg hb
      omega
    obtain ⟨k, hk⟩ := heven a
    omega
  have key : ((Rs.filter (fun a => ∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ contrib s b ≠ 0)).card : ℤ) * 2
      ≤ 2 * (R : ℤ) := by
    calc ((Rs.filter (fun a => ∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ contrib s b ≠ 0)).card : ℤ) * 2
      = ∑ a ∈ Rs.filter (fun a => ∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ contrib s b ≠ 0), (2 : ℤ) := by simp
    _ ≤ ∑ a ∈ Rs.filter (fun a => ∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ contrib s b ≠ 0), S a :=
        Finset.sum_le_sum himp
    _ ≤ ∑ a ∈ Rs, S a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun a _ _ => hnn a
    _ = 2 * R := hsum
  have : ((Rs.filter (fun a => ∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ contrib s b ≠ 0)).card : ℤ) ≤ R := by omega
  exact_mod_cast this

end WaveTurbulence.FinalCountAsm
