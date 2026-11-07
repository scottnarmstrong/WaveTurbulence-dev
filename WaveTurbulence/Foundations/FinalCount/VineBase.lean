/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.Prop94Ops
public import WaveTurbulence.Foundations.FinalCount.AlphaBasics
public import WaveTurbulence.Foundations.FinalCount.TriLattice
/-! Vine removal (DH23 Step 1, L1775), part 1 (FINALCOUNT-G2): darts of the doubly cut molecule `cutMol`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem restrictP_sum {E : Type*} [AddCommMonoid E] (N : Molecule V D) (P : V → Prop) [DecidablePred P] (h : PClosed N P)
    {z : V} (hz : P z) (g : D → E) :
    ∑ x ∈ (restrictP N P h).dartsAt z, g x.1 = ∑ x ∈ N.dartsAt z, g x := by
  rw [restrictP_dartsAt N P h hz, Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem]
  intro x hx
  rw [mem_dartsAt] at hx
  rw [hx]; exact hz

namespace VineCut
variable {M : Molecule V D} (K : VineCut M)

/-- The molecule after the first cut. -/
def m1 : Molecule V D := M.cut K.C.upper K.fa K.x₁ K.x₂

theorem cutMol_eq : K.cutMol = K.m1.cut K.C.lower K.fb K.y₁ K.y₂ := rfl

theorem a_atom : K.C.upper ∈ M.atoms := objectAtoms_sub K.C K.a_mem
theorem b_atom : K.C.lower ∈ M.atoms := objectAtoms_sub K.C K.b_mem
theorem fa_fresh : K.fa ∉ M.atoms := K.cut_a.2.1
theorem fb_fresh1 : K.fb ∉ K.m1.atoms := K.cut_b.2.1
theorem fb_fresh : K.fb ∉ M.atoms := fun h => K.fb_fresh1 (by
  show K.fb ∈ insert K.fa M.atoms; exact Finset.mem_insert_of_mem h)
theorem fa_ne_fb : K.fa ≠ K.fb := fun e => K.fb_fresh1 (by
  show K.fb ∈ insert K.fa M.atoms; rw [← e]; exact Finset.mem_insert_self _ _)
theorem fa_ne_b : K.fa ≠ K.C.lower := fun e => K.fa_fresh (e ▸ K.b_atom)
theorem fb_ne_a : K.fb ≠ K.C.upper := fun e => K.fb_fresh (e ▸ K.a_atom)

theorem dartsAt_other {z : V} (hz : z ∈ M.atoms) (hza : z ≠ K.C.upper) (hzb : z ≠ K.C.lower) :
    K.cutMol.dartsAt z = M.dartsAt z := by
  have hzfa : z ≠ K.fa := fun e => K.fa_fresh (e ▸ hz)
  have hzfb : z ≠ K.fb := fun e => K.fb_fresh (e ▸ hz)
  rw [cutMol_eq, cut_dartsAt_other K.m1 K.cut_b hzb hzfb]
  exact cut_dartsAt_other M K.cut_a hza hzfa

theorem dartsAt_fa : K.cutMol.dartsAt K.fa = (M.dartsAt K.C.upper).filter (fun x => x ≠ K.x₁ ∧ x ≠ K.x₂) := by
  rw [cutMol_eq, cut_dartsAt_other K.m1 K.cut_b K.fa_ne_b K.fa_ne_fb]
  ext x
  rw [mem_dartsAt, Finset.mem_filter, mem_dartsAt]
  have := cut_mem_dartsAt_v₂ M K.cut_a x
  rw [mem_dartsAt] at this
  change (M.cut K.C.upper K.fa K.x₁ K.x₂).atom x = K.fa ↔ _
  rw [this]

theorem m1_dartsAt_b : K.m1.dartsAt K.C.lower = M.dartsAt K.C.lower :=
  cut_dartsAt_other M K.cut_a K.ab_ne.symm K.fa_ne_b.symm

theorem dartsAt_fb : K.cutMol.dartsAt K.fb = (M.dartsAt K.C.lower).filter (fun x => x ≠ K.y₁ ∧ x ≠ K.y₂) := by
  ext x
  rw [mem_dartsAt, Finset.mem_filter, mem_dartsAt]
  have h1 := cut_mem_dartsAt_v₂ K.m1 K.cut_b x
  rw [mem_dartsAt] at h1
  have h2 : x ∈ K.m1.dartsAt K.C.lower ↔ x ∈ M.dartsAt K.C.lower := by rw [K.m1_dartsAt_b]
  rw [mem_dartsAt, mem_dartsAt] at h2
  change (K.m1.cut K.C.lower K.fb K.y₁ K.y₂).atom x = K.fb ↔ _
  rw [h1, h2]

theorem sum_a {E : Type*} [AddCommMonoid E] (g : D → E) :
    ∑ x ∈ M.dartsAt K.C.upper, g x = ∑ x ∈ K.cutMol.dartsAt K.fa, g x + (g K.x₁ + g K.x₂) := by
  have h1 := cut_sum_split M K.cut_a g
  have h2 := cut_dartsAt_v_eq M K.cut_a
  have hne := cut_x_ne M K.cut_a
  have h3 : K.cutMol.dartsAt K.fa = K.m1.dartsAt K.fa := by
    rw [cutMol_eq]; exact cut_dartsAt_other K.m1 K.cut_b K.fa_ne_b K.fa_ne_fb
  rw [h3]
  change ∑ x ∈ M.dartsAt K.C.upper, g x = ∑ x ∈ (M.cut K.C.upper K.fa K.x₁ K.x₂).dartsAt K.C.upper, g x +
    ∑ x ∈ (M.cut K.C.upper K.fa K.x₁ K.x₂).dartsAt K.fa, g x at h1
  rw [h1, h2, Finset.sum_pair hne]; abel

theorem sum_b {E : Type*} [AddCommMonoid E] (g : D → E) :
    ∑ x ∈ M.dartsAt K.C.lower, g x = ∑ x ∈ K.cutMol.dartsAt K.fb, g x + (g K.y₁ + g K.y₂) := by
  have h1 : ∑ x ∈ K.m1.dartsAt K.C.lower, g x =
      ∑ x ∈ K.cutMol.dartsAt K.C.lower, g x + ∑ x ∈ K.cutMol.dartsAt K.fb, g x :=
    cut_sum_split K.m1 K.cut_b g
  have h2 : K.cutMol.dartsAt K.C.lower = {K.y₁, K.y₂} := cut_dartsAt_v_eq K.m1 K.cut_b
  have hne := cut_x_ne K.m1 K.cut_b
  rw [← K.m1_dartsAt_b, h1, h2, Finset.sum_pair hne]; abel

end VineCut
end WaveTurbulence.FinalCount
