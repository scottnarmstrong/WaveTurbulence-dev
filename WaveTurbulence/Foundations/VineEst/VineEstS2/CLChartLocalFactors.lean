/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPhysicalChartLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS2.LocalResonanceFactor

/-! # Every actual chart atom has two local origin factors -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clPhysicalChart_slot_origin (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    {X : VineType} (A : FullVineChart G.molecule X U a b) (v : GBranch G.tree) (i : Fin 4)
    (p : Bond G.molecule U ⊕ Fin 2)
    (hvalue : ∀ {E : Type} [AddCommGroup E] (κ : GNode G.tree → E),
      (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
      origin G.molecule U (fun e => Mole.restrictLabels G κ e.1)
        (κ (clBoundaryNodes R 2)) (κ (clBoundaryNodes R 2)-κ (clBoundaryNodes R 3)) p = κ (Mole.slotNode G v i))
    (g r : Mom d) (x : Fin A.indexing.shape.n → Mom d) :
    origin G.molecule U ((A.chart g r).symm x).1 g r p = clPhysicalChartLabels R A g r x (Mole.slotNode G v i) := by
  have he := hvalue (clPhysicalChartLabels R A g r x) (clPhysicalChartLabels_matching R A g r x)
  have hlabels : (fun e : Bond G.molecule U => Mole.restrictLabels G (clPhysicalChartLabels R A g r x) e.1) =
      ((A.chart g r).symm x).1 := funext (clPhysicalChartLabels_bond R A g r x)
  have h2 : clPhysicalChartLabels R A g r x (clBoundaryNodes R 2) = g := clPhysicalChartLabels_boundary hU R A g r x 2
  have h3 : clPhysicalChartLabels R A g r x (clBoundaryNodes R 3) = g-r := clPhysicalChartLabels_boundary hU R A g r x 3
  rw [hlabels,h2,h3,sub_sub_cancel] at he
  exact he

/-- These are literal local source factors, constructed from actual slots,
not supplied as an extra parametrization premise. -/
theorem clChart_local_factors (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    {X : VineType} (A : FullVineChart G.molecule X U a b)
    (v : GBranch G.tree) (hv : v ∈ U) (ha : v ≠ a) :
    ∃ (p q t : Bond G.molecule U ⊕ Fin 2) (op oq : Bool),
      OriginAt G.molecule U b p v op ∧ OriginAt G.molecule U b q v (!op) ∧
      OriginAt G.molecule U b q v oq ∧ OriginAt G.molecule U b t v (!oq) ∧
      ∀ {d : ℕ} (g r : Mom d) (x : Fin A.indexing.shape.n → Mom d),
        omegaNode G (clPhysicalChartLabels R A g r x) v =
          2*inner ℝ
            (origin G.molecule U ((A.chart g r).symm x).1 g r p-origin G.molecule U ((A.chart g r).symm x).1 g r q)
            (origin G.molecule U ((A.chart g r).symm x).1 g r q-origin G.molecule U ((A.chart g r).symm x).1 g r t) := by
  obtain ⟨p,op,hp,hwp,hvp⟩ := clSlot_origin hU R v hv ha 1
  obtain ⟨q,oq,hq,hwq,hvq⟩ := clSlot_origin hU R v hv ha 0
  obtain ⟨t,ot,ht,hwt,hvt⟩ := clSlot_origin hU R v hv ha 3
  have hpq : oq = !op := by
    have he : (if op then (1 : ℝ) else -1) = -(if oq then 1 else -1) := by
      rw [← hwp,← hwq]
      by_cases hs : G.sign v.toNode = 1 <;> norm_num [Mole.slotWeight,hs]
    cases op <;> cases oq <;> norm_num at he <;> rfl
  have hqt : ot = !oq := by
    have he : (if oq then (1 : ℝ) else -1) = -(if ot then 1 else -1) := by
      rw [← hwq,← hwt]
      by_cases hs : G.sign v.toNode = 1 <;> norm_num [Mole.slotWeight,hs]
    cases oq <;> cases ot <;> norm_num at he <;> rfl
  refine ⟨p,q,t,op,oq,hp,hpq ▸ hq,hq,hqt ▸ ht,?_⟩
  intro d g r x
  have hc := omegaNode_local_factor (clPhysicalChartLabels R A g r x) v
    (clPhysicalChartLabels_conservation hU R A g r x v hv)
  have hpv := clPhysicalChart_slot_origin hU R A v 1 p hvp g r x
  have hqv := clPhysicalChart_slot_origin hU R A v 0 q hvq g r x
  have htv := clPhysicalChart_slot_origin hU R A v 3 t hvt g r x
  exact hc.trans (congrArg (fun z : ℝ => 2*z)
    (congrArg₂ (fun y z : Mom d => inner ℝ y z)
      (congrArg₂ (fun y z : Mom d => y-z) hpv.symm hqv.symm)
      (congrArg₂ (fun y z : Mom d => y-z) hqv.symm htv.symm)))

end WaveTurbulence.VineEstS2
