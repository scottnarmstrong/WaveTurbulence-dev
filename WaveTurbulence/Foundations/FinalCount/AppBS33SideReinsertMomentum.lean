/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33SideResidualParameters
public import WaveTurbulence.Foundations.FinalCount.AppBS33ReinsertSigns
public import WaveTurbulence.Foundations.FinalCount.AppBCutPairDifference
public import WaveTurbulence.Foundations.FinalCount.AppBAddedBondDecorations
import Mathlib.Tactic

/-! # Fixed conservation parameters on the 35 side after reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbS33SideCutMomentum {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) {d : ℕ} (c : V → Mom d) : Mom d :=
  (((appbCutSign M (appbS33Side r) (r.edge ⟨1,by decide⟩).val)⁻¹ : ℤˣ) : ℤ) •
    (∑ v ∈ appbS33Side r,c v)

noncomputable def appbS33SideReinsertMomentum {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) {d : ℕ} (c : V → Mom d) (v : V) : Mom d :=
  c v+if r.vertex 5 = v then (appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val : ℤ) •
    appbS33SideCutMomentum r c else 0

noncomputable def appbS33SideDirectedMomentum {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) {d : ℕ} (L : ℝ) (w : Mom d)
    (c : V → Mom d) (κ : D → (Fin d → ℤ)) : V → Mom d :=
  if M.atom (r.edge ⟨1,by decide⟩).val = r.vertex 3 then
    appbAddedMomentum (r.vertex 3) (r.vertex 5) L w (κ (r.edge ⟨1,by decide⟩).val)
      (Degen.residualMomentum M r.removedAtoms L w c κ)
  else appbAddedMomentum (r.vertex 5) (r.vertex 3) L w (κ (r.edge ⟨1,by decide⟩).val)
      (Degen.residualMomentum M r.removedAtoms L w c κ)

theorem appb_s33_side_directed_momentum_eq {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    {d : ℕ} (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) {v : V} (hv : v ∈ appbS33Side r) :
    appbS33SideDirectedMomentum r L w c κ v = appbS33SideReinsertMomentum r c v := by
  have ht := appb_s33_splitTopology_of_geometry hg
  have hR : Molecule.kvec L w κ (r.edge ⟨1,by decide⟩).val-
      Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val = appbS33SideCutMomentum r c :=
    (appbS33TopologyCutPair r ht).momentum_difference
      ((appb_s33_topology_first_signs_iff M r ht).mpr hg.2.2.2.1) L w c κ hκ
  have hsign := appb_s33_external_signs_opposite r hg.2.2.2.1
  by_cases ha : M.atom (r.edge ⟨1,by decide⟩).val = r.vertex 3
  · have hs3 : appbIncidenceSign M (r.vertex 3) (r.edge ⟨1,by decide⟩).val = 1 := by simp [appbIncidenceSign,ha]
    have hs5 : appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val = -1 := by
      rw [appb_units_eq_neg_of_ne _ _ hsign,hs3]
    unfold appbS33SideDirectedMomentum
    rw [if_pos ha]
    unfold appbAddedMomentum appbS33SideReinsertMomentum
    rw [appb_s33_side_residual_momentum r ht L w c κ hκ.1 hv,← hR,hs3,hs5]
    by_cases hA : r.vertex 3 = v <;> by_cases hB : r.vertex 5 = v
    all_goals simp only [hA,hB,ite_true,ite_false,Units.val_one,Units.val_neg,one_smul,neg_smul]
    all_goals try dsimp only [Molecule.kvec]
    all_goals abel
  · have hs3 : appbIncidenceSign M (r.vertex 3) (r.edge ⟨1,by decide⟩).val = -1 := by simp [appbIncidenceSign,ha]
    have hs5 : appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val = 1 := by
      rw [appb_units_eq_neg_of_ne _ _ hsign,hs3,neg_neg]
    unfold appbS33SideDirectedMomentum
    rw [if_neg ha]
    unfold appbAddedMomentum appbS33SideReinsertMomentum
    rw [appb_s33_side_residual_momentum r ht L w c κ hκ.1 hv,← hR,hs3,hs5]
    by_cases hA : r.vertex 3 = v <;> by_cases hB : r.vertex 5 = v
    all_goals simp only [hA,hB,ite_true,ite_false,Units.val_one,Units.val_neg,one_smul,neg_smul]
    all_goals try dsimp only [Molecule.kvec]
    all_goals abel

end WaveTurbulence.Mole
