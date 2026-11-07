/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD33ResidualParameters
public import WaveTurbulence.Foundations.FinalCount.AppBEndpointSigns
public import WaveTurbulence.Foundations.FinalCount.AppBCutPairDifference
public import WaveTurbulence.Foundations.FinalCount.AppBAddedBondDecorations
import Mathlib.Tactic

/-! # Fixed momentum sources for the actual double-pair reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbD33CutMomentum {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) {d : ℕ} (c : V → Mom d) : Mom d :=
  (((appbCutSign M r.removedAtoms (r.edge ⟨2,by decide⟩).val)⁻¹ : ℤˣ) : ℤ) •
    (∑ v ∈ r.removedAtoms,c v)

noncomputable def appbD33ReinsertMomentum {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) {d : ℕ} (c : V → Mom d) (v : V) : Mom d :=
  c v+if r.vertex 4 = v then (appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val : ℤ) •
    appbD33CutMomentum r c else 0

/-- Both orientations give the same explicitly prescribed source formula.
It depends only on the old source parameters, not on the internal pair
or the copied boundary label. -/
theorem appb_d33_reinsert_isDecoration {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) (hOpp : AppbD33BoundaryOpposite M r)
    {d : ℕ} (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) :
    (r.directedPostWithBond 3 4 ⟨2,by decide⟩).IsDecoration L w (appbD33ReinsertMomentum r c)
      (r.reinsertedLabels κ ⟨2,by decide⟩) := by
  have h3 := r.vertex_mem_post 3 (by decide) (by decide)
  have h4 := r.vertex_mem_post 4 (by decide) (by decide)
  have hR : Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
      Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val = appbD33CutMomentum r c :=
    (appbD33CutPair r).momentum_difference (appb_d33_cut_signs_opposite M r hOpp) L w c κ hκ
  have hsign := appb_d33_external_signs_opposite r hOpp
  have hres := Degen.isDecoration_eraseAtoms M r.removedAtoms hκ
  by_cases ha : M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 3
  · have hs3 : appbIncidenceSign M (r.vertex 3) (r.edge ⟨2,by decide⟩).val = 1 := by
      simp [appbIncidenceSign,ha]
    have hs4 : appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val = -1 := by
      rw [appb_units_eq_neg_of_ne _ _ hsign,hs3]
    rw [AppbRealization.directedPostWithBond,if_pos ha]
    have hm := appb_isDecoration_addBond r.post (r.vertex 3) (r.vertex 4) h3 h4
      (κ (r.edge ⟨2,by decide⟩).val) hres
    refine ⟨hm.1,?_⟩
    intro v hv
    have hvret : v ∈ r.post.atoms := by
      change v ∈ insert (r.vertex 3) (insert (r.vertex 4) r.post.atoms) at hv
      simpa only [insert_eq_of_mem h4,insert_eq_of_mem h3] using hv
    have hc : appbAddedMomentum (r.vertex 3) (r.vertex 4) L w (κ (r.edge ⟨2,by decide⟩).val)
        (Degen.residualMomentum M r.removedAtoms L w c κ) v = appbD33ReinsertMomentum r c v := by
      unfold appbAddedMomentum appbD33ReinsertMomentum
      rw [appb_d33_residual_momentum r L w c κ hκ.1 (mem_sdiff.mp hvret).2,← hR,hs3,hs4]
      by_cases hA : r.vertex 3 = v <;> by_cases hB : r.vertex 4 = v
      all_goals simp only [hA,hB,ite_true,ite_false,Units.val_one,Units.val_neg,one_smul,neg_smul]
      all_goals try dsimp only [Molecule.kvec]
      all_goals abel
    exact (hm.2 v hv).trans hc
  · have hs3 : appbIncidenceSign M (r.vertex 3) (r.edge ⟨2,by decide⟩).val = -1 := by
      simp [appbIncidenceSign,ha]
    have hs4 : appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val = 1 := by
      rw [appb_units_eq_neg_of_ne _ _ hsign,hs3,neg_neg]
    rw [AppbRealization.directedPostWithBond,if_neg ha]
    have hm := appb_isDecoration_addBond r.post (r.vertex 4) (r.vertex 3) h4 h3
      (κ (r.edge ⟨2,by decide⟩).val) hres
    refine ⟨hm.1,?_⟩
    intro v hv
    have hvret : v ∈ r.post.atoms := by
      change v ∈ insert (r.vertex 4) (insert (r.vertex 3) r.post.atoms) at hv
      simpa only [insert_eq_of_mem h3,insert_eq_of_mem h4] using hv
    have hc : appbAddedMomentum (r.vertex 4) (r.vertex 3) L w (κ (r.edge ⟨2,by decide⟩).val)
        (Degen.residualMomentum M r.removedAtoms L w c κ) v = appbD33ReinsertMomentum r c v := by
      unfold appbAddedMomentum appbD33ReinsertMomentum
      rw [appb_d33_residual_momentum r L w c κ hκ.1 (mem_sdiff.mp hvret).2,← hR,hs3,hs4]
      by_cases hA : r.vertex 3 = v <;> by_cases hB : r.vertex 4 = v
      all_goals simp only [hA,hB,ite_true,ite_false,Units.val_one,Units.val_neg,one_smul,neg_smul]
      all_goals try dsimp only [Molecule.kvec]
      all_goals abel
    exact (hm.2 v hv).trans hc

end WaveTurbulence.Mole
