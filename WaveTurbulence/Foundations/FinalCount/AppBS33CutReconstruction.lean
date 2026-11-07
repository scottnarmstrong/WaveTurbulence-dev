/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33ResidualSide
public import WaveTurbulence.Foundations.FinalCount.AppBCutPair
public import WaveTurbulence.Foundations.FinalCount.AppBEdgeCutTables
public import WaveTurbulence.Foundations.FinalCount.AppBTB2Reconstruction
import Mathlib.Tactic

/-! # Exact local-label reconstruction in the split 3S3 geometry -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbS33CutPair {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hgeom : AppbS33SplitGeometry M r) :
    AppbCutPair r (appbS33Side r) where
  subset_atoms := by
    intro a ha
    exact ((Degen.mem_residualComponent M r.removedAtoms (r.vertex 3) a).mp ha).1
  crossing := r.residual_cut_crossing (r.vertex 3)
  first := ⟨1,by decide⟩
  second := ⟨3,by decide⟩
  distinct := by decide
  first_cross := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_s33_side_labels M r hgeom
    apply (r.edge_cut_cross_iff (appbS33Side r) ⟨1,by decide⟩).mpr
    change ((r.vertex 1 ∈ appbS33Side r ∧ r.vertex 3 ∉ appbS33Side r) ∨
      (r.vertex 1 ∉ appbS33Side r ∧ r.vertex 3 ∈ appbS33Side r))
    simp [h1,h3]
  second_cross := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_s33_side_labels M r hgeom
    apply (r.edge_cut_cross_iff (appbS33Side r) ⟨3,by decide⟩).mpr
    change ((r.vertex 2 ∈ appbS33Side r ∧ r.vertex 5 ∉ appbS33Side r) ∨
      (r.vertex 2 ∉ appbS33Side r ∧ r.vertex 5 ∈ appbS33Side r))
    simp [h2,h5]
  other := by
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_s33_side_labels M r hgeom
    intro i hi1 hi3
    fin_cases i
    · apply (r.edge_cut_same_iff (appbS33Side r) ⟨0,by decide⟩).mpr
      change (r.vertex 1 ∈ appbS33Side r ↔ r.vertex 2 ∈ appbS33Side r)
      simp only [h1,h2]
    · exact False.elim (hi1 rfl)
    · apply (r.edge_cut_same_iff (appbS33Side r) ⟨2,by decide⟩).mpr
      change (r.vertex 1 ∈ appbS33Side r ↔ r.vertex 4 ∈ appbS33Side r)
      simp only [h1,h4]
    · exact False.elim (hi3 rfl)
    · apply (r.edge_cut_same_iff (appbS33Side r) ⟨4,by decide⟩).mpr
      change (r.vertex 2 ∈ appbS33Side r ↔ r.vertex 6 ∈ appbS33Side r)
      simp only [h2,h6]

def appbS33Frame {M : Molecule V D} (r : AppbRealization M AppbPatternKind.s33.pattern) :
    AppbTripleFrame r (r.vertex 1) where
  index := appbFirstThreeEmbedding _ (by decide)
  incidence := by
    intro j
    rw [r.edge_incidence _ 1 (by decide)]
    fin_cases j <;> decide
  other := by
    intro i hi
    rw [r.edge_incidence i 1 (by decide)]
    fin_cases i
    · exact False.elim (hi 0 rfl)
    · exact False.elim (hi 1 rfl)
    · exact False.elim (hi 2 rfl)
    · decide
    · decide

/-- The cut is computed from the actual residual graph, not assumed as
a fixed-label premise. Its conservation equation reconstructs label 4;
conservation at vertex 2 then reconstructs label 5. -/
theorem appb_s33_split_projection_injective {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hgeom : AppbS33SplitGeometry M r)
    {d : ℕ} (p : AppbCountParameters M d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    Set.InjOn ((appbS33Frame r).project (K := Fin d → ℤ)) (r.localChoices p hL γ δ w Adm : Set _) := by
  intro q hq q' hq' he
  obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hL γ δ w Adm q).mp hq
  obtain ⟨κ',hκ',rfl⟩ := (r.mem_localChoices p hL γ δ w Adm q').mp hq'
  have h0 := congrFun he (0 : Fin 3)
  have h1 := congrFun he (1 : Fin 3)
  have h2 := congrFun he (2 : Fin 3)
  have h3 := (appbS33CutPair r hgeom).second_label_eq hL.ne' w p.momentum κ κ' hκ.1 hκ'.1 h1
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · apply r.local_label_eq_of_others hL.ne'
      (mem_image_of_mem _ (show 2 ∈ AppbPatternKind.s33.pattern.removed by decide)) ⟨4,by decide⟩
      (by rw [r.edge_incidence _ 2 (by decide)]; decide) w p.momentum κ κ' hκ.1 hκ'.1
    intro j hj
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact False.elim (hj rfl)

end WaveTurbulence.Mole
