/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeLoneParent

/-! # The original external tree time cuts, with only null boundaries changed -/

public section
noncomputable section
open MeasureTheory Set
namespace WaveTurbulence.IncohInst
open Incoh

@[expose] def TreeClockSelection.rootBranch {G : Garden 1} {X : RegChain}
    {hX : X.DecodesTree G} (C : TreeClockSelection hX) : GBranch G.tree :=
  treeLinkEquiv hX (C.selection.coordinates.rootVertex 0)

theorem TreeClockSelection.branchRoot_eq {G : Garden 1} {X : RegChain}
    {hX : X.DecodesTree G} (C : TreeClockSelection hX) (b : GBranch G.tree) :
    branchRoot b = C.rootBranch := by
  apply Subtype.ext
  rw [show C.rootBranch.val = (0, []) from C.first_eq]
  exact Prod.ext (Subsingleton.elim _ _) rfl

/-- Only the null root and lone-parent external hyperplanes change in the literal source domain. -/
theorem tree_kDomain_ae_extremeCut (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden) (C : TreeClockSelection hX) (ts : Fin 2 → ℝ) :
    kDomain LG (fun _ => ts 0) (ts 1) =ᵐ[volume]
      internalTimeDomain LG ∩ {τ | ts 1 ≤ τ C.parentBranch ∧
        τ C.parentBranch ≤ τ C.rootBranch ∧ τ C.rootBranch ≤ ts 0} := by
  have hn₀ := Measure.ae_eval_ne
    (fun _ : GBranch LG.garden.tree => (volume : Measure ℝ)) C.rootBranch (ts 0)
  have hn₁ := Measure.ae_eval_ne
    (fun _ : GBranch LG.garden.tree => (volume : Measure ℝ)) C.parentBranch (ts 1)
  filter_upwards [hn₀, hn₁] with τ hn₀ hn₁
  apply propext
  rw [mem_kDomain_iff]
  constructor
  · rintro ⟨hi, hu, hl⟩
    have hpar := branch_time_le_root τ (fun a b he => (hi a).2.2.2 b he) C.parentBranch
    rw [C.branchRoot_eq] at hpar
    exact ⟨hi, (hl C.parentBranch ((C.isLoneParent_iff _).mpr rfl)).le,
      hpar, (hu C.rootBranch).le⟩
  · rintro ⟨hi, hs, _, ht⟩
    refine ⟨hi, ?_, ?_⟩
    · intro b
      have hb := branch_time_le_root τ (fun a b he => (hi a).2.2.2 b he) b
      rw [C.branchRoot_eq] at hb
      exact hb.trans_lt (lt_of_le_of_ne ht hn₀)
    · intro b hb
      rw [(C.isLoneParent_iff b).mp hb]
      exact lt_of_le_of_ne hs (Ne.symm hn₁)

end WaveTurbulence.IncohInst
