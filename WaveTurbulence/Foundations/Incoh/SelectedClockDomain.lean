/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeClockFibers
public import WaveTurbulence.Foundations.Incoh.CausalKernelSource
public import WaveTurbulence.Foundations.Incoh.RootCausalSource

/-!
# The selected tree clock domain and its external causal constraints

The external root and lone-parent clocks are the first and last selected
vertices. Their triangle constraints give precisely the ordered simplex.
-/

public section
noncomputable section
open Set

namespace WaveTurbulence.Incoh

/-- On a strictly descending fiber, the external constraints only concern its extreme clocks. -/
theorem mem_orderedClockDomain_iff_extremes {m : ℕ} {v : Fin (m + 2) → ℝ}
    (hv : ∀ j : Fin (m + 1), v j.succ < v j.castSucc) (t s : ℝ) :
    v ∈ orderedClockDomain (m + 2) t s ↔ s ≤ v (Fin.last (m + 1)) ∧ v 0 ≤ t := by
  have ha : Antitone v := (Fin.strictAnti_iff_succ_lt.mpr hv).antitone
  constructor
  · intro h
    exact ⟨(h.1 (Fin.last (m + 1))).1, (h.1 0).2⟩
  · intro h
    exact ⟨fun j => ⟨h.1.trans (ha (Fin.le_last j)), (ha (Fin.zero_le j)).trans h.2⟩, ha⟩

/-- A selected root coordinate reads exactly its original vertex clock. -/
theorem RootCoordinates.equiv_fst_apply {n r : ℕ} (R : RootCoordinates n r)
    (t : Fin n → Fin 2 → ℝ) (a : Fin r) :
    (R.equiv t).1 a = t (R.rootVertex a).1 (R.rootVertex a).2 := by
  have h := R.equiv_symm_rootVertex (R.equiv t).1 (R.equiv t).2 a
  simpa only [Prod.eta, MeasurableEquiv.symm_apply_apply] using h.symm

/-- The source time domain has exactly the declared selected-clock fibers. -/
theorem TreeClockFibers.mem_timeDomain_equiv_symm {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (v : Fin (m + 2) → ℝ)
    (u : Fin T.selection.coordinates.restCount → ℝ) :
    T.selection.coordinates.equiv.symm (v, u) ∈ T.timeDomain ↔
      u ∈ T.remainingDomain ∧ v ∈ causalIntervalFiber m (T.lower u) (T.upper u) := by
  simp only [TreeClockFibers.timeDomain, causalIntervalFiber, mem_ofPred_eq,
    MeasurableEquiv.apply_symm_apply]

/-- Both source tree cases have the same exact causal-domain decomposition. -/
theorem TreeClockFibers.mem_causalDomain_equiv_symm {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (R : RootCoordinates n)
    (hfirst : R.rootVertex 0 = T.selection.coordinates.rootVertex 0)
    (hlast : R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (m + 1)))
    (v : Fin (m + 2) → ℝ) (u : Fin T.selection.coordinates.restCount → ℝ) (t : Fin 2 → ℝ) :
    T.selection.coordinates.equiv.symm (v, u) ∈ T.timeDomain ∩ R.causalRootCut t ↔
      u ∈ T.remainingDomain ∧
        v ∈ orderedClockDomain (m + 2) (t 0) (t 1) ∩ causalIntervalFiber m (T.lower u) (T.upper u) := by
  have h0 : (R.equiv (T.selection.coordinates.equiv.symm (v, u))).1 0 = v 0 := by
    rw [R.equiv_fst_apply, hfirst, T.selection.coordinates.equiv_symm_rootVertex]
  have h1 : (R.equiv (T.selection.coordinates.equiv.symm (v, u))).1 1 = v (Fin.last (m + 1)) := by
    rw [R.equiv_fst_apply, hlast, T.selection.coordinates.equiv_symm_rootVertex]
  rw [mem_inter_iff, T.mem_timeDomain_equiv_symm]
  simp only [RootCoordinates.causalRootCut, mem_preimage, mem_prod, mem_univ, and_true,
    causalTriangle, mem_ofPred_eq]

  rw [h0, h1]
  constructor
  · rintro ⟨⟨hu, hv⟩, hs, _, ht⟩
    exact ⟨hu, (mem_orderedClockDomain_iff_extremes hv.2 _ _).mpr ⟨hs, ht⟩, hv⟩
  · rintro ⟨hu, hord, hv⟩
    have he := (mem_orderedClockDomain_iff_extremes hv.2 _ _).mp hord
    exact ⟨⟨hu, hv⟩, he.1, hord.2 (Fin.zero_le _), he.2⟩

end WaveTurbulence.Incoh
