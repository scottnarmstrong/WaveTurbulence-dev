/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineCoarseWordBatch
public import WaveTurbulence.Foundations.Vine.A.VinePrescribedPartition
/-! Path-independent local prescriptions on actual plain gardens. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA.PrescribedPrimeGarden
open Stage1 RedSplice LFTwist Represents
variable {w p : ℕ} {kind : Bool}

/-- The full color graph on qG[S], encoded by literal normalized addresses. -/
def code (a : PrescribedPrimeGarden w) := codedPrescription a.prime.skeleton a.sigma

/-- At a fixed actual garden, the code recovers every local prescription. -/
theorem eq_of_layered_code {a b : PrescribedPrimeGarden w} (hL : a.layered = b.layered)
    (hc : a.code = b.code) : a = b := by
  rcases a with ⟨LG, A, σ⟩
  rcases b with ⟨LH, B, τ⟩
  change LG = LH at hL
  subst LH
  have hA := primeData_unique A B
  subst B
  have hs : σ = τ := codedPrescription_injective A.skeleton hc
  subst τ
  rfl

/-- Actual fine batch edges preserve the whole color graph. -/
theorem BatchReach.code_eq {a b : PrescribedPrimeGarden w}
    (h : BatchReach (p := p) (kind := kind) a b) : a.code = b.code := by
  obtain ⟨L, B, hb, _, rfl⟩ := h
  exact (codedPrescription_map (batchMolIso hb)
    ((batchMolIso_spec hb).fine_coarseAtomWord a.totalSigma (fineState_isV0Fam a.prime a.totalSigma)) a.sigma).symm

/-- Every fine trace, reversal and concatenation preserves the same fixed sigma. -/
theorem Related.code_eq {a b : PrescribedPrimeGarden w}
    (h : Related (p := p) (kind := kind) a b) : a.code = b.code := by
  induction h with
  | rel _ _ h => exact h.code_eq
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact ih.trans hj

end WaveTurbulence.VineA.PrescribedPrimeGarden
