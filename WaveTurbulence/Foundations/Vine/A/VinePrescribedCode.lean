/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineCoarseWordBatch
public import WaveTurbulence.Foundations.Vine.A.VineTauGardenFibres
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

/-- Every member of the actual fine output set has its uniquely coded prescription. -/
theorem output_point {a : PrescribedPrimeGarden w} {LG : LayeredGarden w}
    (h : LG ∈ a.outputs (p := p) (kind := kind)) :
    ∃ b : PrescribedPrimeGarden w, b.layered = LG ∧ a.code = b.code ∧ a.outputs (p := p) (kind := kind) = b.outputs (p := p) (kind := kind) := by
  obtain ⟨b, hb, hL⟩ := (Set.ext_iff.mp (tauClass_image a) LG).mpr h
  exact ⟨b, hL, Related.code_eq hb, Related.outputs_eq hb⟩

/-- Actual coarse transport supplies a prescription over every coarse-class garden. -/
theorem coarse_point {a : PrescribedPrimeGarden w} {LG : LayeredGarden w}
    (h : LG ∈ a.prime.coarseState.allCoreOutputs (p := p) (kind := kind)) :
    ∃ b : PrescribedPrimeGarden w, b.layered = LG ∧ a.code = b.code := by
  obtain ⟨B, ⟨L, _, hb⟩, he⟩ := (congruent_layered_iff p kind a.prime.coarseState LG).mp h
  refine ⟨ofState B (batch_prime hb a.prime.prime) (transportGroupPrescription (batchMolIso hb) a.sigma), he, ?_⟩
  exact ((batchMolIso_spec hb).codedPrescription a.prime.coarseState_isVFamily a.sigma).symm

/-- Coarse return paths recover precisely the starting prescribed point. -/
theorem coarse_return {a : PrescribedPrimeGarden w}
    {L : List (CoreIndex (vinesV a.prime.skeleton))}
    {B : FamilyReconstruction w (CoreIndex (vinesV a.prime.skeleton))}
    (hb : FamilyBatch p kind L a.prime.coarseState B) (hL : B.layered = a.layered) :
    ofState B (batch_prime hb a.prime.prime) (transportGroupPrescription (batchMolIso hb) a.sigma) = a := by
  apply eq_of_layered_code hL
  exact (batchMolIso_spec hb).codedPrescription a.prime.coarseState_isVFamily a.sigma

/-- Any two actual coarse paths to the same garden give the same full local prescription. -/
theorem coarse_path_independent {a : PrescribedPrimeGarden w}
    {L K : List (CoreIndex (vinesV a.prime.skeleton))}
    {B C : FamilyReconstruction w (CoreIndex (vinesV a.prime.skeleton))}
    (hb : FamilyBatch p kind L a.prime.coarseState B) (hc : FamilyBatch p kind K a.prime.coarseState C)
    (hL : B.layered = C.layered) :
    ofState B (batch_prime hb a.prime.prime) (transportGroupPrescription (batchMolIso hb) a.sigma) =
      ofState C (batch_prime hc a.prime.prime) (transportGroupPrescription (batchMolIso hc) a.sigma) := by
  apply eq_of_layered_code hL
  exact ((batchMolIso_spec hb).codedPrescription a.prime.coarseState_isVFamily a.sigma).trans
    ((batchMolIso_spec hc).codedPrescription a.prime.coarseState_isVFamily a.sigma).symm

end WaveTurbulence.VineA.PrescribedPrimeGarden
