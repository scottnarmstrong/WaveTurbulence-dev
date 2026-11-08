/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceKernelData
import Mathlib.MeasureTheory.Integral.Pi
/-! Transport of the literal spliced time integral by finite pi-volume
reindexing, using the proved actual domain and signed-phase identities. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open MeasureTheory WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LGSpine
variable {w d : ℕ} {G : Garden w}

/-- Reindexing finitely many real coordinates preserves their full product volume integral. -/
theorem integral_pi_volume_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : (κ → ℝ) → ℂ) :
    (∫ t : ι → ℝ, f (fun j => t (e.symm j))) = ∫ t : κ → ℝ, f t := by
  have he (t : ι → ℝ) : (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e) t = (fun j => t (e.symm j)) := by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    rw [MeasurableEquiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]
  simpa only [he] using
    (volume_measurePreserving_piCongrLeft (fun _ : κ => ℝ) e).integral_comp' f

/-- B1b-2 (Mk-general form of `unitSplice_splicedTimeIntegral`). -/
theorem unitSplice_splicedTimeIntegralMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (D : SplicedKernelData (stSt G σ Mk).G d)
    (L γ δ : ℝ) (base : Mom d)
    (z : GNode (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree → (Fin d → ℤ)) :
    splicedTimeIntegral (stSt G σ Mk).G D L γ δ base (z ∘ unitSpliceNodeEquivMk Z σ hT hsel) =
      splicedTimeIntegral (stSt Z.target (transportPrescription Z.iso σ) Mk').G
        (mapSplicedKernelData (unitSpliceMolIsoMk Z σ hT hsel) D) L γ δ base z := by
  classical
  let F := unitSpliceMolIsoMk Z σ hT hsel
  let DT := mapSplicedKernelData F D
  let f : (GBranch (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree → ℝ) → ℂ :=
    (splicedTimeDomain (stSt Z.target (transportPrescription Z.iso σ) Mk').G DT.layer DT.rootTime).indicator
      (fun t => phaseProd L γ δ (stSt Z.target (transportPrescription Z.iso σ) Mk').G
        (cosetDecoration (stSt Z.target (transportPrescription Z.iso σ) Mk').G L base z) t *
        ∏ b : GBranch (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree,
          Complex.exp ((Real.pi * DT.frequency b * t b : ℝ) * Complex.I))
  unfold splicedTimeIntegral
  change _ = ∫ t, f t
  trans ∫ t : GBranch (stSt G σ Mk).G.tree → ℝ, f (fun b => t (F.e.symm b))
  · apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [f]
    by_cases ht : t ∈ splicedTimeDomain (stSt G σ Mk).G D.layer D.rootTime
    · have ht' : (fun b => t (F.e.symm b)) ∈
          splicedTimeDomain (stSt Z.target (transportPrescription Z.iso σ) Mk').G DT.layer DT.rootTime :=
        (unitSplice_timeDomain_iffMk Z σ hT hsel D.layer D.rootTime t).mpr ht
      rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht']
      apply congrArg₂ (fun a b : ℂ => a * b)
      · change phaseProd L γ δ (stSt G σ Mk).G
          ((cosetDecoration (stSt Z.target (transportPrescription Z.iso σ) Mk').G L base z) ∘ unitSpliceNodeEquivMk Z σ hT hsel) t = _
        simpa only [F, Function.comp_def, Equiv.symm_apply_apply] using
          unitSplice_phaseProdMk Z σ hT hsel L γ δ
            (cosetDecoration (stSt Z.target (transportPrescription Z.iso σ) Mk').G L base z)
            (fun b => t (F.e.symm b))
      · exact (F.e.symm.prod_comp
          (fun b : GBranch (stSt G σ Mk).G.tree => Complex.exp ((Real.pi * D.frequency b * t b : ℝ) * Complex.I))).symm
    · have ht' : (fun b => t (F.e.symm b)) ∉
          splicedTimeDomain (stSt Z.target (transportPrescription Z.iso σ) Mk').G DT.layer DT.rootTime :=
        fun h => ht ((unitSplice_timeDomain_iffMk Z σ hT hsel D.layer D.rootTime t).mp h)
      rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']
  · exact integral_pi_volume_reindex F.e f

/-- The actual selected-splice time integral agrees for transported actual kernel data. -/
theorem unitSplice_splicedTimeIntegral (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (D : SplicedKernelData (stSt G σ).G d)
    (L γ δ : ℝ) (base : Mom d)
    (z : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → (Fin d → ℤ)) :
    splicedTimeIntegral (stSt G σ).G D L γ δ base (z ∘ unitSpliceNodeEquiv Z σ hsel) =
      splicedTimeIntegral (stSt Z.target (transportPrescription Z.iso σ)).G
        (mapSplicedKernelData (unitSpliceMolIso Z σ hsel) D) L γ δ base z :=
  unitSplice_splicedTimeIntegralMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel D L γ δ base z

end WaveTurbulence.VineA
