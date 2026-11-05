/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalErrorUniform
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ErrorGeometricEstimate
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalErrorScalar

/-! # Original couple kernel remainder, uniformly over every code and logarithmic order -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ClassJR ApproxNT WaveTurbulence.Fourier

/-- The original positive-order couple kernel satisfies the required full
mixed restriction estimate, with a constant before the order exponent and
a large-lattice threshold before every input and couple code. -/
theorem exists_couple_kernel_remainder_bound {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ)
    {Binput : ℝ} (hBi : 0 ≤ Binput) :
    ∃ Cerror : ℝ, 1 ≤ Cerror ∧
      ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ F : Mom d → ℝ, spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal Binput →
      ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder →
      ∀ Q : RegCpl, Q.wf = true → Q.size = 2*n →
      ∀ (LG : LayeredGarden 2) (_hQ : Q.Decodes LG.garden), (∀ a, LG.layer a = 0) →
      ∀ T : Set (Fin 2 → ℝ), (∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1) →
      mixedRestrictionNorm η (30*d) (30*d) T Set.univ
        (fun t k => KQstar L γ δ (fun _ => F) LG (t.val 0) (t.val 1) k.val-Q.app δ 0 F (t.val 0) (t.val 1) k.val) ≤
        ENNReal.ofReal (Cerror*(Cerror*δ)^n*L^(-gamma1 d γ+2*η)) := by
  classical
  obtain ⟨Ccover,hCc,hCover⟩ := actual_couple_uniform_cell_cover d (by omega)
  obtain ⟨Cerror,hCe,hNorm⟩ := exists_geometric_physical_error_bound hd hγ hη0 hη hηγ hηγ'
    A1_nonneg (one_le_C0 (1-η/8) (η/4) (1-η/2))
    (by omega : d+2+30*d ≤ 40*d) (by omega : 30*d+2*d ≤ 40*d) hBi hCc.le
  refine ⟨Cerror,hCe,?_⟩
  intro Aorder
  obtain ⟨Ln,hNorm⟩ := hNorm Aorder
  obtain ⟨Le,hError⟩ := couple_physical_error_profiles_uniform hd hγ hη0 hη hηγ hηγ' A1_nonneg le_rfl Aorder
  obtain ⟨Lr,hjoint⟩ := source_remainders_joint_integrable hd hγ hη0 hη hηγ hηγ' A1 A1_nonneg Aorder
  refine ⟨max Ln (max Le Lr),?_⟩
  intro L hL δ hδ hδ1 F hF n hn hnlog Q hwf hsize LG hQ h0 T hT
  have hLn : Ln ≤ L := (le_max_left _ _).trans hL
  have hLe : Le ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLr : Lr ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hlinks : Q.links.length = n := links_length_eq_half hsize
  have hlinkspos : 0 < Q.links.length := by omega
  have hlinkslog : (Q.links.length:ℝ) ≤ Real.log L^Aorder := by simpa only [hlinks] using hnlog
  obtain ⟨C,hC,_hclass,hError⟩ := hError Q hwf
  choose S hcard hcover using hCover LG.garden Q hQ hQ.1
  have hC' (Z : (chosenSet Q.links).powerset) :
      SRep (1-η/8) (η/4) (1-η/2) A1
        (C0 (1-η/8) (η/4) (1-η/2)^(4*Q.links.length+1)) (C Z) := by
    have he : 2*Q.size+1 = 4*Q.links.length+1 := by omega
    simpa only [he] using hC Z
  have hi (k : Mom d) (Z : (chosenSet Q.links).powerset) :=
    hjoint L hLr (2*δ) hδ hδ1 LG.garden Q hQ hQ.1 hlinkspos hlinkslog
      (markedLinkIndices Q Z.val) (C Z) _ (hC Z) (40*d) (40*d) (by omega) (by omega)
      Binput Ccover hBi (fun k => (F k:ℂ)) hF S hcard k
  have hfun : (fun t : T => fun k : (Set.univ : Set (Mom d)) =>
      KQstar L γ δ (fun _ => F) LG (t.val 0) (t.val 1) k.val-Q.app δ 0 F (t.val 0) (t.val 1) k.val) =
      (fun t : T => fun k : (Set.univ : Set (Mom d)) =>
        sourceScalarProfile hQ hQ.1 (physicalErrorScalar L δ γ Q LG.garden.zeta C)
          (fun k => (F k:ℂ)) S t.val k.val) := by
    funext t k
    have he := hError L hLe δ hδ hδ1 Binput Ccover hBi F hF LG h0 hQ hlinkspos hlinkslog
      S hcard hcover (t.val 0) (hT t.val t.property 0) (t.val 1) (hT t.val t.property 1) k.val
    have hp := physicalErrorScalar_profile_of_joint_integrable hQ hQ.1 L δ γ LG.garden.zeta C
      (fun k => (F k:ℂ)) S k.val (hi k.val) t.val
    have ht : ![t.val 0,t.val 1] = t.val := by
      funext i
      fin_cases i <;> rfl
    simpa only [ht] using he.trans hp.symm
  rw [hfun]
  simpa only [hlinks] using hNorm L hLn δ hδ hδ1 LG.garden Q hQ hQ.1 hlinkspos hlinkslog C hC'
    LG.garden.zeta (norm_garden_zeta LG.garden).le (fun k => (F k:ℂ)) hF S hcard T hT

end WaveTurbulence.RegAsymp
