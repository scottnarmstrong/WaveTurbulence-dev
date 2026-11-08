/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleEnvelope
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoupleCellCover

/-! # FILT-COH: layer-zero regular couples at an arbitrary time weight (bound only)

o82 Lemma 16.1 (coherent case, "the strong coefficient weight `1-η/8 > 1/4` and Theorem 10.1 give a uniform
bound in that stronger norm; no small error estimate is needed"), for a layer-zero regular couple with
separately normalized leaf profiles: main's exact global identity
(`RA1Leafwise.couple_physical_global_profiles_uniform`), the weight-`θ` envelope of `CoupleEnvelope`, and main's
weight-generic assembly `RA1Leafwise.leafScalar_profile_of_local_envelope`. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh
open scoped ENNReal

variable {d : ℕ}

/-- **Layer-zero couple kernels in `X^{θ,30d,30d}`, `0 ≤ θ ≤ 1 - η/8`**, for leaf profiles of `𝔖^{40d,40d}` size at
most `Binput`, positive polylogarithmic order: the bound `Ck (Ck δ)^n`, with no `L` loss. -/
theorem exists_couple_kernel_bound_theta (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1-η/8) {Binput : ℝ} (hBi : 0 ≤ Binput) :
    ∃ Ck : ℝ, 1 ≤ Ck ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder →
      ∀ Q : RegCpl, Q.wf = true → Q.size = 2*n →
      ∀ (LG : LayeredGarden 2) (_hQ : Q.Decodes LG.garden), (∀ a, LG.layer a = 0) →
      ∀ H : LGSpine.LeafProfiles 2 d,
      (∀ z, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.addrFam H z) ≤ ENNReal.ofReal Binput) →
      ∀ T : Set (Fin 2 → ℝ), (∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1) →
      Fourier.mixedRestrictionNorm θ (30*d) (30*d) T Set.univ
        (fun t k => LGSpine.coupleLeaves L γ δ LG H (t.val 0) (t.val 1) k.val) ≤
        ENNReal.ofReal (Ck*(Ck*δ)^n) := by
  classical
  obtain ⟨Ccover,hCc,hCover⟩ := actual_couple_uniform_cell_cover d (by omega)
  obtain ⟨Kr,Cm,hKr,hCm,henv⟩ := physical_scalar_envelope_theta hd hγ hη0 hη hηγ hηγ' hθ0 hθ
    A1_nonneg (one_le_C0 (1-η/8) (η/4) (1-η/2))
  obtain ⟨Ck,hCk,hbudget⟩ := RA1Leafwise.exists_common_physical_error_constant d (30*d) (30*d) (40*d) θ
    hKr.le (zero_le_one.trans hCm) hCc.le hBi
  refine ⟨Ck,hCk,?_⟩
  intro Aorder
  obtain ⟨Le,henv⟩ := henv Aorder
  obtain ⟨Lg,hglobal⟩ := RA1Leafwise.couple_physical_global_profiles_uniform hd hγ hη0 hη hηγ hηγ'
    A1_nonneg le_rfl Aorder
  obtain ⟨Lj,hjoint⟩ := RA1Leafwise.source_physical_symbol_joint_integrable hd hγ hη0 hη hηγ hηγ'
    A1 A1_nonneg Aorder
  refine ⟨max 2 (max Le (max Lg Lj)),?_⟩
  intro L hL δ hδ hδ1 n hn hnlog Q hwf hsize LG hQ h0 H hF T hT
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLe : Le ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLg : Lg ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLj : Lj ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLpos : 0 < L := by linarith
  have hδpos : 0 < δ := by
    have hh := (Real.rpow_pos_of_pos hLpos (-(η/2))).trans_le hδ
    linarith only [hh]
  have hlinks : Q.links.length = n := links_length_eq_half hsize
  have hlinkspos : 0 < Q.links.length := by omega
  have hlinkslog : (Q.links.length:ℝ) ≤ Real.log L^Aorder := by simpa only [hlinks] using hnlog
  obtain ⟨C,hC,_hclass,hid⟩ := hglobal Q hwf
  choose S hcard hcover using hCover LG.garden Q hQ hQ.1
  have hC' (Z : (chosenSet Q.links).powerset) :
      SRep (1-η/8) (η/4) (1-η/2) A1
        (C0 (1-η/8) (η/4) (1-η/2)^(4*Q.links.length+1)) (C Z) := by
    have he : 2*Q.size+1 = 4*Q.links.length+1 := by omega
    simpa only [he] using hC Z
  obtain ⟨B,hmB,hpB,hbB,hgood⟩ := henv L hLe δ hδ hδ1 Q hlinkspos hlinkslog C hC' LG.garden.zeta
    (RA1Leafwise.norm_garden_zeta LG.garden).le
  have hF' : ∀ a, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.leafFam hQ hQ.1 H a) ≤
      ENNReal.ofReal Binput := fun a => hF _
  have hi (k : Mom d) (Z : (chosenSet Q.links).powerset) :=
    hjoint L hLj δ hδ hδ1 LG.garden Q hQ hQ.1 hlinkspos hlinkslog
      (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) _ (hC Z) (40*d) (40*d) (by omega) (by omega)
      Binput Ccover hBi (RA1Leafwise.leafFam hQ hQ.1 H) hF' S hcard k
  have hfun : (fun t : T => fun k : (Set.univ : Set (Mom d)) =>
      LGSpine.coupleLeaves L γ δ LG H (t.val 0) (t.val 1) k.val) =
      (fun t : T => fun k : (Set.univ : Set (Mom d)) =>
        pairedInverseProfile (fun lam => ∫ p, RA1Leafwise.maskedLeafScalarDensity hQ hQ.1
          (physicalScalar L δ γ Q LG.garden.zeta C) (RA1Leafwise.leafFam hQ hQ.1 H) S (lam,p) k.val
          ∂RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) t.val) := by
    funext t k
    have he := hid L hLg δ hδ hδ1 (40*d) (40*d) (by omega) (by omega) Binput Ccover hBi LG h0 hQ H hF
      hlinkspos hlinkslog S hcard hcover (t.val 0) (hT t.val t.property 0) (t.val 1)
      (hT t.val t.property 1) k.val
    have hp := physicalScalar_profile_eq hQ hQ.1 L δ γ LG.garden.zeta C
      (RA1Leafwise.leafFam hQ hQ.1 H) S k.val (hi k.val) t.val
    have ht : ![t.val 0,t.val 1] = t.val := by
      funext i
      fin_cases i <;> rfl
    rw [ht] at he
    exact he.trans hp.symm
  rw [hfun]
  have hBfin : (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) < ⊤ :=
    hbB.trans_lt (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  have hR (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) :=
    stronglyMeasurable_physicalScalar_joint Q hLpos δ γ LG.garden.zeta C (fun Z => (hC' Z).reg.meas) z
  have hmain := RA1Leafwise.leafScalar_profile_of_local_envelope hQ hQ.1
    (physicalScalar L δ γ Q LG.garden.zeta C) hR (N := 30*d) (W := 30*d) (K := 40*d) (M := 40*d)
    (by omega) (by omega) hBi hF' S hcard hθ0 hT (r := (Kr*δ)^Q.links.length) (by positivity)
    hmB hpB hBfin hgood
  refine hmain.trans ?_
  have hb := hbudget Q δ 1 hδpos.le zero_le_one
  rw [mul_one] at hb
  rw [← hlinks]
  refine le_trans ?_ hb
  gcongr
  rw [ENNReal.ofReal_one, one_mul]
  exact hbB

end WaveTurbulence.Flower.FiltCoh
