/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.GateNorm
public import WaveTurbulence.Foundations.Spine.RA1LW.CoupleAsymptotics

/-! # Couples: from the unit-bound statement to arbitrary leaf bounds `B_ℓ` (RA1-LEAFWISE) -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp TTree LGSpine Finset Set Filter Topology Links Incoh IncohInst
open scoped ENNReal

variable {d : ℕ}

/-- The first endpoint of every code pair is an input leaf address. -/
theorem pair_fst_mem_leafAddrs {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    (p : (Fin 2 × Path) × (Fin 2 × Path)) (hp : p ∈ Q.pairsAt (0,[]) (1,[])) :
    p.1 ∈ (inputLeaves G).image (fun ℓ => ℓ.1) := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (show p ∈ Q.raw.2 from hp)
  refine Finset.mem_image.mpr ⟨(positivePairLeaf hQ i).val, ?_, ?_⟩
  · rw [inputLeaves_eq_plusLeaves hG]
    exact (mem_plusLeaves _).mpr (positivePairLeaf hQ i).property
  · exact congrArg Prod.fst hi

theorem couple_scaled (L γ δ η : ℝ) (hd : 1 ≤ d) (Q : RegCpl) (LG : LayeredGarden 2)
    (hQ : Q.Decodes LG.garden) (X : ℝ≥0∞) (hX : X ≠ ⊤)
    (hRA : ∀ H' : LeafProfiles 2 d, (∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1) →
      Fourier.mixedRestrictionNorm η (30 * d) (30 * d) (timeBox 0 0) Set.univ
        (fun ts k => coupleLeaves L γ δ LG H' (ts.1 0) (ts.1 1) k.1 -
          LeafApp.couple δ 0 H' Q (ts.1 0) (ts.1 1) k.1) ≤ X)
    (H : LeafProfiles 2 d) (B : Fin 2 × Path → NNReal) (hH : LeafwiseControlled LG H B) :
    Fourier.mixedRestrictionNorm η (30 * d) (30 * d) (timeBox 0 0) Set.univ
        (fun ts k => coupleLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1 -
          LeafApp.couple δ 0 H Q (ts.1 0) (ts.1 1) k.1) ≤
      ENNReal.ofReal (leafSizeProduct LG B) * X := by
  classical
  have hG := hQ.1
  unfold leafSizeProduct
  refine le_of_forall_eps (inputLeaves LG.garden) (fun ℓ => (B ℓ.1 : ℝ)) _ X hX ?_
  intro ε hε
  let S : Finset (Fin 2 × Path) := (inputLeaves LG.garden).image (fun ℓ => ℓ.1)
  let β : Fin 2 × Path → ℝ := fun z => (B z : ℝ) + ε
  have hβ0 : ∀ z, 0 < β z := fun z => by have := (B z).2; simp only [β]; positivity
  have hβne : ∀ z, β z ≠ 0 := fun z => (hβ0 z).ne'
  let H' := normProfile S β H
  have hnorm : ∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1 := by
    refine normProfile_norm_le (S := S) (B := fun z => (B z : ℝ)) hd (fun z => (B z).2) (fun z => ?_)
      hβ0 ?_
    · simp only [β]; linarith
    · intro z hz
      obtain ⟨ℓ,hℓ,rfl⟩ := Finset.mem_image.mp hz
      exact hH ℓ hℓ
  have hscale : ∀ ℓ ∈ inputLeaves LG.garden, H ℓ.1 = fun k => β ℓ.1 * H' ℓ.1 k := fun ℓ hℓ =>
    normProfile_scale hβne (Finset.mem_image_of_mem _ hℓ)
  set P : ℝ := ∏ ℓ ∈ inputLeaves LG.garden, β ℓ.1 with hP
  have hPpos : 0 < P := Finset.prod_pos fun ℓ _ => hβ0 _
  have hpairs : ∀ p ∈ Q.pairsAt (0,[]) (1,[]), H p.1 = fun k => β p.1 * H' p.1 k := fun p hp =>
    normProfile_scale hβne (pair_fst_mem_leafAddrs hQ hG p hp)
  have hMstar : ∀ Z, LeafApp.cplMstar H Z Q (0,[]) (1,[]) =
      fun k => P * LeafApp.cplMstar H' Z Q (0,[]) (1,[]) k := fun Z => by
    rw [cplMstar_scale H H' β Z Q (0,[]) (1,[]) hpairs, hP,
      prod_inputLeaves_couple_eq_pairScale hQ hG β]
  have happ : ∀ t s k, LeafApp.couple δ 0 H Q t s k = (P : ℂ) * LeafApp.couple δ 0 H' Q t s k := by
    intro t s k
    unfold LeafApp.couple
    split_ifs with hdom
    · simp only [hMstar]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Z _ => ?_
      push_cast
      ring
    · simp
  have hD : (fun (ts : timeBox 0 0) (k : (Set.univ : Set (Mom d))) =>
        coupleLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1 - LeafApp.couple δ 0 H Q (ts.1 0) (ts.1 1) k.1) =
      fun ts k => (P : ℂ) • (coupleLeaves L γ δ LG H' (ts.1 0) (ts.1 1) k.1 -
        LeafApp.couple δ 0 H' Q (ts.1 0) (ts.1 1) k.1) := by
    funext ts k
    rw [happ, coupleLeaves_scale L γ δ LG H H' β hscale]
    simp only [smul_eq_mul]
    ring
  rw [hD]
  have hc : (P : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  refine (mixedRestrictionNorm_smul_le hc η _ _ _ _ _).trans ?_
  rw [show ‖(P : ℂ)‖ₑ = ENNReal.ofReal P by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPpos]]
  exact mul_le_mul' le_rfl (hRA H' hnorm)

theorem couple_Mstar_scaled (hd : 1 ≤ d) (Q : RegCpl) (LG : LayeredGarden 2)
    (hQ : Q.Decodes LG.garden) (Cm : ℝ) (hCm : 0 ≤ Cm)
    (hRA : ∀ H' : LeafProfiles 2 d, (∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1) →
      ∀ Z ∈ specialSets Q.links,
        SNormR (30 * d) (30 * d) (LeafApp.cplMstar H' Z Q (0, []) (1, [])) ≤ ENNReal.ofReal Cm)
    (H : LeafProfiles 2 d) (B : Fin 2 × Path → NNReal) (hH : LeafwiseControlled LG H B)
    (Z : Finset (Fin 2 × Path)) (hZ : Z ∈ specialSets Q.links) :
    SNormR (30 * d) (30 * d) (LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤
      ENNReal.ofReal (Cm * leafSizeProduct LG B) := by
  classical
  have hG := hQ.1
  unfold leafSizeProduct
  have key : SNormR (30 * d) (30 * d) (LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤
      ENNReal.ofReal (∏ ℓ ∈ inputLeaves LG.garden, (B ℓ.1 : ℝ)) * ENNReal.ofReal Cm := by
    refine le_of_forall_eps (inputLeaves LG.garden) (fun ℓ => (B ℓ.1 : ℝ)) _ _ ENNReal.ofReal_ne_top ?_
    intro ε hε
    let S : Finset (Fin 2 × Path) := (inputLeaves LG.garden).image (fun ℓ => ℓ.1)
    let β : Fin 2 × Path → ℝ := fun z => (B z : ℝ) + ε
    have hβ0 : ∀ z, 0 < β z := fun z => by have := (B z).2; simp only [β]; positivity
    have hβne : ∀ z, β z ≠ 0 := fun z => (hβ0 z).ne'
    let H' := normProfile S β H
    have hnorm : ∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1 := by
      refine normProfile_norm_le (S := S) (B := fun z => (B z : ℝ)) hd (fun z => (B z).2) (fun z => ?_)
        hβ0 ?_
      · simp only [β]; linarith
      · intro z hz
        obtain ⟨ℓ,hℓ,rfl⟩ := Finset.mem_image.mp hz
        exact hH ℓ hℓ
    set P : ℝ := ∏ ℓ ∈ inputLeaves LG.garden, β ℓ.1 with hP
    have hPpos : 0 < P := Finset.prod_pos fun ℓ _ => hβ0 _
    have hpairs : ∀ p ∈ Q.pairsAt (0,[]) (1,[]), H p.1 = fun k => β p.1 * H' p.1 k := fun p hp =>
      normProfile_scale hβne (pair_fst_mem_leafAddrs hQ hG p hp)
    have hMstar : LeafApp.cplMstar H Z Q (0,[]) (1,[]) =
        fun k => P * LeafApp.cplMstar H' Z Q (0,[]) (1,[]) k := by
      rw [cplMstar_scale H H' β Z Q (0,[]) (1,[]) hpairs, hP,
        prod_inputLeaves_couple_eq_pairScale hQ hG β]
    rw [hMstar, NormBridgeScratch.SNormR_eq_spatialNorm]
    have h1 := hRA H' hnorm Z hZ
    rw [NormBridgeScratch.SNormR_eq_spatialNorm] at h1
    have h2 := spatialNorm_const_mul_le (by omega : 0 < 30 * d) hCm h1 ((P : ℝ) : ℂ)
    refine (le_of_eq_of_le ?_ h2).trans ?_
    · congr 1
      funext k
      push_cast
      rfl
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPpos, ENNReal.ofReal_mul hPpos.le]
  rw [mul_comm Cm, ENNReal.ofReal_mul (Finset.prod_nonneg fun ℓ _ => (B ℓ.1).2)]
  exact key

end WaveTurbulence.RA1Leafwise
