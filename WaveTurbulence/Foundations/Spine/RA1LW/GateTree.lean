/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.GateNorm
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeAsymptotics

/-! # Trees: from the unit-bound statement to arbitrary leaf bounds `B_ℓ` (RA1-LEAFWISE) -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp TTree LGSpine Finset Set Filter Topology Links Incoh IncohInst
open scoped ENNReal

variable {d : ℕ}

/-- The first endpoint of every tree pair is an input leaf address. -/
theorem tree_pair_fst_mem_leafAddrs {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (p : (Fin 1 × Path) × (Fin 1 × Path)) (hp : p ∈ X.pairsAt (G.sig 0) ((0:Fin 1),[])) :
    p.1 ∈ (inputLeaves G).image (fun ℓ => ℓ.1) := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
  refine Finset.mem_image.mpr ⟨(treePositivePairLeaf hX i).val, ?_, ?_⟩
  · rw [tree_inputLeaves hX]
    simp only [plusPaired, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (treePositivePairLeaf hX i).property
  · exact congrArg Prod.fst hi

theorem tree_scaled (L γ δ η : ℝ) (hd : 1 ≤ d) (X : RegChain) (LG : LayeredGarden 1)
    (hX : X.DecodesTree LG.garden) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hRA : ∀ H' : LeafProfiles 1 d, (∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1) →
      Fourier.mixedRestrictionNorm η (30 * d) 0 (timeBoxGt 0 0) Set.univ
        (fun ts k => treeLeaves L γ δ LG H' (ts.1 0) (ts.1 1) k.1 -
          LeafApp.tree δ 0 H' X (LG.garden.sig 0) (ts.1 0) (ts.1 1) k.1) ≤ M)
    (H : LeafProfiles 1 d) (B : Fin 1 × Path → NNReal) (hH : LeafwiseControlled LG H B) :
    Fourier.mixedRestrictionNorm η (30 * d) 0 (timeBoxGt 0 0) Set.univ
        (fun ts k => treeLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1 -
          LeafApp.tree δ 0 H X (LG.garden.sig 0) (ts.1 0) (ts.1 1) k.1) ≤
      ENNReal.ofReal (leafSizeProduct LG B) * M := by
  classical
  unfold leafSizeProduct
  refine le_of_forall_eps (inputLeaves LG.garden) (fun ℓ => (B ℓ.1 : ℝ)) _ M hM ?_
  intro ε hε
  let S : Finset (Fin 1 × Path) := (inputLeaves LG.garden).image (fun ℓ => ℓ.1)
  let β : Fin 1 × Path → ℝ := fun z => (B z : ℝ) + ε
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
  have hpairs : ∀ p ∈ X.pairsAt (LG.garden.sig 0) ((0:Fin 1),[]), H p.1 = fun k => β p.1 * H' p.1 k :=
    fun p hp => normProfile_scale hβne (tree_pair_fst_mem_leafAddrs hX p hp)
  have hN : ∀ Z, LeafApp.chainNstar H Z X (LG.garden.sig 0) ((0:Fin 1),[]) =
      fun k => P * LeafApp.chainNstar H' Z X (LG.garden.sig 0) ((0:Fin 1),[]) k := fun Z => by
    rw [chainNstar_scale H H' β Z X (LG.garden.sig 0) ((0:Fin 1),[]) hpairs, hP,
      prod_inputLeaves_tree_eq_pairScale hX β]
  have happ : ∀ t s k, LeafApp.tree δ 0 H X (LG.garden.sig 0) t s k =
      (P : ℂ) * LeafApp.tree δ 0 H' X (LG.garden.sig 0) t s k := by
    intro t s k
    unfold LeafApp.tree
    split_ifs with hdom
    · simp only [hN]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Z _ => ?_
      push_cast
      ring
    · simp
  have hD : (fun (ts : timeBoxGt 0 0) (k : (Set.univ : Set (Mom d))) =>
        treeLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1 -
          LeafApp.tree δ 0 H X (LG.garden.sig 0) (ts.1 0) (ts.1 1) k.1) =
      fun ts k => (P : ℂ) • (treeLeaves L γ δ LG H' (ts.1 0) (ts.1 1) k.1 -
        LeafApp.tree δ 0 H' X (LG.garden.sig 0) (ts.1 0) (ts.1 1) k.1) := by
    funext ts k
    rw [happ, treeLeaves_scale L γ δ LG H H' β hscale]
    simp only [smul_eq_mul]
    ring
  rw [hD]
  have hc : (P : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  refine (mixedRestrictionNorm_smul_le hc η _ _ _ _ _).trans ?_
  rw [show ‖(P : ℂ)‖ₑ = ENNReal.ofReal P by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPpos]]
  exact mul_le_mul' le_rfl (hRA H' hnorm)

theorem tree_Nstar_scaled (hd : 1 ≤ d) (X : RegChain) (LG : LayeredGarden 1)
    (hX : X.DecodesTree LG.garden) (Cm : ℝ) (hCm : 0 ≤ Cm)
    (hRA : ∀ H' : LeafProfiles 1 d, (∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1) →
      ∀ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)),
        SNormR (30 * d) 0 (LeafApp.chainNstar H' Z X (LG.garden.sig 0) (0, [])) ≤ ENNReal.ofReal Cm)
    (H : LeafProfiles 1 d) (B : Fin 1 × Path → NNReal) (hH : LeafwiseControlled LG H B)
    (Z : Finset (Fin 1 × Path)) (hZ : Z ∈ specialSets (X.treeLinks (LG.garden.sig 0))) :
    SNormR (30 * d) 0 (LeafApp.chainNstar H Z X (LG.garden.sig 0) (0, [])) ≤
      ENNReal.ofReal (Cm * leafSizeProduct LG B) := by
  classical
  unfold leafSizeProduct
  have key : SNormR (30 * d) 0 (LeafApp.chainNstar H Z X (LG.garden.sig 0) (0, [])) ≤
      ENNReal.ofReal (∏ ℓ ∈ inputLeaves LG.garden, (B ℓ.1 : ℝ)) * ENNReal.ofReal Cm := by
    refine le_of_forall_eps (inputLeaves LG.garden) (fun ℓ => (B ℓ.1 : ℝ)) _ _ ENNReal.ofReal_ne_top ?_
    intro ε hε
    let S : Finset (Fin 1 × Path) := (inputLeaves LG.garden).image (fun ℓ => ℓ.1)
    let β : Fin 1 × Path → ℝ := fun z => (B z : ℝ) + ε
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
    have hpairs : ∀ p ∈ X.pairsAt (LG.garden.sig 0) ((0:Fin 1),[]), H p.1 = fun k => β p.1 * H' p.1 k :=
      fun p hp => normProfile_scale hβne (tree_pair_fst_mem_leafAddrs hX p hp)
    have hN : LeafApp.chainNstar H Z X (LG.garden.sig 0) ((0:Fin 1),[]) =
        fun k => P * LeafApp.chainNstar H' Z X (LG.garden.sig 0) ((0:Fin 1),[]) k := by
      rw [chainNstar_scale H H' β Z X (LG.garden.sig 0) ((0:Fin 1),[]) hpairs, hP,
        prod_inputLeaves_tree_eq_pairScale hX β]
    rw [hN, NormBridgeScratch.SNormR_eq_spatialNorm]
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
