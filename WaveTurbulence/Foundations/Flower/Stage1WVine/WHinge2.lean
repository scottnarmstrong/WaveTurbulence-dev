/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WClass
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD13

/-! # STAGE1W-VINE (T6, part 2): the hinge data of the weighted units of the representative

`unit_hinge_dataW` (main's `unit_hinge_data`, RepVD13): `hinge_units_constW` instantiated at the aligned unit assembly of
the representative `a`, with the common selection `selSkC`, the leaf flags of `G_sb`, `hcont` from T5 + INC-TOP
(`unit_hcontW`), `hind` (`unitHkFW_hind`), G1, G2; the unit bound is the staged **`V5FrontierClassBoundAt`**.
The hinge constant `ChinFW d η` depends only on `(d, η)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS5C
  VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.Represents
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W

/-- The hinge-data constant of `hinge_units_constW`, as a function of `(d, η)`. -/
def ChinFW (d : ℕ) (η : ℝ) : ℝ :=
  if h : 0 ≤ η then (hinge_units_constW d η h).choose else 0

theorem ChinFW_spec (d : ℕ) (η : ℝ) (h : 0 ≤ η) : 0 ≤ ChinFW d η := by
  unfold ChinFW
  rw [dif_pos h]
  exact (hinge_units_constW d η h).choose_spec.1

open scoped Classical in
/-- **The hinge data of the weighted units of the representative** (main's `unit_hinge_data`). -/
theorem unit_hinge_dataW (P : WTParams) (hV : V5FrontierClassBoundAt P) (hM9 : VINEPARAM)
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (htop : TopIncoherentDecayAtR P)
    (hd1 : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η)
    (hη2 : P.η ≤ 1 / 2) (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL1 : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (hcan : IsCanonGC (p + 1) a.layered)
    (hord : (a.prime.data.garden a.prime.prime.1).order ≤ P.N (p + 1) ^ 4)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hgp : ∀ j, GPresented (32 * P.d) (g j) cψ)
    (hre : ∀ j x, (g j x).im = 0)
    (hp' : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (bb : ℝ) (hbb : 0 ≤ bb)
    (hB : ∀ q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (hp' q j j') ≤ ENNReal.ofReal bb)
    (lam : Fin (unitBlocks a.prime.skeleton a.totalSigma).length → ℤ) :
    ∃ (H : HingeFam (Fin (unitBlocks a.prime.skeleton a.totalSigma).length) P.d)
      (Mh : Fin (unitBlocks a.prime.skeleton a.totalSigma).length → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkProp (a.normalizedPiece P.d) tt base roots
        (selSkC a P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots)
        ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
        ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
        (fun j => unitHkFW P p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) g
          (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) hp' j) base (lam j)) H ∧
      ∏ j, Mh j = ChinFW P.d P.η ^ Fintype.card (Fin (unitBlocks a.prime.skeleton a.totalSigma).length) *
        (∏ j, unitMassFW P hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) cψ bb) *
        ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ (6 * P.η ^ 6) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hMa := Mole.garden_isMolecule a.prime.skeleton
  have hspec := (hinge_units_constW P.d P.η hη0.le).choose_spec
  have hChin : ChinFW P.d P.η = (hinge_units_constW P.d P.η hη0.le).choose := by
    unfold ChinFW; rw [dif_pos hη0.le]
  rw [hChin]
  have hcan' : IsCanonGC (p + 1) (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) := by rw [sourceLayer_reconstructs]; exact hcan
  have hordS : a.prime.skeleton.order ≤ P.N (p + 1) ^ 4 := by
    have := a.prime.data.decoded_order a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)
    omega
  have hcl : ∀ j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length,
      clLocalOrder1 (regionOf (unitBlk hMa a.totalSigma j)) ≤ P.N 1 ^ 4 := fun j =>
    clLocalOrder1_le_N1 P _ hordS
  have hh' : ∀ j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length, ∀ r ≤ p,
      SNormR (40 * P.d) (40 * P.d) (unitProfile (unitBlk hMa a.totalSigma) hp' j r) ≤ ENNReal.ofReal bb :=
    fun j r hr => hB r _ _ hr
  have hLay : (a.normalizedPiece P.d).layer = (stSt a.prime.skeleton a.totalSigma).layer
      (RegRed.coreLayer (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
        a.prime.data a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)) := by
    funext c
    show RegRed.coreLayer a.layered a.prime.data a.prime.prime.1 a.prime.decodes
      ((stSt a.prime.skeleton a.totalSigma).M.ob c) = _
    rw [coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
      (sourceLayer_reconstructs a) a.prime.decodes]
    exact (coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) _ rfl _ _).symm
  have hG1 := g1_units P hMa a.totalSigma hM9 (B₀ := sourceAssembly a) a.prime.data a.prime.prime.1 (sourceLayer a)
    (sourceLayer_isLayering a) base tt roots (selSkC a P.L P.γ P.η hL0.ne' base roots)
    (fun j c => sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode)
      (fun i => latPt P.d (c i)))
    (fun j c hc => qOut_one_eq_lay hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) c hc)
    (fun j c hc => qOut_two_eq_lay hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) c hc)
    (fun j => hqle_units hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
  let D' : SplicedKernelData (stSt a.prime.skeleton a.totalSigma).G P.d :=
    ⟨fun _ => 0, ∅, fun _ => 0, fun _ _ => 0, fun _ => 0,
      NormalizedSplice.gapSpecification a.prime.skeleton a.totalSigma, fun _ => 0, fun _ => 0⟩
  have hG2 : ∀ κ : GenDecoration (stSt a.prime.skeleton a.totalSigma).G P.d roots 0,
      selSkC a P.L P.γ P.η hL0.ne' base roots κ → ∀ (j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length)
        (c : Fin 4 → Fin P.d → ℤ),
      (∀ i, ‖(base + latticePoint P.L (κ.1 ((stShape hMa a.totalSigma).hmom (unitBlk_disj hMa a.totalSigma) j i))) -
        latPt P.d (c i)‖ ≤ 1) →
        sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode)
            (fun i => base + latticePoint P.L (κ.1 ((stShape hMa a.totalSigma).hmom (unitBlk_disj hMa a.totalSigma) j i))) ∈
          outSet (unitD hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode)
              (fun i => latPt P.d (c i))) base) P.L P.γ P.η := by
    intro κ hκ j c hball
    refine g2_unitsN P hMa a.prime.prime.1 a.totalSigma hL0.ne' base roots D' rfl (B₀ := sourceAssembly a) hM9
      a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) κ ?_ j c hball
    have hD' : D'.gapSpecification = NormalizedSplice.gapSpecification a.prime.skeleton a.totalSigma := by
      simp only [D']
    have h1 := NormalizedSplice.gapValue_eq_indicator a.totalSigma D' hD' P.L P.γ P.η base κ.1
    have h2 : NormalizedSplice.gapValue a.prime.skeleton a.totalSigma P.L P.γ P.η base κ.1 = 1 :=
      (gap_value_eq_gapValue a P.L P.γ P.η hL0.ne' base roots κ).symm.trans hκ
    rw [← h1, h2]
    exact one_ne_zero
  have hcont : ∀ (j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length) (c : Fin 4 → Fin P.d → ℤ) (lam : ℤ),
      ∀ E ∈ outSet (unitD hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)
        (sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode)
          (fun i => latPt P.d (c i))) base) P.L P.γ P.η,
        ContinuousOn (fun t => unitHkFW P p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) g (unitProfile (unitBlk hMa a.totalSigma) hp' j) base lam t
          (sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode) E))
          (cubeSet (unitD hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a)
            (sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode)
              (fun i => latPt P.d (c i))) base).qOut) :=
    fun j c lam => unit_hcontW hgate hinc htop hd1 hη0 hη6 hη2 hC1 hδ hL1 hw hp
      (unitProfile (unitBlk hMa a.totalSigma) hp' j) bb (hh' j) a.prime.prime hM9 (sourceAssembly a j) a.prime.data
      a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hcan' hord g cψ hc hgp hre _ base lam
  have hind : ∀ (j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length) (lam : ℤ) (t t' : Fin 3 → ℝ)
      (k : Fin 4 → Mom P.d), (∀ i, ¬ leafFlag hMa a.totalSigma j i → t i = t' i) →
      unitHkFW P p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) g
        (unitProfile (unitBlk hMa a.totalSigma) hp' j) base lam t k =
      unitHkFW P p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) g
        (unitProfile (unitBlk hMa a.totalSigma) hp' j) base lam t' k :=
    fun j lam t t' k ht => unitHkFW_hind P p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) g _ base (leafFlag hMa a.totalSigma j) (leafFlag_zero hMa a.totalSigma j)
      (unit_hleaf1 hMa a.totalSigma a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        a.prime.prime j)
      (unit_hleaf2 hMa a.totalSigma a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        a.prime.prime j) lam t t' k ht
  obtain ⟨H, Mh, hsum, hHk, hprod⟩ := hspec.2 P rfl rfl hV (by linarith) hL0 hp a.prime.prime hM9 a.prime.data
    a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hcan' hord (B₀ := sourceAssembly a) hcl g cψ hc hgp hre
    (fun j => unitProfile (unitBlk hMa a.totalSigma) hp' j) (fun _ => bb) (fun _ => hbb) hh'
    (fun j c => sumintBoundary (a.prime.skeleton.sign (unitBlk hMa a.totalSigma j).upper.toNode)
      (fun i => latPt P.d (c i))) base (fun j => hqle_units hMa a.totalSigma j a.prime.data a.prime.prime.1
        (sourceLayer a) (sourceLayer_isLayering a)) hcont (stSt a.prime.skeleton a.totalSigma).G tt roots
    (selSkC a P.L P.γ P.η hL0.ne' base roots)
    ((stSt a.prime.skeleton a.totalSigma).layer
      (RegRed.coreLayer (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
        a.prime.data a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)))
    ((stShape hMa a.totalSigma).hmom (unitBlk_disj hMa a.totalSigma))
    ((stShape hMa a.totalSigma).hclk (unitBlk_disj hMa a.totalSigma))
    (leafFlag hMa a.totalSigma)
    (fun j i => ((qOutOf a.prime.data a.prime.prime.1 (sourceLayer a) (unitBlk hMa a.totalSigma j).upper
      (unitBlk hMa a.totalSigma j).lower (regionOf (unitBlk hMa a.totalSigma j)) i : ℕ) : ℝ)) hind hG1 hG2 lam
  refine ⟨H, Mh, hsum, ?_, hprod⟩
  intro κ hκ τ hτ j c hball
  rw [hLay] at hτ
  exact hHk κ hκ τ hτ j c hball

end WaveTurbulence.Flower.Stage1WVine
