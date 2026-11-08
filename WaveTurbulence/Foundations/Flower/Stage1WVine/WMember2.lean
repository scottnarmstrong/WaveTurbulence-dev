/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WMember1

/-! # STAGE1W-VINE (T3/T4 inputs): the member identity and the integrability data of the weighted class sum

Main's `member_hV` (RepVD8), `member_integ`, `member_hsm` (RepVD9) for the weighted value
`valueSelW … (fwWeight p g base ·)`: for a member `y` of the unit class of the representative `a`, the weighted value is
the outer mode sum with the common data of `a` (the outer slot modes of `a`'s frontier-weighted slot kernels, by the
weighted R-SLOT `sourceShape_slotFW`) and the member's pinned unit kernels `unitRecenteredFW p (g j₁) none y (y.2 j) …`.
These are exactly the hypotheses of V5W-0's T4 `WeightedClassFactorization`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineC
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.Stage1 WaveTurbulence.RepAnalytic WaveTurbulence.VineA

variable {p : ℕ} {kind : Bool}

/-- The regional bound of a member's weighted slot family. -/
def memberRB {R : ℕ} {P : WTParams} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    (base : Mom P.d) (hlay : ∀ x, stateLayer y.1 x ≤ p)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ) (i : U.ι) :
    RegBound (fun j => unitClBlock (y.2 j)) y.1.plain
      (slotFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ (U.h i) p g) P.L base :=
  regBoundFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ (U.h i) p g
    (fun j => unitClBlock (y.2 j)) cψ hc hg base (lt_of_lt_of_le zero_lt_one hL1).ne'
    (fun j => hF_unit_of_bounded y.1.data y.1.plain hL1 hd1 (U.h i) (stateLayer y.1) base p (NNReal.coe_nonneg (U.b i))
      hlay (fun q j j' hq => hB i q j j' hq) j)

open scoped Classical in
/-- **The weighted member identity** (main's `member_hV` with the frontier weight). -/
theorem member_hVW {R : ℕ} {A : Finset (LayeredGarden (2 * R))} (π : PcA R p kind A)
    (a : PrescribedPrimeGarden (2 * R)) (hπ : repPt π = a) (P : WTParams)
    (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hlay : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p kind → ∀ x, stateLayer y.1 x ≤ p)
    (hcanM : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p kind → IsCanonGC (p + 1) y.1.layered)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (fam : U.ι → SlotFam a.fullProfile.piece.gap.garden P.d)
    (hexpR : ∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s'), ∀ x, HasSum
      (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
      (slotFW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) P.L P.γ P.δ (U.h i) p g
        ((profileShape a).iota a.prime.prime.1 hG s') ts x))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (hctrl : U.toLF.Controlled y.1.layered) :
    (valueSelW U.toLF tt base roots y.1.layered (selP p kind A P base roots π y.1.layered)
        (fwWeight p g base y.1.layered) =
      @Finset.sum U.ι ℂ _ (@Finset.univ _ U.fin) (fun i =>
        ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM a.fullProfile.piece.gap.garden P.L P.γ P.δ base roots tt
            a.fullProfile.piece.layer a.fullProfile.piece.hinges
            (fun z => if selSkC a P.L P.γ P.η (by positivity) base roots z then 1 else 0) hG
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((profileShape a).route a.prime.prime.1 hG)
            ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            (fun j lam t k => unitRecenteredFW p
              (g (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma j).upper.1.1) none y.1 (y.2 j)
              P.L P.γ P.δ (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j)
              base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))))
    ∧ ∀ i : U.ι, Summable (fun ξ : (∀ s, (fam i).Λ s) => ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM a.fullProfile.piece.gap.garden P.L P.γ P.δ base roots tt
            a.fullProfile.piece.layer a.fullProfile.piece.hinges
            (fun z => if selSkC a P.L P.γ P.η (by positivity) base roots z then 1 else 0) hG
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((profileShape a).route a.prime.prime.1 hG)
            ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            (fun j lam t k => unitRecenteredFW p
              (g (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma j).upper.1.1) none y.1 (y.2 j)
              P.L P.γ P.δ (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j)
              base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))) := by
  obtain ⟨M, hr, hn, hsh⟩ := sourceShape_data a y hy
  have hL0 : P.L ≠ 0 := (lt_of_lt_of_le zero_lt_one hL1).ne'
  have hrel : PrescribedPrimeGarden.Related (p := p) (kind := kind) (repPt π) (memberPoint a y M hr) :=
    hπ ▸ memberPoint_related' a y hy M hr
  have hsel : selP p kind A P base roots π y.1.layered = fun κ => selAt P base
      ⟨y.1.skeleton, VineA.batch_prime hr.batch a.prime.prime, y.1.data, y.1.decodes⟩
      (transportGroupPrescription (batchMolIso hr.batch) a.sigma) κ :=
    funext fun κ => propext (selP_iff_related P base roots π (memberPoint a y M hr) hrel y.1.layered rfl κ)
  rw [hsel, valueSelW_selAt_reconstruction U.toLF y.1.data (VineA.batch_prime hr.batch a.prime.prime)
    (stateLayer y.1) (stateLayer_isLayering y.1) y.1.layered (stateLayer_spec y.1) y.1.decodes
    (transportGroupPrescription (batchMolIso hr.batch) a.sigma) tt base roots (fwWeight p g base)]
  have hZ : ∀ κ : GenDecoration y.1.skeleton P.d roots 0,
      (if NormalizedSplice.selOf (transportGroupPrescription (batchMolIso hr.batch) a.sigma) P.L P.γ P.η base κ.1
        then (1 : ℝ) else 0) =
      (fun z => if selSkC a P.L P.γ P.η hL0 base roots z then (1 : ℝ) else 0)
        ((sourceShape a y hy).resDec y.1.plain (source_disj a y hy) κ) := by
    intro κ
    rw [hsh]
    exact (hZ_common a hr hn hL0 P.γ P.η base roots κ).trans
      (selSkC_ite a P.L P.γ P.η hL0 base roots _)
  have hctrl' : U.toLF.Controlled (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
      (stateLayer_isLayering y.1)) := by
    rw [stateLayer_spec y.1]; exact hctrl
  have hexp : ∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s'), ∀ x, HasSum
      (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
      (slotFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ (U.h i) p g
        ((sourceShape a y hy).iota y.1.plain hG s') ts x) := by
    intro i s' ts hts x
    rw [sourceShape_slotFW a y hy hG (U.h i) P.L P.γ P.δ p g s']
    exact hexpR i s' ts hts x
  have key := valueSelW_modesW U (sourceShape a y hy) (source_disj a y hy) y.1.data y.1.plain hG (stateLayer y.1)
    (stateLayer_isLayering y.1) hctrl' hd1 hL1 tt base roots
    (fun κ => NormalizedSplice.selOf (transportGroupPrescription (batchMolIso hr.batch) a.sigma) P.L P.γ P.η base κ.1)
    (fun z => if selSkC a P.L P.γ P.η hL0 base roots z then (1 : ℝ) else 0) hZ p g cψ hc hg
    (memberRB a y U hd1 hL1 base (hlay y hy) hB g cψ hc hg) fam
    (fun i s' => slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s')) hexp
    (fun i τ hτ s' => sourceShape_hbox a y hy hG tt htt τ hτ s')
  refine ⟨?_, fun i => ?_⟩
  · rw [key.1, member_lay_eq a y hy, sourceShape_hinges a y hy, sourceShape_route a y hy hG,
      sourceShape_hclk a y hy, sourceShape_hmom a y hy]
    simp only [member_ker_eqW a y hy _ _ _ _ _ _ (hcanM y hy) (hlay y hy)]
  · have h := key.2 i
    rw [member_lay_eq a y hy, sourceShape_hinges a y hy, sourceShape_route a y hy hG,
      sourceShape_hclk a y hy, sourceShape_hmom a y hy] at h
    simp only [member_ker_eqW a y hy _ _ _ _ _ _ (hcanM y hy) (hlay y hy)] at h
    exact h

/-- The integrability hypothesis of T4 for a member, for arbitrary outer modes (main's `member_integ` with the
frontier weight). -/
theorem member_integW {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (P : WTParams)
    (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (tt : Fin (2 * R) → ℝ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hlay : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p kind → ∀ x, stateLayer y.1 x ≤ p)
    (hcanM : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p kind → IsCanonGC (p + 1) y.1.layered)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (amp : ReplacementSlot a.fullProfile.piece.gap.garden → Mom P.d → ℂ)
    (frq : ReplacementSlot a.fullProfile.piece.gap.garden → Fin 2 → ℤ)
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) (i : U.ι)
    (z : GenDecoration a.fullProfile.piece.gap.garden P.d roots 0) :
    Integrable (outerIntegrandM a.fullProfile.piece.gap.garden P.L P.γ P.δ base roots tt
      a.fullProfile.piece.layer hG amp frq
      ((profileShape a).route a.prime.prime.1 hG)
      ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
      ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
      (fun j lam t k => unitRecenteredFW p
        (g (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma j).upper.1.1) none y.1 (y.2 j)
        P.L P.γ P.δ (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j)
        base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z) := by
  have h := integrable_outerIntegrandMG (sourceShape a y hy) (memberRB a y U hd1 hL1 base (hlay y hy) hB g cψ hc hg i)
    (source_disj a y hy) y.1.data hG P.γ P.δ (stateLayer y.1) tt amp frq z
  rw [member_lay_eq a y hy, sourceShape_route a y hy hG, sourceShape_hclk a y hy,
    sourceShape_hmom a y hy] at h
  simp only [member_ker_eqW a y hy _ _ _ _ _ _ (hcanM y hy) (hlay y hy)] at h
  exact h

/-- The decoration-summability hypothesis of T4 for a member, for arbitrary outer modes with summable amplitude bound
(main's `member_hsm` with the frontier weight). -/
theorem member_hsmW {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (P : WTParams)
    (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (tt : Fin (2 * R) → ℝ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hlay : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p kind → ∀ x, stateLayer y.1 x ≤ p)
    (hcanM : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p kind → IsCanonGC (p + 1) y.1.layered)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (amp : ReplacementSlot a.fullProfile.piece.gap.garden → Mom P.d → ℂ)
    (frq : ReplacementSlot a.fullProfile.piece.gap.garden → Fin 2 → ℤ)
    (hsum : Summable fun z : GenDecoration a.fullProfile.piece.gap.garden P.d roots 0 => ampBound hG P.L base amp z)
    (Zw : GenDecoration a.fullProfile.piece.gap.garden P.d roots 0 → ℝ) (hZw : ∀ z, |Zw z| ≤ 1)
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) (i : U.ι) :
    Summable (fun z : GenDecoration a.fullProfile.piece.gap.garden P.d roots 0 =>
      (splicedEpsilon a.fullProfile.piece.gap.garden a.fullProfile.piece.hinges z.1 : ℂ) * (Zw z : ℂ) *
        ∫ τ, outerIntegrandM a.fullProfile.piece.gap.garden P.L P.γ P.δ base roots tt
          a.fullProfile.piece.layer hG amp frq
          ((profileShape a).route a.prime.prime.1 hG)
          ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
          ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
          (fun j lam t k => unitRecenteredFW p
            (g (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma j).upper.1.1) none y.1 (y.2 j)
            P.L P.γ P.δ (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j)
            base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z τ) := by
  have h := summable_outer_decorationsG (sourceShape a y hy) (memberRB a y U hd1 hL1 base (hlay y hy) hB g cψ hc hg i)
    (source_disj a y hy) y.1.data hG P.γ P.δ (stateLayer y.1) tt amp frq Zw hZw hsum
  rw [member_lay_eq a y hy, sourceShape_hinges a y hy, sourceShape_route a y hy hG, sourceShape_hclk a y hy,
    sourceShape_hmom a y hy] at h
  simp only [member_ker_eqW a y hy _ _ _ _ _ _ (hcanM y hy) (hlay y hy)] at h
  exact h

end WaveTurbulence.Flower.Stage1WVine
