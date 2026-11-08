/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FlowerTop.ThreeInputs
public import WaveTurbulence.Foundations.Flower.Stage1W.Defs

/-! # STAGE1W-GLUE: Bridge (ported by source from the S-STAGE1W probe, see COPIED-SHA256SUMS). -/


@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1W
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

/-! ## 4. Unit weight: the gate specialises to main's plain `Stage1ReductionAt` (non-vacuity) -/

theorem topPsi_one {d : ℕ} (p : ℕ) : topPsi p (fun _ : Mom d => (1 : ℂ)) = fun _ _ _ => 1 := by
  funext q q' r
  simp [topPsi]

theorem nodeLabelProduct_topPsi_one {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (k : GNode LG.garden.tree → Mom d) :
    nodeLabelProduct (fun _ : Fin w => topPsi p (fun _ : Mom d => (1 : ℂ))) LG p k = 1 := by
  unfold nodeLabelProduct
  simp [topPsi]

/-- The constant `1` is presented by the Dirac mass at frequency `0` (S2-ST's `gPresented_one`, verbatim proof). -/
theorem gPresented_one {d : ℕ} (J : ℕ) : GPresented J (fun _ : Mom d => (1 : ℂ)) 1 := by
  refine ⟨Unit, inferInstance, ⟨Measure.dirac (), inferInstance, fun _ => 0, measurable_const, fun _ => 1,
    integrable_const _⟩, ?_, fun x => ?_⟩
  · unfold momentMassMom
    simp
  · unfold Cut2A.SpatialMeasure.value
    simp

theorem valueSelW_one {P : WTParams} {w : ℕ} (F : LeafFamily P w) (tt : Fin w → ℝ)
    (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ)) (LG : LayeredGarden w)
    (sel : GenDecoration LG.garden P.d roots 0 → Prop) :
    valueSelW F tt base roots LG sel (fun _ => 1) = F.valueSel tt base roots LG sel := by
  unfold valueSelW LeafFamily.valueSel kernelLeavesSelW kernelLeavesSel
  simp only [one_mul]

theorem fwWeight_one {P : WTParams} {R : ℕ} (p : ℕ) (base : Mom P.d) {roots : Fin (2 * R) → (Fin P.d → ℤ)}
    (LG : LayeredGarden (2 * R)) (κ : GenDecoration LG.garden P.d roots 0) :
    fwWeight p (fun _ _ => (1 : ℂ)) base LG κ = 1 :=
  nodeLabelProduct_topPsi_one LG p _

/-- **`g ≡ 1`**: the frontier-weighted gate implies main's `Stage1ReductionAt` (so it is not vacuous). -/
theorem stage1ReductionAt_of_FW (C₀ : ℕ) (P : WTParams) (h : Stage1ReductionAtFW C₀ P) :
    Stage1ReductionAt C₀ P := by
  intro p hp R hR1 hR2 N hN1 hN2 A hA hTC tt htt base roots U s hs hU hsz
  obtain ⟨S, Cl, hCl, cls, members, sel, hpart, hrep, hsound, hord, hcnt⟩ :=
    h p hp R hR1 hR2 N hN1 hN2 A hA hTC tt htt base roots (fun _ _ => 1) 1 le_rfl
      (fun _ => gPresented_one _) (fun _ _ => by simp) U s hs hU hsz
  refine ⟨S, Cl, hCl, cls, members, sel, hpart, fun π => ?_, hsound, hord, hcnt⟩
  obtain ⟨hv, hi⟩ := hrep π
  refine ⟨?_, ?_⟩
  · rw [hv]
    refine Finset.sum_congr rfl fun LG _ => ?_
    have e : (fwWeight p (fun _ _ => (1 : ℂ)) base LG : GenDecoration LG.garden P.d roots 0 → ℂ) = fun _ => 1 :=
      funext fun κ => fwWeight_one p base LG κ
    rw [e, valueSelW_one]
  · have e : (1 : ℝ) ^ (16 * N) * s = s := by rw [one_pow, one_mul]
    rw [e] at hi
    exact hi

/-! ## 5. The piece statements (O4 / O3 analogues) and the assembly -/

section Pieces
open WaveTurbulence.Represents WaveTurbulence.VineA WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.ClassCount WaveTurbulence.RedSplice
  WaveTurbulence.VineParamContract

/-- **O4′ (vine-free pieces)**: the `RepresentsInt` of the producer's piece of every vine-free tau class, at the
frontier-weighted class sum and size `cψ ^ (16 N) * s`, in the exact data of `Stage1ReductionAtFW`. -/
def NoVineRepresentsFW (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Carries P p N LG) → TwistClosed p A →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
    (∀ j x, (g j x).im = 0) →
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∀ π : PcA R p (objKind (2 * R)) A,
    unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma = [] →
    Stage1Piece.RepresentsInt (P := P) ((repPt π).normalizedPiece P.d) N tt base roots (cψ ^ (16 * N) * s)
      (∑ LG ∈ membersP (clsP π), valueSelW U.toLF tt base roots LG
        (selP p (objKind (2 * R)) A P base roots π LG) (fwWeight p g base LG))

/-- **O3′ (vine pieces)**: as `NoVineRepresentsFW`, for the tau classes whose representative has a unit. -/
def VineCaseRepresentsFW (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Carries P p N LG) → TwistClosed p A →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
    (∀ j x, (g j x).im = 0) →
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∀ π : PcA R p (objKind (2 * R)) A,
    unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma ≠ [] →
    Stage1Piece.RepresentsInt (P := P) ((repPt π).normalizedPiece P.d) N tt base roots (cψ ^ (16 * N) * s)
      (∑ LG ∈ membersP (clsP π), valueSelW U.toLF tt base roots LG
        (selP p (objKind (2 * R)) A P base roots π LG) (fwWeight p g base LG))

/-- **Assembly** (probe proof; the port of main's `stage1ReductionAt_of_inputs`, RepS10c, with weighted values). -/
theorem stage1ReductionAtFW_of_pieces (hcc : ClassCountStmt) :
    ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ ∀ P : WTParams, (K : ℝ) ^ (P.D + 1) ≤ P.C₂ → 2 ≤ P.L → NoVineRepresentsFW P →
      VineCaseRepresentsFW P → Stage1ReductionAtFW C₀ P := by
  obtain ⟨C₀, K, hC₀, hcnt⟩ := prod_stage1Counts hcc
  refine ⟨C₀, K, hC₀, ?_⟩
  intro P hK hL hnv hvine
  intro p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots g cψ hcψ hg hre U s hs0 hb hsize
  have hplain : ∀ LG ∈ A, LG.garden.IsPlain := fun LG hLG => (hA LG hLG).1.1
  set kind := objKind (2 * R) with hkind
  refine ⟨prodData P p kind A (fun π => ∑ LG ∈ membersP (clsP π),
      valueSelW U.toLF tt base roots LG (selP p kind A P base roots π LG) (fwWeight p g base LG)),
    ClA R p kind A, inferInstance, clsP, membersP, selP p kind A P base roots,
    stage1Partition_prod p kind A hplain P base roots, ?_, ?_, ?_, hcnt P hK p hp R hR N hN1 kind A hA _⟩
  · intro π
    refine ⟨rfl, ?_⟩
    by_cases hv : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma = []
    · exact hnv p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots g cψ hcψ hg hre U s hs0 hb hsize π hv
    · exact hvine p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots g cψ hcψ hg hre U s hs0 hb hsize π hv
  · intro π
    exact normalizedPiece_sound P hR (repPt π) (hA _ (repPt_layered_mem π)) hN (by linarith) base roots
  · intro π
    have h := prod_piece_gsb_order P p N kind A hA π
    have h3 := order_add_hinges_le (Mole.garden_isMolecule (repPt π).prime.skeleton) (repPt π).totalSigma
    show (stSt (repPt π).prime.skeleton (repPt π).totalSigma).G.order ≤ N
    omega

theorem noVineRepresentsFW_mono : LargeConstantMonotone NoVineRepresentsFW := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots g cψ hcψ hg hre U s hs0 hb hsize π hv
  have hRmax' : R ≤ 10 * P.R (p + 1) := by simpa only [R_largeConstants] using hRmax
  have hN' : N ≤ P.N (p + 1) ^ 4 := by simpa only [N_largeConstants] using hN
  have h1 := h p hp R hR hRmax' N hN1 hN' A (fun LG hLG => stage1Carries_largeConstants c₁ c₂ LG (hA LG hLG)) hcl
    tt htt base roots g cψ hcψ hg hre U s hs0 hb hsize π hv
  have hs' : 0 ≤ cψ ^ (16 * N) * s := mul_nonneg (pow_nonneg (by linarith) _) hs0.le
  exact RepresentsInt_largeConstants c₁ c₂ h₁ (by linarith) hδ.le (by linarith) _ N tt base roots _ hs' _ h1

theorem vineCaseRepresentsFW_mono : LargeConstantMonotone VineCaseRepresentsFW := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots g cψ hcψ hg hre U s hs0 hb hsize π hv
  have hRmax' : R ≤ 10 * P.R (p + 1) := by simpa only [R_largeConstants] using hRmax
  have hN' : N ≤ P.N (p + 1) ^ 4 := by simpa only [N_largeConstants] using hN
  have h1 := h p hp R hR hRmax' N hN1 hN' A (fun LG hLG => stage1Carries_largeConstants c₁ c₂ LG (hA LG hLG)) hcl
    tt htt base roots g cψ hcψ hg hre U s hs0 hb hsize π hv
  have hs' : 0 ≤ cψ ^ (16 * N) * s := mul_nonneg (pow_nonneg (by linarith) _) hs0.le
  exact RepresentsInt_largeConstants c₁ c₂ h₁ (by linarith) hδ.le (by linarith) _ N tt base roots _ hs' _ h1

/-- **The gate from its two piece statements** (prefix form; port of main's `stage1ReductionGate_of_vineCase`). -/
theorem stage1ReductionGateFW_of_pieces (hnv : WTPrefix NoVineRepresentsFW)
    (hvine : WTPrefix VineCaseRepresentsFW) : Stage1ReductionGateFW := by
  obtain ⟨C₀, K, hC₀, hmain⟩ := stage1ReductionAtFW_of_pieces ClassCount.classCount
  refine ⟨fun _ _ => C₀, fun _ _ => hC₀, ?_⟩
  have hQ := prefix_and hnv hvine noVineRepresentsFW_mono vineCaseRepresentsFW_mono
  have hm : LargeConstantMonotone (fun P => NoVineRepresentsFW P ∧ VineCaseRepresentsFW P) :=
    noVineRepresentsFW_mono.and vineCaseRepresentsFW_mono
  have hQ2 := prefix_with_C2_ge hQ hm (K : ℝ)
  exact prefix_map (fun P hP => hmain P hP.2.1 hP.2.2 hP.1.1 hP.1.2) hQ2

end Pieces


end WaveTurbulence.Flower.Stage1W
