/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleChar
public import WaveTurbulence.Foundations.Flower.FiltCoh.SymbolEnvU
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalLatticeArray
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceScalarProfile
public import WaveTurbulence.Foundations.Flower.IncTop.Top.GardenPresentation

/-! # FILT-COH (b): the exact identities of a star-weighted layer-zero couple

* `kernelLeavesW_couple_lattice`: main's lattice reindexing (`coupleLeaves_integerLinkEquiv`,
  `coupleLeaves_latticeArray`) with an arbitrary decoration multiplier.
* `physicalScalarν`: the whole physical scalar at modulations shifted by a link frequency.
* `couple_char_global`: a lattice character on the lattice sum gives the source profile of `physicalScalarν`
  (main's `couple_physical_global_profiles` with the twisted cell identity of `CoupleChar`).
* `starDensity_eq`, `star_profile_fubini`: the presentation integral of root-modulated source profiles is the
  paired inverse profile of `starDensity`. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh Set
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice)
open scoped ENNReal

variable {d : ℕ}

/-- Main's lattice reindexing of a couple kernel, with an arbitrary multiplier. -/
theorem kernelLeavesW_couple_lattice (L γ δ : ℝ) (H : LGSpine.LeafProfiles 2 d) (LG : LayeredGarden 2)
    {Q : RegCpl} (hQ : Q.Decodes LG.garden) (t s : ℝ) (k : Mom d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0 m =
      (coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
      ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
        m (cosetDecoration LG.garden L k
          ((integerLinkEquiv hQ hQ.1 d).symm (fun j => (p (j,0), p (j,1)))).val) *
        (RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k p *
          (coupleMomentumData hQ hQ.1).sourceLeafWeight (RA1Leafwise.leafFam hQ hQ.1 H) k
            (fun i j => latticePoint L (p (i,j)))) := by
  unfold Flower.Stage1W.kernelLeavesW
  congr 1
  rw [tsum_integerLinkEquiv hQ hQ.1 d,
    ← (RA1Leafwise.linkPairArrayEquiv Q.links.length (Fin d → ℤ)).symm.tsum_eq]
  refine tsum_congr fun p => ?_
  dsimp only [RA1Leafwise.linkPairArrayEquiv, Equiv.coe_fn_symm_mk]
  rw [epsDec_integerLinkEquiv_symm hQ hQ.1 d, RA1Leafwise.actual_coset_leafProduct_eq hQ hQ.1 _ L k H]
  have he : (fun i j => if j=0 then latticePoint L (p (i,0)) else latticePoint L (p (i,1))) =
      (fun i j => latticePoint L (p (i,j))) := by
    funext i j
    fin_cases j <;> simp
  rw [he]
  unfold RA1Leafwise.coupleLatticeTimeCoefficient
  rfl

/-- The whole physical scalar at modulations shifted by a link frequency. -/
@[expose] def physicalScalarν (L δ γ : ℝ) (Q : RegCpl) (ζ : ℂ)
    (C : (Z : (chosenSet Q.links).powerset) →
      ({j : Fin Q.links.length // j ∉ RA1Leafwise.markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ)
    (ν : PairedMomentum d Q.links.length) (lam : ℝ × ℝ) (β γ' : Fin Q.links.length → Mom d)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) : ℂ :=
  physicalScalar L δ γ Q ζ C lam (shiftL β ν 0) (shiftL γ' ν 1) z

/-- Joint measurability of a shifted symbol family in the frequency parameter. -/
theorem stronglyMeasurable_shifted {n : ℕ} {α : Type*} [MeasurableSpace α]
    (R : (ℝ × ℝ) → (Fin n → Mom d) → (Fin n → Mom d) → ((Fin n × Fin 2) → Fin d → ℤ) → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ)
    (hR : StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      R p.1 p.2.1 p.2.2 z))
    {ν : α → PairedMomentum d n} (hν : Measurable ν) :
    StronglyMeasurable (fun p : α × ((ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d))) =>
      R p.2.1 (shiftL p.2.2.1 (ν p.1) 0) (shiftL p.2.2.2 (ν p.1) 1) z) := by
  have hm : Measurable (fun p : α × ((ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d))) =>
      (p.2.1, (shiftL p.2.2.1 (ν p.1) 0, shiftL p.2.2.2 (ν p.1) 1))) := by
    refine measurable_snd.fst.prodMk (Measurable.prodMk ?_ ?_)
    · exact (continuous_shiftL 0).measurable.comp (measurable_snd.snd.fst.prodMk (hν.comp measurable_fst))
    · exact (continuous_shiftL 1).measurable.comp (measurable_snd.snd.snd.prodMk (hν.comp measurable_fst))
  exact hR.comp_measurable hm

/-- **The character-twisted global identity of a layer-zero couple.** -/
theorem couple_char_global {η A : ℝ} (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (Q : RegCpl) (hwf : Q.wf = true) :
    ∃ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ RA1Leafwise.markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) A
        (C0 (1-η/8) (η/4) (1-η/2)^(2*Q.size+1)) (C Z)) ∧
      ∀ (d K M : ℕ) (H : LGSpine.LeafProfiles 2 d) (Binput Ccover L γ δ : ℝ) (LG : LayeredGarden 2)
        (_h0 : ∀ a, LG.layer a = 0) (hQ : Q.Decodes LG.garden),
      d+1 ≤ K → 2*d ≤ M → 0 ≤ Binput →
      (∀ a, Fourier.spatialNorm K M (RA1Leafwise.leafFam hQ hQ.1 H a) ≤ ENNReal.ofReal Binput) → 1 ≤ L →
      ∀ (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
        Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)),
      (∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length) →
      (∀ c k x, (coupleMomentumData hQ hQ.1).inputCellWeight c k x ≠ 0 →
        ∀ z, halfCellArrayWeight z (fun p : Fin Q.links.length × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c) →
      ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, ∀ (k : Mom d) (ν : PairedMomentum d Q.links.length),
      (∀ Z : (chosenSet Q.links).powerset, Integrable (fun q => RA1Leafwise.maskedLeafScalarDensity hQ hQ.1
        (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z (shiftL β ν 0) (shiftL γ' ν 1)
          (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam) (RA1Leafwise.leafFam hQ hQ.1 H) S q k)
        (volume.prod (RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)))) →
      (coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
        ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
          ((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) *
            RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k p) *
          (coupleMomentumData hQ hQ.1).sourceLeafWeight (RA1Leafwise.leafFam hQ hQ.1 H) k
            (fun i j => latticePoint L (p (i,j))) =
      RA1Leafwise.sourceScalarProfile hQ hQ.1 (physicalScalarν L δ γ Q LG.garden.zeta C ν)
        (RA1Leafwise.leafFam hQ hQ.1 H) S ![t,s] k := by
  classical
  obtain ⟨C,hC,hcell⟩ := couple_char_cell_symbols hη hη2 hA Q hwf
  refine ⟨C,hC,?_⟩
  intro d K M H Binput Ccover L γ δ LG h0 hQ hK hM hBi hF hL S hcard hcover t ht s hs k ν hi
  have hLpos : 0 < L := by linarith
  have horder : LG.garden.order = 2*Q.links.length := by
    rw [Reg.size_eq_order hQ]
    have hh := couple_linksAt_length Q ((0:Fin 2),[]) (1,[])
    simpa only [RegCpl.links,Nat.mul_comm] using hh.symm
  have hbH : ∀ p, ‖(Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) *
      RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k p‖ ≤ 1 := by
    intro p
    rw [norm_mul, Circle.norm_coe, one_mul]
    exact RA1Leafwise.norm_coupleLatticeTimeCoefficient_le_one L γ δ LG h0 hQ ht.2 hs.2 k p
  rw [source_lattice_eq_tsum_cells (coupleMomentumData hQ hQ.1) (RA1Leafwise.leafFam hQ hQ.1 H) S k
    (fun c x => hcover c k x) hcard hL hK hM hBi hF _ hbH]
  have hlocal (u : SourceCellIndex S) := hcell d K M (RA1Leafwise.leafFam hQ hQ.1 H) Binput
    (by omega) hBi hF L γ δ LG h0 hQ hLpos t ht s hs k S u ν
  have hrec := RA1Leafwise.masked_source_profiles_recombine hQ hQ.1
    (fun Z lam β γ' z => physicalWeightedCellSymbol L δ γ z (shiftL β ν 0) (shiftL γ' ν 1)
      (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam)
    (fun Z => ∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)
    (RA1Leafwise.leafFam hQ hQ.1 H) S k hi ![t,s]
  have he : (coupling d L γ δ:ℂ)^(2*Q.links.length)*
      (∑' u : SourceCellIndex S, ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
        ((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) *
          RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k p) *
          (coupleMomentumData hQ hQ.1).sourceCellWeight (RA1Leafwise.leafFam hQ hQ.1 H) S k
            (fun i j => latticePoint L (p (i,j))) u) =
      ∑ Z : (chosenSet Q.links).powerset,
        (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
          RA1Leafwise.sourceScalarProfile hQ hQ.1
            (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z (shiftL β ν 0) (shiftL γ' ν 1)
              (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam)
            (RA1Leafwise.leafFam hQ hQ.1 H) S ![t,s] k := by
    rw [← tsum_mul_left]
    simp only [coupling,← Complex.ofReal_pow]
    simp_rw [hlocal]
    exact hrec
  rw [horder, mul_assoc, mul_left_comm ((coupling d L γ δ:ℂ)^(2*Q.links.length)) LG.garden.zeta, he]
  -- linearity of the source profile
  let R : (chosenSet Q.links).powerset → (ℝ × ℝ) →
      (Fin Q.links.length → Mom d) → (Fin Q.links.length → Mom d) →
      ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ := fun Z lam β γ' z =>
    (∏ a ∈ Z.val, ((Cancel.zetaA a:ℂ)*Real.pi*Complex.I)⁻¹) *
      physicalWeightedCellSymbol L δ γ z (shiftL β ν 0) (shiftL γ' ν 1)
        (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam
  have hiR (Z : (chosenSet Q.links).powerset) :
      Integrable (fun q => RA1Leafwise.maskedLeafScalarDensity hQ hQ.1 (R Z)
        (RA1Leafwise.leafFam hQ hQ.1 H) S q k)
        (volume.prod (RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) := by
    have hh := (hi Z).const_mul (∏ a ∈ Z.val, ((Cancel.zetaA a:ℂ)*Real.pi*Complex.I)⁻¹)
    apply hh.congr
    apply ae_of_all
    intro q
    rcases q with ⟨lam,p⟩
    simp only [R,RA1Leafwise.maskedLeafScalarDensity_const_mul]
  change _ = RA1Leafwise.sourceScalarProfile hQ hQ.1
    (fun lam β γ' z => LG.garden.zeta*∑ Z, R Z lam β γ' z) (RA1Leafwise.leafFam hQ hQ.1 H) S ![t,s] k
  rw [RA1Leafwise.sourceScalarProfile_const_mul,
    RA1Leafwise.sourceScalarProfile_finsetSum hQ hQ.1 (RA1Leafwise.leafFam hQ hQ.1 H) S Finset.univ R k
      (fun Z _ => hiR Z)]
  congr 1
  apply Finset.sum_congr rfl
  intro Z _
  dsimp only [R]
  rw [RA1Leafwise.sourceScalarProfile_const_mul]

/-- The star density factors into the presentation amplitude, the root character and the leaf density. -/
theorem starDensity_eq {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    {α : Type*} (R : α → SymFam Q d) (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (amp : α → ℂ) (Ξ : α → Mom d) (lam : ℝ × ℝ)
    (p : RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1)) (a : α) (k : Mom d) :
    starDensity hQ hG R F S amp Ξ (lam, (p, a)) k =
      amp a * IncTop.rootChar (Ξ a) k * RA1Leafwise.maskedLeafScalarDensity hQ hG (R a) F S (lam, p) k := by
  have he : ∀ s : ℝ, (Real.fourierChar s : ℂ) = WeylSums.e s := fun _ => rfl
  simp only [starDensity, starAmplitude, RA1Leafwise.maskedLeafScalarDensity, maskedModulation,
    IncTop.rootChar, inner_add_left, he, WeylSums.e_add]
  ring

end WaveTurbulence.Flower.FiltCoh
