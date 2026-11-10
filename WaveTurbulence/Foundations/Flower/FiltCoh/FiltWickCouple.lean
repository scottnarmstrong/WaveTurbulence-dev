/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.FiltWickEnv
public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleStarId
public import WaveTurbulence.Foundations.Flower.FiltSrc.Identity

/-! # FILT-COH (d2e): the filtered cell identity of a layer-zero couple

On the coset decoration of a lattice link array `p`, the two filter layers are `arrayFiltWeight L φ p =
∏_j φ_j(⟨x_j, y_j⟩)` (FILT-SRC `couple_filtWeight_eq_arrayFiltWeight`), i.e. `∏_j ψ_j(Ω_j)` in the NT energies
`Ω_j = μ⟨x_j, y_j⟩` with `ψ_j = φ_j(·/μ)` (`profFilt`, `arrayFiltWeight_linkPair`). Main's cell identity carries
this factor into the profile:
* `filt_temporal_interchange`, `halfCell_finite_profiles_eq_filtSymbols`: main's finite profile summation with the
  filtered physical symbol `filtCellSymbol`;
* `couple_filt_cell_symbols`: main's `couple_physical_cell_symbols` (with FiltCoh's character twist) with the array
  filter in the lattice coefficient;
* `filtScalar`, `filtScalarν`, `couple_filt_global`: the whole filtered scalar and the global identity
  (`couple_char_global` with filters);
* `filt_scalar_envelope`: its envelope (`physical_scalar_envelope_theta_u` with filters).
Proofs adapted from main's `HalfCellWickTemporal`, `HalfCellProfileSum` and FiltCoh's `CoupleChar`,
`CoupleStarId`, `CoupleEnvelopeU` (sha256 in COPIED-SHA256SUMS). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh Set
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice)
open scoped ENNReal

variable {d : ℕ}

attribute [-instance] WaveTurbulence.Mole.instFintypePositionCode

/-- The link filters in the NT energy coordinate `Ω = μ u`. -/
@[expose] def profFilt {n : ℕ} (μ : ℝ) (φ : Fin n → ℝ → ℂ) : Fin n → ℝ → ℂ := fun j Ω => φ j (Ω / μ)

theorem arrayFiltWeight_linkPair {n : ℕ} {μ : ℝ} (hμ : μ ≠ 0) (L : ℝ) (φ : Fin n → ℝ → ℂ)
    (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
    FiltSrc.arrayFiltWeight L φ (RA1Leafwise.linkPairArrayEquiv n (Fin d → ℤ) θ) =
      ∏ j, profFilt μ φ j (wickLatticeEnergy L μ θ j) := by
  unfold FiltSrc.arrayFiltWeight profFilt wickLatticeEnergy FiltLink.linkBilinear
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  simp only [RA1Leafwise.linkPairArrayEquiv, Equiv.coe_fn_mk, ↓reduceIte,
    one_ne_zero]
  field_simp

/-- **Filtered temporal interchange** (main's `physicalWeightedCellSymbol_temporal_interchange`). -/
theorem filt_temporal_interchange {n : ℕ} {L : ℝ} (hL : 0 < L)
    (δ γ t s : ℝ) (ψ : Fin n → ℝ → ℂ) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) {C : ({j // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) :
    (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*
      (∑' θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ),
        ((((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)*
          halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2))*
          ∏ j, ψ j (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ j))*
        ∫ lam, resProfile J (fun Ω => C (ofLp Ω) lam)
          (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ)*e2 lam t s) =
    ∫ lam, filtCellSymbol L δ γ ψ z β γ' J C lam*e2 lam t s := by
  classical
  let E := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  let T := (halfCellArrayLatticeBox L z).preimage E E.injective.injOn
  rw [tsum_integral_resProfile_e2 T _ _ J hC _ t s, ← integral_const_mul]
  · apply integral_congr_ae
    apply ae_of_all
    intro lam
    dsimp only
    unfold filtCellSymbol filtRes
    rw [← mul_assoc]
    congr 2
    refine tsum_congr fun θ => ?_
    ring
  · intro θ hθ
    by_contra hn
    have hh := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
    apply hθ
    apply Finset.mem_preimage.mpr
    exact mem_halfCellArrayLatticeBox hL z β γ' (E θ) hh

/-- **Finite profile families commute with the filtered half-cell sum** (main's
`halfCell_finite_profiles_eq_physicalSymbols` with the filters). -/
theorem halfCell_finite_profiles_eq_filtSymbols {n : ℕ} {I : Type*} [Fintype I]
    {L : ℝ} (hL : 0 < L) (δ γ : ℝ) (t : Fin 2 → ℝ) (ψ : Fin n → ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : I → Finset (Fin n))
    (C : (i : I) → ({j : Fin n // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, SymReg (C i)) (v : I → ℂ) :
    (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*
      (∑' θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ),
        halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2)*
        ((∏ j, ψ j (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ j)) *
          (((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)*
          ∑ i, v i*∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
            (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ)*e2 lam (t 0) (t 1)))) =
    ∑ i, v i*pairedInverseProfile
      (fun lam => filtCellSymbol L δ γ ψ z β γ' (J i) (C i) lam) t := by
  classical
  let E := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  let A := fun θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ) =>
    halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2)
  let p := fun θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ) =>
    ((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)
  let P := fun θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ) =>
    ∏ j, ψ j (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ j)
  let T := fun (i : I) (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) =>
    ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
      (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ)*e2 lam (t 0) (t 1)
  let R := fun (i : I) θ => ((p θ*A θ)*P θ)*T i θ
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)
  have hs (i : I) : Summable (fun θ => v i*R i θ) := by
    apply (summable_halfCell_lattice_pullback hL z β γ' E E.injective
      (fun θ => v i*p θ*P θ*T i θ)).congr
    intro θ
    rw [show E θ = ((fun j => (θ j).1),(fun j => (θ j).2)) from rfl]
    change A θ*(v i*p θ*P θ*T i θ) = v i*(((p θ*A θ)*P θ)*T i θ)
    ring
  have he (θ) : A θ*(P θ*(p θ*∑ i, v i*T i θ)) = ∑ i, v i*R i θ := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change A θ*(P θ*(p θ*(v i*T i θ))) = v i*(((p θ*A θ)*P θ)*T i θ)
    ring
  change q*(∑' θ, A θ*(P θ*(p θ*∑ i, v i*T i θ))) = _
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun i _ => hs i),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [tsum_mul_left]
  have ht := filt_temporal_interchange hL δ γ (t 0) (t 1) ψ z β γ' (J i) (hC i)
  change q*(∑' θ, R i θ) = pairedInverseProfile
    (fun lam => filtCellSymbol L δ γ ψ z β γ' (J i) (C i) lam) t at ht
  calc
    q*(v i*(∑' θ, R i θ)) = v i*(q*(∑' θ, R i θ)) := by ring
    _ = _ := by rw [ht]

/-- **The twisted, filtered cell identity of a layer-zero couple.** -/
theorem couple_filt_cell_symbols {η A : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (Q : RegCpl) (hwf : Q.wf = true) :
    ∃ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ RA1Leafwise.markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) A
        (C0 (1-η/8) (η/4) (1-η/2)^(2*Q.size+1)) (C Z)) ∧
      ∀ (d K M : ℕ) (F : Fin (2*Q.links.length+1) → Mom d → ℂ) (B : ℝ), d+1 ≤ K → 0 ≤ B →
      (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B) →
      ∀ (L γ δ : ℝ) (LG : LayeredGarden 2) (_h0 : ∀ a, LG.layer a = 0)
        (hQ : Q.Decodes LG.garden), 0 < L → 0 < δ →
      ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, ∀ k : Mom d,
      ∀ (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
        Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) (u : SourceCellIndex S)
        (ν : PairedMomentum d Q.links.length) (φ : Fin Q.links.length → ℝ → ℂ),
      (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)*
        (∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
          (((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) * FiltSrc.arrayFiltWeight L φ p) *
            RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k p) *
            (coupleMomentumData hQ hQ.1).sourceCellWeight F S k
              (fun i j => latticePoint L (p (i,j))) u) =
      ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
        sourceRootMask u.1 k *
          ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ) *
            RA1Leafwise.leafSpectrumCoefficient F u.1 α *
            ∑ Z : (chosenSet Q.links).powerset,
              (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
                pairedInverseProfile (fun lam => filtCellSymbol L δ γ (profFilt (L^(2*γ)*(2*δ)) φ) u.2.val
                  (shiftL (fun j => sourceFrequencyPullback hQ hQ.1 (fun a => toLp 2 (α a)) (some (j,0))) ν 0)
                  (shiftL (fun j => sourceFrequencyPullback hQ hQ.1 (fun a => toLp 2 (α a)) (some (j,1))) ν 1)
                  (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam) ![t,s]) := by
  classical
  obtain ⟨C,hC,_hclass,hpoint⟩ := RA1Leafwise.couple_lattice_profiles_classified hη hη2 hA Q hwf
  refine ⟨C,hC,?_⟩
  intro d K M F B hK hB hF L γ δ LG h0 hQ hL hδ t ht s hs k S u ν φ
  have hμ : L^(2*γ)*(2*δ) ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hL _) (by linarith)).ne'
  rw [RA1Leafwise.sourceCell_lattice_eq_masked_leafSpectrum hQ hQ.1 hK hB hF hL S u k
    (fun p => ((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) * FiltSrc.arrayFiltWeight L φ p) *
      RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k p), ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  let β := fun j => sourceFrequencyPullback hQ hQ.1 (fun a => toLp 2 (α a)) (some (j,0))
  let γ' := fun j => sourceFrequencyPullback hQ hQ.1 (fun a => toLp 2 (α a)) (some (j,1))
  let E := Equiv.arrowProdEquivProdArrow (Fin Q.links.length)
    (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  let H := fun p => FiltSrc.arrayFiltWeight L φ p * RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k p
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*Q.links.length):ℝ):ℂ)
  have harr (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) :
      (RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm (E θ) =
        RA1Leafwise.linkPairArrayEquiv Q.links.length (Fin d → ℤ) θ := by
    change RA1Leafwise.linkPairArrayEquiv Q.links.length (Fin d → ℤ) (E.symm (E θ)) = _
    rw [E.symm_apply_apply]
  have htw : (∑' g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ),
      halfCellAmplitude u.2.val β γ' (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j))*
        (((Real.fourierChar (inner ℝ ν (pairedLattice L
          ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g))) : ℂ) *
            FiltSrc.arrayFiltWeight L φ ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g)) *
          RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k
            ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g))) =
      ∑' g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ),
      halfCellAmplitude u.2.val (shiftL β ν 0) (shiftL γ' ν 1) (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j))*
        H ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g) := by
    refine tsum_congr fun g => ?_
    rw [← halfCellAmplitude_char u.2.val β γ' ν L g]
    simp only [H]
    ring
  have hfreq : q*(∑' g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ),
      halfCellAmplitude u.2.val (shiftL β ν 0) (shiftL γ' ν 1) (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j))*
        H ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g)) =
      ∑ Z : (chosenSet Q.links).powerset,
        (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
          pairedInverseProfile (fun lam => filtCellSymbol L δ γ (profFilt (L^(2*γ)*(2*δ)) φ) u.2.val
            (shiftL β ν 0) (shiftL γ' ν 1)
            (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam) ![t,s] := by
    rw [← E.tsum_eq]
    have he (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) :
        H ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm (E θ)) =
        (∏ j, profFilt (L^(2*γ)*(2*δ)) φ j (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ j)) *
        (((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)*
          ∑ Z : (chosenSet Q.links).powerset,
            (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
              ∫ lam, ApproxNT.resProfile (RA1Leafwise.markedLinkIndices Q Z.val)
                (fun Ω => C Z (ofLp Ω) lam) (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ)*e2 lam t s) := by
      simp only [H]
      rw [harr, arrayFiltWeight_linkPair hμ L φ θ, hpoint d L γ δ LG h0 hQ t ht s hs k θ]
    simp_rw [he]
    exact halfCell_finite_profiles_eq_filtSymbols hL δ γ ![t,s] (profFilt (L^(2*γ)*(2*δ)) φ) u.2.val
      (shiftL β ν 0) (shiftL γ' ν 1)
      (fun Z => RA1Leafwise.markedLinkIndices Q Z.val) C (fun Z => (hC Z).reg)
      (fun Z => ∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)
  rw [← htw] at hfreq
  let R : ℂ := ∑' g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ),
    halfCellAmplitude u.2.val β γ' (fun j => latticePoint L (g.1 j))
      (fun j => latticePoint L (g.2 j))*
      (((Real.fourierChar (inner ℝ ν (pairedLattice L
          ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g))) : ℂ) *
          FiltSrc.arrayFiltWeight L φ ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g)) *
        RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k
          ((RA1Leafwise.latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g))
  change q*R = _ at hfreq
  change q*(sourceRootMask u.1 k*((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*
    RA1Leafwise.leafSpectrumCoefficient F u.1 α*R)) = _
  calc
    _ = sourceRootMask u.1 k*((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*
        RA1Leafwise.leafSpectrumCoefficient F u.1 α*(q*R)) := by ring
    _ = _ := by rw [hfreq]

/-- The whole filtered physical scalar of a couple (all coefficient sets). -/
@[expose] def filtScalar (L δ γ : ℝ) (Q : RegCpl) (ζ : ℂ)
    (C : (Z : (chosenSet Q.links).powerset) →
      ({j : Fin Q.links.length // j ∉ RA1Leafwise.markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ)
    (ψ : Fin Q.links.length → ℝ → ℂ) (lam : ℝ × ℝ) (β γ' : Fin Q.links.length → Mom d)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) : ℂ :=
  ζ * ∑ Z : (chosenSet Q.links).powerset,
    (∏ a ∈ Z.val, ((Cancel.zetaA a:ℂ)*Real.pi*Complex.I)⁻¹) *
      filtCellSymbol L δ γ ψ z β γ' (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam

/-- The whole filtered scalar at modulations shifted by a link frequency. -/
@[expose] def filtScalarν (L δ γ : ℝ) (Q : RegCpl) (ζ : ℂ)
    (C : (Z : (chosenSet Q.links).powerset) →
      ({j : Fin Q.links.length // j ∉ RA1Leafwise.markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ)
    (ψ : Fin Q.links.length → ℝ → ℂ) (ν : PairedMomentum d Q.links.length) (lam : ℝ × ℝ)
    (β γ' : Fin Q.links.length → Mom d) (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) : ℂ :=
  filtScalar L δ γ Q ζ C ψ lam (shiftL β ν 0) (shiftL γ' ν 1) z

theorem stronglyMeasurable_filtScalar_joint (Q : RegCpl) {L : ℝ} (hL : 0 < L) (δ γ : ℝ) (ζ : ℂ)
    (C : (Z : (chosenSet Q.links).powerset) →
      ({j : Fin Q.links.length // j ∉ RA1Leafwise.markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ Z, StronglyMeasurable (Function.uncurry (C Z))) (ψ : Fin Q.links.length → ℝ → ℂ)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) :
    StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) =>
        filtScalar L δ γ Q ζ C ψ p.1 p.2.1 p.2.2 z) := by
  classical
  unfold filtScalar
  apply StronglyMeasurable.const_mul
  apply Finset.stronglyMeasurable_fun_sum
  intro Z _
  exact (stronglyMeasurable_filtCellSymbol_joint hL δ γ ψ _ (hC Z) z).const_mul _

/-- **The character-twisted, filtered global identity of a layer-zero couple.** -/
theorem couple_filt_global {η A : ℝ} (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (Q : RegCpl) (hwf : Q.wf = true) :
    ∃ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ RA1Leafwise.markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) A
        (C0 (1-η/8) (η/4) (1-η/2)^(2*Q.size+1)) (C Z)) ∧
      ∀ (d K M : ℕ) (H : LGSpine.LeafProfiles 2 d) (Binput Ccover L γ δ : ℝ) (LG : LayeredGarden 2)
        (_h0 : ∀ a, LG.layer a = 0) (hQ : Q.Decodes LG.garden),
      d+1 ≤ K → 2*d ≤ M → 0 ≤ Binput →
      (∀ a, Fourier.spatialNorm K M (RA1Leafwise.leafFam hQ hQ.1 H a) ≤ ENNReal.ofReal Binput) → 1 ≤ L →
      0 < δ →
      ∀ (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
        Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)),
      (∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length) →
      (∀ c k x, (coupleMomentumData hQ hQ.1).inputCellWeight c k x ≠ 0 →
        ∀ z, halfCellArrayWeight z (fun p : Fin Q.links.length × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c) →
      ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, ∀ (k : Mom d) (ν : PairedMomentum d Q.links.length)
        (φ : Fin Q.links.length → ℝ → ℂ) (Bφ : ℝ), (∀ j u, ‖φ j u‖ ≤ Bφ) →
      (∀ Z : (chosenSet Q.links).powerset, Integrable (fun q => RA1Leafwise.maskedLeafScalarDensity hQ hQ.1
        (fun lam β γ' z => filtCellSymbol L δ γ (profFilt (L^(2*γ)*(2*δ)) φ) z (shiftL β ν 0) (shiftL γ' ν 1)
          (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam) (RA1Leafwise.leafFam hQ hQ.1 H) S q k)
        (volume.prod (RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)))) →
      (coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
        ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
          (((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) * FiltSrc.arrayFiltWeight L φ p) *
            RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k p) *
          (coupleMomentumData hQ hQ.1).sourceLeafWeight (RA1Leafwise.leafFam hQ hQ.1 H) k
            (fun i j => latticePoint L (p (i,j))) =
      RA1Leafwise.sourceScalarProfile hQ hQ.1
        (filtScalarν L δ γ Q LG.garden.zeta C (profFilt (L^(2*γ)*(2*δ)) φ) ν)
        (RA1Leafwise.leafFam hQ hQ.1 H) S ![t,s] k := by
  classical
  obtain ⟨C,hC,hcell⟩ := couple_filt_cell_symbols hη hη2 hA Q hwf
  refine ⟨C,hC,?_⟩
  intro d K M H Binput Ccover L γ δ LG h0 hQ hK hM hBi hF hL hδ S hcard hcover t ht s hs k ν φ Bφ hφ hi
  have hLpos : 0 < L := by linarith
  have horder : LG.garden.order = 2*Q.links.length := by
    rw [Reg.size_eq_order hQ]
    have hh := couple_linksAt_length Q ((0:Fin 2),[]) (1,[])
    simpa only [RegCpl.links,Nat.mul_comm] using hh.symm
  have hbH : ∀ p, ‖((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) * FiltSrc.arrayFiltWeight L φ p) *
      RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k p‖ ≤ Bφ^Q.links.length := by
    intro p
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul]
    have h1 := FiltSrc.norm_arrayFiltWeight_le L φ hφ p
    have h2 := RA1Leafwise.norm_coupleLatticeTimeCoefficient_le_one L γ δ LG h0 hQ ht.2 hs.2 k p
    calc _ ≤ Bφ^Q.links.length * 1 := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = _ := mul_one _
  rw [source_lattice_eq_tsum_cells (coupleMomentumData hQ hQ.1) (RA1Leafwise.leafFam hQ hQ.1 H) S k
    (fun c x => hcover c k x) hcard hL hK hM hBi hF _ hbH]
  have hlocal (u : SourceCellIndex S) := hcell d K M (RA1Leafwise.leafFam hQ hQ.1 H) Binput
    (by omega) hBi hF L γ δ LG h0 hQ hLpos hδ t ht s hs k S u ν φ
  have hrec := RA1Leafwise.masked_source_profiles_recombine hQ hQ.1
    (fun Z lam β γ' z => filtCellSymbol L δ γ (profFilt (L^(2*γ)*(2*δ)) φ) z (shiftL β ν 0) (shiftL γ' ν 1)
      (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam)
    (fun Z => ∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)
    (RA1Leafwise.leafFam hQ hQ.1 H) S k hi ![t,s]
  have he : (coupling d L γ δ:ℂ)^(2*Q.links.length)*
      (∑' u : SourceCellIndex S, ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
        (((Real.fourierChar (inner ℝ ν (pairedLattice L p)) : ℂ) * FiltSrc.arrayFiltWeight L φ p) *
          RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ t s k p) *
          (coupleMomentumData hQ hQ.1).sourceCellWeight (RA1Leafwise.leafFam hQ hQ.1 H) S k
            (fun i j => latticePoint L (p (i,j))) u) =
      ∑ Z : (chosenSet Q.links).powerset,
        (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
          RA1Leafwise.sourceScalarProfile hQ hQ.1
            (fun lam β γ' z => filtCellSymbol L δ γ (profFilt (L^(2*γ)*(2*δ)) φ) z (shiftL β ν 0)
              (shiftL γ' ν 1) (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam)
            (RA1Leafwise.leafFam hQ hQ.1 H) S ![t,s] k := by
    rw [← tsum_mul_left]
    simp only [coupling,← Complex.ofReal_pow]
    simp_rw [hlocal]
    exact hrec
  rw [horder, mul_assoc, mul_left_comm ((coupling d L γ δ:ℂ)^(2*Q.links.length)) LG.garden.zeta, he]
  let R : (chosenSet Q.links).powerset → (ℝ × ℝ) →
      (Fin Q.links.length → Mom d) → (Fin Q.links.length → Mom d) →
      ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ := fun Z lam β γ' z =>
    (∏ a ∈ Z.val, ((Cancel.zetaA a:ℂ)*Real.pi*Complex.I)⁻¹) *
      filtCellSymbol L δ γ (profFilt (L^(2*γ)*(2*δ)) φ) z (shiftL β ν 0) (shiftL γ' ν 1)
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

end WaveTurbulence.Flower.FiltCoh
