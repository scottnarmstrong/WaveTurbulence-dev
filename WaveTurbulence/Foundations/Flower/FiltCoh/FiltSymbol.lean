/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.FiltWickRep
public import WaveTurbulence.Foundations.Flower.FiltCoh.SymbolEnvelope
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeWickRemainderIdentity

/-! # FILT-COH (d2c): the filtered physical cell symbol and its Wick slices

`filtCellSymbol L δ γ ψ z β γ' J C λ` is main's physical cell symbol (`physicalWeightedCellSymbol`: the normalized
local NT sum with the squared Wick factors at energy `2δ`) with the link filters `∏_j ψ_j(Ω_j)` in the profile
(`filtRes`). It is what the resonance filters of a coherent object produce in the cell identity (o82 Prop. 15.1).

* `filtCellSymbol_eq_sum_add_wick`: the normalized NT sum with the filtered profile plus `4^{-n}` times the
  filtered Wick correction (main's `physicalWeightedCellSymbol_decomposition`, leading term not split off);
* `filtWickCorrection_eq_sum`, `filtWickSlice_eq_zero_of_not_disjoint`, `norm_filtWickCorrection_le_sum`: main's
  inclusion–exclusion over the Wick patterns;
* `tsum_filtWickSlice_eq_traced_NT`, `norm_filtWickSlice_le_traced_NT`: on a Wick slice the traced energies vanish,
  so their filters are the constants `ψ_j(0)`; the survivors carry the relabelled filters `wickSurvivorFilt`;
* `stronglyMeasurable_filtCellSymbol_joint`; `filtCellSymbol_eq_tree` (the tree scalar form with weight
  `∏ψ · treeWickArrayWeight`).

Proofs adapted from main's `PhysicalLocalSymbol`, `WickCorrectionExpansion`, `WickSliceNTIdentity`,
`WickNormalizedSlice`, `WickCorrectionEnvelope`, `WickSliceMeasurable` (sha256 in COPIED-SHA256SUMS). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links
open scoped ENNReal

variable {d : ℕ}

/- The world's closure contains `Mole.instFintypePositionCode` (a classical `Fintype (D → Fin 4)`), which would make
`univ : Finset (Fin n → Fin 4)` differ from main's Wick statements; use the standard instance. -/
attribute [-instance] WaveTurbulence.Mole.instFintypePositionCode

/-- **The filtered physical cell symbol.** -/
@[expose] def filtCellSymbol {n : ℕ} (L δ γ : ℝ) (ψ : Fin n → ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) : ℂ :=
  (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
    ∑' θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ),
      ((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ) *
        (halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2) *
          filtRes J (fun Ω => C (ofLp Ω) lam) ψ (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ))

/-- The filtered Wick correction (normalization and energy at the same `δ`). -/
@[expose] def filtWickCorrection {n : ℕ} (L δ γ : ℝ) (ψ : Fin n → ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) : ℂ :=
  (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
    ∑' θ, (((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)-1) *
      (halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2) *
        filtRes J (fun Ω => C (ofLp Ω) lam) ψ (wickLatticeEnergy L (L^(2*γ)*δ) θ))

/-- One filtered Wick slice. -/
@[expose] def filtWickSlice {n : ℕ} (L δ γ : ℝ) (σ : Fin n → Fin 4) (ψ : Fin n → ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) : ℂ :=
  (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
    ∑' θ, (∏ j, wickPatternTerm θ j (σ j)) *
      (halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2) *
        filtRes J (fun Ω => C (ofLp Ω) lam) ψ (wickLatticeEnergy L (L^(2*γ)*δ) θ))

/-- The filters of the surviving links of a Wick pattern, relabelled. -/
@[expose] def wickSurvivorFilt {n : ℕ} (σ : Fin n → Fin 4) (ψ : Fin n → ℝ → ℂ) :
    Fin (Fintype.card {j : Fin n // j ∉ wickTracedLinks σ}) → ℝ → ℂ :=
  fun i => ψ ((wickSurvivorEquiv σ).symm i).val

theorem filtCellSymbol_one {n : ℕ} (L δ γ : ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) :
    filtCellSymbol L δ γ (fun _ _ => 1) z β γ' J C lam = physicalWeightedCellSymbol L δ γ z β γ' J C lam := by
  simp only [filtCellSymbol, physicalWeightedCellSymbol, filtRes_one]

/-- **Decomposition**: filtered NT sum at energy `2δ` plus the filtered Wick correction. -/
theorem filtCellSymbol_eq_sum_add_wick {n : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ) (ψ : Fin n → ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) :
    filtCellSymbol L δ γ ψ z β γ' J C lam =
      (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ') (filtRes J (fun Ω => C (ofLp Ω) lam) ψ) +
      ((4:ℂ)^n)⁻¹ * filtWickCorrection L (2*δ) γ ψ z β γ' J C lam := by
  let E := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  let W := fun θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ) =>
    halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2)*
      filtRes J (fun Ω => C (ofLp Ω) lam) ψ (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ)
  let p := fun θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ) =>
    ((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)
  have hs : Summable W := summable_halfCell_lattice_pullback hL z β γ' E E.injective
    (fun θ => filtRes J (fun Ω => C (ofLp Ω) lam) ψ (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ))
  have hp : Summable (fun θ => p θ*W θ) := by
    apply (summable_halfCell_lattice_pullback hL z β γ' E E.injective
      (fun θ => p θ*filtRes J (fun Ω => C (ofLp Ω) lam) ψ
        (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ))).congr
    intro θ
    rw [show E θ = ((fun j => (θ j).1),(fun j => (θ j).2)) from rfl]
    dsimp only [W]
    ring
  have hc : (∑' θ, (p θ-1)*W θ) = (∑' θ, p θ*W θ)-(∑' θ, W θ) := by
    rw [← hp.tsum_sub hs]
    apply tsum_congr
    intro θ
    ring
  have ha : (∑' θ, W θ) = approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ')
      (filtRes J (fun Ω => C (ofLp Ω) lam) ψ) := by
    exact E.tsum_eq (fun g => halfCellAmplitude z β γ'
      (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j))*
        filtRes J (fun Ω => C (ofLp Ω) lam) ψ
          (fun j => (L^(2*γ)*(2*δ))*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j))))
  have hq := doubled_coupling_prefactor n d L δ γ
  have h4 : (4:ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold filtCellSymbol filtWickCorrection
  change _ * (∑' θ, p θ * W θ) = _ + _ * (_ * ∑' θ, (p θ - 1) * W θ)
  rw [hc, ← ha, hq]
  field_simp
  ring

/-- Generic: a Wick slice vanishes when its profile vanishes on the pattern plane. -/
theorem wick_slice_tsum_zero {n : ℕ} (L : ℝ) (σ : Fin n → Fin 4) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ' : Fin n → Mom d) (P : (Fin n → (Fin d → ℤ) × (Fin d → ℤ)) → ℂ)
    (hP : ∀ u : WickPatternCoordinates d σ, P (wickPatternInsert σ u) = 0) :
    (∑' θ, (∏ j, wickPatternTerm θ j (σ j)) *
      (halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2) * P θ)) = 0 := by
  rw [tsum_wickPatternTerm_mul σ (fun θ =>
    halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2) * P θ)]
  have he : ∀ u : WickPatternCoordinates d σ,
      halfCellAmplitude z β γ' (fun j => latticePoint L (wickPatternInsert σ u j).1)
        (fun j => latticePoint L (wickPatternInsert σ u j).2) * P (wickPatternInsert σ u) = 0 :=
    fun u => by rw [hP u, mul_zero]
  rw [tsum_congr he, tsum_zero, mul_zero]

/-- Generic inclusion–exclusion of the Wick correction for an arbitrary lattice profile. -/
theorem wick_corr_tsum_expand {n : ℕ} {L : ℝ} (hL : 0 < L) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ' : Fin n → Mom d) (P : (Fin n → (Fin d → ℤ) × (Fin d → ℤ)) → ℂ) :
    (∑' θ, (((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)-1) *
      (halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2) * P θ)) =
      ∑ σ ∈ ((univ : Finset (Fin n → Fin 4)).erase 0), ∑' θ, (∏ j, wickPatternTerm θ j (σ j)) *
        (halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2) * P θ) := by
  let E := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  have hs (σ : Fin n → Fin 4) : Summable (fun θ => (∏ j, wickPatternTerm θ j (σ j)) *
      (halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2) * P θ)) := by
    refine (summable_halfCell_lattice_pullback hL z β γ' E E.injective
      (fun θ => (∏ j, wickPatternTerm θ j (σ j)) * P θ)).congr fun θ => ?_
    change halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2)*
        ((∏ j, wickPatternTerm θ j (σ j))*P θ) = (∏ j, wickPatternTerm θ j (σ j)) *
      (halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2) * P θ)
    ring
  simp_rw [wick_difference_inclusion_exclusion,Finset.sum_mul]
  exact Summable.tsum_finsetSum (fun σ _ => hs σ)

/-- A pattern meeting a special energy contributes identically zero. -/
theorem filtWickSlice_eq_zero_of_not_disjoint {n : ℕ} (L δ γ : ℝ) (σ : Fin n → Fin 4) (ψ : Fin n → ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) (h : ¬Disjoint (wickTracedLinks σ) J) :
    filtWickSlice L δ γ σ ψ z β γ' J C lam = 0 := by
  unfold filtWickSlice
  rw [wick_slice_tsum_zero L σ z β γ' _ (fun u => by
    rw [filtRes, resProfile_wickPatternInsert_eq_zero L (L^(2*γ)*δ) σ u J _ h, zero_mul]), mul_zero]

/-- Inclusion–exclusion over the Wick patterns. -/
theorem filtWickCorrection_eq_sum {n : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ) (ψ : Fin n → ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) :
    filtWickCorrection L δ γ ψ z β γ' J C lam =
      ∑ σ ∈ ((univ : Finset (Fin n → Fin 4)).erase 0), filtWickSlice L δ γ σ ψ z β γ' J C lam := by
  unfold filtWickCorrection filtWickSlice
  rw [wick_corr_tsum_expand hL z β γ'
    (fun θ => filtRes J (fun Ω => C (ofLp Ω) lam) ψ (wickLatticeEnergy L (L^(2*γ)*δ) θ)), Finset.mul_sum]

/-- Only the admissible patterns contribute. -/
theorem norm_filtWickCorrection_le_sum {n : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ) (ψ : Fin n → ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) :
    ‖filtWickCorrection L δ γ ψ z β γ' J C lam‖ ≤
      ∑ σ : {σ // σ ∈ wickAdmissiblePatterns J}, ‖filtWickSlice L δ γ σ.val ψ z β γ' J C lam‖ := by
  have he : filtWickCorrection L δ γ ψ z β γ' J C lam =
      ∑ σ ∈ wickAdmissiblePatterns J, filtWickSlice L δ γ σ ψ z β γ' J C lam := by
    rw [filtWickCorrection_eq_sum hL, wickAdmissiblePatterns]
    refine (Finset.sum_filter_of_ne fun σ _ hne => ?_).symm
    by_contra h
    exact hne (filtWickSlice_eq_zero_of_not_disjoint L δ γ σ ψ z β γ' J C lam h)
  rw [he, Finset.sum_subtype (wickAdmissiblePatterns J) (fun _ => Iff.rfl)]
  exact norm_sum_le _ _

/-- On a Wick slice the filters of the traced links are constant and the survivors are relabelled. -/
theorem prod_filt_wickPatternInsert {n : ℕ} (L μ : ℝ) (σ : Fin n → Fin 4) (ψ : Fin n → ℝ → ℂ)
    (u : WickPatternCoordinates d σ) :
    ∏ j, ψ j (wickLatticeEnergy L μ (wickPatternInsert σ u) j) =
      (∏ j ∈ wickTracedLinks σ, ψ j 0) *
        ∏ i, wickSurvivorFilt σ ψ i (μ*inner ℝ (latticePoint L (u.1 ((wickSurvivorEquiv σ).symm i)).1)
          (latticePoint L (u.1 ((wickSurvivorEquiv σ).symm i)).2)) := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun j : Fin n => σ j = 0), mul_comm]
  congr 1
  · have h1 : ∀ i : {j : Fin n // ¬ σ j = 0},
        ψ i.val (wickLatticeEnergy L μ (wickPatternInsert σ u) i.val) = ψ i.val 0 := fun i => by
      rw [wickLatticeEnergy_insert_zero L μ σ u (by simpa [wickTracedLinks] using i.2)]
    rw [Finset.prod_congr rfl (fun i _ => h1 i)]
    exact (Finset.prod_subtype (wickTracedLinks σ) (fun j => by simp [wickTracedLinks]) (fun j => ψ j 0)).symm
  · rw [← (wickSurvivorEquiv σ).symm.prod_comp]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [wickSurvivorFilt, wickLatticeEnergy, wickPatternInsert,
      dite_eq_left ((wickSurvivorEquiv σ).symm i).property]

/-- **The exact identity of one filtered Wick slice.** -/
theorem tsum_filtWickSlice_eq_traced_NT {n : ℕ} {L : ℝ} (hL : 0 < L) (μ : ℝ)
    (σ : Fin n → Fin 4) (ψ : Fin n → ℝ → ℂ) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (J : Finset (Fin n)) (h : Disjoint (wickTracedLinks σ) J)
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) :
    (∑' θ, (∏ j, wickPatternTerm θ j (σ j)) *
      (halfCellAmplitude z β γ (fun j => latticePoint L (θ j).1)
        (fun j => latticePoint L (θ j).2) *
        filtRes J (fun Ω => C (WithLp.ofLp Ω) lam) ψ (wickLatticeEnergy L μ θ))) =
      (∏ j, wickPatternCoefficient (σ j)) *
        (∑ v ∈ wickFreeLatticeBox L σ z, wickTracedAmplitude L σ z β γ v) *
        ((∏ j ∈ wickTracedLinks σ, ψ j 0) *
          approxSum L μ
            (halfCellAmplitude (fun p => z (((wickSurvivorEquiv σ).symm p.1).val,p.2))
              (fun i => β ((wickSurvivorEquiv σ).symm i).val)
              (fun i => γ ((wickSurvivorEquiv σ).symm i).val))
            (filtRes (survivingSpecial (wickTracedLinks σ) J)
              (fun Ω => survivingTraceCoefficient (wickTracedLinks σ) J h C (WithLp.ofLp Ω) lam)
              (wickSurvivorFilt σ ψ))) := by
  classical
  rw [tsum_wickPattern_halfCell_eq_sum_free hL,mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  calc
    _ = wickTracedAmplitude L σ z β γ v * ((∏ j ∈ wickTracedLinks σ, ψ j 0) *
        (∑' a : {j : Fin n // σ j = 0} → (Fin d → ℤ) × (Fin d → ℤ),
          (∏ j, wickLinkAmplitude L z β γ j.val (a j)) *
            filtRes (survivingSpecial (wickTracedLinks σ) J)
              (fun Ω => survivingTraceCoefficient (wickTracedLinks σ) J h C (WithLp.ofLp Ω) lam)
              (wickSurvivorFilt σ ψ)
              (fun i => μ*inner ℝ (latticePoint L (a ((wickSurvivorEquiv σ).symm i)).1)
                (latticePoint L (a ((wickSurvivorEquiv σ).symm i)).2)))) := by
      rw [← tsum_mul_left, ← tsum_mul_left]
      apply tsum_congr
      intro a
      rw [halfCellAmplitude_wickPatternInsert, filtRes, filtRes,
        resProfile_wickPatternInsert L μ σ (a,v) J h C lam, prod_filt_wickPatternInsert L μ σ ψ (a,v)]
      ring
    _ = _ := by rw [tsum_wickSurvivor_eq_approxSum]

/-- **The norm of one filtered Wick slice**: the traced filters cost `Bψ^{|T|}`. -/
theorem norm_filtWickSlice_le_traced_NT {n : ℕ} {L : ℝ} (hL : 1 ≤ L) (δ γexp : ℝ) (hδ : 0 ≤ δ)
    (σ : Fin n → Fin 4) (ψ : Fin n → ℝ → ℂ) {Bψ : ℝ} (hBψ : ∀ j, ‖ψ j 0‖ ≤ Bψ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (J : Finset (Fin n)) (h : Disjoint (wickTracedLinks σ) J)
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) :
    ‖filtWickSlice L δ γexp σ ψ z β γ J C lam‖ ≤
      2^n * (2^d*L^d)^(wickTracedLinks σ).card * Bψ^(wickTracedLinks σ).card *
      (δ/(2*L^((d:ℝ)-γexp)))^(2*(wickTracedLinks σ).card) *
      ‖(((δ/(2*L^((d:ℝ)-γexp)))^(2*Fintype.card {j : Fin n // j ∉ wickTracedLinks σ}):ℝ):ℂ)*
        approxSum L (L^(2*γexp)*δ)
          (halfCellAmplitude (fun p => z (((wickSurvivorEquiv σ).symm p.1).val,p.2))
            (fun i => β ((wickSurvivorEquiv σ).symm i).val)
            (fun i => γ ((wickSurvivorEquiv σ).symm i).val))
          (filtRes (survivingSpecial (wickTracedLinks σ) J)
            (fun Ω => survivingTraceCoefficient (wickTracedLinks σ) J h C (WithLp.ofLp Ω) lam)
            (wickSurvivorFilt σ ψ))‖ := by
  have hm := card_untraced_add_trace (wickTracedLinks σ)
  have hP : ‖∏ j ∈ wickTracedLinks σ, ψ j 0‖ ≤ Bψ^(wickTracedLinks σ).card := by
    refine (Finset.norm_prod_le _ _).trans ?_
    calc ∏ j ∈ wickTracedLinks σ, ‖ψ j 0‖ ≤ ∏ _j ∈ wickTracedLinks σ, Bψ :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hBψ j)
      _ = _ := Finset.prod_const _
  unfold filtWickSlice
  rw [tsum_filtWickSlice_eq_traced_NT (zero_lt_one.trans_le hL) _ σ ψ z β γ J h C lam]
  rw [show ∀ a b c e : ℂ, a * b * (c * e) = (a * b * c) * e from fun a b c e => by ring,
    norm_normalized_trace_product (by positivity : 0 ≤ δ/(2*L^((d:ℝ)-γexp))) _ _ hm, norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul (mul_le_mul (norm_wickPatternCoefficient_prod_le σ)
    (norm_sum_wickTracedAmplitude_le hL σ z β γ) (norm_nonneg _) (by positivity)) hP (norm_nonneg _)
    (by positivity)

/-- Generic joint measurability of a Wick-slice lattice series. -/
theorem measurable_wickSlice_tsum {n : ℕ} (L : ℝ) (σ : Fin n → Fin 4) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (P : (Fin n → (Fin d → ℤ) × (Fin d → ℤ)) → (ℝ × ℝ) → ℂ) (hP : ∀ θ, Measurable (P θ)) :
    Measurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      ∑' θ, (∏ j, wickPatternTerm θ j (σ j)) *
        (halfCellAmplitude z p.2.1 p.2.2 (fun j => latticePoint L (θ j).1)
          (fun j => latticePoint L (θ j).2) * P θ p.1)) := by
  apply Measurable.tsum
  intro θ
  have hb := (continuous_halfCellAmplitude_joint z).measurable
  have hm : Measurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      (p.2, ((fun j => latticePoint L (θ j).1), (fun j => latticePoint L (θ j).2)))) :=
    measurable_snd.prodMk measurable_const
  have h1 := hb.comp hm
  have h2 : Measurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) => P θ p.1) :=
    (hP θ).comp measurable_fst
  exact measurable_const.mul (h1.mul h2)

/-- Generic joint measurability of a half-cell NT sum with a measurable profile family. -/
theorem measurable_approxSum_halfCell {n : ℕ} (L μ : ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (Ψ : (ℝ × ℝ) → (Fin n → ℝ) → ℂ) (hΨ : ∀ Ω, Measurable (fun lam => Ψ lam Ω)) :
    Measurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      approxSum L μ (halfCellAmplitude z p.2.1 p.2.2) (Ψ p.1)) := by
  unfold approxSum
  apply Measurable.tsum
  intro g
  have hb := (continuous_halfCellAmplitude_joint z).measurable
  have hm : Measurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      (p.2, ((fun j => latticePoint L (g.1 j)), (fun j => latticePoint L (g.2 j))))) :=
    measurable_snd.prodMk measurable_const
  have h1 := hb.comp hm
  have h2 : Measurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      Ψ p.1 (fun j => μ * inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))) :=
    (hΨ _).comp measurable_fst
  exact h1.mul h2

theorem measurable_filtRes_lam {n : ℕ} (J : Finset (Fin n)) {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : StronglyMeasurable (Function.uncurry C)) (ψ : Fin n → ℝ → ℂ) (Ω : Fin n → ℝ) :
    Measurable (fun lam : ℝ × ℝ => filtRes J (fun Ω' => C (ofLp Ω') lam) ψ Ω) := by
  unfold filtRes resProfile
  refine Measurable.mul (measurable_const.mul ?_) measurable_const
  exact (hC.comp_measurable (measurable_const.prodMk measurable_id)).measurable

/-- Joint measurability of the filtered physical cell symbol. -/
theorem stronglyMeasurable_filtCellSymbol_joint {n : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ)
    (ψ : Fin n → ℝ → ℂ) (J : Finset (Fin n)) {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : StronglyMeasurable (Function.uncurry C)) (z : (Fin n × Fin 2) → Fin d → ℤ) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      filtCellSymbol L δ γ ψ z p.2.1 p.2.2 J C p.1) := by
  have hs := measurable_approxSum_halfCell L (L^(2*γ)*(2*δ)) z
    (fun lam => filtRes J (fun Ω => C (ofLp Ω) lam) ψ) (fun Ω => measurable_filtRes_lam J hC ψ Ω)
  have hw : Measurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      filtWickCorrection L (2*δ) γ ψ z p.2.1 p.2.2 J C p.1) := by
    simp_rw [filtWickCorrection_eq_sum hL]
    apply Finset.measurable_sum
    intro σ _
    unfold filtWickSlice
    exact measurable_const.mul (measurable_wickSlice_tsum L σ z
      (fun θ lam => filtRes J (fun Ω => C (ofLp Ω) lam) ψ (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ))
      (fun θ => measurable_filtRes_lam J hC ψ _))
  have he : (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      filtCellSymbol L δ γ ψ z p.2.1 p.2.2 J C p.1) =
      fun p => (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z p.2.1 p.2.2)
          (filtRes J (fun Ω => C (ofLp Ω) p.1) ψ) +
        ((4:ℂ)^n)⁻¹ * filtWickCorrection L (2*δ) γ ψ z p.2.1 p.2.2 J C p.1 := by
    funext p
    exact filtCellSymbol_eq_sum_add_wick hL δ γ ψ z p.2.1 p.2.2 J C p.1
  rw [he]
  exact ((hs.const_mul _).add (hw.const_mul _)).stronglyMeasurable

/-- The tree weight of the filters at the physical energy `2δ`. -/
@[expose] def treeFiltWeight {n : ℕ} (L δ γ : ℝ) (ψ : Fin n → ℝ → ℂ)
    (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) : ℂ :=
  (∏ j, ψ j ((L^(2*γ)*(2*δ))*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))) *
    RA1Leafwise.treeWickArrayWeight g

/-- **The filtered symbol in the tree scalar form.** -/
theorem filtCellSymbol_eq_tree {n : ℕ} (L δ γ : ℝ) (ψ : Fin n → ℝ → ℂ)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d) (lam : ℝ × ℝ) :
    filtCellSymbol L δ γ ψ z β γ' J C lam =
      (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        treeProfileArrayScalar L (2*δ*L^(2*γ)) (treeFiltWeight L δ γ ψ) z β γ' J C lam := by
  let E := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  unfold filtCellSymbol treeProfileArrayScalar treeHalfCellLatticeScalar
  congr 1
  rw [← E.symm.tsum_eq]
  apply tsum_congr
  intro g
  have hμ : 2*δ*L^(2*γ) = L^(2*γ)*(2*δ) := by ring
  have hE : E.symm g = fun j => (g.1 j, g.2 j) := rfl
  have hW : wickLatticeEnergy L (L^(2*γ)*(2*δ)) (fun j => (g.1 j, g.2 j)) =
      fun j => (L^(2*γ)*(2*δ)) * inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)) := rfl
  rw [hE, hW]
  simp only [treeFiltWeight, RA1Leafwise.treeWickArrayWeight_eq_epsXY, filtRes, hμ]
  ring

end WaveTurbulence.Flower.FiltCoh
