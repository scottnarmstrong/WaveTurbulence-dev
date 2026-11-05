/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.FiniteCellDecomposition
public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFrequencyRepresentation
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourcePhasePullback
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellAmplitude
public import WaveTurbulence.Foundations.Incoh.SpectralPhaseFactorization

/-! # Leaf-only Fourier inversion with the actual NT half-cell amplitude

The link cells are retained in physical space. Only the independent leaf
cells are inverted, so the NT Fourier budget requires one spatial moment.
-/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp

/-- Exact factorization of the actual leaf modulation into root and link characters. -/
theorem leaf_character_halfCell_eq {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (α : Fin (2*Q.links.length+1) → Fin d → ℝ) (k : Mom d)
    (x y : Fin Q.links.length → Mom d)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) :
    (∏ a, (Real.fourierChar (Fourier.timePairing d (α a)
      (ofLp ((coupleMomentumData hQ hG).inputMomentum k (fun j i => if i=0 then x j else y j) a))) : ℂ)) *
        halfCellArrayWeight z (fun p => if p.2=0 then x p.1 else y p.1) =
    (Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k) : ℂ) *
      halfCellAmplitude z
        (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0)))
        (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1))) x y := by
  classical
  simp_rw [timePairing_eq_inner]
  rw [← coe_fourierChar_sum,sum_inner_inputMomentum_eq_root_links hQ hG]
  simp only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false,
    AddChar.map_add_eq_mul,Circle.coe_mul,coe_fourierChar_sum,
    halfCellArrayWeight,Fintype.prod_prod_type,Fin.prod_univ_two,
    halfCellAmplitude,Circle.smul_def,smul_eq_mul,Finset.prod_mul_distrib]
  ring

/-- Actual leaf-only inversion, with all retained link cutoffs exactly the
half-cell amplitude to which the NT estimate has already been applied. -/
theorem leafCellProduct_halfCell_eq_frequencyIntegral {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B) (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B))
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ) (k : Mom d)
    (x y : Fin Q.links.length → Mom d)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) :
    (∏ a, leafCell (F a) (c a) ((coupleMomentumData hQ hG).inputMomentum k
      (fun j i => if i=0 then x j else y j) a)) *
        halfCellArrayWeight z (fun p => if p.2=0 then x p.1 else y p.1) =
    ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
      (Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k) : ℂ) *
        (∏ a, Fourier.timeFourier (fun v : Fin d → ℝ => leafCell (F a) (c a) (toLp 2 v)) (α a)) *
        halfCellAmplitude z
          (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0)))
          (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1))) x y := by
  rw [actual_leafCellProduct_eq_frequencyIntegral hQ hG hK hB hF c k,
    ← integral_mul_const]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  simp only [Circle.smul_def,smul_eq_mul,Finset.prod_mul_distrib]
  have hh := leaf_character_halfCell_eq hQ hG α k x y z
  calc
    _ = ((∏ a, (Real.fourierChar (Fourier.timePairing d (α a)
        (ofLp ((coupleMomentumData hQ hG).inputMomentum k (fun j i => if i=0 then x j else y j) a))) : ℂ)) *
          halfCellArrayWeight z (fun p => if p.2=0 then x p.1 else y p.1)) *
            (∏ a, Fourier.timeFourier (fun v : Fin d → ℝ => leafCell (F a) (c a) (toLp 2 v)) (α a)) := by ring
    _ = _ := by rw [hh]; ring

/-- The actual localized source product is a finite sum of leaf-only
spectral integrals. The geometric cell set is chosen before all root momenta. -/
theorem actual_leafOnly_spectral_decomposition (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      ∀ c : Fin (2*Q.links.length+1) → Fin d → ℤ,
      ∃ S : Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
        (S.card : ℝ) ≤ C^Q.links.length ∧
        ∀ K M : ℕ, ∀ B : ℝ, d+1 ≤ K → 0 ≤ B →
        ∀ F : Fin (2*Q.links.length+1) → Mom d → ℂ, (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B) →
        ∀ k : Mom d, ∀ x y : Fin Q.links.length → Mom d,
          coupleLeafCellProduct hQ hG F c k (fun j i => if i=0 then x j else y j) =
          ∑ z ∈ S, ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
            (Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k) : ℂ) *
              (∏ a, Fourier.timeFourier (fun v : Fin d → ℝ => leafCell (F a) (c a) (toLp 2 v)) (α a)) *
              halfCellAmplitude z
                (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0)))
                (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1))) x y := by
  obtain ⟨C,hC,h⟩ := actual_couple_finite_cell_decomposition d hd
  refine ⟨C,hC,?_⟩
  intro G Q hQ hG c
  obtain ⟨S,hS,hdec⟩ := h G Q hQ hG c
  refine ⟨S,hS,?_⟩
  intro K M B hK hB F hF k x y
  rw [hdec F k]
  apply Finset.sum_congr rfl
  intro z _
  exact leafCellProduct_halfCell_eq_frequencyIntegral hQ hG hK hB hF c k x y z

end WaveTurbulence.RA1Leafwise
