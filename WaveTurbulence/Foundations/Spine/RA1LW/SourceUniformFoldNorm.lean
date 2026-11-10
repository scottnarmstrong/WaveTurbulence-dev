/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceZeroLinks
public import WaveTurbulence.Foundations.RegAsymp.SpatialNormMonotone

/-! # Uniform geometric bounds on all complete actual source folds -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Reg TTree

/-- The original complete source fold has geometric full30d spatial
control for every code, including empty codes and arbitrary independent
placements. The constant is fixed before the code and every order cutoff. -/
theorem source_all_placed_fold_spatial_bound {d : ℕ} (hd : 3 ≤ d) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : RegCpl, ∀ (w : ℕ) (H : Fin w × Path → Mom d → ℝ),
      (∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal B) →
      ∀ (Z : Finset (Fin w × Path)) (a b : Fin w × Path), Indep a b →
      ∀ θ : Fin w × Path → Mom d × Mom d,
      Fourier.spatialNorm (30*d) (30*d) (fun k =>
        addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
          (fun θ => cplLeafProduct (addrFam H) θ Q a b k) θ) ≤
        ENNReal.ofReal (C*C^Q.links.length) := by
  obtain ⟨C,hC,hbound⟩ := source_placed_fold_spatial_bound hd hB
  let D := max C B
  have hCD : C ≤ D := le_max_left _ _
  have hBD : B ≤ D := le_max_right _ _
  have hD : 1 ≤ D := hC.trans hCD
  refine ⟨D,hD,?_⟩
  intro Q w H hF Z a b hab θ
  by_cases hn : 0 < Q.links.length
  · apply (hbound (Reg.decodedCouple Q) Q (Reg.decodedCouple_decodes Q)
      (Reg.decodedCouple_decodes Q).1 hn w H hF Z a b hab θ).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul hCD (pow_le_pow_left₀ (zero_le_one.trans hC) hCD _)
      (pow_nonneg (zero_le_one.trans hC) _) (zero_le_one.trans hD)
  · have hn0 : Q.links.length = 0 := by omega
    have hnil : Q.linksAt a b = [] := by
      rw [cpl_links_rootPlacement,List.eq_nil_of_length_eq_zero hn0,List.map_nil]
    have he : (fun k => addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
        (fun θ => cplLeafProduct (addrFam H) θ Q a b k) θ) = addrFam H a := by
      funext k
      rw [hnil,List.map_nil]
      exact cplLeafProduct_eq_input_of_links_nil (addrFam H) θ Q a b k hab hnil
    rw [he,hn0,pow_zero,mul_one]
    exact ((spatialNorm_mono (by omega) (by omega) (addrFam H a)).trans (hF a)).trans
      (ENNReal.ofReal_le_ofReal hBD)

end WaveTurbulence.RA1Leafwise
