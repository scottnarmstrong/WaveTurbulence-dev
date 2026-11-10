/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreeFam
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeLeadingGeometric
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeLeadingSingularExchange
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeOriginalSingular
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeCellCover
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeSpatialConstant
public import WaveTurbulence.Foundations.IncohInst.DecodingObligations
public import WaveTurbulence.Foundations.RegAsymp.SpatialNormScalar

/-! # Geometric spatial control of the literal recursive Nstar for nonempty trees -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Incoh IncohInst Links Reg TTree Finset

/-- The required literal Nstar bound at every positive order, with the constant before
all codes, signs and logarithmic cutoffs. Actual decoding is supplied by REG-STRUCT. -/
theorem literal_Nstar_positive_spatial_bound {d : ℕ} (hd : 3 ≤ d) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (X : RegChain), X.wf = true → X.dominant = true →
      ∀ (ζ : ℤˣ), 0 < (X.treeLinks ζ).length → ∀ H : LGSpine.LeafProfiles 1 d,
      (∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal B) →
      ∀ Z : Finset (Fin 1 × Path), IsSpecialSet (X.treeLinks ζ) Z →
      Fourier.spatialNorm (30*d) 0 (fun k => (LGSpine.LeafApp.chainNstar H Z X ζ ((0:Fin 1),[]) k:ℂ)) ≤
        ENNReal.ofReal (C*C^(X.treeLinks ζ).length) := by
  obtain ⟨Ccover,hCcover,hcover⟩ := actual_tree_augmented_uniform_cell_cover d (by omega)
  obtain ⟨C,hC,hbound⟩ := exists_treeLeadingSpatialProfile_geometric_bound hd (30*d) (40*d) (40*d)
    (by omega) (by omega) B Ccover hB hCcover.le
  refine ⟨C,hC,?_⟩
  intro X hwf hdom ζ hn H hF Z hZ
  obtain ⟨G,hζ,hX,_⟩ := tree_exists_decodes X hwf ζ
  cases hζ
  choose S hS hcov using hcover G X hX
  let J := univ.filter (fun j => treeChosen X (G.sig 0) j ∈ Z)
  have hfull (k : Mom d) : treeLeadingSpatialProfile hX J (treeInputFam G H) S k =
      (2:ℂ)^(X.treeLinks (G.sig 0)).length*(LGSpine.LeafApp.chainNstar H Z X (G.sig 0) ((0:Fin 1),[]) k:ℂ) := by
    rw [treeLeadingSpatialProfile_eq_singInt_source hd hX hn J (treeInputFam G H)
      (by omega) (by omega) hB (fun _ => hF _) S (fun c k x hx z hz => hcov c k x hx z hz) hS k]
    exact tree_original_source_singInt_eq_Nstar hd hX hdom hB hF Z hZ k
  let m := (X.treeLinks (G.sig 0)).length
  have hpow : (2:ℂ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : (fun k => (LGSpine.LeafApp.chainNstar H Z X (G.sig 0) ((0:Fin 1),[]) k:ℂ)) =
      (fun k => ((2:ℂ)^m)⁻¹*treeLeadingSpatialProfile hX J (treeInputFam G H) S k) := by
    funext k
    rw [hfull]
    change _ = ((2:ℂ)^m)⁻¹*((2:ℂ)^m*_)
    rw [← mul_assoc,inv_mul_cancel₀ hpow,one_mul]
  have hc : ‖((2:ℂ)^m)⁻¹‖ ≤ 1 := by
    rw [norm_inv,norm_pow,show ‖(2:ℂ)‖=2 by norm_num]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hCg : 0 ≤ C*C^m := by positivity
  rw [he]
  apply (spatialNorm_const_mul_le (by omega) hCg
    (hbound G X hX hn J (treeInputFam G H) (fun _ => hF _) S hS) _).trans
  exact ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right hc hCg).trans_eq (one_mul _))

/-- The exact source Nstar spatial estimate, including order zero and either root sign. -/
theorem literal_Nstar_spatial_bound {d : ℕ} (hd : 3 ≤ d) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (X : RegChain), X.wf = true → X.dominant = true →
      ∀ n : ℕ, X.size=2*n → ∀ (ζ : ℤˣ) (H : LGSpine.LeafProfiles 1 d),
      (∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal B) →
      ∀ Z : Finset (Fin 1 × Path), IsSpecialSet (X.treeLinks ζ) Z →
      Fourier.spatialNorm (30*d) 0 (fun k => (LGSpine.LeafApp.chainNstar H Z X ζ ((0:Fin 1),[]) k:ℂ)) ≤
        ENNReal.ofReal (C*C^n) := by
  obtain ⟨C,hC,hbound⟩ := literal_Nstar_positive_spatial_bound hd hB
  refine ⟨C,hC,?_⟩
  intro X hwf hdom n hsize ζ H hF Z hZ
  have hlen : (X.treeLinks ζ).length=n := by
    have hh := chain_linksAt_length X ζ ((0:Fin 1),[])
    change (X.treeLinks ζ).length*2=X.size at hh
    omega
  by_cases hn : 0 < (X.treeLinks ζ).length
  · simpa only [hlen] using hbound X hwf hdom ζ hn H hF Z hZ
  · have hn0 : n=0 := by omega
    have hnil : X=RegChain.nil := by
      cases X with
      | nil => rfl
      | pair m Qr Qg inner rest => simp only [RegChain.size,hn0,mul_zero] at hsize; omega
    subst X
    subst n
    have hh := tree_spatialNorm_const_le (d := d) (30*d) (1:ℂ)
    apply (show Fourier.spatialNorm (30*d) 0 (fun k =>
      (LGSpine.LeafApp.chainNstar H Z RegChain.nil ζ ((0:Fin 1),[]) k:ℂ)) ≤ ENNReal.ofReal 1 by
        simpa only [LGSpine.LeafApp.chainNstar,Complex.ofReal_one,norm_one] using hh).trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [pow_zero,mul_one] using hC

end WaveTurbulence.RA1Leafwise
