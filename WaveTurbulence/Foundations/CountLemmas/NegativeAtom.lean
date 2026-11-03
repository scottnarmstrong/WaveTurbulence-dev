/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.AtomProjection
public import WaveTurbulence.Foundations.CountLemmas.LargeCoordinate
public import WaveTurbulence.Foundations.CountLemmas.StripPowers

/-! # The difference-sign atomic count -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- TARGET Lemma A.9, the two-vector difference-sign bound, with the required
nonzero conserved momentum. The constant is explicit and independent of γ. -/
theorem negative_atom_bound {d : ℕ} {L δ γ : ℝ} (hL : 1 ≤ L)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ≤ 1)
    (a b : Mom d) (nk : Fin d → ℤ) (hnk : nk ≠ 0) (β : ℝ) :
    ((atomPairSet L a b nk β (δ⁻¹*L^(-2*γ)) (-1)).ncard : ℝ) ≤
      (2*3^d)*δ⁻¹*min (L^d) (L^((d : ℝ)+1-2*γ)) := by
  have hδp := hδ.1
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨i,hi⟩ := exists_lattice_coordinate_gap hLp nk hnk
  have hip : 0 < |latticePoint L nk i| := (inv_pos.mpr hLp).trans_le hi
  have hc := atomPair_negative_coordinate_bound (τ := δ⁻¹*L^(-2*γ)) hLp (by positivity) a b nk β i
    (abs_pos.mp hip)
  have hb := strip_lattice_power_bound hL hδ.1 hδ.2 hγ hi
  have hc' := hc.trans (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (2*L+1)^(d-1)))
  have hr := box_times_rpow_bound (d-1) hL (by norm_num : (0 : ℝ) ≤ 2)
    (inv_nonneg.mpr hδ.1.le) (e := 2-2*γ)
  have hd : 1 ≤ d := by
    by_contra h
    have hz : d = 0 := by omega
    subst d
    apply hnk
    funext i
    exact Fin.elim0 i
  have hcast : ((d-1 : ℕ) : ℝ)+ (2-2*γ) = (d : ℝ)+1-2*γ := by
    rw [Nat.cast_sub hd]
    push_cast
    ring
  rw [hcast] at hr
  have hconst : 3^(d-1)*2 ≤ 2*(3 : ℝ)^d := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.sub_le d 1)
    linarith only [hh]
  have henergy : ((atomPairSet L a b nk β (δ⁻¹*L^(-2*γ)) (-1)).ncard : ℝ) ≤
      (2*3^d)*δ⁻¹*L^((d : ℝ)+1-2*γ) :=
    (hc'.trans hr).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity))
  have htriv := atomPair_trivial_bound hLp a b nk β (δ⁻¹*L^(-2*γ)) (-1)
  have hbox : (2*L+1)^d ≤ (3 : ℝ)^d*L^d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) d
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hspace : ((atomPairSet L a b nk β (δ⁻¹*L^(-2*γ)) (-1)).ncard : ℝ) ≤
      (2*3^d)*δ⁻¹*L^d := (htriv.trans hbox).trans (by
        have hh : (3 : ℝ)^d ≤ (2*3^d)*δ⁻¹ := by nlinarith only [hδi,pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) d]
        exact mul_le_mul_of_nonneg_right hh (by positivity))
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ (2*3^d)*δ⁻¹)]
  exact le_min hspace henergy

/-- TARGET Lemma A.9, the stronger difference-sign count when the conserved
momentum is at least `L^(-γ+η)`. -/
theorem negative_atom_large_bound {d : ℕ} (hd : 0 < d) {L δ γ η : ℝ}
    (hL : 1 ≤ L) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hη : η ≤ 1-γ)
    (a b : Mom d) (nk : Fin d → ℤ) (β : ℝ)
    (hgap : L^(-γ+η) ≤ ‖latticePoint L nk‖) :
    ((atomPairSet L a b nk β (δ⁻¹*L^(-2*γ)) (-1)).ncard : ℝ) ≤
      (3^(d-1)*((d : ℝ)+1))*δ⁻¹*L^((d : ℝ)-γ-η) := by
  have hδp := hδ.1
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨i,hi⟩ := exists_large_coordinate hd (latticePoint L nk)
  have hip : 0 < |latticePoint L nk i| := by
    have hh := (Real.rpow_pos_of_pos hLp (-γ+η)).trans_le (hgap.trans hi)
    exact (mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < d)).mp hh
  have hc := atomPair_negative_coordinate_bound (τ := δ⁻¹*L^(-2*γ)) hLp (by positivity) a b nk β i (abs_pos.mp hip)
  have hb := strip_power_bound hL hδ.1 hδ.2 hip (by linarith only [hη]) (hgap.trans hi)
  have hr := box_times_rpow_bound (d-1) hL (by positivity : 0 ≤ (d : ℝ)+1)
    (inv_nonneg.mpr hδ.1.le) (e := 1-γ-η)
  have hcast : ((d-1 : ℕ) : ℝ)+(1-γ-η) = (d : ℝ)-γ-η := by
    rw [Nat.cast_sub hd]
    push_cast
    ring
  rw [hcast] at hr
  exact (hc.trans (mul_le_mul_of_nonneg_left hb (by positivity))).trans hr

end WaveTurbulence.CountLemmas
