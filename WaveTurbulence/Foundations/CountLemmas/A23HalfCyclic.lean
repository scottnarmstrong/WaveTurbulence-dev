/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.CountLemmas.SumTripleTarget
public import WaveTurbulence.Foundations.CountLemmas.PositiveShellThreshold

/-!
# DH23 Lemma A.2(3), `γ > 1/2`: the sum selectors `ζ = x + y − v` and `ζ = x + y − v − z`

The cyclic form of the referee's proof (`docs/research/case4-gamma-above-half-referee.txt`, §4.3(i)):

* project to `(s, z)`, `s = x + y`, and count the projection by the bilinear band (`exists_broad_bilinear_band_bound`,
  `≲ τ L^{2d}`), exactly as the landed `exists_sum_triple_bound`;
* at fixed `s` the vector `x` lies in a thin spherical shell (`x·(s − x) = |s|²/4 − |x − s/2|²`); slicing to planar
  annuli and using the circle discrepancy with exponent `2/3` (landed `positive_atom_shell_threshold_bound`, which
  covers small and huge radii) gives `≲ L^{d−2} · U` with `U = 2δ^{-1} L^{(4−2γ)/3}`, i.e. a saving `(2γ − 1)/3`
  over the trivial `L^{d−1}` (`card_fixed_sum_band_threshold_le`).

Result (`coupledTriple_sum_bound_half`): for `1/2 ≤ γ < 1` the two sum selectors of the landed `coupledTripleSet`
have `≲ δ^{-2} L^{3(d−γ) − (1−γ) − (2γ−1)/3}` points.
-/

public section
open Finset Set
namespace WaveTurbulence.CountLemmas

/-- At fixed sum, a bilinear band is a same-sign atomic energy band; the `2/3` shell threshold applies. -/
theorem card_fixed_sum_band_threshold_le {d : ℕ} {L τ U : ℝ} (hL : 0 < L)
    (hτ : 0 ≤ τ) (hW : 1 ≤ 2*τ*L^2) (hWU : 2*τ*L^2 ≤ U) (hbudget : L^2*(2*τ*L^2) ≤ U^3)
    (a b : Mom (d+2)) (nk : Fin (d+2) → ℤ) (α : ℝ)
    (s : Finset ((Fin (d+2) → ℤ) × (Fin (d+2) → ℤ)))
    (hs : ∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧ q.1+q.2 = nk ∧
      |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ τ) :
    (s.card : ℝ) ≤ (2*L+1)^d*(6*Real.pi+1924002)*U := by
  have hsub : (s : Set _) ⊆ atomPairSet L a b nk (‖latticePoint L nk‖^2-2*α) (2*τ) 1 := by
    intro q hq
    obtain ⟨ha,hb,hcon,he⟩ := hs q hq
    refine ⟨ha,hb,by simpa using hcon,?_⟩
    have hk : latticePoint L q.1+latticePoint L q.2 = latticePoint L nk := by
      rw [← WeylSums.latticePoint_add_eq,hcon]
    have hid : ‖latticePoint L q.1‖^2+‖latticePoint L q.2‖^2-
        (‖latticePoint L nk‖^2-2*α) =
        -2*(inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α) := by
      rw [← hk,norm_add_sq_real]
      ring
    simp only [Units.val_one,Int.cast_one,one_mul]
    rw [hid,abs_mul]
    norm_num only [abs_neg,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left he (by norm_num)
  have hc := Set.ncard_le_ncard hsub (finite_atomPairSet hL a b nk _ _ 1)
  have hcR : (s.card : ℝ) ≤ (atomPairSet L a b nk (‖latticePoint L nk‖^2-2*α) (2*τ) 1).ncard := by
    exact_mod_cast (by simpa only [Set.ncard_coe_finset] using hc)
  refine hcR.trans (positive_atom_shell_threshold_bound hL (by positivity) (by linarith only [hW])
    (by linarith only [hWU]) (by linarith only [hbudget]) a b nk _)

/-- The sum-selector triple count with the `2/3` fixed-sum fiber. -/
theorem exists_sum_triple_threshold_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ L τ U : ℝ, 2 ≤ L → 0 < τ →
    1 ≤ τ*L^2 → 1/τ ≤ L^2 → 2*τ*L^2 ≤ U → L^2*(2*τ*L^2) ≤ U^3 →
    ∀ a b c : Mom (d+2), ∀ nv : Fin (d+2) → ℤ, ∀ sel : Bool, ∀ α β : ℝ,
    ∀ s : Finset ((Fin (d+2) → ℤ) × (Fin (d+2) → ℤ) × (Fin (d+2) → ℤ)),
    (∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2.1 ∧ NearLattice L c q.2.2 ∧
      |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1)-α| ≤ τ ∧
      |inner ℝ (latticePoint L (sumTripleProjection nv sel q).1)
        (latticePoint L q.2.2)-β| ≤ τ) →
    (s.card : ℝ) ≤ C*τ*L^(2*((d+2 : ℕ) : ℝ))*(2*L+1)^d*U := by
  obtain ⟨C,hC,hband⟩ := exists_broad_bilinear_band_bound (d+2) (by omega)
  refine ⟨C*(6*Real.pi+1924002),by positivity,?_⟩
  intro L τ U hL hτ hW hwin hWU hbudget a b c nv sel α β s hs
  have hLp : 0 < L := by linarith only [hL]
  let f := sumTripleProjection nv sel
  let g := fun q : (Fin (d+2) → ℤ) × (Fin (d+2) → ℤ) × (Fin (d+2) → ℤ) => (q.1,q.2.1)
  let A := (2*L+1)^d*(6*Real.pi+1924002)*U
  have hU : 0 ≤ U := le_trans (by positivity) hWU
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hproj : ((s.image f).card : ℝ) ≤ C*τ*L^(2*((d+2 : ℕ) : ℝ)) := by
    apply hband L τ hL hτ hwin (a+b-latticePoint L nv-(if sel then c else 0)) c β (s.image f)
    intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    obtain ⟨ha,hb,hc,he₁,he₂⟩ := hs q hq
    exact ⟨sumTripleProjection_norm L a b c nv sel q ha hb hc,
      hc.trans (by norm_num),he₂⟩
  have hfib : ∀ p ∈ s.image f, (((s.filter (fun q => f q = p)).card) : ℝ) ≤ A := by
    intro p hp
    let t := s.filter (fun q => f q = p)
    have hi := sumTripleProjection_pair_injOn nv sel s p
    change (t.card : ℝ) ≤ A
    rw [← card_image_of_injOn hi]
    apply card_fixed_sum_band_threshold_le hLp hτ.le (by linarith only [hW]) hWU hbudget
      a b (p.1+nv+(if sel then p.2 else 0)) α (t.image g)
    intro xy hxy
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hxy
    obtain ⟨ha,hb,hc,he₁,he₂⟩ := hs q (mem_filter.mp hq).1
    exact ⟨ha,hb,sumTripleProjection_sum nv sel q p (mem_filter.mp hq).2,he₁⟩
  have hc := Counting.card_le_image_card_mul_of_fiber_le s f hfib
  calc
    _ ≤ ((s.image f).card : ℝ)*A := hc
    _ ≤ (C*τ*L^(2*((d+2 : ℕ) : ℝ)))*A := mul_le_mul_of_nonneg_right hproj hA
    _ = _ := by dsimp only [A]; ring

/-- The exponent identity `2D − 2γ + (D − 2) + (4 − 2γ)/3 = 3(D − γ) − (1 − γ) − (2γ − 1)/3`. -/
theorem cyclic_exponent_eq (D γ : ℝ) :
    -2*γ+2*D+(D-2)+(4-2*γ)/3 = 3*(D-γ)-(1-γ)-(2*γ-1)/3 := by ring

/-- **DH23 Lemma A.2(3), `γ ≥ 1/2`, sum selectors** (`ζ = x + y − v`, `x + y − v − z`): saving `(2γ − 1)/3`. -/
theorem coupledTriple_sum_bound_half (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Icc (1/2 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ a b c : Mom d, ∀ nv : Fin d → ℤ, ∀ sel : Bool, ∀ α β : ℝ,
      ((coupledTripleSet L a b c (latticePoint L nv) α β (δ⁻¹*L^(-2*γ))
        (if sel then 2 else 1)).ncard : ℝ) ≤
      C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-(1-γ)-(2*γ-1)/3) := by
  obtain ⟨n,hn⟩ : ∃ n, d = n+2 := ⟨d-2,by omega⟩
  subst d
  obtain ⟨C,hC,hbound⟩ := exists_sum_triple_threshold_bound n (by omega)
  refine ⟨2*C*3^n,2,by positivity,?_⟩
  intro L hL δ hδ a b c nv sel α β
  have hLp : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  let τ := δ⁻¹*L^(-2*γ)
  let U := 2*δ⁻¹*L^((4-2*γ)/3)
  have hτ : 0 < τ := mul_pos (inv_pos.mpr hδ.1) (Real.rpow_pos_of_pos hLp _)
  have hτL : τ*L^2 = δ⁻¹*L^(2-2*γ) := by
    dsimp only [τ]
    rw [mul_assoc, ← Real.rpow_natCast L 2, ← Real.rpow_add hLp]
    congr 2
    push_cast
    ring
  have hL22 : 1 ≤ L^(2-2*γ) := Real.one_le_rpow hL1 (by linarith only [hγ.2])
  have hW : 1 ≤ τ*L^2 := by rw [hτL]; nlinarith only [hδi,hL22]
  have hwin : 1/τ ≤ L^2 := by
    rw [div_le_iff₀ hτ]
    linarith only [hW]
  have hWU : 2*τ*L^2 ≤ U := by
    rw [mul_assoc, hτL]
    dsimp only [U]
    have : L^(2-2*γ) ≤ L^((4-2*γ)/3) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hγ.1])
    nlinarith only [this, hδi]
  have hbudget : L^2*(2*τ*L^2) ≤ U^3 := by
    rw [mul_assoc 2, hτL]
    dsimp only [U]
    have hp : (L^((4-2*γ)/3))^3 = L^2*L^(2-2*γ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le, ← Real.rpow_natCast L 2, ← Real.rpow_add hLp]
      norm_num
      ring_nf
    have hδ3 : δ⁻¹ ≤ δ⁻¹^3 := le_self_pow₀ hδi (by norm_num)
    have hpos : 0 ≤ L^2*L^(2-2*γ) := by positivity
    calc L^2*(2*(δ⁻¹*L^(2-2*γ))) = 2*δ⁻¹*(L^2*L^(2-2*γ)) := by ring
      _ ≤ 8*δ⁻¹^3*(L^2*L^(2-2*γ)) := by
        have h1 := mul_le_mul_of_nonneg_right hδ3 hpos
        have h2 : 0 ≤ δ⁻¹^3*(L^2*L^(2-2*γ)) := by positivity
        linarith only [h1, h2]
      _ = (2*δ⁻¹*L^((4-2*γ)/3))^3 := by rw [mul_pow, mul_pow, hp]; ring
  let S := (finite_coupledTripleSet hLp a b c (latticePoint L nv) α β τ
    (if sel then 2 else 1)).toFinset
  have hb := hbound L τ U hL hτ hW hwin hWU hbudget a b c nv sel α β S (by
    intro q hq
    have hh := (finite_coupledTripleSet hLp a b c (latticePoint L nv) α β τ
      (if sel then 2 else 1)).mem_toFinset.mp hq
    refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,?_⟩
    rw [latticePoint_sumTripleProjection]
    cases sel <;> simpa using hh.2.2.2.2)
  rw [Set.ncard_eq_toFinset_card _ (finite_coupledTripleSet hLp a b c (latticePoint L nv) α β τ
    (if sel then 2 else 1))]
  refine hb.trans ?_
  have hbox : (2*L+1)^n ≤ 3^n*L^n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL1]) n
  have hpow : L^(-2*γ)*L^(2*((n+2 : ℕ) : ℝ))*L^n*L^((4-2*γ)/3) =
      L^(3*(((n+2 : ℕ) : ℝ)-γ)-(1-γ)-(2*γ-1)/3) := by
    rw [← Real.rpow_natCast L n, ← Real.rpow_add hLp, ← Real.rpow_add hLp, ← Real.rpow_add hLp]
    congr 1
    push_cast
    ring
  calc C*τ*L^(2*((n+2 : ℕ) : ℝ))*(2*L+1)^n*U
      ≤ C*τ*L^(2*((n+2 : ℕ) : ℝ))*(3^n*L^n)*U :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbox (by positivity))
          (by dsimp only [U]; positivity)
    _ = 2*C*3^n*δ⁻¹^2*(L^(-2*γ)*L^(2*((n+2 : ℕ) : ℝ))*L^n*L^((4-2*γ)/3)) := by
        dsimp only [τ, U]; ring
    _ = _ := by rw [hpow]

end WaveTurbulence.CountLemmas
