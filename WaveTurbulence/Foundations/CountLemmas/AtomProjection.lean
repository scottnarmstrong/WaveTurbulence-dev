/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.LatticeSets
public import WaveTurbulence.Foundations.CountLemmas.LinearBox
public import WaveTurbulence.Foundations.WeylSums.ThreeVectorReduction

/-! # Eliminating the conserved vector in two-atom counts -/

public section
open Set Finset
namespace WaveTurbulence.CountLemmas

/-- For either integer unit sign, conservation determines the second vector. -/
theorem atomPair_fst_injOn {d : ℕ} (L : ℝ) (a b : Mom d)
    (nk : Fin d → ℤ) (β τ : ℝ) (ε : ℤˣ) :
    InjOn Prod.fst (atomPairSet L a b nk β τ ε) := by
  intro q hq r hr he
  apply Prod.ext he
  have h₁ := hq.2.2.1
  have h₂ := hr.2.2.1
  rcases Int.units_eq_one_or ε with hε | hε <;> rw [hε] at h₁ h₂
  all_goals
    funext i
    have hq' := congrFun h₁ i
    have hr' := congrFun h₂ i
    have he' := congrFun he i
    simp at hq' hr'
    omega

/-- The coordinate-box estimate is uniform in the sign and energy level. -/
theorem atomPair_trivial_bound {d : ℕ} {L : ℝ} (hL : 0 < L) (a b : Mom d)
    (nk : Fin d → ℤ) (β τ : ℝ) (ε : ℤˣ) :
    ((atomPairSet L a b nk β τ ε).ncard : ℝ) ≤ (2*L+1)^d := by
  have hi := atomPair_fst_injOn L a b nk β τ ε
  have hm : MapsTo Prod.fst (atomPairSet L a b nk β τ ε)
      (Counting.latticeBox (fun i => L*a i) L : Set (Fin d → ℤ)) :=
    fun q hq => nearLattice_mem_box hL a q.1 hq.1
  have hc := Set.ncard_le_ncard_of_injOn Prod.fst hm hi
    (Counting.latticeBox (fun i => L*a i) L).finite_toSet
  have hcR : ((atomPairSet L a b nk β τ ε).ncard : ℝ) ≤
      ((Counting.latticeBox (fun i => L*a i) L).card : ℝ) := by
    exact_mod_cast (by simpa only [Set.ncard_coe_finset] using hc)
  exact hcR.trans (Counting.card_latticeBox_le _ hL.le)

/-- The difference-sign energy is a linear strip after conservation. -/
theorem atomPair_negative_energy {d : ℕ} (L : ℝ) (a b : Mom d)
    (nk : Fin d → ℤ) (β τ : ℝ) (q : (Fin d → ℤ) × (Fin d → ℤ))
    (hq : q ∈ atomPairSet L a b nk β τ (-1)) :
    |2*inner ℝ (latticePoint L nk) (latticePoint L q.1) -
      ‖latticePoint L nk‖^2 - β| ≤ τ := by
  have hc : q.1-q.2 = nk := by simpa [sub_eq_add_neg] using hq.2.2.1
  have hk : latticePoint L nk = latticePoint L q.1-latticePoint L q.2 := by
    rw [← WeylSums.latticePoint_sub_eq,hc]
  have he : 2*inner ℝ (latticePoint L nk) (latticePoint L q.1) -
      ‖latticePoint L nk‖^2 = ‖latticePoint L q.1‖^2-‖latticePoint L q.2‖^2 := by
    rw [hk]
    simp only [EuclideanSpace.real_norm_sq_eq,PiLp.inner_apply,Real.inner_apply,
      PiLp.sub_apply,mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [he]
  simpa [sub_eq_add_neg] using hq.2.2.2

/-- Fixing a coordinate with nonzero conserved difference gives the exact
strip bound, retaining the useful factor `1 / |kᵢ|`. -/
theorem atomPair_negative_coordinate_bound {d : ℕ} {L τ : ℝ}
    (hL : 0 < L) (hτ : 0 ≤ τ) (a b : Mom d) (nk : Fin d → ℤ) (β : ℝ)
    (i : Fin d) (hi : latticePoint L nk i ≠ 0) :
    ((atomPairSet L a b nk β τ (-1)).ncard : ℝ) ≤
      (2*L+1)^(d-1)*(τ*L/|latticePoint L nk i|+1) := by
  classical
  let S := (finite_atomPairSet hL a b nk β τ (-1)).toFinset
  let T := S.image Prod.fst
  have hc : S.card = T.card := (card_image_of_injOn
    (fun q hq r hr he => atomPair_fst_injOn L a b nk β τ (-1)
      ((finite_atomPairSet hL a b nk β τ (-1)).mem_toFinset.mp hq)
      ((finite_atomPairSet hL a b nk β τ (-1)).mem_toFinset.mp hr) he)).symm
  have hb := card_linear_box_le T (fun j => L*a j)
    (fun j => 2*latticePoint L nk j/L) i hL.le hτ
    (by exact div_ne_zero (mul_ne_zero (by norm_num) hi) hL.ne')
    (by
      intro n hn
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hn
      exact (Counting.mem_latticeBox _ _ _).mp
        (nearLattice_mem_box hL a q.1 ((Set.Finite.mem_toFinset _).mp hq).1))
    (β := β+‖latticePoint L nk‖^2)
    (by
      intro n hn
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hn
      have he := atomPair_negative_energy L a b nk β τ q ((Set.Finite.mem_toFinset _).mp hq)
      have hid : (∑ j, (2*latticePoint L nk j/L)*(q.1 j : ℝ)) =
          2*inner ℝ (latticePoint L nk) (latticePoint L q.1) := by
        simp only [PiLp.inner_apply,Real.inner_apply,latticePoint,mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      rw [hid]
      convert he using 2
      ring)
  have heq : 2*τ/|2*latticePoint L nk i/L| = τ*L/|latticePoint L nk i| := by
    rw [abs_div,abs_mul,abs_of_pos hL]
    norm_num
    field_simp
  rw [heq] at hb
  rw [Set.ncard_eq_toFinset_card _ (finite_atomPairSet hL a b nk β τ (-1))]
  exact (congrArg (fun n : ℕ => (n : ℝ)) hc).le.trans hb

end WaveTurbulence.CountLemmas
