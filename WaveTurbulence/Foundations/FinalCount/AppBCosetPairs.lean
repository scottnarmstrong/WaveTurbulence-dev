/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCosetTriples
public import WaveTurbulence.Foundations.CountLemmas.NegativeAtom
import Mathlib.Tactic

/-! # DH23 basiccount(1) on arbitrary affine lattice cosets -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set CountLemmas

/-- The actual two-label problem, with the two source sign possibilities. -/
def appbCosetPairSet {d : ℕ} (L : ℝ) (w a b : Mom d) (nk : Fin d → ℤ) (β τ : ℝ)
    (ε : ℤˣ) : Set ((Fin d → ℤ) × (Fin d → ℤ)) :=
  {q | ‖w+latticePoint L q.1-a‖ ≤ 1 ∧ ‖w+latticePoint L q.2-b‖ ≤ 1 ∧
    q.1+(ε : ℤ) • q.2 = nk ∧
    |‖w+latticePoint L q.1‖^2 + (ε : ℤ) * ‖w+latticePoint L q.2‖^2 - β| ≤ τ}

/-- The coset changes only the fixed centers; no solution is lost. -/
theorem appb_cosetPairSet_eq {d : ℕ} (L : ℝ) (w a b : Mom d)
    (nk : Fin d → ℤ) (β τ : ℝ) (ε : ℤˣ) :
    appbCosetPairSet L w a b nk β τ ε = atomPairSet L (a-w) (b-w) nk
      (β-2*inner ℝ w (latticePoint L nk)-(1+(ε : ℤ))*‖w‖^2) τ ε := by
  ext q
  have hn (v center : Mom d) : w+v-center = v-(center-w) := by module
  have he (hcon : q.1+(ε : ℤ) • q.2 = nk) :
      ‖w+latticePoint L q.1‖^2 + (ε : ℤ)*‖w+latticePoint L q.2‖^2 - β =
      ‖latticePoint L q.1‖^2 + (ε : ℤ)*‖latticePoint L q.2‖^2 -
        (β-2*inner ℝ w (latticePoint L nk)-(1+(ε : ℤ))*‖w‖^2) := by
    rcases Int.units_eq_one_or ε with rfl | rfl
    · have hc : latticePoint L q.1 + latticePoint L q.2 = latticePoint L nk := by
        rw [← WeylSums.latticePoint_add_eq]
        congr 1
        simpa only [Units.val_one,one_smul] using hcon
      simp only [Units.val_one,Int.cast_one,one_mul]
      rw [norm_add_sq_real,norm_add_sq_real,← hc,inner_add_right]
      ring
    · have hc : latticePoint L q.1 - latticePoint L q.2 = latticePoint L nk := by
        rw [← WeylSums.latticePoint_sub_eq]
        congr 1
        simpa [sub_eq_add_neg] using hcon
      simp only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_mul,one_mul]
      rw [norm_add_sq_real,norm_add_sq_real,← hc,inner_sub_right]
      ring
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
  constructor
  · rintro ⟨h1,h2,hcon,hE⟩
    refine ⟨?_,?_,hcon,?_⟩
    · simpa only [NearLattice,hn] using h1
    · simpa only [NearLattice,hn] using h2
    · simpa only [he hcon] using hE
  · rintro ⟨h1,h2,hcon,hE⟩
    refine ⟨?_,?_,hcon,?_⟩
    · simpa only [NearLattice,hn] using h1
    · simpa only [NearLattice,hn] using h2
    · simpa only [he hcon] using hE

/-- The sharp same-sign bound, uniform in the affine shift w. -/
theorem appb_coset_positive_pair_bound {d : ℕ} (hd : 2 ≤ d) {L δ γ : ℝ}
    (hL : 1 ≤ L) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ≤ 1)
    (w a b : Mom d) (nk : Fin d → ℤ) (β : ℝ) :
    ((appbCosetPairSet L w a b nk β (δ⁻¹*L^(-2*γ)) 1).ncard : ℝ) ≤
      (2*3^(d-2)*(6*Real.pi+1284002))*δ⁻¹*L^((d : ℝ)-γ-min γ (1-γ)) := by
  rw [appb_cosetPairSet_eq]
  exact appb_positive_pair_bound hd hL hδ hγ (a-w) (b-w) nk _

/-- The large-difference saving in basiccount(1), retaining the physical
conserved difference and arbitrary coset shift. -/
theorem appb_coset_negative_pair_large_bound {d : ℕ} (hd : 0 < d) {L δ γ η : ℝ}
    (hL : 1 ≤ L) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hη : η ≤ 1-γ)
    (w a b : Mom d) (nk : Fin d → ℤ) (β : ℝ)
    (hgap : L^(-γ+η) ≤ ‖latticePoint L nk‖) :
    ((appbCosetPairSet L w a b nk β (δ⁻¹*L^(-2*γ)) (-1)).ncard : ℝ) ≤
      (3^(d-1)*((d : ℝ)+1))*δ⁻¹*L^((d : ℝ)-γ-η) := by
  rw [appb_cosetPairSet_eq]
  exact negative_atom_large_bound hd hL hδ hη (a-w) (b-w) nk _ hgap

end WaveTurbulence.Mole
