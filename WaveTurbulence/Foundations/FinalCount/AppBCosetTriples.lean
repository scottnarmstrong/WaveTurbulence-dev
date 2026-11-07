/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBasicPair
public import WaveTurbulence.Foundations.CountLemmas.AtomTriple
import Mathlib.Tactic

/-! # Appendix B three-label counting on an arbitrary lattice coset -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set CountLemmas

/-- Exact translation of the signed three-vector energy. -/
theorem appb_coset_triple_energy {d : ℕ} (w a b c : Mom d) :
    ‖w+a‖^2 - ‖w+b‖^2 + ‖w+c‖^2 =
      ‖a‖^2 - ‖b‖^2 + ‖c‖^2 + 2*inner ℝ w (a-b+c) + ‖w‖^2 := by
  rw [norm_add_sq_real,norm_add_sq_real,norm_add_sq_real]
  simp only [inner_add_right,inner_sub_right]
  ring

/-- Actual three-label problem on the coset w+Z_L^d. The integer conserved
momentum is the value obtained from any one admissible decoration. -/
def appbCosetTripleSet {d : ℕ} (L : ℝ) (w a b c : Mom d)
    (nk : Fin d → ℤ) (β τ : ℝ) : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :=
  {q | ‖w+latticePoint L q.1-a‖ ≤ 1 ∧
    ‖w+latticePoint L q.2.1-b‖ ≤ 1 ∧ ‖w+latticePoint L q.2.2-c‖ ≤ 1 ∧
    q.1-q.2.1+q.2.2 = nk ∧
    |‖w+latticePoint L q.1‖^2 - ‖w+latticePoint L q.2.1‖^2 +
      ‖w+latticePoint L q.2.2‖^2 - β| ≤ τ}

/-- Translation changes the centers and energy constant only, retaining the
actual integer tuples and every localization constraint. -/
theorem appb_cosetTripleSet_eq {d : ℕ} (L : ℝ) (w a b c : Mom d)
    (nk : Fin d → ℤ) (β τ : ℝ) :
    appbCosetTripleSet L w a b c nk β τ =
      atomTripleSet L (a-w) (b-w) (c-w) nk
        (β-2*inner ℝ w (latticePoint L nk)-‖w‖^2) τ := by
  ext q
  have hn (v center : Mom d) : w+v-center = v-(center-w) := by module
  have he (hcon : q.1-q.2.1+q.2.2 = nk) :
      ‖w+latticePoint L q.1‖^2 - ‖w+latticePoint L q.2.1‖^2 +
        ‖w+latticePoint L q.2.2‖^2 - β =
      ‖latticePoint L q.1‖^2 - ‖latticePoint L q.2.1‖^2 + ‖latticePoint L q.2.2‖^2 -
        (β-2*inner ℝ w (latticePoint L nk)-‖w‖^2) := by
    rw [appb_coset_triple_energy,← WeylSums.latticePoint_sub_eq,← WeylSums.latticePoint_add_eq,hcon]
    ring
  change (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _ ∧ _)
  constructor
  · rintro ⟨h1,h2,h3,hcon,hE⟩
    refine ⟨?_,?_,?_,hcon,?_⟩
    · simpa only [NearLattice,hn] using h1
    · simpa only [NearLattice,hn] using h2
    · simpa only [NearLattice,hn] using h3
    · simpa only [he hcon] using hE
  · rintro ⟨h1,h2,h3,hcon,hE⟩
    refine ⟨?_,?_,?_,hcon,?_⟩
    · simpa only [NearLattice,hn] using h1
    · simpa only [NearLattice,hn] using h2
    · simpa only [NearLattice,hn] using h3
    · simpa only [he hcon] using hE

/-- DH23 basiccount(2) on a general coset, with constants uniform in the
coset shift and all energy and spatial centers. -/
theorem appb_coset_triple_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ ∈ Ioo (0 : ℝ) 1,
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ w a b c : Mom d, ∀ nk : Fin d → ℤ, ∀ β : ℝ,
      (appbCosetTripleSet L w a b c nk β (δ⁻¹*L^(-2*γ))).Finite ∧
      ((appbCosetTripleSet L w a b c nk β (δ⁻¹*L^(-2*γ))).ncard : ℝ) ≤
        C*δ⁻¹*L^(2*((d : ℝ)-γ)) := by
  intro d hd γ hγ
  obtain ⟨C,L₀,h⟩ := atomTriple_bound d hd γ hγ
  refine ⟨C,L₀,?_⟩
  intro L hL δ hδ w a b c nk β
  rw [appb_cosetTripleSet_eq]
  exact h L hL δ hδ _ nk (a-w) (b-w) (c-w)

end WaveTurbulence.Mole
