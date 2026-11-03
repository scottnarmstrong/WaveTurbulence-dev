/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.LatticeSets

/-! # Exact selector sets for TARGET Lemma A.8 -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- B1.7's pair set, with selector order `x,y,x+y`. -/
@[expose] def coupledPairSet {d : ℕ} (L : ℝ) (ax ay : Mom d)
    (r : Mom d) (α β τ : ℝ) (ξsel : Fin 3) :
    Set ((Fin d → ℤ) × (Fin d → ℤ)) :=
  {q | NearLattice L ax q.1 ∧ NearLattice L ay q.2 ∧
    |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ τ ∧
    |inner ℝ r (![latticePoint L q.1,latticePoint L q.2,
      latticePoint L q.1+latticePoint L q.2] ξsel)-β| ≤ τ}

/-- B1.7's triple set, with selector order `x-v,x+y-v,x+y-v-z`. -/
@[expose] def coupledTripleSet {d : ℕ} (L : ℝ) (ax ay az v : Mom d)
    (α β τ : ℝ) (ζsel : Fin 3) :
    Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :=
  {q | NearLattice L ax q.1 ∧ NearLattice L ay q.2.1 ∧ NearLattice L az q.2.2 ∧
    |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1)-α| ≤ τ ∧
    |inner ℝ (![latticePoint L q.1-v,latticePoint L q.1+latticePoint L q.2.1-v,
      latticePoint L q.1+latticePoint L q.2.1-v-latticePoint L q.2.2] ζsel)
      (latticePoint L q.2.2)-β| ≤ τ}

theorem finite_coupledPairSet {d : ℕ} {L : ℝ} (hL : 0 < L)
    (ax ay r : Mom d) (α β τ : ℝ) (ξsel : Fin 3) :
    (coupledPairSet L ax ay r α β τ ξsel).Finite :=
  ((finite_nearLattice hL ax).prod (finite_nearLattice hL ay)).subset
    (fun _ h => ⟨h.1,h.2.1⟩)

theorem finite_coupledTripleSet {d : ℕ} {L : ℝ} (hL : 0 < L)
    (ax ay az v : Mom d) (α β τ : ℝ) (ζsel : Fin 3) :
    (coupledTripleSet L ax ay az v α β τ ζsel).Finite :=
  ((finite_nearLattice hL ax).prod
    ((finite_nearLattice hL ay).prod (finite_nearLattice hL az))).subset
    (fun _ h => ⟨h.1,h.2.1,h.2.2.1⟩)

end WaveTurbulence.CountLemmas
