/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Total
/-! FLOWER-P7: the sixteen pieces assemble: `‖∑ᶠ y ∈ Y6Set, K_y(n)‖ ≤` the sum of the explicit piece bounds. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset LGSpine

section
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {tt : Fin (2 * 3) → ℝ} {Creg : ℕ → ℝ}
  (H : PieceHyp C₀ P p N Rr k tt Creg) (kind : TreeKind) (n : Fin (2 * 3) → (Fin P.d → ℤ))
include H

theorem bound_shape6 :
    ‖∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 Finset.univ},
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      Bound6 P p N kind k n := by
  have hset : {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 Finset.univ} = Irr6 P p N kind := by
    ext y
    constructor
    · rintro ⟨hy, hm⟩
      exact ⟨hy, (minimalAt_univ_iff y.garden (Y6Set_plain P p N kind hy)).1 hm⟩
    · rintro ⟨hy, hi⟩
      exact ⟨hy, (minimalAt_univ_iff y.garden (Y6Set_plain P p N kind hy)).2 hi⟩
  rw [hset]
  exact piece0_norm_le C₀ P H.G H.hp H.hN kind Rr H.hRr H.hmmax n k tt H.htt H.hnum6

theorem bound_shape42 (σ : Fin (2 * 2) ⊕ Fin 2 ≃ Fin (2 * 3)) (S : Finset (Fin (2 * 3)))
    (hS : S = Finset.univ.image fun i => σ (.inl i)) (h0 : σ (.inl 0) = 0)
    (hs2 : (fun i => childSig (σ (.inr i))) = ![1, -1]) :
    ‖∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 S},
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      Bound42 P p N kind σ 0 Creg k n := by
  subst hS
  have hset : {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 (Finset.univ.image fun i => σ (.inl i))} =
      {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden (σ (.inl 0)) (Finset.univ.image fun i => σ (.inl i))} := by
    rw [h0]
  rw [hset]
  exact piece42_norm_le C₀ P H.G H.hp H.hN kind Rr H.hRr (by have := H.hmmax; omega) H.hR1 σ 0 hs2 n k tt H.htt H.hF
    H.hnumA H.hnumC Creg H.hreg

theorem bound_shape24 (σ : Fin 2 ⊕ Fin (2 * 2) ≃ Fin (2 * 3)) (S : Finset (Fin (2 * 3)))
    (hS : S = Finset.univ.image fun i => σ (.inl i)) (h0 : σ (.inl 0) = 0)
    (hsA : (fun i => childSig (σ (.inl i))) = ![1, -1])
    (hs4 : (fun i => childSig (σ (.inr i))) = ![1, -1, 1, -1]) :
    ‖∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 S},
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      Bound24 P p N kind σ Creg k n := by
  subst hS
  have hset : {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 (Finset.univ.image fun i => σ (.inl i))} =
      {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden (σ (.inl 0)) (Finset.univ.image fun i => σ (.inl i))} := by
    rw [h0]
  rw [hset]
  exact piece24_norm_le C₀ P H.G H.hp H.hN kind Rr H.hRr H.hR1 (by have := H.hmmax; omega) σ hsA hs4 n k tt H.htt
    H.hF H.hnumA H.hnumC Creg H.hreg

end

theorem shapeFin_eq : shapeFin = {({0, 1} : Finset (Fin (2 * 3))), {0, 3}, {0, 5}, {0, 3, 4, 5}, {0, 1, 4, 5},
    {0, 1, 3, 4}, {0, 2, 3, 5}, {0, 1, 2, 5}, {0, 1, 2, 3}, Finset.univ} := by
  simp [shapeFin, shapeList]

section
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {tt : Fin (2 * 3) → ℝ} {Creg : ℕ → ℝ}
  (H : PieceHyp C₀ P p N Rr k tt Creg) (kind : TreeKind) (n : Fin (2 * 3) → (Fin P.d → ℤ))
include H

/-- **The six-tree sum over the decapitated carrier, at fixed outer root labels `n`, is bounded by the sum of the
sixteen explicit piece bounds.** -/
theorem Y6_sum_norm_le :
    ‖∑ᶠ y ∈ Y6Set P p N kind,
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      Bound24 P p N kind σ1 Creg k n + Bound24 P p N kind σ2 Creg k n + Bound24 P p N kind σ3 Creg k n +
      Bound42 P p N kind σ4 0 Creg k n + Bound42 P p N kind σ5 0 Creg k n + Bound42 P p N kind σ6 0 Creg k n +
      Bound42 P p N kind σ7 0 Creg k n + Bound42 P p N kind σ8 0 Creg k n + Bound42 P p N kind σ9 0 Creg k n +
      Bound6 P p N kind k n := by
  rw [finsum_Y6_partition]
  refine (norm_sum_le _ _).trans ?_
  rw [shapeFin_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have h1 := bound_shape24 H kind n σ1 {0, 1} (by ext x; fin_cases x <;> simp [σ1, tableEquiv, Fin.exists_fin_two])
    (by simp [σ1, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ1, tableEquiv] <;> decide)
    (by funext i; fin_cases i <;> simp [σ1, tableEquiv] <;> decide)
  have h2 := bound_shape24 H kind n σ2 {0, 3} (by ext x; fin_cases x <;> simp [σ2, tableEquiv, Fin.exists_fin_two])
    (by simp [σ2, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ2, tableEquiv] <;> decide)
    (by funext i; fin_cases i <;> simp [σ2, tableEquiv] <;> decide)
  have h3 := bound_shape24 H kind n σ3 {0, 5} (by ext x; fin_cases x <;> simp [σ3, tableEquiv, Fin.exists_fin_two])
    (by simp [σ3, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ3, tableEquiv] <;> decide)
    (by funext i; fin_cases i <;> simp [σ3, tableEquiv] <;> decide)
  have h4 := bound_shape42 H kind n σ4 {0, 3, 4, 5}
    (by ext x; fin_cases x <;> simp [σ4, tableEquiv, Fin.exists_fin_succ]) (by simp [σ4, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ4, tableEquiv] <;> decide)
  have h5 := bound_shape42 H kind n σ5 {0, 1, 4, 5}
    (by ext x; fin_cases x <;> simp [σ5, tableEquiv, Fin.exists_fin_succ]) (by simp [σ5, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ5, tableEquiv] <;> decide)
  have h6 := bound_shape42 H kind n σ6 {0, 1, 3, 4}
    (by ext x; fin_cases x <;> simp [σ6, tableEquiv, Fin.exists_fin_succ]) (by simp [σ6, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ6, tableEquiv] <;> decide)
  have h7 := bound_shape42 H kind n σ7 {0, 2, 3, 5}
    (by ext x; fin_cases x <;> simp [σ7, tableEquiv, Fin.exists_fin_succ]) (by simp [σ7, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ7, tableEquiv] <;> decide)
  have h8 := bound_shape42 H kind n σ8 {0, 1, 2, 5}
    (by ext x; fin_cases x <;> simp [σ8, tableEquiv, Fin.exists_fin_succ]) (by simp [σ8, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ8, tableEquiv] <;> decide)
  have h9 := bound_shape42 H kind n σ9 {0, 1, 2, 3}
    (by ext x; fin_cases x <;> simp [σ9, tableEquiv, Fin.exists_fin_succ]) (by simp [σ9, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ9, tableEquiv] <;> decide)
  have h10 := bound_shape6 H kind n
  linarith

end

end WaveTurbulence.FlowerP7
