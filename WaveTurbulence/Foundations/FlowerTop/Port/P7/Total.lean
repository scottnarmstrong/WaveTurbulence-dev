/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Piece24
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Level0
/-! FLOWER-P7: the norm of the six-tree sum over the decapitated carrier `Y6Set`, at fixed outer root labels,
is bounded by the sum of the explicit bounds of the sixteen pieces. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset LGSpine

/-- Explicit bound of an irreducible width-six piece. -/
noncomputable def Bound6 (P : WTParams) (p N : ℕ) (kind : TreeKind) (k : Mom P.d)
    (n : Fin (2 * 3) → (Fin P.d → ℤ)) : ℝ :=
  open scoped Classical in
  ∑ d ∈ (Irr6_finite P p N kind).toFinset.image (compData p),
    jbrProdAt P.L k n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-(((3 : ℕ) : ℝ) - 1) / 4) *
      P.δ ^ (2 * P.ν * d.1)

/-- Explicit bound of a piece with irreducible width-four first block and a couple second block. -/
noncomputable def Bound42 (P : WTParams) (p N : ℕ) (kind : TreeKind) (σ : Fin (2 * 2) ⊕ Fin 2 ≃ Fin (2 * 3))
    (i0 : Fin (2 * 2)) (Creg : ℕ → ℝ) (k : Mom P.d) (n : Fin (2 * 3) → (Fin P.d → ℤ)) : ℝ :=
  open scoped Classical in
  ∑ d ∈ (Acomp1_finite P p N σ i0).toFinset.image (compData p),
    ∑ e ∈ (Bcomp1_finite P p N (a := 2 * 2) σ).toFinset.image (compData p),
      if Joint1 P p N kind σ d e then
        (jbrProdAt P.L k (fun i => n (σ (.inl i))) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
            P.L ^ (-(((2 : ℕ) : ℝ) - 1) / 4) * P.δ ^ (2 * P.ν * d.1)) *
          (if n (σ (.inr 0)) = n (σ (.inr 1)) then
            jbr (k + latticePoint P.L (n (σ (.inr 0)))) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
              (P.δ ^ (2 * P.ν * e.1) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
                Creg e.1 * P.δ ^ ((e.1 : ℝ) / 4))
          else 0)
      else 0

/-- Explicit bound of a piece with a couple first block and a plain width-four second block. -/
noncomputable def Bound24 (P : WTParams) (p N : ℕ) (kind : TreeKind) (σ : Fin 2 ⊕ Fin (2 * 2) ≃ Fin (2 * 3))
    (Creg : ℕ → ℝ) (k : Mom P.d) (n : Fin (2 * 3) → (Fin P.d → ℤ)) : ℝ :=
  open scoped Classical in
  ∑ d ∈ (Acomp1_finite P p N σ (0 : Fin 2)).toFinset.image (compData p),
    ∑ e ∈ (Bcomp1_finite P p N (a := 2) σ).toFinset.image (compData p),
      if Joint1 P p N kind σ d e then
        (if n (σ (.inl 0)) = n (σ (.inl 1)) then
          jbr (k + latticePoint P.L (n (σ (.inl 0)))) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
            (P.δ ^ (2 * P.ν * d.1) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
              Creg d.1 * P.δ ^ ((d.1 : ℝ) / 4)) else 0) *
        (PieceBound2 P p N τ1 (fun i => childSig (σ (.inr i))) e Creg (fun i => n (σ (.inr i))) k +
          PieceBound2 P p N τ2 (fun i => childSig (σ (.inr i))) e Creg (fun i => n (σ (.inr i))) k +
          jbrProdAt P.L k (fun i => n (σ (.inr i))) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
            P.L ^ (-(((2 : ℕ) : ℝ) - 1) / 4) * P.δ ^ (2 * P.ν * e.1))
      else 0

/-- The shared hypotheses of the piece bounds. -/
structure PieceHyp (C₀ : ℕ) (P : WTParams) (p N : ℕ) (Rr : ℕ → Mom P.d → ℝ) (k : Mom P.d)
    (tt : Fin (2 * 3) → ℝ) (Creg : ℕ → ℝ) where
  G : LGContext C₀ P
  hp : p < P.D
  hN : N ≤ P.N (p + 1) ^ 4
  hRr : RemainderBound P Rr p
  hR1 : 1 ≤ P.R (p + 1)
  hmmax : 3 ≤ 10 * P.R (p + 1)
  htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)
  hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|
  hnum6 : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (4 * 3 * P.Lambda (p + 1)) *
    gardenT P G.Cφ p 3 N' ^ (8 * 3 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 3) * P.δ ^ (6 * P.ν * N') *
    P.L ^ (-P.η ^ 7) * P.L ^ (-((3 : ℕ) - 1 : ℝ) / 70) ≤ 1
  hnumA : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (4 * 2 * P.Lambda (p + 1)) *
    gardenT P G.Cφ p 2 N' ^ (8 * 2 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 2) * P.δ ^ (6 * P.ν * N') *
    P.L ^ (-P.η ^ 7) * P.L ^ (-((2 : ℕ) - 1 : ℝ) / 70) ≤ 1
  hnumC : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) *
    coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') *
    P.L ^ (-P.η ^ 7) ≤ P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))
  hreg : RegularFamilyBound P (inputsF P Rr) p Creg

end WaveTurbulence.FlowerP7
