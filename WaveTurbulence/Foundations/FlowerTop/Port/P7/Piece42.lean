/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Level1Couple
/-! FLOWER-P7: the pieces whose second component is a couple (shapes `σ4 … σ9`): irreducible width-four block and
a couple. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset LGSpine

theorem joint1_allowed (P : WTParams) (p N : ℕ) (kind : TreeKind) {a b : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3))
    (d : ℕ × (Fin a → ℕ)) (e : ℕ × (Fin b → ℕ)) (h : Joint1 P p N kind σ d e) :
    (d.1 ≤ N ∧ ∀ i, d.2 i ≤ P.N (p + 1)) ∧ (e.1 ≤ N ∧ ∀ i, e.2 i ≤ P.N (p + 1)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨by omega, fun i => ?_⟩, ⟨by omega, fun i => ?_⟩⟩
  · have := h2.le (σ (.inl i))
    simpa [glueVec] using this
  · have := h2.le (σ (.inr i))
    simpa [glueVec] using this

open scoped Classical in
/-- **Pieces with an irreducible width-four first block and a couple second block.** -/
theorem piece42_norm_le (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (kind : TreeKind) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    (hmmax : 2 ≤ 10 * P.R (p + 1)) (hR1 : 1 ≤ P.R (p + 1)) (σ : Fin (2 * 2) ⊕ Fin 2 ≃ Fin (2 * 3))
    (i0 : Fin (2 * 2)) (hs2 : (fun i => childSig (σ (.inr i))) = ![1, -1])
    (n : Fin (2 * 3) → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin (2 * 3) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|)
    (hnumA : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (4 * 2 * P.Lambda (p + 1)) *
      gardenT P G.Cφ p 2 N' ^ (8 * 2 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 2) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) * P.L ^ (-((2 : ℕ) - 1 : ℝ) / 70) ≤ 1)
    (hnumB : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) *
      coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) ≤ P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) :
    ‖∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧
        MinimalAt y.garden (σ (.inl i0)) (Finset.univ.image fun i => σ (.inl i))},
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
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
          else 0 := by
  refine piece1_norm_le P (inputsF P Rr) p N kind σ i0 tt k n hF
    (fun d => d.1 ≤ N ∧ ∀ i, d.2 i ≤ P.N (p + 1)) (fun e => e.1 ≤ N ∧ ∀ i, e.2 i ≤ P.N (p + 1))
    (fun d e h => joint1_allowed P p N kind σ d e h) _ _ ?_ ?_
  · intro d _ ⟨hd, hv⟩
    exact Acomp1_slice_bound C₀ P G hp hN Rr hRr (m := 2) (by norm_num) hmmax σ i0 _ k (fun i => tt (σ (.inl i))) (fun i => htt _) d hd hv (hnumA d.1 (hd.trans hN))
  · intro e _ ⟨he, hv⟩
    exact couple_slice_bound C₀ P G hp hN Rr hRr hR1 σ hs2 _ k (fun i => tt (σ (.inr i))) (fun i => htt _) e he hv (hnumB e.1 (he.trans hN)) Creg hreg

end WaveTurbulence.FlowerP7
