/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Level2b
/-! FLOWER-P7: the pieces whose first component is a couple and whose second component is a plain width-four
block (shapes `σ1 … σ3`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset LGSpine

theorem Acomp1_couple_mem_iff (P : WTParams) (p N : ℕ) {b : ℕ} (σ : Fin 2 ⊕ Fin b ≃ Fin (2 * 3))
    (hsA : (fun i => childSig (σ (.inl i))) = ![1, -1]) (i0 : Fin 2) (hi0 : i0 = 0)
    (d : ℕ × (Fin 2 → ℕ)) (hd : d.1 ≤ N) (hv : ∀ i, d.2 i ≤ P.N (p + 1)) (LA : LayeredGarden 2) :
    LA ∈ (Acomp1_finite P p N σ i0).toFinset.filter (fun LA => compData p LA = d) ↔
      (IsCanonC (p + 1) LA ∧ LA.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧ LA.garden.order = d.1) ∧
        ∀ j, LA.topOrder p j = d.2 j := by
  classical
  subst hi0
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Acomp1, Set.mem_ofPred_eq, compData, Prod.ext_iff,
    IsCanonC, IsCouple, Nat.add_sub_cancel]
  constructor
  · rintro ⟨⟨hs, ⟨hpl, hcr, hat⟩, hirr, hle⟩, hord, hvec⟩
    refine ⟨⟨⟨⟨hpl, hs.trans hsA⟩, hcr⟩, ⟨fun j => ?_, hat⟩, hord⟩, fun j => congrFun hvec j⟩
    rw [congrFun hvec j]; exact hv j
  · rintro ⟨⟨⟨⟨hpl, hs⟩, hcr⟩, htr, hord⟩, hvec⟩
    exact ⟨⟨hs.trans hsA.symm, ⟨hpl, hcr, htr.2⟩, irrAt_of_couple LA.garden hs, hord ▸ hd⟩, hord, funext hvec⟩

open scoped Classical in
/-- **Pieces with a couple first block and a plain width-four second block.** -/
theorem piece24_norm_le (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (kind : TreeKind) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    (hR1 : 1 ≤ P.R (p + 1)) (hmmax : 2 ≤ 10 * P.R (p + 1)) (σ : Fin 2 ⊕ Fin (2 * 2) ≃ Fin (2 * 3))
    (hsA : (fun i => childSig (σ (.inl i))) = ![1, -1])
    (hs4 : (fun i => childSig (σ (.inr i))) = ![1, -1, 1, -1])
    (n : Fin (2 * 3) → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin (2 * 3) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|)
    (hnumA : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (4 * 2 * P.Lambda (p + 1)) *
      gardenT P G.Cφ p 2 N' ^ (8 * 2 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 2) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) * P.L ^ (-((2 : ℕ) - 1 : ℝ) / 70) ≤ 1)
    (hnumC : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) *
      coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) ≤ P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) :
    ‖∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧
        MinimalAt y.garden (σ (.inl 0)) (Finset.univ.image fun i => σ (.inl i))},
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
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
          else 0 := by
  refine piece1_norm_le P (inputsF P Rr) p N kind σ 0 tt k n hF
    (fun d => d.1 ≤ N ∧ ∀ i, d.2 i ≤ P.N (p + 1)) (fun e => e.1 ≤ N ∧ ∀ i, e.2 i ≤ P.N (p + 1))
    (fun d e h => joint1_allowed P p N kind σ d e h) _ _ ?_ ?_
  · intro d _ ⟨hd, hv⟩
    exact couple_set_bound C₀ P G hp Rr hRr hR1 (hd.trans hN) (fun i => n (σ (.inl i))) k (fun i => tt (σ (.inl i))) (fun i => htt _) d.2
      (hnumC d.1 (hd.trans hN)) Creg hreg _
      (fun LA h => (Acomp1_couple_mem_iff P p N σ hsA 0 rfl d hd hv LA).1 h)
      (fun LA h => (Acomp1_couple_mem_iff P p N σ hsA 0 rfl d hd hv LA).2 h)
  · intro e _ ⟨he, hv⟩
    exact Bplain4_slice_bound C₀ P G hp hN Rr hRr hR1 hmmax σ hs4 e he hv _ k (fun i => tt (σ (.inr i))) (fun i => htt _) hF hnumA hnumC Creg hreg

end WaveTurbulence.FlowerP7
