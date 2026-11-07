/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Level1Sum
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Slices
/-! FLOWER-P7: slice bounds for the irreducible first component of a first-level piece. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset LGSpine

open scoped Classical in
theorem Acomp1_slice_eq (P : WTParams) (p N : ℕ) {b m : ℕ} (σ : Fin (2 * m) ⊕ Fin b ≃ Fin (2 * 3))
    (i0 : Fin (2 * m)) (hm2 : 2 ≤ m) (d : ℕ × (Fin (2 * m) → ℕ))
    (hd : d.1 ≤ N) (hv : ∀ i, d.2 i ≤ P.N (p + 1)) :
    (Acomp1_finite P p N σ i0).toFinset.filter (fun LA => compData p LA = d) =
      (gardenSet P p d.1 m (fun i => childSig (σ (.inl i)))).filter (fun LG => ∀ j, LG.topOrder p j = d.2 j) := by
  ext LA
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, gardenSet, Acomp1, Set.mem_ofPred_eq, compData,
    Prod.ext_iff]
  simp only [Nat.add_sub_cancel]
  constructor
  · rintro ⟨⟨hs, ⟨hpl, hcr, hat⟩, hirr, hle⟩, hord, hvec⟩
    refine ⟨⟨⟨hpl, Or.inl ⟨by omega, (irreducible_iff_irrAt LA.garden hpl i0).2 hirr⟩, hcr⟩,
      ⟨fun j => ?_, hat⟩, hs, hord⟩, fun j => congrFun hvec j⟩
    rw [congrFun hvec j]; exact hv j
  · rintro ⟨⟨⟨hpl, hir, hcr⟩, htr, hs, hord⟩, hvec⟩
    rcases hir with ⟨-, hirr⟩ | ⟨h2, -⟩
    · exact ⟨⟨hs, ⟨hpl, hcr, htr.2⟩, (irreducible_iff_irrAt LA.garden hpl i0).1 hirr, hord ▸ hd⟩, hord,
        funext hvec⟩
    · omega

open scoped Classical in
/-- **Slice bound for the irreducible first component** of a first-level piece (`m = 2, 3`). -/
theorem Acomp1_slice_bound (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) {b m : ℕ}
    (hm2 : 2 ≤ m) (hmmax : m ≤ 10 * P.R (p + 1)) (σ : Fin (2 * m) ⊕ Fin b ≃ Fin (2 * 3)) (i0 : Fin (2 * m))
    (n : Fin (2 * m) → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin (2 * m) → ℝ) (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (d : ℕ × (Fin (2 * m) → ℕ)) (hd : d.1 ≤ N) (hv : ∀ i, d.2 i ≤ P.N (p + 1))
    (hnum : ((P.d : ℝ) + 1) ^ (4 * m * P.Lambda (p + 1)) * gardenT P G.Cφ p m d.1 ^ (8 * m * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (d.1 + m) * P.δ ^ (6 * P.ν * d.1) * P.L ^ (-P.η ^ 7) * P.L ^ (-((m : ℝ) - 1) / 70) ≤ 1) :
    ‖∑ LA ∈ (Acomp1_finite P p N σ i0).toFinset.filter (fun LA => compData p LA = d),
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LA (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      jbrProdAt P.L k n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4) * P.δ ^ (2 * P.ν * d.1) := by
  rw [Acomp1_slice_eq P p N σ i0 hm2 d hd hv]
  by_cases hbal : IsBalancedSig (fun i => childSig (σ (.inl i)))
  · exact garden_slice_kernelKgen C₀ P G hp Rr hRr hm2 hmmax _ hbal n k (hd.trans hN) tt htt d.2 hnum
  · -- the slice is empty (plain gardens have balanced signatures)
    have hemp : (gardenSet P p d.1 m (fun i => childSig (σ (.inl i)))).filter
        (fun LG => ∀ j, LG.topOrder p j = d.2 j) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun LG hLG => hbal ?_
      have h1 := (Canon.finite_truncSum_support P (p + 1) d.1 (2 * m)
        (fun i => childSig (σ (.inl i)))).mem_toFinset.mp (Finset.mem_filter.1 hLG).1
      have hpl : LG.garden.IsPlain := h1.1.1
      have := Comb.balanced_of_plain hpl
      rw [← h1.2.2.1]
      exact this
    rw [hemp, Finset.sum_empty, norm_zero]
    have hL0 : 0 < P.L := by linarith [G.hs.L_ge]
    have hJ : 0 < jbrProdAt P.L k n := Finset.prod_pos fun j _ => WaveTurbulence.Induct.jbr_pos _
    have hδ : 0 < P.δ := G.hs.delta_pos
    positivity

end WaveTurbulence.FlowerP7
