/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.TotalAssembly
/-! FLOWER-P7: counting of the component data (order, top-order vector) and the bound of the irreducible
width-six piece by a count times a single weight. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset LGSpine

/-- The box of top-order vectors. -/
def vecBox (w M : ℕ) : Finset (Fin w → ℕ) := Fintype.piFinset fun _ => Finset.range (M + 1)

theorem card_vecBox (w M : ℕ) : (vecBox w M).card = (M + 1) ^ w := by
  simp [vecBox, Fintype.card_piFinset]

theorem mem_vecBox {w M : ℕ} {v : Fin w → ℕ} (h : ∀ i, v i ≤ M) : v ∈ vecBox w M := by
  simp only [vecBox, Fintype.mem_piFinset, Finset.mem_range]
  exact fun i => Nat.lt_succ_of_le (h i)

open scoped Classical in
theorem card_data6 (P : WTParams) (p N : ℕ) (kind : TreeKind) :
    ((Irr6_finite P p N kind).toFinset.image (compData p)).card ≤ (P.N (p + 1) + 1) ^ 6 := by
  have hsub : (Irr6_finite P p N kind).toFinset.image (compData p) ⊆
      (vecBox (2 * 3) (P.N (p + 1))).image (fun v => (N - 2, v)) := by
    intro d hd
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hd
    have hy' := (Irr6_finite P p N kind).mem_toFinset.1 hy
    have hcond := hy'.1.2
    have hord : y.garden.order + 2 = N := hcond.2.2.2.1
    have hvk : VecKindOK (P.N (p + 1)) kind (fun i => y.topOrder p i) := hcond.2.2.2.2
    refine Finset.mem_image.2 ⟨fun i => y.topOrder p i, mem_vecBox (fun i => hvk.le i), ?_⟩
    simp only [compData, Prod.mk.injEq]
    exact ⟨by omega, trivial⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_image_le).trans ?_
  rw [card_vecBox]

open scoped Classical in
theorem Bound6_le (P : WTParams) (p N : ℕ) (kind : TreeKind) (k : Mom P.d) (n : Fin (2 * 3) → (Fin P.d → ℤ))
    (hδ : 0 < P.δ) (hL : 0 < P.L) :
    Bound6 P p N kind k n ≤ ((P.N (p + 1) + 1 : ℕ) : ℝ) ^ 6 *
      (jbrProdAt P.L k n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-(((3 : ℕ) : ℝ) - 1) / 4) *
        P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ))) := by
  unfold Bound6
  have hd1 : ∀ d ∈ (Irr6_finite P p N kind).toFinset.image (compData p), d.1 = N - 2 := by
    intro d hd
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hd
    have hy' := (Irr6_finite P p N kind).mem_toFinset.1 hy
    have hord : y.garden.order + 2 = N := hy'.1.2.2.2.2.1
    simp only [compData]; omega
  rw [Finset.sum_congr rfl fun d hd => by rw [hd1 d hd], Finset.sum_const, nsmul_eq_mul]
  have hJ : 0 < jbrProdAt P.L k n := Finset.prod_pos fun j _ => WaveTurbulence.Induct.jbr_pos _
  have hT : 0 ≤ jbrProdAt P.L k n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-(((3 : ℕ) : ℝ) - 1) / 4) *
      P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) := by positivity
  have hc := card_data6 P p N kind
  have hc' : (((Irr6_finite P p N kind).toFinset.image (compData p)).card : ℝ) ≤ ((P.N (p + 1) + 1 : ℕ) : ℝ) ^ 6 := by
    exact_mod_cast hc
  exact mul_le_mul_of_nonneg_right hc' hT

end WaveTurbulence.FlowerP7
