/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerReg.Defs
public import WaveTurbulence.Foundations.XChain.FlowerDraft.GateProbes
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite
public import WaveTurbulence.Foundations.Spine.RegularParity
/-! FLOWER-REG: `regularCoupleSum` of kind `L0` without `∂_t` is a finite sum of `K_𝒬(t, k)` over a finite family of
canonical regular couples of order `N`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerReg
open WaveTurbulence WaveTurbulence.LGSpine MeasureTheory Finset Set
open scoped Classical

theorem finsum_pred_eq_sum {α : Type*} (c : α → Prop) (g : α → ℂ) (T : Finset α)
    (hT : ∀ a, c a → a ∈ T) :
    ∑ᶠ (a : α) (_ : c a), g a = ∑ a ∈ T.filter c, g a := by
  have hsub : (Function.support fun a => ∑ᶠ (_ : c a), g a) ⊆ ↑(T.filter c) := by
    intro a ha
    have hc : c a := by
      by_contra hnc
      exact ha (by simp [hnc])
    simp [hT a hc, hc]
  rw [finsum_eq_sum_of_support_subset _ hsub]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hc : c a := (Finset.mem_filter.1 ha).2
  simp [hc]

/-- The finite family of canonical regular couples of `coupleSum`'s carrier (kind `L0`, no `∂_t`). -/
noncomputable def regFamily (P : WTParams) (p N : ℕ) (t : ℝ) (k : Mom P.d) : Finset (LayeredGarden 2) :=
  (Canon.finite_canonC (p + 1) N).toFinset.filter
    (fun LG => (CoupleDataD.mk .L0 false t k).carries P p N LG ∧ IsRegularCouple LG.garden)

theorem regularCoupleSum_L0_eq (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (t : ℝ)
    (k : Mom P.d) :
    regularCoupleSum P F p N .L0 false t k = ∑ LG ∈ regFamily P p N t k, KQ P.L P.γ P.δ F LG t k := by
  unfold regularCoupleSum regFamily
  rw [finsum_pred_eq_sum _ _ (Canon.finite_canonC (p + 1) N).toFinset
    (fun LG h => (Set.Finite.mem_toFinset _).2 ⟨h.1.1, h.1.2.2.1.le⟩)]
  refine Finset.sum_congr (by ext a; simp only [Finset.mem_filter]) fun LG hLG => ?_
  obtain ⟨_, h, _⟩ := Finset.mem_filter.1 hLG
  have hcan : IsCanonC (p + 1) LG := h.1
  have hplain : LG.garden.IsPlain := hcan.1.1
  have hfix : (fun b : GBranch LG.garden.tree =>
      if (false : Bool) = true ∧ b.1.2 = [] then some t else none) = fun _ => none := by
    funext b
    simp
  rw [hfix, FlowerProbes.kernelKgen_noFix P.L P.γ P.δ F LG hplain (fun _ => t) 0 k (fun _ => 0) 0]
  simp only [KQ, KQstar, ite_self]

theorem regFamily_mem {P : WTParams} {p N : ℕ} {t : ℝ} {k : Mom P.d} {LG : LayeredGarden 2}
    (h : LG ∈ regFamily P p N t k) :
    IsCanonC (p + 1) LG ∧ LG.garden.order = N ∧ IsRegularCouple LG.garden := by
  obtain ⟨_, hc, hr⟩ := Finset.mem_filter.1 h
  exact ⟨hc.1, hc.2.2.1, hr⟩

theorem regFamily_order_pos {P : WTParams} {p N : ℕ} {t : ℝ} {k : Mom P.d} {LG : LayeredGarden 2}
    (h : LG ∈ regFamily P p N t k) : 1 ≤ N := by
  obtain ⟨_, hc, _⟩ := Finset.mem_filter.1 h
  obtain ⟨_, _, hord, hk, _⟩ := hc
  rw [← hord]
  have hle := LG.topOrder_le_order p 0
  have h1 := ((hk : ∀ j, _) 0).1
  omega

theorem regFamily_even {P : WTParams} {p N : ℕ} {t : ℝ} {k : Mom P.d} {LG : LayeredGarden 2}
    (h : LG ∈ regFamily P p N t k) : Even N := by
  obtain ⟨_, hord, hreg⟩ := regFamily_mem h
  exact hord ▸ even_order_of_regular LG.garden hreg

end WaveTurbulence.FlowerReg
