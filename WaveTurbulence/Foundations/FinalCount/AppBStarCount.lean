/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBStarPhase
public import WaveTurbulence.Foundations.FinalCount.AppBCoupledTripleGoodGain
import Mathlib.Tactic

/-! # Actual five-label counting for two overlapping signed triple equations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset CountLemmas

/-- DH23 basiccount(4), canonical overlapping triples on an arbitrary
lattice coset. Integer momentum data are obtained from any nonempty fiber
in the physical-momentum wrapper. -/
theorem appb_star_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, 0 < L → ∀ ζ : Fin 3, ∀ w : Mom d,
    ∀ centers : Fin 5 → Mom d, ∀ nk1 nk2 : Fin d → ℤ, ∀ β1 β2 : ℝ,
    ∀ s : Finset (Fin 5 → (Fin d → ℤ)),
      (∀ q ∈ s, (∀ j,‖w+latticePoint L (q j)-centers j‖ ≤ 1) ∧
        q 0-q 1+q 2 = nk1 ∧
        (appbStarSecond ζ q).1-(appbStarSecond ζ q).2.1+(appbStarSecond ζ q).2.2 = nk2 ∧
        |‖w+latticePoint L (q 0)‖^2-‖w+latticePoint L (q 1)‖^2+‖w+latticePoint L (q 2)‖^2-β1| ≤ appbWidth δ γ m L ∧
        |‖w+latticePoint L (appbStarSecond ζ q).1‖^2-‖w+latticePoint L (appbStarSecond ζ q).2.1‖^2+
          ‖w+latticePoint L (appbStarSecond ζ q).2.2‖^2-β2| ≤ appbWidth δ γ m L) →
      (s.card : ℝ) ≤ L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) := by
  classical
  obtain ⟨L₀,hL₀⟩ := appb_coupled_triple_good_gain d hd γ hγ δ hδ m
  refine ⟨max L₀ 1,?_⟩
  intro L hL hLp ζ w centers nk1 nk2 β1 β2 s hs
  let phys := fun q : Fin 5 → (Fin d → ℤ) => fun j => w+latticePoint L (q j)
  let K1 := w+latticePoint L nk1
  let K2 := w+latticePoint L nk2
  have hm1 (q) (hq : q ∈ s) : phys q 0-phys q 1+phys q 2 = K1 := by
    dsimp only [phys,K1]
    rw [← (hs q hq).2.1,WeylSums.latticePoint_add_eq,WeylSums.latticePoint_sub_eq]
    abel
  have hm2 (q) (hq : q ∈ s) :
      (appbStarSecond ζ (phys q)).1-(appbStarSecond ζ (phys q)).2.1+
        (appbStarSecond ζ (phys q)).2.2 = K2 := by
    have hh := (hs q hq).2.2.1
    fin_cases ζ
    all_goals dsimp [appbStarSecond,appbStarShared,phys] at hh ⊢
    all_goals dsimp only [K2]
    all_goals rw [← hh,WeylSums.latticePoint_add_eq,WeylSums.latticePoint_sub_eq]
    all_goals abel
  have hdif (q : Fin 5 → (Fin d → ℤ)) : appbStarDifferences ζ (phys q) =
      (latticePoint L (appbStarDifferences ζ q).1,
        latticePoint L (appbStarDifferences ζ q).2.1,latticePoint L (appbStarDifferences ζ q).2.2) := by
    fin_cases ζ
    all_goals dsimp [appbStarDifferences,appbStarShared,phys]
    all_goals simp only [WeylSums.latticePoint_sub_eq]
    all_goals congr 1 <;> abel
  have hδp := hδ.1
  have hlog := Real.log_nonneg ((le_max_right L₀ 1).trans hL)
  have hτ : 0 ≤ appbWidth δ γ m L := by unfold appbWidth; positivity
  have hv : K1-K2 = latticePoint L (nk1-nk2) := by
    dsimp only [K1,K2]
    rw [WeylSums.latticePoint_sub_eq]
    abel
  let t := s.image (appbStarDifferences ζ)
  have hinj : Set.InjOn (appbStarDifferences (K := Fin d → ℤ) ζ) (s : Set _) := by
    intro q hq q' hq' he
    exact appb_star_differences_injective ζ nk1 nk2
      ⟨(hs q hq).2.1,(hs q hq).2.2.1⟩ ⟨(hs q' hq').2.1,(hs q' hq').2.2.1⟩ he
  have hb := hL₀ L ((le_max_left L₀ 1).trans hL) (centers 0-centers 1) (centers 2-centers 1)
    (if ζ = 2 then centers 3-centers (appbStarShared ζ) else centers (appbStarShared ζ)-centers 3)
    (nk1-nk2) ((‖K1‖^2-β1)/2) ((‖K2‖^2-β2)/2) ζ t (by
      intro u hu
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hu
      have hp := (hs q hq).1
      have he1 := appb_three_energy_band_bilinear (phys q 0) (phys q 1) (phys q 2) K1 β1 _ hτ (hm1 q hq) (hs q hq).2.2.2.1
      have he2 : |inner ℝ ((appbStarSecond ζ (phys q)).1-(appbStarSecond ζ (phys q)).2.1)
          ((appbStarSecond ζ (phys q)).2.2-(appbStarSecond ζ (phys q)).2.1)-(‖K2‖^2-β2)/2| ≤ appbWidth δ γ m L := by
        apply appb_three_energy_band_bilinear _ _ _ _ _ _ hτ (hm2 q hq)
        have hh := (hs q hq).2.2.2.2
        fin_cases ζ <;> exact hh
      rw [appb_star_second_factor ζ (phys q) K1 K2 (hm1 q hq) (hm2 q hq),hdif,hv] at he2
      refine ⟨?_,?_,?_,?_,he2⟩
      · exact appb_coset_difference_spatial_bound L w (q 0) (q 1) _ _ (hp 0) (hp 1)
      · exact appb_coset_difference_spatial_bound L w (q 2) (q 1) _ _ (hp 2) (hp 1)
      · fin_cases ζ
        all_goals exact appb_coset_difference_spatial_bound L w _ _ _ _ (hp _) (hp _)
      · change |inner ℝ (latticePoint L (q 0-q 1)) (latticePoint L (q 2-q 1))-((‖K1‖^2-β1)/2)| ≤ _
        rw [WeylSums.latticePoint_sub_eq,WeylSums.latticePoint_sub_eq]
        have hx : phys q 0-phys q 1 = latticePoint L (q 0)-latticePoint L (q 1) := by dsimp only [phys]; abel
        have hy : phys q 2-phys q 1 = latticePoint L (q 2)-latticePoint L (q 1) := by dsimp only [phys]; abel
        simpa only [hx,hy] using he1)
  rw [card_image_of_injOn hinj] at hb
  exact hb

end WaveTurbulence.Mole
