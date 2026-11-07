/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountGoodRanges
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountSmallSum
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountExceptions
import Mathlib.Tactic

/-! # The actual canonical terminal K4 counting estimate

DH23 basiccount(5), in the canonical balanced K4 orientation. Every
counting constant precedes delta, conserved charges and all source centers.
The other balanced orientations are transported by the graph enumeration.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

/-- Actual canonical finite source families satisfy the terminal K4 power
saving; all local estimates and all exceptional fibers are derived. -/
theorem k4_canonical_finset_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ L₀ : ℝ,
      ∀ L ≥ L₀, ∀ (A : Fin 6 → Mom d) (a b c : Fin d → ℤ) (β : Fin 3 → ℝ)
      (S : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))),
      (∀ p ∈ S, p ∈ k4CanonicalSet L A a b c β (δ⁻¹*L^(-2*γ))) →
      (S.card : ℝ) ≤ C*(δ⁻¹)^3*L^(3*((d : ℝ)-γ)-(101 : ℝ)/100*min γ (1-γ)) := by
  classical
  obtain ⟨CB,LB,hCB,hbig⟩ := k4_full_small_source_bound d hd γ hγ
  obtain ⟨CL,hCL,hlarge⟩ := k4_large_source_bound d hd γ hγ
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hg : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
  have hK : 0 < k4BlockBoxConstant d := by unfold k4BlockBoxConstant; positivity
  have hε : 0 < min γ (1-γ)/100 := div_pos hg (by norm_num)
  have hCS : 0 < k4SmallSumConstant d γ := by unfold k4SmallSumConstant; positivity
  let B : ℝ := (3 : ℝ)^(2*d)
  let C := 2*B+CB+CL+k4SmallSumConstant d γ
  have hC : 0 < C := by dsimp only [C,B]; positivity
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨LL,hlargeδ⟩ := hlarge δ hδ
  refine ⟨max (max LB LL) 1,?_⟩
  intro L hL A a b c β S hS
  have hL1 : 1 ≤ L := (le_max_right (max LB LL) 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hLB : LB ≤ L := (le_max_left LB LL).trans ((le_max_left (max LB LL) 1).trans hL)
  have hLL : LL ≤ L := (le_max_right LB LL).trans ((le_max_left (max LB LL) 1).trans hL)
  have hD : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hD0 : 0 < δ⁻¹ := inv_pos.mpr hδ.1
  have hD3 : 1 ≤ (δ⁻¹)^3 := by
    simpa only [pow_zero] using pow_le_pow_right₀ hD (by norm_num : (0 : ℕ)≤3)
  let E := 3*((d : ℝ)-γ)-(101 : ℝ)/100*min γ (1-γ)
  let T := (δ⁻¹)^3*L^E
  let M := L^(1-min γ (1-γ)/10)
  let cut := k4CoefficientCut L γ
  let height := fun p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) =>
    ‖latticePoint L (k4SphereLabel b p.1 p.2.2)‖
  let coeff := fun p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) =>
    ‖latticePoint L c+latticePoint L p.2.1‖
  let S1 := S.filter (fun p => p.2.1=a)
  let S2 := S.filter (fun p => p.2.1= -c)
  let SL := S.filter (fun p => M < height p)
  let SB := S.filter (fun p => height p ≤ M ∧ cut ≤ coeff p)
  let SS := S.filter (fun p => height p ≤ M ∧ coeff p ≤ cut ∧ p.2.1 ≠ a ∧ p.2.1 ≠ -c)
  have hcover : S ⊆ S1 ∪ S2 ∪ SL ∪ SB ∪ SS := by
    intro p hp
    simp only [mem_union]
    by_cases h1 : p.2.1=a
    · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_filter.mpr ⟨hp,h1⟩))))
    by_cases h2 : p.2.1= -c
    · exact Or.inl (Or.inl (Or.inl (Or.inr (mem_filter.mpr ⟨hp,h2⟩))))
    by_cases hl : M < height p
    · exact Or.inl (Or.inl (Or.inr (mem_filter.mpr ⟨hp,hl⟩)))
    have hm : height p ≤ M := le_of_not_gt hl
    by_cases hb : cut ≤ coeff p
    · exact Or.inl (Or.inr (mem_filter.mpr ⟨hp,hm,hb⟩))
    exact Or.inr (mem_filter.mpr ⟨hp,hm,(lt_of_not_ge hb).le,h1,h2⟩)
  have hcardNat : S.card ≤ S1.card+S2.card+SL.card+SB.card+SS.card := by
    have hh := card_le_card hcover
    have h12 := card_union_le S1 S2
    have h123 := card_union_le (S1 ∪ S2) SL
    have h1234 := card_union_le (S1 ∪ S2 ∪ SL) SB
    have h12345 := card_union_le (S1 ∪ S2 ∪ SL ∪ SB) SS
    omega
  have hcard : (S.card : ℝ) ≤ (S1.card : ℝ)+(S2.card : ℝ)+(SL.card : ℝ)+(SB.card : ℝ)+(SS.card : ℝ) := by
    exact_mod_cast hcardNat
  have hbox : (2*L+1)^(2*d) ≤ B*T := by
    have hb : (2*L+1)^(2*d) ≤ (3 : ℝ)^(2*d)*L^(2*d) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith only [hL1]) _
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have he : ((2*d : ℕ) : ℝ) ≤ E := by
      simp only [Nat.cast_mul,Nat.cast_ofNat]
      exact k4_exception_exponent_le hd3 hγ.1.le hγ.2.le
    have hp : L^(2*d) ≤ L^E := by simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hL1 he
    have hp' : L^(2*d) ≤ (δ⁻¹)^3*L^E := hp.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD3 (Real.rpow_nonneg hLp.le E))
    exact hb.trans (mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ B))
  have h1 : (S1.card : ℝ) ≤ B*T := by
    apply (k4_fixed_middle_card_le S1 hLp (A 1) (A 2) a ?_).trans hbox
    intro p hp
    have hc := hS p (mem_filter.mp hp).1
    exact ⟨hc.1 1,hc.1 2,(mem_filter.mp hp).2⟩
  have h2 : (S2.card : ℝ) ≤ B*T := by
    apply (k4_fixed_middle_card_le S2 hLp (A 1) (A 2) (-c) ?_).trans hbox
    intro p hp
    have hc := hS p (mem_filter.mp hp).1
    exact ⟨hc.1 1,hc.1 2,(mem_filter.mp hp).2⟩
  have hSL : (SL.card : ℝ) ≤ CL*T := by
    have hh := hlargeδ L hLL A a b c β SL (fun p hp => hS p (mem_filter.mp hp).1)
      (fun p hp => (mem_filter.mp hp).2.le)
    have he : 3*((d : ℝ)-γ)-(11 : ℝ)/10*min γ (1-γ) ≤ E := by dsimp only [E]; linarith only [hg]
    have hres := hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 he) (by positivity : 0 ≤ CL*(δ⁻¹)^3))
    simpa only [T,mul_assoc] using hres
  have hSB : (SB.card : ℝ) ≤ CB*T := by
    have hh := hbig L hLB δ hδ A a b c β SB (fun p hp => hS p (mem_filter.mp hp).1)
      (fun p hp => (mem_filter.mp hp).2.2) (fun p hp => (mem_filter.mp hp).2.1)
    have he : 3*((d : ℝ)-γ)-(21 : ℝ)/20*min γ (1-γ) ≤ E := by dsimp only [E]; linarith only [hg]
    have hres := hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 he) (by positivity : 0 ≤ CB*(δ⁻¹)^3))
    simpa only [T,mul_assoc] using hres
  have hSS : (SS.card : ℝ) ≤ k4SmallSumConstant d γ*T := by
    have hh := k4_small_nonexception_source_le d hd SS hL1 hδ hγ.1 hγ.2 A a b c β
      (fun p hp => hS p (mem_filter.mp hp).1) (fun p hp => (mem_filter.mp hp).2.2.2.1)
      (fun p hp => (mem_filter.mp hp).2.2.2.2) (fun p hp => (mem_filter.mp hp).2.2.1)
      (fun p hp => (mem_filter.mp hp).2.1)
    have he : 3*((d : ℝ)-γ)-(104 : ℝ)/100*min γ (1-γ) ≤ E := by dsimp only [E]; linarith only [hg]
    have hres := hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 he) (by positivity : 0 ≤ k4SmallSumConstant d γ*(δ⁻¹)^3))
    simpa only [T,mul_assoc] using hres
  calc
    _ ≤ (S1.card : ℝ)+(S2.card : ℝ)+(SL.card : ℝ)+(SB.card : ℝ)+(SS.card : ℝ) := hcard
    _ ≤ B*T+B*T+CL*T+CB*T+k4SmallSumConstant d γ*T :=
      add_le_add (add_le_add (add_le_add (add_le_add h1 h2) hSL) hSB) hSS
    _ = _ := by dsimp only [C,T,E]; ring

/-- Canonical balanced-K4 local counting estimate with all source labels
and all three energy constraints retained. This is the analytic terminal
input for DH23 Proposition10.3. -/
theorem k4_canonical_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ L₀ : ℝ,
      ∀ L ≥ L₀, ∀ (A : Fin 6 → Mom d) (a b c : Fin d → ℤ) (β : Fin 3 → ℝ),
      (k4CanonicalSet L A a b c β (δ⁻¹*L^(-2*γ))).Finite ∧
      ((k4CanonicalSet L A a b c β (δ⁻¹*L^(-2*γ))).ncard : ℝ) ≤
        C*(δ⁻¹)^3*L^(3*((d : ℝ)-γ)-(101 : ℝ)/100*min γ (1-γ)) := by
  obtain ⟨C,hC,hcount⟩ := k4_canonical_finset_bound d hd γ hγ
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hcount δ hδ
  refine ⟨max L₀ 1,?_⟩
  intro L hL A a b c β
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right L₀ 1).trans hL)
  have hf := finite_k4CanonicalSet hLp A a b c β (δ⁻¹*L^(-2*γ))
  refine ⟨hf,?_⟩
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact hL₀ L ((le_max_left L₀ 1).trans hL) A a b c β hf.toFinset
    (fun p hp => hf.mem_toFinset.mp hp)

end WaveTurbulence.MoleProp
