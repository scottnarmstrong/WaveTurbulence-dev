/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SGTerm
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestRhoCore
public import WaveTurbulence.Foundations.FinalCount.AppBPairGoodGain
import Mathlib.Tactic

/-! # DH23 Proposition 10.2, third bound, with at most `w` small-gap atoms

`Af ≲ L^(-η² ρ + C (w+1))` for a connected decoration problem with at most `w` atoms of degree
other than four, all of whose admissible decorations are large gap off at most `w` atoms
(DH23 L1834; the proof reduces to the large-gap case by removing the SG atoms, L1913-L1917).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
open Finset Set Filter
universe u v

theorem card_small_subsets_le {α : Type*} [DecidableEq α] (s : Finset α) (w : ℕ)
    (hs : 1 ≤ s.card) :
    (s.powerset.filter (fun S => S.card ≤ w)).card ≤ (w+1)*s.card^w := by
  have hsub : s.powerset.filter (fun S => S.card ≤ w) ⊆
      (range (w+1)).biUnion (fun k => powersetCard k s) := by
    intro S hS
    obtain ⟨h1,h2⟩ := mem_filter.mp hS
    exact mem_biUnion.mpr ⟨S.card,mem_range.mpr (by omega),
      mem_powersetCard.mpr ⟨mem_powerset.mp h1,rfl⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ range (w+1),(powersetCard k s).card := card_biUnion_le
    _ ≤ ∑ _k ∈ range (w+1),s.card^w := by
      apply sum_le_sum
      intro k hk
      rw [card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right hs (by have := mem_range.mp hk; omega))
    _ = (w+1)*s.card^w := by simp

theorem prop102_rho_sg (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η)
    (hηγ : η ≤ min γ (1-γ)) (hηs : 4*1440061*η ≤ 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ m : ℕ,∀ δ ∈ Ioc (0 : ℝ) 1,∀ C1 ≥ C₀,∃ L₀ : ℝ,
    ∀ (V : Type v) [DecidableEq V] (w : Mom d) (wn : ℕ),∀ L ≥ L₀,
    ∀ p : ProblemSG.{u,v} V d L w c (L^(-γ+η)) wn,GraphOk L m p.state →
    (∀ a ∈ p.state.graph.atoms,∀ b ∈ p.state.graph.atoms,p.state.graph.SameComponent a b) →
    p.state.graph.atoms.Nonempty →
    (p.state.graph.atoms.filter (fun a => p.state.graph.deg a ≠ 4)).card ≤ wn →
    p.value γ δ C1 ≤ ENNReal.ofReal
      (L^(-η^2*(sourceRho p.state.graph : ℝ)+(16*(d : ℝ)+28)*((wn : ℝ)+1))) := by
  obtain ⟨C₀,hC₀,h⟩ := prop102_rho_core.{u,v} d hd γ η hγ hη hηγ hηs c hc
  refine ⟨C₀,hC₀,fun m δ hδ C1 hC1 => ?_⟩
  obtain ⟨L₁,hL₁⟩ := h m δ hδ C1 hC1
  have hev := appb_log_coefficient_eventual 2 1 0 1 m (by norm_num)
  obtain ⟨L₂,hL₂⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max L₁ (max L₂ (max 4 (Real.exp 1))),?_⟩
  intro V _ w wn L hL p hpOk hconn hne hwn
  obtain ⟨hL1,hL'⟩ := max_le_iff.mp hL
  obtain ⟨hL2,hL''⟩ := max_le_iff.mp hL'
  obtain ⟨hL4,hLe⟩ := max_le_iff.mp hL''
  have hLp : 0 < L := by linarith only [hL4]
  have hL1' : 1 ≤ L := by linarith only [hL4]
  have hlog : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hLp]; exact hLe
  have hη1 : η ≤ 1 := by linarith only [hηs,hη]
  have hγd : γ ≤ d := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hγ.2,this]
  have hcoreL := hL₁ V w
  have hterm : ∀ S ∈ p.state.graph.atoms.powerset.filter (fun S => S.card ≤ wn),
      appbLinkCountA p.state.graph L γ δ C1 w
        (fun κ => p.admissible κ ∧ AppbLargeGapOff p.state.graph S L w κ (L^(-γ+η))) p.scales ≤
      ENNReal.ofReal (L^((16*d+4)*wn)*
        L^(-η^2*(sourceRho p.state.graph : ℝ)+18*η^2*(wn : ℝ)+η*(5*(wn : ℝ)+1))) := by
    intro S hS
    obtain ⟨h1,h2⟩ := mem_filter.mp hS
    exact sg_term_bound m γ η δ C1 hγd hL4 hlog hδ (by linarith only [hC1,hC₀]) p hpOk hconn hne hwn S
      (mem_powerset.mp h1) h2 (fun p' => hcoreL (5*wn) L hL1 p')
  have hn1 : 1 ≤ p.state.graph.atoms.card := Finset.card_pos.mpr hne
  have hT := card_small_subsets_le p.state.graph.atoms wn hn1
  have hpoly : 2*(1+Real.log L)^m ≤ L := by
    have := hL₂ L hL2
    simpa [Real.rpow_zero,Real.rpow_one] using this
  have hTr : ((p.state.graph.atoms.powerset.filter (fun S => S.card ≤ wn)).card : ℝ) ≤ L^wn := by
    have h1 : ((p.state.graph.atoms.powerset.filter (fun S => S.card ≤ wn)).card : ℝ) ≤
        ((wn+1 : ℕ) : ℝ)*(p.state.graph.atoms.card : ℝ)^wn := by exact_mod_cast hT
    have h2 : ((wn+1 : ℕ) : ℝ) ≤ 2^wn := by exact_mod_cast Nat.lt_two_pow_self
    have h3 : (p.state.graph.atoms.card : ℝ)^wn ≤ ((1+Real.log L)^m)^wn :=
      pow_le_pow_left₀ (by positivity) hpOk.2 wn
    calc _ ≤ _ := h1
      _ ≤ 2^wn*((1+Real.log L)^m)^wn := mul_le_mul h2 h3 (by positivity) (by positivity)
      _ = (2*(1+Real.log L)^m)^wn := by rw [mul_pow]
      _ ≤ L^wn := pow_le_pow_left₀ (by positivity) hpoly wn
  calc p.value γ δ C1 ≤ _ := p.value_le_sum γ δ C1
    _ ≤ ∑ _S ∈ p.state.graph.atoms.powerset.filter (fun S => S.card ≤ wn),
        ENNReal.ofReal (L^((16*d+4)*wn)*
          L^(-η^2*(sourceRho p.state.graph : ℝ)+18*η^2*(wn : ℝ)+η*(5*(wn : ℝ)+1))) :=
      sum_le_sum hterm
    _ = ((p.state.graph.atoms.powerset.filter (fun S => S.card ≤ wn)).card : ℝ≥0∞)*
        ENNReal.ofReal (L^((16*d+4)*wn)*
          L^(-η^2*(sourceRho p.state.graph : ℝ)+18*η^2*(wn : ℝ)+η*(5*(wn : ℝ)+1))) := by
      rw [sum_const,nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (L^wn)*ENNReal.ofReal (L^((16*d+4)*wn)*
          L^(-η^2*(sourceRho p.state.graph : ℝ)+18*η^2*(wn : ℝ)+η*(5*(wn : ℝ)+1))) := by
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hTr
    _ = ENNReal.ofReal (L^wn*(L^((16*d+4)*wn)*
          L^(-η^2*(sourceRho p.state.graph : ℝ)+18*η^2*(wn : ℝ)+η*(5*(wn : ℝ)+1)))) := by
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ L^wn)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [← mul_assoc,← pow_add,← Real.rpow_natCast,← Real.rpow_add hLp]
      apply Real.rpow_le_rpow_of_exponent_le hL1'
      push_cast
      have hw0 : (0 : ℝ) ≤ wn := Nat.cast_nonneg _
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      have hη2 : η^2 ≤ 1 := by nlinarith only [hη,hη1]
      nlinarith only [hw0,hd0,hη2,hη1,hη,mul_nonneg hw0 hd0,mul_le_mul_of_nonneg_right hη2 hw0,
        mul_le_mul_of_nonneg_right hη1 hw0]

end WaveTurbulence.Mole.AppbAlgorithm
