/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SGRemoval
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestInitialData
public import WaveTurbulence.Foundations.FinalCount.Algorithm.LadderCover
import Mathlib.Tactic

/-! # The bound for one exceptional set (DH23 L1834, SG atoms removed first)

For a fixed exceptional set `S` of at most `wn` atoms, deleting `S` costs at most
`L^((16 d+4) wn)` (box count of the at most `8 wn` removed bonds, `(log L)^(4 wn)` for the
links), and the post problem, which is large gap everywhere, falls under the forest core with
`5 wn` atoms of degree other than four and active-link potential at least that of the original
minus `18 wn`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
open Finset Set
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L c : ℝ} {w : Mom d}

theorem sg_term_bound {ws wn : ℕ} (m : ℕ) (γ η δ C1 : ℝ) (hγd : γ ≤ d)
    (hL4 : 4 ≤ L) (hlog : 1 ≤ Real.log L) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1)
    (p : ProblemSG.{u,v} V d L w c (L^(-γ+η)) ws) (hpOk : GraphOk L m p.state)
    (hconn : ∀ a ∈ p.state.graph.atoms,∀ b ∈ p.state.graph.atoms,p.state.graph.SameComponent a b)
    (hne : p.state.graph.atoms.Nonempty)
    (hwn : (p.state.graph.atoms.filter (fun a => p.state.graph.deg a ≠ 4)).card ≤ wn)
    (S : Finset V) (hS : S ⊆ p.state.graph.atoms) (hSc : S.card ≤ wn)
    (hcore : ∀ p' : Problem.{u,v} V d L w c (L^(-γ+η)), GraphOk L m p'.state →
      (-(396 : ℤ)*((5*wn : ℕ) : ℤ) ≤ balancedPotential p'.state.graph) →
      (p'.state.graph.atoms.filter (fun a => p'.state.graph.deg a ≠ 4)).card ≤ 5*wn →
      ∀ ρ : ℕ,(ρ = 0 ∨ (ρ : ℤ) ≤ activeLinkPotential p'.state.graph+1) →
      p'.value γ δ C1 ≤ ENNReal.ofReal (L^(-η^2*(ρ : ℝ)+η*(((5*wn : ℕ) : ℝ)+1)))) :
    appbLinkCountA p.state.graph L γ δ C1 w
      (fun κ => p.admissible κ ∧ AppbLargeGapOff p.state.graph S L w κ (L^(-γ+η))) p.scales ≤
    ENNReal.ofReal (L^((16*d+4)*wn)*
      L^(-η^2*(sourceRho p.state.graph : ℝ)+18*η^2*(wn : ℝ)+η*(5*(wn : ℝ)+1))) := by
  have hL1 : 1 ≤ L := by linarith only [hL4]
  have hLp : 0 < L := by linarith only [hL4]
  obtain ⟨P,r,hrS,hlen,hcard⟩ := exists_removal p.state.graph p.molecule S hS hne
  subst hrS
  have hrank : r.post.circuitRank ≤ p.state.graph.circuitRank := by
    change (Degen.eraseAtoms p.state.graph r.removedAtoms).circuitRank ≤ _
    exact circuitRank_eraseAtoms_le p.state.graph r.removedAtoms hS
  obtain ⟨q,hq⟩ := appb_deletion_value_le p.state.graph p.molecule r L γ δ C1 w
    (fun κ => p.admissible κ ∧ AppbLargeGapOff p.state.graph r.removedAtoms L w κ (L^(-γ+η)))
    p.scales hL1 hlog hδ hC1 hγd p.scales_nonneg hrank
  have hpost : appbLinkCountA r.post L γ δ C1 w
      (r.conditionedPostAdmissibility
        (fun κ => p.admissible κ ∧ AppbLargeGapOff p.state.graph r.removedAtoms L w κ (L^(-γ+η))) q)
      p.scales = (p.post r q).value γ δ C1 := rfl
  rw [hpost] at hq
  refine hq.trans ?_
  -- hypotheses of the core for the post problem
  have hnonfour := card_nonFour_eraseAtoms_le p.state.graph p.molecule r.removedAtoms hS
  have hnf : ((p.post r q).state.graph.atoms.filter
      (fun a => (p.post r q).state.graph.deg a ≠ 4)).card ≤ 5*wn := by
    change ((Degen.eraseAtoms p.state.graph r.removedAtoms).atoms.filter
      (fun a => (Degen.eraseAtoms p.state.graph r.removedAtoms).deg a ≠ 4)).card ≤ _
    omega
  have hok : GraphOk L m (p.post r q).state := by
    refine ⟨appb_eraseAtoms_noTripleBonds p.state.graph r.removedAtoms hpOk.1,?_⟩
    refine le_trans ?_ hpOk.2
    exact_mod_cast Finset.card_le_card (sdiff_subset (s := p.state.graph.atoms) (t := r.removedAtoms))
  have hpot : -(396 : ℤ)*((5*wn : ℕ) : ℤ) ≤ balancedPotential (p.post r q).state.graph :=
    balancedPotential_ge_nonFour_disconnected _ (p.post r q).molecule (5*wn) hnf
  have hρM := sourceRho_le_active_add_one p.state.graph p.molecule hconn
  have hdrop := deletion_activePotential_drop_le r
  have hρ : (sourceRho p.state.graph-18*wn = 0) ∨
      (((sourceRho p.state.graph-18*wn : ℕ) : ℤ) ≤ activeLinkPotential (p.post r q).state.graph+1) := by
    by_cases h : sourceRho p.state.graph ≤ 18*wn
    · exact Or.inl (Nat.sub_eq_zero_of_le h)
    · right
      change _ ≤ activeLinkPotential r.post+1
      have h2 : ((sourceRho p.state.graph-18*wn : ℕ) : ℤ) = (sourceRho p.state.graph : ℤ)-18*wn := by
        omega
      omega
  have hval := hcore (p.post r q) hok hpot hnf _ hρ
  -- numerics
  have ha1 : (1 : ℝ) ≤ ((⌈2*L+1⌉₊ : ℕ) : ℝ) := by
    have := Nat.le_ceil (2*L+1)
    linarith only [this,hL4]
  have ha2 : ((⌈2*L+1⌉₊ : ℕ) : ℝ) ≤ L^2 := by
    have := Nat.ceil_lt_add_one (by linarith only [hL4] : 0 ≤ 2*L+1)
    nlinarith only [this,hL4]
  have hbox : ((⌈2*L+1⌉₊ : ℕ) : ℝ)^(d*P.edges.length) ≤ L^(16*d*wn) := by
    calc _ ≤ ((⌈2*L+1⌉₊ : ℕ) : ℝ)^(d*(8*wn)) := by
          apply pow_le_pow_right₀ ha1
          apply Nat.mul_le_mul_left
          omega
      _ ≤ (L^2)^(d*(8*wn)) := pow_le_pow_left₀ (by linarith only [ha1]) ha2 _
      _ = L^(16*d*wn) := by rw [← pow_mul]; congr 1; ring
  have hlg : (Real.log L)^(4*r.removedAtoms.card) ≤ L^(4*wn) := by
    calc _ ≤ (Real.log L)^(4*wn) := pow_le_pow_right₀ hlog (by omega)
      _ ≤ L^(4*wn) := pow_le_pow_left₀ (by linarith only [hlog]) (Real.log_le_self hLp.le) _
  have hfac : ((⌈2*L+1⌉₊ : ℕ) : ℝ)^(d*P.edges.length)*(Real.log L)^(4*r.removedAtoms.card) ≤
      L^((16*d+4)*wn) := by
    calc _ ≤ L^(16*d*wn)*L^(4*wn) :=
          mul_le_mul hbox hlg (by positivity) (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; ring
  have hρ' : (sourceRho p.state.graph : ℝ)-18*wn ≤ ((sourceRho p.state.graph-18*wn : ℕ) : ℝ) := by
    have : (sourceRho p.state.graph : ℤ)-18*wn ≤ ((sourceRho p.state.graph-18*wn : ℕ) : ℤ) := by omega
    exact_mod_cast this
  have hexp : L^(-η^2*((sourceRho p.state.graph-18*wn : ℕ) : ℝ)+η*(((5*wn : ℕ) : ℝ)+1)) ≤
      L^(-η^2*(sourceRho p.state.graph : ℝ)+18*η^2*(wn : ℝ)+η*(5*(wn : ℝ)+1)) := by
    apply Real.rpow_le_rpow_of_exponent_le hL1
    push_cast
    nlinarith only [hρ',sq_nonneg η]
  calc _ ≤ ENNReal.ofReal (((⌈2*L+1⌉₊ : ℕ) : ℝ)^(d*P.edges.length)*
          (Real.log L)^(4*r.removedAtoms.card))*
        ENNReal.ofReal (L^(-η^2*((sourceRho p.state.graph-18*wn : ℕ) : ℝ)+η*(((5*wn : ℕ) : ℝ)+1))) :=
        mul_le_mul_right hval _
    _ = ENNReal.ofReal ((((⌈2*L+1⌉₊ : ℕ) : ℝ)^(d*P.edges.length)*
          (Real.log L)^(4*r.removedAtoms.card))*
        L^(-η^2*((sourceRho p.state.graph-18*wn : ℕ) : ℝ)+η*(((5*wn : ℕ) : ℝ)+1))) := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((⌈2*L+1⌉₊ : ℕ) : ℝ)^(d*P.edges.length)*
          (Real.log L)^(4*r.removedAtoms.card))]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul hfac hexp (Real.rpow_nonneg hLp.le _) (by positivity)

end WaveTurbulence.Mole.AppbAlgorithm
