/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestProp102
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestRhoAnalytic
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestInitialData
import Mathlib.Tactic

/-! # DH23 Proposition 10.2, third bound: the forest core

For a large-gap problem (not necessarily connected) whose balanced potential is at least
`-396 wn`, `Af ≲ L^(-η² ρ + η (wn+1))` for every `ρ` bounded by the active-link potential plus
one (DH23 L1834, proof L1913-L1917).  The connected and the small-gap versions are corollaries.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
open Set
universe u v

theorem prop102_rho_core (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η)
    (hηγ : η ≤ min γ (1-γ)) (hηs : 4*1440061*η ≤ 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ m : ℕ,∀ δ ∈ Ioc (0 : ℝ) 1,∀ C1 ≥ C₀,∃ L₀ : ℝ,
    ∀ (V : Type v) [DecidableEq V] (w : Mom d) (wn : ℕ),∀ L ≥ L₀,
    ∀ p : Problem.{u,v} V d L w c (L^(-γ+η)),GraphOk L m p.state →
    (-(396 : ℤ)*wn ≤ balancedPotential p.state.graph) →
    (p.state.graph.atoms.filter (fun a => p.state.graph.deg a ≠ 4)).card ≤ wn →
    ∀ ρ : ℕ,(ρ = 0 ∨ (ρ : ℤ) ≤ activeLinkPotential p.state.graph+1) →
    p.value γ δ C1 ≤ ENNReal.ofReal (L^(-η^2*(ρ : ℝ)+η*((wn : ℝ)+1))) := by
  obtain ⟨C₀,hC₀,hstep⟩ := exists_forest_step.{u,v} d hd γ η hγ hη hηγ c hc
  have hηC : η*1440061 ≤ 1/4 := by linarith only [hηs]
  obtain ⟨L₁,hL₁,hbud⟩ := budget_rho γ η ⟨hγ.1,hγ.2⟩ hη hηγ 1440061 hηC
  refine ⟨4*C₀,by linarith only [hC₀],?_⟩
  intro m δ hδ C1 hC1
  have hC1' : C₀ ≤ C1/4 := by linarith only [hC1]
  have hC1pos : 0 < C1 := by linarith only [hC1,hC₀]
  obtain ⟨Ls,hLs⟩ := hstep m δ hδ (C1/4) hC1'
  refine ⟨max Ls (max L₁ (max (Real.exp 1) ((16 : ℝ)^(3/η)))),?_⟩
  intro V _ w wn L hL p hpOk hnn hwn ρ hρ
  obtain ⟨hLs',hL'⟩ := max_le_iff.mp hL
  obtain ⟨hL₁',hL''⟩ := max_le_iff.mp hL'
  obtain ⟨hLe,hL16⟩ := max_le_iff.mp hL''
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hLe
  have hM := p.state.bonds_le_two_mul_atoms p.molecule
  have hB : (p.state.bondPotential : ℝ) ≤ 2*(1+Real.log L)^m := by
    have h1 : (p.state.bondPotential : ℝ) ≤ 2*p.state.graph.atoms.card := by
      unfold State.bondPotential; exact_mod_cast hM
    nlinarith only [h1,hpOk.2]
  set F := CountingForest.singleton.{u,v} (c := c) (w := w) γ η p with hFdef
  have hFok : ForestOk m F := by
    refine ⟨?_,?_⟩
    · intro q hq
      have hq' : q ∈ [p] := hq
      have : q = p := List.mem_singleton.mp hq'
      exact (congrArg (fun x : Problem.{u,v} V d L w c (L^(-γ+η)) => GraphOk L m x.state) this).mpr hpOk
    · change True
      trivial
  have hacct := forest_acct_of_steps (ForestOk m) forestPot forestSlack forestDefect forestAct forestHasBonds
    forestPhi (ENNReal.ofReal (Real.log L^8)) (ENNReal.ofReal (L^(-η/2)))
    (ENNReal.ofReal (L^(-5*min γ (1-γ)/8))) δ (C1/4)
    (fun F _ h => forestBase m F h)
    (fun F' hF' hne' => hLs V w _ L hLs' hB F' hF' hne') F hFok
  obtain ⟨n,kf,kg,hres,-,-,hact,hval⟩ := hacct
  have hSl : forestSlack F = 0 := forestSlack_global F rfl
  have hPot : forestPot F = balancedPotential p.state.graph := by
    change forestBalancedPotential [p.state] = _
    simp [forestBalancedPotential]
  have hAct : forestAct F = stateAct p.state := by
    change ([p.state].map stateAct).sum = _
    simp
  have hPhi : forestPhi F = p.state.graph.bonds.card := by
    change forestBonds [p.state] = _
    simp [forestBonds,State.bondPotential]
  have hVal : F.value δ (C1/4) = p.value γ δ (C1/4) := CountingForest.value_singleton γ η p δ (C1/4)
  have hresc : p.value γ δ C1 = ENNReal.ofReal ((1/4 : ℝ)^p.state.graph.circuitRank)*
      p.value γ δ (C1/4) := by
    have := linkCountA_rescale p.state.graph (d := d) L γ δ (C1/4) C1 (by linarith only [hC1pos])
      hC1pos w p.admissible p.scales
    have e : C1/4/C1 = 1/4 := by field_simp
    rw [e] at this
    exact this
  -- the choice factor
  have hbf := branch_factor_le_nonFour p.state.graph p.molecule wn hwn
  have h2 : ENNReal.ofReal ((2 : ℝ)^p.state.graph.bonds.card) =
      (2 : ℝ≥0∞)^p.state.graph.bonds.card := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  have e4 : ENNReal.ofReal ((1/4 : ℝ)^p.state.graph.circuitRank*(2 : ℝ)^p.state.graph.bonds.card) =
      ENNReal.ofReal ((1/4 : ℝ)^p.state.graph.circuitRank)*(2 : ℝ≥0∞)^p.state.graph.bonds.card := by
    rw [ENNReal.ofReal_mul (by positivity),h2]
  have hmain : p.value γ δ C1 ≤ ENNReal.ofReal ((4 : ℝ)^(2*wn))*
      ((ENNReal.ofReal (Real.log L^8))^n*(ENNReal.ofReal (L^(-η/2)))^kf*
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))^kg) := by
    rw [hresc]
    calc ENNReal.ofReal ((1/4 : ℝ)^p.state.graph.circuitRank)*p.value γ δ (C1/4)
        ≤ ENNReal.ofReal ((1/4 : ℝ)^p.state.graph.circuitRank)*
            (2^p.state.graph.bonds.card*(ENNReal.ofReal (Real.log L^8))^n*
              (ENNReal.ofReal (L^(-η/2)))^kf*(ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))^kg) := by
          gcongr
          rw [← hVal]
          have := hval
          rw [hPhi] at this
          exact this
      _ = ENNReal.ofReal ((1/4 : ℝ)^p.state.graph.circuitRank*(2 : ℝ)^p.state.graph.bonds.card)*
            ((ENNReal.ofReal (Real.log L^8))^n*(ENNReal.ofReal (L^(-η/2)))^kf*
              (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))^kg) := by
          rw [e4]
          ring
      _ ≤ ENNReal.ofReal ((4 : ℝ)^(2*wn))*((ENNReal.ofReal (Real.log L^8))^n*
            (ENNReal.ofReal (L^(-η/2)))^kf*(ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))^kg) := by
          gcongr
  -- budgets
  have hbudget : 2*n ≤ 48000*(kf+kg+(wn+1)) := by
    rw [hSl,hPot] at hres
    have : 2*(n : ℤ) ≤ 48000*((kf : ℤ)+kg+((wn : ℤ)+1)) := by omega
    exact_mod_cast this
  have hrho : ((ρ : ℕ) : ℝ) ≤ 1440061*((kf : ℝ)+kg+((wn+1 : ℕ) : ℝ)) := by
    have h2 := pendingSlack_nonneg p.state
    have h3 : stateAct p.state = activeLinkPotential p.state.graph+pendingSlack p.state := rfl
    rw [hAct] at hact
    have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg _
    have hk0 : (0 : ℤ) ≤ kf := Nat.cast_nonneg _
    have hg0 : (0 : ℤ) ≤ kg := Nat.cast_nonneg _
    have h4 : (ρ : ℤ) ≤ 60*((n : ℤ)+kf+kg)+1 := by
      rcases hρ with h0 | h1
      · subst h0; push_cast; omega
      · omega
    have h5 : (n : ℤ) ≤ 24000*((kf : ℤ)+kg+((wn : ℤ)+1)) := by
      have : 2*(n : ℤ) ≤ 48000*((kf : ℤ)+kg+((wn : ℤ)+1)) := by exact_mod_cast hbudget
      omega
    have h6 : (ρ : ℤ) ≤ 1440061*((kf : ℤ)+kg+((wn : ℤ)+1)) := by
      have : (0 : ℤ) ≤ wn := Nat.cast_nonneg _
      have : (0 : ℤ) ≤ kf := Nat.cast_nonneg _
      have : (0 : ℤ) ≤ kg := Nat.cast_nonneg _
      nlinarith only [h4,h5,‹(0:ℤ) ≤ wn›,‹(0:ℤ) ≤ kf›,‹(0:ℤ) ≤ kg›]
    have h7 : ((ρ : ℤ) : ℝ) ≤ ((1440061*((kf : ℤ)+kg+((wn : ℤ)+1)) : ℤ) : ℝ) := by
      exact_mod_cast h6
    push_cast at h7 ⊢
    exact h7
  have hB1 := (hbud L hL₁' n kf kg (wn+1) ρ hbudget hrho)
  -- the choice factor against L^((η/3) wn)
  have h16 : ENNReal.ofReal ((4 : ℝ)^(2*wn)) ≤ ENNReal.ofReal (L^((η/3)*(wn : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    have h1 : (16 : ℝ) ≤ L^(η/3) := by
      have h2 : (16 : ℝ)^(3/η) ≤ L := hL16
      have h3 := Real.rpow_le_rpow (by positivity) h2 (by positivity : 0 ≤ η/3)
      rw [← Real.rpow_mul (by norm_num)] at h3
      have : 3/η*(η/3) = 1 := by field_simp
      rw [this,Real.rpow_one] at h3
      exact h3
    have e : (4 : ℝ)^(2*wn) = 16^wn := by
      rw [pow_mul]; norm_num
    rw [e, Real.rpow_mul hLp.le,Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) h1 wn
  refine hmain.trans ?_
  calc ENNReal.ofReal ((4 : ℝ)^(2*wn))*((ENNReal.ofReal (Real.log L^8))^n*
          (ENNReal.ofReal (L^(-η/2)))^kf*(ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))^kg)
      ≤ ENNReal.ofReal (L^((η/3)*(wn : ℝ)))*ENNReal.ofReal (L^(-η^2*(ρ : ℝ)+(η/3)*((wn+1 : ℕ) : ℝ))) := by
        gcongr
    _ = ENNReal.ofReal (L^((η/3)*(wn : ℝ))*L^(-η^2*(ρ : ℝ)+(η/3)*((wn+1 : ℕ) : ℝ))) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hLp.le _)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.rpow_add hLp]
        apply Real.rpow_le_rpow_of_exponent_le hL1
        push_cast
        have : (0 : ℝ) ≤ wn := Nat.cast_nonneg _
        nlinarith only [this,hη]

end WaveTurbulence.Mole.AppbAlgorithm
