/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestStepMain
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestAnalytic
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BranchNormalization
public import WaveTurbulence.Foundations.FinalCount.Algorithm.InitialStatistics
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalizationRescale
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DefectPotential
import Mathlib.Tactic

/-! # DH23 Proposition 10.2, the two dense bounds, from the forest accounting

For a connected input problem without triple bonds, with at most `(1+log L)^m`
atoms, the scheduled forest accounting (`forest_acct_of_steps` with the
proved step supply `exists_forest_step`) gives
`Af <= 2^E (log L)^(8n) (L^(-η/2))^kf (L^(-5γ0/8))^kg` with `2n <= 48000 (kf+kg)`.
The first source case (`E = 2V-1`) forces a good step through the defect
potential and the second (`E = 2V-2 > 0`) forces a counted step through
the progress clause. The choice-tree factor `2^E` is absorbed by raising `C1`
by four (`branch_factor_le_one_dense`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
open Set
universe u v

theorem prop102_dense (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η)
    (hηγ : η ≤ min γ (1-γ)) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ m : ℕ,∀ δ ∈ Ioc (0 : ℝ) 1,∀ C1 ≥ C₀,∃ L₀ : ℝ,
    ∀ (V : Type v) [DecidableEq V] (w : Mom d),∀ L ≥ L₀,
    ∀ p : Problem.{u,v} V d L w c (L^(-γ+η)),GraphOk L m p.state →
    (∀ a ∈ p.state.graph.atoms,∀ b ∈ p.state.graph.atoms,p.state.graph.SameComponent a b) →
    p.state.graph.atoms.Nonempty →
    (((p.state.graph.bonds.card : ℤ) = 2*(p.state.graph.atoms.card : ℤ)-1 →
        p.value γ δ C1 ≤ ENNReal.ofReal (L^(-3*min γ (1-γ)/5))) ∧
      ((p.state.graph.bonds.card : ℤ) = 2*(p.state.graph.atoms.card : ℤ)-2 →
        0 < p.state.graph.bonds.card →
        p.value γ δ C1 ≤ ENNReal.ofReal (L^(-η/3)))) := by
  obtain ⟨C₀,hC₀,hstep⟩ := exists_forest_step.{u,v} d hd γ η hγ hη hηγ c hc
  obtain ⟨L₁,hL₁,hbud⟩ := budget_final γ η ⟨hγ.1,hγ.2⟩ hη hηγ
  refine ⟨4*C₀,by linarith only [hC₀],?_⟩
  intro m δ hδ C1 hC1
  have hC1' : C₀ ≤ C1/4 := by linarith only [hC1]
  have hC1pos : 0 < C1 := by linarith only [hC1,hC₀]
  obtain ⟨Ls,hLs⟩ := hstep m δ hδ (C1/4) hC1'
  refine ⟨max Ls (max L₁ (Real.exp 1)),?_⟩
  intro V _ w L hL p hpOk hconn hne
  obtain ⟨hLs',hL'⟩ := max_le_iff.mp hL
  obtain ⟨hL₁',hLe⟩ := max_le_iff.mp hL'
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hM := p.state.bonds_le_two_mul_atoms p.molecule
  have hB : (p.state.bondPotential : ℝ) ≤ 2*(1+Real.log L)^m := by
    have h1 : (p.state.bondPotential : ℝ) ≤ 2*p.state.graph.atoms.card := by
      unfold State.bondPotential; exact_mod_cast hM
    nlinarith only [h1,hpOk.2]
  set F := CountingForest.singleton.{u,v} (c := c) (w := w) γ η p with hFdef
  have hFp : F.problems = [p] := rfl
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hLe
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
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
  obtain ⟨n,kf,kg,hres,hdef,hprog,-,hval⟩ := hacct
  have hSl : forestSlack F = 0 := forestSlack_global F rfl
  have hPot : forestPot F = balancedPotential p.state.graph := by
    change forestBalancedPotential [p.state] = _
    simp [forestBalancedPotential]
  have hDp : forestDefect F = defectPotential p.state.graph := by
    change forestDefectPotential [p.state] = _
    simp [forestDefectPotential]
  have hPhi : forestPhi F = p.state.graph.bonds.card := by
    change forestBonds [p.state] = _
    simp [forestBonds,State.bondPotential]
  have hVal : F.value δ (C1/4) = p.value γ δ (C1/4) := CountingForest.value_singleton γ η p δ (C1/4)
  -- rescale: C1/4 -> C1 pays 2^E
  have hresc : p.value γ δ C1 = ENNReal.ofReal ((1/4 : ℝ)^p.state.graph.circuitRank)*
      p.value γ δ (C1/4) := by
    have := linkCountA_rescale p.state.graph (d := d) L γ δ (C1/4) C1 (by linarith only [hC1pos])
      hC1pos w p.admissible p.scales
    have e : C1/4/C1 = 1/4 := by field_simp
    rw [e] at this
    exact this
  have hmain : ∀ (hE : 2*(p.state.graph.atoms.card : ℤ)-2 ≤ p.state.graph.bonds.card),
      p.value γ δ C1 ≤ (ENNReal.ofReal (Real.log L^8))^n*(ENNReal.ofReal (L^(-η/2)))^kf*
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))^kg := by
    intro hE
    have hbf := branch_factor_le_one_dense p.state.graph hne hconn hE
    have h2 : ENNReal.ofReal ((2 : ℝ)^p.state.graph.bonds.card) =
        (2 : ℝ≥0∞)^p.state.graph.bonds.card := by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp
    have e4 : ENNReal.ofReal ((1/4 : ℝ)^p.state.graph.circuitRank*(2 : ℝ)^p.state.graph.bonds.card) =
        ENNReal.ofReal ((1/4 : ℝ)^p.state.graph.circuitRank)*(2 : ℝ≥0∞)^p.state.graph.bonds.card := by
      rw [ENNReal.ofReal_mul (by positivity),h2]
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
      _ ≤ 1*((ENNReal.ofReal (Real.log L^8))^n*(ENNReal.ofReal (L^(-η/2)))^kf*
              (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))^kg) := by
          gcongr
          exact ENNReal.ofReal_le_one.mpr hbf
      _ = _ := one_mul _
  have hbud' := hbud
  have hLL : L ≥ L₁ := hL₁'
  constructor
  · intro hE1
    obtain ⟨_,hν,_⟩ := odd_initial_statistics p.state.graph p.molecule hconn hE1
    have hnn := balancedPotential_nonneg_initial p.state.graph p.molecule (by omega)
    have hbudget : 2*n ≤ 48000*(kf+kg) := by
      rw [hSl,hPot] at hres
      have : 2*(n : ℤ) ≤ 48000*((kf : ℤ)+kg) := by omega
      exact_mod_cast this
    have hkg : 1 ≤ kg := by
      by_contra h0
      have h00 : kg = 0 := by omega
      have h1 := hdef h00
      rw [hDp] at h1
      have h2 := defectPotential_pos_of_nu_neg p.state.graph (by omega)
      omega
    have h := (hbud L hLL n kf kg hbudget).1
    rw [if_pos hkg] at h
    exact (hmain (by omega)).trans h
  · intro hE2 hpos
    obtain ⟨_,hν,_⟩ := even_initial_statistics p.state.graph p.molecule hconn hE2
    have hnn := balancedPotential_nonneg_initial p.state.graph p.molecule (by omega)
    have hbudget : 2*n ≤ 48000*(kf+kg) := by
      rw [hSl,hPot] at hres
      have : 2*(n : ℤ) ≤ 48000*((kf : ℤ)+kg) := by omega
      exact_mod_cast this
    have hbonds : forestHasBonds F := by
      refine ⟨p.state,?_,Finset.card_pos.mp hpos⟩
      exact List.mem_map.mpr ⟨p,by rw [hFp]; exact List.mem_singleton_self p,rfl⟩
    have h1 := hprog hbonds
    have hk : 1 ≤ kf+kg := by omega
    exact (hmain (by omega)).trans ((hbud' L hLL n kf kg hbudget).2 hk)

end WaveTurbulence.Mole.AppbAlgorithm
