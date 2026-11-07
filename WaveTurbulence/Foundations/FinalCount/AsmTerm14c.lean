/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm14b
public import WaveTurbulence.Foundations.FinalCount.AsmRho2
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 14c: `term_exponent`** (instantiation of `term_arith`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The sum of the component exponents. -/
theorem sum_exa (γ η : ℝ) (hf : HSt V D₀) (Tm : V → Prop) (R : ℕ) (Rs : Finset V) (hR : CompRep (hf.op5 Tm).s.M Rs) :
    ∑ a ∈ Rs, exa γ η hf Tm R a =
      (gam0 γ + 2 * η ^ 2) * ((WaveTurbulence.FinalCountG8.betaAtoms (hf.op5 Tm).s.M.atoms (cl8 hf)).card : ℝ)
        - eraseA γ η * ((Rs.filter fun a => UntC hf Tm R a ∧ ¬ CompOdd hf a).card : ℝ)
        - η ^ 5 * ((hf.op5 Tm).s.M.rho : ℝ)
        + η * ∑ a ∈ Rs.filter (fun a => ¬ UntC hf Tm R a),
            (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) := by
  unfold exa
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hb : ∑ a ∈ Rs, ((WaveTurbulence.FinalCountG8.betaAtoms (compMol (hf.op5 Tm).s.M a).atoms (cl8 hf)).card : ℝ) =
      ((WaveTurbulence.FinalCountG8.betaAtoms (hf.op5 Tm).s.M.atoms (cl8 hf)).card : ℝ) := by
    rw [← Nat.cast_sum, sum_beta_comp hR]
  have hρ : ∑ a ∈ Rs, ((compMol (hf.op5 Tm).s.M a).rho : ℝ) = ((hf.op5 Tm).s.M.rho : ℝ) := by
    rw [← Nat.cast_sum, ← hR.rho_sum]
  rw [hb, hρ]
  have h1 : ∑ a ∈ Rs, (if UntC hf Tm R a ∧ ¬ CompOdd hf a then eraseA γ η else 0) =
      eraseA γ η * ((Rs.filter fun a => UntC hf Tm R a ∧ ¬ CompOdd hf a).card : ℝ) := by
    rw [← Finset.sum_filter]; simp [mul_comm]
  have h2 : ∑ a ∈ Rs, (if UntC hf Tm R a then (0 : ℝ) else
        η * (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ)) =
      η * ∑ a ∈ Rs.filter (fun a => ¬ UntC hf Tm R a),
        (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : UntC hf Tm R a <;> simp [h]
  rw [h1, h2]


theorem isoAtoms_eq (s : St.{u} V D₀) (E : Finset V) :
    isoAtoms s E = (eraseSet s.M E).atoms.filter fun a => ¬ keepM s.M E a := by
  unfold isoAtoms; rw [eraseSet_atoms]; rfl

/-- **The terminal exponent inequality** (`term_arith` at the data of a terminal state): the cluster exponents and the
component exponents add up to at most the exponent of the potential with `Y₀ = L^{aR + 4η(R-1) - (η⁵-4η⁶)/2}`, `crit = 0`. -/
theorem term_exponent {hf : HSt V D₀} {Tm : V → Prop} {R : ℕ} {γ η C₀ : ℝ} (hγ0 : 0 ≤ gam0 γ) (hη : 0 < η)
    (hη4 : η ≤ 1 / 4) (hC₀ : 1 ≤ C₀) {𝒦 : Finset (Finset V)} {j : Finset V → ℤ} {Rs : Finset V}
    (hg : Good R hf.s) (hcl : Clusters hf.s.M 𝒦) (h1 : 𝒦.biUnion id = tameSet hf Tm)
    (hrk : hf.s.M.circuitRank = (eraseSet hf.s.M (tameSet hf Tm)).circuitRank + ∑ K ∈ 𝒦, j K)
    (hR : CompRep (hf.op5 Tm).s.M Rs)
    (hdpos : ∀ a ∈ hf.s.M.atoms, 1 ≤ hf.s.M.deg a) (hM4 : ∀ a ∈ hf.s.M.atoms, hf.s.M.deg a ≤ 4)
    (hZ : ∑ a ∈ Rs.filter (fun a => ¬ UntC hf Tm R a),
        (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) ≤
        (eDart hf.s.M (tameSet hf Tm) : ℝ) + 4 * ((R : ℝ) - 1) + 3 * (𝒦.card : ℝ))
    (hρ1 : 1 ≤ hf.s.M.rho) :
    ∑ K ∈ 𝒦, exK γ η C₀ K.card (eDart hf.s.M K) (j K) + ∑ a ∈ Rs, exa γ η hf Tm R a ≤
      eraseA γ η * (R : ℝ) + 4 * η * ((R : ℝ) - 1) - (η ^ 5 - 4 * η ^ 6) / 2 - 4 * η ^ 6 * (hf.s.M.rho : ℝ)
        - eraseA γ η * (hf.s.M.numComponents : ℝ) + (gam0 γ + 2 * η ^ 2) * (vBeta hf.s : ℝ) := by
  set T := tameSet hf Tm with hT
  have hTsub : T ⊆ hf.s.M.atoms := fun v hv => (tameSet_mem.1 hv).1
  have hE : ∀ v ∈ T, v ∈ hf.s.M.atoms ∧ hf.s.cls v = .eps := fun v hv => by
    have := tameSet_mem.1 hv; exact ⟨this.1, this.2.1⟩
  obtain ⟨R5, hR5, hg5⟩ := Good.erase_set_iso hg hE
  have hg5' : Good R5 (hf.op5 Tm).s := hg5
  rw [sum_exK, sum_exa γ η hf Tm R Rs hR]
  have hsumc : (∑ K ∈ 𝒦, (K.card : ℝ)) = (T.card : ℝ) := by
    rw [← Nat.cast_sum, cluster_card_sum hcl, h1]
  have hsume : (∑ K ∈ 𝒦, (eDart hf.s.M K : ℝ)) = (eDart hf.s.M T : ℝ) := by
    rw [← Nat.cast_sum, ← eDart_biUnion hcl, h1]
  rw [hsumc, hsume]
  -- numbers
  have hiso : ((isoAtoms hf.s T).card : ℝ) ≤ (eDart hf.s.M T : ℝ) := by
    rw [isoAtoms_eq]; exact_mod_cast iso_le_eDart hf.s.M T (fun a ha => hdpos a (Finset.mem_sdiff.1 ha).1)
  have hF5 := op5_numComponents hf.s.M T hTsub
  have hF5' : ((hf.op5 Tm).s.M.numComponents : ℤ) = (Rs.card : ℤ) := by rw [hR.numComponents_eq]
  have htch := tch_eq hf.s.M T
  have hJ : hf.s.M.circuitRank - (eraseSet hf.s.M T).circuitRank = ∑ K ∈ 𝒦, j K := by rw [hrk]; ring
  rw [hJ, ← isoAtoms_eq] at hF5
  have hRc : (R5 : ℝ) * 2 + 4 * T.card + 2 * (isoAtoms hf.s T).card ≤ 2 * R + (2 * eDart hf.s.M T + intDart hf.s.M T) := by
    have := hR5; rw [htch] at this; push_cast at this; exact_mod_cast (by linarith)
  have hFr : (Rs.card : ℝ) = hf.s.M.numComponents - ∑ K ∈ 𝒦, (j K : ℝ) + eDart hf.s.M T + (intDart hf.s.M T : ℝ) / 2 -
      T.card - (isoAtoms hf.s T).card := by
    have e1 : (2 : ℤ) * (Rs.card : ℤ) = 2 * (hf.s.M.numComponents : ℤ) - 2 * ∑ K ∈ 𝒦, j K + (2 * eDart hf.s.M T + intDart hf.s.M T : ℕ)
        - 2 * (T.card : ℤ) - 2 * ((isoAtoms hf.s T).card : ℤ) := by
      rw [← hF5', ← htch]; exact hF5
    have e2 : (2 : ℝ) * (Rs.card : ℝ) = 2 * (hf.s.M.numComponents : ℝ) - 2 * ∑ K ∈ 𝒦, (j K : ℝ) +
        (2 * eDart hf.s.M T + intDart hf.s.M T : ℕ) - 2 * (T.card : ℝ) - 2 * ((isoAtoms hf.s T).card : ℝ) := by
      exact_mod_cast e1
    push_cast at e2
    linarith
  have hFim := Good.imperfect_card_le hg5' hR
  have hρle := rho_op5 hf.s.M hM4 T hTsub
  rw [← isoAtoms_eq] at hρle
  have hUE : ((Rs.card : ℝ)) - ((Rs.filter (fun a => ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧
      contrib (hf.op5 Tm).s b ≠ 0)).card : ℝ) ≤ ((Rs.filter fun a => UntC hf Tm R a ∧ ¬ CompOdd hf a).card : ℝ) := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := Rs) (fun a => ∃ b ∈ (hf.op5 Tm).s.M.atoms,
      (hf.op5 Tm).s.M.SameComponent a b ∧ contrib (hf.op5 Tm).s b ≠ 0)
    have hsub : Rs.filter (fun a => ¬ ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧
        contrib (hf.op5 Tm).s b ≠ 0) ⊆ Rs.filter fun a => UntC hf Tm R a ∧ ¬ CompOdd hf a := by
      intro a ha
      obtain ⟨haR, hna⟩ := Finset.mem_filter.1 ha
      push_neg at hna
      obtain ⟨hT', hnodd⟩ := perfect_unt hg (hR.mem a haR) hna
      exact Finset.mem_filter.2 ⟨haR, ⟨hT', fun h => absurd h hnodd⟩, hnodd⟩
    have := Finset.card_le_card hsub
    have h3 : ((Rs.card : ℕ) : ℝ) = (Rs.filter (fun a => ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧
      contrib (hf.op5 Tm).s b ≠ 0)).card + (Rs.filter (fun a => ¬ ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧
      contrib (hf.op5 Tm).s b ≠ 0)).card := by exact_mod_cast hsplit.symm
    have h4 : ((Rs.filter (fun a => ¬ ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧
        contrib (hf.op5 Tm).s b ≠ 0)).card : ℝ) ≤ ((Rs.filter fun a => UntC hf Tm R a ∧ ¬ CompOdd hf a).card : ℝ) := by
      exact_mod_cast this
    linarith
  have hβ : ((WaveTurbulence.FinalCountG8.betaAtoms (hf.op5 Tm).s.M.atoms (cl8 hf)).card : ℝ) ≤ (vBeta hf.s : ℝ) := by
    exact_mod_cast betaAtoms_le_vBeta (Tm := Tm) hg.2
  have hFimR : ((Rs.filter (fun a => ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧
      contrib (hf.op5 Tm).s b ≠ 0)).card : ℝ) ≤ (R5 : ℝ) := by exact_mod_cast hFim
  have hη2 : 0 ≤ η ^ 2 := by positivity
  have ha0 : 0 ≤ eraseA γ η := by unfold eraseA; linarith
  have hb0 : 0 ≤ gam0 γ + 2 * η ^ 2 := by linarith
  have hA := term_arith (eraseA γ η) (gam0 γ + 2 * η ^ 2) η C₀ (𝒦.card : ℝ) (T.card : ℝ) (eDart hf.s.M T : ℝ)
    (∑ K ∈ 𝒦, (j K : ℝ)) ((intDart hf.s.M T : ℝ) / 2) ((isoAtoms hf.s T).card : ℝ) (hf.s.M.numComponents : ℝ) (Rs.card : ℝ)
    ((Rs.filter (fun a => ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧
      contrib (hf.op5 Tm).s b ≠ 0)).card : ℝ) (R5 : ℝ) (R : ℝ) (hf.s.M.rho : ℝ) ((hf.op5 Tm).s.M.rho : ℝ)
    ((WaveTurbulence.FinalCountG8.betaAtoms (hf.op5 Tm).s.M.atoms (cl8 hf)).card : ℝ) (vBeta hf.s : ℝ)
    (∑ a ∈ Rs.filter (fun a => ¬ UntC hf Tm R a),
        (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ))
    ha0 hb0 hη hη4 hC₀ (Nat.cast_nonneg _) (by linarith) (by linarith) hFimR
    (by exact_mod_cast hρle) (Nat.cast_nonneg _) hiso (Nat.cast_nonneg _) (Nat.cast_nonneg _) hβ hZ (by exact_mod_cast hρ1)
  nlinarith [hA, hUE, mul_nonneg ha0 (sub_nonneg.2 hUE)]

end WaveTurbulence.FinalCountAsm
