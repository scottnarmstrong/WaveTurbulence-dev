/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain32
/-! **FINALCOUNT LOW-CHAIN, session 6 (7): `term_exponentL`** (copy of `term_exponent` with the credit `k`, `R' = r + k`, and the `S`/`ε` form). -/
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

/-- A perfect component of the Operation-5 state lies over a tame-free, `LowFree`, even component of `hf`. -/
theorem perfect_untL {hf : HSt V D₀} {Tm : V → Prop} {R : ℕ} (hg : Good R hf.s) {a : V}
    (ha : a ∈ (hf.op5 Tm).s.M.atoms)
    (hper : ∀ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b → contrib (hf.op5 Tm).s b = 0) :
    TameFree hf Tm a ∧ LowFree hf a ∧ ¬ CompOdd hf a := by
  obtain ⟨hT, hno⟩ := perfect_unt hg ha hper
  refine ⟨hT, ?_, hno⟩
  intro e he hε
  have he' : e ∈ hf.s.M.atoms ∧ hf.s.M.SameComponent a e := by
    unfold compAtoms at he; exact Finset.mem_filter.1 he
  obtain ⟨he5, hsc5⟩ := op5_comp hT ha he'.2
  have h0 := hper e he5 hsc5
  unfold contrib at h0
  have hd := op5_deg_eq hT ha he'.2
  have hc : (hf.op5 Tm).s.cls e = .eps := hε
  rw [hc] at h0
  simp only [Cls.base] at h0
  omega


/-- **The terminal exponent inequality with loop credit**: `R'` is the `Good` index of the state, `R' = r + k`, the clusters carry the rank drops
`j K + kK K` with `Σ kK K = k`; the cluster and component exponents add up to at most the exponent of `Yz r`. -/
theorem term_exponentL {hf : HSt V D₀} {Tm : V → Prop} {R' r k : ℕ} {γ η C₀ : ℝ} (hγ0 : 0 ≤ gam0 γ) (hη : 0 < η)
    (hη4 : η ≤ 1 / 4) (hC₀ : 1 ≤ C₀) {𝒦 : Finset (Finset V)} {j : Finset V → ℤ} {kK : Finset V → ℕ} {Rs : Finset V}
    (hRk : r + k = R') (hkK : ∑ K ∈ 𝒦, kK K = k)
    (hg : Good R' hf.s) (hcl : Clusters hf.s.M 𝒦) (h1 : 𝒦.biUnion id = tameSet hf Tm)
    (hrk : hf.s.M.circuitRank = (eraseSet hf.s.M (tameSet hf Tm)).circuitRank + ∑ K ∈ 𝒦, j K)
    (hR : CompRep (hf.op5 Tm).s.M Rs)
    (hdpos : ∀ a ∈ hf.s.M.atoms, 1 ≤ hf.s.M.deg a) (hM4 : ∀ a ∈ hf.s.M.atoms, hf.s.M.deg a ≤ 4)
    (hZ : ∑ a ∈ Rs.filter (fun a => ¬ UntCL hf Tm r a),
        (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) ≤
        (eDart hf.s.M (tameSet hf Tm) : ℝ) + 4 * (((r - 1 : ℕ) : ℝ)) + 3 * (𝒦.card : ℝ))
    (hρ1 : 1 ≤ r → 1 ≤ hf.s.M.rho) :
    ∑ K ∈ 𝒦, exK γ η C₀ K.card (eDart hf.s.M K) (j K + (kK K : ℤ)) + ∑ a ∈ Rs, exaL γ η hf Tm r a ≤
      eraseA γ η * (r : ℝ) + 4 * η * (((r - 1 : ℕ) : ℝ)) - (if 1 ≤ r then (η ^ 5 - 4 * η ^ 6) / 2 else 0) -
        4 * η ^ 6 * (hf.s.M.rho : ℝ)
        - eraseA γ η * (hf.s.M.numComponents : ℝ) + (gam0 γ + 2 * η ^ 2) * (vBeta hf.s : ℝ) := by
  set T := tameSet hf Tm with hT
  have hTsub : T ⊆ hf.s.M.atoms := fun v hv => (tameSet_mem.1 hv).1
  have hE : ∀ v ∈ T, v ∈ hf.s.M.atoms ∧ hf.s.cls v = .eps := fun v hv => by
    have := tameSet_mem.1 hv; exact ⟨this.1, this.2.1⟩
  obtain ⟨R5, hR5, hg5⟩ := Good.erase_set_iso hg hE
  have hg5' : Good R5 (hf.op5 Tm).s := hg5
  rw [sum_exK 𝒦 γ η C₀ (fun K => K.card) (fun K => eDart hf.s.M K) (fun K => j K + (kK K : ℤ)), sum_exaL γ η hf Tm r Rs hR]
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
  have hRc : (R5 : ℝ) * 2 + 4 * T.card + 2 * (isoAtoms hf.s T).card ≤ 2 * R' + (2 * eDart hf.s.M T + intDart hf.s.M T) := by
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
      contrib (hf.op5 Tm).s b ≠ 0)).card : ℝ) ≤ ((Rs.filter fun a => UntCL hf Tm r a ∧ ¬ CompOdd hf a).card : ℝ) := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := Rs) (fun a => ∃ b ∈ (hf.op5 Tm).s.M.atoms,
      (hf.op5 Tm).s.M.SameComponent a b ∧ contrib (hf.op5 Tm).s b ≠ 0)
    have hsub : Rs.filter (fun a => ¬ ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧
        contrib (hf.op5 Tm).s b ≠ 0) ⊆ Rs.filter fun a => UntCL hf Tm r a ∧ ¬ CompOdd hf a := by
      intro a ha
      obtain ⟨haR, hna⟩ := Finset.mem_filter.1 ha
      push Not at hna
      obtain ⟨hT', hLF, hnodd⟩ := perfect_untL hg (hR.mem a haR) hna
      exact Finset.mem_filter.2 ⟨haR, ⟨hT', hLF, fun h => absurd h hnodd⟩, hnodd⟩
    have := Finset.card_le_card hsub
    have h3 : ((Rs.card : ℕ) : ℝ) = (Rs.filter (fun a => ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧
      contrib (hf.op5 Tm).s b ≠ 0)).card + (Rs.filter (fun a => ¬ ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧
      contrib (hf.op5 Tm).s b ≠ 0)).card := by exact_mod_cast hsplit.symm
    have h4 : ((Rs.filter (fun a => ¬ ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧
        contrib (hf.op5 Tm).s b ≠ 0)).card : ℝ) ≤ ((Rs.filter fun a => UntCL hf Tm r a ∧ ¬ CompOdd hf a).card : ℝ) := by
      exact_mod_cast this
    linarith
  have hβ : ((WaveTurbulence.FinalCountG8.betaAtoms (hf.op5 Tm).s.M.atoms (cl8 hf)).card : ℝ) ≤ (vBeta hf.s : ℝ) := by
    exact_mod_cast betaAtoms_le_vBeta (Tm := Tm) hg.2
  have hFimR : ((Rs.filter (fun a => ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧
      contrib (hf.op5 Tm).s b ≠ 0)).card : ℝ) ≤ (R5 : ℝ) := by exact_mod_cast hFim
  have hη2 : 0 ≤ η ^ 2 := by positivity
  have ha0 : 0 ≤ eraseA γ η := by unfold eraseA; linarith
  have hb0 : 0 ≤ gam0 γ + 2 * η ^ 2 := by linarith
  have hJc : ∑ K ∈ 𝒦, (((j K + (kK K : ℤ) : ℤ)) : ℝ) = ∑ K ∈ 𝒦, (j K : ℝ) + (k : ℝ) := by
    push_cast
    rw [Finset.sum_add_distrib, ← Nat.cast_sum, hkK]
  have hRkR : (R' : ℝ) = (r : ℝ) + k := by rw [← hRk]; push_cast; ring
  have hεr : (if 1 ≤ r then (η ^ 5 - 4 * η ^ 6) / 2 else 0) ≤ (η ^ 5 - 4 * η ^ 6) * (hf.s.M.rho : ℝ) := by
    have h5 : 0 ≤ η ^ 5 - 4 * η ^ 6 := by nlinarith [pow_pos hη 5, pow_pos hη 6]
    split_ifs with hr
    · have := hρ1 hr
      have h6 : (1 : ℝ) ≤ hf.s.M.rho := by exact_mod_cast this
      nlinarith
    · exact mul_nonneg h5 (Nat.cast_nonneg _)
  have hA := term_arithL (eraseA γ η) (gam0 γ + 2 * η ^ 2) η C₀ (𝒦.card : ℝ) (T.card : ℝ) (eDart hf.s.M T : ℝ)
    (∑ K ∈ 𝒦, (j K : ℝ) + (k : ℝ)) ((intDart hf.s.M T : ℝ) / 2 + (k : ℝ)) ((isoAtoms hf.s T).card : ℝ) (hf.s.M.numComponents : ℝ)
    (Rs.card : ℝ)
    ((Rs.filter (fun a => ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧
      contrib (hf.op5 Tm).s b ≠ 0)).card : ℝ) (R5 : ℝ) (r : ℝ) (((r - 1 : ℕ) : ℝ))
    (if 1 ≤ r then (η ^ 5 - 4 * η ^ 6) / 2 else 0) (hf.s.M.rho : ℝ) ((hf.op5 Tm).s.M.rho : ℝ)
    ((WaveTurbulence.FinalCountG8.betaAtoms (hf.op5 Tm).s.M.atoms (cl8 hf)).card : ℝ) (vBeta hf.s : ℝ)
    (∑ a ∈ Rs.filter (fun a => ¬ UntCL hf Tm r a),
        (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ))
    ha0 hb0 hη hη4 hC₀ (Nat.cast_nonneg _) (by linarith) (by linarith) hFimR
    (by exact_mod_cast hρle) (Nat.cast_nonneg _) hiso (Nat.cast_nonneg _) (Nat.cast_nonneg _) hβ (Nat.cast_nonneg _) hZ hεr
  rw [hJc]
  linarith [hA, hUE, mul_nonneg ha0 (sub_nonneg.2 hUE)]



end WaveTurbulence.FinalCountAsm
