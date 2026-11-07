/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.Step0Post
import Mathlib.Tactic

/-! # DH23 Proposition 10.4(2)′

**Statement.** Let `𝕄` be a 4-regular molecule (in/out caps, no loops, connected) with at most two triple bonds and no
bond of multiplicity `> 3`, without cut vertex, not Y-exceptional (repair R2), and with no complete (Y2)-route through a
small cell. Then for every bond `ℓ` the decorations split (`SplitBound`):
`𝔄(𝕄; ¬Q) ≤ K² (|𝕄| + 1) L^{−η/16}` and `𝔄(𝕄 ∖ ℓ; Q) ≤ K² (|𝕄| + 1) L^{−γ₀−η/16}`, with `K = 110 |scaleSet L|² (log L)^{12}`.

**Proof (DH23 L1963).** Step 0: at most two complete (Y) sequences, each ending in (Y1) case 3 (then Prop 10.2 gives
the first alternative, `branch_y1c3`) or in (Y2) (then the split transfers back, `split_transfer_Y2`, with the LG
parameter halved). The molecule reached has no triple bond; it is not `Q` or `T` (not Y-exceptional), so it is core,
and `core_split` applies.

**Inputs** (`Prop104TwoInputs`, at `η`, `η/2`, `η/4`): the seven operation inputs of `CoreInputs` and DH23 Prop 10.2
(both statements). G6's Props 10.1 and 10.3 are used as proved.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

/-- **The named inputs of Prop 10.4(2)′** at one LG parameter. -/
def Prop104TwoInputs (d : ℕ) (γ η : ℝ) : Prop :=
  BetaCutInput.{u, v} d γ η ∧ BridgeSplitInput.{u, v} d γ η ∧ BiBridgeInput.{u, v} d γ η ∧
    BiBridgeEqualInput.{u, v} d γ η ∧ PairGainInput.{u, v} d γ η ∧ SmallGapPairInput.{u, v} d γ η ∧
    MergeInput.{u, v} d γ η ∧ Prop102Input.{u, v} d γ η ∧ Prop102SecondInput.{u, v} d γ η

/-- Comparison of the bounds of the branches. -/
theorem branch_cmp {K L m n x y : ℝ} (hK : 1 ≤ K) (hL : 1 ≤ L) (hmn : m ≤ n) (hm : 0 ≤ m) (hxy : x ≤ y)
    {i j : ℕ} (hij : i ≤ j) : K ^ i * ((m + 1) * L ^ x) ≤ K ^ j * ((n + 1) * L ^ y) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  refine mul_le_mul (pow_le_pow_right₀ hK hij) (mul_le_mul (by linarith) (Real.rpow_le_rpow_of_exponent_le hL hxy)
    (Real.rpow_nonneg hLp.le _) (by linarith)) (by positivity) (by positivity)

/-- **DH23 Proposition 10.4(2)′.** -/
theorem prop104_two (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hη200 : η ≤ min γ (1 - γ) / 200) (hηd : d * η ≤ min γ (1 - γ) / 4) (hγ12 : 1 / 2 < γ)
    (hin0 : Prop104TwoInputs.{u, v} d γ η) (hin1 : Prop104TwoInputs.{u, v} d γ (η / 2))
    (hin2 : Prop104TwoInputs.{u, v} d γ (η / 4)) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
        (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
        (∀ a ∈ M.atoms, M.deg a = 4) → (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
        (∀ w ∈ M.atoms, ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ w → b ≠ w →
          (Degen.eraseAtoms M {w}).SameComponent a b) →
        (∀ p q r s t u, 3 ≤ M.bondsBetween p q → 3 ≤ M.bondsBetween r s → 3 ≤ M.bondsBetween t u →
          s(p, q) = s(r, s) ∨ s(p, q) = s(t, u) ∨ s(r, s) = s(t, u)) → (∀ p q, M.bondsBetween p q ≤ 3) →
        (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        ¬ IsYExceptional M → ¬ YReachesSmallCell M →
        ∀ e : D, SplitBound M e d L γ δ η C1
          ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
            ((M.atoms.card + 1) * L ^ (-(η / 16))))
          ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
            ((M.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16)))) := by
  have hg : 0 < min γ (1 - γ) := lt_min hγ.1 (by linarith [hγ.2])
  have hηmax : η ≤ min γ (1 - γ) / 2 := by linarith
  have hη2 : 0 < η / 2 := by linarith
  have hη2max : η / 2 ≤ min γ (1 - γ) / 2 := by linarith
  have hη4 : 0 < η / 2 / 2 := by positivity
  have hdη : (0 : ℝ) ≤ d * η := by positivity
  obtain ⟨a0, b0, c0, e0, f0, g0, h0, p0, s0⟩ := hin0
  obtain ⟨a1, b1, c1, e1, f1, g1, h1, p1, s1⟩ := hin1
  have hin2' : Prop104TwoInputs.{u, v} d γ (η / 2 / 2) := by rw [show η / 2 / 2 = η / 4 by ring]; exact hin2
  obtain ⟨a2, b2, c2, e2, f2, g2, h2, p2, s2⟩ := hin2'
  obtain ⟨Cc0, hCc0, hc0⟩ := core_split d hd γ hγ η hη hη200 hηd hγ12 a0 b0 c0 e0 f0 g0 h0 p0 s0
  obtain ⟨Cc1, hCc1, hc1⟩ := core_split d hd γ hγ (η / 2) hη2 (by linarith)
    (by rw [← mul_div_assoc]; linarith) hγ12 a1 b1 c1 e1 f1 g1 h1 p1 s1
  obtain ⟨Cc2, hCc2, hc2⟩ := core_split d hd γ hγ (η / 2 / 2) hη4 (by linarith)
    (by rw [← mul_div_assoc, ← mul_div_assoc]; linarith) hγ12 a2 b2 c2 e2 f2 g2 h2 p2 s2
  obtain ⟨Ct0, hCt0, ht0⟩ := split_transfer_Y2 d hd γ hγ η hη hηmax
  obtain ⟨Ct1, hCt1, ht1⟩ := split_transfer_Y2 d hd γ hγ (η / 2) hη2 hη2max
  obtain ⟨Cy0, hCy0, hy0⟩ := branch_y1c3 d hd γ hγ η hη hηmax p0 p1 s0
  obtain ⟨Cy1, hCy1, hy1⟩ := branch_y1c3 d hd γ hγ (η / 2) hη2 hη2max p1 p2 s1
  set Cs := max (max (max Cc0 Cc1) (max Cc2 Ct0)) (max (max Ct1 Cy0) Cy1) with hCs
  have k1 : Cc0 ≤ Cs := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have k2 : Cc1 ≤ Cs := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have k3 : Cc2 ≤ Cs := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have k4 : Ct0 ≤ Cs := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have k5 : Ct1 ≤ Cs := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have k6 : Cy0 ≤ Cs := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have k7 : Cy1 ≤ Cs := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨2 * Cs, by linarith, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R1, hR1⟩ := hc0 m C1 (by linarith) δ hδ
  obtain ⟨R2, hR2⟩ := hc1 m C1 (by linarith) δ hδ
  obtain ⟨R3, hR3⟩ := hc2 m C1 (by linarith) δ hδ
  obtain ⟨R4, hR4⟩ := ht0 C1 (by linarith) δ hδ
  obtain ⟨R5, hR5⟩ := ht1 C1 (by linarith) δ hδ
  obtain ⟨R6, hR6⟩ := hy0 m C1 (by linarith) δ hδ
  obtain ⟨R7, hR7⟩ := hy1 m C1 (by linarith) δ hδ
  refine ⟨max (max (max R1 R2) (max R3 R4)) (max (max R5 R6) (max R7 (Real.exp 1))), fun L hL => ?_⟩
  have l1 : R1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have l2 : R2 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have l3 : R3 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have l4 : R4 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have l5 : R5 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have l6 : R6 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have l7 : R7 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hK := one_le_ylem2Const (L := L) hlog
  have hK0 : (0 : ℝ) ≤ 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 := zero_le_one.trans hK
  intro V D _ _ _ M hcap hloop h4 hconn hcut htri hle3 hsz hexc hns e
  classical
  -- Step 0 at the second level (LG parameter `η/2`): at most one triple bond
  have L1 : ∀ {D' : Type v} [Fintype D'] [DecidableEq D'] (N : Molecule V D'),
      (∀ a ∈ N.atoms, N.outdeg a ≤ 2 ∧ N.indeg a ≤ 2) → (∀ z, N.atom z ≠ N.atom (N.mate z)) →
      (∀ a ∈ N.atoms, N.deg a = 4) → (∀ a ∈ N.atoms, ∀ b ∈ N.atoms, N.SameComponent a b) →
      (∀ w ∈ N.atoms, ∀ a ∈ N.atoms, ∀ b ∈ N.atoms, a ≠ w → b ≠ w →
        (Degen.eraseAtoms N {w}).SameComponent a b) → (∀ p q, N.bondsBetween p q ≤ 3) →
      (∀ p q r s, 3 ≤ N.bondsBetween p q → 3 ≤ N.bondsBetween r s → s(p, q) = s(r, s)) →
      (N.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m → ¬ YReachesQT N → ¬ YReachesSmallCell N → ∀ e₁ : D', SplitBound N e₁ d L γ δ (η / 2) C1
        ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 1 *
          ((N.atoms.card + 1) * L ^ (-(η / 16))))
        ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 1 *
          ((N.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16)))) := by
    intro D' _ _ N hcapN hloopN h4N hconnN hcutN hle3N honeN hszN hqtN hnsN e₁
    have hn0 : (0 : ℝ) ≤ N.atoms.card := Nat.cast_nonneg _
    by_cases hno : ∀ p q, N.bondsBetween p q ≤ 2
    · have hcore : IsCore N := ⟨hcapN, hloopN, h4N, hconnN, hno, fun hT =>
        hqtN (YReachesQT.done N (fun p q => by have := hno p q; omega) (Or.inr hT))⟩
      refine splitBound_mono (hR2 L l2 N hcore hszN e₁) ?_ ?_
      · calc ((N.atoms.card : ℝ) + 1) * L ^ (-(η / 2 / 4)) =
            _ ^ 0 * ((N.atoms.card + 1) * L ^ (-(η / 2 / 4))) := by ring
          _ ≤ _ := branch_cmp hK hL1 le_rfl hn0 (by linarith) (by norm_num)
      · calc ((N.atoms.card : ℝ) + 1) * L ^ (-(min γ (1 - γ) + η / 2 / 4)) =
            _ ^ 0 * ((N.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 2 / 4))) := by ring
          _ ≤ _ := branch_cmp hK hL1 le_rfl hn0 (by linarith) (by norm_num)
    push Not at hno
    obtain ⟨p, q, hpq⟩ := hno
    have h3 : N.bondsBetween p q = 3 := by have := hle3N p q; omega
    have hpq' : p ≠ q := by rintro rfl; rw [bondsBetween_self_eq_zero hloopN] at h3; omega
    have hq : q ∈ N.atoms := mem_atoms_of_bondsBetween_pos (a := p) (by omega)
    have hp : p ∈ N.atoms := mem_atoms_of_bondsBetween_pos (a := q) (by rw [Degen.bondsBetween_comm]; omega)
    obtain ⟨C, hCa, hCb, hcomp⟩ := exists_complete hcapN hloopN hp hq hpq' h3
    rcases C.complete_4reg h4N hcomp with hE | ⟨E, hcompE⟩
    · -- (Y1) case 3: the first alternative
      obtain ⟨E⟩ := hE
      refine splitBound_mono (splitBound_of_first N e₁ (ε₂ := (110 * ((scaleSet L).card : ℝ) ^ 2 *
        (Real.log L ^ 2) ^ 6) ^ 1 * ((N.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16))))
        fun P hP => hR7 L l7 N hcapN hloopN h4N hconnN hcutN
          (fun _ _ _ _ _ _ h1 h2 _ => Or.inl (honeN _ _ _ _ h1 h2)) hle3N hszN C E P hP) ?_ le_rfl
      calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 * L ^ (-(η / 2 / 3)) =
          _ ^ 1 * ((0 + 1) * L ^ (-(η / 2 / 3))) := by ring
        _ ≤ _ := branch_cmp hK hL1 hn0 le_rfl (by linarith) le_rfl
    · -- (Y2): the post molecule is core
      have hone : ∀ p' q', 3 ≤ N.bondsBetween p' q' → s(p', q') = s(C.a 0, C.b 0) := fun p' q' h => by
        rw [hCa, hCb]; exact honeN p' q' p q h (by omega)
      rcases E.post_noTriple hcapN hconnN h4N hle3N hone hcompE with hQ | hno2
      · exact absurd (YReachesQT.y2 N hcapN C E hcompE (YReachesQT.done _ (IsQ.bb_ne_three hQ) (Or.inl hQ))) hqtN
      have hpcore : IsCore (E.toTwoExit hcapN).post :=
        ⟨(E.toTwoExit hcapN).post_caps hcapN, (E.toTwoExit hcapN).post_loop hloopN, fun a ha => by
          rw [TwoExit.post_atoms] at ha
          rw [TwoExit.post_deg _ (mem_sdiff.mp ha).2]; exact h4N a (mem_sdiff.mp ha).1,
          (E.toTwoExit hcapN).post_connected hconnN, hno2, fun hT => hqtN (YReachesQT.y2 N hcapN C E hcompE
            (YReachesQT.done _ (fun p' q' => by have := hno2 p' q'; omega) (Or.inr hT)))⟩
      have hgood := E.good_of_not_small hcapN hconnN hcompE hnsN
      have hcard : ((E.toTwoExit hcapN).post.atoms.card : ℝ) ≤ N.atoms.card := by
        rw [TwoExit.post_atoms]; exact_mod_cast card_le_card sdiff_subset
      have hmain := hR5 L l5 N hcapN h4N hconnN C E hgood _ _ (fun e₂ => hR3 L l3 _ hpcore (hcard.trans hszN) e₂) e₁
      have hc0' : (0 : ℝ) ≤ (E.toTwoExit hcapN).post.atoms.card := Nat.cast_nonneg _
      refine splitBound_mono hmain ?_ ?_
      · calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 *
            (((E.toTwoExit hcapN).post.atoms.card + 1) * L ^ (-(η / 2 / 2 / 4))) =
            _ ^ 1 * (((E.toTwoExit hcapN).post.atoms.card + 1) * L ^ (-(η / 2 / 2 / 4))) := by ring
          _ ≤ _ := branch_cmp hK hL1 hcard hc0' (by linarith) le_rfl
      · calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 *
            (((E.toTwoExit hcapN).post.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 2 / 2 / 4))) =
            _ ^ 1 * (((E.toTwoExit hcapN).post.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 2 / 2 / 4))) := by ring
          _ ≤ _ := branch_cmp hK hL1 hcard hc0' (by linarith) le_rfl
  -- the first level
  have hn0 : (0 : ℝ) ≤ M.atoms.card := Nat.cast_nonneg _
  by_cases hno : ∀ p q, M.bondsBetween p q ≤ 2
  · have hcore : IsCore M := ⟨hcap, hloop, h4, hconn, hno, fun hT =>
      hexc (YReachesQT.done M (fun p q => by have := hno p q; omega) (Or.inr hT))⟩
    refine splitBound_mono (hR1 L l1 M hcore hsz e) ?_ ?_
    · calc ((M.atoms.card : ℝ) + 1) * L ^ (-(η / 4)) = _ ^ 0 * ((M.atoms.card + 1) * L ^ (-(η / 4))) := by ring
        _ ≤ _ := branch_cmp hK hL1 le_rfl hn0 (by linarith) (by norm_num)
    · calc ((M.atoms.card : ℝ) + 1) * L ^ (-(min γ (1 - γ) + η / 4)) =
          _ ^ 0 * ((M.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 4))) := by ring
        _ ≤ _ := branch_cmp hK hL1 le_rfl hn0 (by linarith) (by norm_num)
  push Not at hno
  obtain ⟨p, q, hpq⟩ := hno
  have h3 : M.bondsBetween p q = 3 := by have := hle3 p q; omega
  have hpq' : p ≠ q := by rintro rfl; rw [bondsBetween_self_eq_zero hloop] at h3; omega
  have hq : q ∈ M.atoms := mem_atoms_of_bondsBetween_pos (a := p) (by omega)
  have hp : p ∈ M.atoms := mem_atoms_of_bondsBetween_pos (a := q) (by rw [Degen.bondsBetween_comm]; omega)
  obtain ⟨C, _, _, hcomp⟩ := exists_complete hcap hloop hp hq hpq' h3
  rcases C.complete_4reg h4 hcomp with hE | ⟨E, hcompE⟩
  · obtain ⟨E⟩ := hE
    refine splitBound_mono (splitBound_of_first M e (ε₂ := (110 * ((scaleSet L).card : ℝ) ^ 2 *
      (Real.log L ^ 2) ^ 6) ^ 2 * ((M.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16))))
      fun P hP => hR6 L l6 M hcap hloop h4 hconn hcut htri hle3 hsz C E P hP) ?_ le_rfl
    calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 * L ^ (-(η / 3)) =
        _ ^ 1 * ((0 + 1) * L ^ (-(η / 3))) := by ring
      _ ≤ _ := branch_cmp hK hL1 hn0 le_rfl (by linarith) (by norm_num)
  · rcases E.post_triples hcap hconn h4 hle3 htri hcompE with hQ | ⟨hle3', hone'⟩
    · exact absurd (YReachesQT.y2 M hcap C E hcompE (YReachesQT.done _ (IsQ.bb_ne_three hQ) (Or.inl hQ))) hexc
    have hcard : ((E.toTwoExit hcap).post.atoms.card : ℝ) ≤ M.atoms.card := by
      rw [TwoExit.post_atoms]; exact_mod_cast card_le_card sdiff_subset
    have hpost := L1 (E.toTwoExit hcap).post ((E.toTwoExit hcap).post_caps hcap) ((E.toTwoExit hcap).post_loop hloop)
      (fun a ha => by
        rw [TwoExit.post_atoms] at ha
        rw [TwoExit.post_deg _ (mem_sdiff.mp ha).2]; exact h4 a (mem_sdiff.mp ha).1)
      ((E.toTwoExit hcap).post_connected hconn) ((E.toTwoExit hcap).post_noCut hcut) hle3' hone' (hcard.trans hsz)
      (fun h => hexc (YReachesQT.y2 M hcap C E hcompE h)) (fun h => hns (YReachesSmallCell.y2 M hcap C E hcompE h))
    have hgood := E.good_of_not_small hcap hconn hcompE hns
    have hmain := hR4 L l4 M hcap h4 hconn C E hgood _ _ hpost e
    have hc0' : (0 : ℝ) ≤ (E.toTwoExit hcap).post.atoms.card := Nat.cast_nonneg _
    refine splitBound_mono hmain ?_ ?_
    · calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 *
          ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 1 *
            (((E.toTwoExit hcap).post.atoms.card + 1) * L ^ (-(η / 16)))) =
          _ ^ 2 * (((E.toTwoExit hcap).post.atoms.card + 1) * L ^ (-(η / 16))) := by ring
        _ ≤ _ := branch_cmp hK hL1 hcard hc0' le_rfl le_rfl
    · calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 *
          ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 1 *
            (((E.toTwoExit hcap).post.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16)))) =
          _ ^ 2 * (((E.toTwoExit hcap).post.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16))) := by ring
        _ ≤ _ := branch_cmp hK hL1 hcard hc0' le_rfl le_rfl

end WaveTurbulence.MoleProp4
