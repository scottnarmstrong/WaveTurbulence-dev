/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase2E
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase3c
/-! **Ghost assembly, Phase 2 (F): the node lemma with the bank** (design: `CHAIN-DESIGN.md`).

`node2_bank`: for a triangle node `n` of a class `A` with bank `≤ b` and a split index `σ`, the split class
`B = splitCls … (cls2 h A n) σ` satisfies the phase invariant at the post state, the dart count drops, and for some
`ν ≤ b`, `k`: the bank of the child is `≤ b + k - ν` and `QS h B ≤ 9·25^d·ghostConstLow·stepRHS·L^{5η(ν - k)} · QS h' B`
(`k` cones of the class, `UStep2.excess_cone_at`; or `k = 0` and `ν = 1` iff some `α`-ghost pair of the node is an NC
edge, `UStep2.excess_low_at`). The invariant part follows main's `node2_facts` (`FinalCount/AsmPhase2b.lean`, sha256 in
`COPIED-SHA256SUMS`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The split class `σ` of a node. -/
noncomputable def nodeSplit [Infinite V] (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ)))
    {n : T2 h} (hn : Node2 L γ η h n) (σ : Sig) : Set (D₀ → (Fin d → ℤ)) :=
  splitCls L γ η w h (triOf hn) (Q2 n) (kp2 n) (triOf_cl hn) (cls2 L γ η w h A n) σ

/-- **The node lemma with the bank.** -/
theorem node2_bank [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop}
    {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))}
    (H : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hRA : ∀ κ h, Rch κ h → Relation.ReflTransGen (GammaLow.FinalCount.H.HAny L γ η w κ) (HSt.init M₀) h)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {h : HSt V D₀} (hA : Inv3 M₀ Rn Rch L w A0 A h) {n : T2 h} (hn : Node2 L γ η h n)
    (hext : ∀ k ∈ cls2 L γ η w h A n, Rch k h → Rch k (post2 L γ η h n)) {b : ℕ}
    (hbank : bank L γ η w h A ≤ b) (σ : Sig) :
    Inv3 M₀ Rn Rch L w A0 (nodeSplit L γ η w h A hn σ) (post2 L γ η h n) ∧
    Fintype.card (post2 L γ η h n).s.D < Fintype.card h.s.D ∧
    ∃ ν k : ℕ, ν ≤ b ∧ bank L γ η w (post2 L γ η h n) (nodeSplit L γ η w h A hn σ) + ν ≤ b + k ∧
      QS L γ δ C₁ w P h (nodeSplit L γ η w h A hn σ) ≤
        ENNReal.ofReal (9 * 25 ^ d * ghostConstLow d c η δ * stepRHS L γ η h (post2 L γ η h n) *
          L ^ (5 * η * ((ν : ℝ) - k))) * QS L γ δ C₁ w P (post2 L γ η h n) (nodeSplit L γ η w h A hn σ) := by
  set T := triOf hn with hT
  set hcl := triOf_cl hn
  set B := nodeSplit L γ η w h A hn σ with hB
  have hsub2 : B ⊆ cls2 L γ η w h A n := fun k hk => hk.1
  have hsub : B ⊆ A := fun k hk => (hsub2 hk).1
  have hlt := card_dart_post2 hn
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hQpos : ∀ j, 0 < Q2 n j := fun j => zpow_pos (by norm_num) _
  have hpost : post2 L γ η h n = h.triPost T (Q2 n) (kp2 n) hcl := post2_eq hn
  by_cases hBe : B = ∅
  · refine ⟨⟨hsub.trans hA.1, Or.inl hBe⟩, hlt, 0, 0, Nat.zero_le _, ?_, ?_⟩
    · rw [hBe, bank_empty]; omega
    · rw [hBe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨hc, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hBe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hBe
  have hcc := uctx_mono hc (fun k (hk : k ∈ B) => hsub hk)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ B) => hA.1 (hsub hk))
  have hst : UStep2 L γ η w (fun k => k ∈ B) h (post2 L γ η h n) :=
    Ghost.UStep2.mono (fun k hk => hsub2 hk) (uStep2_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn)
  have hc' : UCtx M₀ Rn (fun k => k ∈ B) L w (post2 L γ η h n) := UCtx.step2 hκ hst hpp hcc
  have hap' : ApPos (post2 L γ η h n).s := by
    rw [hpost]; exact apPos_triSt hap _ _ _ hQpos _
  have hr' : ∀ k ∈ B, Rch k (post2 L γ η h n) := fun k hk => hext k (hsub2 hk) (hr k (hsub hk))
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨hc', hap', hr'⟩⟩, hlt, ?_⟩
  have hI : Inv Rn h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hcard : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c := by
    have := UCtx.card_atoms_le hS hcc
    exact le_trans (by exact_mod_cast this) hnc
  have hIE := GammaLow.FinalCount.H.invE_of_reach hS (h0 κ (hA.1 (hsub hκ))) (hRA κ h (hr κ (hsub hκ)))
  have hCB : CompBeta h.s := hIE.comp
  have hBal : BalS h.s := hIE.bal
  have hRI : ∀ k0, k0 ∈ B → HInv L γ η w k0 h ∧ HGap L w k0 h := fun k0 hk0 => by
    have := GammaLow.FinalCount.H.runInv_of_reach hS (h0 k0 (hA.1 (hsub hk0))) (hRA k0 h (hr k0 (hsub hk0)))
    exact ⟨this.hrec, this.gap⟩
  have hG2 : ∀ k0 ∈ cls2 L γ η w h A n, HGap L w k0 h ∧ HInv L γ η w k0 h := fun k0 hk0 => by
    have := GammaLow.FinalCount.H.runInv_of_reach hS (h0 k0 (hA.1 hk0.1)) (hRA k0 h (hr k0 hk0.1))
    exact ⟨this.gap, this.hrec⟩
  have hS2 : S2Args L γ η w (fun k => k ∈ B) h T (Q2 n) (kp2 n) hcl :=
    Ghost.S2Args.mono (fun k hk => hsub2 hk) (s2args_node (w := w) (A := A) hn)
  have hstep := stepRHS_tri' (γ := γ) (η := η) hL hap T (Q2 n) (kp2 n) hcl
  have hX : 0 ≤ stepRHS L γ η h (post2 L γ η h n) := by
    unfold stepRHS
    have h1 := apProd_pos (L := L) (γ := γ) (η := η) hL hap
    have h2 := apProd_pos (L := L) (γ := γ) (η := η) hL hap'
    positivity
  have hK0 : 0 ≤ ghostConstLow d c η δ := ghostConstLow_nonneg (d := d) (c := c) H.hη H.hδ0
  have h9 : (1 : ℝ) ≤ 9 * 25 ^ d := by have : (1 : ℝ) ≤ 25 ^ d := one_le_pow₀ (by norm_num); linarith
  have hsurv := triSurvMap h T (Q2 n) (kp2 n) hcl
  -- the bank of the child, with a given set of old vertices
  have hbk : ∀ Sold : Finset V, (∀ x, IsCritA L γ η h x → x ∈ (h.triPost T (Q2 n) (kp2 n) hcl).s.M.atoms → x ∈ Sold) →
      bank L γ η w (post2 L γ η h n) B ≤ matchNum (NCEdge L γ η w h A) Sold + (covOf T σ).card := by
    intro Sold hSold
    rw [hpost]
    refine bank_step hsurv hsub Sold (covOf T σ) ?_ ?_
    · intro x y hE hx hy
      exact Or.inl ⟨hSold x (hsurv.critA hx hE.2.1) hx.1, hSold y (hsurv.critA hy hE.2.2.1) hy.1⟩
    · exact edge_cover h T (Q2 n) (kp2 n) hcl (B0 := cls2 L γ η w h A n) subset_rfl
  have hcov := card_covOf_le T σ
  by_cases hk : 1 ≤ kOf σ
  · -- a cone class
    have hcone := creationCone_of_split (δ := δ) h T (Q2 n) (kp2 n) hcl (by have := H.hd; omega) hBal
      (B0 := cls2 L γ η w h A n) subset_rfl ⟨κ, hκ⟩ hRI hk
    have hdev := UStep2.excess_cone_at H hS2 hLC hc.good.2 hCB hcc.atom P hP0 hP hcard ⟨κ, hκ⟩ hRI (kOf σ) hcone
    refine ⟨0, kOf σ, Nat.zero_le _, ?_, ?_⟩
    · have h1 := hbk (critSet L γ η h) (fun x hx _ => mem_critSet.2 hx)
      have h2 : matchNum (NCEdge L γ η w h A) (critSet L γ η h) = bank L γ η w h A := rfl
      omega
    · rw [hpost] at hX ⊢
      refine hdev.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) le_rfl)
      have e : L ^ (5 * η * (((0 : ℕ) : ℝ) - (kOf σ : ℝ))) = L ^ (-5 * η * (kOf σ : ℝ)) := by
        congr 1; push_cast; ring
      rw [hstep, e]; ring
  · -- no cone: `ν` from the ghost pairs
    have hk0 : (covOf T σ).card = 0 := by omega
    have hkO : kOf σ = 0 := by omega
    by_cases hok : GhostPairsOK L γ η w (fun k => k ∈ B) h T
    · have hdev := UStep2.excess_low_at H hS2 hLC hc.good.2 hCB hcc.atom P hP0 hP hcard ⟨κ, hκ⟩ hRI 0 (Or.inl rfl)
        (fun _ => hok)
      refine ⟨0, 0, Nat.zero_le _, ?_, ?_⟩
      · have h1 := hbk (critSet L γ η h) (fun x hx _ => mem_critSet.2 hx)
        have h2 : matchNum (NCEdge L γ η w h A) (critSet L γ η h) = bank L γ η w h A := rfl
        omega
      · rw [hpost] at hX ⊢
        refine hdev.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
        rw [hstep] at hX
        simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one, sub_zero]
        rw [hstep]
        nlinarith [mul_nonneg hK0 hX]
    · obtain ⟨j₁, j₂, hE, hne₁, hne₂⟩ := edge_of_not_ghostPairsOK hn hI hsub2 hG2 ⟨κ, hκ⟩ hok
      have hdev := UStep2.excess_low_at H hS2 hLC hc.good.2 hCB hcc.atom P hP0 hP hcard ⟨κ, hκ⟩ hRI 1 (Or.inr rfl)
        (fun h1 => absurd h1 (by decide))
      have hxc : T.t j₁ ∈ critSet L γ η h := mem_critSet.2 hE.2.1
      have hyc : T.t j₂ ∈ critSet L γ η h := mem_critSet.2 hE.2.2.1
      have herase := matchNum_erase_edge hxc hyc hE.1 hE
      have hnotpost : ∀ j, T.t j ∉ (h.triPost T (Q2 n) (kp2 n) hcl).s.M.atoms := fun j hj =>
        (triPost_atoms h T (Q2 n) (kp2 n) hcl hj).2.1 j rfl
      have h1 := hbk (((critSet L γ η h).erase (T.t j₁)).erase (T.t j₂)) (fun z hz hzp => by
        refine mem_erase.2 ⟨fun e => hnotpost j₂ (by subst e; exact hzp),
          mem_erase.2 ⟨fun e => hnotpost j₁ (by subst e; exact hzp), mem_critSet.2 hz⟩⟩)
      have h2 : matchNum (NCEdge L γ η w h A) (critSet L γ η h) = bank L γ η w h A := rfl
      refine ⟨1, 0, by omega, by omega, ?_⟩
      rw [hpost] at hX ⊢
      refine hdev.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      rw [hstep] at hX
      rw [hstep]
      simp only [Nat.cast_one, Nat.cast_zero, sub_zero, mul_one]
      have hp5 : 0 ≤ L ^ (5 * η) := Real.rpow_nonneg hL.le _
      nlinarith [mul_nonneg (mul_nonneg hK0 hX) hp5]

end WaveTurbulence.GammaLow.FinalCount.Ghost
