/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase2G
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.LowA
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain10
/-! **Ghost assembly, LOW chain (B): Phase 2 with the bank on the LOW invariant** (design: `CHAIN-DESIGN.md`).

`node2_bankL`, `phase2_bank_coverL`: `node2_bank`, `phase2_bank_cover` (`Phase2F`, `Phase2G`) with main's LOW invariant
`Inv3L` (`∃ R' ≤ Rn, UCtx M₀ R' …`), H's `Reach2L`, the run invariant `InvL` (`H.invL_reach2`: `HInv`, `HGap`, `CompBeta`,
`BalS`) and the LOW potential step `hW` (with `Good R'` and a nonempty class, as H's `phase2_coverL`; a child with an
empty class costs `0`). The proofs are those of `Phase2F`/`Phase2G` with these substitutions. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **The node lemma with the bank.** -/
theorem node2_bankL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop}
    {C : GammaLow.FinalCount.H.CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))}
    (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hRA : ∀ κ h, Rch κ h → GammaLow.FinalCount.H.Reach2L C Un Fst L γ η w κ h)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h) {n : T2 h} (hn : Node2 L γ η h n)
    (hext : ∀ k ∈ cls2 L γ η w h A n, Rch k h → Rch k (post2 L γ η h n)) {b : ℕ}
    (hbank : bank L γ η w h A ≤ b) (σ : Sig) :
    Inv3L M₀ Rn Rch L w A0 (nodeSplit L γ η w h A hn σ) (post2 L γ η h n) ∧
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
  rcases hA.2 with he | ⟨⟨R', hR', hc⟩, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hBe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hBe
  have hcc := uctx_mono hc (fun k (hk : k ∈ B) => hsub hk)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ B) => hA.1 (hsub hk))
  have hst : UStep2 L γ η w (fun k => k ∈ B) h (post2 L γ η h n) :=
    Ghost.UStep2.mono (fun k hk => hsub2 hk) (uStep2_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn)
  have hc' : UCtx M₀ R' (fun k => k ∈ B) L w (post2 L γ η h n) := UCtx.step2 hκ hst hpp hcc
  have hap' : ApPos (post2 L γ η h n).s := by
    rw [hpost]; exact apPos_triSt hap _ _ _ hQpos _
  have hr' : ∀ k ∈ B, Rch k (post2 L γ η h n) := fun k hk => hext k (hsub2 hk) (hr k (hsub hk))
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨⟨R', hR', hc'⟩, hap', hr'⟩⟩, hlt, ?_⟩
  have hI : Inv R' h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hcard : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c := by
    have := card_atoms_leL_of_uctx hS hR' hcc
    exact le_trans (by exact_mod_cast this) hnc
  obtain ⟨_, -, hIE⟩ := GammaLow.FinalCount.H.invL_reach2 hS (h0 κ (hA.1 (hsub hκ))) (hRA κ h (hr κ (hsub hκ)))
  have hCB : CompBeta h.s := hIE.comp
  have hBal : BalS h.s := hIE.bal
  have hRI : ∀ k0, k0 ∈ B → HInv L γ η w k0 h ∧ HGap L w k0 h := fun k0 hk0 => by
    obtain ⟨_, -, this⟩ := GammaLow.FinalCount.H.invL_reach2 hS (h0 k0 (hA.1 (hsub hk0))) (hRA k0 h (hr k0 (hsub hk0)))
    exact ⟨this.hrec, this.gap⟩
  have hG2 : ∀ k0 ∈ cls2 L γ η w h A n, HGap L w k0 h ∧ HInv L γ η w k0 h := fun k0 hk0 => by
    obtain ⟨_, -, this⟩ := GammaLow.FinalCount.H.invL_reach2 hS (h0 k0 (hA.1 hk0.1)) (hRA k0 h (hr k0 hk0.1))
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

/-- **The Phase-2 cover with the bank.** -/
theorem phase2_bank_coverL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop}
    {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : H.CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    (HR : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hRA : ∀ κ h, Rch κ h → H.Reach2L C Un Fst L γ η w κ h)
    (hext : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (n : T2 h), Node2 L γ η h n →
      (∀ j : Fin 3, H.Desig C (h.anc (n.1 j)) (h.s.pr (n.2.1 j) (n.2.2.1 j))) → ∀ k ∈ cls2 L γ η w h A n, Rch k h →
        Rch k (post2 L γ η h n))
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h2 : 2 / L ≤ L ^ (-γ + η)) (N : ℕ)
    (hN : nodeBound2 (2 * M₀.atoms.card) (Fintype.card D₀) ⌈2 * Real.log L⌉₊ + 1 ≤ N) (W : HSt V D₀ → ℝ≥0∞)
    (hW : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀) (R' : ℕ), Inv3L M₀ Rn Rch L w A0 A h →
      ApPos h.s → Good R' h.s → (∃ k, k ∈ A) → UStep2 L γ η w (fun k => k ∈ A) h h' →
      ((splitK * N : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (9 * 25 ^ d * ghostConstLow d c η δ * stepRHS L γ η h h') * W h') ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv3L M₀ Rn Rch L w A0 A h →
      (∀ k ∈ A, H.NoEligibleTriangle C L γ η w k h) → (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (b : ℕ), Inv3L M₀ Rn Rch L w A0 A h →
      bank L γ η w h A ≤ b → QS L γ δ C₁ w P h A ≤ W h * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
  have hηγ : η ≤ γ := by have := HR.hη; have := HR.hη1; linarith
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) HR.hL
  have hL : 0 < L := by linarith
  have hη0 : 0 ≤ η := HR.hη.le
  have hN1 : 1 ≤ N := by omega
  have hK1 : 1 ≤ splitK := by unfold splitK; omega
  have hge1 : ∀ b : ℕ, (1 : ℝ≥0∞) ≤ ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := fun b => by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow hL1 (by positivity))
  suffices key : ∀ (hb : HSt V D₀ × ℕ) (A : Set (D₀ → (Fin d → ℤ))),
      (Inv3L M₀ Rn Rch L w A0 A hb.1 ∧ bank L γ η w hb.1 A ≤ hb.2) →
        QS L γ δ C₁ w P hb.1 A ≤ W hb.1 * ENNReal.ofReal (L ^ (5 * η * (hb.2 : ℝ))) by
    intro h A b hA hb
    exact key (h, b) A ⟨hA, hb⟩
  refine cover_induction_split (ι := ℕ × Sig) (fun a b : HSt V D₀ × ℕ => Fintype.card a.1.s.D < Fintype.card b.1.s.D)
    (InvImage.wf (fun hb : HSt V D₀ × ℕ => Fintype.card hb.1.s.D) wellFounded_lt)
    (fun hb A => Inv3L M₀ Rn Rch L w A0 A hb.1 ∧ bank L γ η w hb.1 A ≤ hb.2)
    (fun hb A => ∀ k ∈ A, H.NoEligibleTriangle C L γ η w k hb.1)
    (fun hb A => QS L γ δ C₁ w P hb.1 A) (fun hb => W hb.1 * ENNReal.ofReal (L ^ (5 * η * (hb.2 : ℝ)))) N splitK
    hN1 hK1 (fun hb A B hAB => QS_mono L γ δ C₁ w P hb.1 hAB) (fun hb A B => QS_union L γ δ C₁ w P hb.1 A B)
    (fun hb => QS_empty L γ δ C₁ w P hb.1) ?_ ?_
  · rintro ⟨h, b⟩ A ⟨hA, -⟩ hf
    calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h := hfin A h hA hf
      _ = W h * 1 := (mul_one _).symm
      _ ≤ W h * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by gcongr; exact hge1 b
  rintro ⟨h, b⟩ A ⟨hA, hbank⟩ _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ H.NoEligibleTriangle C L γ η w k h}
  have hAfin : Inv3L M₀ Rn Rch L w A0 Afin h := hA.mono fun k hk => hk.1
  have hbfin : bank L γ η w h Afin ≤ b := (bank_mono fun k hk => hk.1).trans hbank
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => (h, b), fun _ => 0, ⟨hAfin, hbfin⟩, fun k hk => hk.2, ?_,
      (by simpa using Nat.le_mul_of_pos_right splitK (by omega : 0 < N)), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  obtain ⟨R', hR', hc⟩ := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hcardA : h.s.M.atoms.card ≤ 2 * M₀.atoms.card := card_atoms_leL_of_uctx hS hR' hc
  have hcardD : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
  have hcard : (H.nodes2D C L γ η h).card ≤ nodeBound2 (2 * M₀.atoms.card) (Fintype.card D₀) ⌈2 * Real.log L⌉₊ := by
    refine (Finset.card_filter_le _ _).trans ((nodes2_card L γ η h).trans ?_)
    unfold nodeBound2
    gcongr
  have hmem : ∀ j t, H.nodeAt2 C L γ η h j = some t → t ∈ H.nodes2D C L γ η h := by
    intro j t ht
    unfold H.nodeAt2 at ht
    split_ifs at ht with hj
    · cases ht; exact ((H.nodes2D C L γ η h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ H.nodes2D C L γ η h, ∃ j, H.nodeAt2 C L γ η h j = some t := by
    intro t ht
    refine ⟨((H.nodes2D C L γ η h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold H.nodeAt2
    rw [dite_eq_left ((H.nodes2D C L γ η h).equivFin ⟨t, ht⟩).2]
    simp
  have hnode : ∀ t ∈ H.nodes2D C L γ η h, Node2 L γ η h t ∧
      ∀ j : Fin 3, H.Desig C (h.anc (t.1 j)) (h.s.pr (t.2.1 j) (t.2.2.1 j)) := fun t ht =>
    ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).2, (Finset.mem_filter.1 ht).2⟩
  let S : Finset (ℕ × Sig) := (Finset.range (H.nodes2D C L γ η h).card) ×ˢ Finset.univ
  let post : ℕ × Sig → HSt V D₀ × ℕ := fun js =>
    (H.postAt2 C L γ η h js.1, bank L γ η w (H.postAt2 C L γ η h js.1) (clsAtS C L γ η w h A js.1 js.2))
  let cost : ℕ × Sig → ℝ≥0∞ := fun js =>
    if clsAtS C L γ η w h A js.1 js.2 = ∅ then 0 else
    ENNReal.ofReal (9 * 25 ^ d * ghostConstLow d c η δ * stepRHS L γ η h (H.postAt2 C L γ η h js.1) *
      L ^ (5 * η * ((b : ℝ) - (post js).2)))
  refine ⟨Afin, S, fun js => clsAtS C L γ η w h A js.1 js.2, post, cost, ⟨hAfin, hbfin⟩, fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : H.NoEligibleTriangle C L γ η w k h
    · exact Or.inl ⟨hk, hnb⟩
    · right
      obtain ⟨t, htn, hdt, hkt⟩ := H.phase2_cover_memL hS h0 hRA HR.hL hηγ h2 hA hAe hk hnb
      have ht : t ∈ H.nodes2D C L γ η h :=
        Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨node2_mem_box HR.hL hηγ htn, htn⟩, hdt⟩
      obtain ⟨j, hj⟩ := hsurj t ht
      obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 (split_cover h (triOf htn) (Q2 t) (kp2 t) (triOf_cl htn) (w := w) (γ := γ)
        hL (cls2 L γ η w h A t) hkt)
      have hjS : (j, σ) ∈ S := by
        refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
        unfold H.nodeAt2 at hj
        by_contra hnot
        rw [dite_eq_right (by simpa using hnot)] at hj
        cases hj
      refine Set.mem_iUnion₂.2 ⟨(j, σ), hjS, ?_⟩
      show k ∈ clsAtS C L γ η w h A j σ
      unfold clsAtS
      rw [hj]; dsimp only
      rw [dite_eq_left htn]
      exact hσ
  · have hS' : S.card = (H.nodes2D C L γ η h).card * splitK := by
      simp only [S, Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      unfold splitK; ring
    rw [hS']
    have : (H.nodes2D C L γ η h).card + 1 ≤ N := by omega
    nlinarith
  · rintro ⟨j, σ⟩ hjS
    have hj : j < (H.nodes2D C L γ η h).card := Finset.mem_range.1 (Finset.mem_product.1 hjS).1
    obtain ⟨t, ht⟩ : ∃ t, H.nodeAt2 C L γ η h j = some t := ⟨_, by unfold H.nodeAt2; rw [dite_eq_left hj]⟩
    obtain ⟨hnd, hdes⟩ := hnode t (hmem j t ht)
    have hcls : clsAtS C L γ η w h A j σ = nodeSplit L γ η w h A hnd σ := by
      unfold clsAtS; rw [ht]; dsimp only; rw [dite_eq_left hnd]
    have hpost : H.postAt2 C L γ η h j = post2 L γ η h t := by unfold H.postAt2; rw [ht]
    obtain ⟨hinv, hlt, ν, k, hνb, hbk, hdev⟩ := node2_bankL HR hS hp0 hP hP0 c hnc hRA h0 hA hnd
      (hext A h t hnd hdes) hbank σ
    simp only [post, cost, hcls, hpost]
    by_cases hce : nodeSplit L γ η w h A hnd σ = ∅
    · rw [ite_eq_left hce]
      refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
      · rw [hce, QS_empty]; exact bot_le
      · simp
    obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hce
    rw [ite_eq_right hce]
    refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
    · refine hdev.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      have hX : 0 ≤ 9 * 25 ^ d * ghostConstLow d c η δ * stepRHS L γ η h (post2 L γ η h t) := by
        have h1 := ghostConstLow_nonneg (d := d) (c := c) HR.hη HR.hδ0
        have h2 : 0 ≤ stepRHS L γ η h (post2 L γ η h t) := by
          unfold stepRHS
          have := apProd_pos (L := L) (γ := γ) (η := η) hL hapP
          have hap' : ApPos (post2 L γ η h t).s := by
            rw [post2_eq hnd]; exact apPos_triSt hapP _ _ _ (fun j => zpow_pos (by norm_num) _) _
          have := apProd_pos (L := L) (γ := γ) (η := η) hL hap'
          positivity
        positivity
      refine mul_le_mul_of_nonneg_left (rpow_bank_le hL1 hη0 ?_) hX
      have : ((ν : ℕ) : ℝ) + (bank L γ η w (post2 L γ η h t) (nodeSplit L γ η w h A hnd σ) : ℝ) ≤ (b : ℝ) + k := by
        exact_mod_cast (by rw [Nat.add_comm]; exact hbk : ν + bank L γ η w (post2 L γ η h t) (nodeSplit L γ η w h A hnd σ) ≤ b + k)
      linarith
    · have hW' := hW (cls2 L γ η w h A t) h (post2 L γ η h t) R' (hA.mono fun k hk => hk.1) hapP hc.good
        ⟨κ, hκ.1⟩ (uStep2_node (A := A) hnd)
      set bb := bank L γ η w (post2 L γ η h t) (nodeSplit L γ η w h A hnd σ)
      have hsplit : ENNReal.ofReal (9 * 25 ^ d * ghostConstLow d c η δ * stepRHS L γ η h (post2 L γ η h t) *
            L ^ (5 * η * ((b : ℝ) - bb))) * (W (post2 L γ η h t) * ENNReal.ofReal (L ^ (5 * η * (bb : ℝ)))) =
          (ENNReal.ofReal (9 * 25 ^ d * ghostConstLow d c η δ * stepRHS L γ η h (post2 L γ η h t)) *
            W (post2 L γ η h t)) * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
        have hX0 : 0 ≤ 9 * 25 ^ d * ghostConstLow d c η δ * stepRHS L γ η h (post2 L γ η h t) := by
          have h1 := ghostConstLow_nonneg (d := d) (c := c) HR.hη HR.hδ0
          have h2 : 0 ≤ stepRHS L γ η h (post2 L γ η h t) := by
            unfold stepRHS
            have := apProd_pos (L := L) (γ := γ) (η := η) hL hapP
            have hap' : ApPos (post2 L γ η h t).s := by
              rw [post2_eq hnd]; exact apPos_triSt hapP _ _ _ (fun j => zpow_pos (by norm_num) _) _
            have := apProd_pos (L := L) (γ := γ) (η := η) hL hap'
            positivity
          positivity
        have e : L ^ (5 * η * ((b : ℝ) - bb)) * L ^ (5 * η * (bb : ℝ)) = L ^ (5 * η * (b : ℝ)) := by
          rw [← Real.rpow_add hL]; congr 1; ring
        rw [ENNReal.ofReal_mul hX0, ← e, ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)]
        ring
      rw [hsplit, ← mul_assoc]
      exact mul_le_mul' hW' le_rfl

end WaveTurbulence.GammaLow.FinalCount.Ghost
