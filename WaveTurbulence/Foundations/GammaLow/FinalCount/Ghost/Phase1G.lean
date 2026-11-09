/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase1F
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase2G
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1d
/-! **Ghost assembly, Phase 1 (G): the Phase-1 cover with the bank** (design: `CHAIN-DESIGN.md`).

`phase1_bank_cover`: H's `phase1_cover` (`H/FinalCount/AsmPhase1d.lean`) with the bank: for every class `A` of `Inv1`
and every `b ≥ bank h A`, `QS h A ≤ W h · L^{5ηb}`, given the potential steps
`(splitK·N)·(3·5^d·vCost)·W h' ≤ W h` (vine nodes), `(splitK·N)·(3·5^d·max cα cβ·stepRHS)·W h' ≤ W h` (triple cuts)
and the terminal bound with the bank (handed to `phase2_bank_cover`). A node is split by `σ ∈ Fin 3 × Fin 3`
(`node1_bank`, `nodeT_bank`); the child's bank is its actual bank; the cone gain `L^{-5ηk}` pays the bank increase. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The class of the child `(j, σ)` of a Phase-1 step (empty off the nodes). -/
noncomputable def clsAt1S [Infinite V] {M₀ : Molecule V D₀} (C : H.CollData M₀)
    (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀)) (crit : V → Prop)
    (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) (σ : Sig1) :
    Set (D₀ → (Fin d → ℤ)) :=
  match H.nodeAtP C crit L γ η h j with
  | some (Sum.inl t) => if hn : H.Node1 C crit L γ η h t then vineSplit Un Fst w A hn σ else ∅
  | some (Sum.inr t) => tripSplit (C := C) (L := L) (γ := γ) (η := η) Un w A t σ
  | none => ∅

/-- The base cost of the node `j` of a Phase-1 step. -/
noncomputable def baseAt1 [Infinite V] {M₀ : Molecule V D₀} (C : H.CollData M₀) (crit : V → Prop) (L γ η CA CN : ℝ)
    (c d' : ℕ) (h : HSt V D₀) (j : ℕ) : ℝ :=
  match H.nodeAtP C crit L γ η h j with
  | some (Sum.inl t) => 3 * 5 ^ d' * vCost L γ η CA CN h (H.post1 C crit L γ η h t)
  | some (Sum.inr t) => 3 * 5 ^ d' * max (cAlpha d' γ η) (cBeta η c) *
      stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)
  | none => 0

theorem ofReal_mul_mono_right {a X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) :
    ENNReal.ofReal (a * X) ≤ ENNReal.ofReal (a * Y) := by
  rcases le_or_gt 0 a with ha | ha
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hXY ha)
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg ha.le hX)]; exact zero_le

/-- The weight identity of a child: `(KN)·(ofReal(a·L^{5η(b-b')})·(W'·L^{5ηb'})) ≤ W` from `(KN)·(ofReal a·W') ≤ W`. -/
theorem child_weight {L η : ℝ} (hL : 0 < L) (KN : ℝ≥0∞) {a : ℝ} {W W' : ℝ≥0∞} (b b' : ℕ)
    (hW : KN * (ENNReal.ofReal a * W') ≤ W) :
    KN * (ENNReal.ofReal (a * L ^ (5 * η * ((b : ℝ) - b'))) * (W' * ENNReal.ofReal (L ^ (5 * η * (b' : ℝ))))) ≤
      W * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
  rcases le_or_gt 0 a with ha | ha
  · have e : L ^ (5 * η * ((b : ℝ) - b')) * L ^ (5 * η * (b' : ℝ)) = L ^ (5 * η * (b : ℝ)) := by
      rw [← Real.rpow_add hL]; congr 1; ring
    have : ENNReal.ofReal (a * L ^ (5 * η * ((b : ℝ) - b'))) * (W' * ENNReal.ofReal (L ^ (5 * η * (b' : ℝ)))) =
        (ENNReal.ofReal a * W') * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
      rw [ENNReal.ofReal_mul ha, ← e, ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)]
      ring
    rw [this, ← mul_assoc]
    exact mul_le_mul' hW le_rfl
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg ha.le (Real.rpow_nonneg hL.le _))]
    simp

/-- **The Phase-1 cover with the bank.** -/
theorem phase1_bank_cover [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 : Set (D₀ → (Fin d → ℤ))} {C : H.CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {crit : V → Prop} {CA CN ν : ℝ}
    (HR : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hExA : H.Ex1A L γ η δ C₁ w M₀ P CA) (hExN : H.Ex1N L γ η δ C₁ w M₀ P CN ν)
    (hExC : Ex1Cone L γ η δ C₁ w M₀ P CA)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (N : ℕ)
    (hN : (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) + 1 ≤ N)
    (W : HSt V D₀ → ℝ≥0∞)
    (hmem : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), H.Inv1 M₀ Rn C Un Fst L γ η w A0 A h → ∀ κ ∈ A,
      ¬ H.Stuck1 C L γ η w Un κ h →
      (∃ t ∈ H.nodes1 C crit L γ η h, κ ∈ cls1 L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) ∨
      (∃ t ∈ H.nodesT C L γ η h, κ ∈ cls3 L γ η w h (H.Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
          t.2.2.2.2.2.1 t.2.2.2.2.2.2))
    (hW1 : ∀ (h : HSt V D₀) (t : T1 h), ApPos h.s → Inv Rn h.s → H.Node1 C crit L γ η h t →
      ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (3 * 5 ^ d * vCost L γ η CA CN h (H.post1 C crit L γ η h t)) *
        W (H.post1 C crit L γ η h t)) ≤ W h)
    (hW3 : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀), H.Inv1 M₀ Rn C Un Fst L γ η w A0 A h → ApPos h.s →
      Inv Rn h.s → UStep3 L γ η w (fun k => k ∈ A) h h' →
      ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') *
        W h') ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (b : ℕ), H.Inv1 M₀ Rn C Un Fst L γ η w A0 A h →
      bank L γ η w h A ≤ b → (∀ k ∈ A, H.Stuck1 C L γ η w Un k h) →
      (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h * ENNReal.ofReal (L ^ (5 * η * (b : ℝ)))) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (b : ℕ), H.Inv1 M₀ Rn C Un Fst L γ η w A0 A h →
      bank L γ η w h A ≤ b → QS L γ δ C₁ w P h A ≤ W h * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) HR.hL
  have hL : 0 < L := by linarith
  have hη0 : 0 ≤ η := HR.hη.le
  have hN1 : 1 ≤ N := by omega
  have hK1 : 1 ≤ splitK := by unfold splitK; omega
  suffices key : ∀ (hb : HSt V D₀ × ℕ) (A : Set (D₀ → (Fin d → ℤ))),
      (H.Inv1 M₀ Rn C Un Fst L γ η w A0 A hb.1 ∧ bank L γ η w hb.1 A ≤ hb.2) →
        QS L γ δ C₁ w P hb.1 A ≤ W hb.1 * ENNReal.ofReal (L ^ (5 * η * (hb.2 : ℝ))) by
    intro h A b hA hb
    exact key (h, b) A ⟨hA, hb⟩
  refine cover_induction_split (ι := ℕ × Sig1) (fun a b : HSt V D₀ × ℕ => epsCount a.1.s < epsCount b.1.s)
    (InvImage.wf (fun hb : HSt V D₀ × ℕ => epsCount hb.1.s) wellFounded_lt)
    (fun hb A => H.Inv1 M₀ Rn C Un Fst L γ η w A0 A hb.1 ∧ bank L γ η w hb.1 A ≤ hb.2)
    (fun hb A => ∀ k ∈ A, H.Stuck1 C L γ η w Un k hb.1)
    (fun hb A => QS L γ δ C₁ w P hb.1 A) (fun hb => W hb.1 * ENNReal.ofReal (L ^ (5 * η * (hb.2 : ℝ)))) N splitK
    hN1 hK1 (fun hb A B hAB => QS_mono L γ δ C₁ w P hb.1 hAB) (fun hb A B => QS_union L γ δ C₁ w P hb.1 A B)
    (fun hb => QS_empty L γ δ C₁ w P hb.1) ?_ ?_
  · rintro ⟨h, b⟩ A ⟨hA, hbA⟩ hf
    exact hfin A h b hA hbA hf
  rintro ⟨h, b⟩ A ⟨hA, hbank⟩ _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ H.Stuck1 C L γ η w Un k h}
  have hAfin : H.Inv1 M₀ Rn C Un Fst L γ η w A0 Afin h := hA.mono fun k hk => hk.1
  have hbfin : bank L γ η w h Afin ≤ b := (bank_mono fun k hk => hk.1).trans hbank
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => (h, b), fun _ => 0, ⟨hAfin, hbfin⟩, fun k hk => hk.2, ?_,
      (by simpa using Nat.le_mul_of_pos_right splitK (by omega : 0 < N)), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  have hc := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hcardA : h.s.M.atoms.card ≤ 2 * M₀.atoms.card := UCtx.card_atoms_le hS hc
  have hcardD : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
  have hcard : (H.nodesAll C crit L γ η h).card ≤ (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        (Fintype.card D₀ * ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) := by
    unfold H.nodesAll
    rw [Finset.card_disjSum]
    refine add_le_add ((H.nodes1_card C crit L γ η h).trans ?_)
      ((H.nodesT_card_le C L γ η h).trans ((nodes3_card L γ η h).trans ?_))
    · gcongr
    · gcongr
  have hmemN : ∀ j t, H.nodeAtP C crit L γ η h j = some t → t ∈ H.nodesAll C crit L γ η h := by
    intro j t ht
    unfold H.nodeAtP at ht
    split_ifs at ht with hj
    · cases ht; exact ((H.nodesAll C crit L γ η h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ H.nodesAll C crit L γ η h, ∃ j, H.nodeAtP C crit L γ η h j = some t := by
    intro t ht
    refine ⟨((H.nodesAll C crit L γ η h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold H.nodeAtP
    rw [dite_eq_left ((H.nodesAll C crit L γ η h).equivFin ⟨t, ht⟩).2]
    simp
  have hjlt : ∀ j t, H.nodeAtP C crit L γ η h j = some t → j < (H.nodesAll C crit L γ η h).card := by
    intro j t hj
    unfold H.nodeAtP at hj
    by_contra hnot
    rw [dite_eq_right hnot] at hj
    cases hj
  let S : Finset (ℕ × Sig1) := (Finset.range (H.nodesAll C crit L γ η h).card) ×ˢ Finset.univ
  let post : ℕ × Sig1 → HSt V D₀ × ℕ := fun js =>
    (H.postAtP C crit L γ η h js.1,
      bank L γ η w (H.postAtP C crit L γ η h js.1) (clsAt1S C Un Fst crit L γ η w h A js.1 js.2))
  let cost : ℕ × Sig1 → ℝ≥0∞ := fun js =>
    ENNReal.ofReal (baseAt1 C crit L γ η CA CN c d h js.1 * L ^ (5 * η * ((b : ℝ) - (post js).2)))
  refine ⟨Afin, S, fun js => clsAt1S C Un Fst crit L γ η w h A js.1 js.2, post, cost, ⟨hAfin, hbfin⟩,
    fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : H.Stuck1 C L γ η w Un k h
    · exact Or.inl ⟨hk, hnb⟩
    · right
      rcases hmem A h hA k hk hnb with ⟨t, ht, hkt⟩ | ⟨t, ht, hkt⟩
      · have htm : Sum.inl t ∈ H.nodesAll C crit L γ η h := by unfold H.nodesAll; simpa using ht
        obtain ⟨j, hj⟩ := hsurj _ htm
        have hn : H.Node1 C crit L γ η h t := (Finset.mem_filter.1 ht).2
        obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 (split1_cover (h := h) (h' := h.vinePostL (vcut hn) (vR t) (vkp t))
          (X := vineSurv h (vcut hn) (vR t) (vkp t)) (w := w) (γ := γ) ![(vcut hn).fa, (vcut hn).fb]
          (fun k0 => pgap L w k0 (h.s.pr t.1 t.2.1)) hL _ hkt)
        refine Set.mem_iUnion₂.2 ⟨(j, σ), Finset.mem_product.2 ⟨Finset.mem_range.2 (hjlt j _ hj), Finset.mem_univ _⟩, ?_⟩
        show k ∈ clsAt1S C Un Fst crit L γ η w h A j σ
        unfold clsAt1S
        rw [hj]; dsimp only
        rw [dite_eq_left hn]
        exact hσ
      · have htm : Sum.inr t ∈ H.nodesAll C crit L γ η h := by unfold H.nodesAll; simpa using ht
        obtain ⟨j, hj⟩ := hsurj _ htm
        obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 (split1_cover (h := h) (h' := post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)
          (X := cutSurv h t.1 (fresh h) t.2.1 t.2.2.1 ((2 : ℝ) ^ t.2.2.2.1) (if t.2.2.2.2.1 then 50 else 0))
          (w := w) (γ := γ) ![t.1, fresh h] (fun k0 => pgap L w k0 (h.s.pr t.2.1 t.2.2.1)) hL _ hkt)
        refine Set.mem_iUnion₂.2 ⟨(j, σ), Finset.mem_product.2 ⟨Finset.mem_range.2 (hjlt j _ hj), Finset.mem_univ _⟩, ?_⟩
        show k ∈ clsAt1S C Un Fst crit L γ η w h A j σ
        unfold clsAt1S
        rw [hj]
        exact hσ
  · have hS' : S.card = (H.nodesAll C crit L γ η h).card * 9 := by
      simp only [S, Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    rw [hS']
    have : (H.nodesAll C crit L γ η h).card + 1 ≤ N := by omega
    unfold splitK
    nlinarith
  · rintro ⟨j, σ⟩ hjS
    have hj : j < (H.nodesAll C crit L γ η h).card := Finset.mem_range.1 (Finset.mem_product.1 hjS).1
    obtain ⟨t, ht⟩ : ∃ t, H.nodeAtP C crit L γ η h j = some t := ⟨_, by unfold H.nodeAtP; rw [dite_eq_left hj]⟩
    have htm := hmemN j t ht
    unfold H.nodesAll at htm
    rcases t with t | t
    · have hn : H.Node1 C crit L γ η h t := (Finset.mem_filter.1 (Finset.inl_mem_disjSum.1 htm)).2
      have hcls : clsAt1S C Un Fst crit L γ η w h A j σ = vineSplit Un Fst w A hn σ := by
        unfold clsAt1S; rw [ht]; dsimp only; rw [dite_eq_left hn]
      have hpost : H.postAtP C crit L γ η h j = H.post1 C crit L γ η h t := by unfold H.postAtP; rw [ht]
      have hbase : baseAt1 C crit L γ η CA CN c d h j = 3 * 5 ^ d * vCost L γ η CA CN h (H.post1 C crit L γ η h t) := by
        unfold baseAt1; rw [ht]
      obtain ⟨hinv, hlt, hbk, hdev⟩ := node1_bank HR hS hp0 hExA hExN hExC hν hSrc hdec h0 hA hn hbank σ
      simp only [post, cost, hcls, hpost, hbase]
      refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
      · refine hdev.trans (mul_le_mul' (ofReal_mul_mono_right (Real.rpow_nonneg hL.le _) ?_) le_rfl)
        refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
        have : (bank L γ η w (H.post1 C crit L γ η h t) (vineSplit Un Fst w A hn σ) : ℝ) ≤ (b : ℝ) + (k1Of σ : ℝ) := by
          exact_mod_cast hbk
        nlinarith
      · exact child_weight hL _ b _ (hW1 h t hapP hc.good.1 hn)
    · have hn' := Finset.inr_mem_disjSum.1 htm
      have hn : H.NodeT C L γ η h t := ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 hn').1).2, (Finset.mem_filter.1 hn').2⟩
      have hcls : clsAt1S C Un Fst crit L γ η w h A j σ = tripSplit (C := C) (L := L) (γ := γ) (η := η) Un w A t σ := by
        unfold clsAt1S; rw [ht]
      have hpost : H.postAtP C crit L γ η h j = post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 := by
        unfold H.postAtP; rw [ht]
      have hbase : baseAt1 C crit L γ η CA CN c d h j = 3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) *
          stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) := by
        unfold baseAt1; rw [ht]
      obtain ⟨hinv, hlt, hbk, hdev⟩ := nodeT_bank (Fst := Fst) HR hS hp0 hP hP0 c hnc h0 hA hn hbank σ
      simp only [post, cost, hcls, hpost, hbase]
      refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
      · refine hdev.trans (mul_le_mul' (ofReal_mul_mono_right (Real.rpow_nonneg hL.le _) ?_) le_rfl)
        refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
        have : (bank L γ η w (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)
            (tripSplit (C := C) (L := L) (γ := γ) (η := η) Un w A t σ) : ℝ) ≤ (b : ℝ) + (k1Of σ : ℝ) := by
          exact_mod_cast hbk
        nlinarith
      · have hAt : H.Inv1 M₀ Rn C Un Fst L γ η w A0 (H.Atrip C Un L γ η w h A) h := hA.mono H.Atrip_sub
        exact child_weight hL _ b _ (hW3 _ h _ (hAt.mono fun k hk => hk.1) hapP hc.good.1 (uStep3_node hn.1))

end WaveTurbulence.GammaLow.FinalCount.Ghost
