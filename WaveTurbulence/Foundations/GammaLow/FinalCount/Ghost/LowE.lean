/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.LowD
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.LowC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.BankEngine2
/-! **Ghost assembly, LOW chain (E): the LOW Phase-1 cover with the bank** (design: `CHAIN-DESIGN.md`).

`phase1_bank_coverL`: H's `phase1_coverL` (`H/FinalCount/LowChain14.lean`) with the bank, on the weighted engine
`cover_induction_wt` (`K = splitK`): a vine or triple node is split into the `9` classes `σ` (`node1_bankL`,
`nodeT_bankL`), each child of weight `1` (budget `1/(splitK·N)`); a Step D1 node keeps its class (child `σ = (0,0)`,
weight `splitK`, budget `1/N`, `node1D_bankL`; the other `σ` are empty, weight `0`). A child with an empty class
costs `0`. -/
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

/-- The class of the child `(j, σ)` of a LOW Phase-1 step. -/
noncomputable def clsAt1SL [Infinite V] {M₀ : Molecule V D₀} (C : H.CollData M₀)
    (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀)) (crit : V → Prop)
    (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) (σ : Sig1) :
    Set (D₀ → (Fin d → ℤ)) :=
  match H.nodeAtPL C crit L γ η h j with
  | some (Sum.inl (Sum.inl t)) => if hn : H.Node1 C crit L γ η h t then vineSplit Un Fst w A hn σ else ∅
  | some (Sum.inl (Sum.inr t)) => tripSplit (C := C) (L := L) (γ := γ) (η := η) Un w A t σ
  | some (Sum.inr t) => if σ = (0, 0) then
      cls1D L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2 else ∅
  | none => ∅

/-- The base cost of the node `j` of a LOW Phase-1 step. -/
noncomputable def baseAt1L [Infinite V] {M₀ : Molecule V D₀} (C : H.CollData M₀) (crit : V → Prop)
    (L γ η CA CN CD : ℝ) (c d' : ℕ) (h : HSt V D₀) (j : ℕ) : ℝ :=
  match H.nodeAtPL C crit L γ η h j with
  | some (Sum.inl (Sum.inl t)) => 3 * 5 ^ d' * vCost L γ η CA CN h (H.post1 C crit L γ η h t)
  | some (Sum.inl (Sum.inr t)) => 3 * 5 ^ d' * max (cAlpha d' γ η) (cBeta η c) *
      stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)
  | some (Sum.inr _) => CD * excessRHS2 L γ η [] 1 2
  | none => 0

/-- The weight of the child `(j, σ)`. -/
noncomputable def wtAt1L [Infinite V] {M₀ : Molecule V D₀} (C : H.CollData M₀) (crit : V → Prop) (L γ η : ℝ)
    (h : HSt V D₀) (j : ℕ) (σ : Sig1) : ℕ :=
  match H.nodeAtPL C crit L γ η h j with
  | some (Sum.inr _) => if σ = (0, 0) then splitK else 0
  | _ => 1

theorem sum_wtAt1L_le [Infinite V] {M₀ : Molecule V D₀} (C : H.CollData M₀) (crit : V → Prop) (L γ η : ℝ)
    (h : HSt V D₀) (j : ℕ) : ∑ σ : Sig1, wtAt1L C crit L γ η h j σ ≤ splitK := by
  unfold wtAt1L
  cases hj : H.nodeAtPL C crit L γ η h j with
  | none => simp [splitK]
  | some t =>
    rcases t with (t | t) | t
    · simp [splitK]
    · simp [splitK]
    · simp

/-- **The LOW Phase-1 cover with the bank.** -/
theorem phase1_bank_coverL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : H.CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {crit : V → Prop}
    {CA CN CD ν : ℝ}
    (HR : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hExA : H.Ex1A L γ η δ C₁ w M₀ P CA) (hExN : H.Ex1N L γ η δ C₁ w M₀ P CN ν)
    (hExD : H.Ex1D L γ η δ C₁ w M₀ C P CD ν) (hExC : Ex1Cone L γ η δ C₁ w M₀ P CA)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (N : ℕ)
    (hN : (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) + 1 ≤ N)
    (W : HSt V D₀ → ℝ≥0∞)
    (hmem : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), H.Inv1L M₀ Rn C Un Fst L γ η w A0 A h → ∀ κ ∈ A,
      ¬ H.Stuck1 C L γ η w Un κ h →
      (∃ t ∈ H.nodes1 C crit L γ η h, κ ∈ cls1 L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) ∨
      (∃ t ∈ H.nodesT C L γ η h, κ ∈ cls3 L γ η w h (H.Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
          t.2.2.2.2.2.1 t.2.2.2.2.2.2) ∨
      (∃ t ∈ H.nodes1D C crit h, κ ∈ cls1D L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
          t.1 t.2.1 t.2.2.1 t.2.2.2))
    (hW1 : ∀ (h : HSt V D₀) (t : T1 h) (R' : ℕ), ApPos h.s → Good R' h.s → H.Node1 C crit L γ η h t →
      ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (3 * 5 ^ d * vCost L γ η CA CN h (H.post1 C crit L γ η h t)) *
        W (H.post1 C crit L γ η h t)) ≤ W h)
    (hW1D : ∀ (h : HSt V D₀) (t : T1D h) (R' : ℕ), ApPos h.s → Good R' h.s → H.Node1D C crit h t →
      (N : ℝ≥0∞) * (ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2) * W (H.post1D C crit h t)) ≤ W h)
    (hW3 : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀) (R' : ℕ), H.Inv1L M₀ Rn C Un Fst L γ η w A0 A h →
      ApPos h.s → Good R' h.s → (∃ k, k ∈ A) → UStep3 L γ η w (fun k => k ∈ A) h h' →
      ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') *
        W h') ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (b : ℕ), H.Inv1L M₀ Rn C Un Fst L γ η w A0 A h →
      bank L γ η w h A ≤ b → (∀ k ∈ A, H.Stuck1 C L γ η w Un k h) →
      (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h * ENNReal.ofReal (L ^ (5 * η * (b : ℝ)))) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (b : ℕ), H.Inv1L M₀ Rn C Un Fst L γ η w A0 A h →
      bank L γ η w h A ≤ b → QS L γ δ C₁ w P h A ≤ W h * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) HR.hL
  have hL : 0 < L := by linarith
  have hη0 : 0 ≤ η := HR.hη.le
  have hN1 : 1 ≤ N := by omega
  have hK1 : 1 ≤ splitK := by unfold splitK; omega
  suffices key : ∀ (hb : HSt V D₀ × ℕ) (A : Set (D₀ → (Fin d → ℤ))),
      (H.Inv1L M₀ Rn C Un Fst L γ η w A0 A hb.1 ∧ bank L γ η w hb.1 A ≤ hb.2) →
        QS L γ δ C₁ w P hb.1 A ≤ W hb.1 * ENNReal.ofReal (L ^ (5 * η * (hb.2 : ℝ))) by
    intro h A b hA hb
    exact key (h, b) A ⟨hA, hb⟩
  refine cover_induction_wt (ι := ℕ × Sig1) (fun a b : HSt V D₀ × ℕ => epsCount a.1.s < epsCount b.1.s)
    (InvImage.wf (fun hb : HSt V D₀ × ℕ => epsCount hb.1.s) wellFounded_lt)
    (fun hb A => H.Inv1L M₀ Rn C Un Fst L γ η w A0 A hb.1 ∧ bank L γ η w hb.1 A ≤ hb.2)
    (fun hb A => ∀ k ∈ A, H.Stuck1 C L γ η w Un k hb.1)
    (fun hb A => QS L γ δ C₁ w P hb.1 A) (fun hb => W hb.1 * ENNReal.ofReal (L ^ (5 * η * (hb.2 : ℝ)))) N splitK
    hN1 hK1 (fun hb A B hAB => QS_mono L γ δ C₁ w P hb.1 hAB) (fun hb A B => QS_union L γ δ C₁ w P hb.1 A B)
    (fun hb => QS_empty L γ δ C₁ w P hb.1) ?_ ?_
  · rintro ⟨h, b⟩ A ⟨hA, hbA⟩ hf
    exact hfin A h b hA hbA hf
  rintro ⟨h, b⟩ A ⟨hA, hbank⟩ _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ H.Stuck1 C L γ η w Un k h}
  have hAfin : H.Inv1L M₀ Rn C Un Fst L γ η w A0 Afin h := hA.mono fun k hk => hk.1
  have hbfin : bank L γ η w h Afin ≤ b := (bank_mono fun k hk => hk.1).trans hbank
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => (h, b), fun _ => 0, fun _ => 0, ⟨hAfin, hbfin⟩, fun k hk => hk.2, ?_,
      (by simpa using Nat.le_mul_of_pos_right splitK (by omega : 0 < N)), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  obtain ⟨R', hR', hc⟩ := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hcardA : h.s.M.atoms.card ≤ 2 * M₀.atoms.card := card_atoms_leL_of_uctx hS hR' hc
  have hcardD : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
  have hcard : (H.nodesAllL C crit L γ η h).card ≤ (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        (Fintype.card D₀ * ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) := by
    unfold H.nodesAllL
    rw [Finset.card_disjSum, Finset.card_disjSum]
    refine add_le_add (add_le_add ((H.nodes1_card C crit L γ η h).trans ?_)
      ((H.nodesT_card_le C L γ η h).trans ((nodes3_card L γ η h).trans ?_))) ((H.nodes1D_card C crit h).trans ?_)
    · gcongr
    · gcongr
    · gcongr
  have hmemN : ∀ j t, H.nodeAtPL C crit L γ η h j = some t → t ∈ H.nodesAllL C crit L γ η h := by
    intro j t ht
    unfold H.nodeAtPL at ht
    split_ifs at ht with hj
    · cases ht; exact ((H.nodesAllL C crit L γ η h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ H.nodesAllL C crit L γ η h, ∃ j, H.nodeAtPL C crit L γ η h j = some t := by
    intro t ht
    refine ⟨((H.nodesAllL C crit L γ η h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold H.nodeAtPL
    rw [dite_eq_left ((H.nodesAllL C crit L γ η h).equivFin ⟨t, ht⟩).2]
    simp
  have hjlt : ∀ j t, H.nodeAtPL C crit L γ η h j = some t → j < (H.nodesAllL C crit L γ η h).card := by
    intro j t hj
    unfold H.nodeAtPL at hj
    by_contra hnot
    rw [dite_eq_right hnot] at hj
    cases hj
  let S : Finset (ℕ × Sig1) := (Finset.range (H.nodesAllL C crit L γ η h).card) ×ˢ Finset.univ
  let post : ℕ × Sig1 → HSt V D₀ × ℕ := fun js =>
    (H.postAtPL C crit L γ η h js.1,
      bank L γ η w (H.postAtPL C crit L γ η h js.1) (clsAt1SL C Un Fst crit L γ η w h A js.1 js.2))
  let cost : ℕ × Sig1 → ℝ≥0∞ := fun js =>
    if clsAt1SL C Un Fst crit L γ η w h A js.1 js.2 = ∅ then 0 else
      ENNReal.ofReal (baseAt1L C crit L γ η CA CN CD c d h js.1 * L ^ (5 * η * ((b : ℝ) - (post js).2)))
  refine ⟨Afin, S, fun js => clsAt1SL C Un Fst crit L γ η w h A js.1 js.2, post, cost,
    fun js => wtAt1L C crit L γ η h js.1 js.2, ⟨hAfin, hbfin⟩, fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : H.Stuck1 C L γ η w Un k h
    · exact Or.inl ⟨hk, hnb⟩
    · right
      rcases hmem A h hA k hk hnb with ⟨t, ht, hkt⟩ | ⟨t, ht, hkt⟩ | ⟨t, ht, hkt⟩
      · have htm : Sum.inl (Sum.inl t) ∈ H.nodesAllL C crit L γ η h := by unfold H.nodesAllL; simpa using ht
        obtain ⟨j, hj⟩ := hsurj _ htm
        have hn : H.Node1 C crit L γ η h t := (Finset.mem_filter.1 ht).2
        obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 (split1_cover (h := h) (h' := h.vinePostL (vcut hn) (vR t) (vkp t))
          (X := vineSurv h (vcut hn) (vR t) (vkp t)) (w := w) (γ := γ) ![(vcut hn).fa, (vcut hn).fb]
          (fun k0 => pgap L w k0 (h.s.pr t.1 t.2.1)) hL _ hkt)
        refine Set.mem_iUnion₂.2 ⟨(j, σ), Finset.mem_product.2 ⟨Finset.mem_range.2 (hjlt j _ hj), Finset.mem_univ _⟩, ?_⟩
        show k ∈ clsAt1SL C Un Fst crit L γ η w h A j σ
        unfold clsAt1SL
        rw [hj]; dsimp only
        rw [dite_eq_left hn]
        exact hσ
      · have htm : Sum.inl (Sum.inr t) ∈ H.nodesAllL C crit L γ η h := by unfold H.nodesAllL; simpa using ht
        obtain ⟨j, hj⟩ := hsurj _ htm
        obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 (split1_cover (h := h) (h' := post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)
          (X := cutSurv h t.1 (fresh h) t.2.1 t.2.2.1 ((2 : ℝ) ^ t.2.2.2.1) (if t.2.2.2.2.1 then 50 else 0))
          (w := w) (γ := γ) ![t.1, fresh h] (fun k0 => pgap L w k0 (h.s.pr t.2.1 t.2.2.1)) hL _ hkt)
        refine Set.mem_iUnion₂.2 ⟨(j, σ), Finset.mem_product.2 ⟨Finset.mem_range.2 (hjlt j _ hj), Finset.mem_univ _⟩, ?_⟩
        show k ∈ clsAt1SL C Un Fst crit L γ η w h A j σ
        unfold clsAt1SL
        rw [hj]
        exact hσ
      · have htm : Sum.inr t ∈ H.nodesAllL C crit L γ η h := by unfold H.nodesAllL; simpa using ht
        obtain ⟨j, hj⟩ := hsurj _ htm
        refine Set.mem_iUnion₂.2 ⟨(j, (0, 0)), Finset.mem_product.2 ⟨Finset.mem_range.2 (hjlt j _ hj),
          Finset.mem_univ _⟩, ?_⟩
        show k ∈ clsAt1SL C Un Fst crit L γ η w h A j (0, 0)
        unfold clsAt1SL
        rw [hj]; dsimp only
        rw [ite_eq_left rfl]
        exact hkt
  · have hsum : ∑ js ∈ S, wtAt1L C crit L γ η h js.1 js.2 ≤ (H.nodesAllL C crit L γ η h).card * splitK := by
      simp only [S]
      rw [Finset.sum_product]
      calc ∑ j ∈ Finset.range (H.nodesAllL C crit L γ η h).card, ∑ σ : Sig1, wtAt1L C crit L γ η h j σ
          ≤ ∑ j ∈ Finset.range (H.nodesAllL C crit L γ η h).card, splitK :=
            Finset.sum_le_sum fun j _ => sum_wtAt1L_le C crit L γ η h j
        _ = (H.nodesAllL C crit L γ η h).card * splitK := by simp
    have : (H.nodesAllL C crit L γ η h).card + 1 ≤ N := by omega
    have h2 : (H.nodesAllL C crit L γ η h).card * splitK + splitK ≤ splitK * N := by nlinarith
    exact le_trans (Nat.add_le_add_right hsum _) h2
  · rintro ⟨j, σ⟩ hjS
    have hj : j < (H.nodesAllL C crit L γ η h).card := Finset.mem_range.1 (Finset.mem_product.1 hjS).1
    obtain ⟨t, ht⟩ : ∃ t, H.nodeAtPL C crit L γ η h j = some t := ⟨_, by unfold H.nodeAtPL; rw [dite_eq_left hj]⟩
    have htm := hmemN j t ht
    unfold H.nodesAllL at htm
    rcases t with (t | t) | t
    · -- a vine node
      have hn : H.Node1 C crit L γ η h t :=
        (Finset.mem_filter.1 (Finset.inl_mem_disjSum.1 (Finset.inl_mem_disjSum.1 htm))).2
      have hcls : clsAt1SL C Un Fst crit L γ η w h A j σ = vineSplit Un Fst w A hn σ := by
        unfold clsAt1SL; rw [ht]; dsimp only; rw [dite_eq_left hn]
      have hpost : H.postAtPL C crit L γ η h j = H.post1 C crit L γ η h t := by unfold H.postAtPL; rw [ht]
      have hbase : baseAt1L C crit L γ η CA CN CD c d h j =
          3 * 5 ^ d * vCost L γ η CA CN h (H.post1 C crit L γ η h t) := by unfold baseAt1L; rw [ht]
      have hwt : wtAt1L C crit L γ η h j σ = 1 := by unfold wtAt1L; rw [ht]
      obtain ⟨hinv, hlt, hbk, hdev⟩ := node1_bankL HR hS hp0 hExA hExN hExC hν hSrc hdec h0 hA hn hbank σ
      simp only [post, cost, hcls, hpost, hbase, hwt]
      by_cases hce : vineSplit Un Fst w A hn σ = ∅
      · rw [ite_eq_left hce]
        refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
        · rw [hce, QS_empty]; exact bot_le
        · simp
      rw [ite_eq_right hce]
      refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
      · refine hdev.trans (mul_le_mul' (ofReal_mul_mono_right (Real.rpow_nonneg hL.le _) ?_) le_rfl)
        refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
        have : (bank L γ η w (H.post1 C crit L γ η h t) (vineSplit Un Fst w A hn σ) : ℝ) ≤ (b : ℝ) + (k1Of σ : ℝ) := by
          exact_mod_cast hbk
        nlinarith
      · rw [Nat.cast_one, one_mul]
        exact child_weight hL _ b _ (hW1 h t R' hapP hc.good hn)
    · -- a triple node
      have hn' := Finset.inr_mem_disjSum.1 (Finset.inl_mem_disjSum.1 htm)
      have hn : H.NodeT C L γ η h t := ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 hn').1).2, (Finset.mem_filter.1 hn').2⟩
      have hcls : clsAt1SL C Un Fst crit L γ η w h A j σ =
          tripSplit (C := C) (L := L) (γ := γ) (η := η) Un w A t σ := by
        unfold clsAt1SL; rw [ht]
      have hpost : H.postAtPL C crit L γ η h j = post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 := by
        unfold H.postAtPL; rw [ht]
      have hbase : baseAt1L C crit L γ η CA CN CD c d h j = 3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) *
          stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) := by
        unfold baseAt1L; rw [ht]
      have hwt : wtAt1L C crit L γ η h j σ = 1 := by unfold wtAt1L; rw [ht]
      obtain ⟨hinv, hlt, hbk, hdev⟩ := nodeT_bankL (Fst := Fst) HR hS hp0 hP hP0 c hnc h0 hA hn hbank σ
      simp only [post, cost, hcls, hpost, hbase, hwt]
      by_cases hce : tripSplit (C := C) (L := L) (γ := γ) (η := η) Un w A t σ = ∅
      · rw [ite_eq_left hce]
        refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
        · rw [hce, QS_empty]; exact bot_le
        · simp
      obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hce
      rw [ite_eq_right hce]
      refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
      · refine hdev.trans (mul_le_mul' (ofReal_mul_mono_right (Real.rpow_nonneg hL.le _) ?_) le_rfl)
        refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
        have : (bank L γ η w (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)
            (tripSplit (C := C) (L := L) (γ := γ) (η := η) Un w A t σ) : ℝ) ≤ (b : ℝ) + (k1Of σ : ℝ) := by
          exact_mod_cast hbk
        nlinarith
      · have hAt : H.Inv1L M₀ Rn C Un Fst L γ η w A0 (H.Atrip C Un L γ η w h A) h := hA.mono H.Atrip_sub
        rw [Nat.cast_one, one_mul]
        exact child_weight hL _ b _ (hW3 _ h _ R' (hAt.mono fun k hk => hk.1) hapP hc.good ⟨κ, hκ.1⟩
          (uStep3_node hn.1))
    · -- a Step D1 node
      have hn : H.Node1D C crit h t := (Finset.mem_filter.1 (Finset.inr_mem_disjSum.1 htm)).2
      have hpost : H.postAtPL C crit L γ η h j = H.post1D C crit h t := by unfold H.postAtPL; rw [ht]
      have hbase : baseAt1L C crit L γ η CA CN CD c d h j = CD * excessRHS2 L γ η [] 1 2 := by
        unfold baseAt1L; rw [ht]
      obtain ⟨hinv, hlt, hbk, hdev⟩ := node1D_bankL HR hS hp0 hP hP0 hExD hν hSrc hdec h0 hA hn hbank
      by_cases hσ : σ = (0, 0)
      · have hcls : clsAt1SL C Un Fst crit L γ η w h A j σ =
            cls1D L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2 := by
          unfold clsAt1SL; rw [ht]; dsimp only; rw [ite_eq_left hσ]
        have hwt : wtAt1L C crit L γ η h j σ = splitK := by unfold wtAt1L; rw [ht]; dsimp only; rw [ite_eq_left hσ]
        simp only [post, cost, hcls, hpost, hbase, hwt]
        by_cases hce : cls1D L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2 = ∅
        · rw [ite_eq_left hce]
          refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
          · rw [hce, QS_empty]; exact bot_le
          · simp
        rw [ite_eq_right hce]
        refine ⟨hlt, ⟨hinv, le_rfl⟩, ?_, ?_⟩
        · refine hdev.trans (mul_le_mul' ?_ le_rfl)
          have hge : (1 : ℝ) ≤ L ^ (5 * η * ((b : ℝ) - (bank L γ η w (H.post1D C crit h t)
              (cls1D L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) : ℝ))) := by
            refine Real.one_le_rpow hL1 ?_
            have : (bank L γ η w (H.post1D C crit h t)
                (cls1D L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) : ℝ) ≤ b := by
              exact_mod_cast hbk
            nlinarith
          have := ofReal_mul_mono_right (a := CD * excessRHS2 L γ η [] 1 2) zero_le_one hge
          rwa [mul_one] at this
        · have hw := child_weight (η := η) hL (N : ℝ≥0∞) b (bank L γ η w (H.post1D C crit h t)
            (cls1D L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2))
            (hW1D h t R' hapP hc.good hn)
          calc ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2 * L ^ (5 * η * ((b : ℝ) -
                (bank L γ η w (H.post1D C crit h t) (cls1D L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1
                  t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) : ℝ)))) *
                (W (H.post1D C crit h t) * ENNReal.ofReal (L ^ (5 * η * ((bank L γ η w (H.post1D C crit h t)
                  (cls1D L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) : ℕ) :
                    ℝ))))) =
              (splitK : ℝ≥0∞) * ((N : ℝ≥0∞) * (ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2 * L ^ (5 * η * ((b : ℝ) -
                (bank L γ η w (H.post1D C crit h t) (cls1D L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1
                  t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) : ℝ)))) *
                (W (H.post1D C crit h t) * ENNReal.ofReal (L ^ (5 * η * ((bank L γ η w (H.post1D C crit h t)
                  (cls1D L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) : ℕ) :
                    ℝ)))))) := by push_cast; ring
            _ ≤ (splitK : ℝ≥0∞) * (W h * ENNReal.ofReal (L ^ (5 * η * (b : ℝ)))) := by gcongr
      · have hcls : clsAt1SL C Un Fst crit L γ η w h A j σ = ∅ := by
          unfold clsAt1SL; rw [ht]; dsimp only; rw [ite_eq_right hσ]
        have hwt : wtAt1L C crit L γ η h j σ = 0 := by unfold wtAt1L; rw [ht]; dsimp only; rw [ite_eq_right hσ]
        simp only [post, cost, hcls, hpost, hwt, ite_true]
        refine ⟨hlt, ⟨⟨Set.empty_subset _, Or.inl rfl⟩, le_rfl⟩, ?_, ?_⟩
        · rw [QS_empty]; exact bot_le
        · simp

end WaveTurbulence.GammaLow.FinalCount.Ghost
