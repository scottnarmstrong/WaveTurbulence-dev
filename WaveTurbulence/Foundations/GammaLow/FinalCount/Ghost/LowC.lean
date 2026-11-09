/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.LowB
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase1G
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain11
/-! **Ghost assembly, LOW chain (C): the Step D3 phase with the bank** (design: `CHAIN-DESIGN.md`).

`phaseD3_bank_coverL`: H's `phaseD3_coverL` (`H/FinalCount/LowChain11.lean`) carrying the bank: for every class `A` of
the phase invariant and every `b ≥ bank h A`, `QS h A ≤ W h · L^{5ηb}`, from the same potential step and the terminal
bound with the bank. A Step D3 does not increase the bank (`bank_betaPost_le`), so each node has one child (split
factor `1`), with the child's actual bank. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **The Step D3 phase with the bank.** -/
theorem phaseD3_bank_coverL {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop}
    {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : H.CollData M₀}
    (HR : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀) (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀)
    (hext : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D), D3Data h v x₁ x₂ →
      H.Desig C (h.anc v) (h.s.pr x₁ x₂) → ∀ k ∈ clsD3 L w h A x₁ x₂, Rch k h → Rch k (h.betaPost v x₁ x₂))
    (N : ℕ) (hN : 2 * M₀.atoms.card * Fintype.card D₀ * Fintype.card D₀ + 1 ≤ N) (W : HSt V D₀ → ℝ≥0∞)
    (hW : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀) (R' : ℕ), Inv3L M₀ Rn Rch L w A0 A h →
      ApPos h.s → Good R' h.s → (∃ k, k ∈ A) →
      H.UStepD3 C L γ η w (fun k => k ∈ A) h h' →
      (N : ℝ≥0∞) * (ENNReal.ofReal (excessRHS L γ η [] 1 2) * W h') ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (b : ℕ), Inv3L M₀ Rn Rch L w A0 A h →
      bank L γ η w h A ≤ b → (∀ k ∈ A, H.NoD3 C L w k h) →
      (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h * ENNReal.ofReal (L ^ (5 * η * (b : ℝ)))) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (b : ℕ), Inv3L M₀ Rn Rch L w A0 A h →
      bank L γ η w h A ≤ b → QS L γ δ C₁ w P h A ≤ W h * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) HR.hL
  have hL : 0 < L := by linarith
  have hη0 : 0 ≤ η := HR.hη.le
  have hN1 : 1 ≤ N := by omega
  suffices key : ∀ (hb : HSt V D₀ × ℕ) (A : Set (D₀ → (Fin d → ℤ))),
      (Inv3L M₀ Rn Rch L w A0 A hb.1 ∧ bank L γ η w hb.1 A ≤ hb.2) →
        QS L γ δ C₁ w P hb.1 A ≤ W hb.1 * ENNReal.ofReal (L ^ (5 * η * (hb.2 : ℝ))) by
    intro h A b hA hb
    exact key (h, b) A ⟨hA, hb⟩
  refine cover_induction_split (ι := ℕ) (fun a b : HSt V D₀ × ℕ => epsCount a.1.s < epsCount b.1.s)
    (InvImage.wf (fun hb : HSt V D₀ × ℕ => epsCount hb.1.s) wellFounded_lt)
    (fun hb A => Inv3L M₀ Rn Rch L w A0 A hb.1 ∧ bank L γ η w hb.1 A ≤ hb.2)
    (fun hb A => ∀ k ∈ A, H.NoD3 C L w k hb.1)
    (fun hb A => QS L γ δ C₁ w P hb.1 A) (fun hb => W hb.1 * ENNReal.ofReal (L ^ (5 * η * (hb.2 : ℝ)))) N 1
    hN1 le_rfl (fun hb A B hAB => QS_mono L γ δ C₁ w P hb.1 hAB) (fun hb A B => QS_union L γ δ C₁ w P hb.1 A B)
    (fun hb => QS_empty L γ δ C₁ w P hb.1) ?_ ?_
  · rintro ⟨h, b⟩ A ⟨hA, hbA⟩ hf
    exact hfin A h b hA hbA hf
  rintro ⟨h, b⟩ A ⟨hA, hbank⟩ _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ H.NoD3 C L w k h}
  have hAfin : Inv3L M₀ Rn Rch L w A0 Afin h := hA.mono fun k hk => hk.1
  have hbfin : bank L γ η w h Afin ≤ b := (bank_mono fun k hk => hk.1).trans hbank
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => (h, b), fun _ => 0, ⟨hAfin, hbfin⟩, fun k hk => hk.2, ?_,
      (by simp; omega), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  obtain ⟨R', hR', hc⟩ := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hcard : (H.nodesD3 C h).card ≤ 2 * M₀.atoms.card * Fintype.card D₀ * Fintype.card D₀ := by
    refine (H.nodesD3_card C h).trans ?_
    have h1 := card_atoms_leL_of_uctx hS hR' hc
    have h2 : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
    exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h2
  have hmem : ∀ j t, H.nodeAtD3 C h j = some t → t ∈ H.nodesD3 C h := by
    intro j t ht
    unfold H.nodeAtD3 at ht
    split_ifs at ht with hj
    · cases ht; exact ((H.nodesD3 C h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ H.nodesD3 C h, ∃ j, H.nodeAtD3 C h j = some t := by
    intro t ht
    refine ⟨((H.nodesD3 C h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold H.nodeAtD3
    rw [dite_eq_left ((H.nodesD3 C h).equivFin ⟨t, ht⟩).2]
    simp
  let post : ℕ → HSt V D₀ × ℕ := fun j =>
    (H.postAtD3 C h j, bank L γ η w (H.postAtD3 C h j) (H.clsAtD3 C L w h A j))
  let cost : ℕ → ℝ≥0∞ := fun j =>
    if H.clsAtD3 C L w h A j = ∅ then 0 else
      ENNReal.ofReal (excessRHS L γ η [] 1 2 * L ^ (5 * η * ((b : ℝ) - (post j).2)))
  refine ⟨Afin, Finset.range (H.nodesD3 C h).card, H.clsAtD3 C L w h A, post, cost, ⟨hAfin, hbfin⟩,
    fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : H.NoD3 C L w k h
    · exact Or.inl ⟨hk, hnb⟩
    · right
      unfold H.NoD3 at hnb
      push Not at hnb
      obtain ⟨v, x₁, x₂, hD, hnz, hdes⟩ := hnb
      have hmt : (v, x₁, x₂) ∈ H.nodesD3 C h :=
        Finset.mem_filter.2 ⟨by simp [hD.hv], hD, hdes⟩
      obtain ⟨j, hj⟩ := hsurj _ hmt
      have hjS : j ∈ Finset.range (H.nodesD3 C h).card := by
        unfold H.nodeAtD3 at hj
        by_contra hnot
        rw [dite_eq_right (by simpa using hnot)] at hj
        cases hj
      refine Set.mem_iUnion₂.2 ⟨j, hjS, ?_⟩
      unfold H.clsAtD3
      rw [hj]
      exact ⟨hk, hnz⟩
  · simp only [Finset.card_range, one_mul]; omega
  · intro j hjS
    have hj : j < (H.nodesD3 C h).card := Finset.mem_range.1 hjS
    obtain ⟨t, ht⟩ : ∃ t, H.nodeAtD3 C h j = some t := ⟨_, by unfold H.nodeAtD3; rw [dite_eq_left hj]⟩
    have htm := hmem j t ht
    have hnd : D3Data h t.1 t.2.1 t.2.2 := (Finset.mem_filter.1 htm).2.1
    have hdes : H.Desig C (h.anc t.1) (h.s.pr t.2.1 t.2.2) := (Finset.mem_filter.1 htm).2.2
    obtain ⟨h1, h2, h3⟩ := H.nodeD3_factsL (δ := δ) (C₁ := C₁) (P := P) HR hp0 hA hnd hdes (hext A h _ _ _ hnd hdes)
    have hcls : H.clsAtD3 C L w h A j = clsD3 L w h A t.2.1 t.2.2 := by unfold H.clsAtD3; rw [ht]
    have hpost : H.postAtD3 C h j = h.betaPost t.1 t.2.1 t.2.2 := by unfold H.postAtD3; rw [ht]
    have hbk : bank L γ η w (h.betaPost t.1 t.2.1 t.2.2) (clsD3 L w h A t.2.1 t.2.2) ≤ b :=
      (bank_betaPost_le h t.1 t.2.1 t.2.2 (fun k hk => hk.1)).trans hbank
    simp only [post, cost, hcls, hpost]
    by_cases hce : clsD3 L w h A t.2.1 t.2.2 = ∅
    · rw [ite_eq_left hce]
      refine ⟨h2, ⟨h1, le_rfl⟩, ?_, ?_⟩
      · rw [hce, QS_empty]; exact bot_le
      · simp
    obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hce
    rw [ite_eq_right hce]
    refine ⟨h2, ⟨h1, le_rfl⟩, ?_, ?_⟩
    · refine h3.trans (mul_le_mul' ?_ le_rfl)
      have hge : (1 : ℝ) ≤ L ^ (5 * η * ((b : ℝ) - (bank L γ η w (h.betaPost t.1 t.2.1 t.2.2)
          (clsD3 L w h A t.2.1 t.2.2) : ℝ))) := by
        refine Real.one_le_rpow hL1 ?_
        have : (bank L γ η w (h.betaPost t.1 t.2.1 t.2.2) (clsD3 L w h A t.2.1 t.2.2) : ℝ) ≤ b := by
          exact_mod_cast hbk
        nlinarith
      have := ofReal_mul_mono_right (a := excessRHS L γ η [] 1 2) zero_le_one hge
      rwa [mul_one] at this
    · have hW' := hW (clsD3 L w h A t.2.1 t.2.2) h (h.betaPost t.1 t.2.1 t.2.2) R' (hA.mono fun k hk => hk.1) hapP
        hc.good ⟨κ, hκ⟩ (H.uStepD3_node hnd hdes)
      have e : ((1 * N : ℕ) : ℝ≥0∞) = (N : ℝ≥0∞) := by simp
      rw [e]
      exact child_weight hL _ b _ hW'

end WaveTurbulence.GammaLow.FinalCount.Ghost
