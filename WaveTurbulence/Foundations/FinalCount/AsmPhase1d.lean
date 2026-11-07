/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase1c
public import WaveTurbulence.Foundations.FinalCount.AsmCover2
/-! **FINALCOUNT-ASSEMBLY, phase 1: the cover theorem of Step 1** (vine removals and triple cuts), `∀ h A, Inv1 A h → QS h A ≤ W h`, from the
per-step inequalities `hW1`, `hW3`, the terminal inequality `hfin` and the coverage `hmem` (a non-stuck decoration lies in a node class; proved by the
existence part). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The stop condition of Step 1 (`HRunNC`, first stage). -/
def Stuck1 {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  NoTripleCut C L γ η w κ h ∧ ∀ U : Object M₀, Collected C (Un κ) L γ η w κ U → Dartless U h

noncomputable def nodesAll [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) :
    Finset (T1 h ⊕ T3 h) :=
  (nodes1 C crit L γ η h).disjSum (nodesT C L γ η h)

noncomputable def nodeAtP [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) :
    Option (T1 h ⊕ T3 h) :=
  if hj : j < (nodesAll C crit L γ η h).card then
    some (((nodesAll C crit L γ η h).equivFin.symm ⟨j, hj⟩ : nodesAll C crit L γ η h) : T1 h ⊕ T3 h) else none

noncomputable def clsAtP [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (Fst : Set (Object M₀)) (crit : V → Prop) (L γ η : ℝ) (w : Mom d) (h : HSt V D₀)
    (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) : Set (D₀ → (Fin d → ℤ)) :=
  match nodeAtP C crit L γ η h j with
  | some (Sum.inl t) => cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
      t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2
  | some (Sum.inr t) => cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2
  | none => ∅

noncomputable def postAtP [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) :
    HSt V D₀ :=
  match nodeAtP C crit L γ η h j with
  | some (Sum.inl t) => post1 C crit L γ η h t
  | some (Sum.inr t) => post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
  | none => h

noncomputable def costAtP [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η CA CN : ℝ) (c d' : ℕ)
    (h : HSt V D₀) (j : ℕ) : ℝ≥0∞ :=
  match nodeAtP C crit L γ η h j with
  | some (Sum.inl t) => ENNReal.ofReal (vCost L γ η CA CN h (post1 C crit L γ η h t))
  | some (Sum.inr t) => ENNReal.ofReal (max (cAlpha d' γ η) (cBeta η c) *
      stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1))
  | none => 0

/-- **Phase 1 cover theorem.** -/
theorem phase1_cover [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {crit : V → Prop} {CA CN ν : ℝ}
    (H : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hExA : Ex1A L γ η δ C₁ w M₀ P CA) (hExN : Ex1N L γ η δ C₁ w M₀ P CN ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (N : ℕ)
    (hN : (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) + 1 ≤ N)
    (W : HSt V D₀ → ℝ≥0∞)
    (hmem : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1 M₀ Rn C Un Fst L γ η w A0 A h → ∀ κ ∈ A,
      ¬ Stuck1 C L γ η w Un κ h →
      (∃ t ∈ nodes1 C crit L γ η h, κ ∈ cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
          t.2.2.2.2.2.2.2) ∨
      (∃ t ∈ nodesT C L γ η h, κ ∈ cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2))
    (hW1 : ∀ (h : HSt V D₀) (t : T1 h), ApPos h.s → Inv Rn h.s → Node1 C crit L γ η h t →
      (N : ℝ≥0∞) * (ENNReal.ofReal (vCost L γ η CA CN h (post1 C crit L γ η h t)) * W (post1 C crit L γ η h t)) ≤ W h)
    (hW3 : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀), Inv1 M₀ Rn C Un Fst L γ η w A0 A h → ApPos h.s → Inv Rn h.s →
      UStep3 L γ η w (fun k => k ∈ A) h h' →
      (N : ℝ≥0∞) * (ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') * W h') ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1 M₀ Rn C Un Fst L γ η w A0 A h →
      (∀ k ∈ A, Stuck1 C L γ η w Un k h) → (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv1 M₀ Rn C Un Fst L γ η w A0 A h → QS L γ δ C₁ w P h A ≤ W h := by
  refine cover_induction2 (ι := ℕ) (fun a b : HSt V D₀ => epsCount a.s < epsCount b.s)
    (InvImage.wf (fun h : HSt V D₀ => epsCount h.s) wellFounded_lt)
    (fun h A => Inv1 M₀ Rn C Un Fst L γ η w A0 A h) (fun h A => ∀ k ∈ A, Stuck1 C L γ η w Un k h)
    (QS L γ δ C₁ w P) W N
    (by omega) (fun h A B hAB => QS_mono L γ δ C₁ w P h hAB) (fun h A B => QS_union L γ δ C₁ w P h A B)
    (fun h => QS_empty L γ δ C₁ w P h) (fun h A => hfin A h) ?_
  intro h A hA _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ Stuck1 C L γ η w Un k h}
  have hAfin : Inv1 M₀ Rn C Un Fst L γ η w A0 Afin h := hA.mono fun k hk => hk.1
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => h, fun _ => 0, hAfin, fun k hk => hk.2, ?_, (by simp; omega), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  have hc : UCtx M₀ Rn (fun k => k ∈ A) L w h := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hcardA : h.s.M.atoms.card ≤ 2 * M₀.atoms.card := UCtx.card_atoms_le hS hc
  have hcardD : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
  have hcard : (nodesAll C crit L γ η h).card ≤ (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) := by
    unfold nodesAll
    rw [Finset.card_disjSum]
    refine add_le_add ((nodes1_card C crit L γ η h).trans ?_) ((nodesT_card_le C L γ η h).trans ((nodes3_card L γ η h).trans ?_))
    · gcongr
    · gcongr
  have hmemN : ∀ j t, nodeAtP C crit L γ η h j = some t → t ∈ nodesAll C crit L γ η h := by
    intro j t ht
    unfold nodeAtP at ht
    split_ifs at ht with hj
    · cases ht; exact ((nodesAll C crit L γ η h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ nodesAll C crit L γ η h, ∃ j, nodeAtP C crit L γ η h j = some t := by
    intro t ht
    refine ⟨((nodesAll C crit L γ η h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold nodeAtP
    rw [dif_pos ((nodesAll C crit L γ η h).equivFin ⟨t, ht⟩).2]
    simp
  refine ⟨Afin, Finset.range (nodesAll C crit L γ η h).card, clsAtP C Un Fst crit L γ η w h A, postAtP C crit L γ η h,
    costAtP C crit L γ η CA CN c d h, hAfin, fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : Stuck1 C L γ η w Un k h
    · exact Or.inl ⟨hk, hnb⟩
    · right
      have hj : ∃ j, j < (nodesAll C crit L γ η h).card ∧ k ∈ clsAtP C Un Fst crit L γ η w h A j := by
        rcases hmem A h hA k hk hnb with ⟨t, ht, hkt⟩ | ⟨t, ht, hkt⟩
        · have htm : Sum.inl t ∈ nodesAll C crit L γ η h := by unfold nodesAll; simpa using ht
          obtain ⟨j, hj⟩ := hsurj _ htm
          have hjl : j < (nodesAll C crit L γ η h).card := by
            unfold nodeAtP at hj
            by_contra hnot
            rw [dif_neg hnot] at hj
            cases hj
          refine ⟨j, hjl, ?_⟩
          unfold clsAtP; rw [hj]; exact hkt
        · have htm : Sum.inr t ∈ nodesAll C crit L γ η h := by unfold nodesAll; simpa using ht
          obtain ⟨j, hj⟩ := hsurj _ htm
          have hjl : j < (nodesAll C crit L γ η h).card := by
            unfold nodeAtP at hj
            by_contra hnot
            rw [dif_neg hnot] at hj
            cases hj
          refine ⟨j, hjl, ?_⟩
          unfold clsAtP; rw [hj]; exact hkt
      obtain ⟨j, hjl, hkj⟩ := hj
      exact Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hjl, hkj⟩
  · simp only [Finset.card_range]; omega
  · intro j hjS
    have hj : j < (nodesAll C crit L γ η h).card := Finset.mem_range.1 hjS
    obtain ⟨t, ht⟩ : ∃ t, nodeAtP C crit L γ η h j = some t := ⟨_, by unfold nodeAtP; rw [dif_pos hj]⟩
    have htm := hmemN j t ht
    unfold nodesAll at htm
    rcases t with t | t
    · have hn : Node1 C crit L γ η h t := (Finset.mem_filter.1 (Finset.inl_mem_disjSum.1 htm)).2
      obtain ⟨h1, h2', h3⟩ := node1_facts H hS hp0 hExA hExN hν hSrc hdec h0 (hA.mono Avine_sub) hn
        (fun k hk hr => hr.tail (hstep1R_node hn hk))
      have hcls : clsAtP C Un Fst crit L γ η w h A j = cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1
          t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2 := by unfold clsAtP; rw [ht]
      have hpost : postAtP C crit L γ η h j = post1 C crit L γ η h t := by unfold postAtP; rw [ht]
      have hcost : costAtP C crit L γ η CA CN c d h j = ENNReal.ofReal (vCost L γ η CA CN h (post1 C crit L γ η h t)) := by
        unfold costAtP; rw [ht]
      rw [hcls, hpost, hcost]
      exact ⟨h2', h1, h3, hW1 h t hapP hc.good.1 hn⟩
    · have hn' := Finset.inr_mem_disjSum.1 htm
      have hn : NodeT C L γ η h t := ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 hn').1).2, (Finset.mem_filter.1 hn').2⟩
      have hAt : Inv1 M₀ Rn C Un Fst L γ η w A0 (Atrip C Un L γ η w h A) h := hA.mono Atrip_sub
      obtain ⟨h1, h2', h3⟩ := nodeT_facts H hS hp0 hP hP0 c hnc hAt (fun k hk => hk.2) hn
      have hcls : clsAtP C Un Fst crit L γ η w h A j = cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1
          t.2.2.2.2.2.2 := by unfold clsAtP; rw [ht]
      have hpost : postAtP C crit L γ η h j = post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 := by unfold postAtP; rw [ht]
      have hcost : costAtP C crit L γ η CA CN c d h j = ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) *
          stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)) := by
        unfold costAtP; rw [ht]
      rw [hcls, hpost, hcost]
      exact ⟨h2', h1, h3, hW3 _ h _ (hAt.mono fun k hk => hk.1) hapP hc.good.1 (uStep3_node hn.1)⟩

end WaveTurbulence.FinalCountAsm
