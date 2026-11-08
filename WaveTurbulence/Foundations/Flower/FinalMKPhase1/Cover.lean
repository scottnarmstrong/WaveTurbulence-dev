/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Classes

/-! # C1b1 MK-PHASE1 (4): the phase-1 cover theorem with survivors (`phase1_coverLE`)

Copy-thread of main's `phase1_coverL` (LowChain14; sha256 in COPIED-SHA256SUMS) to the survivor Step 1 `HStep1RLE`:
the class invariant is `Inv1LE` (reach `Reach1LE`), the final condition is `Stuck1E` (no triple cut, every `CollectedF`
object and every survivor dartless), and the node families are main's vine, triple and D1 nodes with the survivor classes `AvineE`,
`AtripE`, plus the re-cut nodes `nodesRC` (class `cls1D` on `AvineS`, cost `CR · excessRHS2 [] 1 2`, C1a's `Ex1RC`).
As in main, the cover is generic in the potential `W` and takes the coverage (`hmem`) and the per-node potential
inequalities as hypotheses; nodes with an empty class cost `0`. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- A node with an empty class costs `0`: the per-node conclusion of the cover from the class bound and the potential
step on a nonempty class. -/
theorem cover_node_aux {α : Type*} {Q Q' : Set α → ℝ≥0∞} {B : Set α} {c W W' : ℝ≥0∞} (N : ℕ)
    (hQ : Q B ≤ c * Q' B) (hQ0 : Q' ∅ = 0) (hW : B.Nonempty → (N : ℝ≥0∞) * (c * W') ≤ W) :
    Q B ≤ (if B = ∅ then 0 else c) * Q' B ∧ (N : ℝ≥0∞) * ((if B = ∅ then 0 else c) * W') ≤ W := by
  by_cases hB : B = ∅
  · subst hB
    rw [hQ0, mul_zero] at hQ
    simp only [ite_true, zero_mul, mul_zero]
    exact ⟨hQ, zero_le⟩
  · simp only [hB, ite_false]
    exact ⟨hQ, hW (Set.nonempty_iff_ne_empty.2 hB)⟩

section cover
variable {M₀ : Molecule V D₀} {m : ℕ}

abbrev TAllLE (h : HSt V D₀) := ((T1 h ⊕ T3 h) ⊕ T1D h) ⊕ T1D h

noncomputable def nodesAllLE [Infinite V] (C : CollDataMK M₀) (crit : V → Prop) (E : Fin m → Object M₀) (L γ η : ℝ)
    (h : HSt V D₀) : Finset (TAllLE h) :=
  (((nodes1 C.toCollData crit L γ η h).disjSum (nodesT C.toCollData L γ η h)).disjSum (nodes1D C.toCollData crit h)).disjSum (nodesRC C.toCollData crit E L γ η h)

noncomputable def nodeAtPLE [Infinite V] (C : CollDataMK M₀) (crit : V → Prop) (E : Fin m → Object M₀) (L γ η : ℝ)
    (h : HSt V D₀) (j : ℕ) : Option (TAllLE h) :=
  if hj : j < (nodesAllLE C crit E L γ η h).card then
    some (((nodesAllLE C crit E L γ η h).equivFin.symm ⟨j, hj⟩ : nodesAllLE C crit E L γ η h) : TAllLE h) else none

noncomputable def clsAtPLE [Infinite V] (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (Fst : Set (Object M₀)) (E : Fin m → Object M₀) (crit : V → Prop) (L γ η : ℝ) (w : Mom d) (h : HSt V D₀)
    (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) : Set (D₀ → (Fin d → ℤ)) :=
  match nodeAtPLE C crit E L γ η h j with
  | some (Sum.inl (Sum.inl (Sum.inl t))) => cls1 L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
      t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2
  | some (Sum.inl (Sum.inl (Sum.inr t))) => cls3 L γ η w h (AtripE C Un E L γ η w h A)
      t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2
  | some (Sum.inl (Sum.inr t)) => cls1D L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
      t.1 t.2.1 t.2.2.1 t.2.2.2
  | some (Sum.inr t) => cls1D L γ η w h (AvineS E Fst h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2
  | none => ∅

noncomputable def postAtPLE [Infinite V] (C : CollDataMK M₀) (crit : V → Prop) (E : Fin m → Object M₀) (L γ η : ℝ)
    (h : HSt V D₀) (j : ℕ) : HSt V D₀ :=
  match nodeAtPLE C crit E L γ η h j with
  | some (Sum.inl (Sum.inl (Sum.inl t))) => post1 C.toCollData crit L γ η h t
  | some (Sum.inl (Sum.inl (Sum.inr t))) => post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
  | some (Sum.inl (Sum.inr t)) => post1D C.toCollData crit h t
  | some (Sum.inr t) => post1RC C.toCollData crit E L γ η h t
  | none => h

noncomputable def costAtPLE [Infinite V] (C : CollDataMK M₀) (crit : V → Prop) (E : Fin m → Object M₀)
    (L γ η CA CN CD CR : ℝ) (c d' : ℕ) (h : HSt V D₀) (j : ℕ) : ℝ≥0∞ :=
  match nodeAtPLE C crit E L γ η h j with
  | some (Sum.inl (Sum.inl (Sum.inl t))) => ENNReal.ofReal (vCost L γ η CA CN h (post1 C.toCollData crit L γ η h t))
  | some (Sum.inl (Sum.inl (Sum.inr t))) => ENNReal.ofReal (max (cAlpha d' γ η) (cBeta η c) *
      stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1))
  | some (Sum.inl (Sum.inr _)) => ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2)
  | some (Sum.inr _) => ENNReal.ofReal (CR * excessRHS2 L γ η [] 1 2)
  | none => 0

/-- **Phase 1 cover theorem with survivors (LOW run, ancestor-matched survivor cuts).** -/
theorem phase1_coverLE [Infinite V] {Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)}
    {E : Fin m → Object M₀} {crit : V → Prop} {CA CN CD CR ν : ℝ}
    (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hExA : Ex1A L γ η δ C₁ w M₀ P CA) (hExN : Ex1N L γ η δ C₁ w M₀ P CN ν) (hExD : Ex1D L γ η δ C₁ w M₀ C.toCollData P CD ν)
    (hExR : Ex1RC L γ η δ C₁ w M₀ C.toCollData P CR ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (N : ℕ)
    (hN : (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) + 1 ≤ N)
    (W : HSt V D₀ → ℝ≥0∞)
    (hmem : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h → ∀ κ ∈ A,
      ¬ Stuck1E C L γ η w Un E κ h →
      (∃ t ∈ nodes1 C.toCollData crit L γ η h, κ ∈ cls1 L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) ∨
      (∃ t ∈ nodesT C.toCollData L γ η h, κ ∈ cls3 L γ η w h (AtripE C Un E L γ η w h A)
          t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) ∨
      (∃ t ∈ nodes1D C.toCollData crit h, κ ∈ cls1D L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
          t.1 t.2.1 t.2.2.1 t.2.2.2) ∨
      (∃ t ∈ nodesRC C.toCollData crit E L γ η h, κ ∈ cls1D L γ η w h (AvineS E Fst h A t.1 t.2.1 t.2.2.1 t.2.2.2)
          t.1 t.2.1 t.2.2.1 t.2.2.2))
    (hW1 : ∀ (h : HSt V D₀) (t : T1 h) (R' : ℕ), ApPos h.s → Good R' h.s → Node1 C.toCollData crit L γ η h t →
      (N : ℝ≥0∞) * (ENNReal.ofReal (vCost L γ η CA CN h (post1 C.toCollData crit L γ η h t)) * W (post1 C.toCollData crit L γ η h t)) ≤ W h)
    (hW1D : ∀ (h : HSt V D₀) (t : T1D h) (R' : ℕ), ApPos h.s → Good R' h.s → Node1D C.toCollData crit h t →
      (N : ℝ≥0∞) * (ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2) * W (post1D C.toCollData crit h t)) ≤ W h)
    (hW3 : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀) (R' : ℕ), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h →
      ApPos h.s → Good R' h.s → (∃ k, k ∈ A) →
      UStep3 L γ η w (fun k => k ∈ A) h h' →
      (N : ℝ≥0∞) * (ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') * W h') ≤ W h)
    (hWRC : ∀ (h : HSt V D₀) (t : T1D h) (R' : ℕ), ApPos h.s → Good R' h.s → Node1RC C.toCollData crit E L γ η h t →
      (N : ℝ≥0∞) * (ENNReal.ofReal (CR * excessRHS2 L γ η [] 1 2) * W (post1RC C.toCollData crit E L γ η h t)) ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h →
      (∀ k ∈ A, Stuck1E C L γ η w Un E k h) → (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h →
      QS L γ δ C₁ w P h A ≤ W h := by
  refine cover_induction2 (ι := ℕ) (fun a b : HSt V D₀ => epsCount a.s < epsCount b.s)
    (InvImage.wf (fun h : HSt V D₀ => epsCount h.s) wellFounded_lt)
    (fun h A => Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h) (fun h A => ∀ k ∈ A, Stuck1E C L γ η w Un E k h)
    (QS L γ δ C₁ w P) W N
    (by omega) (fun h A B hAB => QS_mono L γ δ C₁ w P h hAB) (fun h A B => QS_union L γ δ C₁ w P h A B)
    (fun h => QS_empty L γ δ C₁ w P h) (fun h A => hfin A h) ?_
  intro h A hA _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ Stuck1E C L γ η w Un E k h}
  have hAfin : Inv1LE M₀ Rn C Un Fst E L γ η w A0 Afin h := hA.mono fun k hk => hk.1
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => h, fun _ => 0, hAfin, fun k hk => hk.2, ?_, (by simp; omega), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  obtain ⟨R', hR', hc⟩ := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hRC : ∀ κ ∈ A0, Reach1LE C Un Fst E L γ η w κ h → CompBeta h.s := fun κ hκ hr =>
    (invL_reach1E hS (h0 κ hκ) hr).choose_spec.2.comp
  have hcardA : h.s.M.atoms.card ≤ 2 * M₀.atoms.card := card_atoms_leL_of_uctx hS hR' hc
  have hcardD : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
  have hcard : (nodesAllLE C crit E L γ η h).card ≤ (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        (Fintype.card D₀ * ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) := by
    unfold nodesAllLE
    rw [Finset.card_disjSum, Finset.card_disjSum, Finset.card_disjSum]
    refine add_le_add (add_le_add (add_le_add ((nodes1_card C.toCollData crit L γ η h).trans ?_)
      ((nodesT_card_le C.toCollData L γ η h).trans ((nodes3_card L γ η h).trans ?_))) ((nodes1D_card C.toCollData crit h).trans ?_))
      ((nodesRC_card C.toCollData crit E L γ η h).trans ?_)
    · gcongr
    · gcongr
    · gcongr
    · gcongr
  have hmemN : ∀ j t, nodeAtPLE C crit E L γ η h j = some t → t ∈ nodesAllLE C crit E L γ η h := by
    intro j t ht
    unfold nodeAtPLE at ht
    split_ifs at ht with hj
    · cases ht; exact ((nodesAllLE C crit E L γ η h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ nodesAllLE C crit E L γ η h, ∃ j, nodeAtPLE C crit E L γ η h j = some t := by
    intro t ht
    refine ⟨((nodesAllLE C crit E L γ η h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold nodeAtPLE
    rw [dite_eq_left ((nodesAllLE C crit E L γ η h).equivFin ⟨t, ht⟩).2]
    simp
  refine ⟨Afin, Finset.range (nodesAllLE C crit E L γ η h).card, clsAtPLE C Un Fst E crit L γ η w h A,
    postAtPLE C crit E L γ η h,
    (fun j => if clsAtPLE C Un Fst E crit L γ η w h A j = ∅ then 0 else costAtPLE C crit E L γ η CA CN CD CR c d h j),
    hAfin, fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : Stuck1E C L γ η w Un E k h
    · exact Or.inl ⟨hk, hnb⟩
    · right
      have key : ∀ t ∈ nodesAllLE C crit E L γ η h, (k ∈ (match t with
          | Sum.inl (Sum.inl (Sum.inl t)) => cls1 L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
              t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2
          | Sum.inl (Sum.inl (Sum.inr t)) => cls3 L γ η w h (AtripE C Un E L γ η w h A)
              t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2
          | Sum.inl (Sum.inr t) => cls1D L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
              t.1 t.2.1 t.2.2.1 t.2.2.2
          | Sum.inr t => cls1D L γ η w h (AvineS E Fst h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2 :
            Set (D₀ → (Fin d → ℤ)))) →
          k ∈ ⋃ j ∈ Finset.range (nodesAllLE C crit E L γ η h).card, clsAtPLE C Un Fst E crit L γ η w h A j := by
        intro t htm hkt
        obtain ⟨j, hj⟩ := hsurj _ htm
        have hjl : j < (nodesAllLE C crit E L γ η h).card := by
          unfold nodeAtPLE at hj
          by_contra hnot
          rw [dite_eq_right hnot] at hj
          cases hj
        refine Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hjl, ?_⟩
        unfold clsAtPLE; rw [hj]
        rcases t with ((t | t) | t) | t <;> exact hkt
      rcases hmem A h hA k hk hnb with ⟨t, ht, hkt⟩ | ⟨t, ht, hkt⟩ | ⟨t, ht, hkt⟩ | ⟨t, ht, hkt⟩
      · exact key (Sum.inl (Sum.inl (Sum.inl t))) (by unfold nodesAllLE; simpa using ht) hkt
      · exact key (Sum.inl (Sum.inl (Sum.inr t))) (by unfold nodesAllLE; simpa using ht) hkt
      · exact key (Sum.inl (Sum.inr t)) (by unfold nodesAllLE; simpa using ht) hkt
      · exact key (Sum.inr t) (by unfold nodesAllLE; simpa using ht) hkt
  · simp only [Finset.card_range]; omega
  · intro j hjS
    have hj : j < (nodesAllLE C crit E L γ η h).card := Finset.mem_range.1 hjS
    obtain ⟨t, ht⟩ : ∃ t, nodeAtPLE C crit E L γ η h j = some t := ⟨_, by unfold nodeAtPLE; rw [dite_eq_left hj]⟩
    have htm := hmemN j t ht
    unfold nodesAllLE at htm
    rcases t with ((t | t) | t) | t
    · have hn : Node1 C.toCollData crit L γ η h t := (Finset.mem_filter.1 (Finset.inl_mem_disjSum.1
        (Finset.inl_mem_disjSum.1 (Finset.inl_mem_disjSum.1 htm)))).2
      obtain ⟨h1, h2', h3⟩ := node1_factsG H hS hp0 hExA hExN hν hSrc hdec (hA.mono AvineE_sub) hRC hn
        (fun k hk hr => Reach1LE.ext hr (hstep1RLE_vine hn hk))
      have hcls : clsAtPLE C Un Fst E crit L γ η w h A j = cls1 L γ η w h
          (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2 := by
        unfold clsAtPLE; rw [ht]
      have hpost : postAtPLE C crit E L γ η h j = post1 C.toCollData crit L γ η h t := by unfold postAtPLE; rw [ht]
      have hcost : costAtPLE C crit E L γ η CA CN CD CR c d h j =
          ENNReal.ofReal (vCost L γ η CA CN h (post1 C.toCollData crit L γ η h t)) := by
        unfold costAtPLE; rw [ht]
      beta_reduce
      rw [hpost, hcost, hcls]
      exact ⟨h2', h1, cover_node_aux N h3 (QS_empty L γ δ C₁ w P _) (fun _ => hW1 h t R' hapP hc.good hn)⟩
    · have hn' := Finset.inr_mem_disjSum.1 (Finset.inl_mem_disjSum.1 (Finset.inl_mem_disjSum.1 htm))
      have hn : NodeT C.toCollData L γ η h t := ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 hn').1).2, (Finset.mem_filter.1 hn').2⟩
      have hAt : Inv1LE M₀ Rn C Un Fst E L γ η w A0 (AtripE C Un E L γ η w h A) h := hA.mono AtripE_sub
      obtain ⟨h1, h2', h3⟩ := node3_factsL H hS hp0 hP hP0 c hnc hAt hn.1
        (fun k hk hr => Reach1LE.ext hr (hstep1RLE_trip (Fst := Fst) hn hk))
      have hcls : clsAtPLE C Un Fst E crit L γ η w h A j = cls3 L γ η w h (AtripE C Un E L γ η w h A)
          t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 := by unfold clsAtPLE; rw [ht]
      have hpost : postAtPLE C crit E L γ η h j = post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 := by
        unfold postAtPLE; rw [ht]
      have hcost : costAtPLE C crit E L γ η CA CN CD CR c d h j = ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) *
          stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)) := by
        unfold costAtPLE; rw [ht]
      beta_reduce
      rw [hpost, hcost, hcls]
      refine ⟨h2', h1, cover_node_aux N h3 (QS_empty L γ δ C₁ w P _) (fun ⟨κ, hκ⟩ => ?_)⟩
      exact hW3 _ h _ R' (hAt.mono fun k hk => hk.1) hapP hc.good ⟨κ, hκ⟩ (uStep3_node hn.1)
    · have hn : Node1D C.toCollData crit h t := (Finset.mem_filter.1 (Finset.inr_mem_disjSum.1
        (Finset.inl_mem_disjSum.1 htm))).2
      obtain ⟨h1, h2', h3⟩ := node1D_factsG hS hp0 hP hP0 hExD hν hSrc hdec (hA.mono AvineE_sub) hRC hn
        (fun k hk hr => Reach1LE.ext hr (hstep1RLE_D1 hn hk))
      have hcls : clsAtPLE C Un Fst E crit L γ η w h A j = cls1D L γ η w h
          (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2 := by
        unfold clsAtPLE; rw [ht]
      have hpost : postAtPLE C crit E L γ η h j = post1D C.toCollData crit h t := by unfold postAtPLE; rw [ht]
      have hcost : costAtPLE C crit E L γ η CA CN CD CR c d h j = ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2) := by
        unfold costAtPLE; rw [ht]
      beta_reduce
      rw [hpost, hcost, hcls]
      exact ⟨h2', h1, cover_node_aux N h3 (QS_empty L γ δ C₁ w P _) (fun _ => hW1D h t R' hapP hc.good hn)⟩
    · have hn : Node1RC C.toCollData crit E L γ η h t := (Finset.mem_filter.1 (Finset.inr_mem_disjSum.1 htm)).2
      obtain ⟨h1, h2', h3⟩ := nodeRC_factsG hS hp0 hP hP0 hExR hν hSrc hdec (hA.mono AvineS_sub) hRC hn
        (fun k hk hr => Reach1LE.ext hr (hstep1RLE_RC (Un := Un) hn hk))
      have hcls : clsAtPLE C Un Fst E crit L γ η w h A j = cls1D L γ η w h
          (AvineS E Fst h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2 := by
        unfold clsAtPLE; rw [ht]
      have hpost : postAtPLE C crit E L γ η h j = post1RC C.toCollData crit E L γ η h t := by unfold postAtPLE; rw [ht]
      have hcost : costAtPLE C crit E L γ η CA CN CD CR c d h j = ENNReal.ofReal (CR * excessRHS2 L γ η [] 1 2) := by
        unfold costAtPLE; rw [ht]
      beta_reduce
      rw [hpost, hcost, hcls]
      exact ⟨h2', h1, cover_node_aux N h3 (QS_empty L γ δ C₁ w P _) (fun _ => hWRC h t R' hapP hc.good hn)⟩

end cover

end WaveTurbulence.Flower.FinalMKPhase1
