/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain18
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain17
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain18`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, LC-2 (10): the phase-1 cover theorem `phase1_coverL2`** (vine nodes, triple nodes and Step D1 nodes;
copy of `phase1_cover` with `Inv1L`, `SubHypL`, an index `R' ≤ Rn`; nodes with an empty class cost `0`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

noncomputable def nodesAllL2 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) :
    Finset (TAllL2 h) :=
  ((nodes1 C crit L γ η h).disjSum (nodesT C L γ η h)).disjSum (nodes1Dg C crit h)

noncomputable def nodeAtPL2 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) :
    Option (TAllL2 h) :=
  if hj : j < (nodesAllL2 C crit L γ η h).card then
    some (((nodesAllL2 C crit L γ η h).equivFin.symm ⟨j, hj⟩ : nodesAllL2 C crit L γ η h) : TAllL2 h) else none

noncomputable def clsAtPL2 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀))
    (Fst : Set (Src.Object Src.γL M₀)) (crit : V → Prop) (L γ η : ℝ) (w : Mom d) (h : HSt V D₀)
    (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) : Set (D₀ → (Fin d → ℤ)) :=
  match nodeAtPL2 C crit L γ η h j with
  | some (Sum.inl (Sum.inl t)) => cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
      t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2
  | some (Sum.inl (Sum.inr t)) => cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2
  | some (Sum.inr t) => cls1D L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2
  | none => ∅

noncomputable def postAtPL2 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) :
    HSt V D₀ :=
  match nodeAtPL2 C crit L γ η h j with
  | some (Sum.inl (Sum.inl t)) => post1 C crit L γ η h t
  | some (Sum.inl (Sum.inr t)) => post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
  | some (Sum.inr t) => post1Dg C crit h t
  | none => h

noncomputable def costAtPL2 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η CA CN CD : ℝ) (c d' : ℕ)
    (cP : (h : HSt V D₀) → T1D h → ℝ≥0∞) (h : HSt V D₀) (j : ℕ) : ℝ≥0∞ :=
  match nodeAtPL2 C crit L γ η h j with
  | some (Sum.inl (Sum.inl t)) => ENNReal.ofReal (vCost L γ η CA CN h (post1 C crit L γ η h t))
  | some (Sum.inl (Sum.inr t)) => ENNReal.ofReal (max (cAlpha d' γ η) (cBeta η c) *
      stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1))
  | some (Sum.inr t) => if PendQ C crit h t then cP h t else ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2)
  | none => 0

/-- **Phase 1 cover theorem (LOW run).** -/
theorem phase1_coverL2 [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {crit : V → Prop}
    {CA CN CD ν : ℝ}
    (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hExA : Ex1A L γ η δ C₁ w M₀ P CA) (hExN : Ex1N L γ η δ C₁ w M₀ P CN ν) (hExD : Ex1D L γ η δ C₁ w M₀ C P CD ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (N : ℕ)
    (hN : (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) + 1 ≤ N)
    (W : HSt V D₀ → ℝ≥0∞) (cP : (h : HSt V D₀) → T1D h → ℝ≥0∞)
    (hmem : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1L M₀ Rn C Un Fst L γ η w A0 A h → ∀ κ ∈ A,
      ¬ Stuck1 C L γ η w Un κ h →
      (∃ t ∈ nodes1 C crit L γ η h, κ ∈ cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
          t.2.2.2.2.2.2.2) ∨
      (∃ t ∈ nodesT C L γ η h, κ ∈ cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) ∨
      (∃ t ∈ nodes1Dg C crit h, κ ∈ cls1D L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
          t.1 t.2.1 t.2.2.1 t.2.2.2))
    (hW1 : ∀ (h : HSt V D₀) (t : T1 h) (R' : ℕ), ApPos h.s → Good R' h.s → Node1 C crit L γ η h t →
      (N : ℝ≥0∞) * (ENNReal.ofReal (vCost L γ η CA CN h (post1 C crit L γ η h t)) * W (post1 C crit L γ η h t)) ≤ W h)
    (hW1D : ∀ (h : HSt V D₀) (t : T1D h) (R' : ℕ), ApPos h.s → Good R' h.s → Node1Dg C crit h t → ¬ PendQ C crit h t →
      (N : ℝ≥0∞) * (ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2) * W (post1Dg C crit h t)) ≤ W h)
    (hPend : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (t : T1D h) (R' : ℕ), Inv1L M₀ Rn C Un Fst L γ η w A0 A h →
      ApPos h.s → Good R' h.s → PendQ C crit h t →
      QS L γ δ C₁ w P h (cls1D L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) ≤
        cP h t * QS L γ δ C₁ w P (post1Dg C crit h t) (cls1D L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) ∧
      (N : ℝ≥0∞) * (cP h t * W (post1Dg C crit h t)) ≤ W h)
    (hW3 : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀) (R' : ℕ), Inv1L M₀ Rn C Un Fst L γ η w A0 A h → ApPos h.s →
      Good R' h.s → (∃ k, k ∈ A) →
      UStep3 L γ η w (fun k => k ∈ A) h h' →
      (N : ℝ≥0∞) * (ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') * W h') ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1L M₀ Rn C Un Fst L γ η w A0 A h →
      (∀ k ∈ A, Stuck1 C L γ η w Un k h) → (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv1L M₀ Rn C Un Fst L γ η w A0 A h → QS L γ δ C₁ w P h A ≤ W h := by
  refine cover_induction2 (ι := ℕ) (fun a b : HSt V D₀ => epsCount a.s < epsCount b.s)
    (InvImage.wf (fun h : HSt V D₀ => epsCount h.s) wellFounded_lt)
    (fun h A => Inv1L M₀ Rn C Un Fst L γ η w A0 A h) (fun h A => ∀ k ∈ A, Stuck1 C L γ η w Un k h)
    (QS L γ δ C₁ w P) W N
    (by omega) (fun h A B hAB => QS_mono L γ δ C₁ w P h hAB) (fun h A B => QS_union L γ δ C₁ w P h A B)
    (fun h => QS_empty L γ δ C₁ w P h) (fun h A => hfin A h) ?_
  intro h A hA _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ Stuck1 C L γ η w Un k h}
  have hAfin : Inv1L M₀ Rn C Un Fst L γ η w A0 Afin h := hA.mono fun k hk => hk.1
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => h, fun _ => 0, hAfin, fun k hk => hk.2, ?_, (by simp; omega), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  obtain ⟨R', hR', hc⟩ := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hcardA : h.s.M.atoms.card ≤ 2 * M₀.atoms.card := card_atoms_leL_of_uctx hS hR' hc
  have hcardD : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
  have hcard : (nodesAllL2 C crit L γ η h).card ≤ (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) := by
    unfold nodesAllL2
    rw [Finset.card_disjSum, Finset.card_disjSum]
    refine add_le_add (add_le_add ((nodes1_card C crit L γ η h).trans ?_)
      ((nodesT_card_le C L γ η h).trans ((nodes3_card L γ η h).trans ?_))) ((nodes1Dg_card C crit h).trans ?_)
    · gcongr
    · gcongr
    · gcongr
  have hmemN : ∀ j t, nodeAtPL2 C crit L γ η h j = some t → t ∈ nodesAllL2 C crit L γ η h := by
    intro j t ht
    unfold nodeAtPL2 at ht
    split_ifs at ht with hj
    · cases ht; exact ((nodesAllL2 C crit L γ η h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ nodesAllL2 C crit L γ η h, ∃ j, nodeAtPL2 C crit L γ η h j = some t := by
    intro t ht
    refine ⟨((nodesAllL2 C crit L γ η h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold nodeAtPL2
    rw [dif_pos ((nodesAllL2 C crit L γ η h).equivFin ⟨t, ht⟩).2]
    simp
  refine ⟨Afin, Finset.range (nodesAllL2 C crit L γ η h).card, clsAtPL2 C Un Fst crit L γ η w h A, postAtPL2 C crit L γ η h,
    (fun j => if clsAtPL2 C Un Fst crit L γ η w h A j = ∅ then 0 else costAtPL2 C crit L γ η CA CN CD c d cP h j),
    hAfin, fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : Stuck1 C L γ η w Un k h
    · exact Or.inl ⟨hk, hnb⟩
    · right
      have hj : ∃ j, j < (nodesAllL2 C crit L γ η h).card ∧ k ∈ clsAtPL2 C Un Fst crit L γ η w h A j := by
        have key : ∀ t ∈ nodesAllL2 C crit L γ η h, (k ∈ (match t with
            | Sum.inl (Sum.inl t) => cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
                t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2
            | Sum.inl (Sum.inr t) => cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2
            | Sum.inr t => cls1D L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2 : Set (D₀ → (Fin d → ℤ)))) →
            ∃ j, j < (nodesAllL2 C crit L γ η h).card ∧ k ∈ clsAtPL2 C Un Fst crit L γ η w h A j := by
          intro t htm hkt
          obtain ⟨j, hj⟩ := hsurj _ htm
          have hjl : j < (nodesAllL2 C crit L γ η h).card := by
            unfold nodeAtPL2 at hj
            by_contra hnot
            rw [dif_neg hnot] at hj
            cases hj
          refine ⟨j, hjl, ?_⟩
          unfold clsAtPL2; rw [hj]
          rcases t with (t | t) | t <;> exact hkt
        rcases hmem A h hA k hk hnb with ⟨t, ht, hkt⟩ | ⟨t, ht, hkt⟩ | ⟨t, ht, hkt⟩
        · exact key (Sum.inl (Sum.inl t)) (by unfold nodesAllL2; simpa using ht) hkt
        · exact key (Sum.inl (Sum.inr t)) (by unfold nodesAllL2; simpa using ht) hkt
        · exact key (Sum.inr t) (by unfold nodesAllL2; simpa using ht) hkt
      obtain ⟨j, hjl, hkj⟩ := hj
      exact Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hjl, hkj⟩
  · simp only [Finset.card_range]; omega
  · intro j hjS
    have hj : j < (nodesAllL2 C crit L γ η h).card := Finset.mem_range.1 hjS
    obtain ⟨t, ht⟩ : ∃ t, nodeAtPL2 C crit L γ η h j = some t := ⟨_, by unfold nodeAtPL2; rw [dif_pos hj]⟩
    have htm := hmemN j t ht
    unfold nodesAllL2 at htm
    rcases t with (t | t) | t
    · have hn : Node1 C crit L γ η h t :=
        (Finset.mem_filter.1 (Finset.inl_mem_disjSum.1 (Finset.inl_mem_disjSum.1 htm))).2
      obtain ⟨h1, h2', h3⟩ := node1_factsL H hS hp0 hExA hExN hν hSrc hdec h0 (hA.mono Avine_sub) hn
        (fun k hk hr => hr.ext (HStep1RL.old (hstep1R_node hn hk)))
      have hcls : clsAtPL2 C Un Fst crit L γ η w h A j = cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1
          t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2 := by unfold clsAtPL2; rw [ht]
      have hpost : postAtPL2 C crit L γ η h j = post1 C crit L γ η h t := by unfold postAtPL2; rw [ht]
      have hcost : costAtPL2 C crit L γ η CA CN CD c d cP h j = ENNReal.ofReal (vCost L γ η CA CN h (post1 C crit L γ η h t)) := by
        unfold costAtPL2; rw [ht]
      rw [hpost]
      by_cases hce : clsAtPL2 C Un Fst crit L γ η w h A j = ∅
      · rw [hcls] at hce
        rw [hce] at h1
        simp only [hcls, hce, if_true, QS_empty]
        exact ⟨h2', h1, by simp, by simp⟩
      · simp only [hce, if_false]
        rw [hcls] at hce
        obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hce
        rw [hcls, hcost]
        exact ⟨h2', h1, h3, hW1 h t R' hapP hc.good hn⟩
    · have hn' := Finset.inr_mem_disjSum.1 (Finset.inl_mem_disjSum.1 htm)
      have hn : NodeT C L γ η h t := ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 hn').1).2, (Finset.mem_filter.1 hn').2⟩
      have hAt : Inv1L M₀ Rn C Un Fst L γ η w A0 (Atrip C Un L γ η w h A) h := hA.mono Atrip_sub
      obtain ⟨h1, h2', h3⟩ := nodeT_factsL H hS hp0 hP hP0 c hnc hAt (fun k hk => hk.2) hn
      have hcls : clsAtPL2 C Un Fst crit L γ η w h A j = cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1
          t.2.2.2.2.2.2 := by unfold clsAtPL2; rw [ht]
      have hpost : postAtPL2 C crit L γ η h j = post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 := by unfold postAtPL2; rw [ht]
      have hcost : costAtPL2 C crit L γ η CA CN CD c d cP h j = ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) *
          stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)) := by
        unfold costAtPL2; rw [ht]
      rw [hpost]
      by_cases hce : clsAtPL2 C Un Fst crit L γ η w h A j = ∅
      · rw [hcls] at hce
        rw [hce] at h1
        simp only [hcls, hce, if_true, QS_empty]
        exact ⟨h2', h1, by simp, by simp⟩
      · simp only [hce, if_false]
        rw [hcls] at hce
        obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hce
        rw [hcls, hcost]
        exact ⟨h2', h1, h3, hW3 _ h _ R' (hAt.mono fun k hk => hk.1) hapP hc.good ⟨κ, hκ⟩ (uStep3_node hn.1)⟩
    · have hn : Node1Dg C crit h t := (Finset.mem_filter.1 (Finset.inr_mem_disjSum.1 htm)).2
      obtain ⟨h1, h2', h3⟩ := node1Dg_factsL H hS hp0 hP hP0 hExD hν hSrc hdec h0 (hA.mono Avine_sub) hn
        (fun k hk hr => hr.ext (hstep1RL_nodeg hn hk))
      have hcls : clsAtPL2 C Un Fst crit L γ η w h A j = cls1D L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
          t.1 t.2.1 t.2.2.1 t.2.2.2 := by unfold clsAtPL2; rw [ht]
      have hpost : postAtPL2 C crit L γ η h j = post1Dg C crit h t := by unfold postAtPL2; rw [ht]
      have hcost : costAtPL2 C crit L γ η CA CN CD c d cP h j = (if PendQ C crit h t then cP h t else ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2)) := by
        unfold costAtPL2; rw [ht]
      rw [hpost]
      by_cases hce : clsAtPL2 C Un Fst crit L γ η w h A j = ∅
      · rw [hcls] at hce
        rw [hce] at h1
        simp only [hcls, hce, if_true, QS_empty]
        exact ⟨h2', h1, by simp, by simp⟩
      · simp only [hce, if_false]
        rw [hcls] at hce
        obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hce
        rw [hcls, hcost]
        by_cases hp : PendQ C crit h t
        · rw [if_pos hp]
          have hpp := hPend A h t R' hA hapP hc.good hp
          exact ⟨h2', h1, hpp.1, hpp.2⟩
        · rw [if_neg hp]
          refine ⟨h2', h1, h3 (fun K hK => hconn_of_not_pend hn hp hK), hW1D h t R' hapP hc.good hn hp⟩

end WaveTurbulence.GammaLow.FinalCount.H
