/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase3d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase3c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmPhase3d`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, phase 3: the cover theorem** `phase3_cover`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The phase-3 nodes whose cut pair is designated (`HStep3C`). -/
noncomputable def nodes3D [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (h : HSt V D₀) : Finset (T3 h) :=
  (nodes3 L γ η h).filter fun t => Desig C (h.anc t.1) (h.s.pr t.2.1 t.2.2.1)

noncomputable def nodeAt3 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) : Option (T3 h) :=
  if hj : j < (nodes3D C L γ η h).card then some (((nodes3D C L γ η h).equivFin.symm ⟨j, hj⟩ : nodes3D C L γ η h) : T3 h) else none

noncomputable def clsAt3 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) :
    Set (D₀ → (Fin d → ℤ)) :=
  match nodeAt3 C L γ η h j with
  | some t => cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2
  | none => ∅

noncomputable def postAt3 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) : HSt V D₀ :=
  match nodeAt3 C L γ η h j with
  | some t => post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
  | none => h

noncomputable def costAt3 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (c : ℕ) (d' : ℕ) (h : HSt V D₀) (j : ℕ) : ℝ≥0∞ :=
  match nodeAt3 C L γ η h j with
  | some t => ENNReal.ofReal (max (cAlpha d' γ η) (cBeta η c) *
      stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1))
  | none => 0

/-- **Phase 3 cover theorem.** -/
theorem phase3_cover [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} (H : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hobl : ∀ κ ∈ A0, SubproOblG C L γ η w κ)
    (hRA : ∀ κ h, Rch κ h → Relation.ReflTransGen (HAny L γ η w κ) (HSt.init M₀) h)
    (hext : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D) (z : ℤ) (b : Bool) (a : V) (sg : Bool),
      Node3 L γ η h v x₁ x₂ z b a sg → Desig C (h.anc v) (h.s.pr x₁ x₂) → ∀ k ∈ cls3 L γ η w h A x₁ x₂ z b a sg,
        Rch k h → Rch k (post3 h v x₁ x₂ z b))
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h2 : 2 / L ≤ L ^ (-γ + η)) (N : ℕ)
    (hN : (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
      ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) + 1 ≤ N) (W : HSt V D₀ → ℝ≥0∞)
    (hW : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀), Inv3 M₀ Rn Rch L w A0 A h →
      ApPos h.s → Inv Rn h.s →
      UStep3 L γ η w (fun k => k ∈ A) h h' →
      (N : ℝ≥0∞) * (ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') * W h') ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv3 M₀ Rn Rch L w A0 A h →
      (∀ k ∈ A, NoSGLeft L γ η w k (HSt.init M₀).s h.s) → (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3 M₀ Rn Rch L w A0 A h → QS L γ δ C₁ w P h A ≤ W h := by
  have hηγ : η ≤ γ := by have := H.hη; have := H.hη1; linarith
  refine cover_induction2 (ι := ℕ) (fun a b : HSt V D₀ => epsCount a.s < epsCount b.s)
    (InvImage.wf (fun h : HSt V D₀ => epsCount h.s) wellFounded_lt)
    (fun h A => Inv3 M₀ Rn Rch L w A0 A h) (fun h A => ∀ k ∈ A, NoSGLeft L γ η w k (HSt.init M₀).s h.s)
    (QS L γ δ C₁ w P) W N
    (by omega) (fun h A B hAB => QS_mono L γ δ C₁ w P h hAB) (fun h A B => QS_union L γ δ C₁ w P h A B)
    (fun h => QS_empty L γ δ C₁ w P h) (fun h A => hfin A h) ?_
  intro h A hA _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ NoSGLeft L γ η w k (HSt.init M₀).s h.s}
  have hAfin : Inv3 M₀ Rn Rch L w A0 Afin h := hA.mono fun k hk => hk.1
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => h, fun _ => 0, hAfin, fun k hk => hk.2, ?_, (by simp; omega), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  have hc : UCtx M₀ Rn (fun k => k ∈ A) L w h := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hcardA : h.s.M.atoms.card ≤ 2 * M₀.atoms.card := UCtx.card_atoms_le hS hc
  have hcardD : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
  have hcard : (nodes3D C L γ η h).card ≤ (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
      ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) := by
    refine (Finset.card_filter_le _ _).trans ((nodes3_card L γ η h).trans ?_)
    gcongr
  have hmem : ∀ j t, nodeAt3 C L γ η h j = some t → t ∈ nodes3D C L γ η h := by
    intro j t ht
    unfold nodeAt3 at ht
    split_ifs at ht with hj
    · cases ht; exact ((nodes3D C L γ η h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ nodes3D C L γ η h, ∃ j, nodeAt3 C L γ η h j = some t := by
    intro t ht
    refine ⟨((nodes3D C L γ η h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold nodeAt3
    rw [dif_pos ((nodes3D C L γ η h).equivFin ⟨t, ht⟩).2]
    simp
  refine ⟨Afin, Finset.range (nodes3D C L γ η h).card, clsAt3 C L γ η w h A, postAt3 C L γ η h, costAt3 C L γ η c d h, hAfin,
    fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : NoSGLeft L γ η w k (HSt.init M₀).s h.s
    · exact Or.inl ⟨hk, hnb⟩
    · right
      obtain ⟨t, ht, hdt, hkt⟩ := phase3_cover_mem hS hobl h0 hRA H.hL hηγ h2 hA hAe hk hnb
      have ht : t ∈ nodes3D C L γ η h := Finset.mem_filter.2 ⟨ht, hdt⟩
      obtain ⟨j, hj⟩ := hsurj t ht
      have hjS : j ∈ Finset.range (nodes3D C L γ η h).card := by
        unfold nodeAt3 at hj
        by_contra hnot
        rw [dif_neg (by simpa using hnot)] at hj
        cases hj
      refine Set.mem_iUnion₂.2 ⟨j, hjS, ?_⟩
      unfold clsAt3
      rw [hj]
      exact hkt
  · simp only [Finset.card_range]; omega
  · intro j hjS
    have hj : j < (nodes3D C L γ η h).card := Finset.mem_range.1 hjS
    obtain ⟨t, ht⟩ : ∃ t, nodeAt3 C L γ η h j = some t := ⟨_, by unfold nodeAt3; rw [dif_pos hj]⟩
    have htm := hmem j t ht
    have hnd : Node3 L γ η h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 htm).1).2
    have hdes := (Finset.mem_filter.1 htm).2
    obtain ⟨h1, h2', h3⟩ := node3_facts H hS hp0 hP hP0 c hnc hA hnd (hext A h _ _ _ _ _ _ _ hnd hdes)
    have hcls : clsAt3 C L γ η w h A j = cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 := by
      unfold clsAt3; rw [ht]
    have hpost : postAt3 C L γ η h j = post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 := by unfold postAt3; rw [ht]
    have hcost : costAt3 C L γ η c d h j = ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) *
        stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)) := by unfold costAt3; rw [ht]
    rw [hcls, hpost, hcost]
    exact ⟨h2', h1, h3, hW _ h _ (hA.mono fun k hk => hk.1) hapP hc.good.1 (uStep3_node hnd)⟩

end WaveTurbulence.GammaLow.FinalCount.H
