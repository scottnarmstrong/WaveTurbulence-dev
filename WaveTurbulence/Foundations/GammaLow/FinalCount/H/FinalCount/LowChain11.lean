/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain11
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL16
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain11`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, LC-2 (7): the Step D3 phase cover `phaseD3_coverL`.**  Nodes `(v, x₁, x₂)` with `D3Data` and a designated pair; the class of a
node is `{κ ∈ A | pgap ≠ 0}`; the step is `UStepD3` (count unchanged: deviation `1`, `UStepD3.excess`, constant `excessRHS [] 1 2`); `epsCount` drops. -/
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

/-- The finite set of Step D3 nodes of `h`. -/
noncomputable def nodesD3 {M₀ : Molecule V D₀} (C : CollData M₀) (h : HSt V D₀) : Finset (V × h.s.D × h.s.D) :=
  (h.s.M.atoms ×ˢ ((Finset.univ : Finset h.s.D) ×ˢ (Finset.univ : Finset h.s.D))).filter fun t =>
    D3Data h t.1 t.2.1 t.2.2 ∧ Desig C (h.anc t.1) (h.s.pr t.2.1 t.2.2)

theorem nodesD3_card {M₀ : Molecule V D₀} (C : CollData M₀) (h : HSt V D₀) :
    (nodesD3 C h).card ≤ h.s.M.atoms.card * Fintype.card h.s.D * Fintype.card h.s.D := by
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_product, Finset.card_product]
  simp [mul_assoc]

noncomputable def nodeAtD3 {M₀ : Molecule V D₀} (C : CollData M₀) (h : HSt V D₀) (j : ℕ) : Option (V × h.s.D × h.s.D) :=
  if hj : j < (nodesD3 C h).card then some (((nodesD3 C h).equivFin.symm ⟨j, hj⟩ : nodesD3 C h) : V × h.s.D × h.s.D) else none

noncomputable def clsAtD3 {M₀ : Molecule V D₀} (C : CollData M₀) (L : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) :
    Set (D₀ → (Fin d → ℤ)) :=
  match nodeAtD3 C h j with
  | some t => clsD3 L w h A t.2.1 t.2.2
  | none => ∅

noncomputable def postAtD3 {M₀ : Molecule V D₀} (C : CollData M₀) (h : HSt V D₀) (j : ℕ) : HSt V D₀ :=
  match nodeAtD3 C h j with
  | some t => h.betaPost t.1 t.2.1 t.2.2
  | none => h

theorem uStepD3_node {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {w : Mom d} {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {v : V}
    {x₁ x₂ : h.s.D} (hn : D3Data h v x₁ x₂) (hdes : Desig C (h.anc v) (h.s.pr x₁ x₂)) :
    UStepD3 C L γ η w (fun k => k ∈ clsD3 L w h A x₁ x₂) h (h.betaPost v x₁ x₂) :=
  UStepD3.cut h v x₁ x₂ hn.hv hn.hε hn.hd hn.hx₁ hn.hx₂ hn.hne hn.ho₁ hn.ho₂ (fun k hk => hk.2) hdes

theorem nodeD3_factsL {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} (H : TriReal d L γ η δ C₁)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h)
    {v : V} {x₁ x₂ : h.s.D} (hn : D3Data h v x₁ x₂) (hdes : Desig C (h.anc v) (h.s.pr x₁ x₂))
    (hext : ∀ k ∈ clsD3 L w h A x₁ x₂, Rch k h → Rch k (h.betaPost v x₁ x₂)) :
    Inv3L M₀ Rn Rch L w A0 (clsD3 L w h A x₁ x₂) (h.betaPost v x₁ x₂) ∧
    epsCount (h.betaPost v x₁ x₂).s < epsCount h.s ∧
    QS L γ δ C₁ w P h (clsD3 L w h A x₁ x₂) ≤
      ENNReal.ofReal (excessRHS L γ η [] 1 2) * QS L γ δ C₁ w P (h.betaPost v x₁ x₂) (clsD3 L w h A x₁ x₂) := by
  have hsub : clsD3 L w h A x₁ x₂ ⊆ A := fun k hk => hk.1
  have hlt : epsCount (h.betaPost v x₁ x₂).s < epsCount h.s := epsCount_betaSt_lt h.s hn.hv hn.hε
  have hη0 : 0 ≤ η := H.hη.le
  have hη1 : η ≤ 1 := by have := H.hη1; have := H.hη; have := H.hγ1; linarith
  have hQ : QS L γ δ C₁ w P h (clsD3 L w h A x₁ x₂) ≤
      ENNReal.ofReal (excessRHS L γ η [] 1 2) * QS L γ δ C₁ w P (h.betaPost v x₁ x₂) (clsD3 L w h A x₁ x₂) := by
    have := (uStepD3_node (C := C) (L := L) (γ := γ) (η := η) (w := w) (A := A) hn hdes).excess δ C₁ P
      (le_trans (Real.one_le_exp (by norm_num)) H.hL) hη0 hη1
    unfold StepDev IsDeviation at this
    rw [one_mul] at this
    exact this
  by_cases hAe : clsD3 L w h A x₁ x₂ = ∅
  · exact ⟨⟨hsub.trans hA.1, Or.inl hAe⟩, hlt, hQ⟩
  rcases hA.2 with he | ⟨⟨R', hR', hc⟩, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hAe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hcc := uctx_mono hc (fun k (hk : k ∈ clsD3 L w h A x₁ x₂) => hk.1)
  have hst := uStepD3_node (C := C) (L := L) (γ := γ) (η := η) (w := w) (A := A) hn hdes
  obtain ⟨hR1, hc'⟩ := UCtx.stepD3L hκ hst hcc
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨⟨R' - 1, by omega, hc'⟩, apPos_betaSt hap v, fun k hk => hext k hk (hr k hk.1)⟩⟩, hlt, hQ⟩

/-- **The Step D3 phase cover theorem.** -/
theorem phaseD3_coverL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀)
    (hext : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D), D3Data h v x₁ x₂ →
      Desig C (h.anc v) (h.s.pr x₁ x₂) → ∀ k ∈ clsD3 L w h A x₁ x₂, Rch k h → Rch k (h.betaPost v x₁ x₂)) (N : ℕ)
    (hN : 2 * M₀.atoms.card * Fintype.card D₀ * Fintype.card D₀ + 1 ≤ N) (W : HSt V D₀ → ℝ≥0∞)
    (hW : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀) (R' : ℕ), Inv3L M₀ Rn Rch L w A0 A h →
      ApPos h.s → Good R' h.s → (∃ k, k ∈ A) →
      UStepD3 C L γ η w (fun k => k ∈ A) h h' →
      (N : ℝ≥0∞) * (ENNReal.ofReal (excessRHS L γ η [] 1 2) * W h') ≤ W h)
    (hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv3L M₀ Rn Rch L w A0 A h →
      (∀ k ∈ A, NoD3 C L w k h) → (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ W h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn Rch L w A0 A h → QS L γ δ C₁ w P h A ≤ W h := by
  refine cover_induction2 (ι := ℕ) (fun a b : HSt V D₀ => epsCount a.s < epsCount b.s)
    (InvImage.wf (fun h : HSt V D₀ => epsCount h.s) wellFounded_lt)
    (fun h A => Inv3L M₀ Rn Rch L w A0 A h) (fun h A => ∀ k ∈ A, NoD3 C L w k h) (QS L γ δ C₁ w P) W N
    (by omega) (fun h A B hAB => QS_mono L γ δ C₁ w P h hAB) (fun h A B => QS_union L γ δ C₁ w P h A B)
    (fun h => QS_empty L γ δ C₁ w P h) (fun h A => hfin A h) ?_
  intro h A hA _
  let Afin : Set (D₀ → (Fin d → ℤ)) := {k | k ∈ A ∧ NoD3 C L w k h}
  have hAfin : Inv3L M₀ Rn Rch L w A0 Afin h := hA.mono fun k hk => hk.1
  by_cases hAe : A = ∅
  · refine ⟨Afin, ∅, fun _ => ∅, fun _ => h, fun _ => 0, hAfin, fun k hk => hk.2, ?_, (by simp; omega), (by simp)⟩
    intro k hk; rw [hAe] at hk; exact absurd hk (by simp)
  obtain ⟨R', hR', hc⟩ := (hA.2.resolve_left hAe).1
  have hapP : ApPos h.s := (hA.2.resolve_left hAe).2.1
  have hcard : (nodesD3 C h).card ≤ 2 * M₀.atoms.card * Fintype.card D₀ * Fintype.card D₀ := by
    refine (nodesD3_card C h).trans ?_
    have h1 := card_atoms_leL_of_uctx hS hR' hc
    have h2 : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
    exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h2
  have hmem : ∀ j t, nodeAtD3 C h j = some t → t ∈ nodesD3 C h := by
    intro j t ht
    unfold nodeAtD3 at ht
    split_ifs at ht with hj
    · cases ht; exact ((nodesD3 C h).equivFin.symm ⟨j, hj⟩).2
  have hsurj : ∀ t ∈ nodesD3 C h, ∃ j, nodeAtD3 C h j = some t := by
    intro t ht
    refine ⟨((nodesD3 C h).equivFin ⟨t, ht⟩).1, ?_⟩
    unfold nodeAtD3
    rw [dif_pos ((nodesD3 C h).equivFin ⟨t, ht⟩).2]
    simp
  refine ⟨Afin, Finset.range (nodesD3 C h).card, clsAtD3 C L w h A, postAtD3 C h,
    (fun j => if clsAtD3 C L w h A j = ∅ then 0 else ENNReal.ofReal (excessRHS L γ η [] 1 2)), hAfin, fun k hk => hk.2, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hnb : NoD3 C L w k h
    · exact Or.inl ⟨hk, hnb⟩
    · right
      unfold NoD3 at hnb
      push Not at hnb
      obtain ⟨v, x₁, x₂, hD, hnz, hdes⟩ := hnb
      have hmt : (v, x₁, x₂) ∈ nodesD3 C h :=
        Finset.mem_filter.2 ⟨by simp [hD.hv], hD, hdes⟩
      obtain ⟨j, hj⟩ := hsurj _ hmt
      have hjS : j ∈ Finset.range (nodesD3 C h).card := by
        unfold nodeAtD3 at hj
        by_contra hnot
        rw [dif_neg (by simpa using hnot)] at hj
        cases hj
      refine Set.mem_iUnion₂.2 ⟨j, hjS, ?_⟩
      unfold clsAtD3
      rw [hj]
      exact ⟨hk, hnz⟩
  · simp only [Finset.card_range]; omega
  · intro j hjS
    have hj : j < (nodesD3 C h).card := Finset.mem_range.1 hjS
    obtain ⟨t, ht⟩ : ∃ t, nodeAtD3 C h j = some t := ⟨_, by unfold nodeAtD3; rw [dif_pos hj]⟩
    have htm := hmem j t ht
    have hnd : D3Data h t.1 t.2.1 t.2.2 := (Finset.mem_filter.1 htm).2.1
    have hdes : Desig C (h.anc t.1) (h.s.pr t.2.1 t.2.2) := (Finset.mem_filter.1 htm).2.2
    obtain ⟨h1, h2, h3⟩ := nodeD3_factsL H hp0 hA hnd hdes (hext A h _ _ _ hnd hdes)
    have hcls : clsAtD3 C L w h A j = clsD3 L w h A t.2.1 t.2.2 := by unfold clsAtD3; rw [ht]
    have hpost : postAtD3 C h j = h.betaPost t.1 t.2.1 t.2.2 := by unfold postAtD3; rw [ht]
    rw [hcls, hpost]
    by_cases hce : clsD3 L w h A t.2.1 t.2.2 = ∅
    · rw [hce] at h1
      simp only [hcls, hce, if_true, QS_empty]
      exact ⟨h2, h1, by simp, by simp⟩
    · simp only [hcls, hce, if_false]
      obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hce
      exact ⟨h2, h1, h3, hW _ h _ R' (hA.mono fun k hk => hk.1) hapP hc.good ⟨κ, hκ⟩ (uStepD3_node hnd hdes)⟩

end WaveTurbulence.GammaLow.FinalCount.H
