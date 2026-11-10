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

end WaveTurbulence.GammaLow.FinalCount.H
