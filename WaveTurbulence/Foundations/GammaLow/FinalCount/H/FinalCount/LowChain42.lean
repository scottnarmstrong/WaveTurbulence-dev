/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain42
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain40
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain42`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, session 6 (16): helpers for the terminal assembly.**  `desig_deg2` (referee F1: at a degree-`2` `ε`-atom the only opposite
pair is designated, via `hinge_oriented`), `Reach4L.d3info` (the D3-stop state with `EpsLe` to the end of Step 4), `card_le_of_loops`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem desig_deg2 {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {hf : HSt V D₀}
    (obl : SubproOblG C L γ η w κ) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s) :
    ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → hf.s.M.deg a = 2 → ∀ x y : hf.s.D, hf.s.M.atom x = a →
      hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
      Desig C (hf.anc a) (hf.s.pr x y) := by
  intro a ha hε hdeg x y hxa hya hxo hyo hne
  have hanc : hf.anc a = a := hA.eps a ha hε
  intro hh
  rw [hanc] at hh
  obtain ⟨f, s, x', y', h1, h2, hx', hy', hne', ho1, ho2, hsg, hset⟩ := hinge_oriented obl hh
  refine ⟨f, s, by rw [hanc]; exact h1, by rw [hanc]; exact h2, Or.inl ?_⟩
  have hd0 : M₀.deg a = 2 := by rw [← deg_eps_eq hA ha hε]; exact hdeg
  have hxy' : x' ≠ y' := by intro e; rw [e] at ho1; rw [ho1] at ho2; exact absurd ho2 (by simp)
  have hsub : ({x', y'} : Finset D₀) ⊆ M₀.dartsAt a := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (Mole.mem_dartsAt M₀ a z).2 hx'
    · exact (Mole.mem_dartsAt M₀ a z).2 hy'
  have heq : M₀.dartsAt a = {x', y'} := by
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [Finset.card_pair hxy']
    unfold Molecule.deg at hd0; omega
  have hdx : M₀.atom (hf.s.down x) = a := by rw [hD.eps x (by rw [hxa]; exact hε), hxa]
  have hdy : M₀.atom (hf.s.down y) = a := by rw [hD.eps y (by rw [hya]; exact hε), hya]
  have hxm : hf.s.down x ∈ M₀.dartsAt a := (Mole.mem_dartsAt M₀ a _).2 hdx
  have hym : hf.s.down y ∈ M₀.dartsAt a := (Mole.mem_dartsAt M₀ a _).2 hdy
  rw [heq] at hxm hym
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxm hym
  have hox : M₀.out (hf.s.down x) = false := by rw [hD.out]; exact hxo
  have hoy : M₀.out (hf.s.down y) = true := by rw [hD.out]; exact hyo
  have ex : hf.s.down x = x' := by
    rcases hxm with h | h
    · exact h
    · rw [h] at hox; rw [hox] at ho2; exact absurd ho2 (by simp)
  have ey : hf.s.down y = y' := by
    rcases hym with h | h
    · rw [h] at hoy; rw [hoy] at ho1; exact absurd ho1 (by simp)
    · exact h
  show ({hf.s.down x, hf.s.down y} : Set D₀) = {f, s}
  rw [ex, ey]; exact hset

theorem Reach4L.d3info {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {Rn : ℕ} (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach4L C Un Fst L γ η w κ h) :
    ∃ h₂, NoD3 C L w κ h₂ ∧ AncRel M₀ h₂.s h₂.anc ∧ DartRel M₀ h₂.s ∧ EpsLe h₂.s h.s := by
  obtain ⟨h₁, h₂, h₃, h₄, a, -, c, n, e, -, g, -, j⟩ := hr
  obtain ⟨hA, hD⟩ := d3info_aux hS h0 a c
  refine ⟨h₂, n, hA, hD, ?_⟩
  have e2 : EpsLe h₂.s h₃.s :=
    rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.toHStep2.step.epsLe) e (EpsLe.refl _)
  have e3 : EpsLe h₂.s h₄.s :=
    rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.toHStep3.step.epsLe) g e2
  exact rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.step.epsLe) j e3

end WaveTurbulence.GammaLow.FinalCount.H
