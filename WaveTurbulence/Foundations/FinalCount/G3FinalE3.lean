/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3FinalE2
/-! **FINALCOUNT-G3: `Prop95ConclE`**, the corrected conclusions of Prop 9.5 / TARGET `finalmol` for runs with
tame-atom erasures, and its proof (`HRunE.prop95E`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R R' : ℕ} {M₀ : Molecule V D₀}

/-- TARGET `subpro` (3), L2044: every atom of `M_sub` with a zero-gap triple is SG (hinge) or tame (`Tm`). -/
def DegenSGT (M₀ : Molecule V D₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (Tm : V → Prop) : Prop :=
  ∀ a ∈ M₀.atoms, ∀ x y, M₀.atom x = a → M₀.atom y = a → M₀.out x = false →
    M₀.out y = true → y ≠ M₀.mate x → Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .ZG →
    SGat M₀ L γ η w κ a ∨ Tm a

theorem Step5.epsLe {s s' : St.{u} V D₀} (h : Step5 s s') : EpsLe s s' := by
  cases h with
  | erase v _ _ _ => exact EpsLe.eraseSt s v

theorem InvE.noloop {t : ℕ} {h : HSt V D₀} (hI : InvE M₀ R t L γ η w κ h) :
    ∀ x, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x) := by
  obtain ⟨R', -, hg⟩ := hI.good
  exact hg.1.noloop

theorem step5_eps {s s' : St.{u} V D₀} (h : Step5 s s') {a : V} (ha : a ∈ s'.M.atoms) (hae : s'.cls a = .eps) :
    a ∈ s.M.atoms ∧ s.cls a = .eps := by
  cases h with
  | erase v _ _ _ => exact ⟨Finset.mem_of_mem_erase (Finset.mem_filter.1 ha).1, hae⟩

theorem HRunE.noTriple [Infinite V] {h₀ hf : HSt V D₀} {t : ℕ} (hr : HRunE L γ η w κ h₀ hf t)
    (hg : Good R' hf.s) : NoTripleBond hf.s.M := by
  obtain ⟨h₁, h₂, h₃, t₂, -, n1, a2, -, a3, -, a4, -⟩ := hr
  have e2 : EpsLe h₁.s h₂.s :=
    rtgE (P := fun _ h => EpsLe h₁.s h.s) (fun t h t' h' hs he => by
      rcases hs with ⟨rfl, hs⟩ | ⟨v, rfl, hs⟩
      · exact he.trans hs.step.epsLe
      · exact he.trans hs.step.epsLe) a2 (EpsLe.refl _)
  have e3 : EpsLe h₁.s h₃.s :=
    rtgH (P := fun h => EpsLe h₁.s h.s) (fun h h' hs he => he.trans hs.step.epsLe) a3 e2
  have e : EpsLe h₁.s hf.s :=
    rtgE (P := fun _ h => EpsLe h₁.s h.s) (fun t h t' h' hs he => by
      rcases hs with ⟨rfl, hs⟩ | ⟨v, rfl, hs⟩
      · exact he.trans hs.step.epsLe
      · exact he.trans hs.step.epsLe) a4 e3
  intro a ha b hb hab
  by_contra hcon
  push Not at hcon
  have hda : 3 ≤ hf.s.M.deg a := (hcon.trans' (le_refl _)).trans (bondsBetween_le_deg _ _ _)
  have hdb : 3 ≤ hf.s.M.deg b := by
    have : hf.s.M.bondsBetween a b = hf.s.M.bondsBetween b a := by
      unfold Molecule.bondsBetween
      simp only [Sym2.eq_swap]
    rw [this] at hcon
    exact hcon.trans (bondsBetween_le_deg _ _ _)
  have hea : hf.s.cls a = .eps := by
    by_contra hne; have := (hg.1.ab a ha hne).1; omega
  have heb : hf.s.cls b = .eps := by
    by_contra hne; have := (hg.1.ab b hb hne).1; omega
  obtain ⟨⟨a1, -⟩, ⟨b1, -⟩, hle⟩ := e a ha b hb hea heb
  exact absurd (hcon.trans hle) (by have := n1 a a1 b b1 hab; omega)

/-- `NoSGTriangle` at the end of an erasure run. -/
theorem HRunE.noSGTri [Infinite V] {h₀ hf : HSt V D₀} {t : ℕ} (hr : HRunE L γ η w κ h₀ hf t)
    (h0 : InvE M₀ R 0 L γ η w κ h₀) : NoSGTriangle L γ η w κ hf.s := by
  obtain ⟨h₁, h₂, h₃, t₂, a1, -, a2, n2, a3, -, a4, -⟩ := hr
  have i1 : InvE M₀ R 0 L γ η w κ h₁ :=
    rtgH (P := InvE M₀ R 0 L γ η w κ) (fun _ _ hs hI => hI.step1 hs) a1 h0
  have i2 : InvE M₀ R t₂ L γ η w κ h₂ :=
    rtgE (P := fun t h => InvE M₀ R t L γ η w κ h) (fun t h t' h' hs hI => by
      rcases hs with ⟨rfl, hs⟩ | ⟨v, rfl, hs⟩
      · exact hI.step2 hs
      · exact hI.step5 hs) a2 i1
  have k3 : InvE M₀ R t₂ L γ η w κ h₃ ∧ NoSGTriangle L γ η w κ h₃.s :=
    rtgH (P := fun h => InvE M₀ R t₂ L γ η w κ h ∧ NoSGTriangle L γ η w κ h.s) (fun h h' hs hP =>
      ⟨hP.1.step3 hs, hs.step.noSGTri hP.2 hP.1.noloop⟩) a3 ⟨i2, n2⟩
  exact (rtgE (P := fun t h => InvE M₀ R t L γ η w κ h ∧ NoSGTriangle L γ η w κ h.s)
    (fun t h t' h' hs hP => by
      rcases hs with ⟨rfl, hs⟩ | ⟨v, rfl, hs⟩
      · exact ⟨hP.1.step4 hs, hs.step.noSGTri hP.2 hP.1.noloop⟩
      · refine ⟨hP.1.step5 hs, ?_⟩
        cases hs with
        | erase _ v _ _ _ _ => exact hP.2.eraseSt v) a4 k3).2

/-- `ε`-atoms of the end of phase 4 were `ε`-atoms at its start. -/
theorem HRunE.eps_back {h₃ hf : HSt V D₀} {t₂ t : ℕ}
    (a4 : Relation.ReflTransGen (StepE4 L w κ) (t₂, h₃) (t, hf)) :
    ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → a ∈ h₃.s.M.atoms ∧ h₃.s.cls a = .eps := by
  have key : ∀ {p q : ℕ × HSt V D₀}, Relation.ReflTransGen (StepE4 L w κ) p q →
      ∀ a ∈ q.2.s.M.atoms, q.2.s.cls a = .eps → a ∈ p.2.s.M.atoms ∧ p.2.s.cls a = .eps := by
    intro p q h
    induction h with
    | refl => exact fun a ha hae => ⟨ha, hae⟩
    | tail hab hbc ih =>
      intro a ha hae
      rename_i b c
      have : a ∈ b.2.s.M.atoms ∧ b.2.s.cls a = .eps := by
        rcases hbc with ⟨-, hs⟩ | ⟨v, -, hs⟩
        · exact step4_eps hs.step ha hae
        · exact step5_eps hs.step ha hae
      exact ih a this.1 this.2
  exact key a4

end WaveTurbulence.FinalCountG3
