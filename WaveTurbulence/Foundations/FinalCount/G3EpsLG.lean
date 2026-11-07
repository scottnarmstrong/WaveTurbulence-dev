/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3RelRun
/-! **FINALCOUNT-G3**: "any `ε`-atom in `𝕄_fin` must be LG in the decoration" (DH23 Prop 9.5, L1809--L1810). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- DH23 Prop 9.1 (c),(d): every degenerate (zero-gap) atom of `M_sub` is a hinge atom, and a hinge atom is SG; i.e. an
atom of `M_sub` with a zero-gap triple is SG. -/
def DegenSG (M₀ : Molecule V D₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : Prop :=
  ∀ a ∈ M₀.atoms, ∀ x y, M₀.atom x = a → M₀.atom y = a → M₀.out x = false →
    M₀.out y = true → y ≠ M₀.mate x → Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .ZG →
    SGat M₀ L γ η w κ a

/-- Step 4 only cuts `ε`-atoms: an `ε`-atom of the end is an `ε`-atom of the start. -/
theorem step4_eps {s s' : St.{u} V D₀} (h : Step4 s s') {a : V} (ha : a ∈ s'.M.atoms) (hae : s'.cls a = .eps) :
    a ∈ s.M.atoms ∧ s.cls a = .eps := by
  cases h with
  | cut v v₂ x₁ x₂ hcd hε hβ h3 =>
    have ha' : a ∈ insert v₂ s.M.atoms := ha
    have hne2 : a ≠ v₂ := by
      rintro rfl; rw [cutSt_cls_v₂] at hae; exact absurd hae (by simp)
    have hv₂ : v₂ ≠ v := fun e => hcd.2.1 (e ▸ hcd.1)
    have hnev : a ≠ v := by
      rintro rfl; rw [cutSt_cls_v _ _ hv₂] at hae; exact absurd hae (by simp)
    exact ⟨(Finset.mem_insert.1 ha').resolve_left hne2, by rwa [cutSt_cls_other _ _ hnev hne2] at hae⟩

theorem step4_rtg_eps {s s' : St.{u} V D₀} (h : Relation.ReflTransGen Step4 s s') {a : V} (ha : a ∈ s'.M.atoms)
    (hae : s'.cls a = .eps) : a ∈ s.M.atoms ∧ s.cls a = .eps := by
  induction h with
  | refl => exact ⟨ha, hae⟩
  | tail _ hs ih =>
    obtain ⟨h1, h2⟩ := step4_eps hs ha hae
    exact ih h1 h2

variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- **"Any `ε`-atom in `𝕄_fin` must be LG in the decoration"** (DH23 Prop 9.5, L1809). -/
theorem Run.eps_LG {sf : St.{u} V D₀} (hr : Run L γ η w κ (St.init M₀) sf) (hS : SubHyp R M₀)
    (hdeg : DegenSG M₀ L γ η w κ) :
    ∀ a ∈ sf.M.atoms, sf.cls a = .eps → ∀ x y : sf.D, sf.M.atom x = a → sf.M.atom y = a →
      sf.M.out x = false → sf.M.out y = true → y ≠ sf.M.mate x →
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ sf.down) x y) = .LG := by
  intro a ha hae x y hx hy hox hoy hxy
  have hrel := hr.dartRel
  obtain ⟨s₁, s₂, s₃, _, _, _, _, _, hsg, h4, _⟩ := hr
  obtain ⟨ha3, hae3⟩ := step4_rtg_eps h4 ha hae
  have hnsg : ¬ SGat M₀ L γ η w κ a := hsg a ha3 hae3
  have hx0 : M₀.atom (sf.down x) = a := by rw [hrel.eps x (by rw [hx]; exact hae), hx]
  have hy0 : M₀.atom (sf.down y) = a := by rw [hrel.eps y (by rw [hy]; exact hae), hy]
  have hox0 : M₀.out (sf.down x) = false := by rw [hrel.out]; exact hox
  have hoy0 : M₀.out (sf.down y) = true := by rw [hrel.out]; exact hoy
  have hxy0 : sf.down y ≠ M₀.mate (sf.down x) := by
    intro e
    have := hS.noloop (sf.down x)
    rw [← e, hx0, hy0] at this
    exact this rfl
  have haM : a ∈ M₀.atoms := hx0 ▸ M₀.atom_mem _
  have hgap : Molecule.gapAt L w (κ ∘ sf.down) x y = Molecule.gapAt L w κ (sf.down x) (sf.down y) := rfl
  rw [hgap]
  by_contra hne
  have hk : Molecule.gapKind L γ η (Molecule.gapAt L w κ (sf.down x) (sf.down y)) = .SG ∨
      Molecule.gapKind L γ η (Molecule.gapAt L w κ (sf.down x) (sf.down y)) = .ZG := by
    rcases hk : Molecule.gapKind L γ η (Molecule.gapAt L w κ (sf.down x) (sf.down y)) with _ | _ | _
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact absurd hk hne
  rcases hk with hk | hk
  · exact hnsg ⟨sf.down x, sf.down y, hx0, hy0, hox0, hoy0, hxy0, hk⟩
  · exact hnsg (hdeg a haM _ _ hx0 hy0 hox0 hoy0 hxy0 hk)


end WaveTurbulence.FinalCountG3
