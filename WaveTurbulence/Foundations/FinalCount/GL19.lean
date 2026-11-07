/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL18
public import WaveTurbulence.Foundations.FinalCount.Prop95Statement
/-! **G3-LOWDEG (R48), part 19: `FinalStructM` and `Prop95ConclAtL`** (the form consumed by the ported `FinalShape`/`FinalDec`
mapping, `GM01..GM17`).  `FinalStructM` = `FinalStructL` plus the two derived facts used by the shape lemmas: non-`ε` atoms are
`α`/`β` (ghost-free), and for `R = 1` all odd-degree atoms lie in one component.  `Prop95ConclAtL` = `Prop95ConclAt` with `FinalStructM`
and with the balance field `BalS` (`α`/`β`-atoms only) and the chains clause carrying the `ε`-degree `≥ 3` hypothesis of the component. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

structure FinalStructM (R : ℕ) (s : St.{u} V D₀) : Prop extends FinalStructL R s where
  ab_cls : ∀ a ∈ s.M.atoms, s.cls a ≠ .eps → (∃ ρ kp, s.cls a = .alpha ρ kp) ∨ s.cls a = .beta
  odd_comp : R = 1 → ∀ a ∈ s.M.atoms, ∀ b ∈ s.M.atoms, ¬ Even (s.M.deg a) → ¬ Even (s.M.deg b) →
    s.M.SameComponent a b

theorem FinalStructM.of_L {s : St.{u} V D₀} (F : FinalStructL R s) (hghost : ∀ a ∈ s.M.atoms, s.cls a ≠ .ghost) :
    FinalStructM R s where
  toFinalStructL := F
  ab_cls := by
    intro a ha hne
    rcases hc : s.cls a with _ | ⟨ρ, kp⟩ | _ | _
    · exact absurd hc hne
    · exact Or.inl ⟨ρ, kp, rfl⟩
    · exact Or.inr rfl
    · exact absurd hc (hghost a ha)
  odd_comp := by
    rintro rfl a ha b hb hoa hob
    obtain ⟨reps, _, hcard, hcov⟩ := F.imperfect
    have hnz : ∀ x ∈ s.M.atoms, ¬ Even (s.M.deg x) → contrib s x ≠ 0 := by
      intro x hx hodd h0
      apply hodd
      unfold contrib at h0
      have h1 : (s.cls x).base = (s.M.deg x : ℤ) := by linarith
      have h2 : Even (s.cls x).base := by
        rcases hc : s.cls x <;> simp [Cls.base] <;> decide
      rw [h1] at h2
      exact (Int.even_coe_nat _).mp h2
    obtain ⟨ra, hra, hara⟩ := hcov a ha ⟨a, ha, Relation.EqvGen.refl _, hnz a ha hoa⟩
    obtain ⟨rb, hrb, hbrb⟩ := hcov b hb ⟨b, hb, Relation.EqvGen.refl _, hnz b hb hob⟩
    have : ra = rb := Finset.card_le_one.1 hcard ra hra rb hrb
    subst this
    exact Relation.EqvGen.trans _ _ _ hara (Relation.EqvGen.symm _ _ hbrb)

/-- The conclusion of the LOW run in the form consumed by the ported `FinalShape` mapping (cf. `Prop95ConclAt`). -/
structure Prop95ConclAtL (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (R : ℕ) (hf : HSt V D₀) (Tm : V → Prop) : Prop where
  struct : FinalStructM R hf.s
  label : ∀ a ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls a = .alpha ρ kp → IsLabel L γ η ρ ∧ (kp = 0 ∨ kp = 50) ∧
    ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true →
      y ≠ hf.s.M.mate x → GapSim L w (κ ∘ hf.s.down) x y ρ
  eps_LG : ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → TameFree hf Tm a → ∀ x y : hf.s.D, hf.s.M.atom x = a →
    hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
    Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .LG
  no_triple : NoTripleBond hf.s.M
  cycles : ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → (∀ b ∈ compAtoms hf.s.M a, hf.s.cls b ≠ .eps) →
    CycleShape hf.s a
  chains : ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → hf.s.cls a ≠ .eps → (∃ b ∈ compAtoms hf.s.M a, hf.s.cls b = .eps) →
    TameFree hf Tm a → (∀ e ∈ compAtoms hf.s.M a, hf.s.cls e = .eps → 3 ≤ hf.s.M.deg e) → ChainEnds hf.s a
  bal : BalS hf.s
  noloop : ∀ x : hf.s.D, hf.s.M.atom x ≠ hf.s.M.atom (hf.s.M.mate x)
  alpha_sg : ∀ b ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls b = .alpha ρ kp → ∀ x y : hf.s.D, hf.s.M.atom x = b →
    hf.s.M.atom y = b → hf.s.M.out x = false → hf.s.M.out y = true →
    Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .SG
  dartGap : ∀ a ∈ hf.s.M.atoms, hf.s.cls a ≠ .eps → ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a →
    hf.s.M.out x = false → hf.s.M.out y = true → ∃ g, AtomGap L w κ hf a g ∧
      (Molecule.gapAt L w (κ ∘ hf.s.down) x y = g ∨ Molecule.gapAt L w (κ ∘ hf.s.down) x y = -g)
  noBetaCut : NoBetaCut L w κ hf.s
  N1 : ∀ b ∈ hf.s.M.atoms, hf.s.cls b = .beta → ∃ g, AtomGap L w κ hf b g ∧ g ≠ 0
  N2 : 1 ≤ L → 0 ≤ η → ∀ v₁ ∈ hf.s.M.atoms, ∀ v₂ ∈ hf.s.M.atoms, ∀ b ∈ hf.s.M.atoms, ∀ R₁ R₂ : ℝ,
    hf.s.cls v₁ = .alpha R₁ 0 → hf.s.cls v₂ = .alpha R₂ 0 → hf.s.cls b = .beta →
    ∀ g₁ g₂ gb : Mom d, AtomGap L w κ hf v₁ g₁ → AtomGap L w κ hf v₂ g₂ → AtomGap L w κ hf b gb →
    ∀ s₁ s₂ : ℝ, (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) → gb = s₁ • g₁ + s₂ • g₂ →
    L ^ (-50 * η) * min R₁ R₂ ≤ ‖gb‖

/-- The component of `a₀` has no low-degree `ε`-atom. -/
def LowFree (hf : HSt V D₀) (a₀ : V) : Prop := ∀ e ∈ compAtoms hf.s.M a₀, hf.s.cls e = .eps → 3 ≤ hf.s.M.deg e

/-- **`Prop95ConclL` ⇒ `Prop95ConclAtL`** (given the ghost-freeness of the final state). -/
theorem Prop95ConclL.toAtL {Tm : V → Prop} {hf : HSt V D₀} (h : Prop95ConclL L γ η w κ Tm R hf)
    (hghost : ∀ a ∈ hf.s.M.atoms, hf.s.cls a ≠ .ghost) : Prop95ConclAtL L γ η w κ R hf Tm where
  struct := FinalStructM.of_L h.struct hghost
  label := h.label
  eps_LG := fun a ha hae hT => (h.eps_LG a ha hae).resolve_left (hT a ha (Relation.EqvGen.refl _) hae)
  no_triple := h.no_triple
  cycles := h.cycles
  chains := fun a ha hev hne hex hT h3 => h.chains a ha hev hne hex
    (fun e he hce => ⟨hT e (Finset.mem_filter.1 he).1 (Finset.mem_filter.1 he).2 hce, h3 e he hce⟩)
  bal := h.bal
  noloop := h.noloop
  alpha_sg := h.alpha_sg
  dartGap := h.dartGap
  noBetaCut := h.noBetaCut
  N1 := h.N1
  N2 := h.N2

end WaveTurbulence.FinalCountG3
