/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.Prop95Statement
public import WaveTurbulence.Foundations.FinalCount.G3HRun
public import WaveTurbulence.Foundations.FinalCount.G3NoTriple
/-! **FINALCOUNT-G3: the proved fields of `Prop95Concl`** (`struct`, `label`, `eps_LG`, `N1`, `N2`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ}

/-- The proved part of Prop 9.5: all fields of `Prop95Concl` except `cycles`, `chains`. -/
structure Prop95Core (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (R : ℕ) (hf : HSt V D₀) : Prop where
  struct : FinalStruct R hf.s
  label : ∀ a ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls a = .alpha ρ kp → IsLabel L γ η ρ ∧ (kp = 0 ∨ kp = 50) ∧
    ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true →
      y ≠ hf.s.M.mate x → GapSim L w (κ ∘ hf.s.down) x y ρ
  eps_LG : ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a →
    hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
    Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .LG
  no_triple : NoTripleBond hf.s.M
  N1 : ∀ b ∈ hf.s.M.atoms, hf.s.cls b = .beta → ∃ g, AtomGap L w κ hf b g ∧ g ≠ 0
  N2 : 1 ≤ L → 0 ≤ η → ∀ v₁ ∈ hf.s.M.atoms, ∀ v₂ ∈ hf.s.M.atoms, ∀ b ∈ hf.s.M.atoms, ∀ R₁ R₂ : ℝ,
    hf.s.cls v₁ = .alpha R₁ 0 → hf.s.cls v₂ = .alpha R₂ 0 → hf.s.cls b = .beta →
    ∀ g₁ g₂ gb : Mom d, AtomGap L w κ hf v₁ g₁ → AtomGap L w κ hf v₂ g₂ → AtomGap L w κ hf b gb →
    ∀ s₁ s₂ : ℝ, (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) → gb = s₁ • g₁ + s₂ • g₂ →
    L ^ (-50 * η) * min R₁ R₂ ≤ ‖gb‖

theorem HRun.core {M₀ : Molecule V D₀} {hf : HSt V D₀} (hr : HRun L γ η w κ (HSt.init M₀) hf) (hS : SubHyp R M₀)
    (hdeg : DegenSG M₀ L γ η w κ)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    Prop95Core L γ η w κ R hf where
  struct := hr.toRun.finalStruct hS
  label := by
    intro a ha ρ kp hc
    have hI := (hr.runInv hS h0).hrec
    have hG := (hr.runInv hS h0).gap
    obtain ⟨hl, p, vis, hrec, hp, hkp, -, -⟩ := (hI.ok a ha).1 ρ kp hc
    refine ⟨hl, hkp, fun x y hx hy hox hoy _ => ?_⟩
    obtain ⟨p', vis', hrec', hn⟩ := hG.dg a ha (by rw [hc]; simp) x y hx hy hox hoy
    rw [hrec] at hrec'
    simp only [Option.some.injEq, Prod.mk.injEq] at hrec'
    obtain ⟨rfl, rfl⟩ := hrec'
    unfold GapSim
    rw [norm_gap_of_pm hn]
    exact hp
  eps_LG := hr.toRun.eps_LG hS hdeg
  no_triple := hr.toRun.noTriple (hr.runInv hS h0).good
  N1 := fun b hb hcb => (hr.runInv hS h0).hrec.N1 hb hcb
  N2 := fun hL hη v₁ h1 v₂ h2 b hb R₁ R₂ c1 c2 cb g₁ g₂ gb a1 a2 ab s₁ s₂ hs₁ hs₂ hsum =>
    (hr.runInv hS h0).hrec.N2 hL hη h1 h2 hb c1 c2 cb a1 a2 ab s₁ s₂ hs₁ hs₂ hsum

end WaveTurbulence.FinalCountG3
