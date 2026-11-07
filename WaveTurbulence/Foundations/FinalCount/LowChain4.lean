/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain3
/-! **FINALCOUNT LOW-CHAIN, LC-1 (4): the LOW class invariant `Inv3L` and the per-decoration invariants along the reach relations.**
`Inv3L` is `Inv3` with `UCtx M₀ Rn` replaced by `∃ R' ≤ Rn, UCtx M₀ R'` (the index drops along D1/D3 steps).  For a decoration `κ` reaching
`h` the invariant `InvL M₀ R'` (G3-LOWDEG GL3: `good`, `hrec`, `gap`, `comp`, `bal`, `rel`) holds with some `R' ≤ Rn`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The class invariant of the LOW cover: `Inv3` with an index `R' ≤ Rn`. -/
def Inv3L (M₀ : Molecule V D₀) (Rn : ℕ) (Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop) (L : ℝ) (w : Mom d)
    (A0 A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) : Prop :=
  A ⊆ A0 ∧ (A = ∅ ∨ ((∃ R', R' ≤ Rn ∧ UCtx M₀ R' (fun k => k ∈ A) L w h) ∧ ApPos h.s ∧ ∀ κ ∈ A, Rch κ h))

theorem Inv3L.mono {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L : ℝ} {w : Mom d}
    {A0 A B : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h) (hB : B ⊆ A) :
    Inv3L M₀ Rn Rch L w A0 B h := by
  refine ⟨hB.trans hA.1, ?_⟩
  by_cases hBe : B = ∅
  · exact Or.inl hBe
  · right
    rcases hA.2 with he | ⟨⟨R', hR', hc⟩, hap, hr⟩
    · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hB)) hBe
    · exact ⟨⟨R', hR', uctx_mono hc fun k hk => hB hk⟩, hap, fun κ hκ => hr κ (hB hκ)⟩

section inv
variable {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {L γ η : ℝ}
  {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {Rn : ℕ}

theorem invL_reach1 (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach1L C Un Fst L γ η w κ h) : ∃ R', R' ≤ Rn ∧ InvL M₀ R' L γ η w κ h :=
  HRunL.inv1 hr.toL (InvL.init hS h0)

/-- Generic closure of `∃ R' ≤ Rn, InvL` along a chain of steps each of which preserves it up to a smaller index. -/
theorem invL_chain {S : HSt V D₀ → HSt V D₀ → Prop}
    (hS : ∀ a b, S a b → ∀ R', InvL M₀ R' L γ η w κ a → ∃ R'', R'' ≤ R' ∧ InvL M₀ R'' L γ η w κ b)
    {a b : HSt V D₀} (hab : Relation.ReflTransGen S a b) (ha : ∃ R', R' ≤ Rn ∧ InvL M₀ R' L γ η w κ a) :
    ∃ R', R' ≤ Rn ∧ InvL M₀ R' L γ η w κ b := by
  induction hab with
  | refl => exact ha
  | tail _ hs ih =>
    obtain ⟨R', hR', hI⟩ := ih
    obtain ⟨R'', hR'', hI''⟩ := hS _ _ hs R' hI
    exact ⟨R'', hR''.trans hR', hI''⟩

theorem invL_D3 (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : ReachD3 C Un Fst L γ η w κ h) : ∃ R', R' ≤ Rn ∧ InvL M₀ R' L γ η w κ h := by
  obtain ⟨h₁, a, -, c⟩ := hr
  exact invL_chain (fun a b hs R' hI => hI.stepD3' hs) c (invL_reach1 hS h0 a)

theorem invL_reach2 (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach2L C Un Fst L γ η w κ h) : ∃ R', R' ≤ Rn ∧ InvL M₀ R' L γ η w κ h := by
  obtain ⟨h₁, h₂, a, -, c, -, e⟩ := hr
  exact invL_chain (fun a b hs R' hI => ⟨R', le_rfl, hI.step2 hs.toHStep2⟩) e
    (invL_chain (fun a b hs R' hI => hI.stepD3' hs) c (invL_reach1 hS h0 a))

theorem invL_reach3 (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach3L C Un Fst L γ η w κ h) : ∃ R', R' ≤ Rn ∧ InvL M₀ R' L γ η w κ h := by
  obtain ⟨h₁, h₂, h₃, a, -, c, -, e, -, g⟩ := hr
  exact invL_chain (fun a b hs R' hI => ⟨R', le_rfl, hI.step3 hs.toHStep3⟩) g
    (invL_chain (fun a b hs R' hI => ⟨R', le_rfl, hI.step2 hs.toHStep2⟩) e
      (invL_chain (fun a b hs R' hI => hI.stepD3' hs) c (invL_reach1 hS h0 a)))

theorem invL_reach4 (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach4L C Un Fst L γ η w κ h) : ∃ R', R' ≤ Rn ∧ InvL M₀ R' L γ η w κ h := by
  obtain ⟨h₁, h₂, h₃, h₄, a, -, c, -, e, -, g, -, j⟩ := hr
  exact invL_chain (fun a b hs R' hI => ⟨R', le_rfl, hI.step4 hs⟩) j
    (invL_chain (fun a b hs R' hI => ⟨R', le_rfl, hI.step3 hs.toHStep3⟩) g
      (invL_chain (fun a b hs R' hI => ⟨R', le_rfl, hI.step2 hs.toHStep2⟩) e
        (invL_chain (fun a b hs R' hI => hI.stepD3' hs) c (invL_reach1 hS h0 a))))

end inv

end WaveTurbulence.FinalCountAsm
