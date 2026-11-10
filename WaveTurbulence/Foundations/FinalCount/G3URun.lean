/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3AdmRun
public import WaveTurbulence.Foundations.FinalCount.G3Init
public import WaveTurbulence.Foundations.FinalCount.G3RelRun
public import WaveTurbulence.Foundations.FinalCount.G3Run
/-! **FINALCOUNT-G3: runs for an admissible class** (`UReach`) and their invariants.

`UReach … h` : `h` is reached from `HSt.init M₀` by uniform steps (`UStep1..4`).  `UCtx` bundles the invariants used by
the per-step estimates: `Good` (degree bounds, atom count), `AncRel`, `DartRel`, and the charge relation `AtomRelU`.
For every `κ ∈ Adm0` a `UReach` state is `HStep`-reachable (`UStepk.hstep`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {M₀ : Molecule V D₀} {Rn : ℕ}

structure UCtx (M₀ : Molecule V D₀) (Rn : ℕ) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (L : ℝ) (w : Mom d)
    (h : HSt V D₀) : Prop where
  good : Good Rn h.s
  anc : AncRel M₀ h.s h.anc
  rel : DartRel M₀ h.s
  atom : AtomRelU Adm0 L w h

theorem UCtx.init (hS : SubHyp Rn M₀) : UCtx M₀ Rn Adm0 L w (HSt.init M₀) where
  good := ⟨hS.inv, St.init_clean M₀⟩
  anc := AncRel.init M₀
  rel := DartRel.init M₀
  atom := (AtomRelX.init (fun _ => False) M₀).toU

theorem UCtx.eps {h : HSt V D₀} (hc : UCtx M₀ Rn Adm0 L w h) (hp : PinnedM0 Adm0 L w M₀) : EpsPin Adm0 L w h :=
  epsPin_of_anc hc.anc hc.rel hp

theorem UCtx.step1 {h h' : HSt V D₀} {κ : D₀ → (Fin d → ℤ)} (hk : Adm0 κ) (hs : UStep1 L γ η w Adm0 h h')
    (hp : PinnedM0 Adm0 L w M₀) (hc : UCtx M₀ Rn Adm0 L w h) : UCtx M₀ Rn Adm0 L w h' := by
  have hh := hs.hstep hk
  refine ⟨hh.step.good hc.good, hh.anc hc.anc, hh.step.rel hc.rel, ?_⟩
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι hι0 hsg h3a h3b => exact hc.atom.step1 (hc.eps hp) K hu hl R kp

theorem UCtx.step2 {h h' : HSt V D₀} {κ : D₀ → (Fin d → ℤ)} (hk : Adm0 κ) (hs : UStep2 L γ η w Adm0 h h')
    (hp : PinnedM0 Adm0 L w M₀) (hc : UCtx M₀ Rn Adm0 L w h) : UCtx M₀ Rn Adm0 L w h' := by
  have hh := hs.hstep hk
  refine ⟨hh.step.good hc.good, hh.anc hc.anc, hh.step.rel hc.rel, ?_⟩
  cases hs with
  | tri T Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₀' hι₁ hι₁' h3 => exact hc.atom.step2 (hc.eps hp) T Q kp hcl

theorem UCtx.step3 {h h' : HSt V D₀} {κ : D₀ → (Fin d → ℤ)} (hk : Adm0 κ) (hs : UStep3 L γ η w Adm0 h h')
    (hp : PinnedM0 Adm0 L w M₀) (hc : UCtx M₀ Rn Adm0 L w h) : UCtx M₀ Rn Adm0 L w h' := by
  have hh := hs.hstep hk
  refine ⟨hh.step.good hc.good, hh.anc hc.anc, hh.step.rel hc.rel, ?_⟩
  cases hs with
  | cut v v₂ x₁ x₂ hcd R kp hR hkp hε hsg hsim hι hι' h3 => exact hc.atom.step3 (hc.eps hp) hcd hε R kp

theorem UCtx.step4 {h h' : HSt V D₀} {κ : D₀ → (Fin d → ℤ)} (hk : Adm0 κ) (hs : UStep4 L w Adm0 h h')
    (hp : PinnedM0 Adm0 L w M₀) (hc : UCtx M₀ Rn Adm0 L w h) : UCtx M₀ Rn Adm0 L w h' := by
  have hh := hs.hstep hk
  refine ⟨hh.step.good hc.good, hh.anc hc.anc, hh.step.rel hc.rel, ?_⟩
  cases hs with
  | cut v v₂ x₁ x₂ hcd hε hβ hnz h3 => exact hc.atom.step4 (hc.eps hp) hcd hε

/-- The number of atoms of a state is at most twice that of `M_sub` (`Σ base = |D| + 2R`, `base ≥ 2` on the
non-ghost atoms, `|D| ≤ |D₀|`, `|D₀| = 4n - 2R`). -/
theorem UCtx.card_atoms_le (hS : SubHyp Rn M₀) {h : HSt V D₀} (hc : UCtx M₀ Rn Adm0 L w h) :
    h.s.M.atoms.card ≤ 2 * M₀.atoms.card := by
  have hphi := hc.good.1.phi
  have hD : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
  have hD0 := card_darts_eq_two_bonds M₀
  have hcount := hS.count
  have hbase : ∀ a ∈ h.s.M.atoms, (2 : ℤ) ≤ (h.s.cls a).base := by
    intro a ha
    have hg := hc.good.2 a ha
    rcases hcls : h.s.cls a with _ | _ | _ | _
    · simp [Cls.base]
    · simp [Cls.base]
    · simp [Cls.base]
    · exact absurd hcls hg
  have hsum : (2 : ℤ) * h.s.M.atoms.card ≤ ∑ a ∈ h.s.M.atoms, (h.s.cls a).base := by
    have := Finset.card_nsmul_le_sum h.s.M.atoms (fun a => (h.s.cls a).base) 2 hbase
    simpa [mul_comm] using this
  have : ((h.s.M.atoms.card : ℕ) : ℤ) ≤ 2 * M₀.atoms.card := by
    have h1 : (Fintype.card h.s.D : ℤ) ≤ Fintype.card D₀ := by exact_mod_cast hD
    have h2 : (Fintype.card D₀ : ℤ) = 2 * M₀.bonds.card := by exact_mod_cast hD0
    have h3 : (M₀.bonds.card : ℤ) + Rn = 2 * M₀.atoms.card := by exact_mod_cast hcount
    omega
  exact_mod_cast this

end WaveTurbulence.FinalCountG3
