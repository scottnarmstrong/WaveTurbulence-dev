/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase1c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1b
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmPhase1c`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, phase 1: triple-bond cuts (R37(b), `HStep1C.triple`).**  A triple node is a phase-3 cut node (`Node3`, `cls3`, `post3`)
together with the state-level conditions of `HStep1C.triple`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The state-level conditions of `HStep1C.triple`. -/
def TripleCond {M₀ : Molecule V D₀} (C : CollData M₀) (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D) : Prop :=
  h.anc v ∈ C.hinges ∧ Desig C (h.anc v) (h.s.pr x₁ x₂) ∧
    ∃ u : V, u ≠ v ∧ 3 ≤ h.s.M.bondsBetween v u ∧ h.s.M.atom (h.s.M.mate x₁) = u ∧ h.s.M.atom (h.s.M.mate x₂) = u

def NodeT [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (h : HSt V D₀) (t : T3 h) : Prop :=
  Node3 L γ η h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 ∧ TripleCond C h t.1 t.2.1 t.2.2.1

noncomputable def nodesT [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (h : HSt V D₀) : Finset (T3 h) :=
  (nodes3 L γ η h).filter fun t => TripleCond C h t.1 t.2.1 t.2.2.1

theorem nodesT_card_le [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (h : HSt V D₀) :
    (nodesT C L γ η h).card ≤ (nodes3 L γ η h).card := Finset.card_filter_le _ _

theorem mem_nodesT [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {h : HSt V D₀} {t : T3 h} :
    t ∈ nodesT C L γ η h ↔ t ∈ nodes3 L γ η h ∧ TripleCond C h t.1 t.2.1 t.2.2.1 := by
  unfold nodesT; rw [Finset.mem_filter]

/-- A triple node's post state has no more components than its pre state. -/
theorem post3_F_le [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {h : HSt V D₀} {v : V} {x₁ x₂ : h.s.D} {z : ℤ}
    {b : Bool} {a : V} {sg : Bool} (hn : Node3 L γ η h v x₁ x₂ z b a sg) (hT : TripleCond C h v x₁ x₂) :
    (post3 h v x₁ x₂ z b).s.M.numComponents ≤ h.s.M.numComponents := by
  obtain ⟨hc, -⟩ := hn
  obtain ⟨-, -, u, hu, hb3, hm₁, hm₂⟩ := hT
  exact (isAlphaCut_iff h.s.M hc).2 (cut_sc_of_triple hc hu hb3 hm₁)

/-- `HStep1C.triple` on a decoration of a triple class. -/
theorem hstep1C_triple_both [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {w : Mom d} {h : HSt V D₀}
    {A : Set (D₀ → (Fin d → ℤ))} {v : V} {x₁ x₂ : h.s.D} {z : ℤ} {b : Bool} {a : V} {sg : Bool}
    (hn : Node3 L γ η h v x₁ x₂ z b a sg) (hT : TripleCond C h v x₁ x₂) {κ : D₀ → (Fin d → ℤ)}
    (hk : κ ∈ cls3 L γ η w h A x₁ x₂ z b a sg) :
    HStep1C C L γ η w κ h (post3 h v x₁ x₂ z b) ∧ HStep3C C L γ η w κ h (post3 h v x₁ x₂ z b) := by
  obtain ⟨hc, hε, h3, hR, ha, hb⟩ := hn
  obtain ⟨hhinge, hdes, u, hu, hb3, hm₁, hm₂⟩ := hT
  obtain ⟨-, hsg, hsim, hb1, hb0⟩ := hk
  have hkp : (if b then 50 else 0) = 0 ∨ (if b then 50 else 0) = 50 := by cases b <;> simp
  have hI : (if b then 50 else 0) = 50 ↔ IotaHit L η w κ h.alive (h.s.pr x₁ x₂) ((2 : ℝ) ^ z) := by
    constructor
    · intro h50
      have hb' : b = true := by cases b <;> simp_all
      obtain ⟨q, vis, hcr, hq⟩ := hb hb'
      have := hb1 hb'
      have hq' : qOf h a (h.s.pr x₁ x₂) = q := by simp [qOf, hcr]
      rw [hq'] at this
      exact ⟨q, HSt.mem_alive.2 ⟨hq, ⟨a, ha, vis, hcr⟩⟩, if sg then 1 else -1, by cases sg <;> simp, this.1, this.2⟩
    · intro hit
      by_contra hne
      have hb' : b = false := by cases b <;> simp_all
      exact hb0 hb' hit
  exact ⟨HStep1C.triple h v (fresh h) x₁ x₂ hc ((2 : ℝ) ^ z) (if b then 50 else 0) hR hkp hε hsg hsim hI h3 hdes hhinge u hu hb3 hm₁ hm₂,
    HStep3C.cut h v (fresh h) x₁ x₂ hc ((2 : ℝ) ^ z) (if b then 50 else 0) hR hkp hε hsg hsim hI h3 hdes⟩

/-- **Per-node facts of phase 1 (triple nodes)**: from `node3_facts`, with the reach relation of `HStep1C`. -/
theorem nodeT_facts [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    {A0 A : Set (D₀ → (Fin d → ℤ))} (H : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c) {h : HSt V D₀} (hA : Inv1 M₀ Rn C Un Fst L γ η w A0 A h)
    (hall : ∀ k ∈ A, ∀ U, Collected C (Un k) L γ η w k U → Dartless U h) {t : T3 h}
    (hn : NodeT C L γ η h t) :
    Inv1 M₀ Rn C Un Fst L γ η w A0 (cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2)
      (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) ∧
    epsCount (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1).s < epsCount h.s ∧
    QS L γ δ C₁ w P h (cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) ≤
      ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)) *
        QS L γ δ C₁ w P (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)
          (cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) := by
  exact node3_facts H hS hp0 hP hP0 c hnc hA hn.1
    (fun k hk hr => hr.tail (by
      have hb := hstep1C_triple_both hn.1 hn.2 hk
      exact HStep1R.triple h _ hb.1 hb.2 (hall k hk.1) (post3_F_le hn.1 hn.2)))

end WaveTurbulence.GammaLow.FinalCount.H
