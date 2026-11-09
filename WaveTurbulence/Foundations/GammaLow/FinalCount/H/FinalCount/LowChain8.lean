/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain8`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, LC-2 (4): phase 3 (SG cuts) in the LOW run: `Reach*L.d3info`, `phase3_cover_memL`, `node3_factsL`.** -/
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

section d3info
variable {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ}
  {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {Rn : ℕ}

theorem d3info_aux (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h₁ h₂ : HSt V D₀}
    (a : Reach1L C Un Fst L γ η w κ h₁) (c : Relation.ReflTransGen (HStepD3 C L γ η w κ) h₁ h₂) :
    AncRel M₀ h₂.s h₂.anc ∧ DartRel M₀ h₂.s := by
  have p1 : RunAux M₀ C h₁ := rtgH (P := fun h => RunAux M₀ C h) (fun _ _ hs hp => hs.aux hp) a.toL (RunAux.init C)
  have p2 : RunAux M₀ C h₂ := rtgH (P := fun h => RunAux M₀ C h) (fun _ _ hs hp => hs.aux hp) c p1
  obtain ⟨R', -, hI⟩ := invL_chain (fun _ _ hs R' hI => hI.stepD3'L hs) c (invL_reach1 hS h0 a)
  exact ⟨p2.2.1, hI.rel⟩

theorem Reach2L.d3info (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach2L C Un Fst L γ η w κ h) :
    ∃ h₂, NoD3 C L w κ h₂ ∧ AncRel M₀ h₂.s h₂.anc ∧ DartRel M₀ h₂.s ∧ EpsLe h₂.s h.s := by
  obtain ⟨h₁, h₂, a, -, c, n, e⟩ := hr
  obtain ⟨hA, hD⟩ := d3info_aux hS h0 a c
  refine ⟨h₂, n, hA, hD, ?_⟩
  exact rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.toHStep2.step.epsLe) e (EpsLe.refl _)

theorem Reach3L.d3info (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach3L C Un Fst L γ η w κ h) :
    ∃ h₂, NoD3 C L w κ h₂ ∧ AncRel M₀ h₂.s h₂.anc ∧ DartRel M₀ h₂.s ∧ EpsLe h₂.s h.s := by
  obtain ⟨h₁, h₂, h₃, a, -, c, n, e, -, g⟩ := hr
  obtain ⟨hA, hD⟩ := d3info_aux hS h0 a c
  refine ⟨h₂, n, hA, hD, ?_⟩
  have e2 : EpsLe h₂.s h₃.s :=
    rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.toHStep2.step.epsLe) e (EpsLe.refl _)
  exact rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.toHStep3.step.epsLe) g e2

end d3info

/-- **A decoration that is not stuck lies in a node class** (phase 3, LOW run). -/
theorem phase3_cover_memL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η : ℝ} {w : Mom d}
    {A0 A : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    (hS : SubHypL Rn M₀) (hobl : ∀ κ ∈ A0, SubproOblG C L γ η w κ)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hRA : ∀ κ h, Rch κ h → Reach3L C Un Fst L γ η w κ h)
    (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ) (h2 : 2 / L ≤ L ^ (-γ + η))
    {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h) (hAe : A ≠ ∅) {κ : D₀ → (Fin d → ℤ)} (hκ : κ ∈ A)
    (hnb : ¬ NoSGLeft L γ η w κ (HSt.init M₀).s h.s) :
    ∃ t ∈ nodes3 L γ η h, Desig C (h.anc t.1) (h.s.pr t.2.1 t.2.2.1) ∧
      κ ∈ cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 := by
  obtain ⟨⟨R', hR', hc⟩, hap, hr⟩ := hA.2.resolve_left hAe
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hreach := hRA κ h (hr κ hκ)
  obtain ⟨R'', -, hIL⟩ := invL_reach3 hS (h0 κ (hA.1 hκ)) hreach
  obtain ⟨h₂, hN, hA₂, hD₂, hE⟩ := hreach.d3info hS (h0 κ (hA.1 hκ))
  unfold NoSGLeft at hnb
  push Not at hnb
  obtain ⟨v, hv, hε, hSG⟩ := hnb
  have h3 : 3 ≤ h.s.M.deg v := deg_three_of_sg (hobl κ (hA.1 hκ)) hA₂ hD₂ hc.anc hIL.rel hE hN hv hε hSG
  obtain ⟨h', hs'⟩ := exists_step3C_L (hobl κ (hA.1 hκ)) hL h2 hIL hc.anc hv hε hSG h3
  cases hs' with
  | cut v' v₂ x₁ x₂ hcd R' kp hR hkp hε' hsg hsim hι h3 hdes =>
    obtain ⟨z, hRz, hz1, hz2⟩ := label_zrange hLe hηγ hR
    subst hRz
    have hcd' : h.s.M.IsCutData v' (fresh h) x₁ x₂ :=
      ⟨hcd.1, fresh_notMem h, hcd.2.2.1, hcd.2.2.2.1, hcd.2.2.2.2.1, hcd.2.2.2.2.2.1, hcd.2.2.2.2.2.2⟩
    by_cases hk50 : kp = 50
    · have hhit := hι.1 hk50
      obtain ⟨q, hq, ⟨a, ha, vis, hcr⟩, sg, hsgn, h1, h2'⟩ := iotaAlive_of_hit hhit
      refine ⟨(v', x₁, x₂, z, true, a, decide (sg = 1)), ?_, hdes, ?_⟩
      · refine Finset.mem_filter.2 ⟨?_, hcd', hε', h3, hR, ha, fun _ => ⟨q, vis, hcr, hq⟩⟩
        simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
        exact ⟨hcd.1, ⟨hz1, hz2⟩, ha, trivial⟩
      · have hq' : qOf h a (h.s.pr x₁ x₂) = q := by simp [qOf, hcr]
        have hsg' : (if decide (sg = 1) then (1 : ℝ) else -1) = sg := by
          rcases hsgn with rfl | rfl <;> norm_num
        refine ⟨hκ, hsg, hsim, fun _ => ?_, fun hb => by simp at hb⟩
        rw [hq', hsg']; exact ⟨h1, h2'⟩
    · have hk0 : ¬ IotaHit L η w κ h.alive (h.s.pr x₁ x₂) ((2 : ℝ) ^ z) := fun hh => hk50 (hι.2 hh)
      refine ⟨(v', x₁, x₂, z, false, v', true), ?_, hdes, ?_⟩
      · refine Finset.mem_filter.2 ⟨?_, hcd', hε', h3, hR, hcd.1, fun hb => by simp at hb⟩
        simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
        exact ⟨hcd.1, ⟨hz1, hz2⟩, hcd.1, trivial⟩
      · exact ⟨hκ, hsg, hsim, fun hb => by simp at hb, fun _ => hk0⟩


end WaveTurbulence.GammaLow.FinalCount.H
