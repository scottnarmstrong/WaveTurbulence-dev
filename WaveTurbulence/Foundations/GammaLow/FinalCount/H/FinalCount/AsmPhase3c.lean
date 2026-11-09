/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase3c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmPhase3c`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, phase 3: the cover theorem** (copy of `phase4_cover` with the node data of `AsmPhase3b`).  Coverage of a decoration
that is not stuck uses `exists_step3C`, the dyadic label `label_zrange` and the alive hit `AliveHitK`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem invE_of_reach {M₀ : Molecule V D₀} {Rn : ℕ} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} (hS : SubHyp Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Relation.ReflTransGen (HAny L γ η w κ) (HSt.init M₀) h) : InvE M₀ Rn 0 L γ η w κ h :=
  rtgH (S := HAny L γ η w κ) (P := InvE M₀ Rn 0 L γ η w κ)
    (fun _ _ hs hI => by rcases hs with hs | hs | hs | hs; exacts [hI.step1L hs, hI.step2 hs, hI.step3 hs, hI.step4 hs]) hr
    (InvE.init hS h0)

/-- **A decoration that is not stuck lies in a node class** (phase 3). -/
theorem phase3_cover_mem [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η : ℝ} {w : Mom d} {A0 A : Set (D₀ → (Fin d → ℤ))}
    {C : CollData M₀} (hS : SubHyp Rn M₀) (hobl : ∀ κ ∈ A0, SubproOblG C L γ η w κ)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hRA : ∀ κ h, Rch κ h → Relation.ReflTransGen (HAny L γ η w κ) (HSt.init M₀) h)
    (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ) (h2 : 2 / L ≤ L ^ (-γ + η))
    {h : HSt V D₀} (hA : Inv3 M₀ Rn Rch L w A0 A h) (hAe : A ≠ ∅) {κ : D₀ → (Fin d → ℤ)} (hκ : κ ∈ A)
    (hnb : ¬ NoSGLeft L γ η w κ (HSt.init M₀).s h.s) :
    ∃ t ∈ nodes3 L γ η h, Desig C (h.anc t.1) (h.s.pr t.2.1 t.2.2.1) ∧
      κ ∈ cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 := by
  obtain ⟨hc, hap, hr⟩ := hA.2.resolve_left hAe
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hIE := invE_of_reach hS (h0 κ (hA.1 hκ)) (hRA κ h (hr κ hκ))
  unfold NoSGLeft at hnb
  push Not at hnb
  obtain ⟨v, hv, hε, hSG⟩ := hnb
  obtain ⟨h', hs'⟩ := exists_step3C (hobl κ (hA.1 hκ)) hL h2 hIE hc.anc hv hε hSG
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
