/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmIntact
public import WaveTurbulence.Foundations.FinalCount.AsmPhase1d
public import WaveTurbulence.Foundations.FinalCount.AsmTopClass2
/-! **FINALCOUNT-ASSEMBLY (E1-E4): coverage `HmemAt`, triple-cut part.**  A decoration `κ` of the Step-1 phase for which every collected
object is dartless but a triple cut is still enabled (`¬ NoTripleCut`) lies in the class of a triple node (`nodesT`, `cls3` on `Atrip`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine.SourceVine


variable {V : Type*} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem hmem_triple {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {L γ η : ℝ}
    {w : Mom d} (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ) (h2 : 2 / L ≤ L ^ (-γ + η)) {A : Set (D₀ → (Fin d → ℤ))}
    {κ : D₀ → (Fin d → ℤ)} {h : HSt V D₀} (hκ : κ ∈ A)
    (hall : ∀ U, Collected C (Un κ) L γ η w κ U → Dartless U h) (hnt : ¬ NoTripleCut C L γ η w κ h) :
    ∃ t ∈ nodesT C L γ η h, κ ∈ cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1
      t.2.2.2.2.2.2 := by
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hκA : κ ∈ Atrip C Un L γ η w h A := ⟨hκ, hall⟩
  unfold NoTripleCut at hnt
  push Not at hnt
  obtain ⟨v, v₂, x₁, x₂, hcd0, hε', h3, hhinge, hdes, hu, hsg⟩ := hnt
  have hcd : h.s.M.IsCutData v (fresh h) x₁ x₂ :=
    ⟨hcd0.1, fresh_notMem h, hcd0.2.2.1, hcd0.2.2.2.1, hcd0.2.2.2.2.1, hcd0.2.2.2.2.2.1, hcd0.2.2.2.2.2.2⟩
  obtain ⟨R', hR, hsim⟩ := exists_label_of_SG w (κ ∘ h.s.down) x₁ x₂ hL h2 hsg
  obtain ⟨z, hRz, hz1, hz2⟩ := label_zrange hLe hηγ hR
  subst hRz
  have hT : TripleCond C h v x₁ x₂ := ⟨hhinge, hdes, hu⟩
  by_cases hI : IotaHit L η w κ h.alive (h.s.pr x₁ x₂) ((2 : ℝ) ^ z)
  · obtain ⟨q, hq, ⟨a, ha, vis, hcr⟩, sg, hsgn, h1, h2'⟩ := iotaAlive_of_hit hI
    refine ⟨(v, x₁, x₂, z, true, a, decide (sg = 1)), ?_, ?_⟩
    · refine mem_nodesT.2 ⟨Finset.mem_filter.2 ⟨?_, hcd, hε', h3, hR, ha, fun _ => ⟨q, vis, hcr, hq⟩⟩, hT⟩
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
      exact ⟨hcd0.1, ⟨hz1, hz2⟩, ha, trivial⟩
    · have hq' : qOf h a (h.s.pr x₁ x₂) = q := by simp [qOf, hcr]
      have hsg' : (if decide (sg = 1) then (1 : ℝ) else -1) = sg := by
        rcases hsgn with rfl | rfl <;> norm_num
      refine ⟨hκA, hsg, hsim, fun _ => ?_, fun hb => by simp at hb⟩
      rw [hq', hsg']; exact ⟨h1, h2'⟩
  · refine ⟨(v, x₁, x₂, z, false, v, true), ?_, ?_⟩
    · refine mem_nodesT.2 ⟨Finset.mem_filter.2 ⟨?_, hcd, hε', h3, hR, hcd0.1, fun hb => by simp at hb⟩, hT⟩
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
      exact ⟨hcd0.1, ⟨hz1, hz2⟩, hcd0.1, trivial⟩
    · exact ⟨hκA, hsg, hsim, fun hb => by simp at hb, fun _ => hI⟩

/-- **`VineNodeExists`** (the vine case of coverage, named residual): an intact collected object that is not yet removed and respects
the first-stage order gives a vine node whose class contains `κ`. -/
def VineNodeExists (M₀ : Molecule V D₀) (Rn : ℕ) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (Fst : Set (Object M₀)) (crit : V → Prop) (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ))) : Prop :=
  ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1 M₀ Rn C Un Fst L γ η w A0 A h → ∀ κ ∈ A,
    ∀ U : Object M₀, Collected C (Un κ) L γ η w κ U → UIntact U h → ¬ Dartless U h →
    (U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' h) →
    ∃ t ∈ nodes1 C crit L γ η h, κ ∈ cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
      t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2

/-- **`HmemAt` from the vine case.**  Hypotheses: `hdisj` (collected objects have the same designation or are atom-disjoint, `desDisj_of_parts`), `hFst` (first-stage objects are
collected for every decoration, i.e. lie in `C₁`). -/
theorem hmemAt_of_vineNodes {M₀ : Molecule V D₀} {Rn : ℕ} (hS : SubHyp Rn M₀) {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {crit : V → Prop} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))} (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ) (h2 : 2 / L ≤ L ^ (-γ + η))
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Object M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hFst : ∀ κ ∈ A0, ∀ U ∈ Fst, Collected C (Un κ) L γ η w κ U)
    (hv : VineNodeExists M₀ Rn C Un Fst crit L γ η w A0) :
    HmemAt M₀ Rn C L γ η w A0 Un Fst crit := by
  intro A h hA κ hκ hns
  have hAe : A ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨κ, hκ⟩
  have hr : Reach1 C Un Fst L γ η w κ h := (hA.2.resolve_left hAe).2.2 κ hκ
  have hκ0 : κ ∈ A0 := hA.1 hκ
  have hinv := collInv_of_reach1 hS (h0 κ hκ0) (hdisj κ hκ0) hr
  unfold Stuck1 at hns
  by_cases hex : ∃ U, Collected C (Un κ) L γ η w κ U ∧ ¬ Dartless U h
  · left
    obtain ⟨U₀, hU₀, hnd₀⟩ := hex
    by_cases hF : ∃ U ∈ Fst, ¬ Dartless U h
    · obtain ⟨U, hUF, hnd⟩ := hF
      exact hv A h hA κ hκ U (hFst κ hκ0 U hUF) ((hinv U (hFst κ hκ0 U hUF)).resolve_left hnd) hnd (Or.inl hUF)
    · push Not at hF
      exact hv A h hA κ hκ U₀ hU₀ ((hinv U₀ hU₀).resolve_left hnd₀) hnd₀ (Or.inr hF)
  · right
    push Not at hex
    have hall : ∀ U, Collected C (Un κ) L γ η w κ U → Dartless U h := fun U hU => hex U hU
    have hnt : ¬ NoTripleCut C L γ η w κ h := fun hn => hns ⟨hn, hall⟩
    exact hmem_triple hLe hηγ h2 hκ hall hnt

end WaveTurbulence.FinalCountAsm
