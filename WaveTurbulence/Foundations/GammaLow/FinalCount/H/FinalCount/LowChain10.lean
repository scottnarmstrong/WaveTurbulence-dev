/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain9
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain10`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, LC-2 (6): the phase-2 (triangle) cover with the LOW invariant** (`node2_factsL`, `phase2_cover_memL`, `phase2_coverL`;
the degree bound `3 ≤ deg` of the `ε`-atoms of an eligible triangle comes from `NoD3`, `deg_three_of_eligible`). -/
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


/-- **A decoration with an eligible triangle lies in a node class** (phase 2). -/
theorem phase2_cover_memL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η : ℝ} {w : Mom d} {A0 A : Set (D₀ → (Fin d → ℤ))}
    {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} (hS : SubHypL Rn M₀)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hRA : ∀ κ h, Rch κ h → Reach2L C Un Fst L γ η w κ h)
    (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ) (h2 : 2 / L ≤ L ^ (-γ + η))
    {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h) (hAe : A ≠ ∅) {κ : D₀ → (Fin d → ℤ)} (hκ : κ ∈ A)
    (hnb : ¬ NoEligibleTriangle C L γ η w κ h) :
    ∃ n : T2 h, Node2 L γ η h n ∧ (∀ j : Fin 3, Desig C (h.anc (n.1 j)) (h.s.pr (n.2.1 j) (n.2.2.1 j))) ∧ κ ∈ cls2 L γ η w h A n := by
  obtain ⟨⟨R', hR', hc⟩, hap, hr⟩ := hA.2.resolve_left hAe
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hreach := hRA κ h (hr κ hκ)
  obtain ⟨R'', -, hIL⟩ := invL_reach2 hS (h0 κ (hA.1 hκ)) hreach
  obtain ⟨h₂, hN, hA₂, hD₂, hE⟩ := hreach.d3info hS (h0 κ (hA.1 hκ))
  unfold NoEligibleTriangle at hnb
  push Not at hnb
  obtain ⟨T0, hel⟩ := hnb
  obtain ⟨Q, kp, hQ, hsim, hkp, hi0, hi1⟩ := step2_data (C := C) hL h2 T0 hel
  have hInv := hIL.good.1
  have fs := fresh3_spec h
  let T : TriData h.s.M := triWithF T0 (fresh3 h) fs.1 fs.2
  have hcl : PClosed T.kept (triKeep h.s T) := tri_keep_closed hInv T
  have h3 : ∀ j, h.s.cls (T.t j) = .eps → 3 ≤ h.s.M.deg (T.t j) :=
    deg_three_of_eligible hA₂ hD₂ hc.anc hIL.rel hE hN T0 hel
  have hz : ∀ j : Fin 2, ∃ z : ℤ, Q j = (2 : ℝ) ^ z := fun j => by
    obtain ⟨z, hz, -⟩ := label_zrange hLe hηγ (hQ j); exact ⟨z, hz⟩
  choose z hzQ using hz
  have hQe : Q = fun j => (2 : ℝ) ^ z j := funext hzQ
  have hkpe : kp = fun j => if decide (kp j = 50) then 50 else 0 := by
    funext j; rcases hkp j with e | e <;> simp [e]
  have hd0 : T.t 0 ∈ h.s.M.atoms := T.t_mem 0
  obtain ⟨a0, sg0, ha0, hw0⟩ := alive_data0 (L := L) (γ := γ) (η := η) (w := w) (κ := κ) (h := h) (h.s.pr (T.a 0) (T.b 0)) (Q 0) (T.t 0) hd0
  obtain ⟨a1, sg1, sib, ha1, hw1⟩ := alive_data1 (L := L) (γ := γ) (η := η) (w := w) (κ := κ) (h := h) T (h.s.pr (T.a 0) (T.b 0))
    (h.s.pr (T.a 1) (T.b 1)) rfl (Q 1) (T.t 0) hd0
  let n : T2 h := (T.t, T.a, T.b, z, fun j => decide (kp j = 50), ![a0, a1], ![sg0, sg1], sib)
  have hb0 : (decide (kp 0 = 50)) = true ↔ kp 0 = 50 := decide_eq_true_iff
  have hb1 : (decide (kp 1 = 50)) = true ↔ kp 1 = 50 := decide_eq_true_iff
  have hf0 : (decide (kp 0 = 50)) = false ↔ ¬ kp 0 = 50 := decide_eq_false_iff_not
  have hf1 : (decide (kp 1 = 50)) = false ↔ ¬ kp 1 = 50 := decide_eq_false_iff_not
  refine ⟨n, ⟨T, hcl, rfl, rfl, rfl, rfl, fun j => ?_, h3, fun j => ?_, fun hb => ?_, fun hb hs => ?_, fun hb hs => ?_⟩, hel.2.2, ?_⟩
  · rw [← hzQ j]; exact hQ j
  · fin_cases j <;> simp [n, ha0, ha1]
  · obtain ⟨q, vis, hcr, hq, -⟩ := hw0 (hi0.1 (hb0.1 hb))
    exact ⟨q, vis, hcr, hq⟩
  · obtain ⟨q, vis, hcr, hq, -⟩ := (hw1 (hi1.1 (hb1.1 hb))).1 hs
    exact ⟨q, vis, hcr, hq⟩
  · exact (hw1 (hi1.1 (hb1.1 hb))).2.2 hs
  · subst hQe
    refine ⟨hκ, fun j => hel.1 j, fun j => hsim j, hel.2.1, fun he hb => ?_, fun he hb => ?_, fun he hb => ?_, fun he hb => ?_⟩
    · exact (hw0 (hi0.1 (hb0.1 hb))).choose_spec.choose_spec.2.2
    · exact fun hit => (hf0.1 hb) (hi0.2 hit)
    · refine ⟨fun hs => (hw1 (hi1.1 (hb1.1 hb))).1 hs |>.choose_spec.choose_spec.2.2, fun hs => (hw1 (hi1.1 (hb1.1 hb))).2.1 hs⟩
    · exact fun hit => (hf1.1 hb) (hi1.2 hit)


end WaveTurbulence.GammaLow.FinalCount.H
