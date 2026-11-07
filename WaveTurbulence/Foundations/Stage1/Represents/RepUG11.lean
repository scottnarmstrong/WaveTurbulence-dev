/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG10
public import WaveTurbulence.Foundations.Vine.B.Src5
import Mathlib.Tactic

/-!
# S2 REPRESENTS, G1 (3): the clock tuple of a unit lies in the weak output box

`g1_weak`: for `τ` in the spliced time domain, the clock tuple `(τ_{u1}, τ_{u21}, τ_{u22})` of a unit, with the clock of every
LEAF lower child replaced by the dummy time `qOut i`, lies in `outBoxW`.  Inputs (all about the layer indices only):
`qOut 0 = lay (hinge)`, `qOut i = lay c` for a BRANCH lower child `c` (core layers; this is the content of R74's `outNode` box),
and `qOut 1, qOut 2 ≤ qOut 0`.  The dummy time of a leaf child is `qOut i`, which is below the hinge clock by the last hypothesis.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS2 WaveTurbulence.RepAnalytic

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

open scoped Classical in
theorem coord_ok (tt : Fin w → ℝ) (τ : GBranch Gsb.tree → ℝ) (lay : GBranch Gsb.tree → ℕ) (q q0 : ℕ) (T0 : ℝ)
    (hT0 : (q0 : ℝ) ≤ T0) (hq : q ≤ q0) (ns : ClkSrc Gsb) (leaf : Prop) (hl : leaf ↔ ∃ r, ns = Sum.inl r)
    (hb : ∀ c, ns = Sum.inr c → q = lay c ∧ τ c < T0 ∧ τ c ∈ Set.Icc (lay c : ℝ) (lay c + 1)) :
    ((q : ℝ) ≤ (if leaf then (q : ℝ) else clockOf Gsb tt τ ns) ∧
        (if leaf then (q : ℝ) else clockOf Gsb tt τ ns) ≤ q + 1) ∧
      (if leaf then (q : ℝ) else clockOf Gsb tt τ ns) ≤ T0 := by
  have hq' : (q : ℝ) ≤ q0 := by exact_mod_cast hq
  rcases ns with r | c
  · have hleaf : leaf := hl.mpr ⟨r, rfl⟩
    rw [if_pos hleaf]
    exact ⟨⟨le_refl _, by linarith⟩, by linarith⟩
  · have hnl : ¬ leaf := fun h => by obtain ⟨r, hr⟩ := hl.mp h; exact absurd hr (by simp)
    rw [if_neg hnl]
    obtain ⟨hqc, hlt, hbox⟩ := hb c rfl
    show ((q : ℝ) ≤ τ c ∧ τ c ≤ q + 1) ∧ τ c ≤ T0
    rw [hqc]
    exact ⟨hbox, hlt.le⟩

open scoped Classical in
theorem g1_weak (Φ : SpliceShape blk Gsb) (hd : Disj blk) (j : J) (tt : Fin w → ℝ) (lay : GBranch Gsb.tree → ℕ)
    {τ : GBranch Gsb.tree → ℝ} (hτ : τ ∈ splicedTimeDomain Gsb lay tt) (D : SumintDatum d)
    (h0 : D.qOut 0 = lay (Φ.hinge hd j))
    (h1 : ∀ c, nodeClk Gsb (Φ.hmom hd j 2) = Sum.inr c → D.qOut 1 = lay c)
    (h2 : ∀ c, nodeClk Gsb (Φ.hmom hd j 3) = Sum.inr c → D.qOut 2 = lay c)
    (hq1 : D.qOut 1 ≤ D.qOut 0) (hq2 : D.qOut 2 ≤ D.qOut 0)
    (leaf : Fin 3 → Prop) (hl0 : ¬ leaf 0)
    (hl1 : leaf 1 ↔ ∃ r, nodeClk Gsb (Φ.hmom hd j 2) = Sum.inl r)
    (hl2 : leaf 2 ↔ ∃ r, nodeClk Gsb (Φ.hmom hd j 3) = Sum.inl r) :
    (fun i => if leaf i then (D.qOut i : ℝ) else clockOf Gsb tt τ (Φ.hclk hd j i)) ∈ outBoxW D := by
  have hbox0 := Φ.hinge_clock_box hd j tt lay hτ
  rw [← h0] at hbox0
  have e0 : (if leaf 0 then (D.qOut 0 : ℝ) else clockOf Gsb tt τ (Φ.hclk hd j 0)) = τ (Φ.hinge hd j) := by
    rw [if_neg hl0]; rfl
  have c1 := coord_ok (Gsb := Gsb) tt τ lay (D.qOut 1) (D.qOut 0) (τ (Φ.hinge hd j)) hbox0.1 hq1
    (Φ.hclk hd j 1) (leaf 1) hl1 (fun c hc => by
      have hc' : nodeClk Gsb (Φ.hmom hd j 2) = Sum.inr c := hc
      obtain ⟨hlt, hbx⟩ := Φ.child_clock hd j 2 (by decide) tt lay hτ c hc'
      exact ⟨h1 c hc', hlt, hbx⟩)
  have c2 := coord_ok (Gsb := Gsb) tt τ lay (D.qOut 2) (D.qOut 0) (τ (Φ.hinge hd j)) hbox0.1 hq2
    (Φ.hclk hd j 2) (leaf 2) hl2 (fun c hc => by
      have hc' : nodeClk Gsb (Φ.hmom hd j 3) = Sum.inr c := hc
      obtain ⟨hlt, hbx⟩ := Φ.child_clock hd j 3 (by decide) tt lay hτ c hc'
      exact ⟨h2 c hc', hlt, hbx⟩)
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · show (D.qOut 0 : ℝ) ≤ (if leaf 0 then (D.qOut 0 : ℝ) else clockOf Gsb tt τ (Φ.hclk hd j 0)) ∧
        (if leaf 0 then (D.qOut 0 : ℝ) else clockOf Gsb tt τ (Φ.hclk hd j 0)) ≤ (D.qOut 0 : ℝ) + 1
      rw [e0]; exact ⟨hbox0.1, hbox0.2⟩
    · exact c1.1
    · exact c2.1
  · show max (if leaf 1 then (D.qOut 1 : ℝ) else clockOf Gsb tt τ (Φ.hclk hd j 1))
        (if leaf 2 then (D.qOut 2 : ℝ) else clockOf Gsb tt τ (Φ.hclk hd j 2)) ≤
      (if leaf 0 then (D.qOut 0 : ℝ) else clockOf Gsb tt τ (Φ.hclk hd j 0))
    rw [e0]
    exact max_le c1.2 c2.2

end WaveTurbulence.Represents
