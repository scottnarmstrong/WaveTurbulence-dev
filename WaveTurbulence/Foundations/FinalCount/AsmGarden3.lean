/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGarden2
public import WaveTurbulence.Foundations.FinalCount.AsmGapBase
/-! **FINALCOUNT-ASSEMBLY (garden level, 3): base independence of the gap notions** (`HasGapKind`, `SubproOblG`, `SGat`, `DegenSGT`,
`SourceLadderGaps`).  The counting hypotheses are stated at the base of `FinalCountAt`; the chain runs at base `0`.  Gaps are base independent
(`gapAt_base_indep`), hence so is every notion defined through `gapAt`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem isBlockGap_base_indep (M : Molecule V D) (L : ℝ) (w w' : Mom d) (κ : D → (Fin d → ℤ)) (S : Finset V) (j : V) (r : Mom d) :
    M.IsBlockGap L w κ S j r ↔ M.IsBlockGap L w' κ S j r := by
  unfold Molecule.IsBlockGap
  simp only [gapAt_base_indep L w w' κ]

theorem vineLike_isGap_base_indep {M : Molecule V D} {S : Finset V} {a b : V} (C : VineLikeObject M S a b) (L : ℝ) (w w' : Mom d)
    (κ : D → (Fin d → ℤ)) (r : Mom d) : C.IsGap L w κ r ↔ C.IsGap L w' κ r := by
  cases C with
  | vc h => exact isBlockGap_base_indep M L w w' κ S a r
  | hyper R => exact isBlockGap_base_indep _ L w w' _ S a r

theorem object_hasGapKind_base_indep {M : Molecule V D} (O : Object M) (L γ η : ℝ) (w w' : Mom d)
    (κ : D → (Fin d → ℤ)) (k : Molecule.GapKind) : O.HasGapKind L γ η w κ k ↔ O.HasGapKind L γ η w' κ k := by
  unfold Object.HasGapKind
  exact exists_congr fun r => and_congr_left' (vineLike_isGap_base_indep O.shape L w w' κ r)

theorem sgat_base_indep (M : Molecule V D) (L γ η : ℝ) (w w' : Mom d) (κ : D → (Fin d → ℤ)) (v : V) :
    SGat M L γ η w κ v ↔ SGat M L γ η w' κ v := by
  unfold SGat
  simp only [gapAt_base_indep L w w' κ]

theorem degenSGT_base_indep (M : Molecule V D) (L γ η : ℝ) (w w' : Mom d) (κ : D → (Fin d → ℤ)) (Tm : V → Prop) :
    DegenSGT M L γ η w κ Tm ↔ DegenSGT M L γ η w' κ Tm := by
  unfold DegenSGT
  simp only [gapAt_base_indep L w w' κ, sgat_base_indep M L γ η w w' κ]

theorem hasChosenPair_congr' {E : Type*} {f s : Option E} {P Q : E → E → Prop} (h : ∀ x y, P x y ↔ Q x y) :
    HasChosenPair f s P ↔ HasChosenPair f s Q := by
  unfold HasChosenPair
  exact exists_congr fun x => exists_congr fun y => and_congr_right fun _ => and_congr_right fun _ => h x y

theorem subproOblG_base_indep {M : Molecule V D} (C : CollData M) (L γ η : ℝ) (w w' : Mom d) (κ : D → (Fin d → ℤ)) :
    SubproOblG C L γ η w κ ↔ SubproOblG C L γ η w' κ := by
  have hhost : ∀ P : Object M, C.Host L γ η w κ P ↔ C.Host L γ η w' κ P := by
    intro P
    unfold CollData.Host
    simp only [object_hasGapKind_base_indep _ L γ η w w' κ]
  have hsg : ∀ P : Object M, P.HasGapKind L γ η w κ .SG ↔ P.HasGapKind L γ η w' κ .SG :=
    fun P => object_hasGapKind_base_indep P L γ η w w' κ _
  constructor
  · intro h
    refine ⟨fun P hP hO hD => (hhost P).1 (h.contained P ((hsg P).2 hP) hO hD), fun v hv => ?_, h.hingeJoint, fun P hP hO hD => ?_⟩
    · exact (hasChosenPair_congr' fun x y => by simp only [gapAt_base_indep L w w' κ]).1 (h.hingeSG v hv)
    · obtain ⟨v, hv, hvP, hr⟩ := h.crossing P ((hsg P).2 hP) hO hD
      exact ⟨v, hv, hvP, hr⟩
  · intro h
    refine ⟨fun P hP hO hD => (hhost P).2 (h.contained P ((hsg P).1 hP) hO hD), fun v hv => ?_, h.hingeJoint, fun P hP hO hD => ?_⟩
    · exact (hasChosenPair_congr' fun x y => by simp only [gapAt_base_indep L w w' κ]).1 (h.hingeSG v hv)
    · obtain ⟨v, hv, hvP, hr⟩ := h.crossing P ((hsg P).1 hP) hO hD
      exact ⟨v, hv, hvP, hr⟩

theorem sourceLadderGaps_base_indep (M : Molecule V D) (L : ℝ) (w w' : Mom d) (P : Finset V → ℝ) (κ : D → (Fin d → ℤ)) :
    SourceLadderGaps M L w P κ ↔ SourceLadderGaps M L w' P κ := by
  unfold SourceLadderGaps Molecule.IsLadderGap
  simp only [gapAt_base_indep L w w' κ]

end WaveTurbulence.FinalCountAsm
