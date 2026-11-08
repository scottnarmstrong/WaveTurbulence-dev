/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKFine.Gate
import Mathlib.Tactic

/-! # C4b FINE-PIN: non-vacuity bridge to main's fine bound

At unmarked data (C2's `toMKData`: no pins, no filters, indicator `1`), no survivors (`survEmpty`) and `E = ∅`,
`FineSplicedAtMK P` gives exactly the conclusion of main's `Cover.fine_spliced_of_subpro_choices` under main's
`SubproConclusions` (the extra factors `L^{2·0}` and `((N+1)L)^0` are `1`). -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine
open Set Finset
open scoped Classical ENNReal

/-- Main's subpro conclusions are the marked ones with no survivors. -/
theorem subproConclusionsMK_of_empty {R d : ℕ} {G : Garden (2 * R)} {D : SplicedKernelData G d}
    {Cs : SubproChoices G} {L γ η : ℝ} {base : Mom d} {roots : Fin (2 * R) → (Fin d → ℤ)}
    (h : Cover.SubproConclusions G D Cs L γ η base roots) :
    SubproConclusionsMK G D Cs (survEmpty G) L γ η base roots :=
  ⟨h.structural, structural_empty Cs, chainOrder_empty G, h.hinges,
    fun z he hg => subproSupportMK_of_empty G Cs L γ η base _ _ (h.support z he hg),
    h.hingeOutsideFirst, h.tripleDesignated, h.hingeNoLoop⟩

/-- **Non-vacuity**: `FineSplicedAtMK P` gives main's fine bound (the conclusion of
`Cover.fine_spliced_of_subpro_choices`) for unmarked data. -/
theorem fine_spliced_of_MK (P : WTParams) (h : FineSplicedAtMK P)
    {p R : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (G : Garden (2 * R)) (hplain : G.IsPlain) (hirred : G.Irreducible)
    (hbal : IsBalancedSig G.sig) (hn : 1 ≤ G.order) (hnmax : G.order ≤ P.N (p + 1) ^ 4)
    (D : SplicedKernelData G P.d) (hD : SplicedAmplitudeBounds G D) (hlayer : ∀ v, D.layer v ≤ p)
    (hM : G.molecule.IsMolecule) (hconn : G.molecule.IsConnected)
    (hatoms : G.molecule.atoms.card = G.order) (hbonds : G.molecule.bonds.card + R = 2 * G.order)
    (Cs : SubproChoices G) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hS : Cover.SubproConclusions G D Cs P.L P.γ P.η base roots) :
    ‖splicedKernel G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) *
          P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) := by
  have hb := h p hp R hR hRmax G hplain hirred hbal hn hnmax (toMKData D) Cs (survEmpty G) ∅ hD hlayer
    (fun a q hq => by simp [toMKData] at hq) (fun k => by simp [toMKData])
    (fun b hb => by simp [toMKData] at hb) (fun b t hb => by simp [toMKData] at hb) base roots
    ⟨hM, hconn, hatoms, hbonds⟩ (subproConclusionsMK_of_empty hS)
  rw [splicedKernelMK_toMK] at hb
  simpa [survEmpty, toMKData] using hb

end WaveTurbulence.Flower.FinalMKFine
