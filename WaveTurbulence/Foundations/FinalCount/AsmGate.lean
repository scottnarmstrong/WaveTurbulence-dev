/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGeom
/-! **FINALCOUNT-ASSEMBLY (R48): the REG/LOW split of the amended gate** (the real `FinalCountAt` of LG-SPINE AMEND7+8).  `RegGeom G`: every atom has degree `≥ 3` and there is no loop.
`FinalCountAt P ← FinalCountRegAt P ∧ FinalCountLowAt P` (`finalCountAt_of_reg_low`). -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Set Finset
open scoped ENNReal

/-- The REG predicate: all atoms of degree `≥ 3`, no loops. -/
def RegGeom {R : ℕ} (G : Garden (2 * R)) : Prop :=
  (∀ a ∈ G.molecule.atoms, 3 ≤ G.molecule.deg a) ∧ ∀ x, G.molecule.atom x ≠ G.molecule.atom (G.molecule.mate x)

/-- The amended `FinalCountAt` with an extra case hypothesis `Φ G` (after the geometry). -/
def FinalCountAtWith (P : WTParams) (Φ : ∀ {R : ℕ}, Garden (2 * R) → Prop) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelData G P.d) (C : SourceVine.CountingChoices G P.d),
    D.hinges = C.subpro.hinges → SourceVine.CountingGeometry G C → Φ G →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ Adm : (GardenDart G → (Fin P.d → ℤ)) → Prop,
    (∀ κ, Adm κ → splicedCountingAdmissible G D C P.L P.γ P.η base roots κ) →
    G.molecule.countA P.L P.γ P.δ P.C₁ base Adm C.ladderScale ≤
      ENNReal.ofReal
        (P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
          P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40)))

/-- REG: every atom of degree `≥ 3` and no loops. -/
def FinalCountRegAt (P : WTParams) : Prop := FinalCountAtWith P (fun G => RegGeom G)

/-- LOW (R48 named residual, owner G3-LOWDEG): some atom of degree `< 3` or some loop. -/
def FinalCountLowAt (P : WTParams) : Prop := FinalCountAtWith P (fun G => ¬ RegGeom G)

theorem finalCountAt_of_reg_low {P : WTParams} (hr : FinalCountRegAt P) (hl : FinalCountLowAt P) : FinalCountAt P := by
  intro p hp R hR hRm G hpl hirr hbal hn hnm D C hh hg base roots Adm hA
  by_cases hreg : RegGeom G
  · exact hr p hp R hR hRm G hpl hirr hbal hn hnm D C hh hg hreg base roots Adm hA
  · exact hl p hp R hR hRm G hpl hirr hbal hn hnm D C hh hg hreg base roots Adm hA

theorem finalCountReg_of_at7 {P : WTParams} (h : FinalCountAt P) : FinalCountRegAt P :=
  fun p hp R hR hRm G hpl hirr hbal hn hnm D C hh hg _ base roots Adm hA =>
    h p hp R hR hRm G hpl hirr hbal hn hnm D C hh hg base roots Adm hA

end WaveTurbulence.FinalCountAsm
