/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL27
public import WaveTurbulence.Foundations.FinalCount.GV14
/-! **G3-LOWDEG (R48), part 28: the loop start, assembled.**  `runDataL_of_loop`: a garden molecule `M` with self-loops, with the
producers' data on `M` (the same data as in the loop-free case: `C`, `Unsel`, `SubproOblG`, `TripleDesig`, `UnselOK`) and the
run on `M.unloop`, gives `RunDataL` for `M.unloop` with the admissible set `unloopAdm`.  Together with `countA_unloop_le` (GL17),
`SubHypLoop.unloop` (GL18): `𝔄(M) ≤ g^k 𝔄(M.unloop)`, `M.unloop` satisfies `SubHypL (R+k)`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
universe u
variable {V : Type*} [DecidableEq V] {D : Type u} [Fintype D] [DecidableEq D] {d : ℕ}
variable {R' : ℕ} {M : Molecule V D} {L γ η : ℝ}

/-- **Example B reduces to Example A**: a molecule all of whose darts are loops (a single atom with self-loops) has
`𝔄(M) ≤ (L^{-(d-γ)} C₁⁻¹ δ^{1/2})^k` (here `k = 1`), since its `unloop` is dartless (`𝔄 ≤ 1`). -/
theorem countA_allLoops_le (hb : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hall : ∀ x : D, M.atom x = M.atom (M.mate x))
    (L γ δ C₁ : ℝ) (hL : 0 < L) (hC : 0 < C₁) (hδ : 0 < δ) (w : Mom d) (Adm : (D → Fin d → ℤ) → Prop)
    (hdet : ∀ κ₁ κ₂, Adm κ₁ → Adm κ₂ → (∀ x : D, M.atom x ≠ M.atom (M.mate x) → κ₁ x = κ₂ x) → κ₁ = κ₂)
    (P : Finset V → ℝ) :
    M.countA L γ δ C₁ w Adm P ≤ ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ))) ^ M.loopBonds.card) := by
  haveI : IsEmpty (NonLoop M) := unloop_isEmpty_of_allLoops M hall
  calc M.countA L γ δ C₁ w Adm P ≤ _ := countA_unloop_le M hb L γ δ C₁ hL hC hδ w Adm hdet P
    _ ≤ ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ))) ^ M.loopBonds.card) * 1 := by
        gcongr; exact countA_dartless_le_one M.unloop L γ δ C₁ w _ P
    _ = _ := mul_one _

end WaveTurbulence.FinalCountG3
