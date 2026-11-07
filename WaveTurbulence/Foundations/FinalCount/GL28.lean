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

theorem runDataL_of_loop {hf : HSt V (NonLoop M)} (Adm : (D → Fin d → ℤ) → Prop)
    (hctx : ∀ κ, Adm κ → LoopCtx L (0 : Mom d) κ R' M)
    (hdata : ∀ κ, Adm κ → ∃ (C : CollData M) (Unsel : Set (Object M)), SubproOblG C L γ η (0 : Mom d) κ ∧ TripleDesig C ∧
      HingeNoLoop C ∧ C.UnselOK L γ η (0 : Mom d) κ Unsel ∧
      HRunLC L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1) M.unloop hf C.unloop (unloopSet M Unsel)) :
    RunDataL L γ η M.unloop hf (unloopAdm M Adm) := by
  rintro κ' ⟨κ, hκ, rfl⟩
  obtain ⟨C, Unsel, obl, hT3, hH, hU, hrun⟩ := hdata κ hκ
  exact ⟨C.unloop, unloopSet M Unsel, SubproOblG.unloop (hctx κ hκ) hH obl, TripleDesig.unloop hH hT3,
    UnselOK.unloop (hctx κ hκ) hH obl hU, hrun⟩

/-- The whole loop-start package at the level of the molecule: `M.unloop` satisfies `SubHypL (R + k)`, and its `h0`, `DegenSGT`. -/
theorem loopStart {R : ℕ} (hS : SubHypLoop R M) {κ : D → Fin d → ℤ} (hκ : ∀ x, κ (M.mate x) = κ x) {Tm : V → Prop}
    (hdeg : DegenSGT M L γ η (0 : Mom d) κ Tm)
    (h0 : ∀ a ∈ M.atoms, M.deg a = 4 → ∑ x ∈ M.dartsAt a, M.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0)
    (heq : ∀ y : D, M.atom y = M.atom (M.mate y) → ∀ z : D, M.atom z = M.atom y → κ z = κ y) :
    SubHypL (R + M.loopBonds.card) M.unloop ∧ LoopCtx L (0 : Mom d) κ (R + M.loopBonds.card) M ∧
      DegenSGT M.unloop L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1) Tm ∧
      (∀ a ∈ M.unloop.atoms, M.unloop.deg a = 4 → ∑ x ∈ M.unloop.dartsAt a, M.unloop.dartSign x •
        Molecule.kvec L (0 : Mom d) (fun y : NonLoop M => κ y.1) x = 0) := by
  have hb : ∀ a ∈ M.atoms, M.deg a ≤ 4 := fun a ha => deg_le_four M (hS.bounds a ha)
  have h0' := h0_unloop hS hκ h0
  have hctx : LoopCtx L (0 : Mom d) κ (R + M.loopBonds.card) M := ⟨hS.unloop, hb, hκ, heq, h0'⟩
  exact ⟨hS.unloop, hctx, DegenSGT.unloop hctx hdeg, h0'⟩

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
