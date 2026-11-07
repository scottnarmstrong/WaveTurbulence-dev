/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot18

/-! # V5 Step 4d-B2: the bottom vine, part 19 (absolute convergence of the bundle)

`psiBot_BOKd`: the bundle `psiBot` is integrable in the clock for every decoration of the chain region, with summable `L¹` norms in the
decorations (sum over the finite class of the per-state `BOKd`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

theorem BOKd.finset_sum {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {L : ℝ} {base : Mom d} {β : Fin 4 → Mom d} {β' : Type*} (s : Finset β')
    (g : β' → CLLocalDecoration R L base β → CLInternalTime R → ℂ) (hg : ∀ i ∈ s, BOKd R L base β (g i)) :
    BOKd R L base β (fun κ τ => ∑ i ∈ s, g i κ τ) := by
  refine ⟨fun κ => integrable_finset_sum s (fun i hi => (hg i hi).1 κ), ?_⟩
  have hb : ∀ κ, ∫ τ, ‖∑ i ∈ s, g i κ τ‖ ≤ ∑ i ∈ s, ∫ τ, ‖g i κ τ‖ := by
    intro κ
    calc ∫ τ, ‖∑ i ∈ s, g i κ τ‖ ≤ ∫ τ, ∑ i ∈ s, ‖g i κ τ‖ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => norm_nonneg _)
            (integrable_finset_sum s (fun i hi => ((hg i hi).1 κ).norm))
            (Filter.Eventually.of_forall fun τ => norm_sum_le _ _)
      _ = ∑ i ∈ s, ∫ τ, ‖g i κ τ‖ := integral_finset_sum s (fun i hi => ((hg i hi).1 κ).norm)
  exact Summable.of_nonneg_of_le (fun κ => integral_nonneg (fun _ => norm_nonneg _)) hb
    (summable_sum (fun i hi => (hg i hi).2))

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} [Fintype ι] [DecidableEq ι]

theorem psiBot_BOKd (κ0 : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hA : IsPrimeGarden A.skeleton) (hb0 : c0.b = (A.family.placement pstar).lower)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j)) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    BOKd (botR A c0) κ0.L κ0.base ![e, f, g, h] fun κd τ =>
      psiBot p kind κ0 A c0 pstar (clExtendIndices (botR A c0) κd.1) ![t0, t1, t2]
        (clLocalClock (botR A c0) ![t0, t1, t2] τ) := by
  have hz := fun z (hz : z ∈ canonFinsetK p kind A c0) =>
    botGoal_of_mem (p := p) { κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h } A c0 hA hb0 hup hL hF hz
  exact BOKd.finset_sum (canonFinsetK p kind A c0) (fun z κd τ => stBot { κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h } A c0 pstar z.1
    (clExtendIndices (botR A c0) κd.1) ![t0, t1, t2] (clLocalClock (botR A c0) ![t0, t1, t2] τ)) (fun z hz' => (hz z hz').2)

end WaveTurbulence.VineEstS5B2
