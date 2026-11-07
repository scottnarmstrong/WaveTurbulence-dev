/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsBase
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelLoc2

/-! # Joint measurability of the native summand `psiNat` in the exterior times and the clock (V5 Step 4d part C) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {D : ReconstructionData G} {hG : G.IsPlain} {L γ δ : ℝ} {F : ℕ → Mom d → ℝ}
  {layer : GNode (D.forest hG) → ℕ} {hLayer : IsLayering (D.garden hG) layer} {base : Mom d}

theorem measurable_parentClock_top {α : Type*} [MeasurableSpace α] {tree : Fin w → TTree} (top : α → ℝ)
    (u : α → GBranch tree → ℝ) (hT : Measurable top) (hu : ∀ b, Measurable fun z => u z b) (x : GNode tree) :
    Measurable (fun z => parentClock (top z) (u z) x) := by
  unfold parentClock
  generalize nodeToSlot x = s
  rcases s with _ | ⟨b, _⟩
  · exact hT
  · exact hu b

section Meas
variable (R : CLRegionData G U a b) (layer0 : GBranch G.tree → ℕ)

theorem measurableSet_ClDom :
    MeasurableSet {z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) | ClDom R layer0 z.1 z.2} := by
  classical
  have hu : ∀ v : GBranch G.tree, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.2 v :=
    fun v => (measurable_pi_apply v).comp measurable_snd
  have ht : ∀ j : Fin 3, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.1 j :=
    fun j => (measurable_pi_apply j).comp measurable_fst
  have hp : ∀ x : GNode G.tree, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => parentClock (z.1 0) z.2 x :=
    fun x => measurable_parentClock_top (α := (Fin 3 → ℝ) × (GBranch G.tree → ℝ)) (fun z => z.1 0) (fun z => z.2) (ht 0) hu x
  unfold ClDom
  simp only [Set.setOf_and]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => ?_
    simp only [Set.setOf_and]
    exact (measurableSet_lt measurable_const (hu v)).inter ((measurableSet_lt (hu v) measurable_const).inter
      ((measurableSet_lt measurable_const (hu v)).inter (measurableSet_lt (hu v) (hp _))))
  · by_cases hP : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching
    · simp only [hP, true_implies]
      exact measurableSet_lt (ht 1) (hu b)
    · simp only [hP, false_implies, Set.setOf_true]
      exact MeasurableSet.univ
  · by_cases hP : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching
    · simp only [hP, true_implies]
      exact measurableSet_lt (ht 2) (hu b)
    · simp only [hP, false_implies, Set.setOf_true]
      exact MeasurableSet.univ

end Meas

/-- **`psiNat` is jointly measurable** in the exterior times and the clock. -/
theorem measT_psiNat (R : CLRegionData G U a b) (hF : HF D hG L F layer base) :
    ∀ x : GNode G.tree → (Fin d → ℤ), Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) =>
      psiNat D hG R L γ δ F layer hLayer base x z.1 z.2 := by
  classical
  intro x
  have hu : ∀ v : GBranch G.tree, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.2 v :=
    fun v => (measurable_pi_apply v).comp measurable_snd
  have ht : ∀ j : Fin 3, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => z.1 j :=
    fun j => (measurable_pi_apply j).comp measurable_fst
  have hp : ∀ y : GNode G.tree, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => parentClock (z.1 0) z.2 y :=
    fun y => measurable_parentClock_top (α := (Fin 3 → ℝ) × (GBranch G.tree → ℝ)) (fun z => z.1 0) (fun z => z.2) (ht 0) hu y
  have hphase : Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) =>
      clRegionalPhase G U L γ δ (cosetDecoration G L base x) z.2 := by
    unfold clRegionalPhase
    exact Finset.measurable_prod _ fun v _ =>
      (continuous_phaseAtom L γ δ (G.sign v.toNode) _).measurable.comp (hu v)
  have hstar : Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) =>
      starProd D hG L γ δ F layer hLayer base U a (z.1 0) x z.2 := by
    unfold starProd
    refine Measurable.mul (Finset.measurable_prod _ fun p _ => ?_) (Finset.measurable_prod _ fun v _ => ?_)
    · exact VineEst.measurable_KQsel_comp _ _ _ L γ δ F _ (native_couple_plain D hG layer hLayer p) _
        (couple_hF hF p (x (p.firstLeaf hG).toNode)) (hp _) (hp _)
    · exact VineEst.measurable_KTsel_comp _ _ L γ δ F _ (native_chain_paired D hG layer hLayer v) _
        (chain_hF hF v (x v.toNode)) (hp _) (hu v)
  unfold psiNat
  exact measurable_const.mul (Measurable.ite (measurableSet_ClDom R _) (hphase.mul hstar) measurable_const)


section Lv
variable {R : CLRegionData G U a b} {n : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **The base leaf obligations of `hAbs`**: the native summand of a level has a uniform `UAbs` bound and is jointly measurable. -/
theorem Lvl.abs_base (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (lv : Lvl B) :
    (∃ C : ℝ, 0 ≤ C ∧ UAbs lv.region κ0.L κ0.base (lv.psiBase B RD hG layer hLayer κ0) C) ∧
      MeasT (lv.psiBase B RD hG layer hLayer κ0) := by
  have hHF := HF_of_all (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain κ0.L κ0.F
    (stateLayer (lv.state B RD hG layer hLayer)) κ0.base hF
  have hu := uAbs_psiNat (hLayer := stateLayer_isLayering (lv.state B RD hG layer hLayer)) (γ := κ0.γ) (δ := κ0.δ)
    lv.c.block lv.region hHF hL
  have hm := measT_psiNat (hLayer := stateLayer_isLayering (lv.state B RD hG layer hLayer)) (γ := κ0.γ) (δ := κ0.δ)
    lv.region hHF
  refine ⟨⟨_, ?_, hu⟩, hm⟩
  exact baseConst_nonneg _

end Lv

end WaveTurbulence.VineEstS5C
