/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.Time

/-! # D2c PROT-CUT: algebraic and measurability tools for the cut identities

* `link_cancel`: the linked phases of a chain pair cancel, `ζ_a Ω_a + ζ_b Ω_b = 0` (DH21 Prop 4.3, checked on the
  six mini-tree codes), for the boundary momenta of the closing pair.
* `epsDec_add_const`, `cosetDecoration_add_const`: a constant shift of the integer labels does not change `ε` and
  moves the coset base point.
* `stronglyMeasurable_protTime_param`: the free-time integral depends measurably on clocks that depend measurably
  on a parameter. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Flower.ProtDefs

/-- The momenta at the children of `𝔫_a`: `Px` at the chain slot, `Pr`, `Pg` at the red and green slots. -/
def cA {α : Type*} (m : MiniTreeCode) (Px Pr Pg : α) (i : Fin 3) : α :=
  if i = m.c then Px else if i = m.red.1 then Pr else Pg

/-- The momenta at the children of `𝔫_b`: `P0` at the lone slot. -/
def cB {α : Type*} (m : MiniTreeCode) (P0 Pr Pg : α) (k : Fin 3) : α :=
  if k = m.lone then P0 else if k = m.red.2 then Pr else Pg

/-- **The linked phases cancel** (DH21 Prop 4.3 for a chain pair): with `𝔫_a` of sign `ζ` and momentum `P0`,
`𝔫_b` of sign `slotSign ζ m.c` and momentum `Px`, `ζ_a Ω_a + ζ_b Ω_b = 0`. -/
theorem link_cancel (m : MiniTreeCode) (ζ : ℤˣ) {d : ℕ} (P0 Px Pr Pg : Mom d) :
    (((ζ : ℤˣ) : ℤ) : ℝ) * resFactor (cA m Px Pr Pg 0) (cA m Px Pr Pg 1) (cA m Px Pr Pg 2) P0 +
      (((slotSign ζ m.c : ℤˣ) : ℤ) : ℝ) * resFactor (cB m P0 Pr Pg 0) (cB m P0 Pr Pg 1) (cB m P0 Pr Pg 2) Px = 0 := by
  obtain ⟨c, b⟩ := m
  rcases Int.units_eq_one_or ζ with rfl | rfl <;> fin_cases c <;> fin_cases b <;>
    simp [cA, cB, resFactor, slotSign, MiniTreeCode.red, MiniTreeCode.green, MiniTreeCode.lone] <;> ring

theorem epsCoef_add_const {d : ℕ} (a b c x : Fin d → ℤ) : epsCoef (a + x) (b + x) (c + x) = epsCoef a b c := by
  unfold epsCoef
  simp only [ne_eq, add_left_inj]

theorem epsDec_add_const {w d : ℕ} (G : Garden w) (κ : GNode G.tree → (Fin d → ℤ)) (x : Fin d → ℤ) :
    epsDec G (fun z => κ z + x) = epsDec G κ := by
  unfold epsDec
  exact Finset.prod_congr rfl fun b _ => epsCoef_add_const _ _ _ _

theorem latticePoint_add {d : ℕ} (L : ℝ) (a b : Fin d → ℤ) :
    latticePoint L (a + b) = latticePoint L a + latticePoint L b := by
  unfold latticePoint
  ext j
  simp [add_div]

theorem latticePoint_zero {d : ℕ} (L : ℝ) : latticePoint L (0 : Fin d → ℤ) = 0 := by
  unfold latticePoint
  ext j
  simp

theorem cosetDecoration_add_const {w d : ℕ} (G : Garden w) (L : ℝ) (k : Mom d) (κ : GNode G.tree → (Fin d → ℤ))
    (x : Fin d → ℤ) :
    cosetDecoration G L k (fun z => κ z + x) = cosetDecoration G L (k + latticePoint L x) κ := by
  funext z
  show k + latticePoint L (κ z + x) = k + latticePoint L x + latticePoint L (κ z)
  rw [add_comm (κ z) x, latticePoint_add, add_assoc]

/-! ### Measurability in a parameter -/

theorem measurableSet_protDom_param {w : ℕ} (LG : LayeredGarden w) (up : ℝ → GBranch LG.garden.tree → ℝ)
    (sl : ℝ → ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (hup : ∀ b, Measurable fun u => up u b)
    (hsl : Measurable sl) :
    MeasurableSet {p : ℝ × ({b : GBranch LG.garden.tree // fix b = none} → ℝ) |
      LG.garden.extendFix fix p.2 ∈ protDom LG (up p.1) (sl p.1) fix} := by
  classical
  have hτ : ∀ b, Measurable fun p : ℝ × ({b : GBranch LG.garden.tree // fix b = none} → ℝ) =>
      LG.garden.extendFix fix p.2 b :=
    fun b => ((measurable_pi_apply b).comp (measurable_extendFix LG.garden fix)).comp measurable_snd
  have hU : ∀ b, Measurable fun p : ℝ × ({b : GBranch LG.garden.tree // fix b = none} → ℝ) => up p.1 b :=
    fun b => (hup b).comp measurable_fst
  have hS : Measurable fun p : ℝ × ({b : GBranch LG.garden.tree // fix b = none} → ℝ) => sl p.1 :=
    hsl.comp measurable_fst
  unfold protDom kDomainFix
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [Set.ofPred_and]
  refine MeasurableSet.inter ?_ ?_
  · rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun b => ?_
    rw [Set.ofPred_and]
    refine MeasurableSet.inter ?_ ?_
    · refine measurableSet_imp _ ?_
      exact (measurableSet_lt measurable_const (hτ b)).inter ((measurableSet_lt (hτ b) measurable_const).inter
        ((measurableSet_lt measurable_const (hτ b)).inter (measurableSet_lt (hτ b) (hU b))))
    · rw [Set.ofPred_forall]
      refine MeasurableSet.iInter fun b' => measurableSet_imp _ (measurableSet_imp _ ?_)
      exact measurableSet_lt (hτ b') (hτ b)
  · rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun b => measurableSet_imp _ (measurableSet_imp _ ?_)
    exact measurableSet_lt hS (hτ b)

/-- **The free-time integral depends measurably on parameter-dependent clocks.** -/
theorem stronglyMeasurable_protTime_param (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w)
    (up : ℝ → GBranch LG.garden.tree → ℝ) (sl : ℝ → ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (K : GNode LG.garden.tree → Mom d) (hup : ∀ b, Measurable fun u => up u b) (hsl : Measurable sl) :
    StronglyMeasurable fun u => protTime L γ δ LG (up u) (sl u) fix K := by
  classical
  set S := {p : ℝ × ({b : GBranch LG.garden.tree // fix b = none} → ℝ) |
      LG.garden.extendFix fix p.2 ∈ protDom LG (up p.1) (sl p.1) fix}
  have hSm : MeasurableSet S := measurableSet_protDom_param LG up sl fix hup hsl
  let g : ℝ × ({b : GBranch LG.garden.tree // fix b = none} → ℝ) → ℂ := fun p =>
    phaseProd L γ δ LG.garden K (LG.garden.extendFix fix p.2)
  have hg : Measurable g :=
    ((continuous_phaseProd L γ δ LG.garden K).measurable.comp (measurable_extendFix LG.garden fix)).comp
      measurable_snd
  have hf : StronglyMeasurable (S.indicator g) := (hg.indicator hSm).stronglyMeasurable
  have key := hf.integral_prod_right' (ν := (volume : Measure ({b : GBranch LG.garden.tree // fix b = none} → ℝ)))
  convert key using 2 with u
  unfold protTime
  congr 1

end WaveTurbulence.Flower.ProtCut
