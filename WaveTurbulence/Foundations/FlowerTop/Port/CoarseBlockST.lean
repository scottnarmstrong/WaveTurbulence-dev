/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.CoarseAsm1ST
/-! # FLOWER-P5: block integrals over the free clocks (copy-and-thread of the provider's `prod_block_integral`) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.CoarseSpliced Finset MeasureTheory Set
open scoped Classical

/-- Integral over a box of the coordinates of `S i` (a subset of the free coordinates) agrees with the
integral over the box of the corresponding coordinates in the free subtype. -/
theorem setIntegral_pi_free {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P] (a : X → ℝ) (T : Finset X) (hT : ∀ v ∈ T, P v)
    (g : (T → ℝ) → ℝ) :
    ∫ s' in Set.pi univ (fun v' : ((T.subtype P : Finset {x // P x})) => Icc (a v'.1.1) (a v'.1.1 + 1)),
      g (fun v : T => s' ⟨⟨v.1, hT v.1 v.2⟩, Finset.mem_subtype.mpr v.2⟩) =
    ∫ s in Set.pi univ (fun v : T => Icc (a v.1) (a v.1 + 1)), g s := by
  let e : ((T.subtype P : Finset {x // P x})) ≃ T :=
    { toFun := fun v' => ⟨v'.1.1, Finset.mem_subtype.mp v'.2⟩
      invFun := fun v => ⟨⟨v.1, hT v.1 v.2⟩, Finset.mem_subtype.mpr v.2⟩
      left_inv := fun v' => by ext; rfl
      right_inv := fun v => by ext; rfl }
  have hmp := measurePreserving_piCongrLeft (fun _ : T => (volume : Measure ℝ)) e
  rw [← integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc),
    ← integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Icc)]
  have := hmp.integral_comp' (f := MeasurableEquiv.piCongrLeft (fun _ : T => ℝ) e)
    (fun s => (Set.pi univ (fun v : T => Icc (a v.1) (a v.1 + 1))).indicator g s)
  have this' : ∫ x, (Set.pi univ (fun v : T => Icc (a v.1) (a v.1 + 1))).indicator g
      ((MeasurableEquiv.piCongrLeft (fun _ : T => ℝ) e) x) = ∫ y, (Set.pi univ (fun v : T => Icc (a v.1) (a v.1 + 1))).indicator g y := this
  rw [← this']
  congr 1
  funext s'
  have hmem : (MeasurableEquiv.piCongrLeft (fun _ : T => ℝ) e s') ∈
      Set.pi univ (fun v : T => Icc (a v.1) (a v.1 + 1)) ↔
      s' ∈ Set.pi univ (fun v' : ((T.subtype P : Finset {x // P x})) => Icc (a v'.1.1) (a v'.1.1 + 1)) := by
    simp only [Set.mem_pi, mem_univ, forall_true_left, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
    constructor
    · intro h v'
      have := h (e v')
      simpa [e] using this
    · intro h v
      have := h (e.symm v)
      simpa [e] using this
  by_cases h : s' ∈ Set.pi univ (fun v' : ((T.subtype P : Finset {x // P x})) => Icc (a v'.1.1) (a v'.1.1 + 1))
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.2 h)]
    congr 1
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.1 h'))]

variable {w : ℕ} {G : Garden w} {ι : Type*} [DecidableEq ι]

/-- **Product over disjoint blocks of free coordinates** (the stub coordinates are held at their fixed times). -/
theorem prod_block_integral_free (layer : GBranch G.tree → ℕ) (fix : GBranch G.tree → Option ℝ)
    (S : ι → Finset (GBranch G.tree)) (hfree : ∀ i, ∀ v ∈ S i, fix v = none)
    (g : (i : ι) → (S i → ℝ) → ℝ) (I : Finset ι)
    (hS : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) :
    ∫ τ in freeBox G layer fix, ∏ i ∈ I, g i (fun v : S i => G.extendFix fix τ v.1) =
      ∏ i ∈ I, ∫ s in Set.pi univ (fun v : S i => Icc (layer v.1 : ℝ) (layer v.1 + 1)), g i s := by
  let P : GBranch G.tree → Prop := fun b => fix b = none
  let S' : ι → Finset {b : GBranch G.tree // fix b = none} := fun i => (S i).subtype P
  let g' : (i : ι) → (S' i → ℝ) → ℝ := fun i s' =>
    g i (fun v : S i => s' ⟨⟨v.1, hfree i v.1 v.2⟩, Finset.mem_subtype.mpr v.2⟩)
  have hS' : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S' i) (S' j) := by
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Finset.disjoint_left.mp (hS i hi j hj hij) (Finset.mem_subtype.mp hx) (Finset.mem_subtype.mp hx')
  have key := prod_block_integral (X := {b : GBranch G.tree // fix b = none})
    (fun v => (layer v.1 : ℝ)) S' g' I hS'
  have hL : ∫ τ in freeBox G layer fix, ∏ i ∈ I, g i (fun v : S i => G.extendFix fix τ v.1) =
      ∫ τ in ubox (fun v : {b : GBranch G.tree // fix b = none} => (layer v.1 : ℝ)),
        ∏ i ∈ I, g' i (fun v : S' i => τ v.1) := by
    refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Icc) (fun τ _ => ?_)
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [g']
    congr 1
    funext v
    exact extendFix_free fix τ v.1 (hfree i v.1 v.2)
  rw [hL, key]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have := setIntegral_pi_free P (fun b => (layer b : ℝ)) (S i) (hfree i) (g i)
  exact this

end WaveTurbulence.FlowerP5
