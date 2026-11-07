/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.PointA
public import WaveTurbulence.Foundations.Stage1.Represents.RepOuterM
import Mathlib.Tactic

/-!
# VINE-B: the pointwise factorization, part B (outer slot modes, routing, regional slots)

* `amp_glue`: the outer slot momenta of a glued decoration are the slot momenta of `G_sb`;
* `modes_glue`: the outer slot modes `e^{πi(m_0 t + m_1 s)}` at the skeleton clocks are S2's `routedPhase` on `G_sb`
  times, per unit, V5's modulation `lowModC` at the lower joint with `λ_j = modLam` (finding F-LOWCLOCK, R58);
* `regional_glue`: the regional slot kernels of unit `j` are V5's `clLocalStarProduct` with `F = h(·, j₁, j₁)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden w}

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

theorem amp_glue (hS : S.IsPlain) (hSb : Gsb.IsPlain) (L : ℝ) (base : Mom d)
    (z : GNode Gsb.tree → (Fin d → ℤ)) (κs : ∀ j, ↥(clLocalSupport (regionOf (blk j))) → (Fin d → ℤ))
    (amp : ReplacementSlot Gsb → Mom d → ℂ) :
    ∏ s', amp s' (base + latticePoint L (Φ.glueFun z κs (slotNode hS (Φ.iota hS hSb s')))) =
      ∏ s', amp s' (base + latticePoint L (z (slotNode hSb s'))) := by
  refine Finset.prod_congr rfl fun s' _ => ?_
  rw [← Φ.node_slotNode, Φ.glue_node]

theorem exp_ite_prod {ι : Type*} (s : Finset ι) (P : ι → Prop) [DecidablePred P] (a : ι → ℝ) :
    ∏ i ∈ s, (if P i then Complex.exp (((a i : ℝ) : ℂ) * Complex.I) else 1) =
      Complex.exp ((((∑ i ∈ s, if P i then a i else 0) : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- **The routing of the outer slot modes** (R58, INTERFACE v2). -/
theorem modes_glue (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) (tt : Fin w → ℝ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (τ' : GBranch Gsb.tree → ℝ)
    (τs : ∀ j, CLInternalTime (regionOf (blk j))) :
    ∏ s', fsPhase (frq s') (slotTs hS tt (Φ.glueTime hd τ' τs) (Φ.iota hS hSb s')) =
      routedPhase frq (Φ.route hS hSb) tt τ' *
        ∏ j, lowModC (regionOf (blk j)) (modLam frq (Φ.route hS hSb) j : ℝ) (Φ.clocks τ' j) (τs j) := by
  classical
  set τ := Φ.glueTime hd τ' τs
  set rt := Φ.route hS hSb
  -- the clock of the lower joint of unit `j`
  have hb : ∀ j, clLocalClock (regionOf (blk j)) (Φ.clocks τ' j) (τs j) (blk j).lower = τ (blk j).lower :=
    fun j => Φ.clLocalClock_glue hd τ' τs j (lower_mem _)
  have hfac : ∀ s' i, Complex.exp (((Real.pi * (frq s' i : ℝ) * slotTs hS tt τ (Φ.iota hS hSb s') i : ℝ) : ℂ) *
      Complex.I) =
      (match rt s' i with
        | Sum.inl y => Complex.exp (((Real.pi * (frq s' i : ℝ) * clockOf Gsb tt τ' y : ℝ) : ℂ) * Complex.I)
        | Sum.inr _ => 1) *
      ∏ j, (if rt s' i = Sum.inr j then
        Complex.exp (((Real.pi * (frq s' i : ℝ) * τ (blk j).lower : ℝ) : ℂ) * Complex.I) else 1) := by
    intro s' i
    rcases hr : rt s' i with y | j0
    · simp only [reduceCtorEq, ite_false, Finset.prod_const_one, mul_one]
      have h := Φ.route_inl hS hSb hr
      show Complex.exp (((Real.pi * (frq s' i : ℝ) * clockOf S tt τ (argSrc hS (Φ.iota hS hSb s') i) : ℝ) : ℂ) *
        Complex.I) = _
      rw [h, Φ.clockOf_srcMap hd tt τ' τs y]
    · simp only [one_mul, Sum.inr.injEq]
      rw [Finset.prod_ite_eq Finset.univ j0, ite_eq_left_iff.mpr (fun h => absurd (Finset.mem_univ _) h)]
      have h := Φ.route_inr hS hSb hr
      show Complex.exp (((Real.pi * (frq s' i : ℝ) * clockOf S tt τ (argSrc hS (Φ.iota hS hSb s') i) : ℝ) : ℂ) *
        Complex.I) = _
      rw [h]
      rfl
  simp_rw [fsPhase_eq_prod_fin2, hfac, Finset.prod_mul_distrib]
  unfold routedPhase
  congr 1
  · refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => ?_
    generalize rt s i = r
    cases r <;> rfl
  have e : ∀ s' : ReplacementSlot Gsb, ∏ i : Fin 2, ∏ j, (if rt s' i = Sum.inr j then
        Complex.exp (((Real.pi * (frq s' i : ℝ) * τ (blk j).lower : ℝ) : ℂ) * Complex.I) else 1) =
      ∏ j, ∏ i : Fin 2, (if rt s' i = Sum.inr j then
        Complex.exp (((Real.pi * (frq s' i : ℝ) * τ (blk j).lower : ℝ) : ℂ) * Complex.I) else 1) :=
    fun s' => Finset.prod_comm
  simp_rw [e]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp_rw [← Finset.prod_product']
  rw [exp_ite_prod]
  unfold lowModC modLam
  rw [hb j]
  congr 3
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

theorem parentClockWith_eq_parentClock (tt : Fin w → ℝ) (top : ℝ) (τ : GBranch S.tree → ℝ) (x : GNode S.tree)
    (hn : x.1.2 ≠ []) : parentClockWith tt τ x = parentClock top τ x := by
  rw [parentClockWith_nonroot _ _ x hn, parentClock_nonroot _ _ x hn]

/-- **The regional slots of unit `j`** are V5's `clLocalStarProduct` (P* lemma 1). -/
theorem regional_glue (hd : Disj blk) (hS : S.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ) (base : Mom d)
    (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (tt : Fin w → ℝ) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j))) (j : J) :
    ∏ s ∈ regSlots blk hS j, slotFn D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h)
        layer hLayer s (slotTs hS tt (Φ.glueTime hd τ' τs) s)
        (base + latticePoint L (Φ.glueFun z.1 (fun j => (κs j).1) (slotNode hS s))) =
      clLocalStarProduct D hS (regionOf (blk j)) L γ δ (fun q => h q (blk j).upper.1.1 (blk j).upper.1.1)
        layer hLayer base (clExtendIndices (regionOf (blk j)) (κs j).1) (Φ.clocks τ' j) (τs j) := by
  set τ := Φ.glueTime hd τ' τs
  set κ := Φ.glueFun z.1 (fun j => (κs j).1)
  rw [Φ.locDec_eq hd hL base z κs j, Φ.clocks_eq_external hd τ' τs j, ← Φ.restrict_glueTime hd τ' τs j,
    clLocalStarProduct_restrict (blk j).isBlock D hS (regionOf (blk j)) L γ δ 0, prod_regSlots]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hf : Mole.IsInternalLeaf S (blk j).atoms (p.firstLeaf hS) := by
      classical
      exact (Finset.mem_filter.mp hp).2
    have hs := (second_internal_iff hS (blk j).atoms p).mpr hf
    obtain ⟨_, hn1, _, _⟩ := hf
    obtain ⟨_, hn2, _, _⟩ := hs
    simp only [slotFn, slotTs, argSrc, Fin.isValue, ↓reduceIte, one_ne_zero, slotNode]
    rw [pstar_couple D hS layer hLayer h (blk j) hp, ← parentClockWith_eq_clockOf, ← parentClockWith_eq_clockOf,
      parentClockWith_eq_parentClock tt 0 τ _ hn1, parentClockWith_eq_parentClock tt 0 τ _ hn2]
    rfl
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hvm := mem_inter.mp hv
    obtain ⟨hn, -⟩ := real_parent (blk j) ((branch_real_iff _ _).mpr hvm.1)
      (fun he => hvm.2 (Subtype.ext (congrArg (fun x : GNode S.tree => x.1) he)))
    simp only [slotFn, slotTs, argSrc, Fin.isValue, ↓reduceIte, one_ne_zero, slotNode]
    rw [pstar_chain D hS layer hLayer h (blk j) hvm.1, ← parentClockWith_eq_clockOf,
      parentClockWith_eq_parentClock tt 0 τ _ hn]
    rfl

end SpliceShape

end WaveTurbulence.VineB
