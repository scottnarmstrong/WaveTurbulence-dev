/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLIngredientJunction
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLBoundaryIdentities

/-! # The common momentum gap of consecutive CL ingredients -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree
variable {w d : ℕ} {G : Garden w}

theorem cl_lower_gap {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : CLRegionData G U a b) (k : GNode G.tree → Mom d) (hk : IsDecoration G k) :
    ((G.sign b.toNode : ℤ) : ℝ) • (k b.toNode-k (b.child R.kept)) =
      k (b.child R.positive)-k (b.child R.negative) := by
  have h0 := (Mole.slotSum_eq_zero_iff G k b).mpr (hk.1 b)
  have hpn : R.positive ≠ R.negative := R.distinct
  have hkp : R.kept ≠ R.positive := fun h => ((R.lower_excluded R.positive).mpr (Or.inl rfl)) h.symm
  have hkn : R.kept ≠ R.negative := fun h => ((R.lower_excluded R.negative).mpr (Or.inr rfl)) h.symm
  have hu : (Finset.univ : Finset (Fin 3)) = {R.kept,R.positive,R.negative} := by
    ext i
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    by_cases hi : i = R.kept
    · exact Or.inl hi
    · exact Or.inr ((R.lower_excluded i).mp hi)
  unfold Mole.slotSum at h0
  rw [Fin.sum_univ_succ] at h0
  rw [hu,Finset.sum_insert (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; exact ⟨hkp,hkn⟩),
    Finset.sum_pair hpn] at h0
  change Mole.slotWeight G b 0 • k b.toNode +
    (Mole.slotWeight G b R.kept.succ • k (b.child R.kept) +
      (Mole.slotWeight G b R.positive.succ • k (b.child R.positive) +
        Mole.slotWeight G b R.negative.succ • k (b.child R.negative))) = 0 at h0
  rw [slotWeight_parent,slotWeight_child,slotWeight_child,slotWeight_child,
    Mole.outer_child_sign G b R.kept R.kept_ne_middle,R.positive_sign,R.negative_sign] at h0
  simp only [Units.val_one,Units.val_neg,Int.cast_one,Int.cast_neg,one_smul,neg_smul,neg_neg] at h0
  rw [smul_sub]
  have he : ((G.sign b.toNode : ℤ) : ℝ) • k b.toNode -
      ((G.sign b.toNode : ℤ) : ℝ) • k (b.child R.kept) -
      (k (b.child R.positive)-k (b.child R.negative)) = 0 := by
    calc
      _ = ((G.sign b.toNode : ℤ) : ℝ) • k b.toNode +
        (-(((G.sign b.toNode : ℤ) : ℝ) • k (b.child R.kept)) +
          (-k (b.child R.positive)+k (b.child R.negative))) := by abel
      _ = 0 := h0
  exact sub_eq_zero.mp he

/-- With positive/negative lower children ordered by their actual signs, the
signed gap is unchanged at each bottom-to-top ingredient junction, including
zero-gap decorations. Nonzero propagation is a separate case distinction. -/
theorem cl_ingredient_gap_eq {A B : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hA : G.molecule.IsBlock A c a) (hB : G.molecule.IsBlock B b c)
    (RA : CLRegionData G A c a) (RB : CLRegionData G B b c)
    (hi : A ∩ B = {c}) (k : GNode G.tree → Mom d) (hk : IsDecoration G k) :
    k (a.child RA.positive)-k (a.child RA.negative) =
      k (c.child RB.positive)-k (c.child RB.negative) := by
  rw [← cl_boundary_momentum hA RA k hk,cl_ingredient_shared_child hA hB RA RB hi]
  exact cl_lower_gap RB k hk

end WaveTurbulence.RegRed
