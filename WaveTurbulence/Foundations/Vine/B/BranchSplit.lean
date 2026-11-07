/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Shape
import Mathlib.Tactic

/-!
# VINE-B: splitting the branching nodes of the skeleton

The branching nodes of `S = G_sk` are the branching nodes of `G_sb` (the retained ones, through `Φ.br`) together with
the interior branches `U_j \ {u1^j}` of the units (`branchSplit`).  Hence (TARGET L1954–L1957):
* `n_sk = n_sb + Σ_j n_(1)^j` (`order_split`, `clLocalOrder1`),
* `ζ(G_sk) = ζ(G_sb) · Π_j Π_{n ∈ U_j \ {u1^j}} (i ζ_n)` (`zeta_split`, `clLocalZeta`),
* every product over the branches of `S` splits into the non-hinge branches of `G_sb` and the full units `U_j`
  (`prod_split_atoms`), the form used for `ε` and for the phases.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset

variable {w : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden w}

/-- The interior branches `U_j \ {u1^j}` of a unit. -/
noncomputable abbrev inter (blk : J → CLBlock S) (j : J) : Finset (GBranch S.tree) :=
  clInteriorBranches (regionOf (blk j))

theorem mem_inter {j : J} {v : GBranch S.tree} : v ∈ inter blk j ↔ v ∈ (blk j).atoms ∧ v ≠ (blk j).upper := by
  unfold inter clInteriorBranches
  rw [Finset.mem_erase]
  tauto

theorem not_ret_inter {j : J} {v : GBranch S.tree} (hv : v ∈ inter blk j) : ¬ Ret blk v.toNode := by
  rw [mem_inter] at hv
  refine not_ret_of_interior (j := j) ((branch_real_iff _ _).mpr hv.1) fun h => hv.2 ?_
  exact Subtype.ext (congrArg (fun x : GNode S.tree => x.1) h)

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

/-- The reassembly map `G_sb`-branches ⊕ unit interiors → skeleton branches. -/
noncomputable def assemble : GBranch Gsb.tree ⊕ (Σ j, ↥(inter blk j)) → GBranch S.tree
  | .inl c => Φ.br c
  | .inr x => x.2.1

theorem assemble_bijective (hd : Disj blk) : Function.Bijective Φ.assemble := by
  constructor
  · rintro (c | ⟨j, v⟩) (c' | ⟨j', v'⟩) h
    · exact congrArg Sum.inl (Φ.br_inj h)
    · change Φ.br c = v'.1 at h
      exact (not_ret_inter v'.2 (h ▸ Φ.ret_br c)).elim
    · change v.1 = Φ.br c' at h
      exact (not_ret_inter v.2 (h.symm ▸ Φ.ret_br c')).elim
    · change v.1 = v'.1 at h
      have hv := mem_inter.mp v.2
      have hv' := mem_inter.mp v'.2
      have hj : j = j' := by
        refine interior_unique hd ((branch_real_iff _ _).mpr hv.1) (fun he => hv.2 ?_)
          ((branch_real_iff _ _).mpr (h ▸ hv'.1))
        exact Subtype.ext (congrArg (fun x : GNode S.tree => x.1) he)
      subst hj
      have : v = v' := Subtype.ext h
      subst this
      rfl
  · intro v
    rcases ret_or_interior (blk := blk) v.toNode with h | ⟨j, h1, h2⟩
    · obtain ⟨c, hc⟩ := Φ.exists_br h
      exact ⟨.inl c, hc⟩
    · refine ⟨.inr ⟨j, ⟨v, mem_inter.mpr ⟨(branch_real_iff _ _).mp h1, ?_⟩⟩⟩, rfl⟩
      rintro rfl
      exact h2 rfl

/-- `GBranch S ≃ GBranch G_sb ⊕ Σ_j (U_j \ {u1^j})`. -/
noncomputable def branchSplit (hd : Disj blk) : GBranch S.tree ≃ GBranch Gsb.tree ⊕ (Σ j, ↥(inter blk j)) :=
  (Equiv.ofBijective _ (Φ.assemble_bijective hd)).symm

theorem branchSplit_symm_inl (hd : Disj blk) (c : GBranch Gsb.tree) :
    (Φ.branchSplit hd).symm (.inl c) = Φ.br c := rfl

theorem branchSplit_symm_inr (hd : Disj blk) (x : Σ j, ↥(inter blk j)) :
    (Φ.branchSplit hd).symm (.inr x) = x.2.1 := rfl

theorem prod_split (hd : Disj blk) {M : Type*} [CommMonoid M] (f : GBranch S.tree → M) :
    ∏ v, f v = (∏ c : GBranch Gsb.tree, f (Φ.br c)) * ∏ j, ∏ v ∈ inter blk j, f v := by
  rw [← (Φ.branchSplit hd).symm.prod_comp, Fintype.prod_sum_type, Fintype.prod_sigma]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  exact Finset.prod_coe_sort (inter blk j) f

include Φ in
theorem order_split (hd : Disj blk) :
    S.order = Gsb.order + ∑ j, clLocalOrder1 (regionOf (blk j)) := by
  have h := Fintype.card_congr (Φ.branchSplit hd)
  rw [Fintype.card_sum, Fintype.card_sigma] at h
  rw [Garden.order, Garden.order, ← card_gbranch, ← card_gbranch, h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fintype.card_coe]
  rfl

include Φ in
theorem zeta_split (hd : Disj blk) : S.zeta = Gsb.zeta * ∏ j, clLocalZeta (regionOf (blk j)) := by
  unfold Garden.zeta clLocalZeta
  rw [Φ.prod_split hd]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Φ.br_node, Φ.sign]

/-! ## Hinges -/

/-- The hinge `u1^j` as a branch of `G_sb`. -/
noncomputable def hinge (hd : Disj blk) (j : J) : GBranch Gsb.tree :=
  Φ.brEquiv.symm ⟨(blk j).upper, ret_upper hd j⟩

theorem br_hinge (hd : Disj blk) (j : J) : Φ.br (Φ.hinge hd j) = (blk j).upper :=
  Φ.br_brEquiv_symm _

theorem upper_inj (hd : Disj blk) {j k : J} (h : (blk j).upper = (blk k).upper) : j = k := by
  by_contra hne
  exact Finset.disjoint_left.mp (hd j k hne) (upper_mem _) (h ▸ upper_mem _)

theorem hinge_inj (hd : Disj blk) : Function.Injective (Φ.hinge hd) := fun j k h =>
  upper_inj hd ((Φ.br_hinge hd j).symm.trans ((congrArg Φ.br h).trans (Φ.br_hinge hd k)))

/-- The hinges of `G_sb`. -/
noncomputable def hinges (hd : Disj blk) : Finset (GBranch Gsb.tree) := univ.image (Φ.hinge hd)

theorem mem_hinges (hd : Disj blk) (c : GBranch Gsb.tree) :
    c ∈ Φ.hinges hd ↔ ∃ j, Φ.br c = (blk j).upper := by
  unfold hinges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, -, rfl⟩
    exact ⟨j, Φ.br_hinge hd j⟩
  · rintro ⟨j, hj⟩
    refine ⟨j, Finset.mem_univ _, Φ.br_inj ?_⟩
    rw [Φ.br_hinge, hj]

theorem not_mem_hinges (hd : Disj blk) (c : GBranch Gsb.tree) :
    c ∉ Φ.hinges hd ↔ ∀ j, Φ.br c ≠ (blk j).upper := by
  rw [Φ.mem_hinges hd]
  push Not
  rfl

theorem prod_hinges (hd : Disj blk) {M : Type*} [CommMonoid M] (g : GBranch Gsb.tree → M) :
    ∏ c ∈ Φ.hinges hd, g c = ∏ j, g (Φ.hinge hd j) := by
  unfold hinges
  rw [Finset.prod_image fun j _ k _ h => Φ.hinge_inj hd h]

/-- Products over the skeleton branches split into the non-hinge branches of `G_sb` and the full units. -/
theorem prod_split_atoms (hd : Disj blk) {M : Type*} [CommMonoid M] (f : GBranch S.tree → M) :
    ∏ v, f v = (∏ c ∈ (univ : Finset (GBranch Gsb.tree)).filter (fun c => c ∉ Φ.hinges hd), f (Φ.br c)) *
      ∏ j, ∏ v ∈ (blk j).atoms, f v := by
  rw [Φ.prod_split hd, ← Finset.prod_filter_mul_prod_filter_not univ (fun c => c ∈ Φ.hinges hd)]
  have hf : (univ : Finset (GBranch Gsb.tree)).filter (fun c => c ∈ Φ.hinges hd) = Φ.hinges hd := by
    ext c; simp
  rw [hf, Φ.prod_hinges hd, mul_comm (∏ c ∈ _, _) _, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Φ.br_hinge, inter, clInteriorBranches]
  exact Finset.mul_prod_erase _ f (upper_mem _)

end SpliceShape

end WaveTurbulence.VineB
