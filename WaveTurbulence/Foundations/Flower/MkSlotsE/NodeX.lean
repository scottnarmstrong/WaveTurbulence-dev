/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.CentreForm

/-! # B3s-HELPER9 (MkSlotsE) 1: node-centre assignments restricted to the centred slots

Main's assembled expansion (`Represents.hasSum_node_slots`) inserts the node partition of unity
`∏_b χ_{x_b}(k_b)` over ALL branches `b` of `G_sb`, with `x` ranging over `nodeCentreSet cl` (`cl` the leaf-pair
centres). In the centre-indexed outer mode form (`MkSlotsI.CentreForm`) the chain families of the CENTRED slots
(non-root branches) are indexed by `X : CentredSlot G → ℤ^d` and the decoration weight carries
`chiX X = ∏_{c centred} χ_{X c}(k_c)`. The engine uses the SAME node centres: an assembled node-centre assignment `x`
belongs to the outer centre `X` iff it restricts to `X` on the centred slots (`ResX X x`). Then

* `hasSum_chiRes`: `Σ_{x, x|centred = X} ∏_b χ_{x_b}(k_b) = ∏_{c centred} χ_{X c}(k_c)` (the root branches are summed
  freely, `Σ_m χ_m = 1`);
* `tsum_ncard_ncsX_le`: `Σ_X #{x ∈ nodeCentreSet cl | x|centred = X} ≤ nodeBallCard d ^ m` — the outer centre sum is
  the engine's node-centre count, no new constant. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkSlotsI (CentredSlot chiX)
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsE

variable {w d : ℕ}

/-- A node-centre assignment `x` (on all branches) restricts to the outer centre `X` on the centred slots. -/
def ResX {G : Garden w} (X : CentredSlot G → (Fin d → ℤ)) (x : GBranch G.tree → (Fin d → ℤ)) : Prop :=
  ∀ c : CentredSlot G, x c.1 = X c

instance {G : Garden w} (X : CentredSlot G → (Fin d → ℤ)) (x : GBranch G.tree → (Fin d → ℤ)) :
    Decidable (ResX X x) := by
  unfold ResX; infer_instance

/-- The restriction of `x` to the centred slots. -/
def resC {G : Garden w} (x : GBranch G.tree → (Fin d → ℤ)) : CentredSlot G → (Fin d → ℤ) := fun c => x c.1

theorem resX_iff {G : Garden w} (X : CentredSlot G → (Fin d → ℤ)) (x : GBranch G.tree → (Fin d → ℤ)) :
    ResX X x ↔ resC x = X :=
  ⟨fun h => funext fun c => h c, fun h c => congrFun h c⟩

theorem resX_resC {G : Garden w} (x : GBranch G.tree → (Fin d → ℤ)) : ResX (resC x) x := fun _ => rfl

/-! ## The restricted partition of unity -/

section Partition

variable {G : Garden w} (X : CentredSlot G → (Fin d → ℤ)) (k : GBranch G.tree → Mom d)

/-- The per-branch factor of the restricted partition: `χ_m(k_b)` at a root branch, `[m = X b] χ_m(k_b)` at a centred
branch. -/
def chiRes (b : GBranch G.tree) (m : Fin d → ℤ) : ℝ :=
  if h : b.1.2 ≠ [] then (if m = X ⟨b, h⟩ then chi d m (k b) else 0) else chi d m (k b)

theorem chiRes_nonneg (b : GBranch G.tree) (m : Fin d → ℤ) : 0 ≤ chiRes X k b m := by
  unfold chiRes
  split_ifs
  · exact chi_nonneg d _ _
  · exact le_rfl
  · exact chi_nonneg d _ _

theorem chiRes_le (b : GBranch G.tree) (m : Fin d → ℤ) : chiRes X k b m ≤ chi d m (k b) := by
  unfold chiRes
  split_ifs
  · exact le_rfl
  · exact chi_nonneg d _ _
  · exact le_rfl

theorem prod_chiRes (x : GBranch G.tree → (Fin d → ℤ)) :
    ∏ b, chiRes X k b (x b) = if ResX X x then ∏ b, chi d (x b) (k b) else 0 := by
  by_cases hx : ResX X x
  · rw [if_pos hx]
    refine Finset.prod_congr rfl fun b _ => ?_
    unfold chiRes
    split_ifs with h h'
    · rfl
    · exact absurd (hx ⟨b, h⟩) h'
    · rfl
  · rw [if_neg hx]
    obtain ⟨c, hc⟩ : ∃ c : CentredSlot G, x c.1 ≠ X c := by
      by_contra h
      push_neg at h
      exact hx h
    refine Finset.prod_eq_zero (Finset.mem_univ c.1) ?_
    unfold chiRes
    rw [dif_pos c.2, if_neg hc]

theorem tsum_chiRes (b : GBranch G.tree) :
    ∑' m, chiRes X k b m = if h : b.1.2 ≠ [] then chi d (X ⟨b, h⟩) (k b) else 1 := by
  by_cases h : b.1.2 ≠ []
  · rw [dif_pos h]
    have e : ∀ m, chiRes X k b m = if m = X ⟨b, h⟩ then chi d (X ⟨b, h⟩) (k b) else 0 := by
      intro m
      unfold chiRes
      rw [dif_pos h]
      split_ifs with hm
      · rw [hm]
      · rfl
    simp_rw [e]
    exact tsum_ite_eq _ _
  · rw [dif_neg h]
    have e : ∀ m, chiRes X k b m = chi d m (k b) := by
      intro m
      unfold chiRes
      rw [dif_neg h]
    simp_rw [e]
    exact (hasSum_chi d (k b)).tsum_eq

theorem summable_chiRes (b : GBranch G.tree) : Summable fun m => ‖chiRes X k b m‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) (hasSum_chi d (k b)).summable
  rw [Real.norm_of_nonneg (chiRes_nonneg X k b m)]
  exact chiRes_le X k b m

/-- **The restricted node partition**: `Σ_{x, x|centred = X} ∏_b χ_{x_b}(k_b) = ∏_{c centred} χ_{X c}(k_c)`. -/
theorem hasSum_chiRes :
    HasSum (fun x : GBranch G.tree → (Fin d → ℤ) => if ResX X x then ∏ b, chi d (x b) (k b) else 0)
      (∏ c : CentredSlot G, chi d (X c) (k c.1)) := by
  have h := (VineEstS3.Eng.hasSum_pi_prod (M := Fin d → ℤ) (𝕜 := ℝ) (chiRes X k) (summable_chiRes X k)).2
  simp only [prod_chiRes, tsum_chiRes] at h
  convert h using 1
  rw [Fintype.prod_dite]
  simp

/-- The restricted node partition, complex form, at slot momenta. -/
theorem hasSum_chiResC :
    HasSum (fun x : GBranch G.tree → (Fin d → ℤ) =>
        (if ResX X x then (1 : ℂ) else 0) * ((∏ b, chi d (x b) (k b) : ℝ) : ℂ))
      (∏ c : CentredSlot G, chiC d (X c) (k c.1)) := by
  have h := Complex.ofRealCLM.hasSum (hasSum_chiRes X k)
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_prod] at h
  convert h using 1
  · funext x
    by_cases hx : ResX X x
    · simp [hx, Complex.ofReal_prod]
    · simp [hx]
  · simp [chiC]

end Partition

/-! ## The count of the restricted node centres -/

section Count

variable {G : Garden w}

/-- The node-centre assignments compatible with the leaf centres `cl` that restrict to `X`. -/
def ncsX (cl : GLeaf G.tree → (Fin d → ℤ)) (X : CentredSlot G → (Fin d → ℤ)) :
    Set (GBranch G.tree → (Fin d → ℤ)) :=
  nodeCentreSet cl ∩ {x | ResX X x}

theorem ncsX_finite (cl : GLeaf G.tree → (Fin d → ℤ)) (X : CentredSlot G → (Fin d → ℤ)) :
    (ncsX cl X).Finite :=
  (nodeCentreSet_finite_card cl).1.subset Set.inter_subset_left

open scoped Classical in
theorem ncard_eq_tsum_of_finite {α : Type*} {s : Set α} (hs : s.Finite) :
    ((s.ncard : ℕ) : ℝ≥0∞) = ∑' x, if x ∈ s then (1 : ℝ≥0∞) else 0 := by
  rw [tsum_eq_sum (s := hs.toFinset) (fun x hx => by
    rw [if_neg]; exact fun h => hx ((Set.Finite.mem_toFinset hs).2 h))]
  rw [Finset.sum_ite_of_true (fun x hx => (Set.Finite.mem_toFinset hs).1 hx), Finset.sum_const, nsmul_eq_mul,
    mul_one, Set.ncard_eq_toFinset_card _ hs]

open scoped Classical in
/-- **The outer centre sum is the node-centre count**: `Σ_X #(nodeCentreSet cl ∩ {x|centred = X}) ≤ nodeBallCard^m`. -/
theorem tsum_ncard_ncsX_le (cl : GLeaf G.tree → (Fin d → ℤ)) :
    ∑' X : CentredSlot G → (Fin d → ℤ), (((ncsX cl X).ncard : ℕ) : ℝ≥0∞) ≤
      ((nodeBallCard d ^ ∑ j, (G.tree j).order : ℕ) : ℝ≥0∞) := by
  obtain ⟨hF, hC⟩ := nodeCentreSet_finite_card cl
  simp_rw [ncard_eq_tsum_of_finite (ncsX_finite cl _)]
  rw [ENNReal.tsum_comm]
  have hfib : ∀ x : GBranch G.tree → (Fin d → ℤ),
      ∑' X : CentredSlot G → (Fin d → ℤ), (if x ∈ ncsX cl X then (1 : ℝ≥0∞) else 0) =
        if x ∈ nodeCentreSet cl then 1 else 0 := by
    intro x
    rw [tsum_eq_single (resC x)]
    · by_cases hx : x ∈ nodeCentreSet cl
      · rw [if_pos hx, if_pos ⟨hx, resX_resC x⟩]
      · rw [if_neg hx, if_neg (fun h => hx h.1)]
    · intro X hX
      rw [if_neg]
      rintro ⟨-, h⟩
      exact hX ((resX_iff X x).1 h).symm
  simp_rw [hfib]
  rw [← ncard_eq_tsum_of_finite hF]
  exact_mod_cast hC

end Count

end WaveTurbulence.Flower.MkSlotsE
