/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.KernelPolarize
public import WaveTurbulence.Foundations.Spine.RootFormSum
/-! AMEND6' (design P*, identity (M), kernel level): multiplying the kernel by the signed root coordinate
`sigma_{j0} k_{j0}^i` equals the sum over the positive input leaves of the kernels with the profile at that
leaf multiplied by `c_a k_a^i`, `c_a = [a in T_{j0}] - [partner(a) in T_{j0}]`. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem kernelLeaves_rootform {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (hp : LG.garden.IsPlain)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (H : LeafProfiles w d) (c : (Fin w × TTree.Path) → ℝ) (j0 : Fin w) (i : Fin d)
    (hc : ∀ ℓ ∈ inputLeaves LG.garden, c ℓ.1 =
      (if ℓ.1.1 = j0 then (1 : ℝ) else 0) - (if (LG.garden.pair ℓ).1.1 = j0 then (1 : ℝ) else 0))
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hH : ∀ l ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H l.1 (k₀ + latticePoint L n)|)
    (hV : ∀ l ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ =>
      |c l.1 * (k₀ + latticePoint L n) i * H l.1 (k₀ + latticePoint L n)|) :
    ((((nodeSign LG.garden.sig (GNode.root LG.garden.tree j0).1 : ℤˣ) : ℤ) : ℝ) *
        (k₀ + latticePoint L (nroot j0)) i : ℝ) * kernelLeaves L γ δ LG H up s k₀ nroot nfl =
      ∑ a : ActualInputLeaves LG.garden, kernelLeaves L γ δ LG
        (Function.update H a.1.1 (fun x => c a.1.1 * x i * H a.1.1 x)) up s k₀ nroot nfl := by
  classical
  set V : LeafProfiles w d := fun addr x => c addr * x i * H addr x with hVdef
  rw [show (Function.update H) = (Function.update H) from rfl]
  have hVs : ∀ l ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |V l.1 (k₀ + latticePoint L n)| :=
    fun l hl => hV l hl
  have hrw : ∀ a : ActualInputLeaves LG.garden,
      kernelLeaves L γ δ LG (Function.update H a.1.1 (fun x => c a.1.1 * x i * H a.1.1 x)) up s k₀ nroot nfl =
        kernelLeaves L γ δ LG (Function.update H a.1.1 (V a.1.1)) up s k₀ nroot nfl := fun a => rfl
  simp_rw [hrw]
  rw [sum_update_kernel L γ δ LG hlone H V up s k₀ nroot nfl hH hVs]
  unfold kernelLeaves
  rw [mul_left_comm, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun κ => ?_
  set k := cosetDecoration LG.garden L k₀ κ.1 with hk
  have hdec : IsDecoration LG.garden k := isDecoration_cosetDecoration LG.garden L k₀ κ.1 κ.2.1
  have hroot : k (GNode.root LG.garden.tree j0) = k₀ + latticePoint L (nroot j0) := by
    change k₀ + latticePoint L (κ.1 (GNode.root LG.garden.tree j0)) = _
    rw [κ.2.2.1 j0]
  have hsum := congrArg (fun v : Mom d => v i) (root_sum_inputs LG.garden hp k hdec j0)
  simp only [hroot, PiLp.smul_apply, zsmul_eq_mul, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply] at hsum
  set S := inputLeaves LG.garden
  have key : ∀ a ∈ S, (V a.1 (k a.toNode) : ℂ) * ∏ l ∈ S.erase a, (H l.1 (k l.toNode) : ℂ) =
      ((c a.1 * k a.toNode i : ℝ) : ℂ) * ∏ l ∈ S, (H l.1 (k l.toNode) : ℂ) := by
    intro a ha
    rw [← Finset.mul_prod_erase S (fun l => (H l.1 (k l.toNode) : ℂ)) ha]
    simp only [hVdef]
    push_cast
    ring
  rw [Finset.sum_congr rfl key, ← Finset.sum_mul]
  have hs2 : ((((nodeSign LG.garden.sig (GNode.root LG.garden.tree j0).1 : ℤˣ) : ℤ) : ℝ) *
        (k₀ + latticePoint L (nroot j0)) i : ℝ) = ∑ a ∈ S, c a.1 * k a.toNode i := by
    rw [hsum]
    refine sum_congr rfl fun a ha => ?_
    rw [hc a ha]
    push_cast
    ring
  rw [hs2]
  push_cast
  ring

end WaveTurbulence.LGSpine
