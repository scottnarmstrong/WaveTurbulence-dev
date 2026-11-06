/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CentralDiffC
public import WaveTurbulence.Foundations.Spine.WeightedLeafKernel
public import WaveTurbulence.Foundations.Spine.SingleLeafDerivative
/-! AMEND6' (design P*, identity (L) + (C)): the kernel `kernelLeaves` is multilinear in the profiles at its
input leaves, so the sum over input leaves of the kernels with ONE profile replaced by `V` (and the rest `H`)
is exactly the central-difference combination `sum_k (w_k / lam) K[H + lam (k - M) V]` of `2M + 1` kernels with
the ordinary (leaf-uniform) profile `H + lam (k - M) V`, whenever `M >= 1` and `#inputLeaves <= 2 M`. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset CentralDiff

/-- Common form of the one-leaf-replaced kernels: `sum_a K[H with V at a] = pre * sum_kappa f(kappa) * sum_a V_a prod_{l != a} H_l`
(the decoration sum interchanged with the finite sum over the input leaves). -/
theorem sum_update_kernel {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (H V : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hH : ∀ l ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H l.1 (k₀ + latticePoint L n)|)
    (hV : ∀ l ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |V l.1 (k₀ + latticePoint L n)|) :
    ∑ l : ActualInputLeaves LG.garden,
        kernelLeaves L γ δ LG (Function.update H l.1.1 (V l.1.1)) up s k₀ nroot nfl =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl,
          ((epsDec LG.garden κ.1 : ℂ) *
            phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1)) *
          ∑ a ∈ inputLeaves LG.garden, ((V a.1 (cosetDecoration LG.garden L k₀ κ.1 a.toNode) : ℂ) *
            ∏ l ∈ (inputLeaves LG.garden).erase a,
              (H l.1 (cosetDecoration LG.garden L k₀ κ.1 l.toNode) : ℂ)) := by
  classical
  set S := inputLeaves LG.garden with hS
  have hupd : ∀ a ∈ S, ∀ l ∈ S, Summable fun n : Fin d → ℤ =>
      |Function.update H a.1 (V a.1) l.1 (k₀ + latticePoint L n)| := by
    intro a _ l hl
    by_cases hla : l.1 = a.1
    · simp only [hla, Function.update_self]
      have : l = a := Subtype.ext hla
      subst this
      exact hV l hl
    · simp only [Function.update_of_ne hla]
      exact hH l hl
  have hA : ∀ a ∈ S, Summable fun κ : GenDecoration LG.garden d nroot nfl =>
      ((epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1)) *
        ∏ l ∈ S, ((Function.update H a.1 (V a.1)) l.1 (cosetDecoration LG.garden L k₀ κ.1 l.toNode) : ℂ) :=
    fun a ha => summable_leafKernel_summand L γ δ LG _ up s k₀ nroot nfl hlone (hupd a ha)
  have e1 : ∀ a : ActualInputLeaves LG.garden,
      kernelLeaves L γ δ LG (Function.update H a.1.1 (V a.1.1)) up s k₀ nroot nfl =
        (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl,
          ((epsDec LG.garden κ.1 : ℂ) *
            phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1)) *
            ∏ l ∈ S, ((Function.update H a.1.1 (V a.1.1)) l.1
              (cosetDecoration LG.garden L k₀ κ.1 l.toNode) : ℂ) := fun a => rfl
  simp_rw [e1]
  rw [← mul_sum]
  congr 1
  rw [Finset.sum_coe_sort S (fun a => ∑' κ : GenDecoration LG.garden d nroot nfl,
      ((epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1)) *
        ∏ l ∈ S, ((Function.update H a.1 (V a.1)) l.1 (cosetDecoration LG.garden L k₀ κ.1 l.toNode) : ℂ))]
  rw [← Summable.tsum_finsetSum hA]
  refine tsum_congr fun κ => ?_
  rw [← mul_sum]
  congr 1
  refine sum_congr rfl fun a ha => ?_
  rw [← Finset.mul_prod_erase S _ ha]
  simp only [Function.update_self]
  congr 1
  refine prod_congr rfl fun l hl => ?_
  have hla : l.1 ≠ a.1 := fun h => (Finset.ne_of_mem_erase hl) (Subtype.ext h)
  simp only [Function.update_of_ne hla]

/-- The generic tsum form of the polarization. -/
theorem tsum_polarize {Ω ι : Type*} [DecidableEq ι] (S : Finset ι) (M : ℕ) (hM : 1 ≤ M)
    (hS : S.card ≤ 2 * M) (lam : ℝ) (hlam : lam ≠ 0) (f : Ω → ℂ) (x y : Ω → ι → ℂ)
    (hsumK : ∀ k ∈ range (2 * M + 1), Summable fun ω =>
      f ω * ∏ l ∈ S, (x ω l + ((lam * ((k : ℝ) - M) : ℝ) : ℂ) * y ω l)) :
    ∑' ω, f ω * ∑ a ∈ S, (y ω a * ∏ l ∈ S.erase a, x ω l) =
      ∑ k ∈ range (2 * M + 1), ((cw M k / lam : ℝ) : ℂ) *
        ∑' ω, f ω * ∏ l ∈ S, (x ω l + ((lam * ((k : ℝ) - M) : ℝ) : ℂ) * y ω l) := by
  have hpt : ∀ ω, f ω * ∑ a ∈ S, (y ω a * ∏ l ∈ S.erase a, x ω l) =
      ∑ k ∈ range (2 * M + 1), ((cw M k / lam : ℝ) : ℂ) *
        (f ω * ∏ l ∈ S, (x ω l + ((lam * ((k : ℝ) - M) : ℝ) : ℂ) * y ω l)) := by
    intro ω
    rw [polarization_extraction S M hM hS (x ω) (y ω) lam hlam, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hpt]
  rw [Summable.tsum_finsetSum fun k hk => (hsumK k hk).mul_left _]
  refine sum_congr rfl fun k _ => ?_
  rw [tsum_mul_left]

theorem prod_add_cast {ι : Type*} (S : Finset ι) (a b : ι → ℝ) (μ : ℝ) :
    ∏ l ∈ S, ((a l + μ * b l : ℝ) : ℂ) = ∏ l ∈ S, ((a l : ℂ) + (μ : ℂ) * (b l : ℂ)) := by
  refine prod_congr rfl fun l _ => ?_
  push_cast
  rfl

theorem kernelLeaves_polarize {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (H V : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hH : ∀ l ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H l.1 (k₀ + latticePoint L n)|)
    (hV : ∀ l ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |V l.1 (k₀ + latticePoint L n)|)
    (M : ℕ) (hM : 1 ≤ M) (hcard : (inputLeaves LG.garden).card ≤ 2 * M) (lam : ℝ) (hlam : lam ≠ 0) :
    ∑ l : ActualInputLeaves LG.garden,
        kernelLeaves L γ δ LG (Function.update H l.1.1 (V l.1.1)) up s k₀ nroot nfl =
      ∑ k ∈ range (2 * M + 1), ((cw M k / lam : ℝ) : ℂ) *
        kernelLeaves L γ δ LG (fun a x => H a x + lam * ((k : ℝ) - M) * V a x) up s k₀ nroot nfl := by
  classical
  rw [sum_update_kernel L γ δ LG hlone H V up s k₀ nroot nfl hH hV]
  have hlin : ∀ k : ℕ, ∀ l ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ =>
      |(fun a x => H a x + lam * ((k : ℝ) - M) * V a x) l.1 (k₀ + latticePoint L n)| := by
    intro k l hl
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      ((hH l hl).add ((hV l hl).mul_left |lam * ((k : ℝ) - M)|))
    calc _ ≤ |H l.1 (k₀ + latticePoint L n)| + |lam * ((k : ℝ) - M) * V l.1 (k₀ + latticePoint L n)| :=
          abs_add_le _ _
      _ = _ := by rw [abs_mul]
  generalize hf : (fun κ : GenDecoration LG.garden d nroot nfl =>
      ((epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1))) = f
  generalize hc : (fun κ : GenDecoration LG.garden d nroot nfl => cosetDecoration LG.garden L k₀ κ.1) = c
  have hsumK : ∀ k ∈ range (2 * M + 1), Summable fun κ : GenDecoration LG.garden d nroot nfl =>
      f κ * ∏ l ∈ inputLeaves LG.garden,
        ((H l.1 (c κ l.toNode) : ℂ) + ((lam * ((k : ℝ) - M) : ℝ) : ℂ) * (V l.1 (c κ l.toNode) : ℂ)) := by
    intro k _
    have h1 := summable_leafKernel_summand L γ δ LG (fun a x => H a x + lam * ((k : ℝ) - M) * V a x) up s k₀
      nroot nfl hlone (hlin k)
    rw [← hc, ← hf]
    refine h1.congr fun κ => ?_
    congr 1
    exact prod_add_cast _ (fun l : GLeaf LG.garden.tree => H l.1 (cosetDecoration LG.garden L k₀ κ.1 l.toNode))
      (fun l : GLeaf LG.garden.tree => V l.1 (cosetDecoration LG.garden L k₀ κ.1 l.toNode)) (lam * ((k : ℝ) - M))
  have key : ∑' κ : GenDecoration LG.garden d nroot nfl, f κ * ∑ a ∈ inputLeaves LG.garden,
        ((V a.1 (c κ a.toNode) : ℂ) * ∏ l ∈ (inputLeaves LG.garden).erase a, (H l.1 (c κ l.toNode) : ℂ)) =
      ∑ k ∈ range (2 * M + 1), ((cw M k / lam : ℝ) : ℂ) *
        ∑' κ : GenDecoration LG.garden d nroot nfl, f κ * ∏ l ∈ inputLeaves LG.garden,
          ((H l.1 (c κ l.toNode) : ℂ) + ((lam * ((k : ℝ) - M) : ℝ) : ℂ) * (V l.1 (c κ l.toNode) : ℂ)) :=
    tsum_polarize (Ω := GenDecoration LG.garden d nroot nfl) (inputLeaves LG.garden) M hM hcard lam hlam f
      (fun κ l => (H l.1 (c κ l.toNode) : ℂ)) (fun κ l => (V l.1 (c κ l.toNode) : ℂ)) hsumK
  subst hf hc
  beta_reduce at key
  rw [key, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have e : ∀ κ : GenDecoration LG.garden d nroot nfl,
      ((epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1)) *
        ∏ l ∈ inputLeaves LG.garden,
        ((H l.1 (cosetDecoration LG.garden L k₀ κ.1 l.toNode) : ℂ) +
          ((lam * ((k : ℝ) - M) : ℝ) : ℂ) * (V l.1 (cosetDecoration LG.garden L k₀ κ.1 l.toNode) : ℂ)) =
      ((epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1)) *
        ∏ ℓ ∈ inputLeaves LG.garden,
          (((fun a x => H a x + lam * ((k : ℝ) - M) * V a x) : LeafProfiles w d) ℓ.1
            (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) := by
    intro κ
    rw [← prod_add_cast _ (fun l : GLeaf LG.garden.tree => H l.1 (cosetDecoration LG.garden L k₀ κ.1 l.toNode))
      (fun l : GLeaf LG.garden.tree => V l.1 (cosetDecoration LG.garden L k₀ κ.1 l.toNode))
      (lam * ((k : ℝ) - M))]
  simp_rw [e]
  unfold kernelLeaves
  ring

end WaveTurbulence.LGSpine
