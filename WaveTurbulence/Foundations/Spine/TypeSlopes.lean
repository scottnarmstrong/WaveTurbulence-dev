/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RootFormKernel
public import WaveTurbulence.Foundations.Spine.TypeFamily
public import WaveTurbulence.Foundations.Spine.SingleLeafDerivativeNorm
/-! AMEND6' (design P*): the first-order slopes of pair-type profiles and the exact kernel identities

* `(D)`: `partial_i K[tp h] = sum_k (w_k/lam) K[tp (h + lam (k-M) D_i h)]`,
* `(M)`: `sigma_{j0} k_{j0}^i K[tp h] = sum_k (w_k/lam) K[tp (h + lam (k-M) M^{(j0)}_i h)]`,

with `D_i h = partial_i h` and `M^{(j0)}_i h (q,j,j') = ([j = j0] - [j' = j0]) x_i h (q,j,j')`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset CentralDiff

/-- Pair-type profiles (the data of a one-element `TypeFamily`). -/
abbrev TProf (d w : ℕ) := ℕ → Fin w → Fin w → Mom d → ℝ

namespace TProf
variable {d w : ℕ}

/-- `h + mu O`. -/
def perturb (h O : TProf d w) (μ : ℝ) : TProf d w := fun q j j' x => h q j j' x + μ * O q j j' x

/-- The coordinate derivative slope `D_i`. -/
noncomputable def der (i : Fin d) (h : TProf d w) : TProf d w := fun q j j' => realPartialMom i (h q j j')

/-- The root linear form slope `M^{(j0)}_i`. -/
def form (j0 : Fin w) (i : Fin d) (h : TProf d w) : TProf d w := fun q j j' x =>
  ((if j = j0 then (1 : ℝ) else 0) - (if j' = j0 then (1 : ℝ) else 0)) * x i * h q j j' x

end TProf

theorem typeProfiles_perturb {w d : ℕ} (LG : LayeredGarden w) (h O : TProf d w) (μ : ℝ) :
    typeProfiles LG (TProf.perturb h O μ) = fun a x => typeProfiles LG h a x + μ * typeProfiles LG O a x := by
  funext a x
  unfold typeProfiles TProf.perturb
  split_ifs <;> simp

theorem typeProfiles_der {w d : ℕ} (LG : LayeredGarden w) (i : Fin d) (h : TProf d w) (a : Fin w × TTree.Path) :
    typeProfiles LG (TProf.der i h) a = realPartialMom i (typeProfiles LG h a) := by
  unfold typeProfiles TProf.der
  split_ifs
  · rfl
  · funext x
    simp [realPartialMom]

theorem typeProfiles_form {w d : ℕ} (LG : LayeredGarden w) (j0 : Fin w) (i : Fin d) (h : TProf d w)
    (ℓ : GLeaf LG.garden.tree) (x : Mom d) :
    typeProfiles LG (TProf.form j0 i h) ℓ.1 x =
      ((if ℓ.1.1 = j0 then (1 : ℝ) else 0) - (if (LG.garden.pair ℓ).1.1 = j0 then (1 : ℝ) else 0)) *
        x i * typeProfiles LG h ℓ.1 x := by
  rw [typeProfiles_leaf, typeProfiles_leaf]
  rfl

/-- (D): one coordinate derivative of the kernel with pair-type profile `h`, as a central-difference
combination of kernels with pair-type profiles. -/
theorem partialMom_kernel_typeProfiles {w d B : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L) (hB : d + 1 ≤ B)
    (γ δ : ℝ) (LG : LayeredGarden w) (h : TProf d w) (i : Fin d) (C : (Fin w × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (1 : ℕ) (typeProfiles LG h l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR 1 B (typeProfiles LG h l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (hH : ∀ k : Mom d, ∀ l ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |typeProfiles LG h l.1 (k + latticePoint L n)|)
    (hV : ∀ k : Mom d, ∀ l ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |typeProfiles LG (TProf.der i h) l.1 (k + latticePoint L n)|)
    (M : ℕ) (hM : 1 ≤ M) (hcard : (inputLeaves LG.garden).card ≤ 2 * M) (lam : ℝ) (hlam : lam ≠ 0)
    (k : Mom d) :
    partialMom i (fun x => kernelLeaves L γ δ LG (typeProfiles LG h) up s x nroot nfl) k =
      ∑ m ∈ range (2 * M + 1), ((cw M m / lam : ℝ) : ℂ) *
        kernelLeaves L γ δ LG (typeProfiles LG (TProf.perturb h (TProf.der i h) (lam * ((m : ℝ) - M))))
          up s k nroot nfl := by
  rw [partialMom_kernelLeaves_eq_sum hd hL hB γ δ LG (typeProfiles LG h) C hc hb up s nroot nfl hlone i k]
  have e : ∀ l : ActualInputLeaves LG.garden, singleLeafDerivative LG.garden (typeProfiles LG h) l i =
      Function.update (typeProfiles LG h) l.1.1 (typeProfiles LG (TProf.der i h) l.1.1) := by
    intro l
    unfold singleLeafDerivative
    rw [typeProfiles_der]
  simp_rw [e]
  rw [kernelLeaves_polarize L γ δ LG hlone (typeProfiles LG h) (typeProfiles LG (TProf.der i h)) up s k nroot nfl
    (hH k) (hV k) M hM hcard lam hlam]
  refine sum_congr rfl fun m _ => ?_
  rw [typeProfiles_perturb]

/-- (M): multiplication by the signed root coordinate, as a central-difference combination. -/
theorem rootcoord_mul_kernel_typeProfiles {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (hp : LG.garden.IsPlain)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (h : TProf d w) (j0 : Fin w) (i : Fin d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hH : ∀ l ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |typeProfiles LG h l.1 (k₀ + latticePoint L n)|)
    (hV : ∀ l ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ =>
      |typeProfiles LG (TProf.form j0 i h) l.1 (k₀ + latticePoint L n)|)
    (M : ℕ) (hM : 1 ≤ M) (hcard : (inputLeaves LG.garden).card ≤ 2 * M) (lam : ℝ) (hlam : lam ≠ 0) :
    ((((nodeSign LG.garden.sig (GNode.root LG.garden.tree j0).1 : ℤˣ) : ℤ) : ℝ) *
        (k₀ + latticePoint L (nroot j0)) i : ℝ) *
        kernelLeaves L γ δ LG (typeProfiles LG h) up s k₀ nroot nfl =
      ∑ m ∈ range (2 * M + 1), ((cw M m / lam : ℝ) : ℂ) *
        kernelLeaves L γ δ LG (typeProfiles LG (TProf.perturb h (TProf.form j0 i h) (lam * ((m : ℝ) - M))))
          up s k₀ nroot nfl := by
  set c : (Fin w × TTree.Path) → ℝ := fun a =>
    if hn : ∃ ℓ : GLeaf LG.garden.tree, ℓ.1 = a then
      (if a.1 = j0 then (1 : ℝ) else 0) - (if (LG.garden.pair hn.choose).1.1 = j0 then (1 : ℝ) else 0)
    else 0 with hcdef
  have hc : ∀ ℓ ∈ inputLeaves LG.garden, c ℓ.1 =
      (if ℓ.1.1 = j0 then (1 : ℝ) else 0) - (if (LG.garden.pair ℓ).1.1 = j0 then (1 : ℝ) else 0) := by
    intro ℓ _
    have he : ∃ ℓ' : GLeaf LG.garden.tree, ℓ'.1 = ℓ.1 := ⟨ℓ, rfl⟩
    have hch : he.choose = ℓ := Subtype.ext he.choose_spec
    simp only [hcdef, dif_pos he, hch]
  have hVc : ∀ l ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ =>
      |c l.1 * (k₀ + latticePoint L n) i * typeProfiles LG h l.1 (k₀ + latticePoint L n)| := by
    intro l hl
    refine (hV l hl).congr fun n => ?_
    rw [typeProfiles_form, hc l hl]
  have hupd : ∀ a : ActualInputLeaves LG.garden,
      Function.update (typeProfiles LG h) a.1.1 (fun x => c a.1.1 * x i * typeProfiles LG h a.1.1 x) =
      Function.update (typeProfiles LG h) a.1.1 (typeProfiles LG (TProf.form j0 i h) a.1.1) := by
    intro a
    congr 1
    funext x
    rw [typeProfiles_form, hc a.1 a.2]
  have h1 := kernelLeaves_rootform L γ δ LG hp hlone (typeProfiles LG h) c j0 i hc up s k₀ nroot nfl hH hVc
  simp_rw [hupd] at h1
  rw [h1, kernelLeaves_polarize L γ δ LG hlone (typeProfiles LG h) (typeProfiles LG (TProf.form j0 i h))
    up s k₀ nroot nfl hH hV M hM hcard lam hlam]
  refine sum_congr rfl fun m _ => ?_
  rw [typeProfiles_perturb]

end WaveTurbulence.LGSpine
