/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.CentralDiffC
public import WaveTurbulence.Foundations.Spine.RootWeightOps

/-!
# X5: exact pair-type polarization over non-anchored inputs

The type `τ` is the layer / positive-tree / negative-tree pair type. An
anchored type contributes the constant profile one and is never perturbed.
Every evaluation changes a whole pair type, independently of the individual
leaf addresses and independently of its momentum decoration. No estimate of
an oscillatory sum or flower kernel is assumed.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerX7X5
open Finset LGSpine LGSpine.CentralDiff
open scoped Classical

abbrev PairProfile (τ : Type*) (d : ℕ) := τ → Mom d → ℝ

/-- The input set that actually carries decaying profiles. -/
noncomputable def freeInputs {ι τ : Type*} [DecidableEq ι]
    (S : Finset ι) (typ : ι → τ) (anchor : τ → Prop) : Finset ι :=
  S.filter fun a => ¬ anchor (typ a)

/-- Product of the non-anchored profiles; anchor factors are exactly one. -/
noncomputable def profileProduct {ι τ : Type*} [DecidableEq ι] {d : ℕ}
    (S : Finset ι) (typ : ι → τ) (anchor : τ → Prop) (x : ι → Mom d)
    (h : PairProfile τ d) : ℂ :=
  ∏ a ∈ freeInputs S typ anchor, (h (typ a) (x a) : ℂ)

/-- A pair-type-uniform affine evaluation. Anchors are omitted by
`profileProduct`, so their profiles stay one at every evaluation. -/
def profilePerturb {τ : Type*} {d : ℕ} (h O : PairProfile τ d) (u : ℝ) : PairProfile τ d :=
  fun t x => h t x + u * O t x

/-- A linear-form multiplication, uniformly on the entire pair type. -/
def profileForm {τ : Type*} {d : ℕ} (c : τ → ℝ) (i : Fin d)
    (h : PairProfile τ d) : PairProfile τ d := fun t x => c t * x i * h t x

/-- The momentum supplied by the non-anchored inputs alone. -/
noncomputable def freeMomentum {ι τ : Type*} [DecidableEq ι] {d : ℕ}
    (S : Finset ι) (typ : ι → τ) (anchor : τ → Prop) (x : ι → Mom d)
    (c : τ → ℝ) : Mom d := ∑ a ∈ freeInputs S typ anchor, c (typ a) • x a

theorem freeMomentum_apply {ι τ : Type*} [DecidableEq ι] {d : ℕ}
    (S : Finset ι) (typ : ι → τ) (anchor : τ → Prop) (x : ι → Mom d)
    (c : τ → ℝ) (i : Fin d) :
    freeMomentum S typ anchor x c i = ∑ a ∈ freeInputs S typ anchor, c (typ a) * x a i := by
  simp [freeMomentum, WithLp.ofLp_sum, Finset.sum_apply]

/-- X5's first-order weight identity (M), with degree equal to the number
of non-anchored inputs. The coefficients are the real P* central differences. -/
theorem freeMomentum_mul_profileProduct {ι τ : Type*} [DecidableEq ι] {d : ℕ}
    (S : Finset ι) (typ : ι → τ) (anchor : τ → Prop) (x : ι → Mom d)
    (c : τ → ℝ) (i : Fin d) (h : PairProfile τ d)
    (M : ℕ) (hM : 1 ≤ M) (hcard : (freeInputs S typ anchor).card ≤ 2 * M)
    (lam : ℝ) (hlam : lam ≠ 0) :
    (freeMomentum S typ anchor x c i : ℂ) * profileProduct S typ anchor x h =
      ∑ k ∈ range (2 * M + 1), ((cw M k / lam : ℝ) : ℂ) *
        profileProduct S typ anchor x
          (profilePerturb h (profileForm c i h) (lam * ((k : ℝ) - M))) := by
  classical
  rw [freeMomentum_apply]
  simp only [Complex.ofReal_sum, profileProduct]
  have he : (∑ a ∈ freeInputs S typ anchor, ((c (typ a) * x a i : ℝ) : ℂ)) *
      (∏ a ∈ freeInputs S typ anchor, (h (typ a) (x a) : ℂ)) =
      ∑ a ∈ freeInputs S typ anchor,
        ((c (typ a) * x a i * h (typ a) (x a) : ℝ) : ℂ) *
          ∏ b ∈ (freeInputs S typ anchor).erase a, (h (typ b) (x b) : ℂ) := by
    rw [sum_mul]
    refine sum_congr rfl fun a ha => ?_
    rw [← Finset.mul_prod_erase (freeInputs S typ anchor) _ ha]
    push_cast
    ring
  rw [he]
  have hex := polarization_extraction (freeInputs S typ anchor) M hM hcard
    (fun a => (h (typ a) (x a) : ℂ))
    (fun a => ((c (typ a) * x a i * h (typ a) (x a) : ℝ) : ℂ)) lam hlam
  rw [hex]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  refine prod_congr rfl fun a _ => ?_
  simp [profilePerturb, profileForm]

/-- Iterated real pair-type evaluations. This is a finite expression with
no leaf-choice index; each operation is a whole pair-type perturbation. -/
noncomputable def formWord {ι τ : Type*} [DecidableEq ι] {d m : ℕ}
    (S : Finset ι) (typ : ι → τ) (anchor : τ → Prop) (x : ι → Mom d)
    (c : Fin m → τ → ℝ) (M : ℕ) (lam : ℝ) :
    List (Fin m × Fin d) → PairProfile τ d → ℂ
  | [], h => profileProduct S typ anchor x h
  | f :: rest, h => ∑ k ∈ range (2 * M + 1), ((cw M k / lam : ℝ) : ℂ) *
      formWord S typ anchor x c M lam rest
        (profilePerturb h (profileForm (c f.1) f.2 h) (lam * ((k : ℝ) - M)))

theorem formWord_eq {ι τ : Type*} [DecidableEq ι] {d m : ℕ}
    (S : Finset ι) (typ : ι → τ) (anchor : τ → Prop) (x : ι → Mom d)
    (c : Fin m → τ → ℝ) (M : ℕ) (hM : 1 ≤ M)
    (hcard : (freeInputs S typ anchor).card ≤ 2 * M) (lam : ℝ) (hlam : lam ≠ 0)
    (word : List (Fin m × Fin d)) (h : PairProfile τ d) :
    formWord S typ anchor x c M lam word h =
      (word.map fun f => (freeMomentum S typ anchor x (c f.1) f.2 : ℂ)).prod *
        profileProduct S typ anchor x h := by
  induction word generalizing h with
  | nil => simp [formWord]
  | cons f rest ih =>
    simp only [formWord, ih]
    simp_rw [mul_left_comm ((cw M _ / lam : ℝ) : ℂ)]
    rw [← mul_sum, ← freeMomentum_mul_profileProduct S typ anchor x (c f.1) f.2 h M hM hcard lam hlam]
    simp only [List.map_cons, List.prod_cons]
    ring

/-- X5's full even weight identity, over arbitrary many flower charges.
With `n = 2*Λ` it supplies the product of `⟨charge_j⟩^(4Λ)` factors.
All input profiles on the right remain pair-typed and anchors remain one. -/
theorem free_weight_profileProduct {ι τ : Type*} [DecidableEq ι] {d m : ℕ}
    (S : Finset ι) (typ : ι → τ) (anchor : τ → Prop) (x : ι → Mom d)
    (c : Fin m → τ → ℝ) (h : PairProfile τ d)
    (M : ℕ) (hM : 1 ≤ M) (hcard : (freeInputs S typ anchor).card ≤ 2 * M)
    (lam : ℝ) (hlam : lam ≠ 0) (n : ℕ) :
    ((∏ j, jbr (freeMomentum S typ anchor x (c j)) ^ (2 * n) : ℝ) : ℂ) *
        profileProduct S typ anchor x h =
      ∑ choice : Fin m → Fin n → Option (Fin d),
        formWord S typ anchor x c M lam (opsOfChoice choice) h := by
  classical
  simp_rw [formWord_eq S typ anchor x c M hM hcard lam hlam]
  rw [prod_jbr_pow_expand, Complex.ofReal_sum, sum_mul]
  refine sum_congr rfl fun choice _ => ?_
  congr 1
  have he := prod_opsOfChoice choice (fun j i =>
    (freeMomentum S typ anchor x (c j) i : ℂ))
  rw [he]
  push_cast
  refine prod_congr rfl fun j _ => prod_congr rfl fun t _ => ?_
  cases choice j t <;> simp

end WaveTurbulence.FlowerX7X5
