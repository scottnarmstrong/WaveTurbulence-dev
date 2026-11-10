/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.LemmaD

/-!
# Local piece charts (M4 Prop L) as decidable finite data

A **local chart** of a piece is a small directed graph (`nA` atoms; `nB` local bonds, internal or stubs) with
* an **input pair** `eO` (entering, label `κ + ρ_in r`) and `eI` (leaving, label `κ`) whose labels are known
  (the entry pair of M4 §3.2 Step 1), and the other local bonds **owned**;
* `nC` local coordinates, each a difference `k(orgP c) − k(orgQ c)` of two local bonds;
* the local solution: every local label is `κ + Σ_c loc l c • y_c + locR l • r` (`y` the coordinates);
* optional **output pairs** (exit pair `outM`, pendant pair `outB`), each with equal coordinate parts;
* **extra equations** `k(X₁ x) = k(X₂ x)` (2-cut relations of N1 Lemma D, used only for uniqueness);
* a **uniqueness certificate**: each owned label is an explicit integer combination of the conservation laws at the
  local atoms, the coordinate equations and the extra equations, modulo the inputs (this is the referee's repair R1:
  the local square system is unimodular, so the solution is unique over every abelian group);
* **phase data**: the expected Gram matrix of the energy at each local atom, as a quadratic form in
  `(y_0, …, y_{nC−1}, r)`.

`LocalChart.Valid` is a decidable conjunction; each instance (`Chart.Configs`) is proved valid by `decide`. This
file proves the soundness lemmas used by the gluing.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset

/-- **A local piece chart** with `nA` atoms, `nC` coordinates and `nB` local bonds. -/
structure LocalChart (nA nC nB : ℕ) where
  src : Fin nB → Option (Fin nA)
  dst : Fin nB → Option (Fin nA)
  loc : Fin nB → Fin nC → ℤ
  locR : Fin nB → ℤ
  eO : Fin nB
  eI : Fin nB
  outM : Option (Fin nB × Fin nB)
  outB : Option (Fin nB × Fin nB)
  orgP : Fin nC → Fin nB
  orgQ : Fin nC → Fin nB
  nX : ℕ
  X₁ : Fin nX → Fin nB
  X₂ : Fin nX → Fin nB
  certA : Fin nB → Fin nA → ℤ
  certC : Fin nB → Fin nC → ℤ
  certX : Fin nB → Fin nX → ℤ
  /-- The expected Gram matrix of the energy at each atom, in the variables `(y_0, …, y_{nC−1}, r)`. -/
  gram : Fin nA → Fin (nC + 1) → Fin (nC + 1) → ℤ
  /-- Pair data: the number of bonds between the two atoms, and `ζ`. -/
  mu : ℕ
  ζ : Fin 3 → ℤ
  /-- Core data. -/
  lin : Bool
  σ₁ : ℤ
  σ₂ : ℤ
  ξ : Fin 4 → ℤ

namespace LocalChart

variable {nA nC nB : ℕ} (c : LocalChart nA nC nB)

/-- The local graph. -/
abbrev graph : LocalGraph := ⟨nA, nB, c.src, c.dst⟩

/-- Local incidence. -/
def inc (u : Fin nA) (l : Fin nB) : ℤ :=
  (if c.src l = some u then 1 else 0) - (if c.dst l = some u then 1 else 0)

/-- Inputs. -/
def IsInput (l : Fin nB) : Prop := l = c.eO ∨ l = c.eI

instance (l : Fin nB) : Decidable (c.IsInput l) := inferInstanceAs (Decidable (_ ∨ _))

/-- The full local vector `(loc l, locR l)` of a bond. -/
def vec (l : Fin nB) : Fin (nC + 1) → ℤ := fun i => if h : i.val < nC then c.loc l ⟨i, h⟩ else c.locR l

/-- The Gram matrix of the energy at `u` computed from the local solution. -/
def gramOf (u : Fin nA) (i j : Fin (nC + 1)) : ℤ := ∑ l, -(c.inc u l) * c.vec l i * c.vec l j

/-- The coefficient of the local label `l'` in the certificate combination for `l`. -/
def certCoef (l l' : Fin nB) : ℤ :=
  (∑ u, c.certA l u * c.inc u l') +
    (∑ k, c.certC l k * ((if l' = c.orgP k then 1 else 0) - (if l' = c.orgQ k then 1 else 0))) +
    (∑ x, c.certX l x * ((if l' = c.X₁ x then 1 else 0) - (if l' = c.X₂ x then 1 else 0)))

/-- **Validity** (decidable). -/
def Valid : Prop :=
  c.eO ≠ c.eI ∧
  (∀ k, c.loc c.eO k = 0) ∧ (∀ k, c.loc c.eI k = 0) ∧ c.locR c.eI = 0 ∧
  (∀ u, (∑ l, c.inc u l) = 0) ∧
  (∀ u k, (∑ l, c.inc u l * c.loc l k) = 0) ∧
  (∀ u, (∑ l, c.inc u l * c.locR l) = 0) ∧
  (∀ l k, c.loc l k = 0 ∨ c.loc l k = 1 ∨ c.loc l k = -1) ∧
  (∀ k k', c.loc (c.orgP k) k' - c.loc (c.orgQ k) k' = if k = k' then 1 else 0) ∧
  (∀ k, c.locR (c.orgP k) = c.locR (c.orgQ k)) ∧
  (∀ p ∈ c.outM, ∀ k, c.loc p.1 k = c.loc p.2 k) ∧
  (∀ p ∈ c.outB, ∀ k, c.loc p.1 k = c.loc p.2 k) ∧
  (∀ l l', ¬ c.IsInput l → ¬ c.IsInput l' → c.certCoef l l' = if l = l' then 1 else 0) ∧
  (∀ u i j, c.gramOf u i j + c.gramOf u j i = c.gram u i j + c.gram u j i)

instance : Decidable c.Valid := by unfold Valid; infer_instance

variable {c}

/-! ## Soundness -/

section Sound

variable (hc : c.Valid)
include hc

theorem eO_ne_eI : c.eO ≠ c.eI := hc.1
theorem loc_eO (k : Fin nC) : c.loc c.eO k = 0 := hc.2.1 k
theorem loc_eI (k : Fin nC) : c.loc c.eI k = 0 := hc.2.2.1 k
theorem locR_eI : c.locR c.eI = 0 := hc.2.2.2.1
theorem sum_inc (u : Fin nA) : (∑ l, c.inc u l) = 0 := hc.2.2.2.2.1 u
theorem sum_inc_loc (u : Fin nA) (k : Fin nC) : (∑ l, c.inc u l * c.loc l k) = 0 := hc.2.2.2.2.2.1 u k
theorem sum_inc_locR (u : Fin nA) : (∑ l, c.inc u l * c.locR l) = 0 := hc.2.2.2.2.2.2.1 u
theorem loc_unit (l : Fin nB) (k : Fin nC) : c.loc l k = 0 ∨ c.loc l k = 1 ∨ c.loc l k = -1 :=
  hc.2.2.2.2.2.2.2.1 l k
theorem coord_loc (k k' : Fin nC) : c.loc (c.orgP k) k' - c.loc (c.orgQ k) k' = if k = k' then 1 else 0 :=
  hc.2.2.2.2.2.2.2.2.1 k k'
theorem coord_locR (k : Fin nC) : c.locR (c.orgP k) = c.locR (c.orgQ k) := hc.2.2.2.2.2.2.2.2.2.1 k
theorem outM_loc {p : Fin nB × Fin nB} (hp : c.outM = some p) (k : Fin nC) : c.loc p.1 k = c.loc p.2 k :=
  hc.2.2.2.2.2.2.2.2.2.2.1 p (by rw [hp]; rfl) k
theorem outB_loc {p : Fin nB × Fin nB} (hp : c.outB = some p) (k : Fin nC) : c.loc p.1 k = c.loc p.2 k :=
  hc.2.2.2.2.2.2.2.2.2.2.2.1 p (by rw [hp]; rfl) k
theorem certCoef_eq {l l' : Fin nB} (hl : ¬ c.IsInput l) (hl' : ¬ c.IsInput l') :
    c.certCoef l l' = if l = l' then 1 else 0 := hc.2.2.2.2.2.2.2.2.2.2.2.2.1 l l' hl hl'
theorem gram_symm (u : Fin nA) (i j : Fin (nC + 1)) :
    c.gramOf u i j + c.gramOf u j i = c.gram u i j + c.gram u j i := hc.2.2.2.2.2.2.2.2.2.2.2.2.2 u i j

/-- **Local uniqueness** over any abelian group: a local labelling with zero inputs, zero flow at every local atom,
zero coordinates and zero extra equations vanishes. -/
theorem unique_local {E : Type*} [AddCommGroup E] (d : Fin nB → E) (hO : d c.eO = 0) (hI : d c.eI = 0)
    (hflow : ∀ u, (∑ l, c.inc u l • d l) = 0) (hcoord : ∀ k, d (c.orgP k) - d (c.orgQ k) = 0)
    (hX : ∀ x, d (c.X₁ x) - d (c.X₂ x) = 0) (l : Fin nB) : d l = 0 := by
  classical
  by_cases hl : c.IsInput l
  · rcases hl with rfl | rfl <;> assumption
  have hin : ∀ l', c.IsInput l' → d l' = 0 := by
    rintro l' (rfl | rfl) <;> assumption
  have key : (∑ l', c.certCoef l l' • d l') = 0 := by
    unfold certCoef
    simp only [add_smul, Finset.sum_add_distrib, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm (f := fun l' u => c.certA l u • c.inc u l' • d l')]
    rw [Finset.sum_comm (f := fun l' k => c.certC l k • ((if l' = c.orgP k then (1 : ℤ) else 0) -
      (if l' = c.orgQ k then 1 else 0)) • d l')]
    rw [Finset.sum_comm (f := fun l' x => c.certX l x • ((if l' = c.X₁ x then (1 : ℤ) else 0) -
      (if l' = c.X₂ x then 1 else 0)) • d l')]
    have e1 : ∀ u, (∑ l', c.certA l u • c.inc u l' • d l') = c.certA l u • ∑ l', c.inc u l' • d l' := by
      intro u; rw [Finset.smul_sum]
    have e2 : ∀ k, (∑ l', c.certC l k • ((if l' = c.orgP k then (1 : ℤ) else 0) -
        (if l' = c.orgQ k then 1 else 0)) • d l') = c.certC l k • (d (c.orgP k) - d (c.orgQ k)) := by
      intro k
      rw [← Finset.smul_sum]; congr 1
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        mem_univ, ite_true]
    have e3 : ∀ x, (∑ l', c.certX l x • ((if l' = c.X₁ x then (1 : ℤ) else 0) -
        (if l' = c.X₂ x then 1 else 0)) • d l') = c.certX l x • (d (c.X₁ x) - d (c.X₂ x)) := by
      intro x
      rw [← Finset.smul_sum]; congr 1
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        mem_univ, ite_true]
    simp only [e1, e2, e3, hflow, hcoord, hX, smul_zero, Finset.sum_const_zero, add_zero]
  have hsplit : (∑ l', c.certCoef l l' • d l') = d l := by
    rw [Finset.sum_eq_single l]
    · rw [certCoef_eq hc hl hl, if_pos rfl, one_smul]
    · intro l' _ hne
      by_cases hl' : c.IsInput l'
      · rw [hin l' hl', smul_zero]
      · rw [certCoef_eq hc hl hl', if_neg (Ne.symm hne), zero_smul]
    · simp
  rw [← hsplit, key]

end Sound

/-! ## Quadratic forms -/

/-- The quadratic form of an integer matrix on vectors. -/
noncomputable def quad {m d : ℕ} (G : Fin m → Fin m → ℤ) (z : Fin m → Mom d) : ℝ :=
  ∑ i, ∑ j, (G i j : ℝ) * inner ℝ (z i) (z j)

theorem quad_eq_of_symm {m d : ℕ} {G H : Fin m → Fin m → ℤ} (h : ∀ i j, G i j + G j i = H i j + H j i)
    (z : Fin m → Mom d) : quad G z = quad H z := by
  have key : ∀ K : Fin m → Fin m → ℤ, 2 * quad K z = ∑ i, ∑ j, ((K i j + K j i : ℤ) : ℝ) * inner ℝ (z i) (z j) := by
    intro K
    unfold quad
    have hs : (∑ i, ∑ j, (K j i : ℝ) * inner ℝ (z i) (z j)) = ∑ i, ∑ j, (K i j : ℝ) * inner ℝ (z i) (z j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [real_inner_comm]
    simp only [Int.cast_add, add_mul, Finset.sum_add_distrib, hs]
    ring
  have h2 : 2 * quad G z = 2 * quad H z := by rw [key, key]; simp only [h]
  linarith

/-- The squared norm of an integer combination is the quadratic form of its outer product. -/
theorem norm_sq_comb {m d : ℕ} (v : Fin m → ℤ) (z : Fin m → Mom d) :
    ‖∑ i, (v i : ℝ) • z i‖ ^ 2 = quad (fun i j => v i * v j) z := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  unfold quad
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [real_inner_smul_left, real_inner_smul_right]
  push_cast; ring

/-- **The energy at a local atom as a quadratic form** (from the Gram check). -/
theorem energy_local (hc : c.Valid) {d : ℕ} (u : Fin nA) (z : Fin (nC + 1) → Mom d) :
    (∑ l, -(c.inc u l : ℝ) * ‖∑ i, (c.vec l i : ℝ) • z i‖ ^ 2) = quad (c.gram u) z := by
  simp only [norm_sq_comb]
  rw [← quad_eq_of_symm (gram_symm hc u) z]
  unfold quad gramOf
  simp only [Finset.mul_sum, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  push_cast; ring

end LocalChart

end WaveTurbulence.TVine.Chart
