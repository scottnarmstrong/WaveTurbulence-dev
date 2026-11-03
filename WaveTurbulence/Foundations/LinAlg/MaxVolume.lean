/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Finset.Max

/-!
# Maximal-volume selection from a finite spanning set

TARGET Lemma A.7 (`lincomblem`, L2449–L2457). Selecting a globally maximal
absolute determinant gives the stronger coordinate bound one. The source uses
a successive-volume selection and the bound `2^(d-1)`.
-/

public section

namespace WaveTurbulence.LinAlg
open Module
open scoped Classical

/-- A finite spanning set in a real finite-dimensional vector space contains a
basis in which all its vectors have coordinates of absolute value at most one. -/
theorem exists_basis_repr_le_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (S : Finset V) (hS : Submodule.span ℝ (S : Set V) = ⊤) :
    ∃ b : Basis (Fin (Module.finrank ℝ V)) ℝ V,
      (∀ i, b i ∈ S) ∧ ∀ Y ∈ S, ∀ i, |b.repr Y i| ≤ 1 := by
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℝ (S : Set V)
  rw [hS, finrank_top] at hex
  obtain ⟨f₀, hf₀, hspan₀, hli₀⟩ := hex
  let e : Basis (Fin (Module.finrank ℝ V)) ℝ V := Module.finBasis ℝ V
  let f₀S : Fin (Module.finrank ℝ V) → S := fun i => ⟨f₀ i, hf₀ i⟩
  have hd₀ : e.det (fun i => (f₀S i : V)) ≠ 0 := by
    apply isUnit_iff_ne_zero.mp
    apply e.is_basis_iff_det.mp
    exact ⟨hli₀, hspan₀⟩
  obtain ⟨f, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (Module.finrank ℝ V) → S))
    (fun g => |e.det (fun i => (g i : V))|) ⟨f₀S, Finset.mem_univ _⟩
  let v : Fin (Module.finrank ℝ V) → V := fun i => (f i : V)
  have hd : e.det v ≠ 0 := by
    intro hz
    have hm := hmax f₀S (Finset.mem_univ _)
    change |e.det (fun i => (f₀S i : V))| ≤ |e.det v| at hm
    rw [hz, abs_zero] at hm
    exact hd₀ (abs_nonpos_iff.mp hm)
  obtain ⟨hli, hspan⟩ := e.is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr hd)
  let b : Basis (Fin (Module.finrank ℝ V)) ℝ V := Basis.mk hli hspan.ge
  refine ⟨b, ?_, ?_⟩
  · intro i
    simpa only [b, Basis.coe_mk, v] using (f i).property
  intro Y hY i
  have hc : e.det v * b.repr Y i = e.det (Function.update v i Y) := by
    have h := congrArg (fun l : V →ₗ[ℝ] ℝ => l Y)
      (e.det_smul_mk_coord_eq_det_update hli hspan.ge i)
    simpa only [b, LinearMap.smul_apply, smul_eq_mul, Basis.coord_apply,
      MultilinearMap.toLinearMap_apply, AlternatingMap.coe_multilinearMap] using h
  have hup : Function.update v i Y =
      fun j => ((Function.update f i (⟨Y, hY⟩ : S)) j : V) := by
    funext j
    by_cases hji : j = i <;> simp [hji, v]
  have hm := hmax (Function.update f i (⟨Y, hY⟩ : S)) (Finset.mem_univ _)
  change |e.det (fun j => ((Function.update f i (⟨Y, hY⟩ : S)) j : V))| ≤ |e.det v| at hm
  have hb : |e.det v| * |b.repr Y i| ≤ |e.det v| * 1 := by
    rw [← abs_mul, hc, hup, mul_one]
    exact hm
  exact (mul_le_mul_iff_right₀ (abs_pos.mpr hd)).mp (by simpa only [mul_comm] using hb)

/-- A finite set has a spanning selection from itself with coefficients bounded
by one, including when its span is a proper subspace or the set is empty. -/
theorem exists_spanning_selection {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (S : Finset V) :
    ∃ q ≤ Module.finrank ℝ V, ∃ X : Fin q → V,
      (∀ i, X i ∈ S) ∧ ∀ Y ∈ S, ∃ c : Fin q → ℝ,
        (∀ i, |c i| ≤ 1) ∧ (∑ i, c i • X i) = Y := by
  let W := Submodule.span ℝ (S : Set V)
  let lift : S → W := fun Y => ⟨Y, Submodule.subset_span Y.property⟩
  let T : Finset W := Finset.univ.image lift
  have hT : (T : Set W) = Set.range lift := by
    ext Y
    simp [T]
  have hspan : Submodule.span ℝ (T : Set W) = ⊤ := by
    rw [hT]
    apply (Submodule.span_range_subtype_eq_top_iff W
      (fun Y : S => Submodule.subset_span Y.property)).mpr
    rw [Subtype.range_coe_subtype]
    rfl
  obtain ⟨b, hb, hc⟩ := exists_basis_repr_le_one T hspan
  refine ⟨Module.finrank ℝ W, W.finrank_le, fun i => (b i : V), ?_, ?_⟩
  · intro i
    obtain ⟨Y, _, hY⟩ := Finset.mem_image.mp (hb i)
    have heq : (Y : V) = (b i : V) := congrArg Subtype.val hY
    change (b i : V) ∈ S
    rw [← heq]
    exact Y.property
  intro Y hY
  let Z : W := lift ⟨Y, hY⟩
  have hZ : Z ∈ T := Finset.mem_image.mpr ⟨⟨Y, hY⟩, Finset.mem_univ _, rfl⟩
  refine ⟨fun i => b.repr Z i, hc Z hZ, ?_⟩
  have heq := congrArg W.subtype (b.sum_repr Z)
  simpa only [map_sum, map_smul, Submodule.subtype_apply] using heq

end WaveTurbulence.LinAlg
