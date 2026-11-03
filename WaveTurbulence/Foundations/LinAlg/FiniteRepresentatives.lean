/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LinAlg.MaxVolume
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card

/-!
# Finite representatives of bounded linear observations

The finite-representative argument in TARGET Lemma A.6 (`finitelem`,
L2435–L2445). A linear functional is recorded on a basis of the span of the
observations taking values in a fixed finite set. Two functionals with the
same record have the same accepted observations and agree on those observations.
-/

public section

namespace WaveTurbulence.LinAlg
open Module Finset
open scoped Classical

/-- A record consists of at most `n` test vectors and their accepted values. -/
abbrev LinearObservationTag {V : Type*} (S : Finset V) (Y : Finset ℝ) (n : ℕ) :=
  Σ q : Fin (n + 1), (Fin q.val → S) × (Fin q.val → Y)

/-- A record represents a functional when its recorded values are correct and
its test vectors span every accepted observation. -/
@[expose] def RepresentsLinearObservations {V : Type*} [AddCommGroup V] [Module ℝ V]
    {S : Finset V} {Y : Finset ℝ} {n : ℕ}
    (ℓ : V →ₗ[ℝ] ℝ) (t : LinearObservationTag S Y n) : Prop :=
  (∀ i, ℓ (t.2.1 i : V) = (t.2.2 i : ℝ)) ∧
    ∀ z ∈ S, ℓ z ∈ Y → z ∈ Submodule.span ℝ (Set.range fun i => (t.2.1 i : V))

/-- Every functional admits a record of length at most the ambient dimension. -/
theorem exists_linear_observation_tag {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (S : Finset V) (Y : Finset ℝ) (ℓ : V →ₗ[ℝ] ℝ) :
    ∃ t : LinearObservationTag S Y (finrank ℝ V), RepresentsLinearObservations ℓ t := by
  let H := S.filter (fun z => ℓ z ∈ Y)
  let W := Submodule.span ℝ (H : Set V)
  obtain ⟨f, hf, hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (H : Set V)
  have hfS (i) : f i ∈ S := (mem_filter.mp (hf i)).1
  have hfY (i) : ℓ (f i) ∈ Y := (mem_filter.mp (hf i)).2
  refine ⟨⟨⟨finrank ℝ W, Nat.lt_succ_of_le W.finrank_le⟩,
    (fun i => ⟨f i, hfS i⟩), (fun i => ⟨ℓ (f i), hfY i⟩)⟩, ?_⟩
  refine ⟨fun _ => rfl, ?_⟩
  intro z hz hY
  change z ∈ Submodule.span ℝ (Set.range f)
  rw [hspan]
  exact Submodule.subset_span (mem_filter.mpr ⟨hz, hY⟩)

/-- Functionals represented by the same record agree on all its accepted tests. -/
theorem same_tag_observations {V : Type*} [AddCommGroup V] [Module ℝ V]
    {S : Finset V} {Y : Finset ℝ} {n : ℕ} {ℓ ℓ' : V →ₗ[ℝ] ℝ}
    {t : LinearObservationTag S Y n}
    (h : RepresentsLinearObservations ℓ t) (h' : RepresentsLinearObservations ℓ' t)
    {z : V} (hz : z ∈ S) :
    (ℓ z ∈ Y ↔ ℓ' z ∈ Y) ∧ (ℓ z ∈ Y → ℓ z = ℓ' z) := by
  have heq : Set.EqOn ℓ ℓ' (Submodule.span ℝ (Set.range fun i => (t.2.1 i : V))) := by
    apply LinearMap.eqOn_span'
    rintro _ ⟨i, rfl⟩
    exact (h.1 i).trans (h'.1 i).symm
  refine ⟨⟨fun hy => ?_, fun hy => ?_⟩, fun hy => heq (h.2 z hz hy)⟩
  · rw [← heq (h.2 z hz hy)]
    exact hy
  · rw [heq (h'.2 z hz hy)]
    exact hy

/-- TARGET A.6's abstract finite-representative mechanism, with an explicit
cardinality bound. No finiteness assumption is imposed on the parameter set. -/
theorem exists_finite_linear_representatives {V K : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (S : Finset V) (Y : Finset ℝ) (ℓ : K → V →ₗ[ℝ] ℝ) :
    ∃ R : Finset K,
      R.card ≤ ∑ q : Fin (finrank ℝ V + 1), (S.card * Y.card) ^ q.val ∧
      ∀ k, ∃ k' ∈ R, ∀ z ∈ S,
        (ℓ k z ∈ Y ↔ ℓ k' z ∈ Y) ∧ (ℓ k z ∈ Y → ℓ k z = ℓ k' z) := by
  let T := LinearObservationTag S Y (finrank ℝ V)
  let A := {t : T // ∃ k, RepresentsLinearObservations (ℓ k) t}
  let pick : A → K := fun a => Classical.choose a.property
  have hpick (a : A) : RepresentsLinearObservations (ℓ (pick a)) a.val :=
    Classical.choose_spec a.property
  let R : Finset K := univ.image pick
  refine ⟨R, ?_, ?_⟩
  · calc
      R.card ≤ Fintype.card A := card_image_le.trans (by simp)
      _ ≤ Fintype.card T := Fintype.card_subtype_le _
      _ = _ := by simp [T, LinearObservationTag, Fintype.card_sigma, ← mul_pow]
  intro k
  obtain ⟨t, ht⟩ := exists_linear_observation_tag S Y (ℓ k)
  let a : A := ⟨t, k, ht⟩
  refine ⟨pick a, mem_image.mpr ⟨a, mem_univ _, rfl⟩, ?_⟩
  intro z hz
  exact same_tag_observations ht (hpick a) hz

end WaveTurbulence.LinAlg
