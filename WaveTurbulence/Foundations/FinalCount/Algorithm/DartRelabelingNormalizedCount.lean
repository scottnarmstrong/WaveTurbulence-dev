/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DartRelabelingCount
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionDartEquiv
public import WaveTurbulence.Foundations.FinalCount.AppBLinks
import Mathlib.Tactic

/-! # Actual selected-link normalization is invariant under dart relabeling -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem bondsBetween_relabel (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (ha : ∀ x,N.atom (f x) = M.atom x) (hm : ∀ x,N.mate (f x) = f (M.mate x))
    (ho : ∀ x,N.out (f x) = M.out x) (a b : V) : M.bondsBetween a b = N.bondsBetween a b := by
  have he (x : D) : N.ends (f x) = M.ends x := by
    change s(N.atom (f x),N.atom (N.mate (f x))) = s(M.atom x,M.atom (M.mate x))
    rw [ha,hm,ha]
  apply card_bij (fun x _ => f x)
  · intro x hx
    obtain ⟨hx,hend⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(ho x).trans (mem_filter.mp hx).2⟩,(he x).trans hend⟩
  · intro x hx y hy h
    exact f.injective h
  · intro y hy
    obtain ⟨x,rfl⟩ := f.surjective y
    obtain ⟨hy,hend⟩ := mem_filter.mp hy
    exact ⟨x,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(ho x).symm.trans (mem_filter.mp hy).2⟩,
      (he x).symm.trans hend⟩,rfl⟩

theorem directed_relabel_iff (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (ha : ∀ x,N.atom (f x) = M.atom x) (hm : ∀ x,N.mate (f x) = f (M.mate x))
    (ho : ∀ x,N.out (f x) = M.out x) (a b : V) : M.Directed a b ↔ N.Directed a b := by
  constructor
  · rintro ⟨x,hout,hx,hy⟩
    exact ⟨f x,(ho x).trans hout,(ha x).trans hx,by rw [hm,ha]; exact hy⟩
  · rintro ⟨y,hout,hx,hy⟩
    obtain ⟨x,rfl⟩ := f.surjective y
    exact ⟨x,(ho x).symm.trans hout,(ha x).symm.trans hx,by rw [hm,ha] at hy; exact hy⟩

theorem sourceLadder_relabel_iff (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x,N.atom (f x) = M.atom x)
    (hm : ∀ x,N.mate (f x) = f (M.mate x)) (ho : ∀ x,N.out (f x) = M.out x)
    {m : ℕ} (u v : Fin (m+1) → V) : Degen.SourceLadder M u v ↔ Degen.SourceLadder N u v := by
  unfold Degen.SourceLadder
  simp_rw [hA,bondsBetween_relabel M N f ha hm ho,directed_relabel_iff M N f ha hm ho]

theorem links_relabel_eq (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x,N.atom (f x) = M.atom x)
    (hm : ∀ x,N.mate (f x) = f (M.mate x)) (ho : ∀ x,N.out (f x) = M.out x) : appbLinks M = appbLinks N := by
  classical
  ext T
  simp only [mem_appbLinks,AppbLink]
  simp_rw [sourceLadder_relabel_iff M N f hA ha hm ho]

theorem linkProduct_relabel_eq (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x,N.atom (f x) = M.atom x)
    (hm : ∀ x,N.mate (f x) = f (M.mate x)) (ho : ∀ x,N.out (f x) = M.out x)
    (L γ δ : ℝ) (P : Finset V → ℝ) : appbLinkProduct M L γ δ P = appbLinkProduct N L γ δ P := by
  unfold appbLinkProduct
  rw [links_relabel_eq M N f hA ha hm ho]

/-- Explicit admissibility transport gives a normalized count bound with
constant one, without any positivity or finite-count hypotheses. -/
theorem linkCountA_le_of_dart_relabeling (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x,N.atom (f x) = M.atom x)
    (hm : ∀ x,N.mate (f x) = f (M.mate x)) (ho : ∀ x,N.out (f x) = M.out x)
    {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d) (P : Finset V → ℝ)
    (A : (D → (Fin d → ℤ)) → Prop) (B : (E → (Fin d → ℤ)) → Prop)
    (hAB : ∀ κ,A κ → B (relabelLabels f κ)) :
    appbLinkCountA M L γ δ C1 w A P ≤ appbLinkCountA N L γ δ C1 w B P := by
  have hh := countE_le_of_dart_relabeling M N f hA ha hm ho L γ δ w A B hAB
  have hr := (numComponents_and_circuitRank_eq_of_dart_equiv M N f hA ha hm ho).2
  have hp := linkProduct_relabel_eq M N f hA ha hm ho L γ δ P
  unfold appbLinkCountA
  rw [hr,hp]
  exact mul_le_mul_left (ENat.toENNReal_mono hh) _

end WaveTurbulence.Mole.AppbAlgorithm
