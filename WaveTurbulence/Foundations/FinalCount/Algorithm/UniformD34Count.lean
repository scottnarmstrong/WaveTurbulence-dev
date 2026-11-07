/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD34BoundarySigns
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformStarCut
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameReindex
import Mathlib.Tactic

/-! # Actual five-label counting for all four degree-three/four groups -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

theorem uniform_d34_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (k : AppbPatternKind) (hk : k ∈ appbD34Kinds)
      (r : AppbRealization M k.pattern), M.IsMolecule →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      ∃ q : Fin k.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4))*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_star_cut_projection_bound d hd γ hγ δ hδ 1
  refine ⟨max L₀ (Real.exp 1),?_⟩
  intro V D instV instF instD L hL hLp M k hk r hM w Adm
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr ((le_max_right _ _).trans hL)
  have ht : ∀ k ∈ appbD34Kinds,1 ∈ k.pattern.removed ∧ k.pattern.removed.card = 2 := by decide
  have hv : r.vertex 1 ∈ r.removedAtoms := mem_image_of_mem _ (ht k hk).1
  have hc : (r.removedAtoms.card : ℝ) ≤ (1+Real.log L)^1 := by
    have hh : r.removedAtoms.card ≤ 2 := by
      change (k.pattern.removed.image r.vertex).card ≤ 2
      exact card_image_le.trans_eq (ht k hk).2
    have hh' : (r.removedAtoms.card : ℝ) ≤ 2 := by exact_mod_cast hh
    simpa only [pow_one] using hh'.trans (by linarith only [hlog])
  let π : Equiv.Perm (Fin 3) := Equiv.ofBijective ![2,0,1] (by decide)
  let t := (appbD34Frame k hk r).reindex π
  let e : Fin 5 ↪ Fin k.pattern.edges.length :=
    (⟨![2,0,1,3,4],by decide⟩ : Fin 5 ↪ Fin 5).trans (appbFiveEmbedding (appb_d34_kind_length k hk))
  have he : Function.Surjective e := (finCongr (appb_d34_kind_length k hk).symm).surjective.comp
    (Finite.surjective_of_injective (⟨![2,0,1,3,4],by decide⟩ : Fin 5 ↪ Fin 5).injective)
  obtain ⟨p,q,hp,hE⟩ := r.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  have hN := hL₀ V D L ((le_max_left _ _).trans hL) hLp M _ r hM (r.vertex 1) hv t r.removedAtoms
    (appbD34CutTriple k hk r) hc (appb_d34_boundary_signs_not_all k hk r hM) e
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl) p w Adm
  have hinj : Function.Injective (fun q : Fin k.pattern.edges.length → (Fin d → ℤ) => fun j => q (e j)) := by
    intro q q' hh
    funext i
    obtain ⟨j,rfl⟩ := he i
    exact congrFun hh j
  rw [card_image_of_injective _ hinj] at hN
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hN' : ((r.localChoices p hLp γ δ w Adm).card : ℝ≥0∞) ≤
      ENNReal.ofReal (L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hN
  exact hcast.trans (mul_le_mul_left hN' _)

end WaveTurbulence.Mole.AppbAlgorithm
