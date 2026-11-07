/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformR32IndirectProjection
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformR32FiveTailFiber
import Mathlib.Tactic

/-! # Actual combined count for the indirect-entry branch -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

theorem uniform_r32_indirect_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∃ C L₀ : ℝ, 0 < C ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern)
      (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms),
      M.IsMolecule → (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (S : Finset V) (hS : S ⊆ r.post.atoms) (j : Fin 3) (which : Bool)
      (hcross : appbCrossingBonds M S = {(r.edge j).val,(s.edge ⟨0,by decide⟩).val.val}),
      s.specialAtom which ∈ S → s.specialCompanion which ∈ S → s.specialAtom (!which) ∉ S →
      appbIncidence M (s.specialAtom which) (r.edge j).val = 0 →
      appbCutSign M S (r.edge j).val ≠ appbCutSign M S (s.edge ⟨0,by decide⟩).val.val →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∃ q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (C*L^(4*((d : ℝ)-γ)-31*min γ (1-γ)/48))*
          (appbCountE (r.combinedRemoval s v0).post L γ δ w
            ((r.combinedRemoval s v0).conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  classical
  obtain ⟨Lp,hLp0⟩ := uniform_r32_indirect_projection_bound d hd γ hγ δ hδ m
  obtain ⟨Lt,hLt⟩ := uniform_r32_five_tail_fiber_bound d (by omega) δ γ η hδ hγ hη hηγ
  refine ⟨1,max Lp (max Lt 1),by norm_num,?_⟩
  intro V D instV instF instD L hL hLp M r s v0 hM hsize S hS j which hcross ha hc ho hstar hopp w Adm hLG
  have hL1 : 1 ≤ L := (le_max_right Lt 1).trans ((le_max_right Lp _).trans hL)
  let b := r.combinedRemoval s v0
  obtain ⟨p,q,hp,hE⟩ := b.deletion_countE_exists_post hLp γ δ w Adm
  refine ⟨q,?_⟩
  let Q := b.localChoices p hLp γ δ w Adm
  let f := fun q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ) =>
    fun k => q (appbR32FiveIndices r s j which k)
  have hproj := hLp0 V D L ((le_max_left _ _).trans hL) hLp M r s v0 hM hsize S hS j which hcross ha hc ho hstar hopp p w Adm
  have hfiber (z : Fin 5 → (Fin d → ℤ)) : ((Q.filter (fun q => f q = z)).card : ℝ) ≤ L^(((d : ℝ)-γ)) := by
    have hh := hLt V D L ((le_max_left Lt _).trans ((le_max_right Lp _).trans hL)) hLp M r s v0 S hS j which hcross
      p w Adm hLG (Q.filter (fun q => f q = z)) (filter_subset _ _) z (fun q hq => (mem_filter.mp hq).2)
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hη]))
  have hcount : (Q.card : ℝ) ≤ ((Q.image f).card : ℝ)*L^(((d : ℝ)-γ)) := by
    have hh := card_eq_sum_card_image f Q
    calc
      _ = ∑ z ∈ Q.image f,((Q.filter (fun q => f q = z)).card : ℝ) := by exact_mod_cast hh
      _ ≤ ∑ _z ∈ Q.image f,L^(((d : ℝ)-γ)) := sum_le_sum (fun z _ => hfiber z)
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  have hraw : (Q.card : ℝ) ≤ 1*L^(4*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
    calc
      _ ≤ ((Q.image f).card : ℝ)*L^(((d : ℝ)-γ)) := hcount
      _ ≤ (L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4))*L^(((d : ℝ)-γ)) :=
        mul_le_mul_of_nonneg_right hproj (Real.rpow_nonneg hLp.le _)
      _ ≤ _ := by
        rw [← Real.rpow_add hLp, one_mul]
        apply Real.rpow_le_rpow_of_exponent_le hL1
        have hg : 0 ≤ min γ (1-γ) := le_min hγ.1.le (by linarith [hγ.2])
        linarith
  have hcast := ENat.toENNReal_mono hE
  rw [ENat.toENNReal_mul,ENat.toENNReal_coe] at hcast
  have hraw' : (Q.card : ℝ≥0∞) ≤ ENNReal.ofReal (1*L^(4*((d : ℝ)-γ)-31*min γ (1-γ)/48)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hraw
  exact hcast.trans (mul_le_mul_left hraw' _)

end WaveTurbulence.Mole.AppbAlgorithm
