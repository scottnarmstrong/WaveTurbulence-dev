/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutSameSignChoices
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFixedThirdFine
import Mathlib.Tactic

/-! # Same-direction cut pair followed by an LG internal pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Conditional reconstruction helper. Its only algebraic reconstruction
premise is injectivity of the actual triple projection; concrete figure
exports prove this independently from momentum conservation. -/
theorem appb_cut_triple_card_bound_of_projection_injective (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ η : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P)
      (S : Finset V) (cut : AppbCutPair r S),
      appbCutSign M S (r.edge cut.first).val = appbCutSign M S (r.edge cut.second).val →
      (S.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ v ∈ r.removedAtoms,∀ t : AppbTripleFrame r v, cut.first = t.index 2 →
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      Set.InjOn (t.project (K := Fin d → ℤ)) (r.localChoices p hLp γ δ w Adm : Set _) →
      (appbIncidenceSign M v (r.edge (t.index 0)).val ≠ appbIncidenceSign M v (r.edge (t.index 1)).val →
        ∀ κ,κ ∈ p.decorations L γ δ w Adm →
        L^(-γ+η) ≤ ‖Molecule.kvec L w κ (r.edge (t.index 0)).val-
          Molecule.kvec L w κ (r.edge (t.index 1)).val‖) →
      ((r.localChoices p hLp γ δ w Adm).card : ℝ) ≤
        L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
  classical
  obtain ⟨Lb,hLb⟩ := appb_cut_same_sign_projection_bound (V := V) (D := D) d hd γ hγ δ hδ m
  obtain ⟨Li,hLi⟩ := appb_triple_fixed_third_fine_bound (V := V) (D := D) d hd δ γ η hδ hγ hη hηγ
  refine ⟨max Lb (max Li 1),?_⟩
  intro L hL hLp M P r S cut hsame hcard v hv t hthird p w Adm hinj hgap
  let Q := r.localChoices p hLp γ δ w Adm
  let f := fun q : Fin P.edges.length → (Fin d → ℤ) => (q cut.first,q cut.second)
  have hL1 : 1 ≤ L := (le_max_right Li 1).trans ((le_max_right Lb _).trans hL)
  have hb := hLb L ((le_max_left _ _).trans hL) hLp M P r S cut hsame hcard p w Adm
  have hfiber (z : (Fin d → ℤ) × (Fin d → ℤ)) :
      ((Q.filter fun q => f q = z).card : ℝ) ≤ L^((d : ℝ)-γ) := by
    let T := Q.filter fun q => f q = z
    have hT : T ⊆ Q := filter_subset _ _
    have hz : ∀ q ∈ T,q (t.index 2) = z.1 := by
      intro q hq
      rw [← hthird]
      exact congrArg Prod.fst (mem_filter.mp hq).2
    have hh := hLi L ((le_max_left Li _).trans ((le_max_right Lb _).trans hL)) hLp M P r v hv t p w Adm z.1 T hT hz hgap
    have hi : Set.InjOn (fun q : Fin P.edges.length → (Fin d → ℤ) => (q (t.index 0),q (t.index 1))) (T : Set _) := by
      intro q hq q' hq' he
      apply hinj (hT hq) (hT hq')
      funext j
      fin_cases j
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
      · exact (hz q hq).trans (hz q' hq').symm
    rw [card_image_of_injOn hi] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hη]))
  have hcount : (Q.card : ℝ) ≤ (Q.image f).card*L^((d : ℝ)-γ) := by
    have hc := card_eq_sum_card_image f Q
    calc
      _ = ∑ z ∈ Q.image f,((Q.filter fun q => f q = z).card : ℝ) := by exact_mod_cast hc
      _ ≤ ∑ _z ∈ Q.image f,L^((d : ℝ)-γ) := sum_le_sum (fun z hz => hfiber z)
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  calc
    _ ≤ (Q.image f).card*L^((d : ℝ)-γ) := hcount
    _ ≤ L^((d : ℝ)-γ-31*min γ (1-γ)/48)*L^((d : ℝ)-γ) :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hLp.le _)
    _ = _ := by rw [← Real.rpow_add hLp]; congr 1; ring

end WaveTurbulence.Mole
