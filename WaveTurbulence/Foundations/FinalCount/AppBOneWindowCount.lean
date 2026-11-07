/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBEnergyBins
public import WaveTurbulence.Foundations.FinalCount.AppBFiniteCounts
import Mathlib.Tactic

/-! # Counting with one enlarged energy window by finitely many original windows -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Only the selected vertex has a widened energy window. All other
energy windows, all localizers, and the admissibility predicate are kept
in the actual count. No global change of delta is made. -/
theorem appb_one_window_count_le (M : Molecule V D) {d : ℕ} {L γ δ : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (w : Mom d) (p : AppbCountParameters M d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (v : V) (hv : v ∈ M.atoms) (N : ℕ)
    (S : Finset (D → (Fin d → ℤ)))
    (hs : ∀ κ ∈ S,M.IsDecoration L w p.momentum κ ∧ Adm κ ∧
      (∀ x,‖Molecule.kvec L w κ x-p.center x‖ ≤ 1) ∧
      (∀ a ∈ M.atoms, |M.Gamma L w κ a-p.energy a| ≤
        (if a = v then (N : ℝ) else 1)*(δ⁻¹*L^(-2*γ)))) :
    (S.card : ℕ∞) ≤ (2*N+2)*appbCountE M L γ δ w Adm := by
  classical
  let τ := δ⁻¹*L^(-2*γ)
  have hτ : 0 < τ := by unfold τ; positivity
  let T : ℤ → Finset (D → (Fin d → ℤ)) := fun i =>
    S.filter fun κ => |M.Gamma L w κ v-(p.energy v+(i : ℝ)*τ)| ≤ τ
  have hcover : S ⊆ (appbEnergyBins N).biUnion T := by
    intro κ hκ
    have hx := (hs κ hκ).2.2.2 v hv
    simp only [if_pos rfl] at hx
    obtain ⟨i,hi,hbin⟩ := appb_exists_energy_bin N hτ (M.Gamma L w κ v) (p.energy v) hx
    exact mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨hκ,hbin⟩⟩
  have hTi (i : ℤ) : ((T i).card : ℕ∞) ≤ appbCountE M L γ δ w Adm := by
    let pi : AppbCountParameters M d := {p with energy := Function.update p.energy v (p.energy v+(i : ℝ)*τ)}
    have hsub : (T i : Set _) ⊆ pi.decorations L γ δ w Adm := by
      intro κ hκ
      obtain ⟨hS,hbin⟩ := mem_filter.mp hκ
      have hh := hs κ hS
      refine ⟨hh.1,⟨?_,hh.2.2.1⟩,hh.2.1⟩
      intro a ha
      by_cases hav : a = v
      · subst a
        simpa only [pi,Function.update_self] using hbin
      · have he := hh.2.2.2 a ha
        simpa only [pi,Function.update_of_ne hav,if_neg hav,one_mul] using he
    rw [← Set.encard_coe_eq_coe_finsetCard]
    exact (Set.encard_mono hsub).trans (by rw [appbCountE_eq_iSup]; exact le_iSup (fun pp : AppbCountParameters M d => (pp.decorations L γ δ w Adm).encard) pi)
  have hc : S.card ≤ ∑ i ∈ appbEnergyBins N,(T i).card :=
    (card_le_card hcover).trans card_biUnion_le
  have hc' : (S.card : ℕ∞) ≤ ∑ i ∈ appbEnergyBins N,((T i).card : ℕ∞) := by exact_mod_cast hc
  refine hc'.trans ((sum_le_sum (fun i hi => hTi i)).trans_eq ?_)
  rw [sum_const,nsmul_eq_mul,appbEnergyBins_card]
  push_cast
  rfl

end WaveTurbulence.Mole
