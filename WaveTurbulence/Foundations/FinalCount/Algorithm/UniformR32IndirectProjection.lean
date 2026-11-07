/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBR32IndirectSigns
public import WaveTurbulence.Foundations.FinalCount.AppBR32Frame
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformStarCut
import Mathlib.Tactic

/-! # The coupled five-label gain in the indirect-entry branch of 3R-2G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

theorem uniform_r32_indirect_projection_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (m : ℕ) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern)
      (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms),
      M.IsMolecule → (M.atoms.card : ℝ) ≤ (1+Real.log L)^m →
    ∀ (S : Finset V) (hS : S ⊆ r.post.atoms) (j : Fin 3) (which : Bool)
      (hcross : appbCrossingBonds M S = {(r.edge j).val,(s.edge ⟨0,by decide⟩).val.val}),
      s.specialAtom which ∈ S → s.specialCompanion which ∈ S → s.specialAtom (!which) ∉ S →
      appbIncidence M (s.specialAtom which) (r.edge j).val = 0 →
      appbCutSign M S (r.edge j).val ≠ appbCutSign M S (s.edge ⟨0,by decide⟩).val.val →
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      ((((r.combinedRemoval s v0).localChoices p hLp γ δ w Adm).image
        (fun q k => q (appbR32FiveIndices r s j which k))).card : ℝ) ≤
        L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) := by
  obtain ⟨L₀,hL₀⟩ := uniform_star_cut_projection_bound d hd γ hγ δ hδ m
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M r s v0 hM hsize S hS j which hcross ha hc ho hstar hopp p w Adm
  let b := r.combinedRemoval s v0
  let T := S \ {s.specialAtom which}
  let cut := appbR32IndirectCut r s v0 S hS j which hcross ha hc ho hstar
  let t := appbR32Frame r s v0 (Equiv.swap j 0)
  have hv := appb_r32_center_removed r s v0
  have hcard : (T.card : ℝ) ≤ (1+Real.log L)^m := by
    have hh := Finset.card_le_card cut.subset_atoms
    exact (show (T.card : ℝ) ≤ (M.atoms.card : ℝ) by exact_mod_cast hh).trans hsize
  apply hL₀ V D L hL hLp M _ b hM (r.vertex 1) hv t T cut hcard
    (appb_r32_indirect_cut_sign_cap r s v0 hM S hS j which hcross ha hc ho hstar hopp)
    (appbR32FiveIndices r s j which)
    (by intro k; fin_cases k <;> rfl) (by intro k; rfl) p w Adm

end WaveTurbulence.Mole.AppbAlgorithm
