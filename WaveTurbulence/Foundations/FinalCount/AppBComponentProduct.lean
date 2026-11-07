/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBGlueParameters
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # Product lower bound for counts on two actual closed component sides -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbSeparatedAdmissibility (M : Molecule V D) (S : Finset V) {d : ℕ}
    (A1 : (AppbSideDart M S → (Fin d → ℤ)) → Prop)
    (A2 : (AppbSideDart M (M.atoms \ S) → (Fin d → ℤ)) → Prop)
    (κ : D → (Fin d → ℤ)) : Prop := A1 (appbSideLabels M S κ) ∧ A2 (appbSideLabels M (M.atoms \ S) κ)

/-- The component count product is realized in the actual full molecule
with explicitly glued parameters. This is valid at zero counts, and does
not assume multiplicativity as a count hypothesis. -/
theorem appb_component_product_le (M : Molecule V D) (S : Finset V) (h : AppbClosedSide M S)
    {d : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (w : Mom d)
    (A1 : (AppbSideDart M S → (Fin d → ℤ)) → Prop)
    (A2 : (AppbSideDart M (M.atoms \ S) → (Fin d → ℤ)) → Prop) :
    appbCountE (appbSideMolecule M S h) L γ δ w A1*
      appbCountE (appbSideMolecule M (M.atoms \ S) h.complement) L γ δ w A2 ≤
        appbCountE M L γ δ w (appbSeparatedAdmissibility M S A1 A2) := by
  classical
  let M1 := appbSideMolecule M S h
  let M2 := appbSideMolecule M (M.atoms \ S) h.complement
  obtain ⟨p1,hp1⟩ := appbCountE_attained M1 hL γ δ w A1
  obtain ⟨p2,hp2⟩ := appbCountE_attained M2 hL γ δ w A2
  let T1 := (p1.decorations_finite hL γ δ w A1).toFinset
  let T2 := (p2.decorations_finite hL γ δ w A2).toFinset
  let glue := fun q : (AppbSideDart M S → (Fin d → ℤ)) × (AppbSideDart M (M.atoms \ S) → (Fin d → ℤ)) =>
    appbGlueLabels M S q.1 q.2
  let T := (T1 ×ˢ T2).image glue
  let p := appbGlueParameters M S h p1 p2
  have hsub : (T : Set _) ⊆ p.decorations L γ δ w (appbSeparatedAdmissibility M S A1 A2) := by
    intro κ hκ
    change κ ∈ (T1 ×ˢ T2).image glue at hκ
    obtain ⟨⟨κ1,κ2⟩,hpair,rfl⟩ := Finset.mem_image.mp hκ
    obtain ⟨hκ1,hκ2⟩ := mem_product.mp hpair
    have hh1 : κ1 ∈ p1.decorations L γ δ w A1 := (p1.decorations_finite hL γ δ w A1).mem_toFinset.mp hκ1
    have hh2 : κ2 ∈ p2.decorations L γ δ w A2 := (p2.decorations_finite hL γ δ w A2).mem_toFinset.mp hκ2
    refine ⟨appb_isDecoration_glue M S h L w p1 p2 κ1 κ2 hh1.1 hh2.1,
      appb_isRestricted_glue M S h L γ δ w p1 p2 κ1 κ2 hh1.2.1 hh2.2.1,?_⟩
    change A1 (appbSideLabels M S (appbGlueLabels M S κ1 κ2)) ∧
      A2 (appbSideLabels M (M.atoms \ S) (appbGlueLabels M S κ1 κ2))
    rw [appbGlueLabels_left,appbGlueLabels_right]
    exact ⟨hh1.2.2,hh2.2.2⟩
  have hc : T.card = T1.card*T2.card := by
    rw [Finset.card_image_of_injective _ (appbGlueLabels_injective M S),card_product]
  have hbound : (T.card : ℕ∞) ≤ appbCountE M L γ δ w (appbSeparatedAdmissibility M S A1 A2) := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    refine (Set.encard_mono hsub).trans ?_
    rw [appbCountE_eq_iSup]
    exact le_iSup_of_le p le_rfl
  have hcard1 : (T1.card : ℕ∞) = appbCountE M1 L γ δ w A1 :=
    (p1.decorations_finite hL γ δ w A1).encard_eq_coe_toFinset_card.symm.trans hp1
  have hcard2 : (T2.card : ℕ∞) = appbCountE M2 L γ δ w A2 :=
    (p2.decorations_finite hL γ δ w A2).encard_eq_coe_toFinset_card.symm.trans hp2
  rw [hc,Nat.cast_mul,hcard1,hcard2] at hbound
  exact hbound

end WaveTurbulence.Mole
