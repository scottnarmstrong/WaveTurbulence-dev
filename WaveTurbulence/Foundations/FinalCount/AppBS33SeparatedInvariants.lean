/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBComponentHullInvariants
public import WaveTurbulence.Foundations.FinalCount.AppBS33ComponentCount
public import WaveTurbulence.Foundations.FinalCount.AppBSourceReinsertGap
public import WaveTurbulence.Foundations.FinalCount.AppBSourceReinsertValidScales
import Mathlib.Tactic

/-! # The actual separated 3S3 output retains LG and valid physical scales -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_s33_separated_iff_componentHull {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) {d : ℕ}
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (ζ : Degen.RetainedDart M r.removedAtoms ⊕ Bool → (Fin d → ℤ)) :
    appbS33SeparatedPostAdmissibility r Adm ζ ↔
      appbComponentHull (r.directedPostWithBond 3 5 ⟨1,by decide⟩) (appbS33Side r)
        (r.reinsertedPostAdmissibility Adm ⟨1,by decide⟩) ζ := by
  constructor
  · rintro ⟨⟨κ,hκ,hm,he⟩,hR⟩
    exact ⟨⟨r.reinsertedLabels κ ⟨1,by decide⟩,⟨κ,hκ,hm,rfl⟩,he⟩,hR⟩
  · rintro ⟨⟨ζ',⟨κ,hκ,hm,hr⟩,he⟩,hR⟩
    subst ζ'
    exact ⟨⟨κ,hκ,hm,he⟩,hR⟩

theorem appb_s33_separated_largeGap {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    {d : ℕ} {L γ γ0 g : ℝ} (hL : 0 ≤ L) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (hLG : ∀ κ,Adm κ → AppbLargeGap M L w κ g)
    (htest : ∀ κ,Adm κ → AppbS33LabelConditions M r L γ γ0 w κ)
    {ζ : Degen.RetainedDart M r.removedAtoms ⊕ Bool → (Fin d → ℤ)}
    (hζ : appbS33SeparatedPostAdmissibility r Adm ζ) :
    AppbLargeGap (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L w ζ (g-L^(-γ)) := by
  apply appb_componentHull_largeGap _ _ L w (r.reinsertedPostAdmissibility Adm ⟨1,by decide⟩) (g-L^(-γ)) _
    ((appb_s33_separated_iff_componentHull r Adm ζ).mp hζ)
  intro ζ' hζ'
  obtain ⟨κ,hκ,hm,rfl⟩ := hζ'
  exact appb_s33_reinsert_largeGap r hg w κ hm (hLG κ hκ) (htest κ hκ) hL

theorem appb_s33_separated_validLinkScales {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    {d : ℕ} {L c : ℝ} {w : Mom d} {Adm : (D → (Fin d → ℤ)) → Prop}
    {scales : Finset V → ℝ} (h : AppbValidLinkScales M L w Adm c scales) :
    AppbValidLinkScales (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L w
      (appbS33SeparatedPostAdmissibility r Adm) c
      (appbReinsertScales M r.removedAtoms (r.vertex 3) (r.vertex 5) scales) := by
  apply ((r.reinsertedPost_validLinkScales 3 5 ⟨1,by decide⟩ h).componentHull
    (appb_s33_reinsert_closedSide M r (appb_s33_splitTopology_of_geometry hg) ⟨1,by decide⟩)).mono
  intro ζ hζ
  exact (appb_s33_separated_iff_componentHull r Adm ζ).mp hζ

end WaveTurbulence.Mole
