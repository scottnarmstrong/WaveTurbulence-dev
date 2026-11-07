/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GV12
public import WaveTurbulence.Foundations.FinalCount.G3VineLG8
/-! **G3-LOWDEG port of `G3VineLG8`** (only the declarations that change: `SubHypL->SubHypL`, `HRunL->HRunL`, `InvL->InvL`, `FinalStructM->FinalStructM`, `Prop95ConclAtL->Prop95ConclAtL`; names get suffix `L`). -/
@[expose] public section
open WaveTurbulence.VineParamContract

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R R₀ : ℕ} {Tm : V → Prop}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

theorem nonEps_gap_ne_zeroL (hrec : HInv L γ η w κ hf) (hC : Prop95ConclAtL L γ η w κ R hf Tm) {j : V}
    (hj : j ∈ hf.s.M.atoms) (hne : hf.s.cls j ≠ .eps) {g : Mom d} (hg : AtomGap L w κ hf j g) : g ≠ 0 := by
  obtain ⟨p, vis, hr, rfl⟩ := hg
  have ok := hrec.ok j hj
  rcases hC.struct.ab_cls j hj hne with ⟨ρ, kp, h⟩ | h
  · obtain ⟨hlab, p', vis', hr', hps, -⟩ := ok.1 ρ kp h
    rw [hr] at hr'
    simp only [Option.some.injEq, Prod.mk.injEq] at hr'
    rw [hr'.1]
    exact hps.ne_zero hlab.pos
  · obtain ⟨p', vis', hr', hnz⟩ := ok.2 h
    rw [hr] at hr'
    simp only [Option.some.injEq, Prod.mk.injEq] at hr'
    rw [hr'.1]; exact hnz

/-- **The gap at a joint of a final vine component is LG.** -/
theorem joint_LGL (hS : SubHypL R₀ M₀) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hC : Prop95ConclAtL L γ η w κ R hf Tm) (hT : TameFree hf Tm a₀) (hrec : HInv L γ η w κ hf) (hdp : DPInv hf)
    {C : CollData M₀} {Unsel : Set (Object M₀)} (obl : SubproOblG C L γ η w κ) (hU : C.UnselOK L γ η w κ Unsel)
    (hrem1 : ∀ i, ∀ x : hf.s.D, ¬ (C.collection i).ContainsDart (hf.s.down x))
    (hrem2 : ∀ U ∈ C.C2Can L γ η w κ Unsel, ∀ x : hf.s.D, ¬ U.ContainsDart (hf.s.down x))
    (hdes : DesRecN C hf) (J : FinalJoints hf a₀ j₁ j₂) {X : VineType}
    (hv : (compMol hf.s.M a₀).IsVine X (compMol hf.s.M a₀).atoms j₁ j₂) (x y : hf.s.D)
    (hx : hf.s.M.atom x = j₁) (hy : hf.s.M.atom y = j₁) (hox : hf.s.M.out x = false) (hoy : hf.s.M.out y = true) :
    L ^ (-γ + η) < ‖Molecule.kvec L w (κ ∘ hf.s.down) x - Molecule.kvec L w (κ ∘ hf.s.down) y‖ := by
  obtain ⟨P, hPat, hPup, hPlo, hgap, hPa, hPb⟩ := final_vine_object'L J hA hD hS hv
  obtain ⟨r, hr, hre⟩ := hgap L w κ x y hx hy hox hoy
  have hno := no_SGL hS hA hD hC hT hrec hdp obl hU hrem1 hrem2 hdes J P hPat hPup hPlo hPa hPb
  have hnSG : Molecule.gapKind L γ η r ≠ .SG := fun h => hno ⟨r, hr, h⟩
  have hne : hf.s.cls j₁ ≠ .eps := J.n1
  obtain ⟨g, hg, hgg⟩ := hC.dartGap j₁ J.m1 hne x y hx hy hox hoy
  have hg0 := nonEps_gap_ne_zeroL hrec hC J.m1 J.n1 hg
  have hxy0 : Molecule.gapAt L w (κ ∘ hf.s.down) x y ≠ 0 := by
    rcases hgg with h | h
    · rw [h]; exact hg0
    · rw [h]; exact neg_ne_zero.2 hg0
  have hr0 : r ≠ 0 := by
    rw [hre]
    have : Molecule.gapAt L w (κ ∘ hf.s.down) y x = -Molecule.gapAt L w (κ ∘ hf.s.down) x y := by
      unfold Molecule.gapAt; abel
    rw [this]; exact neg_ne_zero.2 hxy0
  have hlt := lt_norm_of_LGL (kind_LG_of hr0 hnSG)
  rw [hre] at hlt
  unfold Molecule.gapAt at hlt
  rwa [norm_sub_rev] at hlt

theorem joint_LG2L (hS : SubHypL R₀ M₀) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hC : Prop95ConclAtL L γ η w κ R hf Tm) (hT : TameFree hf Tm a₀) (hrec : HInv L γ η w κ hf) (hdp : DPInv hf)
    {C : CollData M₀} {Unsel : Set (Object M₀)} (obl : SubproOblG C L γ η w κ) (hU : C.UnselOK L γ η w κ Unsel)
    (hrem1 : ∀ i, ∀ x : hf.s.D, ¬ (C.collection i).ContainsDart (hf.s.down x))
    (hrem2 : ∀ U ∈ C.C2Can L γ η w κ Unsel, ∀ x : hf.s.D, ¬ U.ContainsDart (hf.s.down x))
    (hdes : DesRecN C hf) (J : FinalJoints hf a₀ j₁ j₂) {X : VineType}
    (hv : (compMol hf.s.M a₀).IsVine X (compMol hf.s.M a₀).atoms j₁ j₂) (x y : hf.s.D)
    (hx : hf.s.M.atom x = j₁) (hy : hf.s.M.atom y = j₁) (hxy : hf.s.M.out x ≠ hf.s.M.out y) :
    L ^ (-γ + η) < ‖Molecule.kvec L w (κ ∘ hf.s.down) x - Molecule.kvec L w (κ ∘ hf.s.down) y‖ := by
  cases hox : hf.s.M.out x
  · have hoy : hf.s.M.out y = true := by
      cases h : hf.s.M.out y
      · exact absurd (hox.trans h.symm) hxy
      · rfl
    exact joint_LGL hS hA hD hC hT hrec hdp obl hU hrem1 hrem2 hdes J hv x y hx hy hox hoy
  · have hoy : hf.s.M.out y = false := by
      cases h : hf.s.M.out y
      · rfl
      · exact absurd (hox.trans h.symm) hxy
    rw [norm_sub_rev]
    exact joint_LGL hS hA hD hC hT hrec hdp obl hU hrem1 hrem2 hdes J hv y x hy hx hoy hox

end WaveTurbulence.FinalCountG3

