/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineLG8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.FinalCount.G3VineBridge
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3VineLG8`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: `vineLG`, part 8: the joint gaps of a final vine component are LG, and `VineLGAt`.**

Low-range change (L6-HG3): the vine hypothesis `{X : VineType} (hv : (compMol …).IsVine X …)` of `joint_LG`,
`joint_LG2` is the family member `Src.IsSomeVine Src.γL (compMol …) …` (main's `∃ X, IsVine X`, PLAN-L6 §3e);
`finalJoints_of_someVine` is main's `FinalCountG3.finalJoints_of_vine` (`FinalCount/G3VineBridge.lean`, sha256 in
`H-G3-COPIED-SHA256SUMS`) for a family member (its proof uses only the block part). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R R₀ : ℕ} {Tm : V → Prop}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

/-- A component of the final molecule that is a member of the low family has the shape `FinalJoints` (main's
`finalJoints_of_vine`, proof copied with `hv.1` → `hv.block`). -/
theorem finalJoints_of_someVine {R : ℕ} (hst : FinalStruct R hf.s)
    (hv : Src.IsSomeVine Src.γL (compMol hf.s.M a₀) (compMol hf.s.M a₀).atoms j₁ j₂) (ha₀ : a₀ ∈ hf.s.M.atoms) :
    FinalJoints hf a₀ j₁ j₂ := by
  obtain ⟨-, h1, h2, hne, o1, i1, o2, i2, hd, -⟩ := hv.block
  have m1 := (mem_compMol _ _).1 h1
  have m2 := (mem_compMol _ _).1 h2
  have hg := compMol_grp hf a₀
  have d1 : hf.s.M.deg j₁ = 2 := by
    rw [← compMol_deg hf.s.M a₀ m1.2, deg_eq, ← outIn_of_all hg, ← inIn_of_all hg, o1, i1]
  have d2 : hf.s.M.deg j₂ = 2 := by
    rw [← compMol_deg hf.s.M a₀ m2.2, deg_eq, ← outIn_of_all hg, ← inIn_of_all hg, o2, i2]
  refine ⟨m1.1, m2.1, hne, m1.2, m2.2, d1, d2, ?_, ?_, ?_⟩
  · intro h; have := hst.eps_deg j₁ m1.1 h; omega
  · intro h; have := hst.eps_deg j₂ m2.1 h; omega
  · intro b hb hbc
    by_cases e1 : b = j₁
    · exact Or.inl e1
    by_cases e2 : b = j₂
    · exact Or.inr (Or.inl e2)
    right; right
    have hbm : b ∈ (compMol hf.s.M a₀).atoms := (mem_compMol _ _).2 ⟨hb, hbc⟩
    have h4 := hd b hbm e1 e2
    have hdeg : hf.s.M.deg b = 4 := by
      rw [← compMol_deg hf.s.M a₀ hbc, ← degIn_of_all hg]; exact h4
    refine ⟨?_, hdeg⟩
    by_contra hne'
    have := hst.ab_deg b hb hne'
    omega

/-- **The gap at a joint of a final vine component is LG.** -/
theorem joint_LG (hS : SubHyp R₀ M₀) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hC : Prop95ConclAt L γ η w κ R hf Tm) (hT : TameFree hf Tm a₀) (hrec : HInv L γ η w κ hf) (hdp : DPInv hf)
    {C : CollData M₀} {Unsel : Set (Src.Object Src.γL M₀)} (obl : SubproOblG C L γ η w κ) (hU : C.UnselOK L γ η w κ Unsel)
    (hrem1 : ∀ i, ∀ x : hf.s.D, ¬ (C.collection i).ContainsDart (hf.s.down x))
    (hrem2 : ∀ U ∈ C.C2Can L γ η w κ Unsel, ∀ x : hf.s.D, ¬ U.ContainsDart (hf.s.down x))
    (hdes : DesRecN C hf) (J : FinalJoints hf a₀ j₁ j₂)
    (hv : Src.IsSomeVine Src.γL (compMol hf.s.M a₀) (compMol hf.s.M a₀).atoms j₁ j₂) (x y : hf.s.D)
    (hx : hf.s.M.atom x = j₁) (hy : hf.s.M.atom y = j₁) (hox : hf.s.M.out x = false) (hoy : hf.s.M.out y = true) :
    L ^ (-γ + η) < ‖Molecule.kvec L w (κ ∘ hf.s.down) x - Molecule.kvec L w (κ ∘ hf.s.down) y‖ := by
  obtain ⟨P, hPat, hPup, hPlo, hgap, hPa, hPb⟩ := final_vine_object' J hA hD hS hv
  obtain ⟨r, hr, hre⟩ := hgap L w κ x y hx hy hox hoy
  have hno := no_SG hS hA hD hC hT hrec hdp obl hU hrem1 hrem2 hdes J P hPat hPup hPlo hPa hPb
  have hnSG : Molecule.gapKind L γ η r ≠ .SG := fun h => hno ⟨r, hr, h⟩
  have hne : hf.s.cls j₁ ≠ .eps := J.n1
  obtain ⟨g, hg, hgg⟩ := hC.dartGap j₁ J.m1 hne x y hx hy hox hoy
  have hg0 := nonEps_gap_ne_zero hrec hC J.m1 J.d1.le hg
  have hxy0 : Molecule.gapAt L w (κ ∘ hf.s.down) x y ≠ 0 := by
    rcases hgg with h | h
    · rw [h]; exact hg0
    · rw [h]; exact neg_ne_zero.2 hg0
  have hr0 : r ≠ 0 := by
    rw [hre]
    have : Molecule.gapAt L w (κ ∘ hf.s.down) y x = -Molecule.gapAt L w (κ ∘ hf.s.down) x y := by
      unfold Molecule.gapAt; abel
    rw [this]; exact neg_ne_zero.2 hxy0
  have hlt := lt_norm_of_LG (kind_LG_of hr0 hnSG)
  rw [hre] at hlt
  unfold Molecule.gapAt at hlt
  rwa [norm_sub_rev] at hlt

theorem joint_LG2 (hS : SubHyp R₀ M₀) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hC : Prop95ConclAt L γ η w κ R hf Tm) (hT : TameFree hf Tm a₀) (hrec : HInv L γ η w κ hf) (hdp : DPInv hf)
    {C : CollData M₀} {Unsel : Set (Src.Object Src.γL M₀)} (obl : SubproOblG C L γ η w κ) (hU : C.UnselOK L γ η w κ Unsel)
    (hrem1 : ∀ i, ∀ x : hf.s.D, ¬ (C.collection i).ContainsDart (hf.s.down x))
    (hrem2 : ∀ U ∈ C.C2Can L γ η w κ Unsel, ∀ x : hf.s.D, ¬ U.ContainsDart (hf.s.down x))
    (hdes : DesRecN C hf) (J : FinalJoints hf a₀ j₁ j₂)
    (hv : Src.IsSomeVine Src.γL (compMol hf.s.M a₀) (compMol hf.s.M a₀).atoms j₁ j₂) (x y : hf.s.D)
    (hx : hf.s.M.atom x = j₁) (hy : hf.s.M.atom y = j₁) (hxy : hf.s.M.out x ≠ hf.s.M.out y) :
    L ^ (-γ + η) < ‖Molecule.kvec L w (κ ∘ hf.s.down) x - Molecule.kvec L w (κ ∘ hf.s.down) y‖ := by
  cases hox : hf.s.M.out x
  · have hoy : hf.s.M.out y = true := by
      cases h : hf.s.M.out y
      · exact absurd (hox.trans h.symm) hxy
      · rfl
    exact joint_LG hS hA hD hC hT hrec hdp obl hU hrem1 hrem2 hdes J hv x y hx hy hox hoy
  · have hoy : hf.s.M.out y = false := by
      cases h : hf.s.M.out y
      · rfl
      · exact absurd (hox.trans h.symm) hxy
    rw [norm_sub_rev]
    exact joint_LG hS hA hD hC hT hrec hdp obl hU hrem1 hrem2 hdes J hv y x hy hx hoy hox

end WaveTurbulence.GammaLow.FinalCount.H
