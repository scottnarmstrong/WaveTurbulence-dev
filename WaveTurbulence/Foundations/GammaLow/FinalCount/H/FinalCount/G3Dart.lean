/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Dart
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Dart`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: dart-level gaps of the cut atoms.**  For a decoration with charge `0` at the degree-`4` atoms of
`M_sub` (`(c_v)`-decorations with `c_v = 0` at degree-`4` atoms, `Molecule.countE`), the two remaining darts of a
cut degree-`4` atom `v₂` have gap `-(gap of the cut)`.  `HGap` records this for every `α`/`β`-atom of degree `2`:
`‖gap(x,y)‖ = ‖gap of the recorded cut‖`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

variable {R : ℕ}

theorem HStep1.gap {h h' : HSt V D₀} (hs : HStep1 L γ η w κ h h') (hG : HGap L w κ h) (hI : Inv R h.s) :
    HGap L w κ h' := by
  cases hs with
  | vine K R' kp hR hkp hu hl ga gb htwin hι₁ hι₂ hsg h3a h3b =>
    have hab := alphaOrBeta_isAB K.post.numComponents h.s.M.numComponents R' kp
    have hne := Cls.ne_eps_of_isAB hab
    have g1 := hG.cut_gen (na := Function.update h.anc K.fa (h.anc K.C.upper)) K.cut_a hu h3a (deg_le_four _ (hI.bounds _ K.cut_a.1)) _ _ hne hne
      h.alive (h.s.pr K.x₁ K.x₂ :: h.hist)
    have hlo : K.C.lower ∈ h.s.M.atoms := Step1.objectAtoms_sub K.C K.b_mem
    have hlne : K.C.lower ≠ K.C.upper := K.ab_ne.symm
    have hlfa : K.C.lower ≠ K.fa := fun e => K.fa_fresh (e ▸ hlo)
    have hcl : (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ (alphaOrBeta K.post.numComponents h.s.M.numComponents R' kp)
        (alphaOrBeta K.post.numComponents h.s.M.numComponents R' kp)).cls K.C.lower = .eps := by
      rw [cutSt_cls_other _ _ hlne hlfa]; exact hl
    have hD : (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).dartsAt K.C.lower = h.s.M.dartsAt K.C.lower :=
      cut_dartsAt_other h.s.M K.cut_a hlne hlfa
    have hdeg : (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = h.s.M.deg K.C.lower :=
      congrArg Finset.card hD
    have h3 := h3b
    have h4 := deg_le_four _ (hI.bounds _ hlo)
    have g2 := g1.cut_gen (na := Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)) K.cut_b hcl (by show 3 ≤ (h.s.M.cut _ _ _ _).deg _; omega)
      (by show (h.s.M.cut _ _ _ _).deg _ ≤ 4; omega) _ _ hne hne (h.s.pr K.x₁ K.x₂ :: h.alive)
      (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
    exact g2.delSt _ K.closed


section tri
variable {s : St.{u} V D₀} (T : TriData s.M)

end tri

end WaveTurbulence.GammaLow.FinalCount.H
