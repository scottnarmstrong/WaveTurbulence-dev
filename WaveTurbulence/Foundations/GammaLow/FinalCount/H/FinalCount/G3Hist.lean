/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RelRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Hist`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: the cutting history** (DH23 Remark `remiota` = L1782, TARGET Remark `remiota` L2150, and the
cut gaps).  An `HSt` is a state `s` together with the chronological list `hist` of the dart pairs of every cut
performed so far (newest first) and, for every atom produced by a cut, a record `(pair, vis)`: the pair of darts of
`M_sub` that the cut used (its gap is *the gap of the atom*) and the list `vis` of the cuts that happened *before* it.
`ι_v ≠ 0` is `IotaHit`: some earlier cut *that is still alive when `v` is cut* (R38(4), DEAD-HIT: it is carried by an atom
present at that moment) has gap `r'` with `0 < |r ± r'| ≤ L^{-50η} R_v` (sign `±`); `κ_v = 50` iff `ι_v ≠ 0`, `κ_v = 0`
otherwise (DH23 Prop `excessprop1`, L1786).  The `vis` of a record is the list of the cuts alive at the time (`HSt.alive`,
plus the earlier cuts of the same operation); `κ_v` is fixed at the creation of `v` and stored in its class.  Cuts of one operation are ordered as in the text
(triangle: `v₁, v₂, v₃`; vine: the two joints), and a cut sees all earlier cuts of the same operation.

The step relations `HStep1..HStep4` are the relations `Step1..Step4` of `G3Steps` with extra data:
* the nonzero gap of every cut (DH23 L1985: no cut at a degenerate atom; the `v₃` of a triangle and the atom of
  Step 4 are not ZG, TARGET Remark `remtame`);
* the two joints of a vine have the same gap up to sign (the *gap of the VC*, TARGET `defdiff`);
* the `ι/κ` relation `κ_v = 50 ↔ ι_v ≠ 0`. -/
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

/-- **Step 1** with history (DH23 L1775). -/
inductive HStep1 (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | vine (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) (R : ℝ) (kp : ℕ) (hR : IsLabel L γ η R) (hkp : kp = 0 ∨ kp = 50)
      (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps)
      (ga : GapSim L w (κ ∘ h.s.down) K.x₁ K.x₂ R) (gb : GapSim L w (κ ∘ h.s.down) K.y₁ K.y₂ R)
      (htwin : pgap L w κ (h.s.pr K.y₁ K.y₂) = pgap L w κ (h.s.pr K.x₁ K.x₂) ∨
        pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂))
      (hι₁ : kp = 50 ↔ IotaHit L η w κ h.alive (h.s.pr K.x₁ K.x₂) R)
      (hι₂ : kp = 50 ↔ IotaHit L η w κ (h.s.pr K.x₁ K.x₂ :: h.alive) (h.s.pr K.y₁ K.y₂) R)
      (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG)
      (h3a : 3 ≤ h.s.M.deg K.C.upper) (h3b : 3 ≤ h.s.M.deg K.C.lower) :
      HStep1 L γ η w κ h
        ⟨vineSt h.s K (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp),
         h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist,
         Function.update (Function.update (Function.update (Function.update h.crec K.C.upper
           (some (h.s.pr K.x₁ K.x₂, h.alive))) K.fa (some (h.s.pr K.x₁ K.x₂, h.alive))) K.C.lower
           (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive))) K.fb
           (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive)),
         Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)⟩

/-! ### Forgetting the history -/

theorem HStep1.step {h h' : HSt V D₀} (hs : HStep1 L γ η w κ h h') : Step1 L γ η w κ h.s h'.s := by
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι₁ hι₂ hsg h3a h3b => exact Step1.vine h.s K R kp hR hkp hu hl ga gb h3a h3b

end WaveTurbulence.GammaLow.FinalCount.H
