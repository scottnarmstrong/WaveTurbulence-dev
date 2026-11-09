/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3HInv`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: the record invariant `HInv`**: every `α`-atom is labelled (`IsLabel`) and carries the record of
its cut with `|gap| ∼ R` and `κ = 50 ↔ ι ≠ 0`; every `β`-atom carries the record of its cut, with nonzero gap. -/
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

theorem HStep1.inv {h h' : HSt V D₀} (hs : HStep1 L γ η w κ h h') (hI : HInv L γ η w κ h) :
    HInv L γ η w κ h' := by
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι₁ hι₂ hsg h3a h3b =>
    have hpa : PSim L w κ (h.s.pr K.x₁ K.x₂) R := ga
    have hpb : PSim L w κ (h.s.pr K.y₁ K.y₂) R := gb
    have e1 : AtomOK L γ η w κ (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp)
        (some (h.s.pr K.x₁ K.x₂, h.alive)) := AtomOK.ofAlphaOrBeta hR hpa hkp hι₁ hsg
    have e2 : AtomOK L γ η w κ (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp)
        (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive)) :=
      AtomOK.ofAlphaOrBeta hR hpb hkp hι₂ (gapKind_of_twin htwin hsg)
    have g1 := hI.cut_gen (na := Function.update h.anc K.fa (h.anc K.C.upper)) K.cut_a.1 K.cut_a.2.1 K.x₁ K.x₂ _ _ _ _ _ e1 e1
      (fun p vis e => mem_of_some List.mem_cons_self e) (fun p vis e => mem_of_some List.mem_cons_self e)
      (fun x hx => List.mem_cons_of_mem _ hx)
      (fun p vis e => sub_of_some (fun q hq => hq) e) (fun p vis e => sub_of_some (fun q hq => hq) e)
      (fun p vis p' vis' e e' => cmp_same e e')
    have g2 := g1.cut_gen (na := Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)) K.cut_b.1 K.cut_b.2.1 K.y₁ K.y₂ _ _ _ _ _ e2 e2
      (fun p vis e => mem_of_some List.mem_cons_self e) (fun p vis e => mem_of_some List.mem_cons_self e)
      (fun x hx => List.mem_cons_of_mem _ hx)
      (fun p vis e => sub_of_some (HSt.alive_cut_sub h _ _ _ _ _ _ _ _ _ _) e)
      (fun p vis e => sub_of_some (HSt.alive_cut_sub h _ _ _ _ _ _ _ _ _ _) e)
      (fun p vis p' vis' e e' => cmp_same e e')
    exact g2.delSt _ K.closed

end WaveTurbulence.GammaLow.FinalCount.H
