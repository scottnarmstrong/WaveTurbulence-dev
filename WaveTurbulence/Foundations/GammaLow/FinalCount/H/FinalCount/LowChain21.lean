/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain21
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain20
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain21`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, session 4 (3): along the LOW Step 1 every collected object is dartless or intact, and the removal bookkeeping holds
(`reach1L_ancRel`, `collInv_of_reach1L`, `reach1L_connInv`).** -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem reach1L_ancRel {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h : HSt V D₀}
    (hr : Reach1L C Un Fst L γ η w κ h) : AncRel M₀ h.s h.anc :=
  (rtgH (P := fun h => RunAux M₀ C h) (fun _ _ hs hp => hs.aux hp) hr.toL (RunAux.init C)).2.1

theorem collInv_of_reach1L [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} (hS : SubHypL Rn M₀) {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ U U' : Src.Object Src.γL M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    {h : HSt V D₀} (hr : Reach1L C Un Fst L γ η w κ h) :
    ∀ U, Collected C (Un κ) L γ η w κ U → Dartless U h ∨ UIntact U h := by
  induction hr with
  | refl => exact fun U _ => Or.inr (uIntact_init U)
  | @tail b h' hrb hs ih =>
    have hrb' : Reach1L C Un Fst L γ η w κ b := hrb
    have hA := reach1L_ancRel hrb'
    have hD : DartRel M₀ b.s := (invL_reach1 hS h0 hrb').choose_spec.2.rel
    intro U hU
    cases hs with
    | old hs =>
      cases hs with
      | vine K R kp hs U' hU' hUK hUD hUJ hord =>
        rcases ih U hU with hd | hi
        · exact Or.inl (fun x hx => hd x.1 hx)
        · rcases hdisj U U' hU hU' with hsd | hdis
          · exact Or.inl (dartless_vineSt hA hD K _ U (hsd.1.trans hUK) hi
              ⟨(hsd.2.1 _).2 hUD.1, (hsd.2.1 _).2 hUD.2.1, (hsd.2.1 _).2 hUD.2.2.1, (hsd.2.1 _).2 hUD.2.2.2⟩
              (by
                rcases hUJ with ⟨a, b⟩ | ⟨a, b⟩
                · exact hsd.joint_id (Or.inl ⟨a, b⟩)
                · exact hsd.joint_id (Or.inr ⟨a, b⟩)))
          · exact Or.inr (uIntact_vinePost K R kp U hi (hUK ▸ hdis))
      | triple _ hs hs3 hall _ =>
        exact Or.inl (by
          cases hs3 with
          | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes => exact fun x hx => hall U hU x hx)
    | d1 K hs U' hU' hUK hUD hUJ hord =>
      rcases ih U hU with hd | hi
      · exact Or.inl (fun x hx => hd x.1 hx)
      · rcases hdisj U U' hU hU' with hsd | hdis
        · exact Or.inl (dartless_vineStG hA hD K U (hsd.1.trans hUK) hi
            ⟨(hsd.2.1 _).2 hUD.1, (hsd.2.1 _).2 hUD.2.1, (hsd.2.1 _).2 hUD.2.2.1, (hsd.2.1 _).2 hUD.2.2.2⟩
            (by
              rcases hUJ with ⟨a, b⟩ | ⟨a, b⟩
              · exact hsd.joint_id (Or.inl ⟨a, b⟩)
              · exact hsd.joint_id (Or.inr ⟨a, b⟩)))
        · exact Or.inr (uIntact_vinePostG K U hi (hUK ▸ hdis))

/-- **Along the LOW Step 1, either every collected object is dartless or the removal bookkeeping `ConnInvL` holds.** -/
theorem reach1L_connInv [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} (hS : SubHypL Rn M₀) {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ U U' : Src.Object Src.γL M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    {h : HSt V D₀} (hr : Reach1L C Un Fst L γ η w κ h) :
    (∀ U, Collected C (Un κ) L γ η w κ U → Dartless U h) ∨ ConnInvL M₀ C Un Fst L γ η w κ h := by
  induction hr with
  | refl => exact Or.inr ⟨[], connDataL_init M₀ C Un Fst L γ η w κ⟩
  | @tail b h' hrb hs ih =>
    have hrb' : Reach1L C Un Fst L γ η w κ b := hrb
    have hA := reach1L_ancRel hrb'
    cases hs with
    | old hs =>
      cases hs with
      | vine K R kp hs U hU hUK hUD hUJ hord =>
        rcases ih with hd | hI
        · exact absurd (hUD.1) (hd U hU K.x₁)
        · right
          have hint : UIntact U b := by
            rcases collInv_of_reach1L hS h0 hdisj hrb' U hU with hd | hi
            · exact absurd (hUD.1) (hd K.x₁)
            · exact hi
          obtain ⟨ps, hI⟩ := hI
          exact ⟨_, connDataL_vine hA hI K R kp U hU hUK hUD hUJ hord hint⟩
      | triple _ hs hs3 hall _ =>
        left
        intro U hU x hx
        cases hs3 with
        | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes => exact hall U hU x hx
    | d1 K hs U hU hUK hUD hUJ hord =>
      rcases ih with hd | hI
      · exact absurd (hUD.1) (hd U hU K.x₁)
      · right
        have hint : UIntact U b := by
          rcases collInv_of_reach1L hS h0 hdisj hrb' U hU with hd | hi
          · exact absurd (hUD.1) (hd K.x₁)
          · exact hi
        obtain ⟨ps, hI⟩ := hI
        exact ⟨_, connDataL_vineG hA hI K U hU hUK hUD hUJ hord hint⟩

end WaveTurbulence.GammaLow.FinalCount.H
