/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain30
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain28
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain30`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, session 6 (4): the end bound with separate indices.**  `endInvL_of_reach1L2`, `hendAtL_of_inputs2` are the
LowChain26 statements with the index of `SubHypL`/`Good` (`Rn = R + k` on `M.unloop`) separated from the index `Rc = R` of `CnBound`
(the ORIGINAL index, equality clause intact): `F ≤ 2 Rc - 1`. -/
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

variable {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem endInvL_of_reach1L2 [Infinite V] {M₀ : Molecule V D₀} {Rn Rc : ℕ} (hS : SubHypL Rn M₀) {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))} {κ : D₀ → (Fin d → ℤ)}
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ U U' : Src.Object Src.γL M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hcn : CnBound M₀ C Un Fst L γ η w A0 Rc) (hHF : HostConnFL M₀ C Un Fst L γ η w A0) (hκ : κ ∈ A0)
    {h : HSt V D₀} (hr : Reach1L C Un Fst L γ η w κ h) :
    (∃ ps, ConnDataL2 M₀ C Un Fst L γ η w κ h ps ∧ h.s.M.numComponents + 1 ≤ 2 * Rc) ∨
      ((∀ U, Collected C (Un κ) L γ η w κ U → Dartless U h) ∧ h.s.M.numComponents + 1 ≤ 2 * Rc) := by
  induction hr with
  | refl =>
    left
    obtain ⟨R', -, hR'⟩ := invL_reach1 hS h0
      (show Reach1L C Un Fst L γ η w κ (HSt.init M₀) from Relation.ReflTransGen.refl)
    exact ⟨[], connDataL2_init M₀ C Un Fst L γ η w κ,
      fst_boundL hcn hκ (AncRel.init M₀) (DartRel.init M₀) (connDataL2_init M₀ C Un Fst L γ η w κ) ⟨R', hR'.good⟩ (by simp)⟩
  | @tail b h' hrb hs ih =>
    have hrb' : Reach1L C Un Fst L γ η w κ b := hrb
    have hrh : Reach1L C Un Fst L γ η w κ h' := hrb'.tail hs
    have hA := reach1L_ancRel hrb'
    have hD : DartRel M₀ b.s := (invL_reach1 hS h0 hrb').choose_spec.2.rel
    cases hs with
    | old hs =>
      cases hs with
      | vine K R kp hs U hU hUK hUD hUJ hord =>
        rcases ih with ⟨ps, hI, hF⟩ | ⟨hd, hF⟩
        · left
          have hint : UIntact U b := by
            rcases collInv_of_reach1L hS h0 hdisj hrb' U hU with hd | hi
            · exact absurd (hUD.1) (hd K.x₁)
            · exact hi
          have hI' := connDataL2_vine hA hI K R kp U hU hUK hUD hUJ hord hint
          refine ⟨_, hI', ?_⟩
          by_cases hUF : U ∈ Fst
          · have hA' := reach1L_ancRel hrh
            have hD' : DartRel M₀ (b.vinePostL K R kp).s := (invL_reach1 hS h0 hrh).choose_spec.2.rel
            have hg' := (invL_reach1 hS h0 hrh).choose_spec.2.good
            refine fst_boundL hcn hκ hA' hD' hI' ⟨_, hg'⟩ ?_
            intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            · exact hUF
            · by_contra hpF
              exact (hI.2.2.2.2 ⟨p, hp, hpF⟩ U hUF K.x₁) hUD.1
          · have h3 := deg3_of_good_post K R kp (invL_reach1 hS h0 hrh).choose_spec.2.good
            have := vine_F_le_of_hostConnFL hHF hκ hA hD hI K U hU hUK hUD hUJ hint hUF h3.1 h3.2
            have e : (b.vinePostL K R kp).s.M.numComponents = K.post.numComponents := rfl
            omega
        · exact absurd (hUD.1) (hd U hU K.x₁)
      | triple _ hs hs3 hall hFle =>
        right
        refine ⟨?_, ?_⟩
        · intro U hU x hx
          cases hs3 with
          | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes => exact hall U hU x hx
        · rcases ih with ⟨ps, hI, hF⟩ | ⟨hd, hF⟩ <;> omega
    | d1 K hs U hU hUK hUD hUJ hord =>
      rcases ih with ⟨ps, hI, hF⟩ | ⟨hd, hF⟩
      · left
        have hint : UIntact U b := by
          rcases collInv_of_reach1L hS h0 hdisj hrb' U hU with hd | hi
          · exact absurd (hUD.1) (hd K.x₁)
          · exact hi
        refine ⟨_, connDataL2_vineG hA hI K U hU hUK hUD hUJ hord hint, ?_⟩
        obtain ⟨K', -, -, hd2, -, -, hK'⟩ := hs.data
        have hj := jdeg2_pos K' hd2
        have hFc := numComponents_vineStG K'
        have hsucc := vine_F_le_succ K'
        have e : (b.vinePostGL K).s.M.numComponents = (vineStG b.s K').M.numComponents := by rw [hK']; rfl
        omega
      · exact absurd (hUD.1) (hd U hU K.x₁)

/-- **`HendAt` for the LOW run** (the `hend` hypothesis of `chain_coverL`): `F(end of Step 1) ≤ 2R - 1`. -/
theorem hendAtL_of_inputs2 [Infinite V] {M₀ : Molecule V D₀} {Rn Rc : ℕ} (hS : SubHypL Rn M₀) {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))}
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Src.Object Src.γL M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hcn : CnBound M₀ C Un Fst L γ η w A0 Rc) (hHF : HostConnFL M₀ C Un Fst L γ η w A0) :
    ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1L M₀ Rn C Un Fst L γ η w A0 A h → A ≠ ∅ →
      (∀ k ∈ A, Stuck1 C L γ η w Un k h) → (h.s.M.numComponents : ℝ) ≤ 2 * (Rc : ℝ) - 1 := by
  intro A h hinv hAne _
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAne
  obtain ⟨hA0, hctx⟩ := hinv
  obtain ⟨hc, -, hr⟩ := hctx.resolve_left hAne
  have hκ0 : κ ∈ A0 := hA0 hκ
  have hend := endInvL_of_reach1L2 hS (h0 κ hκ0) (hdisj κ hκ0) hcn hHF hκ0 (hr κ hκ)
  have hF : h.s.M.numComponents + 1 ≤ 2 * Rc := by
    rcases hend with ⟨_, _, hF⟩ | ⟨_, hF⟩ <;> exact hF
  have : ((h.s.M.numComponents : ℕ) : ℝ) + 1 ≤ 2 * (Rc : ℝ) := by exact_mod_cast hF
  linarith

end WaveTurbulence.GammaLow.FinalCount.H
