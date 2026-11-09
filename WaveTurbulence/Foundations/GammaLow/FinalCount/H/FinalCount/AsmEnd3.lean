/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmEnd3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEnd2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmEnd3`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (HendAt, part 3): `HendAt`.**  Along `Reach1` the number of components of the state stays `≤ 2R - 1`: the first-stage
(CN / root-CL) removals are bounded by `CnBound` (NAMED INPUT: the universe's `cnblock_component_excess_bound` read on `remMol M₀`, owner
S4-SHAPE/garden instantiation) and the Good states have no degree-0 atom; every later vine step is non-increasing (`HostConnF`, NAMED INPUT of
S4-SHAPE) and triple cuts are non-increasing (`cut_sc_of_triple`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **NAMED INPUT (the universe's cnblock bound on the removal of first-stage vines).**  The molecule `M₀` with a pairwise atom-disjoint family
of first-stage collected objects removed has at most `2R` components, and exactly `2R` only with an atom of degree `0`
(`cnblock_component_excess_bound`; garden instantiation: `remMol` is `removeBlockFamily` up to renaming). -/
def CnBound (M₀ : Molecule V D₀) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀))
    (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ))) (Rn : ℕ) : Prop :=
  ∀ κ ∈ A0, ∀ ps : List (Src.Object Src.γL M₀ × Quad D₀), (∀ p ∈ ps, PieceData C Un L γ η w κ p ∧ p.1 ∈ Fst) →
    ps.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) →
    (remMol M₀ ps).numComponents ≤ 2 * Rn ∧
      ((remMol M₀ ps).numComponents = 2 * Rn → ∃ v ∈ (remMol M₀ ps).atoms, (remMol M₀ ps).deg v = 0)

theorem fst_bound {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    {L γ η : ℝ} {w : Mom d} {A0 : Set (D₀ → (Fin d → ℤ))} {Rn : ℕ} {κ : D₀ → (Fin d → ℤ)}
    (hcn : CnBound M₀ C Un Fst L γ η w A0 Rn) (hκ : κ ∈ A0) {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
    {ps : List (Src.Object Src.γL M₀ × Quad D₀)} (hI : ConnData M₀ C Un Fst L γ η w κ h ps) (hg : ∃ R', Good R' h.s)
    (hF : ∀ p ∈ ps, p.1 ∈ Fst) : h.s.M.numComponents + 1 ≤ 2 * Rn := by
  obtain ⟨hinj, hps, hpw, hrem, hpres, he1, he2, he3, hfo⟩ := hI
  obtain ⟨hnum, hdeg, hatoms⟩ := state_rem_iso hA hD ps hinj hpres he1 he2 he3
  obtain ⟨h1, h2⟩ := hcn κ hκ ps (fun p hp => ⟨hps p hp, hF p hp⟩) hpw
  rw [hnum] at h1 h2
  rcases Nat.lt_or_ge h.s.M.numComponents (2 * Rn) with hlt | hge
  · omega
  · have heq : h.s.M.numComponents = 2 * Rn := le_antisymm h1 hge
    obtain ⟨v, hv, hv0⟩ := h2 heq
    rw [hatoms, Finset.mem_image] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    rw [hdeg c hc] at hv0
    obtain ⟨R', hg⟩ := hg
    have := good_deg_pos hg c hc
    omega

theorem endInv_of_reach1 [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} (hS : SubHyp Rn M₀) {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))} {κ : D₀ → (Fin d → ℤ)}
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ U U' : Src.Object Src.γL M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hcn : CnBound M₀ C Un Fst L γ η w A0 Rn) (hHF : HostConnF M₀ C Un Fst L γ η w A0) (hκ : κ ∈ A0)
    {h : HSt V D₀} (hr : Reach1 C Un Fst L γ η w κ h) :
    (∃ ps, ConnData M₀ C Un Fst L γ η w κ h ps ∧ h.s.M.numComponents + 1 ≤ 2 * Rn) ∨
      ((∀ U, Collected C (Un κ) L γ η w κ U → Dartless U h) ∧ h.s.M.numComponents + 1 ≤ 2 * Rn) := by
  induction hr with
  | refl =>
    left
    have hg := (invE_of_reach hS h0 (Relation.ReflTransGen.refl (r := HAny L γ η w κ) (a := HSt.init M₀))).good
    exact ⟨[], connData_init M₀ C Un Fst L γ η w κ,
      fst_bound hcn hκ (AncRel.init M₀) (DartRel.init M₀) (connData_init M₀ C Un Fst L γ η w κ) (let ⟨R', _, hR'⟩ := hg; ⟨R', hR'⟩) (by simp)⟩
  | @tail b h' hrb hs ih =>
    have hrb' : Reach1 C Un Fst L γ η w κ b := hrb
    have hrh : Reach1 C Un Fst L γ η w κ h' := hrb'.tail hs
    have hA := reach1_ancRel hrb'
    have hD := (invE_of_reach hS h0 (Reach1.toAny hrb')).rel
    cases hs with
    | vine K R kp hs U hU hUK hUD hUJ hord =>
      rcases ih with ⟨ps, hI, hF⟩ | ⟨hd, hF⟩
      · left
        have hint : UIntact U b := by
          rcases collInv_of_reach1 hS h0 hdisj hrb' U hU with hd | hi
          · exact absurd (hUD.1) (hd K.x₁)
          · exact hi
        have hI' := connData_vine hA hI K R kp U hU hUK hUD hUJ hord hint
        refine ⟨_, hI', ?_⟩
        by_cases hUF : U ∈ Fst
        · have hA' := reach1_ancRel hrh
          have hD' := (invE_of_reach hS h0 (Reach1.toAny hrh)).rel
          have hg' := (invE_of_reach hS h0 (Reach1.toAny hrh)).good
          refine fst_bound hcn hκ hA' hD' hI' (let ⟨R', _, hR'⟩ := hg'; ⟨R', hR'⟩) ?_
          intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact hUF
          · by_contra hpF
            exact (hI.2.2.2.2.2.2.2.2 ⟨p, hp, hpF⟩ U hUF K.x₁) hUD.1
        · have := vine_F_le_of_hostConnF hHF hκ hA hD hI K U hU hUK hUD hUJ hint hUF
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

/-- **`HendAt`**: `F(end of Step 1) ≤ 2R - 1` from the first-stage bound and the non-increase of the later steps. -/
theorem hendAt_of_inputs [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} (hS : SubHyp Rn M₀) {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))}
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Src.Object Src.γL M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hcn : CnBound M₀ C Un Fst L γ η w A0 Rn) (hHF : HostConnF M₀ C Un Fst L γ η w A0) :
    HendAt M₀ Rn C L γ η w A0 Un Fst (2 * (Rn : ℝ) - 1) := by
  intro A h hinv hAne _
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAne
  obtain ⟨hA0, hctx⟩ := hinv
  obtain ⟨hc, -, hr⟩ := hctx.resolve_left hAne
  have hκ0 : κ ∈ A0 := hA0 hκ
  have hend := endInv_of_reach1 hS (h0 κ hκ0) (hdisj κ hκ0) hcn hHF hκ0 (hr κ hκ)
  have hF : h.s.M.numComponents + 1 ≤ 2 * Rn := by
    rcases hend with ⟨_, _, hF⟩ | ⟨_, hF⟩ <;> exact hF
  have : ((h.s.M.numComponents : ℕ) : ℝ) + 1 ≤ 2 * (Rn : ℝ) := by exact_mod_cast hF
  linarith

end WaveTurbulence.GammaLow.FinalCount.H
