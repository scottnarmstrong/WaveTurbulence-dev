/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain25
/-! **FINALCOUNT LOW-CHAIN, session 5 (4): `HendAtL`.**  Along `Reach1L` the number of components of the state stays `≤ 2R - 1`:
first-stage vine removals by `CnBound` on `remMol` (`fst_boundL`, with the isolated joints deleted by Step D1), later old vine steps by
`HostConnFL`, Step D1 never increases the number of components (`K.post.F ≤ F + 1` and a deleted degree-`2` joint), triple cuts do not
increase it.  `hendAtL_of_inputs` is exactly the `hend` hypothesis of `chain_coverL`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

variable {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem fst_boundL {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)}
    {L γ η : ℝ} {w : Mom d} {A0 : Set (D₀ → (Fin d → ℤ))} {Rn : ℕ} {κ : D₀ → (Fin d → ℤ)}
    (hcn : CnBound M₀ C Un Fst L γ η w A0 Rn) (hκ : κ ∈ A0) {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
    {ps : List (Object M₀ × Quad D₀)} (hI : ConnDataL2 M₀ C Un Fst L γ η w κ h ps) (hg : ∃ R', Good R' h.s)
    (hF : ∀ p ∈ ps, p.1 ∈ Fst) : h.s.M.numComponents + 1 ≤ 2 * Rn := by
  obtain ⟨⟨hinj, hps, hpw, hrem, hpres⟩, he1, he2, he3, hfo⟩ := hI
  obtain ⟨E, hE, hdeg⟩ := state_rem_isoE hA hD ps hinj hpres he1 he3
  obtain ⟨h1, h2⟩ := hcn κ hκ ps (fun p hp => ⟨hps p hp, hF p hp⟩) hpw
  rw [hE] at h1 h2
  rcases Nat.lt_or_ge (h.s.M.numComponents + E) (2 * Rn) with hlt | hge
  · omega
  · have heq : h.s.M.numComponents + E = 2 * Rn := le_antisymm h1 hge
    obtain ⟨v, hv, hv0⟩ := h2 heq
    rcases hdeg v hv hv0 with hE1 | ⟨c, hc, hc0⟩
    · omega
    · obtain ⟨R', hg⟩ := hg
      have := good_deg_pos hg c hc
      omega

theorem deg3_of_good_post {b : HSt V D₀} (K : VineCut b.s.M) (R : ℝ) (kp : ℕ) {R' : ℕ}
    (hg : Good R' (b.vinePost K R kp).s) : 3 ≤ b.s.M.deg K.C.upper ∧ 3 ≤ b.s.M.deg K.C.lower := by
  have hfa : K.fa ∈ K.post.atoms := fa_mem_post K
  have hfb : K.fb ∈ K.post.atoms := fb_mem_post K
  have h1 : 1 ≤ K.post.deg K.fa := good_deg_pos hg K.fa hfa
  have h2 : 1 ≤ K.post.deg K.fb := good_deg_pos hg K.fb hfb
  have e1 : K.post.deg K.fa = K.cutMol.deg K.fa :=
    restrictP_deg K.cutMol (fun a => a ∉ K.C.atoms) K.closed (fun h => K.fa_fresh (objectAtoms_sub K.C h))
  have e2 : K.post.deg K.fb = K.cutMol.deg K.fb :=
    restrictP_deg K.cutMol (fun a => a ∉ K.C.atoms) K.closed (fun h => K.fb_fresh (objectAtoms_sub K.C h))
  have d1 := K.deg_fa
  have d2 := K.deg_fb
  omega

theorem endInvL_of_reach1L [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} (hS : SubHypL Rn M₀) {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))} {κ : D₀ → (Fin d → ℤ)}
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ U U' : Object M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hcn : CnBound M₀ C Un Fst L γ η w A0 Rn) (hHF : HostConnFL M₀ C Un Fst L γ η w A0) (hκ : κ ∈ A0)
    {h : HSt V D₀} (hr : Reach1L C Un Fst L γ η w κ h) :
    (∃ ps, ConnDataL2 M₀ C Un Fst L γ η w κ h ps ∧ h.s.M.numComponents + 1 ≤ 2 * Rn) ∨
      ((∀ U, Collected C (Un κ) L γ η w κ U → Dartless U h) ∧ h.s.M.numComponents + 1 ≤ 2 * Rn) := by
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
            have hD' : DartRel M₀ (b.vinePost K R kp).s := (invL_reach1 hS h0 hrh).choose_spec.2.rel
            have hg' := (invL_reach1 hS h0 hrh).choose_spec.2.good
            refine fst_boundL hcn hκ hA' hD' hI' ⟨_, hg'⟩ ?_
            intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            · exact hUF
            · by_contra hpF
              exact (hI.2.2.2.2 ⟨p, hp, hpF⟩ U hUF K.x₁) hUD.1
          · have h3 := deg3_of_good_post K R kp (invL_reach1 hS h0 hrh).choose_spec.2.good
            have := vine_F_le_of_hostConnFL hHF hκ hA hD hI K U hU hUK hUD hUJ hint hUF h3.1 h3.2
            have e : (b.vinePost K R kp).s.M.numComponents = K.post.numComponents := rfl
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
        have e : (b.vinePostG K).s.M.numComponents = (vineStG b.s K').M.numComponents := by rw [hK']; rfl
        omega
      · exact absurd (hUD.1) (hd U hU K.x₁)

/-- **`HendAt` for the LOW run** (the `hend` hypothesis of `chain_coverL`): `F(end of Step 1) ≤ 2R - 1`. -/
theorem hendAtL_of_inputs [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} (hS : SubHypL Rn M₀) {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))}
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Object M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hcn : CnBound M₀ C Un Fst L γ η w A0 Rn) (hHF : HostConnFL M₀ C Un Fst L γ η w A0) :
    ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1L M₀ Rn C Un Fst L γ η w A0 A h → A ≠ ∅ →
      (∀ k ∈ A, Stuck1 C L γ η w Un k h) → (h.s.M.numComponents : ℝ) ≤ 2 * (Rn : ℝ) - 1 := by
  intro A h hinv hAne _
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAne
  obtain ⟨hA0, hctx⟩ := hinv
  obtain ⟨hc, -, hr⟩ := hctx.resolve_left hAne
  have hκ0 : κ ∈ A0 := hA0 hκ
  have hend := endInvL_of_reach1L hS (h0 κ hκ0) (hdisj κ hκ0) hcn hHF hκ0 (hr κ hκ)
  have hF : h.s.M.numComponents + 1 ≤ 2 * Rn := by
    rcases hend with ⟨_, _, hF⟩ | ⟨_, hF⟩ <;> exact hF
  have : ((h.s.M.numComponents : ℕ) : ℝ) + 1 ≤ 2 * (Rn : ℝ) := by exact_mod_cast hF
  linarith

end WaveTurbulence.FinalCountAsm
