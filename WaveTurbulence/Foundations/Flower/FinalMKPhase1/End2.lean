/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.End

/-! # C1b1 MK-PHASE1 (11): `HendAtLE` (o75 Prop 4.7(3)): `F ≤ 2R - 1 + m` at the end of Step 1

`endE_of_reach1LE`: along `Reach1LE`, `F + 1 ≤ 2R + nDart` with `nDart` the number of dartless survivors (main's
`endInvL_of_reach1L2`, LowChain30, with one component per survivor removal). `hendAtLE_of_inputs : HendAtLE …` from the
fields of `LowLoopClassHypsMK` (`h0`, `disj`, `survDisjC`, `cnBound`, `hostConnFLE`) and `SubHypL`; `hendAtLE_inv1` is
the `hend` input of the chain cover (main's `hendAtL_of_inputs2` form). -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine

variable {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section endE
variable {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
  {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
  {A0 : Set (D₀ → (Fin d → ℤ))}

/-- The number of dartless (removed) survivors. -/
noncomputable def nDart (E : Fin m → Object M₀) (h : HSt V D₀) : ℕ :=
  (Finset.univ.filter fun i : Fin m => Dartless (E i) h).card

theorem nDart_le (E : Fin m → Object M₀) (h : HSt V D₀) : nDart E h ≤ m := by
  unfold nDart
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem nDart_mono (E : Fin m → Object M₀) {h h' : HSt V D₀} (hmono : ∀ k, Dartless (E k) h → Dartless (E k) h') :
    nDart E h ≤ nDart E h' := by
  unfold nDart
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, hmono k hk.2⟩

theorem nDart_succ (E : Fin m → Object M₀) {h h' : HSt V D₀} (hmono : ∀ k, Dartless (E k) h → Dartless (E k) h')
    (i : Fin m) (hi : ¬ Dartless (E i) h) (hi' : Dartless (E i) h') : nDart E h + 1 ≤ nDart E h' := by
  unfold nDart
  have hsub : (Finset.univ.filter fun k : Fin m => Dartless (E k) h) ⊆
      (Finset.univ.filter fun k : Fin m => Dartless (E k) h').erase i := by
    intro k hk
    rw [Finset.mem_filter] at hk
    refine Finset.mem_erase.2 ⟨fun e => hi (e ▸ hk.2), Finset.mem_filter.2 ⟨hk.1, hmono k hk.2⟩⟩
  have hmem : i ∈ (Finset.univ.filter fun k : Fin m => Dartless (E k) h') := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi'⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmem] at h1
  have h2 := Finset.card_pos.2 ⟨i, hmem⟩
  omega

/-- The number of components after `vinePostG` grows by at most one. -/
theorem vinePostG_F_le_succ {b : HSt V D₀} (K : VineCut b.s.M) :
    (b.vinePostG K).s.M.numComponents ≤ b.s.M.numComponents + 1 := by
  have hFc := numComponents_vineStG K
  have hsucc := vine_F_le_succ K
  have e : (b.vinePostG K).s.M.numComponents = (vineStG b.s K).M.numComponents := rfl
  omega

/-- **The end invariant along the survivor Step 1**: `F + 1 ≤ 2R + nDart`. -/
theorem endE_of_reach1LE [Infinite V] {Rn Rc : ℕ} (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ U U' : Object M₀, CollectedF C (Un κ) L γ η w κ U → CollectedF C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hsd : ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hcn : CnBoundF M₀ C Un Fst L γ η w A0 Rc) (hHF : HostConnFLE M₀ C Un Fst E L γ η w A0) (hκ : κ ∈ A0)
    {h : HSt V D₀} (hr : Reach1LE C Un Fst E L γ η w κ h) :
    h.s.M.numComponents + 1 ≤ 2 * Rc + nDart E h := by
  induction hr with
  | refl =>
    have hg := (invL_reach1E (C := C) (Un := Un) (Fst := Fst) (E := E) hS h0
      (show Reach1LE C Un Fst E L γ η w κ (HSt.init M₀) from Relation.ReflTransGen.refl)).choose_spec.2.good
    have := fst_boundE hcn hκ (AncRel.init M₀) (DartRel.init M₀) (bookE_init M₀ C Un Fst E L γ η w κ) ⟨_, hg⟩
      (by simp)
    omega
  | @tail b h' hrb hs ih =>
    have hrb' : Reach1LE C Un Fst E L γ η w κ b := hrb
    have hrh : Reach1LE C Un Fst E L γ η w κ h' := Reach1LE.ext hrb' hs
    have hA := reach1LE_ancRel hrb'
    have hD : DartRel M₀ b.s := (invL_reach1E hS h0 hrb').choose_spec.2.rel
    obtain ⟨ihc, ihb⟩ := reach1LE_book hS h0 hdisj hsd hrb'
    have hmono : ∀ U' : Object M₀, Dartless U' b → Dartless U' h' := fun U' hd => HStep1RLE.dartless hs hd
    have hnd := nDart_mono E (fun k hd => hmono (E k) hd)
    cases hs with
    | vine K R kp hs U hU hUK hUD hUJ hord =>
      have hint : UIntact U b := (ihc U hU).resolve_left (not_dartless_of_cd hUD.1)
      rcases ihb with ⟨ps, qs, B⟩ | ⟨hd, -⟩
      · by_cases hUF : U ∈ Fst
        · have hnd' : ¬ Dartless U b := not_dartless_of_cd hUD.1
          have hq : qs = [] := by
            by_contra hq
            exact hnd' (B.hfo (Or.inr hq) U hUF)
          subst hq
          have hpF : ∀ p ∈ ps, p.1 ∈ Fst := fun p hp => by
            by_contra hpF
            exact hnd' (B.hfo (Or.inl ⟨p, hp, hpF⟩) U hUF)
          have B' := B.coll hA K U hU hUD hUJ hord hint
            (fun hG => hG.vine hA K R kp U (remA_of_intact hA K U hUK hint hUD hUJ)) hmono
          have hA' := reach1LE_ancRel hrh
          have hI' := (invL_reach1E hS h0 hrh).choose_spec.2
          have := fst_boundE hcn hκ hA' hI'.rel B' ⟨_, hI'.good⟩ (fun p hp => by
            rcases List.mem_cons.1 hp with rfl | hp
            · exact hUF
            · exact hpF p hp)
          omega
        · have h3 := deg3_of_good_post K R kp (invL_reach1E hS h0 hrh).choose_spec.2.good
          have := vine_F_le_of_hostConnFLE hHF hκ hA hD B K U hU hUK hUD hUJ hint hUF h3.1 h3.2
          have e : (b.vinePost K R kp).s.M.numComponents = K.post.numComponents := rfl
          omega
      · exact absurd hUD.1 (hd U hU K.x₁)
    | d1 K hs U hU hUK hUD hUJ hord =>
      obtain ⟨K', -, -, hd2, -, -, hK'⟩ := hs.data
      have hj := jdeg2_pos K' hd2
      have hFc := numComponents_vineStG K'
      have hsucc := vine_F_le_succ K'
      have e : (b.vinePostG K).s.M.numComponents = (vineStG b.s K').M.numComponents := by rw [hK']; rfl
      omega
    | triple _ hs hs3 hall hallE hF => omega
    | survVine K R kp i hs hc ho =>
      rcases ihb with ⟨ps, qs, B⟩ | ⟨-, hd⟩
      · have hn := nDart_succ E (fun k hd => hmono (E k) hd) i (not_dartless_of_cd hc.2.1.1)
          (dartless_vinePostA hA hD B.geom.inj K R kp (remA_of_survCut hc))
        have hsucc := vine_F_le_succ K
        have e : (b.vinePost K R kp).s.M.numComponents = K.post.numComponents := rfl
        omega
      · exact absurd hc.2.1.1 (hd i K.x₁)
    | survD1 K i hs hc ho =>
      rcases ihb with ⟨ps, qs, B⟩ | ⟨-, hd⟩
      · have hn := nDart_succ E (fun k hd => hmono (E k) hd) i (not_dartless_of_cd hc.2.1.1)
          (dartless_vinePostGA hA hD B.geom.inj K (remA_of_survCut hc))
        have := vinePostG_F_le_succ K
        omega
      · exact absurd hc.2.1.1 (hd i K.x₁)
    | survRC K i hs hc ho =>
      rcases ihb with ⟨ps, qs, B⟩ | ⟨-, hd⟩
      · have hn := nDart_succ E (fun k hd => hmono (E k) hd) i (not_dartless_of_cd hc.2.1.1)
          (dartless_vinePostGA hA hD B.geom.inj K (remA_of_survCut hc))
        have := vinePostG_F_le_succ K
        omega
      · exact absurd hc.2.1.1 (hd i K.x₁)

/-- **C1b1 target: `HendAtLE`** (o75 Prop 4.7(3)): at the end of the survivor Step 1 the state has at most
`2R - 1 + m` components (in fact at every reachable state), from the fields of `LowLoopClassHypsMK`. -/
theorem hendAtLE_of_inputs [Infinite V] {Rn Rc : ℕ} (hS : SubHypL Rn M₀)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Object M₀, CollectedF C (Un κ) L γ η w κ U → CollectedF C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hsd : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hcn : CnBoundF M₀ C Un Fst L γ η w A0 Rc) (hHF : HostConnFLE M₀ C Un Fst E L γ η w A0) :
    HendAtLE M₀ C Un Fst E L γ η w A0 Rc := by
  intro κ hκ h hr _
  have h1 := endE_of_reach1LE hS (h0 κ hκ) (hdisj κ hκ) (hsd κ hκ) hcn hHF hκ hr
  have h2 := nDart_le E h
  have : ((h.s.M.numComponents : ℕ) : ℝ) + 1 ≤ 2 * (Rc : ℝ) + m := by exact_mod_cast (by omega)
  linarith

/-- **The `hend` input of the chain cover** (main's `hendAtL_of_inputs2` form, `Fmax = 2R - 1 + m`). -/
theorem hendAtLE_inv1 [Infinite V] {Rn Rc : ℕ} (hS : SubHypL Rn M₀)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Object M₀, CollectedF C (Un κ) L γ η w κ U → CollectedF C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hsd : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hcn : CnBoundF M₀ C Un Fst L γ η w A0 Rc) (hHF : HostConnFLE M₀ C Un Fst E L γ η w A0) :
    ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h → A ≠ ∅ →
      (∀ k ∈ A, Stuck1E C L γ η w Un E k h) → (h.s.M.numComponents : ℝ) ≤ 2 * (Rc : ℝ) - 1 + m := by
  intro A h hinv hAne hst
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAne
  obtain ⟨hA0, hctx⟩ := hinv
  obtain ⟨-, -, hr⟩ := hctx.resolve_left hAne
  exact hendAtLE_of_inputs hS h0 hdisj hsd hcn hHF κ (hA0 hκ) h (hr κ hκ) (hst κ hκ)

end endE

end WaveTurbulence.Flower.FinalMKPhase1
