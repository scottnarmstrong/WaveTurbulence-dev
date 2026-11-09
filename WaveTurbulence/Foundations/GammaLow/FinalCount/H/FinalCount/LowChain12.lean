/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain11
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain12`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, LC-2 (8): phase-1 node facts for the old (REG) steps in the LOW run**: `Inv1L`, `node1_factsL` (vine nodes),
`nodeT_factsL` (triple nodes). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

abbrev Inv1L (M₀ : Molecule V D₀) (Rn : ℕ) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀))
    (Fst : Set (Src.Object Src.γL M₀)) (L γ η : ℝ) (w : Mom d) (A0 A : Set (D₀ → (Fin d → ℤ)))
    (h : HSt V D₀) : Prop :=
  Inv3L M₀ Rn (fun κ h => Reach1L C Un Fst L γ η w κ h) L w A0 A h

theorem Inv1L.mono {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d} {A0 A B : Set (D₀ → (Fin d → ℤ))}
    {h : HSt V D₀} (hA : Inv1L M₀ Rn C Un Fst L γ η w A0 A h) (hB : B ⊆ A) : Inv1L M₀ Rn C Un Fst L γ η w A0 B h :=
  Inv3L.mono hA hB

/-- **Per-node facts of phase 1 (vine nodes).** -/
theorem node1_factsL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {crit : V → Prop} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))} {CA CN ν : ℝ} (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hExA : Ex1A L γ η δ C₁ w M₀ P CA) (hExN : Ex1N L γ η δ C₁ w M₀ P CN ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {h : HSt V D₀} (hA : Inv1L M₀ Rn C Un Fst L γ η w A0 A h) {t : T1 h} (hn : Node1 C crit L γ η h t)
    (hext : ∀ k ∈ cls1 L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2,
      Reach1L C Un Fst L γ η w k h → Reach1L C Un Fst L γ η w k (post1 C crit L γ η h t)) :
    Inv1L M₀ Rn C Un Fst L γ η w A0 (cls1 L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2)
      (post1 C crit L γ η h t) ∧
    epsCount (post1 C crit L γ η h t).s < epsCount h.s ∧
    QS L γ δ C₁ w P h (cls1 L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) ≤
      ENNReal.ofReal (vCost L γ η CA CN h (post1 C crit L γ η h t)) *
        QS L γ δ C₁ w P (post1 C crit L γ η h t)
          (cls1 L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) := by
  set B := cls1 L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2 with hB
  have hsub : B ⊆ A := fun k hk => hk.1
  obtain ⟨K, F, hK⟩ := node1_spec hn
  have hRpos : (0 : ℝ) < (2 : ℝ) ^ t.2.2.2.2.1 := zpow_pos (by norm_num) _
  set R : ℝ := (2 : ℝ) ^ t.2.2.2.2.1 with hRdef
  set kp : ℕ := (if t.2.2.2.2.2.1 then 50 else 0) with hkpdef
  set c := alphaOrBeta K.post.numComponents h.s.M.numComponents R kp with hcdef
  have hcne : c ≠ .eps := by
    rw [hcdef]; unfold alphaOrBeta; split_ifs <;> simp
  have hcpos : ∀ R' kp', c = .alpha R' kp' → 0 < R' := by
    intro R' kp' hc
    rw [hcdef] at hc; unfold alphaOrBeta at hc
    split_ifs at hc
    · cases hc; exact hRpos
  have hlt : epsCount (post1 C crit L γ η h t).s < epsCount h.s := by
    rw [hK, vinePost_s]; exact epsCount_vineSt_lt K F.hu c hcne
  by_cases hAe : B = ∅
  · refine ⟨⟨hsub.trans hA.1, Or.inl hAe⟩, hlt, ?_⟩
    rw [hAe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨⟨R', hR', hc⟩, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hAe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hcc := uctx_mono hc (fun k (hk : k ∈ B) => hsub hk)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ B) => hA.1 (hsub hk))
  have hst := uStep1_node (w := w) (A := A) hn
  have hc' : UCtx M₀ R' (fun k => k ∈ B) L w (post1 C crit L γ η h t) := UCtx.step1L hκ hst hpp hcc
  have hap' : ApPos (post1 C crit L γ η h t).s := by
    rw [hK, vinePost_s]; exact apPos_vineSt hap K c hcpos
  have hr' : ∀ k ∈ B, Reach1L C Un Fst L γ η w k (post1 C crit L γ η h t) :=
    fun k hk => hext k hk (hr k (hsub hk))
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨⟨R', hR', hc'⟩, hap', hr'⟩⟩, hlt, ?_⟩
  have hI : Inv R' h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hCB : CompBeta h.s := by
    obtain ⟨R'', -, hIL⟩ := invL_reach1 hS (h0 κ (hA.1 (hsub hκ))) (hr κ (hsub hκ))
    exact hIL.comp
  have hMol : h.s.M.IsMolecule := isMolecule_of_compBeta hc.good hCB
  have hrem := vine_atoms_eps hI K F.hu F.hl
  have hAp := apProd_pos (L := L) (γ := γ) (η := η) (lt_of_lt_of_le (Real.exp_pos 1) H.hL) hap
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  rw [hK] at hst
  have hne : ∃ k0, (fun k => k ∈ B) k0 := ⟨κ, hκ⟩
  have hSrc' : ∀ k0, (fun k => k ∈ B) k0 → SourceLadderGaps M₀ L w P k0 := fun k hk => hSrc k (hA.1 (hsub hk))
  have hdec' := fun k (hk : (fun k => k ∈ B) k) => hdec k (hA.1 (hsub hk))
  unfold vCost
  rw [hK, vinePost_s]
  show QS L γ δ C₁ w P h B ≤ _
  have hnum : (vineSt h.s K c).M.numComponents = K.post.numComponents := rfl
  by_cases hF : K.post.numComponents ≤ h.s.M.numComponents
  · obtain ⟨K', R', kp', he, hdev0⟩ := hExA (fun k => k ∈ B) hne hSrc' hdec' hst hLC hcc.atom hMol
    have hdev := hdev0 (F.hcls _ _ K' R' kp' he)
    have hcc' := vinePost_cls_eq he
    have hF' := vinePost_F_eq he
    have hc1 : c = Cls.alpha R kp := by rw [hcdef]; unfold alphaOrBeta; rw [if_pos hF]
    have hc2 : alphaOrBeta K'.post.numComponents h.s.M.numComponents R' kp' = Cls.alpha R' kp' := by
      unfold alphaOrBeta; rw [if_pos (hF' ▸ hF)]
    rw [← hcdef, hc1, hc2] at hcc'
    obtain ⟨hR1, hkp1⟩ := Cls.alpha.inj hcc'
    subst hR1 hkp1
    have hd := hdev (hF' ▸ hF)
    have hX := stepRHS_vine_alpha (L := L) (γ := γ) (η := η) hL hap K (R := R) (kp := kp) hrem hF
    rw [if_pos (by rw [hnum]; exact hF)]
    rw [← hX] at hd
    exact hd
  · have hF1 : K.post.numComponents = h.s.M.numComponents + 1 := le_antisymm (vine_F_le_succ K) (by omega)
    have hνat : (h.s.M.atoms.card : ℝ) ≤ ν := by
      have := card_atoms_leL_of_uctx hS hR' hcc
      exact le_trans (by exact_mod_cast this) hν
    obtain ⟨K', R', kp', he, hdev0⟩ := hExN (fun k => k ∈ B) hne hSrc' hdec' hst hLC hcc.atom hMol F.hnl hνat
    have hdev := hdev0 (F.hcls _ _ K' R' kp' he) (fun hd => F.hconn _ _ K' R' kp' he hd)
    have hF' := vinePost_F_eq he
    have hd := hdev (hF' ▸ hF1)
    have hX := stepRHS_vine_new (L := L) (γ := γ) (η := η) hL hap K (R := R) (kp := kp) hrem hF1
    rw [if_neg (by rw [hnum]; exact hF)]
    rw [excessRHS2_vine hL, ← hX, ← mul_assoc] at hd
    exact hd


/-- **Per-node facts of phase 1 (triple nodes)**: from `node3_facts`, with the reach relation of `HStep1C`. -/
theorem nodeT_factsL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    {A0 A : Set (D₀ → (Fin d → ℤ))} (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c) {h : HSt V D₀} (hA : Inv1L M₀ Rn C Un Fst L γ η w A0 A h)
    (hall : ∀ k ∈ A, ∀ U, Collected C (Un k) L γ η w k U → Dartless U h) {t : T3 h}
    (hn : NodeT C L γ η h t) :
    Inv1L M₀ Rn C Un Fst L γ η w A0 (cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2)
      (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) ∧
    epsCount (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1).s < epsCount h.s ∧
    QS L γ δ C₁ w P h (cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) ≤
      ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)) *
        QS L γ δ C₁ w P (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)
          (cls3 L γ η w h A t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) := by
  exact node3_factsL H hS hp0 hP hP0 c hnc hA hn.1
    (fun k hk hr => hr.ext (by
      have hb := hstep1C_triple_both hn.1 hn.2 hk
      exact HStep1RL.old (HStep1R.triple h _ hb.1 hb.2 (hall k hk.1) (post3_F_le hn.1 hn.2))))

end WaveTurbulence.GammaLow.FinalCount.H
