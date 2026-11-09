/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.LowD
/-! **Ghost assembly for L8-H2 (B): the Phase-1 nodes with the bank for any reach with the LOW facts** (wt-l6ghost;
design: `GammaLow/FinalCount/Ghost/CHAIN-DESIGN.md`).

`node1_bankG`, `nodeT_bankG`: wt-l6ghost's `node1_bankL`, `nodeT_bankL` (`Ghost/LowD`) with the invariant `Inv3L` for any
reach `Rch` (the facts `InvL` via `hIL`), the node class `cls1 … A' …` / `cls3 … A' …` for any `A' ⊆ A` (L8-H2's
`AvineE`, `AtripE`), and the node facts (H's `node1_factsL` / `nodeT_factsL` on the sub-class) as the hypothesis
`hfacts`. `nodeGL_bank`: a Step D1 or re-cut node (post state `h.vinePostGL K`) keeps the bank. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.Flower.H2.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount
open WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.FinalCount.Ghost

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section vine
variable [Infinite V] {M₀ : Molecule V D₀} {C : H.CollData M₀} {crit : V → Prop} {L γ η : ℝ} {h : HSt V D₀}
  {t : T1 h}

/-- The split class `σ` of a vine node with the node class `cls1 … A' …`. -/
noncomputable def vineSplitG (w : Mom d) (A' : Set (D₀ → (Fin d → ℤ))) (hn : H.Node1 C crit L γ η h t) (σ : Sig1) :
    Set (D₀ → (Fin d → ℤ)) :=
  split1 L γ η w h (h.vinePostL (vcut hn) (vR t) (vkp t)) (vineSurv h (vcut hn) (vR t) (vkp t))
    ![(vcut hn).fa, (vcut hn).fb] (fun k0 => pgap L w k0 (h.s.pr t.1 t.2.1))
    (cls1 L γ η w h A' t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) σ

theorem node1_bankG {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop}
    {δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ} {A0 A A' : Set (D₀ → (Fin d → ℤ))} {CA CN : ℝ}
    (HR : TriReal d L γ η δ C₁) (hExC : Ex1Cone L γ η δ C₁ w M₀ P CA)
    (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (hIL : ∀ κ ∈ A0, ∀ h', Rch κ h' → ∃ R'', R'' ≤ Rn ∧ InvL M₀ R'' L γ η w κ h')
    (hA : Inv3L M₀ Rn Rch L w A0 A h) (hA'A : A' ⊆ A) (hn : H.Node1 C crit L γ η h t)
    (hfacts : ∀ B, B ⊆ cls1 L γ η w h A' t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
        t.2.2.2.2.2.2.2 → Inv3L M₀ Rn Rch L w A0 B (H.post1 C crit L γ η h t) ∧
      epsCount (H.post1 C crit L γ η h t).s < epsCount h.s ∧
      QS L γ δ C₁ w P h B ≤ ENNReal.ofReal (vCost L γ η CA CN h (H.post1 C crit L γ η h t)) *
        QS L γ δ C₁ w P (H.post1 C crit L γ η h t) B) {b : ℕ}
    (hbank : bank L γ η w h A ≤ b) (σ : Sig1) :
    Inv3L M₀ Rn Rch L w A0 (vineSplitG w A' hn σ) (H.post1 C crit L γ η h t) ∧
    epsCount (H.post1 C crit L γ η h t).s < epsCount h.s ∧
    bank L γ η w (H.post1 C crit L γ η h t) (vineSplitG w A' hn σ) ≤ b + k1Of σ ∧
    QS L γ δ C₁ w P h (vineSplitG w A' hn σ) ≤
      ENNReal.ofReal (3 * 5 ^ d * vCost L γ η CA CN h (H.post1 C crit L γ η h t) *
        L ^ (-5 * η * ((k1Of σ : ℕ) : ℝ))) * QS L γ δ C₁ w P (H.post1 C crit L γ η h t) (vineSplitG w A' hn σ) := by
  obtain ⟨hx1, hx2, hy1, hy2, hF⟩ := vcut_spec hn
  set K := vcut hn with hKdef
  set R := vR t with hRdef
  set kp := vkp t with hkpdef
  set B0 := cls1 L γ η w h A' t.1 t.2.1 t.2.2.1 t.2.2.2.1
      t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2 with hB0
  set B := vineSplitG w A' hn σ with hBdef
  set n : Fin 2 → V := ![K.fa, K.fb] with hndef
  set g : (D₀ → (Fin d → ℤ)) → Mom d := fun k0 => pgap L w k0 (h.s.pr t.1 t.2.1) with hgdef
  have hpost : H.post1 C crit L γ η h t = h.vinePostL K R kp := post1_eq hn
  have hBB0 : B ⊆ B0 := fun k hk => hk.1
  have hBA : B ⊆ A := fun k hk => hA'A (hBB0 hk).1
  have hself : cls1 L γ η w h B t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
      t.2.2.2.2.2.2.2 = B := by
    ext k; exact ⟨fun hk => hk.1, fun hk => ⟨hk, (hBB0 hk).2⟩⟩
  obtain ⟨hinv, hlt, hdevTR⟩ := hfacts B hBB0
  refine ⟨hinv, hlt, ?_⟩
  by_cases hBe : B = ∅
  · refine ⟨?_, ?_⟩
    · rw [hBe, bank_empty]; omega
    · rw [hBe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨⟨R', hR', hc⟩, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hBA)) hBe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hBe
  have hI : Inv R' h.s := hc.good.1
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) HR.hL
  obtain ⟨_, -, hIE⟩ := hIL κ (hA.1 (hBA hκ)) h (hr κ (hBA hκ))
  have hBal : BalS h.s := hIE.bal
  have hCB : CompBeta h.s := hIE.comp
  have hRI : ∀ k0 ∈ B, HInv L γ η w k0 h ∧ HGap L w k0 h := fun k0 hk0 => by
    obtain ⟨_, -, this⟩ := hIL k0 (hA.1 (hBA hk0)) h (hr k0 (hBA hk0))
    exact ⟨this.hrec, this.gap⟩
  have hmate : ∀ k0 ∈ B, ∀ x, k0 (h.s.down (h.s.M.mate x)) = k0 (h.s.down x) := by
    intro k0 hk0 x
    obtain ⟨c0, hd0, -⟩ := hdec k0 (hA.1 (hBA hk0))
    rw [← hc.rel.mate x]
    exact hd0.1 (h.s.down x)
  have hsurv := vineSurvMap h K R kp
  have hgx : ∀ k0, pgap L w k0 (h.s.pr K.x₁ K.x₂) = g k0 := fun k0 => by rw [hx1, hx2]
  have hgv : ∀ k0 ∈ B, ∀ j, IsCritA L γ η (h.vinePostL K R kp) (n j) →
      gvec (h.vinePostL K R kp) L w k0 (n j) = g k0 ∨ gvec (h.vinePostL K R kp) L w k0 (n j) = -g k0 := by
    intro k0 hk0 j _
    fin_cases j
    · left
      show gvec (h.vinePostL K R kp) L w k0 K.fa = g k0
      rw [gvec_vine_fa, hgx]
    · show gvec (h.vinePostL K R kp) L w k0 K.fb = g k0 ∨ gvec (h.vinePostL K R kp) L w k0 K.fb = -g k0
      rw [gvec_vine_fb, hy1, hy2]
      exact (hBB0 hk0).2.2.2.2.1
  have hnew : ∀ x, IsCritA L γ η (h.vinePostL K R kp) x → x ∉ vineSurv h K R kp → ∃ j, x = n j := by
    intro x hx hX
    rcases vine_critA_cases h K R kp hx hX with e | e
    · exact ⟨0, e⟩
    · exact ⟨1, e⟩
  have hpair : NCEdge L γ η w (h.vinePostL K R kp) B (n 0) (n 1) → n 0 ∈ cov1Of n σ ∨ n 1 ∈ cov1Of n σ := by
    intro hE
    by_cases hs0 : sOf σ 0 = 0
    · by_cases hs1 : sOf σ 1 = 0
      · exfalso
        obtain ⟨-, hc0, hc1, hadj, -, hLk, -⟩ := hE
        exact hLk (vine_twin_locked h K R kp hI hF.hu hF.hl (fun k0 hk0 => (hRI k0 hk0).2.chg) hmate
          hc0.2.1 hc1.2.1 hadj)
      · exact Or.inr (mem_cov1Of n hs1)
    · exact Or.inl (mem_cov1Of n hs0)
  have hbk : bank L γ η w (h.vinePostL K R kp) B ≤ bank L γ η w h A + (cov1Of n σ).card := by
    refine bank_step hsurv hBA (critSet L γ η h) (cov1Of n σ) ?_ ?_
    · intro x y hE hx hy
      exact Or.inl ⟨mem_critSet.2 (hsurv.critA hx hE.2.1), mem_critSet.2 (hsurv.critA hy hE.2.2.1)⟩
    · exact edge_cover1 n g hsurv (B0 := B0) subset_rfl hnew hgv hpair
  have hcov := card_cov1Of_le n σ
  rw [hpost]
  refine ⟨by omega, ?_⟩
  rw [hpost] at hdevTR
  by_cases hz : ∀ j, sOf σ j = 0
  · -- the TR class
    rw [k1Of_eq_zero hz]
    refine hdevTR.trans (mul_le_mul' (ofReal_le_mul_rpow_zero ?_) le_rfl)
    have : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
    linarith
  · -- a cone class: `Ex1Cone` with `k = 2`
    push Not at hz
    obtain ⟨j, hsj⟩ := hz
    rw [k1Of_eq_two ⟨j, hsj⟩]
    obtain ⟨hcj, y, hyX, hyc, hcone⟩ := stat1_cone n g hsurv (B0 := B0) subset_rfl ⟨κ, hκ⟩ j hsj
    -- the class of the twins: `α R 0`, critical, `ΔF = 0`
    have hclsn : (h.vinePostL K R kp).s.cls (n j) =
        alphaOrBeta K.post.numComponents h.s.M.numComponents R kp := by
      rw [H.vinePost_s]
      fin_cases j
      · exact H.vineSt_cls_fa_AsmP1Basic h.s K _
      · exact H.vineSt_cls_fb_AsmP1Basic h.s K _
    obtain ⟨R₀, hR₀, hcrit⟩ := hcj.2.2
    rw [hclsn] at hR₀
    obtain ⟨hFle, hRR, hkp0⟩ := alphaOrBeta_eq_alpha hR₀
    have hcc := uctx_mono hc (fun k (hk : k ∈ B) => hBA hk)
    have hst : H.UStep1 L γ η w (fun k => k ∈ B) h (h.vinePostL K R kp) := by
      have := H.uStep1_node (L := L) (γ := γ) (η := η) (w := w) (A := B) hn
      rw [hself, hpost] at this
      exact this
    have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
    have hMol : h.s.M.IsMolecule := isMolecule_of_compBeta hc.good hCB
    obtain ⟨K', R', kp', he, hdev0⟩ := hExC (fun k => k ∈ B) ⟨κ, hκ⟩
      (fun k hk => hSrc k (hA.1 (hBA hk))) (fun k hk => hdec k (hA.1 (hBA hk))) hst hLC hcc.atom hMol
    have hcls' := H.vinePost_cls_eq he
    rw [hR₀] at hcls'
    obtain ⟨hFle', hRR', hkp0'⟩ := alphaOrBeta_eq_alpha hcls'.symm
    have hhist : (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist) =
        (h.s.pr K'.y₁ K'.y₂ :: h.s.pr K'.x₁ K'.x₂ :: h.hist) := congrArg HSt.hist he
    have hpx : h.s.pr K'.x₁ K'.x₂ = h.s.pr t.1 t.2.1 := by
      rw [← hx1, ← hx2]; exact ((List.cons.inj (List.cons.inj hhist).2).1).symm
    have hJC : JointCone K' L γ δ η w (AdmS (fun k => k ∈ B) h.s) :=
      jointCone_of_crit (by have := HR.hd; omega) hBal hRI hyc K' (h.s.pr t.1 t.2.1) hpx hcone
    have hcrit' : Crit L γ η R' := by rw [hRR']; exact hcrit
    have hdev := hdev0 (hF.hcls R kp K' R' kp' he) hFle' hkp0' hcrit' hJC 2 le_rfl
    have hrem := H.vine_atoms_eps hI K hF.hu hF.hl
    have hX := H.stepRHS_vine_alpha (L := L) (γ := γ) (η := η) hL hap K (R := R) (kp := kp) hrem hFle
    have hvc : vCost L γ η CA CN h (h.vinePostL K R kp) = CA * stepRHS L γ η h (h.vinePostL K R kp) := by
      unfold vCost; rw [ite_eq_left (by rw [H.vinePost_numComponents]; exact hFle)]
    refine hdev.trans (mul_le_mul' (le_of_eq (congrArg ENNReal.ofReal ?_)) le_rfl)
    rw [hvc, hX, hkp0, hRR', hRR]
    ring

end vine

section trip
variable [Infinite V] {M₀ : Molecule V D₀} {C : H.CollData M₀} {L γ η : ℝ} {h : HSt V D₀} {t : T3 h}

/-- The split class `σ` of a triple node with the node class `cls3 … A' …`. -/
noncomputable def tripSplitG (w : Mom d) (A' : Set (D₀ → (Fin d → ℤ))) (t : T3 h) (σ : Sig1) :
    Set (D₀ → (Fin d → ℤ)) :=
  split1 L γ η w h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)
    (cutSurv h t.1 (fresh h) t.2.1 t.2.2.1 ((2 : ℝ) ^ t.2.2.2.1) (if t.2.2.2.2.1 then 50 else 0))
    ![t.1, fresh h] (fun k0 => pgap L w k0 (h.s.pr t.2.1 t.2.2.1))
    (cls3 L γ η w h A' t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) σ

theorem nodeT_bankG {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop}
    {δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ} {A0 A A' : Set (D₀ → (Fin d → ℤ))}
    (HR : TriReal d L γ η δ C₁) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hIL : ∀ κ ∈ A0, ∀ h', Rch κ h' → ∃ R'', R'' ≤ Rn ∧ InvL M₀ R'' L γ η w κ h')
    (hA : Inv3L M₀ Rn Rch L w A0 A h) (hA'A : A' ⊆ A) (hn : H.NodeT C L γ η h t)
    (hfacts : ∀ B, B ⊆ cls3 L γ η w h A' t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2 →
      Inv3L M₀ Rn Rch L w A0 B (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) ∧
      epsCount (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1).s < epsCount h.s ∧
      QS L γ δ C₁ w P h B ≤ ENNReal.ofReal (max (cAlpha d γ η) (cBeta η c) *
        stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)) *
        QS L γ δ C₁ w P (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) B) {b : ℕ}
    (hbank : bank L γ η w h A ≤ b) (σ : Sig1) :
    Inv3L M₀ Rn Rch L w A0 (tripSplitG (L := L) (γ := γ) (η := η) w A' t σ) (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) ∧
    epsCount (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1).s < epsCount h.s ∧
    bank L γ η w (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) (tripSplitG (L := L) (γ := γ) (η := η) w A' t σ) ≤ b + k1Of σ ∧
    QS L γ δ C₁ w P h (tripSplitG (L := L) (γ := γ) (η := η) w A' t σ) ≤
      ENNReal.ofReal (3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) *
        stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) * L ^ (-5 * η * ((k1Of σ : ℕ) : ℝ))) *
        QS L γ δ C₁ w P (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) (tripSplitG (L := L) (γ := γ) (η := η) w A' t σ) := by
  set v := t.1 with hvdef
  set x₁ := t.2.1 with hx1def
  set x₂ := t.2.2.1 with hx2def
  set z := t.2.2.2.1 with hzdef
  set bb := t.2.2.2.2.1 with hbbdef
  set a := t.2.2.2.2.2.1 with hadef
  set sg := t.2.2.2.2.2.2 with hsgdef
  set R : ℝ := (2 : ℝ) ^ z with hRdef
  set kp : ℕ := if bb then 50 else 0 with hkpdef
  set v₂ := fresh h with hv₂def
  set h' := post3 h v x₁ x₂ z bb with hh'
  set B0 := cls3 L γ η w h A' x₁ x₂ z bb a sg with hB0
  set B := tripSplitG (L := L) (γ := γ) (η := η) w A' t σ with hBdef
  set n : Fin 2 → V := ![v, v₂] with hndef
  set g : (D₀ → (Fin d → ℤ)) → Mom d := fun k0 => pgap L w k0 (h.s.pr x₁ x₂) with hgdef
  have hpost : h' = h.cut3Post v v₂ x₁ x₂ R kp := rfl
  obtain ⟨hcd, hε, h3, hR, ha, hb⟩ := hn.1
  have hBB0 : B ⊆ B0 := fun k hk => hk.1
  have hBA : B ⊆ A := fun k hk => hA'A (hBB0 hk).1
  have hself : cls3 L γ η w h B x₁ x₂ z bb a sg = B := by
    ext k; exact ⟨fun hk => hk.1, fun hk => ⟨hk, (hBB0 hk).2⟩⟩
  obtain ⟨hinv, hlt, hdevTR⟩ := hfacts B hBB0
  refine ⟨hinv, hlt, ?_⟩
  by_cases hBe : B = ∅
  · refine ⟨?_, ?_⟩
    · rw [hBe, bank_empty]; omega
    · rw [hBe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨⟨R', hR', hc⟩, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hBA)) hBe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hBe
  have hI : Inv R' h.s := hc.good.1
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) HR.hL
  obtain ⟨_, -, hIE⟩ := hIL κ (hA.1 (hBA hκ)) h (hr κ (hBA hκ))
  have hBal : BalS h.s := hIE.bal
  have hRI : ∀ k0 ∈ B, HInv L γ η w k0 h ∧ HGap L w k0 h := fun k0 hk0 => by
    obtain ⟨_, -, this⟩ := hIL k0 (hA.1 (hBA hk0)) h (hr k0 (hBA hk0))
    exact ⟨this.hrec, this.gap⟩
  have hv₂ : v₂ ∉ h.s.M.atoms := hcd.2.1
  have hvv : v ≠ v₂ := fun e => hv₂ (e ▸ hcd.1)
  have hsurv := cutSurvMap h v v₂ x₁ x₂ R kp hv₂
  have hgv : ∀ k0 ∈ B, ∀ j, IsCritA L γ η h' (n j) →
      gvec h' L w k0 (n j) = g k0 ∨ gvec h' L w k0 (n j) = -g k0 := by
    intro k0 _ j _
    left
    fin_cases j
    · exact gvec_cut_v h v v₂ x₁ x₂ R kp hvv L w k0
    · exact gvec_cut_v₂ h v v₂ x₁ x₂ R kp L w k0
  have hnew : ∀ x, IsCritA L γ η h' x → x ∉ cutSurv h v v₂ x₁ x₂ R kp → ∃ j, x = n j := by
    intro x hx hX
    rcases cut_critA_cases h v v₂ x₁ x₂ R kp hx hX with e | e
    · exact ⟨0, e⟩
    · exact ⟨1, e⟩
  have hpair : NCEdge L γ η w h' B (n 0) (n 1) → n 0 ∈ cov1Of n σ ∨ n 1 ∈ cov1Of n σ := by
    intro hE
    exact absurd hE.2.2.2.1 (trip_not_adj hn)
  have hbk : bank L γ η w h' B ≤ bank L γ η w h A + (cov1Of n σ).card := by
    refine bank_step hsurv hBA (critSet L γ η h) (cov1Of n σ) ?_ ?_
    · intro x y hE hx hy
      exact Or.inl ⟨mem_critSet.2 (hsurv.critA hx hE.2.1), mem_critSet.2 (hsurv.critA hy hE.2.2.1)⟩
    · exact edge_cover1 n g hsurv (B0 := B0) subset_rfl hnew hgv hpair
  have hcov := card_cov1Of_le n σ
  refine ⟨by omega, ?_⟩
  have hX0 : 0 ≤ stepRHS L γ η h h' := by
    have hc'' := (hinv.2.resolve_left hBe)
    unfold stepRHS
    have h1 := apProd_pos (L := L) (γ := γ) (η := η) hL hap
    have h2 := apProd_pos (L := L) (γ := γ) (η := η) hL hc''.2.1
    positivity
  by_cases hz : ∀ j, sOf σ j = 0
  · -- the TR class
    rw [k1Of_eq_zero hz]
    refine hdevTR.trans (mul_le_mul' ?_ le_rfl)
    have : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
    have h1 := ofReal_le_mul_rpow_zero (L := L) (η := η) (a := 3 * 5 ^ d)
      (X := max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') (by linarith)
    refine h1.trans (le_of_eq (congrArg ENNReal.ofReal ?_))
    ring
  · -- a cone class: `cut_excess_cone` with `k = 2`
    push Not at hz
    obtain ⟨j, hsj⟩ := hz
    rw [k1Of_eq_two ⟨j, hsj⟩]
    obtain ⟨hcj, y, hyX, hyc, hcone⟩ := stat1_cone n g hsurv (B0 := B0) subset_rfl ⟨κ, hκ⟩ j hsj
    have hclsn : (h.cut3Post v v₂ x₁ x₂ R kp).s.cls (n j) = if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta := by
      fin_cases j
      · show Function.update (Function.update h.s.cls v _) v₂ _ v = _
        rw [Function.update_of_ne hvv, Function.update_self]
      · show Function.update (Function.update h.s.cls v _) v₂ _ v₂ = _
        rw [Function.update_self]
    obtain ⟨R₀, hR₀, hcrit⟩ := hcj.2.2
    rw [hclsn] at hR₀
    have hα : h.s.M.IsAlphaCut v v₂ x₁ x₂ := by
      by_contra hn'
      rw [ite_eq_right hn'] at hR₀
      cases hR₀
    rw [ite_eq_left hα] at hR₀
    obtain ⟨hRR, hkp0⟩ := Cls.alpha.inj hR₀
    have hc' := hinv.2.resolve_left hBe
    have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
    have hLC' : LCtx M₀ (h.s.cutSt v v₂ x₁ x₂ (.alpha R kp) (.alpha R kp)) :=
      LCtx.cutSt hLC hcd (.alpha R kp) (.alpha R kp) (fun e => by cases e) (fun e => by cases e)
    have hPinh := LCtx.hPinh (s := h.s) (s' := h.s.cutSt v v₂ x₁ x₂ (.alpha R kp) (.alpha R kp)) hP hLC hLC'
    have hcone' : CutCone h.s.M x₁ x₂ L γ δ (L ^ (-6 * η)) w (AdmS (fun k => k ∈ B) h.s) :=
      cutCone_of_crit (by have := HR.hd; omega) hBal hRI hyc x₁ x₂ hcone
    have hcrit' : Crit L γ η R := by rw [hRR]; exact hcrit
    have hdev := cut_excess_cone (Adm0 := fun k => k ∈ B) HR hI P hP0 hcd hPinh R hR
      hcrit' (fun k0 hk0 => (hBB0 hk0).2.2.1) hα hcone' 2 le_rfl
    have hs' : h'.s = h.s.cutSt v v₂ x₁ x₂ (.alpha R kp) (.alpha R kp) := by
      show h.s.cutSt v v₂ x₁ x₂ (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta)
        (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta) = _
      rw [ite_eq_left hα]
    have hF : h'.s.M.numComponents = h.s.M.numComponents :=
      numComponents_cut_of_same h.s.M hcd ((isAlphaCut_iff h.s.M hcd).1 hα)
    have hBv : vBeta h'.s = vBeta h.s := by rw [hs']; exact vBeta_cutSt_alpha h.s hcd hε R kp
    have hAp : apProd L γ η h'.s = apProd L γ η h.s * apFactor L γ η (.alpha R kp) ^ 2 := by
      rw [hs']; exact apProd_cutSt_alpha h.s L γ η hcd hε R kp
    have hst := stepRHS_alpha hL (apProd_pos hL hap) hF hBv hAp
    have hEx : 0 ≤ excessRHS L γ η [(R, 0), (R, 0)] 0 0 := by rw [excessRHS_alpha]; positivity
    refine hdev.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    rw [hst, hkp0]
    have hLp : 0 ≤ L ^ (-5 * η * ((2 : ℕ) : ℝ)) := Real.rpow_nonneg hL.le _
    have h5 : (0 : ℝ) ≤ 3 * 5 ^ d := by positivity
    have hle := le_max_left (cAlpha d γ η) (cBeta η c)
    calc 3 * 5 ^ d * cAlpha d γ η * L ^ (-5 * η * ((2 : ℕ) : ℝ)) * excessRHS L γ η [(R, 0), (R, 0)] 0 0
        = (3 * 5 ^ d) * (L ^ (-5 * η * ((2 : ℕ) : ℝ)) * excessRHS L γ η [(R, 0), (R, 0)] 0 0) *
            cAlpha d γ η := by ring
      _ ≤ (3 * 5 ^ d) * (L ^ (-5 * η * ((2 : ℕ) : ℝ)) * excessRHS L γ η [(R, 0), (R, 0)] 0 0) *
            max (cAlpha d γ η) (cBeta η c) := mul_le_mul_of_nonneg_left hle (mul_nonneg h5 (mul_nonneg hLp hEx))
      _ = 3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) * excessRHS L γ η [(R, 0), (R, 0)] 0 0 *
            L ^ (-5 * η * ((2 : ℕ) : ℝ)) := by ring

end trip

/-- **A Step D1 or re-cut node keeps the bank** (post state `h.vinePostGL K`). -/
theorem nodeGL_bank {L γ η : ℝ} {w : Mom d} {h h' : HSt V D₀} (K : Step1.VineCut Src.γL h.s.M)
    (hK : h' = h.vinePostGL K) {A B : Set (D₀ → (Fin d → ℤ))} (hBA : B ⊆ A) {b : ℕ} (hbank : bank L γ η w h A ≤ b) :
    bank L γ η w h' B ≤ b := by
  rw [hK]; exact (bank_vinePostGL_le h K hBA).trans hbank

end WaveTurbulence.GammaLow.Flower.H2.Ghost
