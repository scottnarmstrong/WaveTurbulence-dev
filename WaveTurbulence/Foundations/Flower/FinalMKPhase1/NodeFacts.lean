/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Rel
public import WaveTurbulence.Foundations.Flower.FinalMKStep.Obj
public import WaveTurbulence.Foundations.FinalCount.LowChain14

/-! # C1b1 MK-PHASE1 (2): per-node facts of phase 1, generic in the reach relation; the re-cut nodes

* `node1_factsG`, `node1D_factsG`: main's `node1_factsL` (LowChain12) and `node1D_factsL` (LowChain13) with the reach
  relation `Reach1L` replaced by an arbitrary `Rch` (main reads the reach only through `CompBeta`, now `hRC`). Copied
  by source; sha256 in COPIED-SHA256SUMS.
* The re-cut step on a class: `AtomRelU.vinePostRC` (the charge records survive a re-cut: a non-`ε` joint has degree
  `2`, so its fresh half is deleted), `UCtx.stepRC` (the index drops by `jeps K`), `epsCount_vineStRC_lt` (one joint
  is `ε`).
* **Re-cut nodes** `Node1RC`: dart data `(x₁, x₂, y₁, y₂)` of a vine cut with fresh names `fresh3 h 0, 1` and the
  state-level facts `VFactsRC` (re-cut joints, exactly one `α/β` joint (`hone`), designation, the shape facts that
  `Ex1RC` reads, labels, and one pending re-cut paid (`hpend`)); the class is main's D1 class `cls1D`; the post state is
  `vinePostG`; `nodeRC_factsG` is the per-node fact from C1a's `Ex1RC`. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **Per-node facts of phase 1 (vine nodes)**, generic in the reach relation (main's `node1_factsL`). -/
theorem node1_factsG [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop}
    {crit : V → Prop} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))} {CA CN ν : ℝ} (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hExA : Ex1A L γ η δ C₁ w M₀ P CA) (hExN : Ex1N L γ η δ C₁ w M₀ P CN ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h)
    (hRC : ∀ κ ∈ A0, Rch κ h → CompBeta h.s) {t : T1 h} (hn : Node1 C crit L γ η h t)
    (hext : ∀ k ∈ cls1 L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2,
      Rch k h → Rch k (post1 C crit L γ η h t)) :
    Inv3L M₀ Rn Rch L w A0 (cls1 L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2)
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
  have hc' : UCtx M₀ R' (fun k => k ∈ B) L w (post1 C crit L γ η h t) := UCtx.step1 hκ hst hpp hcc
  have hap' : ApPos (post1 C crit L γ η h t).s := by
    rw [hK, vinePost_s]; exact apPos_vineSt hap K c hcpos
  have hr' : ∀ k ∈ B, Rch k (post1 C crit L γ η h t) :=
    fun k hk => hext k hk (hr k (hsub hk))
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨⟨R', hR', hc'⟩, hap', hr'⟩⟩, hlt, ?_⟩
  have hI : Inv R' h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hCB : CompBeta h.s := hRC κ (hA.1 (hsub hκ)) (hr κ (hsub hκ))
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
    have hc1 : c = Cls.alpha R kp := by rw [hcdef]; unfold alphaOrBeta; rw [ite_eq_left hF]
    have hc2 : alphaOrBeta K'.post.numComponents h.s.M.numComponents R' kp' = Cls.alpha R' kp' := by
      unfold alphaOrBeta; rw [ite_eq_left (hF' ▸ hF)]
    rw [← hcdef, hc1, hc2] at hcc'
    obtain ⟨hR1, hkp1⟩ := Cls.alpha.inj hcc'
    subst hR1 hkp1
    have hd := hdev (hF' ▸ hF)
    have hX := stepRHS_vine_alpha (L := L) (γ := γ) (η := η) hL hap K (R := R) (kp := kp) hrem hF
    rw [ite_eq_left (by rw [hnum]; exact hF)]
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
    rw [ite_eq_right (by rw [hnum]; exact hF)]
    rw [excessRHS2_vine hL, ← hX, ← mul_assoc] at hd
    exact hd


/-- **Per-node facts of phase 1 (D1 nodes)**, generic in the reach relation (main's `node1D_factsL`). -/
theorem node1D_factsG [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop}
    {crit : V → Prop} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))} {CD ν : ℝ} (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S)
    (hExD : Ex1D L γ η δ C₁ w M₀ C P CD ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h)
    (hRC : ∀ κ ∈ A0, Rch κ h → CompBeta h.s) {t : T1D h} (hn : Node1D C crit h t)
    (hext : ∀ k ∈ cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2,
      Rch k h → Rch k (post1D C crit h t)) :
    Inv3L M₀ Rn Rch L w A0 (cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) (post1D C crit h t) ∧
    epsCount (post1D C crit h t).s < epsCount h.s ∧
    QS L γ δ C₁ w P h (cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) ≤
      ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2) *
        QS L γ δ C₁ w P (post1D C crit h t) (cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  set B := cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2 with hB
  have hsub : B ⊆ A := fun k hk => hk.1
  obtain ⟨K, F, hK, -, -, -, -, -, -⟩ := node1D_spec hn
  have hlt : epsCount (post1D C crit h t).s < epsCount h.s := by
    rw [hK]; exact epsCount_vineStG_lt h.s K F.hu
  by_cases hAe : B = ∅
  · refine ⟨⟨hsub.trans hA.1, Or.inl hAe⟩, hlt, ?_⟩
    rw [hAe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨⟨R', hR', hc⟩, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hAe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hcc := uctx_mono hc (fun k (hk : k ∈ B) => hsub hk)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ B) => hA.1 (hsub hk))
  have hst := uStepD1_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn
  obtain ⟨j, R'', hj1, hjR, hc'⟩ := UCtx.stepD1 hκ hst hpp hcc
  have hap' : ApPos (post1D C crit h t).s := by
    rw [hK]; exact apPos_vineStG h.s K hap
  have hr' : ∀ k ∈ B, Rch k (post1D C crit h t) := fun k hk => hext k hk (hr k (hsub hk))
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨⟨R'', by omega, hc'⟩, hap', hr'⟩⟩, hlt, ?_⟩
  have hI : Inv R' h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hCB : CompBeta h.s := hRC κ (hA.1 (hsub hκ)) (hr κ (hsub hκ))
  have hMol : h.s.M.IsMolecule := isMolecule_of_compBeta hc.good hCB
  have hne : ∃ k0, (fun k => k ∈ B) k0 := ⟨κ, hκ⟩
  have hSrc' : ∀ k0, (fun k => k ∈ B) k0 → SourceLadderGaps M₀ L w P k0 := fun k hk => hSrc k (hA.1 (hsub hk))
  have hdec' := fun k (hk : (fun k => k ∈ B) k) => hdec k (hA.1 (hsub hk))
  have hνat : (h.s.M.atoms.card : ℝ) ≤ ν := by
    have := card_atoms_leL_of_uctx hS hR' hcc
    exact le_trans (by exact_mod_cast this) hν
  rw [hK] at hst ⊢
  have hMol0 : M₀.IsMolecule := hS.isMolecule
  obtain ⟨K', he, hdev0⟩ := hExD hP0 hP hMol0 (fun k => k ∈ B) hne hSrc' hdec' hst hLC hcc.atom hMol F.hnl hνat
  have hdev := hdev0 (F.hcls K' he) (fun hd => F.hconn K' he hd)
  exact hdev


/-! ### The re-cut step on a class -/

section recut
variable {L γ η : ℝ} {w : Mom d} {M₀ : Molecule V D₀} {Rn : ℕ} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop}

/-- **The charge records along a re-cut** (main's `AtomRelU.vinePostG`, GL16, with re-cut joints): a non-`ε` joint has
degree `2`, so its fresh half (whose charge need not be pinned) is a deleted ghost. -/
theorem AtomRelU.vinePostRC {h : HSt V D₀} (hR : AtomRelU Adm0 L w h) (hpin : EpsPin Adm0 L w h) (K : VineCut h.s.M)
    (hu : RCJoint h.s K.C.upper) (hl : RCJoint h.s K.C.lower) :
    AtomRelU Adm0 L w (h.vinePostG K) := by
  have hup : K.C.upper ∈ h.s.M.atoms := objectAtoms_sub K.C K.a_mem
  have hlo : K.C.lower ∈ h.s.M.atoms := objectAtoms_sub K.C K.b_mem
  have h1 := (hR.toX (ex := fun _ => False)).cut K.cut_a .beta (jcls h.s.M K.C.upper)
    (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
    (Function.update h.anc K.fa (h.anc K.C.upper)) h.alive
  have h2 := h1.cut (h := ⟨h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ .beta (jcls h.s.M K.C.upper),
      h.s.pr K.x₁ K.x₂ :: h.hist,
      Function.update (Function.update h.crec K.C.upper (some (h.s.pr K.x₁ K.x₂, h.alive))) K.fa
        (some (h.s.pr K.x₁ K.x₂, h.alive)), Function.update h.anc K.fa (h.anc K.C.upper)⟩) K.cut_b .beta
    (jcls h.s.M K.C.lower)
    (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
    (Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower))
    (h.s.pr K.x₁ K.x₂ :: h.alive)
  refine (AtomRelX.del h2 (VineKeep K) (VineKeep.closed K) ?_ _ _).toU
  intro a _ hk hx
  obtain ⟨-, hka, hkb⟩ := hk
  rcases hx with ⟨hx1, -, -⟩ | ⟨rfl, hnp⟩
  · rcases hx1 with ⟨hf, -⟩ | ⟨rfl, hnp⟩
    · exact hf
    · have hd : h.s.M.deg K.C.upper ≠ 2 := fun e => hka ⟨rfl, e⟩
      have hε : h.s.cls K.C.upper = .eps := by
        rcases hu with e | ⟨-, e⟩
        · exact e
        · exact absurd e hd
      exact hnp (hpin _ hup hε)
  · have hd : h.s.M.deg K.C.lower ≠ 2 := fun e => hkb ⟨rfl, e⟩
    have hε : h.s.cls K.C.lower = .eps := by
      rcases hl with e | ⟨-, e⟩
      · exact e
      · exact absurd e hd
    obtain ⟨cl, hcl⟩ := hpin _ hlo hε
    refine hnp ⟨cl, fun k0 hk0 => ?_⟩
    show chargeAt (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂) L w (k0 ∘ h.s.down) K.C.lower = cl
    rw [chargeAt_cut_other h.s.M K.cut_a K.ab_ne.symm K.fa_ne_b.symm]
    exact hcl k0 hk0

/-- **`UCtx` along a re-cut**: the index drops by `jeps K` (C1a's `Inv.vineStRC`). -/
theorem UCtx.stepRC {C : CollData M₀} {h h' : HSt V D₀} (hs : UStepRC C L γ η w Adm0 h h')
    (hp : PinnedM0 Adm0 L w M₀) (hc : UCtx M₀ Rn Adm0 L w h) :
    ∃ j R', R' + j = Rn ∧ UCtx M₀ R' Adm0 L w h' := by
  cases hs with
  | vine K hu hl hrc htwin hsg hdu hdl =>
    obtain ⟨R', e, hI⟩ := Inv.vineStRC hc.good.1 K hu hl
    exact ⟨jeps K, R', e, ⟨⟨hI, clean_vineStG hc.good.2 K⟩, hc.anc.vinePostG K, hc.rel.vineStG K,
      AtomRelU.vinePostRC hc.atom (hc.eps hp) K hu hl⟩⟩

/-- `epsCount` drops along `vineStG` when the lower joint is `ε` (main's `epsCount_vineStG_lt` at the other joint). -/
theorem epsCount_vineStG_lt' (s : St.{u} V D₀) (K : VineCut s.M) (hl : s.cls K.C.lower = .eps) :
    epsCount (vineStG s K) < epsCount s := by
  unfold epsCount
  have hsub : (vineStG s K).M.atoms.filter (fun a => (vineStG s K).cls a = .eps) ⊆
      (s.M.atoms.filter fun a => s.cls a = .eps).erase K.C.lower := by
    intro a ha
    obtain ⟨ham, hae⟩ := Finset.mem_filter.1 ha
    rw [vineStG_atoms] at ham
    obtain ⟨ham1, hk⟩ := Finset.mem_filter.1 ham
    by_cases hfa : a = K.fa
    · subst hfa; rw [vineStG_cls_fa] at hae; exact absurd hae (jcls_ne_eps _ _)
    by_cases hfb : a = K.fb
    · subst hfb; rw [vineStG_cls_fb] at hae; exact absurd hae (jcls_ne_eps _ _)
    have has : a ∈ s.M.atoms := by
      rcases Finset.mem_insert.1 ham1 with e | e
      · exact absurd e hfb
      · rcases Finset.mem_insert.1 e with e | e
        · exact absurd e hfa
        · exact e
    rw [vineStG_cls_old s K hk.1 has] at hae
    have hal : a ≠ K.C.lower := fun e => hk.1 (e ▸ K.b_mem)
    exact Finset.mem_erase.2 ⟨hal, Finset.mem_filter.2 ⟨has, hae⟩⟩
  refine lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem ?_)
  exact Finset.mem_filter.2 ⟨objectAtoms_sub K.C K.b_mem, hl⟩

/-- `epsCount` drops along a re-cut with one `ε` joint. -/
theorem epsCount_vineStRC_lt (s : St.{u} V D₀) (K : VineCut s.M)
    (hone : s.cls K.C.upper = .eps ∨ s.cls K.C.lower = .eps) : epsCount (vineStG s K) < epsCount s := by
  rcases hone with hu | hl
  · exact epsCount_vineStG_lt s K hu
  · exact epsCount_vineStG_lt' s K hl

end recut

/-! ### Re-cut nodes -/

section rcnodes
variable {M₀ : Molecule V D₀} {m : ℕ}

/-- The state-level facts of a re-cut node: the step data of `HStepRC` that do not depend on the decoration, exactly
one `α/β` joint (`hone`, obligation 1 of the brief), the shape facts read by `Ex1RC` (main's `VFactsD1`), the labels,
and the pending re-cut paid by the step (`hpend`). -/
structure VFactsRC (C : CollData M₀) (crit : V → Prop) (E : Fin m → Object M₀) (L γ η : ℝ) (h : HSt V D₀)
    (K : VineCut h.s.M) : Prop where
  hu : RCJoint h.s K.C.upper
  hl : RCJoint h.s K.C.lower
  hrc : h.s.cls K.C.upper ≠ .eps ∨ h.s.cls K.C.lower ≠ .eps
  hone : h.s.cls K.C.upper = .eps ∨ h.s.cls K.C.lower = .eps
  hdu : Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂)
  hdl : Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂)
  hcls : ∀ K' : VineCut h.s.M, h.vinePostG K = h.vinePostG K' → SingleVineVC K' ∨ Nonempty (DoubleShape K')
  hconn : ∀ K' : VineCut h.s.M, h.vinePostG K = h.vinePostG K' → Nonempty (DoubleShape K') →
    ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G
  hnl : ∀ x, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x)
  hloss : ladderLoss h.s.M (h.s.M.atoms.filter (fun a => a ∉ K.C.atoms)) ≤ 86
  hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a
  hlab : ∀ a ∈ h.s.M.atoms, ∀ R kp, h.s.cls a = .alpha R kp → IsLabel L γ η R
  hpend : pendRC E (h.vinePostG K) + 1 ≤ pendRC E h

/-- A re-cut node. -/
def Node1RC [Infinite V] (C : CollData M₀) (crit : V → Prop) (E : Fin m → Object M₀) (L γ η : ℝ) (h : HSt V D₀)
    (t : T1D h) : Prop :=
  ∃ K : VineCut h.s.M, K.x₁ = t.1 ∧ K.x₂ = t.2.1 ∧ K.y₁ = t.2.2.1 ∧ K.y₂ = t.2.2.2 ∧ K.fa = fresh3 h 0 ∧ K.fb = fresh3 h 1 ∧
    VFactsRC C crit E L γ η h K

noncomputable def nodesRC [Infinite V] (C : CollData M₀) (crit : V → Prop) (E : Fin m → Object M₀) (L γ η : ℝ)
    (h : HSt V D₀) : Finset (T1D h) :=
  (Finset.univ : Finset (T1D h)).filter fun t => Node1RC C crit E L γ η h t

theorem nodesRC_card [Infinite V] (C : CollData M₀) (crit : V → Prop) (E : Fin m → Object M₀) (L γ η : ℝ)
    (h : HSt V D₀) :
    (nodesRC C crit E L γ η h).card ≤ Fintype.card h.s.D * (Fintype.card h.s.D * (Fintype.card h.s.D * Fintype.card h.s.D)) := by
  refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
  simp [Fintype.card_prod]

noncomputable def post1RC [Infinite V] (C : CollData M₀) (crit : V → Prop) (E : Fin m → Object M₀) (L γ η : ℝ)
    (h : HSt V D₀) (t : T1D h) : HSt V D₀ :=
  if hn : Node1RC C crit E L γ η h t then h.vinePostG (Classical.choose hn) else h

variable {C : CollData M₀} {crit : V → Prop} {E : Fin m → Object M₀} {L γ η : ℝ}

theorem nodeRC_spec [Infinite V] {h : HSt V D₀} {t : T1D h} (hn : Node1RC C crit E L γ η h t) :
    ∃ K : VineCut h.s.M, VFactsRC C crit E L γ η h K ∧ post1RC C crit E L γ η h t = h.vinePostG K ∧
      K.x₁ = t.1 ∧ K.x₂ = t.2.1 ∧ K.y₁ = t.2.2.1 ∧ K.y₂ = t.2.2.2 ∧ K.fa = fresh3 h 0 ∧ K.fb = fresh3 h 1 := by
  have hspec := Classical.choose_spec hn
  obtain ⟨e1, e2, e3, e4, e5, e6, F⟩ := hspec
  refine ⟨Classical.choose hn, F, ?_, e1, e2, e3, e4, e5, e6⟩
  unfold post1RC; rw [dite_eq_left hn]

/-- The re-cut on a class. -/
theorem uStepRC_node [Infinite V] {w : Mom d} {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {t : T1D h}
    (hn : Node1RC C crit E L γ η h t) :
    UStepRC C L γ η w (fun k => k ∈ cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) h (post1RC C crit E L γ η h t) := by
  obtain ⟨x₁, x₂, y₁, y₂⟩ := t
  obtain ⟨K, F, hK, e1, e2, e3, e4, -, -⟩ := nodeRC_spec hn
  simp only at e1 e2 e3 e4 hK ⊢
  rw [hK]
  subst e1 e2 e3 e4
  exact UStepRC.vine h K F.hu F.hl F.hrc (fun k hk => hk.2.2) (fun k hk => hk.2.1) F.hdu F.hdl

/-- `HStepRC` on a decoration of a re-cut class. -/
theorem hstepRC_node [Infinite V] {w : Mom d} {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {t : T1D h}
    (hn : Node1RC C crit E L γ η h t) {κ : D₀ → (Fin d → ℤ)}
    (hk : κ ∈ cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) : HStepRC C L γ η w κ h (post1RC C crit E L γ η h t) :=
  (uStepRC_node (A := A) hn).hstep hk

end rcnodes

/-- **Per-node facts of phase 1 (re-cut nodes)**: main's `node1D_factsL` with C1a's `Ex1RC`, `UCtx.stepRC` and
`epsCount_vineStRC_lt`. -/
theorem nodeRC_factsG [Infinite V] {M₀ : Molecule V D₀} {m : ℕ} {Rn : ℕ} {C : CollData M₀}
    {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {crit : V → Prop} {E : Fin m → Object M₀} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))} {CR ν : ℝ} (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S)
    (hExR : Ex1RC L γ η δ C₁ w M₀ C P CR ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    {h : HSt V D₀} (hA : Inv3L M₀ Rn Rch L w A0 A h)
    (hRC : ∀ κ ∈ A0, Rch κ h → CompBeta h.s) {t : T1D h} (hn : Node1RC C crit E L γ η h t)
    (hext : ∀ k ∈ cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2,
      Rch k h → Rch k (post1RC C crit E L γ η h t)) :
    Inv3L M₀ Rn Rch L w A0 (cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) (post1RC C crit E L γ η h t) ∧
    epsCount (post1RC C crit E L γ η h t).s < epsCount h.s ∧
    QS L γ δ C₁ w P h (cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) ≤
      ENNReal.ofReal (CR * excessRHS2 L γ η [] 1 2) *
        QS L γ δ C₁ w P (post1RC C crit E L γ η h t) (cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  set B := cls1D L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2 with hB
  have hsub : B ⊆ A := fun k hk => hk.1
  obtain ⟨K, F, hK, -, -, -, -, -, -⟩ := nodeRC_spec hn
  have hlt : epsCount (post1RC C crit E L γ η h t).s < epsCount h.s := by
    rw [hK]; exact epsCount_vineStRC_lt h.s K F.hone
  by_cases hAe : B = ∅
  · refine ⟨⟨hsub.trans hA.1, Or.inl hAe⟩, hlt, ?_⟩
    rw [hAe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨⟨R', hR', hc⟩, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hAe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hcc := uctx_mono hc (fun k (hk : k ∈ B) => hsub hk)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ B) => hA.1 (hsub hk))
  have hst := uStepRC_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn
  obtain ⟨j, R'', hjR, hc'⟩ := UCtx.stepRC hst hpp hcc
  have hap' : ApPos (post1RC C crit E L γ η h t).s := by
    rw [hK]; exact apPos_vineStG h.s K hap
  have hr' : ∀ k ∈ B, Rch k (post1RC C crit E L γ η h t) := fun k hk => hext k hk (hr k (hsub hk))
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨⟨R'', by omega, hc'⟩, hap', hr'⟩⟩, hlt, ?_⟩
  have hI : Inv R' h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hCB : CompBeta h.s := hRC κ (hA.1 (hsub hκ)) (hr κ (hsub hκ))
  have hMol : h.s.M.IsMolecule := isMolecule_of_compBeta hc.good hCB
  have hne : ∃ k0, (fun k => k ∈ B) k0 := ⟨κ, hκ⟩
  have hSrc' : ∀ k0, (fun k => k ∈ B) k0 → SourceLadderGaps M₀ L w P k0 := fun k hk => hSrc k (hA.1 (hsub hk))
  have hdec' := fun k (hk : (fun k => k ∈ B) k) => hdec k (hA.1 (hsub hk))
  have hνat : (h.s.M.atoms.card : ℝ) ≤ ν := by
    have := card_atoms_leL_of_uctx hS hR' hcc
    exact le_trans (by exact_mod_cast this) hν
  rw [hK] at hst ⊢
  have hMol0 : M₀.IsMolecule := hS.isMolecule
  obtain ⟨K', he, hdev0⟩ := hExR hP0 hP hMol0 (fun k => k ∈ B) hne hSrc' hdec' hst hLC hcc.atom hMol F.hnl hνat
  exact hdev0 (F.hcls K' he) (fun hd => F.hconn K' he hd)

end WaveTurbulence.Flower.FinalMKPhase1
