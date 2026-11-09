/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase1B
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase1C
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase1D
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase2E
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1b
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase2b
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase3c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEx1Cone
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.ChainSpec
/-! **Ghost assembly, Phase 1 (E): the vine node with the bank** (design: `CHAIN-DESIGN.md`).

`node1_bank`: for a vine node `t` (H's `Node1`, post state `h.vinePostL K R kp`) of a class `A` with bank `≤ b` and a
split index `σ`, the split class `B = vineSplit … σ` (`split1` with the twins `fa`, `fb` and the joint gap) satisfies
`Inv1` at the post state, `epsCount` drops, and for `k = k1Of σ`: the child's bank is `≤ b + k` and
`QS h B ≤ 3·5^d·vCost·L^{-5ηk} · QS h' B`. The class `k = 0` uses H's `node1_facts` (`Ex1A`/`Ex1N`) and the twin lock
(`vine_twin_locked`); a cone class uses `Ex1Cone` with `k = 2` and `jointCone_of_crit` (the cut `K'` that `Ex1Cone`
returns has the same post state, hence the same joint record). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem alphaOrBeta_eq_alpha {F F0 : ℕ} {R R₀ : ℝ} {kp kp₀ : ℕ} (h : alphaOrBeta F F0 R kp = .alpha R₀ kp₀) :
    F ≤ F0 ∧ R = R₀ ∧ kp = kp₀ := by
  unfold alphaOrBeta at h
  split_ifs at h with hF
  · obtain ⟨h1, h2⟩ := Cls.alpha.inj h
    exact ⟨hF, h1, h2⟩

theorem ofReal_le_mul_rpow_zero {a X L η : ℝ} (ha : 1 ≤ a) :
    ENNReal.ofReal X ≤ ENNReal.ofReal (a * X * L ^ (-5 * η * ((0 : ℕ) : ℝ))) := by
  simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
  rcases le_or_gt 0 X with hX | hX
  · exact ENNReal.ofReal_le_ofReal (by nlinarith)
  · rw [ENNReal.ofReal_of_nonpos hX.le]; exact zero_le

section vine
variable [Infinite V] {M₀ : Molecule V D₀} {C : H.CollData M₀} {crit : V → Prop} {L γ η : ℝ} {h : HSt V D₀}
  {t : T1 h}

/-- The cut of a vine node. -/
noncomputable def vcut (hn : H.Node1 C crit L γ η h t) : Step1.VineCut Src.γL h.s.M := Classical.choose hn

/-- The label and the bit of a vine node. -/
noncomputable def vR (t : T1 h) : ℝ := (2 : ℝ) ^ t.2.2.2.2.1
def vkp (t : T1 h) : ℕ := if t.2.2.2.2.2.1 then 50 else 0

theorem post1_eq (hn : H.Node1 C crit L γ η h t) :
    H.post1 C crit L γ η h t = h.vinePostL (vcut hn) (vR t) (vkp t) := by
  unfold H.post1; rw [dite_eq_left hn]; rfl

theorem vcut_spec (hn : H.Node1 C crit L γ η h t) :
    (vcut hn).x₁ = t.1 ∧ (vcut hn).x₂ = t.2.1 ∧ (vcut hn).y₁ = t.2.2.1 ∧ (vcut hn).y₂ = t.2.2.2.1 ∧
      H.VFacts C crit h (vcut hn) := by
  have hs := Classical.choose_spec hn
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.2.2.1⟩

/-- **The split class `σ` of a vine node.** -/
noncomputable def vineSplit (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀))
    (w : Mom d) (A : Set (D₀ → (Fin d → ℤ))) (hn : H.Node1 C crit L γ η h t) (σ : Sig1) :
    Set (D₀ → (Fin d → ℤ)) :=
  split1 L γ η w h (h.vinePostL (vcut hn) (vR t) (vkp t)) (vineSurv h (vcut hn) (vR t) (vkp t))
    ![(vcut hn).fa, (vcut hn).fb] (fun k0 => pgap L w k0 (h.s.pr t.1 t.2.1))
    (cls1 L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1) t.1 t.2.1 t.2.2.1 t.2.2.2.1
      t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) σ

/-- **The vine node with the bank.** -/
theorem node1_bank {Rn : ℕ} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    {δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))} {CA CN ν : ℝ}
    (HR : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hExA : H.Ex1A L γ η δ C₁ w M₀ P CA) (hExN : H.Ex1N L γ η δ C₁ w M₀ P CN ν)
    (hExC : Ex1Cone L γ η δ C₁ w M₀ P CA)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hA : H.Inv1 M₀ Rn C Un Fst L γ η w A0 A h) (hn : H.Node1 C crit L γ η h t) {b : ℕ}
    (hbank : bank L γ η w h A ≤ b) (σ : Sig1) :
    H.Inv1 M₀ Rn C Un Fst L γ η w A0 (vineSplit Un Fst w A hn σ) (H.post1 C crit L γ η h t) ∧
    epsCount (H.post1 C crit L γ η h t).s < epsCount h.s ∧
    bank L γ η w (H.post1 C crit L γ η h t) (vineSplit Un Fst w A hn σ) ≤ b + k1Of σ ∧
    QS L γ δ C₁ w P h (vineSplit Un Fst w A hn σ) ≤
      ENNReal.ofReal (3 * 5 ^ d * vCost L γ η CA CN h (H.post1 C crit L γ η h t) *
        L ^ (-5 * η * ((k1Of σ : ℕ) : ℝ))) * QS L γ δ C₁ w P (H.post1 C crit L γ η h t) (vineSplit Un Fst w A hn σ) := by
  obtain ⟨hx1, hx2, hy1, hy2, hF⟩ := vcut_spec hn
  set K := vcut hn with hKdef
  set R := vR t with hRdef
  set kp := vkp t with hkpdef
  set B0 := cls1 L γ η w h (H.Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1) t.1 t.2.1 t.2.2.1 t.2.2.2.1
      t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2 with hB0
  set B := vineSplit Un Fst w A hn σ with hBdef
  set n : Fin 2 → V := ![K.fa, K.fb] with hndef
  set g : (D₀ → (Fin d → ℤ)) → Mom d := fun k0 => pgap L w k0 (h.s.pr t.1 t.2.1) with hgdef
  have hpost : H.post1 C crit L γ η h t = h.vinePostL K R kp := post1_eq hn
  have hBB0 : B ⊆ B0 := fun k hk => hk.1
  have hBA : B ⊆ A := fun k hk => (hBB0 hk).1.1
  have hself : cls1 L γ η w h B t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
      t.2.2.2.2.2.2.2 = B := by
    ext k; exact ⟨fun hk => hk.1, fun hk => ⟨hk, (hBB0 hk).2⟩⟩
  obtain ⟨hinv, hlt, hdevTR⟩ := H.node1_facts HR hS hp0 hExA hExN hν hSrc hdec h0 (hA.mono hBA) hn
    (fun k hk hr => hr.tail (H.hstep1R_node hn (hBB0 hk.1)))
  rw [hself] at hinv hdevTR
  refine ⟨hinv, hlt, ?_⟩
  by_cases hBe : B = ∅
  · refine ⟨?_, ?_⟩
    · rw [hBe, bank_empty]; omega
    · rw [hBe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨hc, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hBA)) hBe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hBe
  have hI : Inv Rn h.s := hc.good.1
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) HR.hL
  have hIE := H.invE_of_reach hS (h0 κ (hA.1 (hBA hκ))) (H.Reach1.toAny (hr κ (hBA hκ)))
  have hBal : BalS h.s := hIE.bal
  have hCB : CompBeta h.s := hIE.comp
  have hRI : ∀ k0 ∈ B, HInv L γ η w k0 h ∧ HGap L w k0 h := fun k0 hk0 => by
    have := H.runInv_of_reach hS (h0 k0 (hA.1 (hBA hk0))) (H.Reach1.toAny (hr k0 (hBA hk0)))
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

end WaveTurbulence.GammaLow.FinalCount.Ghost
