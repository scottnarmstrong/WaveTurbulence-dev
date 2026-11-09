/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase1b
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase3c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Gamma
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Step5c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmPhase1b`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, phase 1: the uniform step on a vine class, and the per-node facts.** -/
@[expose] public section
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

/-- `excessprop1 (1)` for Step 1 (no new component), the statement of `UStep1.excess` with the constants fixed. -/
def Ex1A (L γ η δ C₁ : ℝ) (w : Mom d) (M₀ : Molecule V D₀) (P : Finset V → ℝ) (CA : ℝ) : Prop :=
  ∀ (Adm0 : (D₀ → (Fin d → ℤ)) → Prop), (∃ k0, Adm0 k0) → (∀ k0, Adm0 k0 → SourceLadderGaps M₀ L w P k0) →
    (∀ k0, Adm0 k0 → ∃ c0, M₀.IsDecoration L w c0 k0 ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0) →
    ∀ {h h' : HSt V D₀}, UStep1 L γ η w Adm0 h h' → LCtx M₀ h.s → AtomRelU Adm0 L w h → h.s.M.IsMolecule →
      ∃ (K : Step1.VineCut Src.γL h.s.M) (R : ℝ) (kp : ℕ), h' = h.vinePostL K R kp ∧
        ((Step1.SingleVineVCGamma K ∨ Nonempty (Step1.DoubleShape K)) →
        K.post.numComponents ≤ h.s.M.numComponents →
          IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P) (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
            (ENNReal.ofReal (CA * excessRHS L γ η [(R, kp), (R, kp)] 0 0)))

/-- `excessprop1 (2)`: one new component. -/
def Ex1N (L γ η δ C₁ : ℝ) (w : Mom d) (M₀ : Molecule V D₀) (P : Finset V → ℝ) (CN ν : ℝ) : Prop :=
  ∀ (Adm0 : (D₀ → (Fin d → ℤ)) → Prop), (∃ k0, Adm0 k0) → (∀ k0, Adm0 k0 → SourceLadderGaps M₀ L w P k0) →
    (∀ k0, Adm0 k0 → ∃ c0, M₀.IsDecoration L w c0 k0 ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0) →
    ∀ {h h' : HSt V D₀}, UStep1 L γ η w Adm0 h h' → LCtx M₀ h.s → AtomRelU Adm0 L w h → h.s.M.IsMolecule →
      (∀ x, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x)) → (h.s.M.atoms.card : ℝ) ≤ ν →
      ∃ (K : Step1.VineCut Src.γL h.s.M) (R : ℝ) (kp : ℕ), h' = h.vinePostL K R kp ∧
        ((Step1.SingleVineVCGamma K ∨ Nonempty (Step1.DoubleShape K)) →
        (Nonempty (Step1.DoubleShape K) →
          ∃ G : Finset h.s.D, (∀ z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K G) →
        K.post.numComponents = h.s.M.numComponents + 1 →
          IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P) (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
            (ENNReal.ofReal (CN * WaveTurbulence.VineCount.excessRHS2 L γ η [] 1 2)))

/-- The vine step on a class. -/
theorem uStep1_node [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {crit : V → Prop} {L γ η : ℝ} {w : Mom d} {h : HSt V D₀}
    {A : Set (D₀ → (Fin d → ℤ))} {t : T1 h} (hn : Node1 C crit L γ η h t) :
    UStep1 L γ η w (fun k => k ∈ cls1 L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2)
      h (post1 C crit L γ η h t) := by
  obtain ⟨x₁, x₂, y₁, y₂, z, b, a, sg⟩ := t
  have hspec := Classical.choose_spec hn
  generalize hKd : Classical.choose hn = K at hspec
  obtain ⟨e1, e2, e3, e4, -, -, F, hR, ha, hb⟩ := hspec
  simp only at e1 e2 e3 e4 hR ha hb ⊢
  have hpost : post1 C crit L γ η h (x₁, x₂, y₁, y₂, z, b, a, sg) = h.vinePostL K ((2 : ℝ) ^ z) (if b then 50 else 0) := by
    unfold post1
    rw [dif_pos hn, hKd]
  rw [hpost]
  subst e1 e2 e3 e4
  refine UStep1.vine h K ((2 : ℝ) ^ z) (if b then 50 else 0) hR (by cases b <;> simp) F.hu F.hl
    (fun k hk => hk.2.2.1) (fun k hk => hk.2.2.2.1) (fun k hk => hk.2.2.2.2.1) ?_ ?_ (fun k hk => hk.2.1) F.h3a F.h3b
  · intro h50
    have hb' : b = true := by cases b <;> simp_all
    obtain ⟨q, vis, hcr, hq⟩ := hb hb'
    refine ⟨q, hq, ⟨a, ha, vis, hcr⟩, if sg then 1 else -1, by cases sg <;> simp, fun k hk => ?_⟩
    have := hk.2.2.2.2.2.1 hb'
    have hq' : qOf h a (h.s.pr K.x₁ K.x₂) = q := by simp [qOf, hcr]
    rw [hq'] at this
    exact this
  · intro h0 k hk
    have hb' : b = false := by cases b <;> simp_all
    exact hk.2.2.2.2.2.2 hb'

/-- The cut underlying a node. -/
theorem node1_spec [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {crit : V → Prop} {L γ η : ℝ} {h : HSt V D₀} {t : T1 h}
    (hn : Node1 C crit L γ η h t) :
    ∃ K : Step1.VineCut Src.γL h.s.M, VFacts C crit h K ∧
      post1 C crit L γ η h t = h.vinePostL K ((2 : ℝ) ^ t.2.2.2.2.1) (if t.2.2.2.2.2.1 then 50 else 0) := by
  have hspec := Classical.choose_spec hn
  refine ⟨Classical.choose hn, hspec.2.2.2.2.2.2.1, ?_⟩
  unfold post1; rw [dif_pos hn]

theorem vinePost_cls_eq {h : HSt V D₀} {K K' : Step1.VineCut Src.γL h.s.M} {R R' : ℝ} {kp kp' : ℕ}
    (he : h.vinePostL K R kp = h.vinePostL K' R' kp') :
    alphaOrBeta K.post.numComponents h.s.M.numComponents R kp = alphaOrBeta K'.post.numComponents h.s.M.numComponents R' kp' := by
  set c := alphaOrBeta K.post.numComponents h.s.M.numComponents R kp
  set c' := alphaOrBeta K'.post.numComponents h.s.M.numComponents R' kp'
  have hat : (h.vinePostL K R kp).s.M.atoms = (h.vinePostL K' R' kp').s.M.atoms := by rw [he]
  have hcl : (h.vinePostL K R kp).s.cls = (h.vinePostL K' R' kp').s.cls := by rw [he]
  have hmem : K'.fa ∈ (h.vinePostL K R kp).s.M.atoms := by rw [hat]; exact fa_mem_vineSt h.s K' c'
  have hnot : K'.fa ∉ h.s.M.atoms := K'.fa_fresh
  have hfa : K'.fa = K.fa ∨ K'.fa = K.fb := by
    have hm : K'.fa ∈ (vineSt h.s K c).M.atoms := hmem
    rw [vineSt_atoms, Finset.mem_filter] at hm
    rcases Finset.mem_insert.1 hm.1 with e | e
    · exact Or.inr e
    · rcases Finset.mem_insert.1 e with e | e
      · exact Or.inl e
      · exact absurd e hnot
  have h1 : (vineSt h.s K' c').cls K'.fa = c' := vineSt_cls_fa_AsmP1Basic h.s K' c'
  have h2 : (vineSt h.s K c).cls = (vineSt h.s K' c').cls := hcl
  rw [← h2] at h1
  rcases hfa with e | e
  · rw [e, vineSt_cls_fa_AsmP1Basic] at h1; exact h1
  · rw [e, vineSt_cls_fb_AsmP1Basic] at h1; exact h1

theorem vinePost_F_eq {h : HSt V D₀} {K K' : Step1.VineCut Src.γL h.s.M} {R R' : ℝ} {kp kp' : ℕ}
    (he : h.vinePostL K R kp = h.vinePostL K' R' kp') : K.post.numComponents = K'.post.numComponents := by
  have := congrArg (fun p : HSt V D₀ => p.s.M.numComponents) he
  exact this

/-- The Step-1 move `HStep1C` on a decoration of a vine class. -/
theorem hstep1C_node [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {crit : V → Prop} {L γ η : ℝ} {w : Mom d} {h : HSt V D₀}
    {A : Set (D₀ → (Fin d → ℤ))} {t : T1 h} (hn : Node1 C crit L γ η h t) {κ : D₀ → (Fin d → ℤ)}
    (hk : κ ∈ cls1 L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) :
    HStep1C C L γ η w κ h (post1 C crit L γ η h t) := by
  obtain ⟨x₁, x₂, y₁, y₂, z, b, a, sg⟩ := t
  have hspec := Classical.choose_spec hn
  generalize hKd : Classical.choose hn = K at hspec
  obtain ⟨e1, e2, e3, e4, -, -, F, hR, ha, hb⟩ := hspec
  simp only at e1 e2 e3 e4 hR ha hb hk ⊢
  have hpost : post1 C crit L γ η h (x₁, x₂, y₁, y₂, z, b, a, sg) = h.vinePostL K ((2 : ℝ) ^ z) (if b then 50 else 0) := by
    unfold post1
    rw [dif_pos hn, hKd]
  rw [hpost]
  subst e1 e2 e3 e4
  obtain ⟨-, hsg, ga, gb, htw, hb1, hb0⟩ := hk
  have hkp : (if b then 50 else 0) = 0 ∨ (if b then 50 else 0) = 50 := by cases b <;> simp
  have hI1 : (if b then 50 else 0) = 50 ↔ IotaHit L η w κ h.alive (h.s.pr K.x₁ K.x₂) ((2 : ℝ) ^ z) := by
    constructor
    · intro h50
      have hb' : b = true := by cases b <;> simp_all
      obtain ⟨q, vis, hcr, hq⟩ := hb hb'
      have := hb1 hb'
      have hq' : qOf h a (h.s.pr K.x₁ K.x₂) = q := by simp [qOf, hcr]
      rw [hq'] at this
      exact ⟨q, HSt.mem_alive.2 ⟨hq, ⟨a, ha, vis, hcr⟩⟩, if sg then 1 else -1, by cases sg <;> simp, this.1, this.2⟩
    · intro hit
      by_contra hne
      have hb' : b = false := by cases b <;> simp_all
      exact (hb0 hb').1 hit
  have hI2 : (if b then 50 else 0) = 50 ↔
      IotaHit L η w κ (h.s.pr K.x₁ K.x₂ :: h.alive) (h.s.pr K.y₁ K.y₂) ((2 : ℝ) ^ z) := by
    constructor
    · intro h50
      exact iotaHit_twin ((hI1.1 h50).mono fun q hq => List.mem_cons_of_mem _ hq) htw
    · intro hit
      by_contra hne
      have hb' : b = false := by cases b <;> simp_all
      exact (hb0 hb').2 hit
  exact HStep1C.vine h K ((2 : ℝ) ^ z) (if b then 50 else 0) hR hkp F.hu F.hl ga gb htw hI1 hI2 hsg F.h3a F.h3b F.hdu F.hdl

theorem hstep1R_node [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {crit : V → Prop} {L γ η : ℝ} {w : Mom d} {h : HSt V D₀}
    {A : Set (D₀ → (Fin d → ℤ))} {t : T1 h} (hn : Node1 C crit L γ η h t) {κ : D₀ → (Fin d → ℤ)}
    (hk : κ ∈ cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
      t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) :
    HStep1R C Un Fst L γ η w κ h (post1 C crit L γ η h t) := by
  have hC := hstep1C_node hn hk
  obtain ⟨hkA, -⟩ := hk
  obtain ⟨-, U, hU, hUK, hUD, hUJ, hord⟩ := hkA
  obtain ⟨x₁, x₂, y₁, y₂, z, b, a, sg⟩ := t
  have hspec := Classical.choose_spec hn
  generalize hKd : Classical.choose hn = K at hspec
  obtain ⟨e1, e2, e3, e4, e5, e6, -⟩ := hspec
  simp only at e1 e2 e3 e4 hUK hUD hUJ
  have hpost : post1 C crit L γ η h (x₁, x₂, y₁, y₂, z, b, a, sg) = h.vinePostL K ((2 : ℝ) ^ z) (if b then 50 else 0) := by
    unfold post1
    rw [dif_pos hn, hKd]
  rw [hpost] at hC ⊢
  subst e1 e2 e3 e4
  exact HStep1R.vine h K _ _ hC U hU (hUK K rfl rfl rfl rfl e5 e6) hUD hUJ hord

/-- **Per-node facts of phase 1 (vine nodes).** -/
theorem node1_facts [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {crit : V → Prop} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))} {CA CN ν : ℝ} (H : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hExA : Ex1A L γ η δ C₁ w M₀ P CA) (hExN : Ex1N L γ η δ C₁ w M₀ P CN ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {h : HSt V D₀} (hA : Inv1 M₀ Rn C Un Fst L γ η w A0 A h) {t : T1 h} (hn : Node1 C crit L γ η h t)
    (hext : ∀ k ∈ cls1 L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2,
      Reach1 C Un Fst L γ η w k h → Reach1 C Un Fst L γ η w k (post1 C crit L γ η h t)) :
    Inv1 M₀ Rn C Un Fst L γ η w A0 (cls1 L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2)
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
  rcases hA.2 with he | ⟨hc, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hAe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hcc := uctx_mono hc (fun k (hk : k ∈ B) => hsub hk)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ B) => hA.1 (hsub hk))
  have hst := uStep1_node (w := w) (A := A) hn
  have hc' : UCtx M₀ Rn (fun k => k ∈ B) L w (post1 C crit L γ η h t) := UCtx.step1L hκ hst hpp hcc
  have hap' : ApPos (post1 C crit L γ η h t).s := by
    rw [hK, vinePost_s]; exact apPos_vineSt hap K c hcpos
  have hr' : ∀ k ∈ B, Reach1 C Un Fst L γ η w k (post1 C crit L γ η h t) :=
    fun k hk => hext k hk (hr k (hsub hk))
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨hc', hap', hr'⟩⟩, hlt, ?_⟩
  have hI : Inv Rn h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hCB : CompBeta h.s := (invE_of_reach hS (h0 κ (hA.1 (hsub hκ)))
    (Reach1.toAny (hr κ (hsub hκ)))).comp
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
      have := UCtx.card_atoms_le hS hcc
      exact le_trans (by exact_mod_cast this) hν
    obtain ⟨K', R', kp', he, hdev0⟩ := hExN (fun k => k ∈ B) hne hSrc' hdec' hst hLC hcc.atom hMol F.hnl hνat
    have hdev := hdev0 (F.hcls _ _ K' R' kp' he) (fun hd => F.hconn _ _ K' R' kp' he hd)
    have hF' := vinePost_F_eq he
    have hd := hdev (hF' ▸ hF1)
    have hX := stepRHS_vine_new (L := L) (γ := γ) (η := η) hL hap K (R := R) (kp := kp) hrem hF1
    rw [if_neg (by rw [hnum]; exact hF)]
    rw [excessRHS2_vine hL, ← hX, ← mul_assoc] at hd
    exact hd

end WaveTurbulence.GammaLow.FinalCount.H
