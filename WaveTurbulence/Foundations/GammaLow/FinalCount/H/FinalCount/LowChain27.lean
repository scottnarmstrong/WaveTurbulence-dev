/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain27
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain26
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain27`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, session 6 (R79), LC-B (1): B-persistence.**  `B` is the set of loop atoms of the original molecule (degree `≤ 2`
in `M₀ = M.unloop`, all `M₀`-darts at a `b ∈ B` carry one label, no SG object contains a `b`).  Along every step of the LOW run an atom
of `B` stays an `ε`-atom (Steps 2, 3, 4 and triple cuts need degree `≥ 3`; Step D3 needs a nonzero pair gap; the vine steps remove only
collected, hence SG, objects).  `QB` packages `RunAux`, `InvL` and `BP`; `QB_reach4` carries it along `Reach4L`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The data of B-persistence at the base molecule. -/
structure BHyp (M₀ : Molecule V D₀) (B : Finset V) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀))
    (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : Prop where
  sub : ∀ b ∈ B, b ∈ M₀.atoms
  deg : ∀ b ∈ B, M₀.deg b ≤ 2
  zg : ∀ b ∈ B, ∀ x y, M₀.atom x = b → M₀.atom y = b → κ x = κ y
  sg : ∀ U, Collected C (Un κ) L γ η w κ U → ∀ b ∈ B, b ∉ U.atoms

section bp
variable {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
  {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {B : Finset V} {h h' : HSt V D₀} {Rn : ℕ}

theorem BP.initL (M₀ : Molecule V D₀) {B : Finset V} (hB : ∀ b ∈ B, b ∈ M₀.atoms) : BP B (HSt.init M₀) :=
  fun b hb => ⟨hB b hb, rfl⟩

alias _root_.WaveTurbulence.FinalCountAsm.BP.initL := _root_.WaveTurbulence.GammaLow.FinalCount.H.BP.initL
theorem BP.deg_leL (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ) :
    ∀ b ∈ B, h.s.M.deg b ≤ 2 := fun b hb => by
  rw [deg_eps_eq hA (hbp b hb).1 (hbp b hb).2]; exact H.deg b hb

alias _root_.WaveTurbulence.FinalCountAsm.BP.deg_leL := _root_.WaveTurbulence.GammaLow.FinalCount.H.BP.deg_leL
theorem BP.cutL (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ) {v v₂ : V} {x₁ x₂ : h.s.D}
    {c₁ c₂ : Cls} (hc : h.s.M.IsCutData v v₂ x₁ x₂) (h3 : 3 ≤ h.s.M.deg v)
    (hs : h'.s = h.s.cutSt v v₂ x₁ x₂ c₁ c₂) : BP B h' := by
  intro b hb
  have hd := hbp.deg_leL hA H b hb
  have hbv : b ≠ v := fun e => by rw [e] at hd; omega
  rw [hs]
  exact bp_cutSt hc (hbp b hb).1 hbv (hbp b hb).2

alias _root_.WaveTurbulence.FinalCountAsm.BP.cutL := _root_.WaveTurbulence.GammaLow.FinalCount.H.BP.cutL
theorem BP.vineL (hbp : BP B h) (K : Step1.VineCut Src.γL h.s.M) (c : Cls) (hK : ∀ b ∈ B, b ∉ K.C.atoms)
    (hs : h'.s = vineSt h.s K c) : BP B h' := by
  intro b hb
  obtain ⟨hba, hbe⟩ := hbp b hb
  have hf1 : b ≠ K.fa := fun e => K.fa_fresh (e ▸ hba)
  have hf2 : b ≠ K.fb := fun e => K.fb_fresh (e ▸ hba)
  rw [hs]
  refine ⟨?_, ?_⟩
  · rw [vineSt_atoms, Finset.mem_filter]
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hba), hK b hb⟩
  · rw [vineSt_cls_old_AsmP1Basic h.s K c hba (hK b hb)]; exact hbe

alias _root_.WaveTurbulence.FinalCountAsm.BP.vineL := _root_.WaveTurbulence.GammaLow.FinalCount.H.BP.vineL
theorem BP.vineGL (hbp : BP B h) (K : Step1.VineCut Src.γL h.s.M) (hK : ∀ b ∈ B, b ∉ K.C.atoms)
    (hs : h'.s = vineStG h.s K) : BP B h' := by
  intro b hb
  obtain ⟨hba, hbe⟩ := hbp b hb
  have hf1 : b ≠ K.fa := fun e => K.fa_fresh (e ▸ hba)
  have hf2 : b ≠ K.fb := fun e => K.fb_fresh (e ▸ hba)
  rw [hs]
  refine ⟨?_, ?_⟩
  · rw [vineStG_atoms, Finset.mem_filter]
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hba), hK b hb, fun e => hf1 e.1, fun e => hf2 e.1⟩
  · rw [vineStG_cls_old h.s K (hK b hb) hba]; exact hbe

alias _root_.WaveTurbulence.FinalCountAsm.BP.vineGL := _root_.WaveTurbulence.GammaLow.FinalCount.H.BP.vineGL
theorem BP.triL (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ) (T : TriData h.s.M) (Q : Fin 2 → ℝ)
    (kp : Fin 2 → ℕ) (hcl : PClosed T.kept (triKeep h.s T)) (h3 : ∀ j, h.s.cls (T.t j) = .eps → 3 ≤ h.s.M.deg (T.t j))
    (hs : h'.s = triSt h.s T Q kp hcl) : BP B h' := by
  intro b hb
  obtain ⟨hba, hbe⟩ := hbp b hb
  have hd := hbp.deg_leL hA H b hb
  have hbt : ∀ j, b ≠ T.t j := fun j e => by
    have := h3 j (by rw [← e]; exact hbe)
    rw [← e] at this; omega
  rw [hs]
  refine ⟨?_, ?_⟩
  · rw [triSt_atoms']
    exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hba, hbt⟩)
  · rw [triSt_cls, triCls_other T Q kp (fun j e => T.f_fresh j (by rw [← e]; exact hba))]; exact hbe

alias _root_.WaveTurbulence.FinalCountAsm.BP.triL := _root_.WaveTurbulence.GammaLow.FinalCount.H.BP.triL
theorem BP.d3L (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s) (H : BHyp M₀ B C Un L γ η w κ)
    (hs : HStepD3 C L γ η w κ h h') : BP B h' := by
  cases hs with
  | cut v x₁ x₂ hv hε hd hx₁ hx₂ hne ho₁ ho₂ hnz hdes =>
    intro b hb
    obtain ⟨hba, hbe⟩ := hbp b hb
    have hbv : b ≠ v := by
      intro e
      subst e
      apply hnz
      have e1 : M₀.atom (h.s.down x₁) = b := by rw [hD.eps x₁ (by rw [hx₁]; exact hbe), hx₁]
      have e2 : M₀.atom (h.s.down x₂) = b := by rw [hD.eps x₂ (by rw [hx₂]; exact hbe), hx₂]
      have := H.zg b hb _ _ e1 e2
      show Molecule.gapAt L w (κ ∘ h.s.down) x₁ x₂ = 0
      unfold Molecule.gapAt Molecule.kvec
      simp only [Function.comp_apply, this, sub_self]
    refine ⟨hba, ?_⟩
    show (h.s.betaSt v).cls b = .eps
    rw [St.betaSt_cls, Function.update_of_ne hbv]; exact hbe

alias _root_.WaveTurbulence.FinalCountAsm.BP.d3L := _root_.WaveTurbulence.GammaLow.FinalCount.H.BP.d3L
theorem BP.step1RLL (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ)
    (hs : HStep1RL C Un Fst L γ η w κ h h') : BP B h' := by
  cases hs with
  | old hs =>
    cases hs with
    | vine K R kp hs U hU hUK hUD hUJ hord =>
      exact hbp.vineL K _ (fun b hb => by rw [← hUK]; exact H.sg U hU b hb) rfl
    | triple _ hs hs3 hall hF =>
      cases hs3 with
      | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes => exact hbp.cutL hA H hc h3 rfl
  | d1 K hs U hU hUK hUD hUJ hord =>
    exact hbp.vineGL K (fun b hb => by rw [← hUK]; exact H.sg U hU b hb) rfl

alias _root_.WaveTurbulence.FinalCountAsm.BP.step1RLL := _root_.WaveTurbulence.GammaLow.FinalCount.H.BP.step1RLL
theorem BP.step2L (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ)
    (hs : HStep2C C L γ η w κ h h') : BP B h' := by
  cases hs with
  | mk T hel hs hT =>
    cases hs with
    | tri T' Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₁ h3 => exact hbp.triL hA H T' Q kp hcl h3 rfl

alias _root_.WaveTurbulence.FinalCountAsm.BP.step2L := _root_.WaveTurbulence.GammaLow.FinalCount.H.BP.step2L
theorem BP.step3L (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ)
    (hs : HStep3C C L γ η w κ h h') : BP B h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes => exact hbp.cutL hA H hc h3 rfl

alias _root_.WaveTurbulence.FinalCountAsm.BP.step3L := _root_.WaveTurbulence.GammaLow.FinalCount.H.BP.step3L
theorem BP.step4L (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ)
    (hs : HStep4 L w κ h h') : BP B h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc hε hβ hnz h3 => exact hbp.cutL hA H hc h3 rfl

alias _root_.WaveTurbulence.FinalCountAsm.BP.step4L := _root_.WaveTurbulence.GammaLow.FinalCount.H.BP.step4L
end bp

section qb
variable {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
  {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {B : Finset V} {h h' : HSt V D₀} {Rn : ℕ}

/-- The combined invariant: the ancestor relation, the class invariant at some index `≤ Rn`, and B-persistence. -/
def QB (M₀ : Molecule V D₀) (C : CollData M₀) (Rn : ℕ) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (B : Finset V)
    (h : HSt V D₀) : Prop :=
  AncRel M₀ h.s h.anc ∧ (∃ R', R' ≤ Rn ∧ InvL M₀ R' L γ η w κ h) ∧ BP B h

theorem AncRel.step1LL (hs : HStep1L C L γ η w κ h h') (hA : AncRel M₀ h.s h.anc) : AncRel M₀ h'.s h'.anc := by
  cases hs with
  | old hs => exact hs.anc hA
  | low hs =>
    obtain ⟨K, hu, hl, hd2, htwin, hsg, rfl⟩ := hs.data
    exact hA.vinePostGL K

alias _root_.WaveTurbulence.FinalCountAsm.AncRel.step1LL := _root_.WaveTurbulence.GammaLow.FinalCount.H.AncRel.step1LL
theorem AncRel.stepD3L (hs : HStepD3 C L γ η w κ h h') (hA : AncRel M₀ h.s h.anc) : AncRel M₀ h'.s h'.anc := by
  obtain ⟨v, x₁, x₂, hDa, rfl⟩ := hs.data
  exact hA.betaSt v

alias _root_.WaveTurbulence.FinalCountAsm.AncRel.stepD3L := _root_.WaveTurbulence.GammaLow.FinalCount.H.AncRel.stepD3L
theorem QB.initL (hS : SubHypL Rn M₀) (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {B : Finset V} (hB : ∀ b ∈ B, b ∈ M₀.atoms) : QB M₀ C Rn L γ η w κ B (HSt.init M₀) :=
  ⟨AncRel.init M₀, ⟨Rn, le_rfl, InvL.init hS h0⟩, BP.initL M₀ hB⟩

theorem QB.step1RLL (H : BHyp M₀ B C Un L γ η w κ) (hs : HStep1RL C Un Fst L γ η w κ h h') (hq : QB M₀ C Rn L γ η w κ B h) :
    QB M₀ C Rn L γ η w κ B h' := by
  obtain ⟨ha, ⟨R', hR', hI⟩, hb⟩ := hq
  obtain ⟨R'', hR'', hI''⟩ := hI.step1LL hs.toL
  exact ⟨AncRel.step1LL hs.toL ha, ⟨R'', hR''.trans hR', hI''⟩, hb.step1RLL ha H hs⟩

theorem QB.stepD3L (H : BHyp M₀ B C Un L γ η w κ) (hs : HStepD3 C L γ η w κ h h') (hq : QB M₀ C Rn L γ η w κ B h) :
    QB M₀ C Rn L γ η w κ B h' := by
  obtain ⟨ha, ⟨R', hR', hI⟩, hb⟩ := hq
  obtain ⟨R'', hR'', hI''⟩ := hI.stepD3'L hs
  exact ⟨AncRel.stepD3L hs ha, ⟨R'', hR''.trans hR', hI''⟩, hb.d3L ha hI.rel H hs⟩

theorem QB.step2L (H : BHyp M₀ B C Un L γ η w κ) (hs : HStep2C C L γ η w κ h h') (hq : QB M₀ C Rn L γ η w κ B h) :
    QB M₀ C Rn L γ η w κ B h' := by
  obtain ⟨ha, ⟨R', hR', hI⟩, hb⟩ := hq
  exact ⟨hs.toHStep2.anc ha, ⟨R', hR', hI.step2 hs.toHStep2⟩, hb.step2L ha H hs⟩

theorem QB.step3L (H : BHyp M₀ B C Un L γ η w κ) (hs : HStep3C C L γ η w κ h h') (hq : QB M₀ C Rn L γ η w κ B h) :
    QB M₀ C Rn L γ η w κ B h' := by
  obtain ⟨ha, ⟨R', hR', hI⟩, hb⟩ := hq
  exact ⟨hs.toHStep3.anc ha, ⟨R', hR', hI.step3 hs.toHStep3⟩, hb.step3L ha H hs⟩

theorem QB.step4L (H : BHyp M₀ B C Un L γ η w κ) (hs : HStep4 L w κ h h') (hq : QB M₀ C Rn L γ η w κ B h) :
    QB M₀ C Rn L γ η w κ B h' := by
  obtain ⟨ha, ⟨R', hR', hI⟩, hb⟩ := hq
  exact ⟨hs.anc ha, ⟨R', hR', hI.step4 hs⟩, hb.step4L ha H hs⟩

theorem QB_reach4 (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (H : BHyp M₀ B C Un L γ η w κ) {h : HSt V D₀} (hr : Reach4L C Un Fst L γ η w κ h) :
    QB M₀ C Rn L γ η w κ B h := by
  obtain ⟨h₁, h₂, h₃, h₄, a, -, c, -, e, -, g, -, j⟩ := hr
  have q1 : QB M₀ C Rn L γ η w κ B h₁ :=
    rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.step1RLL H hs) a (QB.initL hS h0 H.sub)
  have q2 := rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.stepD3L H hs) c q1
  have q3 := rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.step2L H hs) e q2
  have q4 := rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.step3L H hs) g q3
  exact rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.step4L H hs) j q4

theorem QB_reach1 (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (H : BHyp M₀ B C Un L γ η w κ) {h : HSt V D₀} (hr : Reach1L C Un Fst L γ η w κ h) :
    QB M₀ C Rn L γ η w κ B h :=
  rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.step1RLL H hs) hr (QB.initL hS h0 H.sub)

theorem QB_reachD3 (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (H : BHyp M₀ B C Un L γ η w κ) {h : HSt V D₀} (hr : ReachD3 C Un Fst L γ η w κ h) :
    QB M₀ C Rn L γ η w κ B h := by
  obtain ⟨h₁, a, -, c⟩ := hr
  exact rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.stepD3L H hs) c (QB_reach1 hS h0 H a)

theorem QB_reach2 (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (H : BHyp M₀ B C Un L γ η w κ) {h : HSt V D₀} (hr : Reach2L C Un Fst L γ η w κ h) :
    QB M₀ C Rn L γ η w κ B h := by
  obtain ⟨h₁, h₂, a, s, c, -, e⟩ := hr
  exact rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.step2L H hs) e
    (QB_reachD3 hS h0 H (⟨h₁, a, s, c⟩ : ReachD3 C Un Fst L γ η w κ h₂))

theorem QB_reach3 (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (H : BHyp M₀ B C Un L γ η w κ) {h : HSt V D₀} (hr : Reach3L C Un Fst L γ η w κ h) :
    QB M₀ C Rn L γ η w κ B h := by
  obtain ⟨h₁, h₂, h₃, a, s, c, n, e, f, g⟩ := hr
  exact rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.step3L H hs) g
    (QB_reach2 hS h0 H (⟨h₁, h₂, a, s, c, n, e⟩ : Reach2L C Un Fst L γ η w κ h₃))

end qb

end WaveTurbulence.GammaLow.FinalCount.H
