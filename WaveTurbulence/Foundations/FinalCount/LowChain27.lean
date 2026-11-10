/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain26
/-! **FINALCOUNT LOW-CHAIN, session 6 (R79), LC-B (1): B-persistence.**  `B` is the set of loop atoms of the original molecule (degree `≤ 2`
in `M₀ = M.unloop`, all `M₀`-darts at a `b ∈ B` carry one label, no SG object contains a `b`).  Along every step of the LOW run an atom
of `B` stays an `ε`-atom (Steps 2, 3, 4 and triple cuts need degree `≥ 3`; Step D3 needs a nonzero pair gap; the vine steps remove only
collected, hence SG, objects).  `QB` packages `RunAux`, `InvL` and `BP`; `QB_reach4` carries it along `Reach4L`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The loop atoms are still `ε`-atoms of the state. -/
def BP (B : Finset V) (h : HSt V D₀) : Prop := ∀ b ∈ B, b ∈ h.s.M.atoms ∧ h.s.cls b = .eps

/-- The data of B-persistence at the base molecule. -/
structure BHyp (M₀ : Molecule V D₀) (B : Finset V) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : Prop where
  sub : ∀ b ∈ B, b ∈ M₀.atoms
  deg : ∀ b ∈ B, M₀.deg b ≤ 2
  zg : ∀ b ∈ B, ∀ x y, M₀.atom x = b → M₀.atom y = b → κ x = κ y
  sg : ∀ U, Collected C (Un κ) L γ η w κ U → ∀ b ∈ B, b ∉ U.atoms

section bp
variable {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)}
  {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {B : Finset V} {h h' : HSt V D₀} {Rn : ℕ}

theorem BP.init (M₀ : Molecule V D₀) {B : Finset V} (hB : ∀ b ∈ B, b ∈ M₀.atoms) : BP B (HSt.init M₀) :=
  fun b hb => ⟨hB b hb, rfl⟩

theorem BP.deg_le (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ) :
    ∀ b ∈ B, h.s.M.deg b ≤ 2 := fun b hb => by
  rw [deg_eps_eq hA (hbp b hb).1 (hbp b hb).2]; exact H.deg b hb

theorem bp_cutSt {s : St.{u} V D₀} {v v₂ b : V} {x₁ x₂ : s.D} {c₁ c₂ : Cls} (hc : s.M.IsCutData v v₂ x₁ x₂)
    (hb : b ∈ s.M.atoms) (hbv : b ≠ v) (he : s.cls b = .eps) :
    b ∈ (s.cutSt v v₂ x₁ x₂ c₁ c₂).M.atoms ∧ (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls b = .eps := by
  have hv₂ : v₂ ∉ s.M.atoms := hc.2.1
  have hbv₂ : b ≠ v₂ := fun e => hv₂ (e ▸ hb)
  refine ⟨?_, ?_⟩
  · rw [cutSt_atoms]; exact Finset.mem_insert_of_mem hb
  · rw [cutSt_cls, Function.update_of_ne hbv₂, Function.update_of_ne hbv]; exact he

theorem BP.cut (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ) {v v₂ : V} {x₁ x₂ : h.s.D}
    {c₁ c₂ : Cls} (hc : h.s.M.IsCutData v v₂ x₁ x₂) (h3 : 3 ≤ h.s.M.deg v)
    (hs : h'.s = h.s.cutSt v v₂ x₁ x₂ c₁ c₂) : BP B h' := by
  intro b hb
  have hd := hbp.deg_le hA H b hb
  have hbv : b ≠ v := fun e => by rw [e] at hd; omega
  rw [hs]
  exact bp_cutSt hc (hbp b hb).1 hbv (hbp b hb).2

theorem BP.vine (hbp : BP B h) (K : VineCut h.s.M) (c : Cls) (hK : ∀ b ∈ B, b ∉ K.C.atoms)
    (hs : h'.s = vineSt h.s K c) : BP B h' := by
  intro b hb
  obtain ⟨hba, hbe⟩ := hbp b hb
  have hf1 : b ≠ K.fa := fun e => K.fa_fresh (e ▸ hba)
  have hf2 : b ≠ K.fb := fun e => K.fb_fresh (e ▸ hba)
  rw [hs]
  refine ⟨?_, ?_⟩
  · rw [vineSt_atoms, Finset.mem_filter]
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hba), hK b hb⟩
  · rw [vineSt_cls_old h.s K c hba (hK b hb)]; exact hbe

theorem BP.vineG (hbp : BP B h) (K : VineCut h.s.M) (hK : ∀ b ∈ B, b ∉ K.C.atoms)
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

theorem BP.tri (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ) (T : TriData h.s.M) (Q : Fin 2 → ℝ)
    (kp : Fin 2 → ℕ) (hcl : PClosed T.kept (triKeep h.s T)) (h3 : ∀ j, h.s.cls (T.t j) = .eps → 3 ≤ h.s.M.deg (T.t j))
    (hs : h'.s = triSt h.s T Q kp hcl) : BP B h' := by
  intro b hb
  obtain ⟨hba, hbe⟩ := hbp b hb
  have hd := hbp.deg_le hA H b hb
  have hbt : ∀ j, b ≠ T.t j := fun j e => by
    have := h3 j (by rw [← e]; exact hbe)
    rw [← e] at this; omega
  rw [hs]
  refine ⟨?_, ?_⟩
  · rw [triSt_atoms']
    exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hba, hbt⟩)
  · rw [triSt_cls, triCls_other T Q kp (fun j e => T.f_fresh j (by rw [← e]; exact hba))]; exact hbe

theorem BP.d3 (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s) (H : BHyp M₀ B C Un L γ η w κ)
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

theorem BP.step1RL (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ)
    (hs : HStep1RL C Un Fst L γ η w κ h h') : BP B h' := by
  cases hs with
  | old hs =>
    cases hs with
    | vine K R kp hs U hU hUK hUD hUJ hord =>
      exact hbp.vine K _ (fun b hb => by rw [← hUK]; exact H.sg U hU b hb) rfl
    | triple _ hs hs3 hall hF =>
      cases hs3 with
      | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes => exact hbp.cut hA H hc h3 rfl
  | d1 K hs U hU hUK hUD hUJ hord =>
    exact hbp.vineG K (fun b hb => by rw [← hUK]; exact H.sg U hU b hb) rfl

theorem BP.step2 (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ)
    (hs : HStep2C C L γ η w κ h h') : BP B h' := by
  cases hs with
  | mk T hel hs hT =>
    cases hs with
    | tri T' Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₁ h3 => exact hbp.tri hA H T' Q kp hcl h3 rfl

theorem BP.step3 (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ)
    (hs : HStep3C C L γ η w κ h h') : BP B h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes => exact hbp.cut hA H hc h3 rfl

theorem BP.step4 (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHyp M₀ B C Un L γ η w κ)
    (hs : HStep4 L w κ h h') : BP B h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc hε hβ hnz h3 => exact hbp.cut hA H hc h3 rfl

end bp

section qb
variable {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)}
  {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {B : Finset V} {h h' : HSt V D₀} {Rn : ℕ}

/-- The combined invariant: the ancestor relation, the class invariant at some index `≤ Rn`, and B-persistence. -/
def QB (M₀ : Molecule V D₀) (C : CollData M₀) (Rn : ℕ) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (B : Finset V)
    (h : HSt V D₀) : Prop :=
  AncRel M₀ h.s h.anc ∧ (∃ R', R' ≤ Rn ∧ InvL M₀ R' L γ η w κ h) ∧ BP B h

theorem AncRel.step1L (hs : HStep1L C L γ η w κ h h') (hA : AncRel M₀ h.s h.anc) : AncRel M₀ h'.s h'.anc := by
  cases hs with
  | old hs => exact hs.anc hA
  | low hs =>
    obtain ⟨K, hu, hl, hd2, htwin, hsg, rfl⟩ := hs.data
    exact hA.vinePostG K

theorem AncRel.stepD3 (hs : HStepD3 C L γ η w κ h h') (hA : AncRel M₀ h.s h.anc) : AncRel M₀ h'.s h'.anc := by
  obtain ⟨v, x₁, x₂, hDa, rfl⟩ := hs.data
  exact hA.betaSt v

theorem QB.init (hS : SubHypL Rn M₀) (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {B : Finset V} (hB : ∀ b ∈ B, b ∈ M₀.atoms) : QB M₀ C Rn L γ η w κ B (HSt.init M₀) :=
  ⟨AncRel.init M₀, ⟨Rn, le_rfl, InvL.init hS h0⟩, BP.init M₀ hB⟩

theorem QB.step1RL (H : BHyp M₀ B C Un L γ η w κ) (hs : HStep1RL C Un Fst L γ η w κ h h') (hq : QB M₀ C Rn L γ η w κ B h) :
    QB M₀ C Rn L γ η w κ B h' := by
  obtain ⟨ha, ⟨R', hR', hI⟩, hb⟩ := hq
  obtain ⟨R'', hR'', hI''⟩ := hI.step1L hs.toL
  exact ⟨AncRel.step1L hs.toL ha, ⟨R'', hR''.trans hR', hI''⟩, hb.step1RL ha H hs⟩

theorem QB.stepD3 (H : BHyp M₀ B C Un L γ η w κ) (hs : HStepD3 C L γ η w κ h h') (hq : QB M₀ C Rn L γ η w κ B h) :
    QB M₀ C Rn L γ η w κ B h' := by
  obtain ⟨ha, ⟨R', hR', hI⟩, hb⟩ := hq
  obtain ⟨R'', hR'', hI''⟩ := hI.stepD3' hs
  exact ⟨AncRel.stepD3 hs ha, ⟨R'', hR''.trans hR', hI''⟩, hb.d3 ha hI.rel H hs⟩

theorem QB.step2 (H : BHyp M₀ B C Un L γ η w κ) (hs : HStep2C C L γ η w κ h h') (hq : QB M₀ C Rn L γ η w κ B h) :
    QB M₀ C Rn L γ η w κ B h' := by
  obtain ⟨ha, ⟨R', hR', hI⟩, hb⟩ := hq
  exact ⟨hs.toHStep2.anc ha, ⟨R', hR', hI.step2 hs.toHStep2⟩, hb.step2 ha H hs⟩

theorem QB.step3 (H : BHyp M₀ B C Un L γ η w κ) (hs : HStep3C C L γ η w κ h h') (hq : QB M₀ C Rn L γ η w κ B h) :
    QB M₀ C Rn L γ η w κ B h' := by
  obtain ⟨ha, ⟨R', hR', hI⟩, hb⟩ := hq
  exact ⟨hs.toHStep3.anc ha, ⟨R', hR', hI.step3 hs.toHStep3⟩, hb.step3 ha H hs⟩

theorem QB.step4 (H : BHyp M₀ B C Un L γ η w κ) (hs : HStep4 L w κ h h') (hq : QB M₀ C Rn L γ η w κ B h) :
    QB M₀ C Rn L γ η w κ B h' := by
  obtain ⟨ha, ⟨R', hR', hI⟩, hb⟩ := hq
  exact ⟨hs.anc ha, ⟨R', hR', hI.step4 hs⟩, hb.step4 ha H hs⟩

theorem QB_reach4 (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (H : BHyp M₀ B C Un L γ η w κ) {h : HSt V D₀} (hr : Reach4L C Un Fst L γ η w κ h) :
    QB M₀ C Rn L γ η w κ B h := by
  obtain ⟨h₁, h₂, h₃, h₄, a, -, c, -, e, -, g, -, j⟩ := hr
  have q1 : QB M₀ C Rn L γ η w κ B h₁ :=
    rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.step1RL H hs) a (QB.init hS h0 H.sub)
  have q2 := rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.stepD3 H hs) c q1
  have q3 := rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.step2 H hs) e q2
  have q4 := rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.step3 H hs) g q3
  exact rtgH (P := fun x => QB M₀ C Rn L γ η w κ B x) (fun _ _ hs hq => hq.step4 H hs) j q4

end qb

end WaveTurbulence.FinalCountAsm
