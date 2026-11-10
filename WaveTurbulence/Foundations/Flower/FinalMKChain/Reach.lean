/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Rel
public import WaveTurbulence.Foundations.FinalCount.LowChain15
public import WaveTurbulence.Foundations.FinalCount.GV14

/-! # C1b2 MK-CHAIN (1): the LOW reach relations after the survivor Step 1

Copy-thread of main's LowChain3 (`ReachD3`, `Reach2L–4L`, `Reach4L.toRunLC`), LowChain4 (`invL_reach2–4`), LowChain8 and
LowChain42 (`Reach*L.d3info`), LowChain15 (`hext*L`) and GV14 (`HRunLC`): the first stage is C1b1's survivor Step 1
(`Reach1LE ∧ Stuck1E`, over `CollDataMK`), the later phases are main's steps on `C.toCollData`. The run `HRunLCE` is
main's `HRunLC` with C1a's `HStep1LE` and the `rem` clause on the forbidden pool `CollectedF` (C0's sweep, R164) and on
the survivors. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKChain
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.Flower.FinalMKPhase1 WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section defs
variable {M₀ : Molecule V D₀} {m : ℕ} (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
  (Fst : Set (Object M₀)) (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d)

/-- The D3 phase after the survivor Step 1 (main's `ReachD3`). -/
def ReachD3E (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∃ h₁, Reach1LE C Un Fst E L γ η w κ h₁ ∧ Stuck1E C L γ η w Un E κ h₁ ∧
    Relation.ReflTransGen (HStepD3 C.toCollData L γ η w κ) h₁ h

/-- Phase 2 after the survivor Step 1 (main's `Reach2L`). -/
def Reach2LE (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∃ h₁ h₂, Reach1LE C Un Fst E L γ η w κ h₁ ∧ Stuck1E C L γ η w Un E κ h₁ ∧
    Relation.ReflTransGen (HStepD3 C.toCollData L γ η w κ) h₁ h₂ ∧
    NoD3 C.toCollData L w κ h₂ ∧ Relation.ReflTransGen (HStep2C C.toCollData L γ η w κ) h₂ h

/-- Phase 3 after the survivor Step 1 (main's `Reach3L`). -/
def Reach3LE (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∃ h₁ h₂ h₃, Reach1LE C Un Fst E L γ η w κ h₁ ∧ Stuck1E C L γ η w Un E κ h₁ ∧
    Relation.ReflTransGen (HStepD3 C.toCollData L γ η w κ) h₁ h₂ ∧
    NoD3 C.toCollData L w κ h₂ ∧ Relation.ReflTransGen (HStep2C C.toCollData L γ η w κ) h₂ h₃ ∧
    NoEligibleTriangle C.toCollData L γ η w κ h₃ ∧ Relation.ReflTransGen (HStep3C C.toCollData L γ η w κ) h₃ h

/-- Phase 4 after the survivor Step 1 (main's `Reach4L`). -/
def Reach4LE (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∃ h₁ h₂ h₃ h₄, Reach1LE C Un Fst E L γ η w κ h₁ ∧ Stuck1E C L γ η w Un E κ h₁ ∧
    Relation.ReflTransGen (HStepD3 C.toCollData L γ η w κ) h₁ h₂ ∧
    NoD3 C.toCollData L w κ h₂ ∧ Relation.ReflTransGen (HStep2C C.toCollData L γ η w κ) h₂ h₃ ∧
    NoEligibleTriangle C.toCollData L γ η w κ h₃ ∧ Relation.ReflTransGen (HStep3C C.toCollData L γ η w κ) h₃ h₄ ∧
    NoSGLeft L γ η w κ (HSt.init M₀).s h₄.s ∧ Relation.ReflTransGen (HStep4 L w κ) h₄ h

end defs

/-- **The LOW run with re-cuts and the forbidden pool** (main's `HRunLC`, GV14): C1a's `HStep1LE` in Step 1, and at the end
of Step 1 every `CollectedF` object and every survivor is dartless. -/
def HRunLCE {m : ℕ} (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (M₀ : Molecule V D₀) (hf : HSt V D₀)
    (C : CollDataMK M₀) (E : Fin m → Object M₀) (Unsel : Set (Object M₀)) : Prop :=
  ∃ h₁ h₂ h₃ h₄ : HSt V D₀,
    Relation.ReflTransGen (HStep1LE C.toCollData L γ η w κ) (HSt.init M₀) h₁ ∧
    NoTripleCut C.toCollData L γ η w κ h₁ ∧
    Relation.ReflTransGen (HStepD3 C.toCollData L γ η w κ) h₁ h₂ ∧ NoD3 C.toCollData L w κ h₂ ∧
    Relation.ReflTransGen (HStep2C C.toCollData L γ η w κ) h₂ h₃ ∧ NoEligibleTriangle C.toCollData L γ η w κ h₃ ∧
    Relation.ReflTransGen (HStep3C C.toCollData L γ η w κ) h₃ h₄ ∧ NoSGLeft L γ η w κ (HSt.init M₀).s h₄.s ∧
    Relation.ReflTransGen (HStep4 L w κ) h₄ hf ∧ NoBetaCut L w κ hf.s ∧
    (∀ U, CollectedF C Unsel L γ η w κ U → ∀ x : h₁.s.D, ¬ U.ContainsDart (h₁.s.down x)) ∧
    (∀ i, ∀ x : h₁.s.D, ¬ (E i).ContainsDart (h₁.s.down x))

section run
variable {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀} {E : Fin m → Object M₀} {Unsel : Set (Object M₀)}
  {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {hf : HSt V D₀}

theorem HRunLCE.toHRunLE (h : HRunLCE L γ η w κ M₀ hf C E Unsel) :
    HRunLE C.toCollData L γ η w κ (HSt.init M₀) hf := by
  obtain ⟨h₁, h₂, h₃, h₄, a1, n1, a2, n2, a3, n3, a4, n4, a5, n5, -⟩ := h
  exact ⟨h₁, h₂, h₃, h₄, a1, n1, a2, n2, a3, n3, a4, n4, a5, n5⟩

/-- At the final state every `CollectedF` object and every survivor is dartless (main's `HRunLC.rem`). -/
theorem HRunLCE.rem (h : HRunLCE L γ η w κ M₀ hf C E Unsel) :
    (∀ U, CollectedF C Unsel L γ η w κ U → ∀ x : hf.s.D, ¬ U.ContainsDart (hf.s.down x)) ∧
    (∀ i, ∀ x : hf.s.D, ¬ (E i).ContainsDart (hf.s.down x)) := by
  obtain ⟨h₁, h₂, h₃, h₄, a1, n1, a2, n2, a3, n3, a4, n4, a5, n5, hrem, hremE⟩ := h
  have s5 : St.Sub hf.s h₄.s := rtg_sub (fun _ _ h => h.sub) a5
  have s4 : St.Sub h₄.s h₃.s := rtg_sub (fun _ _ h => h.toHStep3.sub) a4
  have s3 : St.Sub h₃.s h₂.s := rtg_sub (fun _ _ h => h.toHStep2.sub) a3
  have s2 : St.Sub h₂.s h₁.s := rtg_sub (fun _ _ h => h.sub) a2
  have key : ∀ U : Object M₀, (∀ x : h₁.s.D, ¬ U.ContainsDart (h₁.s.down x)) → ∀ x : hf.s.D,
      ¬ U.ContainsDart (hf.s.down x) := by
    intro U hU x hx
    obtain ⟨x', hx'⟩ := (s5.trans (s4.trans (s3.trans s2))) ⟨x, rfl⟩
    exact hU x' (by rw [hx']; exact hx)
  exact ⟨fun U hU => key U (hrem U hU), fun i => key (E i) (hremE i)⟩

end run

section reach
variable {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
  {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

theorem ReachD3E.ext {h h' : HSt V D₀} (hr : ReachD3E C Un Fst E L γ η w κ h)
    (hs : HStepD3 C.toCollData L γ η w κ h h') : ReachD3E C Un Fst E L γ η w κ h' := by
  obtain ⟨h₁, a, b, c⟩ := hr; exact ⟨h₁, a, b, c.tail hs⟩

theorem Reach2LE.ext {h h' : HSt V D₀} (hr : Reach2LE C Un Fst E L γ η w κ h)
    (hs : HStep2C C.toCollData L γ η w κ h h') : Reach2LE C Un Fst E L γ η w κ h' := by
  obtain ⟨h₁, h₂, a, b, c, d', e⟩ := hr; exact ⟨h₁, h₂, a, b, c, d', e.tail hs⟩

theorem Reach3LE.ext {h h' : HSt V D₀} (hr : Reach3LE C Un Fst E L γ η w κ h)
    (hs : HStep3C C.toCollData L γ η w κ h h') : Reach3LE C Un Fst E L γ η w κ h' := by
  obtain ⟨h₁, h₂, h₃, a, b, c, d', e, f, g⟩ := hr; exact ⟨h₁, h₂, h₃, a, b, c, d', e, f, g.tail hs⟩

theorem Reach4LE.ext {h h' : HSt V D₀} (hr : Reach4LE C Un Fst E L γ η w κ h)
    (hs : HStep4 L w κ h h') : Reach4LE C Un Fst E L γ η w κ h' := by
  obtain ⟨h₁, h₂, h₃, h₄, a, b, c, d', e, f, g, i, j⟩ := hr
  exact ⟨h₁, h₂, h₃, h₄, a, b, c, d', e, f, g, i, j.tail hs⟩

theorem Reach1LE.toD3 {h : HSt V D₀} (hr : Reach1LE C Un Fst E L γ η w κ h) (hs : Stuck1E C L γ η w Un E κ h) :
    ReachD3E C Un Fst E L γ η w κ h := ⟨h, hr, hs, Relation.ReflTransGen.refl⟩

theorem ReachD3E.to2 {h : HSt V D₀} (hr : ReachD3E C Un Fst E L γ η w κ h) (hs : NoD3 C.toCollData L w κ h) :
    Reach2LE C Un Fst E L γ η w κ h := by
  obtain ⟨h₁, a, b, c⟩ := hr; exact ⟨h₁, h, a, b, c, hs, Relation.ReflTransGen.refl⟩

theorem Reach2LE.to3 {h : HSt V D₀} (hr : Reach2LE C Un Fst E L γ η w κ h)
    (hs : NoEligibleTriangle C.toCollData L γ η w κ h) : Reach3LE C Un Fst E L γ η w κ h := by
  obtain ⟨h₁, h₂, a, b, c, d', e⟩ := hr; exact ⟨h₁, h₂, h, a, b, c, d', e, hs, Relation.ReflTransGen.refl⟩

theorem Reach3LE.to4 {h : HSt V D₀} (hr : Reach3LE C Un Fst E L γ η w κ h)
    (hs : NoSGLeft L γ η w κ (HSt.init M₀).s h.s) : Reach4LE C Un Fst E L γ η w κ h := by
  obtain ⟨h₁, h₂, h₃, a, b, c, d', e, f, g⟩ := hr
  exact ⟨h₁, h₂, h₃, h, a, b, c, d', e, f, g, hs, Relation.ReflTransGen.refl⟩

/-- **The run `HRunLCE` from `Reach4LE` at a state where Step 4 stops** (main's `Reach4L.toRunLC`). -/
theorem Reach4LE.toRunLCE {h : HSt V D₀} (hr : Reach4LE C Un Fst E L γ η w κ h) (hn : NoBetaCut L w κ h.s) :
    HRunLCE L γ η w κ M₀ h C E (Un κ) := by
  obtain ⟨h₁, h₂, h₃, h₄, a, ⟨b1, b2, b3⟩, c, d', e, f, g, i, j⟩ := hr
  exact ⟨h₁, h₂, h₃, h₄, Reach1LE.toLE a, b1, c, d', e, f, g, i, j, hn, fun U hU x => b2 U hU x, fun k x => b3 k x⟩

end reach

section inv
variable {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
  {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {Rn : ℕ}

theorem invL_reach2E (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach2LE C Un Fst E L γ η w κ h) : ∃ R', R' ≤ Rn ∧ InvL M₀ R' L γ η w κ h := by
  obtain ⟨h₁, h₂, a, -, c, -, e⟩ := hr
  exact invL_chain (fun a b hs R' hI => ⟨R', le_rfl, hI.step2 hs.toHStep2⟩) e
    (invL_chain (fun a b hs R' hI => hI.stepD3' hs) c (invL_reach1E hS h0 a))

theorem invL_reach3E (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach3LE C Un Fst E L γ η w κ h) : ∃ R', R' ≤ Rn ∧ InvL M₀ R' L γ η w κ h := by
  obtain ⟨h₁, h₂, h₃, a, -, c, -, e, -, g⟩ := hr
  exact invL_chain (fun a b hs R' hI => ⟨R', le_rfl, hI.step3 hs.toHStep3⟩) g
    (invL_chain (fun a b hs R' hI => ⟨R', le_rfl, hI.step2 hs.toHStep2⟩) e
      (invL_chain (fun a b hs R' hI => hI.stepD3' hs) c (invL_reach1E hS h0 a)))

theorem d3info_auxE (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h₁ h₂ : HSt V D₀}
    (a : Reach1LE C Un Fst E L γ η w κ h₁) (c : Relation.ReflTransGen (HStepD3 C.toCollData L γ η w κ) h₁ h₂) :
    AncRel M₀ h₂.s h₂.anc ∧ DartRel M₀ h₂.s := by
  have p1 : RunAux M₀ C.toCollData h₁ := reach1LE_aux a
  have p2 : RunAux M₀ C.toCollData h₂ :=
    rtgH (P := fun h => RunAux M₀ C.toCollData h) (fun _ _ hs hp => hs.aux hp) c p1
  obtain ⟨R', -, hI⟩ := invL_chain (fun _ _ hs R' hI => hI.stepD3' hs) c (invL_reach1E hS h0 a)
  exact ⟨p2.2.1, hI.rel⟩

theorem Reach2LE.d3info (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach2LE C Un Fst E L γ η w κ h) :
    ∃ h₂, NoD3 C.toCollData L w κ h₂ ∧ AncRel M₀ h₂.s h₂.anc ∧ DartRel M₀ h₂.s ∧ EpsLe h₂.s h.s := by
  obtain ⟨h₁, h₂, a, -, c, n, e⟩ := hr
  obtain ⟨hA, hD⟩ := d3info_auxE hS h0 a c
  refine ⟨h₂, n, hA, hD, ?_⟩
  exact rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.toHStep2.step.epsLe) e (EpsLe.refl _)

theorem Reach3LE.d3info (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach3LE C Un Fst E L γ η w κ h) :
    ∃ h₂, NoD3 C.toCollData L w κ h₂ ∧ AncRel M₀ h₂.s h₂.anc ∧ DartRel M₀ h₂.s ∧ EpsLe h₂.s h.s := by
  obtain ⟨h₁, h₂, h₃, a, -, c, n, e, -, g⟩ := hr
  obtain ⟨hA, hD⟩ := d3info_auxE hS h0 a c
  refine ⟨h₂, n, hA, hD, ?_⟩
  have e2 : EpsLe h₂.s h₃.s :=
    rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.toHStep2.step.epsLe) e (EpsLe.refl _)
  exact rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.toHStep3.step.epsLe) g e2

theorem Reach4LE.d3info (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach4LE C Un Fst E L γ η w κ h) :
    ∃ h₂, NoD3 C.toCollData L w κ h₂ ∧ AncRel M₀ h₂.s h₂.anc ∧ DartRel M₀ h₂.s ∧ EpsLe h₂.s h.s := by
  obtain ⟨h₁, h₂, h₃, h₄, a, -, c, n, e, -, g, -, j⟩ := hr
  obtain ⟨hA, hD⟩ := d3info_auxE hS h0 a c
  refine ⟨h₂, n, hA, hD, ?_⟩
  have e2 : EpsLe h₂.s h₃.s :=
    rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.toHStep2.step.epsLe) e (EpsLe.refl _)
  have e3 : EpsLe h₂.s h₄.s :=
    rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.toHStep3.step.epsLe) g e2
  exact rtgH (P := fun x => EpsLe h₂.s x.s) (fun _ _ hs he => he.trans hs.step.epsLe) j e3

end inv

section ext
variable {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
  {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d}

theorem hext4LE [Infinite V] {A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} {v : V} {x₁ x₂ : h.s.D}
    (hn : Node4 h v x₁ x₂) (k : D₀ → (Fin d → ℤ)) (hk : k ∈ cls4 L w h A x₁ x₂)
    (hr : Reach4LE C Un Fst E L γ η w k h) : Reach4LE C Un Fst E L γ η w k (post4 h v x₁ x₂) :=
  hr.ext (UStep4.hstep (uStep4_node (L := L) (w := w) (A := A) hn) hk)

theorem hext3LE [Infinite V] {A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} {v : V} {x₁ x₂ : h.s.D} {z : ℤ} {b : Bool}
    {a : V} {sg : Bool} (hn : Node3 L γ η h v x₁ x₂ z b a sg) (hdes : Desig C.toCollData (h.anc v) (h.s.pr x₁ x₂))
    (k : D₀ → (Fin d → ℤ)) (hk : k ∈ cls3 L γ η w h A x₁ x₂ z b a sg) (hr : Reach3LE C Un Fst E L γ η w k h) :
    Reach3LE C Un Fst E L γ η w k (post3 h v x₁ x₂ z b) :=
  hr.ext (hstep3C_node hn hdes hk)

theorem hext2LE [Infinite V] {A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} {n : T2 h} (hn : Node2 L γ η h n)
    (hdes : ∀ j : Fin 3, Desig C.toCollData (h.anc (n.1 j)) (h.s.pr (n.2.1 j) (n.2.2.1 j)))
    (k : D₀ → (Fin d → ℤ)) (hk : k ∈ cls2 L γ η w h A n) (hr : Reach2LE C Un Fst E L γ η w k h) :
    Reach2LE C Un Fst E L γ η w k (post2 L γ η h n) := by
  obtain ⟨hcl0, ht, ha, hb, hf, -⟩ := Classical.choose_spec hn
  change (triOf hn).t = _ at ht
  change (triOf hn).a = _ at ha
  change (triOf hn).b = _ at hb
  have hel : Eligible C.toCollData L γ η w k h (triOf hn) := by
    refine ⟨fun j => ?_, ?_, fun j => ?_⟩
    · rw [ha, hb]; exact hk.2.1 j
    · rw [ha, hb]; exact hk.2.2.2.1
    · rw [ht, ha, hb]; exact hdes j
  have hs2 : HStep2 L γ η w k h (post2 L γ η h n) := by
    have := UStep2.hstep (uStep2_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn) hk
    exact this
  refine hr.ext (HStep2C.mk (triOf hn) hel hs2 ⟨Q2 n, kp2 n, triOf_cl hn, ?_⟩)
  rw [post2_eq hn]; rfl

theorem hextD3LE {A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} {v : V} {x₁ x₂ : h.s.D} (hn : D3Data h v x₁ x₂)
    (hdes : Desig C.toCollData (h.anc v) (h.s.pr x₁ x₂)) (k : D₀ → (Fin d → ℤ)) (hk : k ∈ clsD3 L w h A x₁ x₂)
    (hr : ReachD3E C Un Fst E L γ η w k h) : ReachD3E C Un Fst E L γ η w k (h.betaPost v x₁ x₂) :=
  hr.ext (UStepD3.hstep (uStepD3_node (C := C.toCollData) (L := L) (γ := γ) (η := η) (w := w) (A := A) hn hdes) hk)

end ext

end WaveTurbulence.Flower.FinalMKChain
