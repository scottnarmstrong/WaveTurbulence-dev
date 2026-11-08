/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKChain.Reach
public import WaveTurbulence.Foundations.FinalCount.LowChain27

/-! # C1b2 MK-CHAIN (6): B-persistence along the survivor run

Copy-thread of main's LowChain27 (`BP.step1RL`, `QB.step1RL`, `QB_reach4`) for the survivor Step 1 `HStep1RLE`. The
loop atoms `B` avoid every `CollectedF` object and every survivor (`BHypE`; both are SG objects, and no SG object
contains a loop atom). A survivor removal cuts `K` with `(E i).atoms = K.C.atoms.image h.anc` (`SurvCut`); an atom of
`B` is a present `ε`-atom, hence its own ancestor, so it is not in `K.C.atoms`. The later phases use main's
`QB.stepD3/2/3/4` through `BHypE.toBHyp` (main's `BHyp` with `Un := univ`: then main's `Collected` is `𝒞₁` only). -/

@[expose] public section
open WaveTurbulence.Induct
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

/-- The data of B-persistence with survivors (main's `BHyp` on `CollectedF`, plus the survivors). -/
structure BHypE {m : ℕ} (M₀ : Molecule V D₀) (B : Finset V) (C : CollDataMK M₀)
    (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d)
    (κ : D₀ → (Fin d → ℤ)) : Prop where
  sub : ∀ b ∈ B, b ∈ M₀.atoms
  deg : ∀ b ∈ B, M₀.deg b ≤ 2
  zg : ∀ b ∈ B, ∀ x y, M₀.atom x = b → M₀.atom y = b → κ x = κ y
  sg : ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ b ∈ B, b ∉ U.atoms
  sgE : ∀ i, ∀ b ∈ B, b ∉ (E i).atoms

section bp
variable {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
  {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {B : Finset V}
  {h h' : HSt V D₀} {Rn : ℕ}

/-- Main's `BHyp` with no unselected-pool objects (`Un := univ`, so `C2Can` is empty). -/
theorem BHypE.toBHyp (H : BHypE M₀ B C Un E L γ η w κ) :
    BHyp M₀ B C.toCollData (fun _ => Set.univ) L γ η w κ where
  sub := H.sub
  deg := H.deg
  zg := H.zg
  sg := fun U hU b hb => by
    rcases hU with hU | hU
    · exact H.sg U (Or.inl hU) b hb
    · exact absurd (Set.mem_univ U) hU.1.1.2

/-- An atom of `B` is not in the cut of a survivor removal. -/
theorem survCut_notMem (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHypE M₀ B C Un E L γ η w κ) {K : VineCut h.s.M}
    {i : Fin m} (hc : SurvCut E i h K) : ∀ b ∈ B, b ∉ K.C.atoms := by
  intro b hb hbK
  obtain ⟨hba, hbe⟩ := hbp b hb
  have hab : h.anc b = b := hA.eps b hba hbe
  have : b ∈ (E i).atoms := by rw [hc.1]; exact Finset.mem_image.2 ⟨b, hbK, hab⟩
  exact H.sgE i b hb this

theorem BP.step1RLE (hbp : BP B h) (hA : AncRel M₀ h.s h.anc) (H : BHypE M₀ B C Un E L γ η w κ)
    (hs : HStep1RLE C Un Fst E L γ η w κ h h') : BP B h' := by
  cases hs with
  | vine K R kp hs U hU hUK hUD hUJ hord =>
    exact hbp.vine K _ (fun b hb => by rw [← hUK]; exact H.sg U hU b hb) rfl
  | d1 K hs U hU hUK hUD hUJ hord =>
    exact hbp.vineG K (fun b hb => by rw [← hUK]; exact H.sg U hU b hb) rfl
  | triple _ hs hs3 hall hallE hF =>
    cases hs3 with
    | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes => exact hbp.cut hA H.toBHyp hc h3 rfl
  | survVine K R kp i hs hc ho => exact hbp.vine K _ (survCut_notMem hbp hA H hc) rfl
  | survD1 K i hs hc ho => exact hbp.vineG K (survCut_notMem hbp hA H hc) rfl
  | survRC K i hs hc ho => exact hbp.vineG K (survCut_notMem hbp hA H hc) rfl

/-- The ancestor relation along a Step-1 step with re-cuts. -/
theorem AncRel.step1LE {C : CollData M₀} (hs : HStep1LE C L γ η w κ h h') (hA : AncRel M₀ h.s h.anc) :
    AncRel M₀ h'.s h'.anc := by
  cases hs with
  | base hs => exact AncRel.step1L hs hA
  | recut hs =>
    obtain ⟨K, -, -, -, -, -, -, -, rfl⟩ := HStepRC.data hs
    exact hA.vinePostG K

theorem QB.step1RLE (H : BHypE M₀ B C Un E L γ η w κ) (hs : HStep1RLE C Un Fst E L γ η w κ h h')
    (hq : QB M₀ C.toCollData Rn L γ η w κ B h) : QB M₀ C.toCollData Rn L γ η w κ B h' := by
  obtain ⟨ha, ⟨R', hR', hI⟩, hb⟩ := hq
  obtain ⟨R'', hR'', hI''⟩ := InvL.step1LE (HStep1RLE.toLE hs) hI
  exact ⟨AncRel.step1LE (HStep1RLE.toLE hs) ha, ⟨R'', hR''.trans hR', hI''⟩, BP.step1RLE hb ha H hs⟩

/-- **B-persistence along the survivor run** (main's `QB_reach4`). -/
theorem QB_reach4E (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (H : BHypE M₀ B C Un E L γ η w κ) {h : HSt V D₀} (hr : Reach4LE C Un Fst E L γ η w κ h) :
    QB M₀ C.toCollData Rn L γ η w κ B h := by
  obtain ⟨h₁, h₂, h₃, h₄, a, -, c, -, e, -, g, -, j⟩ := hr
  have q1 : QB M₀ C.toCollData Rn L γ η w κ B h₁ :=
    rtgH (P := fun x => QB M₀ C.toCollData Rn L γ η w κ B x) (fun _ _ hs hq => QB.step1RLE H hs hq) a
      (QB.init hS h0 H.sub)
  have q2 := rtgH (P := fun x => QB M₀ C.toCollData Rn L γ η w κ B x) (fun _ _ hs hq => QB.stepD3 H.toBHyp hs hq) c q1
  have q3 := rtgH (P := fun x => QB M₀ C.toCollData Rn L γ η w κ B x) (fun _ _ hs hq => QB.step2 H.toBHyp hs hq) e q2
  have q4 := rtgH (P := fun x => QB M₀ C.toCollData Rn L γ η w κ B x) (fun _ _ hs hq => QB.step3 H.toBHyp hs hq) g q3
  exact rtgH (P := fun x => QB M₀ C.toCollData Rn L γ η w κ B x) (fun _ _ hs hq => QB.step4 H.toBHyp hs hq) j q4

end bp

end WaveTurbulence.Flower.FinalMKChain
