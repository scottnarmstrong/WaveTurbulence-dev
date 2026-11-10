/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.FinalCount.G3Cycle
public import WaveTurbulence.Foundations.FinalCount.G3BalS
public import WaveTurbulence.Foundations.FinalCount.G3RelRun
public import WaveTurbulence.Foundations.FinalCount.G3Flat
public import WaveTurbulence.Foundations.FinalCount.G3CompRun
/-! **FINALCOUNT-G3: runs with tame-atom erasures** (`HRunE`) and their invariants.

TARGET Remark `remtame` (L2152): a ZG tame atom `v₃` of Operation 2 or `v` of Operation 4 is either cut with a zero
gap (case (i), the model's `HStep2`/`HStep4` allow `pgap = 0` only through the cases below) or *erased* (case (ii),
`HStep5`).  `HRunE … t` is the run in which `HStep5` is interleaved with Steps 2 and 4; `t` counts the erasures.
The invariant `Good` holds with `R + 2 t` (each erasure raises `4V - 2E - 2(V_α + V_β)` by `4`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-! ### Balance of the steps -/

theorem Step1.balS {s s' : St.{u} V D₀} (h : Step1 L γ η w κ s s') (hB : BalS s) : BalS s' := by
  cases h with
  | vine K R kp hR hkp hu hl ga gb h3a h3b =>
    exact ((hB.cutSt K.cut_a _ _).cutSt K.cut_b _ _).delSt _ K.closed

theorem Step2.balS {s s' : St.{u} V D₀} (h : Step2 L γ η w κ s s') (hB : BalS s) : BalS s' := by
  cases h with
  | tri T Q kp hQ hkp hsg hsim hcl h3 =>
    have h1 := hB.cutSt T.cd1 .beta (if s.cls (T.t 0) = .eps then .beta else .ghost)
    have h2 := h1.cutSt T.cd2 .beta (if s.cls (T.t 1) = .eps then .beta else .ghost)
    have h3' := h2.cutSt T.cd3 .beta (if s.cls (T.t 2) = .eps then .beta else .ghost)
    have h4 := h3'.delSt T.TP T.pclosed
    have h5 := h4.withCls (triCls s T Q kp) (fun a ha hc => by
      have ha' : a ∈ T.m3.atoms.filter T.TP := ha
      rw [Finset.mem_filter] at ha'
      exact fun he => hc ((tri_cls_agree T Q kp a ha'.1 ha'.2).2.1.2 he))
    exact h5.delSt _ hcl

theorem Step3.balS {s s' : St.{u} V D₀} (h : Step3 L γ η w κ s s') (hB : BalS s) : BalS s' := by
  cases h with
  | cut v v₂ x₁ x₂ hcd R kp hR hkp hε hsg hsim h3 => exact hB.cutSt hcd _ _

theorem Step4.balS {s s' : St.{u} V D₀} (h : Step4 s s') (hB : BalS s) : BalS s' := by
  cases h with
  | cut v v₂ x₁ x₂ hcd hε hβ h3 => exact hB.cutSt hcd _ _

theorem BalS.init {R : ℕ} (hS : SubHyp R M₀) : BalS (St.init M₀) :=
  ⟨hS.bounds, fun a _ he _ => absurd rfl he⟩

/-! ### The combined invariant -/

/-- All invariants of a run whose erasures have total weight `t = ∑ (deg v - 2)`.  `Good R` holds while there is no erasure;
afterwards `Good R'` holds for some `R' ≤ R + t` (the deleted ghost neighbours of an erasure lower the index). -/
structure InvE (M₀ : Molecule V D₀) (R t : ℕ) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) :
    Prop where
  good0 : t = 0 → Good R h.s
  good : ∃ R', R' ≤ R + t ∧ Good R' h.s
  hrec : HInv L γ η w κ h
  gap : HGap L w κ h
  flat : t = 0 → Flat h.s
  comp : CompBeta h.s
  bal : BalS h.s
  rel : DartRel M₀ h.s

theorem InvE.init (hS : SubHyp R M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    InvE M₀ R 0 L γ η w κ (HSt.init M₀) where
  good0 := fun _ => ⟨hS.inv, St.init_clean M₀⟩
  good := ⟨R, le_refl _, hS.inv, St.init_clean M₀⟩
  hrec := HInv.init M₀
  gap := HGap.init h0
  flat := fun _ => Flat.init hS
  comp := hS.compBeta
  bal := BalS.init hS
  rel := DartRel.init M₀

variable {t : ℕ} {h h' : HSt V D₀}

theorem InvE.step1 (hs : HStep1 L γ η w κ h h') (hr : InvE M₀ R t L γ η w κ h) : InvE M₀ R t L γ η w κ h' where
  good0 := fun ht => hs.step.good (hr.good0 ht)
  good := by obtain ⟨R', hR', hg⟩ := hr.good; exact ⟨R', hR', hs.step.good hg⟩
  hrec := hs.inv hr.hrec
  gap := by obtain ⟨R', -, hg⟩ := hr.good; exact hs.gap hr.gap hg.1
  flat := fun ht => hs.step.flat (hr.flat ht)
  comp := by obtain ⟨R', -, hg⟩ := hr.good; exact hs.step.compBeta hg hr.comp
  bal := hs.step.balS hr.bal
  rel := hs.step.rel hr.rel

theorem InvE.step2 (hs : HStep2 L γ η w κ h h') (hr : InvE M₀ R t L γ η w κ h) : InvE M₀ R t L γ η w κ h' where
  good0 := fun ht => hs.step.good (hr.good0 ht)
  good := by obtain ⟨R', hR', hg⟩ := hr.good; exact ⟨R', hR', hs.step.good hg⟩
  hrec := hs.inv hr.hrec
  gap := by obtain ⟨R', -, hg⟩ := hr.good; exact hs.gap hr.gap hg.1
  flat := fun ht => hs.step.flat (hr.flat ht) (hr.good0 ht).2
  comp := by obtain ⟨R', -, hg⟩ := hr.good; exact hs.step.compBeta hg hr.comp
  bal := hs.step.balS hr.bal
  rel := hs.step.rel hr.rel

theorem InvE.step3 (hs : HStep3 L γ η w κ h h') (hr : InvE M₀ R t L γ η w κ h) : InvE M₀ R t L γ η w κ h' where
  good0 := fun ht => hs.step.good (hr.good0 ht)
  good := by obtain ⟨R', hR', hg⟩ := hr.good; exact ⟨R', hR', hs.step.good hg⟩
  hrec := hs.inv hr.hrec
  gap := by obtain ⟨R', -, hg⟩ := hr.good; exact hs.gap hr.gap hg.1
  flat := fun ht => hs.step.flat (hr.flat ht)
  comp := by obtain ⟨R', -, hg⟩ := hr.good; exact hs.step.compBeta hg hr.comp
  bal := hs.step.balS hr.bal
  rel := hs.step.rel hr.rel

theorem InvE.step4 (hs : HStep4 L w κ h h') (hr : InvE M₀ R t L γ η w κ h) : InvE M₀ R t L γ η w κ h' where
  good0 := fun ht => hs.step.good (hr.good0 ht)
  good := by obtain ⟨R', hR', hg⟩ := hr.good; exact ⟨R', hR', hs.step.good hg⟩
  hrec := hs.inv hr.hrec
  gap := by obtain ⟨R', -, hg⟩ := hr.good; exact hs.gap hr.gap hg.1
  flat := fun ht => hs.step.flat (hr.flat ht)
  comp := hs.step.compBeta hr.comp
  bal := hs.step.balS hr.bal
  rel := hs.step.rel hr.rel

end WaveTurbulence.FinalCountG3
