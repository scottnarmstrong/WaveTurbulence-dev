/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase2D
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3UStep
public import WaveTurbulence.Foundations.FinalCount.AsmPhase3b
/-! **Ghost assembly, Phase 1 (A): the survivors of an Operation-1 step and of a cut** (design: `CHAIN-DESIGN.md`).

`vineSurvMap`: `h' = h.vinePostL K R kp` (cuts of the two joints, removal of the object); every atom of `h'` other than
the fresh joints `fa`, `fb` keeps its darts, class and record. `cutSurvMap`: `h' = h.cut3Post v v₂ x₁ x₂ R kp`; every atom
other than `v`, `v₂`. The new atoms carry the records of their cuts (`gvec_vine_fa/fb`, `gvec_cut_v/v₂`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {d : ℕ}

section cut
variable {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} {v v₂ : V} {x₁ x₂ : D}

theorem cut_atom_of_ne (y : D) (hy : (M.cut v v₂ x₁ x₂).atom y ≠ v₂) : (M.cut v v₂ x₁ x₂).atom y = M.atom y := by
  change (if M.atom y = v ∧ y ≠ x₁ ∧ y ≠ x₂ then v₂ else M.atom y) ≠ v₂ at hy
  change (if M.atom y = v ∧ y ≠ x₁ ∧ y ≠ x₂ then v₂ else M.atom y) = M.atom y
  split_ifs at hy ⊢ with hc
  · exact absurd rfl hy
  · rfl

theorem cut_atom_eq_new (y : D) (hv₂ : v₂ ∉ M.atoms) (hy : (M.cut v v₂ x₁ x₂).atom y = v₂) : M.atom y = v := by
  change (if M.atom y = v ∧ y ≠ x₁ ∧ y ≠ x₂ then v₂ else M.atom y) = v₂ at hy
  split_ifs at hy with hc
  · exact hc.1
  · exact absurd (hy ▸ M.atom_mem y) hv₂

theorem cut_dartsAt_other' {a : V} (hav : a ≠ v) (ha2 : a ≠ v₂) : (M.cut v v₂ x₁ x₂).dartsAt a = M.dartsAt a := by
  ext y
  simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]
  constructor
  · intro hy; rw [← hy, cut_atom_of_ne y (by rw [hy]; exact ha2)]
  · intro hy
    change (if M.atom y = v ∧ y ≠ x₁ ∧ y ≠ x₂ then v₂ else M.atom y) = a
    rw [ite_eq_right (fun hc => hav (hy ▸ hc.1))]; exact hy

theorem cut_common (hv₂ : v₂ ∉ M.atoms) (a b : D) (hab : (M.cut v v₂ x₁ x₂).atom a = (M.cut v v₂ x₁ x₂).atom b) :
    M.atom a = M.atom b := by
  by_cases ha : (M.cut v v₂ x₁ x₂).atom a = v₂
  · rw [cut_atom_eq_new a hv₂ ha, cut_atom_eq_new b hv₂ (hab ▸ ha)]
  · rw [← cut_atom_of_ne a ha, ← cut_atom_of_ne b (hab ▸ ha), hab]

end cut

variable {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

/-! ### The Operation-1 step -/

section vine
variable (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) (R : ℝ) (kp : ℕ)

/-- The survivors of an Operation-1 step: the atoms of the post state other than the fresh joints. -/
def vineSurv : Set V := {a | a ∈ (h.vinePostL K R kp).s.M.atoms ∧ a ≠ K.fa ∧ a ≠ K.fb}

theorem upper_mem : K.C.upper ∈ h.s.M.atoms := Step1.objectAtoms_sub K.C K.a_mem
theorem lower_mem : K.C.lower ∈ h.s.M.atoms := Step1.objectAtoms_sub K.C K.b_mem
theorem fa_notMem : K.fa ∉ h.s.M.atoms := K.cut_a.2.1
theorem fa_ne_fb : K.fa ≠ K.fb := fun e => K.cut_b.2.1 (by rw [← e]; exact Finset.mem_insert_self _ _)
theorem fb_notMem : K.fb ∉ h.s.M.atoms := fun hm => K.cut_b.2.1 (Finset.mem_insert_of_mem hm)
theorem fa_ne_atom {a : V} (ha : a ∈ h.s.M.atoms) : a ≠ K.fa := fun e => fa_notMem h K (e ▸ ha)
theorem fb_ne_atom {a : V} (ha : a ∈ h.s.M.atoms) : a ≠ K.fb := fun e => fb_notMem h K (e ▸ ha)

theorem vine_atom_of_ne (y : h.s.D) (h1 : K.cutMol.atom y ≠ K.fa) (h2 : K.cutMol.atom y ≠ K.fb) :
    K.cutMol.atom y = h.s.M.atom y := by
  have e2 : K.cutMol.atom y = (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).atom y := cut_atom_of_ne y h2
  rw [e2] at h1 ⊢
  exact cut_atom_of_ne y h1

theorem vine_common (a b : h.s.D) (hab : K.cutMol.atom a = K.cutMol.atom b) : h.s.M.atom a = h.s.M.atom b :=
  cut_common (fa_notMem h K) a b (cut_common K.cut_b.2.1 a b hab)

theorem vine_dartsAt_other {a : V} (hu : a ≠ K.C.upper) (hl : a ≠ K.C.lower) (hfa : a ≠ K.fa) (hfb : a ≠ K.fb) :
    K.cutMol.dartsAt a = h.s.M.dartsAt a := by
  unfold Step1.VineCut.cutMol
  rw [cut_dartsAt_other' hl hfb, cut_dartsAt_other' hu hfa]

/-- **The survivor map of an Operation-1 step.** -/
noncomputable def vineSurvMap : SurvMap h (h.vinePostL K R kp) (vineSurv h K R kp) where
  ι := fun x => x.1
  down_eq := fun _ => rfl
  out_eq := fun _ => rfl
  mate_eq := fun _ => rfl
  atom_eq := fun x hx => (vine_atom_of_ne h K x.1 hx.2.1 hx.2.2).symm
  common := fun a b hab => vine_common h K a.1 b.1 hab
  mem := fun a ha _ => by
    have h1 : a ∈ K.cutMol.atoms := (Finset.mem_filter.1 ha.1).1
    change a ∈ insert K.fb (insert K.fa h.s.M.atoms) at h1
    simp only [Finset.mem_insert] at h1
    rcases h1 with e | e | e
    · exact absurd e ha.2.2
    · exact absurd e ha.2.1
    · exact e
  deg_eq := fun a ha => by
    have hnot : a ∉ K.C.atoms := (Finset.mem_filter.1 ha.1).2
    have hu : a ≠ K.C.upper := fun e => hnot (e ▸ K.a_mem)
    have hl : a ≠ K.C.lower := fun e => hnot (e ▸ K.b_mem)
    have e1 : (h.vinePostL K R kp).s.M.deg a = K.cutMol.deg a :=
      restrictP_deg K.cutMol (fun a => a ∉ K.C.atoms) K.closed hnot
    rw [e1]
    unfold Molecule.deg
    rw [vine_dartsAt_other h K hu hl ha.2.1 ha.2.2]
  cls_eq := fun a ha => by
    have hnot : a ∉ K.C.atoms := (Finset.mem_filter.1 ha.1).2
    have hu : a ≠ K.C.upper := fun e => hnot (e ▸ K.a_mem)
    have hl : a ≠ K.C.lower := fun e => hnot (e ▸ K.b_mem)
    show Function.update (Function.update (Function.update (Function.update h.s.cls K.C.upper _) K.fa _) K.C.lower _)
      K.fb _ a = h.s.cls a
    rw [Function.update_of_ne ha.2.2, Function.update_of_ne hl, Function.update_of_ne ha.2.1, Function.update_of_ne hu]
  crec_eq := fun a ha => by
    have hnot : a ∉ K.C.atoms := (Finset.mem_filter.1 ha.1).2
    have hu : a ≠ K.C.upper := fun e => hnot (e ▸ K.a_mem)
    have hl : a ≠ K.C.lower := fun e => hnot (e ▸ K.b_mem)
    show Function.update (Function.update (Function.update (Function.update h.crec K.C.upper _) K.fa _) K.C.lower _)
      K.fb _ a = h.crec a
    rw [Function.update_of_ne ha.2.2, Function.update_of_ne hl, Function.update_of_ne ha.2.1, Function.update_of_ne hu]

theorem gvec_vine_fa (L : ℝ) (w : Mom d) (k0 : D₀ → (Fin d → ℤ)) :
    gvec (h.vinePostL K R kp) L w k0 K.fa = pgap L w k0 (h.s.pr K.x₁ K.x₂) := by
  have e : (h.vinePostL K R kp).crec K.fa = some (h.s.pr K.x₁ K.x₂, h.alive) := by
    show Function.update (Function.update (Function.update (Function.update h.crec K.C.upper _) K.fa _) K.C.lower _)
      K.fb _ K.fa = _
    rw [Function.update_of_ne (fa_ne_fb h K), Function.update_of_ne (fa_ne_atom h K (lower_mem h K)).symm,
      Function.update_self]
  unfold gvec; rw [e]

theorem gvec_vine_fb (L : ℝ) (w : Mom d) (k0 : D₀ → (Fin d → ℤ)) :
    gvec (h.vinePostL K R kp) L w k0 K.fb = pgap L w k0 (h.s.pr K.y₁ K.y₂) := by
  have e : (h.vinePostL K R kp).crec K.fb = some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive) := by
    show Function.update (Function.update (Function.update (Function.update h.crec K.C.upper _) K.fa _) K.C.lower _)
      K.fb _ K.fb = _
    rw [Function.update_self]
  unfold gvec; rw [e]

/-- A critical atom of the post state that is not a survivor is `fa` or `fb`. -/
theorem vine_critA_cases {L γ η : ℝ} {x : V} (hx : IsCritA L γ η (h.vinePostL K R kp) x)
    (hX : x ∉ vineSurv h K R kp) : x = K.fa ∨ x = K.fb := by
  by_contra hn
  push Not at hn
  exact hX ⟨hx.1, hn.1, hn.2⟩

end vine

/-! ### A cut (Steps 3–4 and the triple cuts of Phase 1) -/

section cut3
variable (h : HSt V D₀) (v v₂ : V) (x₁ x₂ : h.s.D) (R : ℝ) (kp : ℕ)

/-- The survivors of a cut: the atoms of the post state other than `v`, `v₂`. -/
def cutSurv : Set V := {a | a ∈ (h.cut3Post v v₂ x₁ x₂ R kp).s.M.atoms ∧ a ≠ v ∧ a ≠ v₂}

/-- **The survivor map of a cut.** -/
noncomputable def cutSurvMap (hv₂ : v₂ ∉ h.s.M.atoms) : SurvMap h (h.cut3Post v v₂ x₁ x₂ R kp) (cutSurv h v v₂ x₁ x₂ R kp) where
  ι := fun x => x
  down_eq := fun _ => rfl
  out_eq := fun _ => rfl
  mate_eq := fun _ => rfl
  atom_eq := fun x hx => (cut_atom_of_ne (M := h.s.M) (v := v) (v₂ := v₂) (x₁ := x₁) (x₂ := x₂) x hx.2.2).symm
  common := fun a b hab => cut_common (M := h.s.M) (v := v) (x₁ := x₁) (x₂ := x₂) hv₂ a b hab
  mem := fun a ha _ => by
    have h1 : a ∈ insert v₂ h.s.M.atoms := ha.1
    rcases Finset.mem_insert.1 h1 with e | e
    · exact absurd e ha.2.2
    · exact e
  deg_eq := fun a ha => by
    show (h.s.M.cut v v₂ x₁ x₂).deg a = h.s.M.deg a
    unfold Molecule.deg
    rw [cut_dartsAt_other' ha.2.1 ha.2.2]
  cls_eq := fun a ha => by
    show Function.update (Function.update h.s.cls v _) v₂ _ a = h.s.cls a
    rw [Function.update_of_ne ha.2.2, Function.update_of_ne ha.2.1]
  crec_eq := fun a ha => by
    show Function.update (Function.update h.crec v _) v₂ _ a = h.crec a
    rw [Function.update_of_ne ha.2.2, Function.update_of_ne ha.2.1]

theorem gvec_cut_v₂ (L : ℝ) (w : Mom d) (k0 : D₀ → (Fin d → ℤ)) :
    gvec (h.cut3Post v v₂ x₁ x₂ R kp) L w k0 v₂ = pgap L w k0 (h.s.pr x₁ x₂) := by
  have e : (h.cut3Post v v₂ x₁ x₂ R kp).crec v₂ = some (h.s.pr x₁ x₂, h.alive) := by
    show Function.update (Function.update h.crec v _) v₂ _ v₂ = _
    rw [Function.update_self]
  unfold gvec; rw [e]

theorem gvec_cut_v (hne : v ≠ v₂) (L : ℝ) (w : Mom d) (k0 : D₀ → (Fin d → ℤ)) :
    gvec (h.cut3Post v v₂ x₁ x₂ R kp) L w k0 v = pgap L w k0 (h.s.pr x₁ x₂) := by
  have e : (h.cut3Post v v₂ x₁ x₂ R kp).crec v = some (h.s.pr x₁ x₂, h.alive) := by
    show Function.update (Function.update h.crec v _) v₂ _ v = _
    rw [Function.update_of_ne hne, Function.update_self]
  unfold gvec; rw [e]

theorem cut_critA_cases {L γ η : ℝ} {x : V} (hx : IsCritA L γ η (h.cut3Post v v₂ x₁ x₂ R kp) x)
    (hX : x ∉ cutSurv h v v₂ x₁ x₂ R kp) : x = v ∨ x = v₂ := by
  by_contra hn
  push Not at hn
  exact hX ⟨hx.1, hn.1, hn.2⟩

end cut3

end WaveTurbulence.GammaLow.FinalCount.Ghost
