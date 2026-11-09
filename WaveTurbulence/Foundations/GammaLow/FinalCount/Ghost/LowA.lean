/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase1A
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL5
public import WaveTurbulence.Foundations.FinalCount.GL2
/-! **Ghost assembly, LOW chain (A): the degree-2 steps keep the bank** (design: `CHAIN-DESIGN.md`).

The LOW run has two extra steps: Step D1 (Operation 1 at an object with a degree-`2` joint, post state
`h.vinePostGL K`: the fresh joints get the class `jcls` — a ghost or `β`) and Step D3 (`h.betaPost v x₁ x₂`: the
degree-`2` `ε`-atom `v` becomes a `β`-atom, the molecule is unchanged). Neither creates a critical `α`-atom, so with
the survivor maps `vineGSurvMap`, `betaSurvMap` the bank does not grow: `bank_vinePostGL_le`, `bank_betaPost_le`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-! ### Step D3 -/

section d3
variable (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D)

/-- **The survivor map of a Step D3**: every atom other than `v`. -/
noncomputable def betaSurvMap : SurvMap h (h.betaPost v x₁ x₂) {a | a ≠ v} where
  ι := fun x => x
  down_eq := fun _ => rfl
  out_eq := fun _ => rfl
  mate_eq := fun _ => rfl
  atom_eq := fun _ _ => rfl
  common := fun _ _ hab => hab
  mem := fun _ _ hx => hx
  deg_eq := fun _ _ => rfl
  cls_eq := fun a ha => by
    show Function.update h.s.cls v .beta a = h.s.cls a
    exact Function.update_of_ne ha _ _
  crec_eq := fun a ha => by
    show Function.update h.crec v _ a = h.crec a
    exact Function.update_of_ne ha _ _

/-- **A Step D3 does not increase the bank.** -/
theorem bank_betaPost_le {L γ η : ℝ} {w : Mom d} {A B : Set (D₀ → (Fin d → ℤ))} (hBA : B ⊆ A) :
    bank L γ η w (h.betaPost v x₁ x₂) B ≤ bank L γ η w h A := by
  have hF := betaSurvMap h v x₁ x₂
  have hnc : ¬ IsCritA L γ η (h.betaPost v x₁ x₂) v := by
    rintro ⟨-, -, R, hR, -⟩
    have e : (h.betaPost v x₁ x₂).s.cls v = .beta := by
      show Function.update h.s.cls v .beta v = .beta
      exact Function.update_self _ _ _
    rw [e] at hR; cases hR
  have := bank_step (L := L) (γ := γ) (η := η) (w := w) hF hBA (critSet L γ η h) ∅ (fun x y hE hx hy =>
    Or.inl ⟨mem_critSet.2 (hF.critA hx hE.2.1), mem_critSet.2 (hF.critA hy hE.2.2.1)⟩) (by
      intro x y hE hXY
      exfalso
      rcases hXY with hx | hy
      · have : x = v := by simpa using hx
        exact hnc (this ▸ hE.2.1)
      · have : y = v := by simpa using hy
        exact hnc (this ▸ hE.2.2.1))
  rw [Finset.card_empty, add_zero] at this
  exact this

end d3

/-! ### Step D1 -/

section d1
variable (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M)

/-- The survivors of a Step D1: the atoms of the post state other than the fresh joints. -/
def vineGSurv : Set V := {a | a ∈ (h.vinePostGL K).s.M.atoms ∧ a ≠ K.fa ∧ a ≠ K.fb}

/-- **The survivor map of a Step D1.** -/
noncomputable def vineGSurvMap : SurvMap h (h.vinePostGL K) (vineGSurv h K) where
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
    have hk : H.VineKeep K a := (Finset.mem_filter.1 ha.1).2
    have hnot : a ∉ K.C.atoms := hk.1
    have hu : a ≠ K.C.upper := fun e => hnot (e ▸ K.a_mem)
    have hl : a ≠ K.C.lower := fun e => hnot (e ▸ K.b_mem)
    have e1 : (h.vinePostGL K).s.M.deg a = K.cutMol.deg a :=
      restrictP_deg K.cutMol (H.VineKeep K) (H.VineKeep.closed K) hk
    rw [e1]
    unfold Molecule.deg
    rw [vine_dartsAt_other h K hu hl ha.2.1 ha.2.2]
  cls_eq := fun a ha => by
    have hnot : a ∉ K.C.atoms := (Finset.mem_filter.1 ha.1).2.1
    have hu : a ≠ K.C.upper := fun e => hnot (e ▸ K.a_mem)
    have hl : a ≠ K.C.lower := fun e => hnot (e ▸ K.b_mem)
    show Function.update (Function.update (Function.update (Function.update h.s.cls K.C.upper _) K.fa _) K.C.lower _)
      K.fb _ a = h.s.cls a
    rw [Function.update_of_ne ha.2.2, Function.update_of_ne hl, Function.update_of_ne ha.2.1, Function.update_of_ne hu]
  crec_eq := fun a ha => by
    have hnot : a ∉ K.C.atoms := (Finset.mem_filter.1 ha.1).2.1
    have hu : a ≠ K.C.upper := fun e => hnot (e ▸ K.a_mem)
    have hl : a ≠ K.C.lower := fun e => hnot (e ▸ K.b_mem)
    show Function.update (Function.update (Function.update (Function.update h.crec K.C.upper _) K.fa _) K.C.lower _)
      K.fb _ a = h.crec a
    rw [Function.update_of_ne ha.2.2, Function.update_of_ne hl, Function.update_of_ne ha.2.1, Function.update_of_ne hu]

/-- **A Step D1 does not increase the bank**: the fresh joints are ghosts or `β`-atoms. -/
theorem bank_vinePostGL_le {L γ η : ℝ} {w : Mom d} {A B : Set (D₀ → (Fin d → ℤ))} (hBA : B ⊆ A) :
    bank L γ η w (h.vinePostGL K) B ≤ bank L γ η w h A := by
  have hF := vineGSurvMap h K
  have hnc : ∀ x, IsCritA L γ η (h.vinePostGL K) x → x ∉ vineGSurv h K → False := by
    rintro x ⟨hxm, -, R, hR, -⟩ hX
    have hfab : x = K.fa ∨ x = K.fb := by
      by_contra hn
      push Not at hn
      exact hX ⟨hxm, hn.1, hn.2⟩
    have hcl : (h.vinePostGL K).s.cls x = jcls h.s.M K.C.upper ∨ (h.vinePostGL K).s.cls x = jcls h.s.M K.C.lower := by
      rcases hfab with rfl | rfl
      · left
        show Function.update (Function.update (Function.update (Function.update h.s.cls K.C.upper _) K.fa _)
          K.C.lower _) K.fb _ K.fa = _
        rw [Function.update_of_ne (fa_ne_fb h K), Function.update_of_ne (fa_ne_atom h K (lower_mem h K)).symm,
          Function.update_self]
      · right
        show Function.update (Function.update (Function.update (Function.update h.s.cls K.C.upper _) K.fa _)
          K.C.lower _) K.fb _ K.fb = _
        rw [Function.update_self]
    have hj : ∀ v, jcls h.s.M v ≠ Cls.alpha R 0 := by
      intro v; unfold jcls; split_ifs <;> exact fun e => by cases e
    rcases hcl with e | e
    · rw [e] at hR; exact hj _ hR
    · rw [e] at hR; exact hj _ hR
  have := bank_step (L := L) (γ := γ) (η := η) (w := w) hF hBA (critSet L γ η h) ∅ (fun x y hE hx hy =>
    Or.inl ⟨mem_critSet.2 (hF.critA hx hE.2.1), mem_critSet.2 (hF.critA hy hE.2.2.1)⟩) (by
      intro x y hE hXY
      exfalso
      rcases hXY with hx | hy
      · exact hnc x hE.2.1 hx
      · exact hnc y hE.2.2.1 hy)
  rw [Finset.card_empty, add_zero] at this
  exact this

end d1

end WaveTurbulence.GammaLow.FinalCount.Ghost
