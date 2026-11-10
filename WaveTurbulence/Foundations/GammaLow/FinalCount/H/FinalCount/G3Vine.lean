/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Vine`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3**: degrees of the atoms of a vine-like object (Step 1) and `Inv` for Step 1. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {D₀ : Type*}

/-- The interior atoms of a vine-like object have degree `4`. -/
theorem vine_interior_deg {M : Molecule V D} (K : Step1.VineCut Src.γL M)
    (hb : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) {a : V} (ha : a ∈ K.C.atoms)
    (h1 : a ≠ K.C.upper) (h2 : a ≠ K.C.lower) : M.deg a = 4 := by
  have hle : M.deg a ≤ 4 := deg_le_four M (hb a (Step1.objectAtoms_sub K.C ha))
  have h4 : 4 ≤ M.deg a := by
    rcases K.C.shape with h | R
    · obtain ⟨_, _, _, _, _, _, _, _, hdeg, _⟩ := h.1
      have := hdeg a ha h1 h2
      have h5 : M.degIn K.C.atoms a ≤ M.deg a := Finset.card_filter_le _ _
      omega
    · obtain ⟨_, _, _, _, _, _, _, _, hdeg, _⟩ := R.adjoint.1
      have := hdeg a ha h1 h2
      have h5 := erase_degIn_le M R.added K.C.atoms a
      omega
  omega


theorem Inv.vineStL {s : St.{u} V D₀} {R : ℕ} (hI : Inv R s) (K : Step1.VineCut Src.γL s.M) (c : Cls) (hc : c.IsAB)
    (hu : s.cls K.C.upper = .eps) (hl : s.cls K.C.lower = .eps)
    (h3a : 3 ≤ s.M.deg K.C.upper) (h3b : 3 ≤ s.M.deg K.C.lower) :
    Inv R (vineSt s K c) := by
  have hc2 := Cls.base_eq_two hc
  have hce := Cls.ne_eps_of_isAB hc
  have hcg := Cls.ne_ghost_of_isAB hc
  have hI1 : Inv R (s.cutSt K.C.upper K.fa K.x₁ K.x₂ c c) :=
    hI.cutSt K.cut_a c c (by rw [hu, hc2]; rfl) hce hce hcg (fun h => absurd h hcg) (fun _ => h3a)
  have hlow : (s.cutSt K.C.upper K.fa K.x₁ K.x₂ c c).cls K.C.lower = .eps := by
    show Function.update (Function.update s.cls K.C.upper c) K.fa c K.C.lower = _
    rw [Function.update_of_ne K.fa_ne_b.symm, Function.update_of_ne K.ab_ne.symm]; exact hl
  have hI2 : Inv R ((s.cutSt K.C.upper K.fa K.x₁ K.x₂ c c).cutSt K.C.lower K.fb K.y₁ K.y₂ c c) :=
    hI1.cutSt K.cut_b c c (by rw [hlow, hc2]; rfl) hce hce hcg (fun h => absurd h hcg)
      (fun _ => by
        show 3 ≤ (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower
        rw [cut_deg_other K.cut_a K.ab_ne.symm K.fa_ne_b.symm]; exact h3b)
  refine hI2.delSt _ K.closed ?_
  intro a ha hna
  have haC : a ∈ K.C.atoms := not_not.mp hna
  have haM : a ∈ s.M.atoms := Step1.objectAtoms_sub K.C haC
  have hfa : a ≠ K.fa := fun e => K.fa_fresh (e ▸ haM)
  have hfb : a ≠ K.fb := fun e => K.fb_fresh (e ▸ haM)
  show (Function.update (Function.update (Function.update (Function.update s.cls K.C.upper c) K.fa c)
      K.C.lower c) K.fb c a).base = ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg a
  have hdeg1 : (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.upper = 2 := cut_deg_v s.M K.cut_a
  have hdeg1' : ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg K.C.lower = 2 :=
    cut_deg_v _ K.cut_b
  have e_ua : K.C.upper ≠ K.fa := fun e => K.fa_fresh (e ▸ K.a_atom)
  have e_ub : K.C.upper ≠ K.fb := K.fb_ne_a.symm
  have e_ul : K.C.upper ≠ K.C.lower := K.ab_ne
  have e_lb : K.C.lower ≠ K.fb := fun e => K.fb_fresh (e ▸ K.b_atom)
  have e_la : K.C.lower ≠ K.fa := K.fa_ne_b.symm
  by_cases h1 : a = K.C.upper
  · rw [h1, Function.update_of_ne e_ub, Function.update_of_ne e_ul, Function.update_of_ne e_ua,
      Function.update_self, hc2]
    have : ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg K.C.upper = 2 := by
      rw [cut_deg_other K.cut_b e_ul e_ub]; exact hdeg1
    rw [this]; rfl
  · by_cases h2 : a = K.C.lower
    · rw [h2, Function.update_of_ne e_lb, Function.update_self, hc2, hdeg1']; rfl
    · rw [Function.update_of_ne hfb, Function.update_of_ne h2, Function.update_of_ne hfa,
        Function.update_of_ne h1, cut_deg_other K.cut_b h2 hfb, cut_deg_other K.cut_a h1 hfa]
      have h4 := vine_interior_deg K hI.bounds haC h1 h2
      have hce' : s.cls a = .eps := by
        by_contra hne
        have := (hI.ab a haM hne).1; omega
      rw [hce', h4]; rfl

alias _root_.WaveTurbulence.FinalCountG3.Inv.vineStL := _root_.WaveTurbulence.GammaLow.FinalCount.H.Inv.vineStL
end WaveTurbulence.GammaLow.FinalCount.H
