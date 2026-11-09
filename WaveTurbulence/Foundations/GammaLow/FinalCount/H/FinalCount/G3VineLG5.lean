/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineLG5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3VineLG5`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: `vineLG`, part 5: `no_SG`.**  The ancestor object `P` of a final vine component is not SG. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R R₀ : ℕ} {Tm : V → Prop}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

theorem no_SG (hS : SubHyp R₀ M₀) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hC : Prop95ConclAt L γ η w κ R hf Tm) (hT : TameFree hf Tm a₀) (hrec : HInv L γ η w κ hf) (hdp : DPInv hf)
    {C : CollData M₀} {Unsel : Set (Src.Object Src.γL M₀)} (obl : SubproOblG C L γ η w κ) (hU : C.UnselOK L γ η w κ Unsel)
    (hrem1 : ∀ i, ∀ x : hf.s.D, ¬ (C.collection i).ContainsDart (hf.s.down x))
    (hrem2 : ∀ U ∈ C.C2Can L γ η w κ Unsel, ∀ x : hf.s.D, ¬ U.ContainsDart (hf.s.down x))
    (hdes : DesRecN C hf) (J : FinalJoints hf a₀ j₁ j₂)
    (P : Src.Object Src.γL M₀) (hPat : P.atoms = AncGroup hf a₀) (hPup : P.upper = hf.anc j₁) (hPlo : P.lower = hf.anc j₂)
    (hPa : ∀ x : hf.s.D, hf.s.M.SameComponent a₀ (hf.s.M.atom x) → P.ContainsDart (hf.s.down x))
    (hPb : ∀ z, P.ContainsDart z → ∃ x : hf.s.D, hf.s.M.SameComponent a₀ (hf.s.M.atom x) ∧ hf.s.down x = z) :
    ¬ P.HasGapKind L γ η w κ .SG := by
  intro hSG
  have hnl := hC.noloop
  by_cases hOut : C.Outside P
  swap
  · obtain ⟨i, hi⟩ : ∃ i, P.atoms ⊆ (C.collection i).atoms := by
      by_contra h'; push Not at h'; exact hOut h'
    obtain ⟨x, hx⟩ := final_dart_contained J hA hD hnl (C.collection i) (hPat ▸ hi)
    exact hrem1 i x hx
  by_cases hdis : Disjoint P.atoms C.hinges
  · have hInP : C.InP L γ η w κ P := ⟨hSG, hOut, hdis, obl.contained P hSG hOut hdis⟩
    rcases C.coverCan Unsel hInP with hmem | ⟨U, hUC, hsub⟩
    · rcases (hU.dv P hmem).2 with ⟨U, hU2, hsub⟩ | ⟨A, a, b, -, hVA, hVB, hAB, U, hU2, hUA, hvc⟩
      · obtain ⟨x, hx⟩ := final_dart_contained J hA hD hnl U (hPat ▸ hsub)
        exact hrem2 U hU2 x hx
      · exact residual_unsel hS J hA hD hnl P.atoms hPat A a b hVA hVB hAB U hUA hvc (hrem2 U hU2)
    · obtain ⟨x, hx⟩ := final_dart_contained J hA hD hnl U (hPat ▸ hsub)
      exact hrem2 U hUC x hx
  · obtain ⟨v, hvH, hvP, hcase⟩ := obl.crossing P hSG hOut hdis
    obtain ⟨f0, s0, hf0, hs0, hsg0⟩ := obl.hingeSG v hvH
    rcases hcase with ⟨h1, h2⟩ | ⟨hjoint, x, y, hx, hy, hxor⟩
    · exact hinge_interior hA hD hC hT J (hPat ▸ hvP) (hPup ▸ h1) (hPlo ▸ h2) hsg0.1 hsg0.2
    · have hfx : f0 = x := Option.some.inj (hf0.symm.trans hx)
      have hsy : s0 = y := Option.some.inj (hs0.symm.trans hy)
      subst hfx hsy
      -- the joint `j` with `anc j = v`
      obtain ⟨j, hjc, hjv⟩ : ∃ j, (j = j₁ ∨ j = j₂) ∧ v = hf.anc j := by
        rcases hjoint with h | h
        · exact ⟨j₁, Or.inl rfl, by rw [← hPup, h]⟩
        · exact ⟨j₂, Or.inr rfl, by rw [← hPlo, h]⟩
      have hjm : j ∈ hf.s.M.atoms := by rcases hjc with rfl | rfl; exacts [J.m1, J.m2]
      have hjd : hf.s.M.deg j = 2 := by rcases hjc with rfl | rfl; exacts [J.d1, J.d2]
      obtain ⟨p, vis, hr⟩ := record_of_nonEps hrec hC hjm hjd.le
      have hdpj := hdp.ok j hjm p vis hr
      obtain ⟨f, s, hf1, hs1, hset⟩ := hdes j p vis hr (hjv ▸ hvH)
      rw [← hjv] at hf1 hs1
      have hff : f = f0 := Option.some.inj (hf1.symm.trans hf0)
      have hss : s = s0 := Option.some.inj (hs1.symm.trans hs0)
      subst hff hss
      exact hinge_joint_xor hA hD hS J hPa hPb hjc hdpj hset (fun e => hsg0.1.2.2.2 (by rw [e])) hjd (hjv ▸ hsg0.1.1) (hjv ▸ hsg0.1.2.1) hxor

end WaveTurbulence.GammaLow.FinalCount.H
