/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.GateParts

/-! # D3 PROT-PIN: the `penTerm` tree slice (empty prefix or nonempty interior)

`X = appendChain Xp (cpair m Qr Qg inner)` (the last pair, `exists_last_pair`): a nonempty interior is (P5)
(`pen_final5`), an empty interior with an empty prefix is (P4) with the root pinned (`pen_final_root`). The remaining
case (P4) with a nonempty prefix is a separate slice. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem eq_nil_of_lonePath {X : RegChain} (h : X.lonePath = []) : X = .nil := by
  cases X with
  | nil => rfl
  | pair m Qr Qg inner rest => simp [RegChain.lonePath] at h

/-- The selector of the slice: every last-pair decomposition has a nonempty interior or an empty prefix. -/
def selPenNoPrefix (X : RegChain) : Prop :=
  ∀ (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain),
    X = appendChain Xp (cpair m Qr Qg inner) → inner.lonePath ≠ [] ∨ Xp = .nil

/-- **penTerm, trees, empty prefix or nonempty interior.** -/
theorem cfgU_pen_tree {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgU θ Cr (fun w _ X cfg => w = 1 ∧ cfg = .penTerm ∧ selPenNoPrefix X) := by
  obtain ⟨Cr1, h1, hf1⟩ := pen_final_root hθ0
  obtain ⟨Cr2, h2, hf2⟩ := pen_final5 hθ0 hθ1
  refine ⟨Cr1 + Cr2, by linarith, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hη CL hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb hsel s t hps hst
    htp q' hq' S ω cω hpres F M hM Fu Mu hMu ind hind hind1 H B hH b₀ c₀
  obtain ⟨rfl, rfl, hX⟩ := hsel
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hθc := pieceLoss_eta hη
  have hc : 31 * (P.d : ℝ) + 6 ≤ 31 * P.d + 6 := le_rfl
  have hlen : 2 ≤ X.lonePath.length := hval
  have hXne : X ≠ .nil := by rintro rfl; simp [RegChain.lonePath] at hlen
  obtain ⟨Xp, m, Qr, Qg, inner, rfl⟩ := exists_last_pair X hXne
  obtain ⟨LGp, LGi, LGr, LGg, D⟩ := CutTermData.exists_of_wf LG Xp m Qr Qg inner hsh.2.1 hsh.1
  by_cases hin : inner.lonePath ≠ []
  · exact hf2 K hθc hc hCL hC11 hLOE (big2_mono hCL (by linarith) hL0 hbig2) hp hn D hin hsh hsz hamb hps hst htp
      q' S ω cω hpres F M hM Fu Mu hMu ind hind H B hH b₀ c₀
  · have hinn : inner = .nil := eq_nil_of_lonePath (not_not.mp hin)
    subst hinn
    have hXp : Xp = .nil := (hX Xp m Qr Qg .nil rfl).resolve_left hin
    subst hXp
    exact hf1 K hθc hc hCL hC11 hLOE (big_mono hCL (by linarith) K.hδ hL0 hbig) hp hn D hsh hsz hamb hps hst htp
      q' S ω cω hpres F M hM Fu Mu hMu ind hind H B hH b₀ c₀

end WaveTurbulence.Flower.ProtPin
