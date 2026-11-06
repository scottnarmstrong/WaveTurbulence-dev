/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.Gate61Helpers

/-!
# The momentum factors read their profiles only at embedded leaves

`ℳ*` and `𝒩*` (`LeafApp.cplMstar`, `LeafApp.chainNstar`) evaluate the profiles only at the positions of trivial
sub-couples, which are leaves of any garden in which the code is embedded:

* `cplMstar_congr`, `chainNstar_congr`: profiles agreeing on the embedded leaves among the code's nodes give the
  same momentum factor;
* `LeafApp.couple_congr`, `LeafApp.tree_congr`: the same for the single-layer leading terms.
-/

@[expose] public section

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

section Congr

variable {d w : ℕ} {G : Garden w} {H H' : LeafProfiles w d} {Z : Finset (Fin w × Path)}

mutual

theorem cplMstar_congr : ∀ (Q : RegCpl) (a b : Fin w × Path), Embeds G Q a b →
    (∀ z ∈ cplNodes Q a b, z.2 ∈ (G.tree z.1).leaves → H z = H' z) →
    LeafApp.cplMstar H Z Q a b = LeafApp.cplMstar H' Z Q a b
  | .triv, a, b, hE, h => by
    have hl : a.2 ∈ (G.tree a.1).leaves :=
      hE.leaf_of_mem ((mem_pairEndpoints_iff _ _).2 ⟨(a, b), by simp [RegCpl.pairsAt], Or.inl rfl⟩)
    simp only [LeafApp.cplMstar]
    exact h a (mem_cplNodes_triv.2 (Or.inl rfl)) hl
  | .type1 c Q₁ Q₂ Q₃, a, b, hE, h => by
    obtain ⟨h1, h2, h3⟩ := hE.type1
    have e1 := cplMstar_congr Q₁ _ _ h1 fun z hz hl =>
      h z (mem_cplNodes_type1.2 (Or.inr (Or.inr (Or.inl hz)))) hl
    have e2 := cplMstar_congr Q₂ _ _ h2 fun z hz hl =>
      h z (mem_cplNodes_type1.2 (Or.inr (Or.inr (Or.inr (Or.inl hz))))) hl
    have e3 := cplMstar_congr Q₃ _ _ h3 fun z hz hl =>
      h z (mem_cplNodes_type1.2 (Or.inr (Or.inr (Or.inr (Or.inr hz))))) hl
    simp only [LeafApp.cplMstar, e1, e2, e3]
  | .type2 Xp Xm Qlp, a, b, hE, h => by
    obtain ⟨Cp, Cm, Elp⟩ := hE.type2
    have e1 := cplMstar_congr Qlp _ _ Elp fun z hz hl =>
      h z (mem_cplNodes_type2.2 (Or.inr (Or.inr hz))) hl
    have e2 := chainNstar_congr Xp 1 a _ Cp fun z hz hl => h z (mem_cplNodes_type2.2 (Or.inl hz)) hl
    have e3 := chainNstar_congr Xm (-1) b _ Cm fun z hz hl =>
      h z (mem_cplNodes_type2.2 (Or.inr (Or.inl hz))) hl
    simp only [LeafApp.cplMstar, e1, e2, e3]

theorem chainNstar_congr : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (h₀ : TTree), ChainEmb G X ζ a h₀ →
    (∀ z ∈ chainNodesSet X ζ a, z.2 ∈ (G.tree z.1).leaves → H z = H' z) →
    LeafApp.chainNstar H Z X ζ a = LeafApp.chainNstar H' Z X ζ a
  | .nil, _, _, _, _, _ => rfl
  | .pair m Qr Qg inner rest, ζ, a, h₀, hC, h => by
    obtain ⟨hr, hg, hi, hs⟩ := hC.parts
    have eR : (if slotSign ζ m.red.1 = 1 then
          LeafApp.cplMstar H Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        else LeafApp.cplMstar H Z Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) =
        (if slotSign ζ m.red.1 = 1 then
          LeafApp.cplMstar H' Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        else LeafApp.cplMstar H' Z Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
          (addrExt a [m.red.1])) := by
      by_cases hσ : slotSign ζ m.red.1 = 1
      · rw [ite_eq_left hσ] at hr
        rw [ite_eq_left hσ, ite_eq_left hσ]
        exact cplMstar_congr Qr _ _ hr fun z hz hl => h z (mem_chainNodesSet_red (by
          unfold orientedNodes
          rw [ite_eq_left hσ]
          exact hz)) hl
      · rw [ite_eq_right hσ] at hr
        rw [ite_eq_right hσ, ite_eq_right hσ]
        exact cplMstar_congr Qr _ _ hr fun z hz hl => h z (mem_chainNodesSet_red (by
          unfold orientedNodes
          rw [ite_eq_right hσ]
          exact hz)) hl
    have eG : (if slotSign ζ m.green.1 = 1 then
          LeafApp.cplMstar H Z Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        else LeafApp.cplMstar H Z Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
          (addrExt a [m.green.1])) =
        (if slotSign ζ m.green.1 = 1 then
          LeafApp.cplMstar H' Z Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        else LeafApp.cplMstar H' Z Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
          (addrExt a [m.green.1])) := by
      by_cases hσ : slotSign ζ m.green.1 = 1
      · rw [ite_eq_left hσ] at hg
        rw [ite_eq_left hσ, ite_eq_left hσ]
        exact cplMstar_congr Qg _ _ hg fun z hz hl => h z (mem_chainNodesSet_green (by
          unfold orientedNodes
          rw [ite_eq_left hσ]
          exact hz)) hl
      · rw [ite_eq_right hσ] at hg
        rw [ite_eq_right hσ, ite_eq_right hσ]
        exact cplMstar_congr Qg _ _ hg fun z hz hl => h z (mem_chainNodesSet_green (by
          unfold orientedNodes
          rw [ite_eq_right hσ]
          exact hz)) hl
    have eI := chainNstar_congr inner _ _ _ hi fun z hz hl => h z (mem_chainNodesSet_inner hz) hl
    have eS := chainNstar_congr rest _ _ _ hs fun z hz hl => h z (mem_chainNodesSet_rest hz) hl
    simp only [LeafApp.chainNstar, eR, eG, eI, eS]

end

end Congr

theorem LeafApp.couple_congr {d : ℕ} {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (δ r : ℝ)
    {H H' : LeafProfiles 2 d}
    (h : ∀ z ∈ cplNodes Q ((0 : Fin 2), []) ((1 : Fin 2), []), z.2 ∈ (G.tree z.1).leaves → H z = H' z)
    (t s : ℝ) (k : Mom d) : LeafApp.couple δ r H Q t s k = LeafApp.couple δ r H' Q t s k := by
  have e : ∀ Z, LeafApp.cplMstar H Z Q ((0 : Fin 2), []) ((1 : Fin 2), []) =
      LeafApp.cplMstar H' Z Q ((0 : Fin 2), []) ((1 : Fin 2), []) := fun Z =>
    cplMstar_congr Q _ _ (Embeds.of_decodes hQ) h
  unfold LeafApp.couple
  simp only [e]

theorem LeafApp.tree_congr {d : ℕ} {G : Garden 1} {X : RegChain} {ζ : ℤˣ} {h₀ : TTree}
    (hX : ChainEmb G X ζ ((0 : Fin 1), []) h₀) (δ r : ℝ) {H H' : LeafProfiles 1 d}
    (h : ∀ z ∈ chainNodesSet X ζ ((0 : Fin 1), []), z.2 ∈ (G.tree z.1).leaves → H z = H' z)
    (t s : ℝ) (k : Mom d) : LeafApp.tree δ r H X ζ t s k = LeafApp.tree δ r H' X ζ t s k := by
  have e : ∀ Z, LeafApp.chainNstar H Z X ζ ((0 : Fin 1), []) = LeafApp.chainNstar H' Z X ζ ((0 : Fin 1), []) :=
    fun Z => chainNstar_congr X _ _ _ hX h
  unfold LeafApp.tree
  simp only [e]

end WaveTurbulence.PL234
