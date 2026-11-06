/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.NonspecialCoefficient
public import WaveTurbulence.Foundations.RegularAsymptotics.CancelDraft.Props
public import WaveTurbulence.Foundations.Spine.RA1LW.AppAssembly

/-! # Complete classification and assembly of the actual limiting time coefficients -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open TTree Reg ClassJR Links Cancel Set

/-- The actual cancellation recursion has exactly the special-set leading
coefficients, including the corrected F61 sign, and vanishes otherwise. -/
theorem cplJ_eq_if_special (Q : RegCpl) (Z : Finset Addr) (hZ : Z ⊆ chosenSet Q.links)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    cplJ Z Q (0,[]) (1,[]) t s =
      if Q.dominant = true ∧ IsSpecialSet Q.links Z then
        (-1:ℂ)^Z.card*(Q.JB 0 t s : ℂ) else 0 := by
  classical
  by_cases hd : Q.dominant = true
  · by_cases hsp : IsSpecialSet Q.links Z
    · rw [ite_eq_left ⟨hd,hsp⟩,cplJ_eq_JB Z Q _ _ hd (chosen_nodup Q)
        (fun z hz _ => (isSpecialSet_iff Q Z).mp hsp z hz) t ht s hs]
      rw [show chosenSet (Q.linksAt (0,[]) (1,[])) = chosenSet Q.links from rfl,
        Finset.inter_eq_left.mpr hZ]
    · rw [ite_eq_right (fun h => hsp h.2)]
      have hn : ¬ ∀ z ∈ Z, z ∈ cplSpecial Q ((0:Fin 2),[]) (1,[]) :=
        fun h => hsp ((isSpecialSet_iff Q Z).mpr h)
      push Not at hn
      obtain ⟨z,hz,hnz⟩ := hn
      exact cplJ_eq_zero_of_nonspecial Z z hz Q _ _ (hZ hz) hnz t ht s hs
  · rw [ite_eq_right (fun h => hd h.1)]
    exact cplJ_eq_zero Z Q _ _ (Bool.eq_false_iff.mpr hd) t ht s hs

/-- The corrected B2 app is the literal finite sum with the actual
limiting time coefficients, with no assumed coefficient identity. -/
theorem assemble_couple_app_from_cplJ {d : ℕ}
    (Q : RegCpl) (δ : ℝ) (H : LGSpine.LeafProfiles 2 d) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (k : Mom d) :
    ((2:ℂ)⁻¹^Q.size*(δ:ℂ)^(Q.size/2)*zetaOfTrees ![1,-1] ![Q.trees.1,Q.trees.2]) *
      (∑ Z ∈ (chosenSet Q.links).powerset,
        (∏ z ∈ Z, (((((nodeSign ![1,-1] z : ℤˣ):ℤ):ℂ)*Real.pi*Complex.I))⁻¹) *
          cplJ Z Q (0,[]) (1,[]) t s * (LGSpine.LeafApp.cplMstar H Z Q (0,[]) (1,[]) k : ℂ)) =
        LGSpine.LeafApp.couple δ 0 H Q t s k :=
  assemble_couple_app_of_coefficient_identity Q δ 0 H t s k
    (fun Z => cplJ Z Q (0,[]) (1,[]) t s)
    (fun Z hZ => cplJ_eq_if_special Q Z hZ t ht s hs)

end WaveTurbulence.RA1Leafwise
