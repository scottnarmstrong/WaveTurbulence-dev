/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceMomentumHomogeneity

/-! # Homogeneity of the leafwise leading terms in each leaf profile (RA1-LEAFWISE)

If `H z = β z • H' z` at the first endpoint `z` of every pair of a code, then the literal recursive
`cplMstar H` (`chainNstar H`) is `∏_pairs β` times `cplMstar H'` (`chainNstar H'`). The proof is the recursion of
the definition together with the unconditional homogeneity of `resIntegral`, `pvResonantIntegral`
(`SourceMomentumHomogeneity`), which are defined by a quotient formula, not by `limUnder`. -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp TTree LGSpine LeafApp

variable {d w : ℕ}

/-- The product of the scale factors over the first endpoints of a list of pairs. -/
@[expose] def pairScale (β : Fin w × Path → ℝ) (l : List ((Fin w × Path) × (Fin w × Path))) : ℝ :=
  (l.map (fun p => β p.1)).prod

mutual
theorem cplMstar_scale (H H' : LeafProfiles w d) (β : Fin w × Path → ℝ) (Z : Finset (Fin w × Path)) :
    (Q : RegCpl) → (a b : Fin w × Path) →
    (∀ p ∈ Q.pairsAt a b, H p.1 = fun k => β p.1 * H' p.1 k) →
    cplMstar H Z Q a b = fun k => pairScale β (Q.pairsAt a b) * cplMstar H' Z Q a b k
  | .triv, a, b, h => by
    have := h (a,b) (by simp [RegCpl.pairsAt])
    funext k
    simp only [cplMstar, pairScale, RegCpl.pairsAt, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    exact congrFun this k
  | .type1 c Q₁ Q₂ Q₃, a, b, h => by
    have h₁ := cplMstar_scale H H' β Z Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) (fun p hp => h p (by
      simp only [RegCpl.pairsAt, List.mem_append]; exact Or.inl (Or.inl hp)))
    have h₂ := cplMstar_scale H H' β Z Q₂ (addrExt b [1]) (addrExt a [1]) (fun p hp => h p (by
      simp only [RegCpl.pairsAt, List.mem_append]; exact Or.inl (Or.inr hp)))
    have h₃ := cplMstar_scale H H' β Z Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) (fun p hp => h p (by
      simp only [RegCpl.pairsAt, List.mem_append]; exact Or.inr hp))
    funext k
    simp only [cplMstar]
    have he : (fun k₁ k₂ k₃ =>
        cplMstar H Z Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) k₁ *
          cplMstar H Z Q₂ (addrExt b [1]) (addrExt a [1]) k₂ *
          cplMstar H Z Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) k₃) =
        (fun k₁ k₂ k₃ => (pairScale β (Q₁.pairsAt (addrExt a [0]) (addrExt b [c.partner 0])) *
          pairScale β (Q₂.pairsAt (addrExt b [1]) (addrExt a [1])) *
          pairScale β (Q₃.pairsAt (addrExt a [2]) (addrExt b [c.partner 2]))) *
          (cplMstar H' Z Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) k₁ *
            cplMstar H' Z Q₂ (addrExt b [1]) (addrExt a [1]) k₂ *
            cplMstar H' Z Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) k₃)) := by
      funext k₁ k₂ k₃
      rw [h₁,h₂,h₃]
      ring
    rw [he,resIntegral_const_mul]
    simp only [pairScale, RegCpl.pairsAt, List.map_append, List.prod_append]
  | .type2 Xp Xm Qlp, a, b, h => by
    have hp := chainNstar_scale H H' β Z Xp 1 a (fun p hp => h p (by
      simp only [RegCpl.pairsAt, List.mem_append]; exact Or.inl (Or.inl hp)))
    have hm := chainNstar_scale H H' β Z Xm (-1) b (fun p hp => h p (by
      simp only [RegCpl.pairsAt, List.mem_append]; exact Or.inl (Or.inr hp)))
    have hq := cplMstar_scale H H' β Z Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) (fun p hp => h p (by
      simp only [RegCpl.pairsAt, List.mem_append]; exact Or.inr hp))
    funext k
    simp only [cplMstar]
    rw [hq,hp,hm]
    simp only [pairScale, RegCpl.pairsAt, List.map_append, List.prod_append]
    ring
  termination_by structural Q => Q

theorem chainNstar_scale (H H' : LeafProfiles w d) (β : Fin w × Path → ℝ) (Z : Finset (Fin w × Path)) :
    (X : RegChain) → (ζ : ℤˣ) → (a : Fin w × Path) →
    (∀ p ∈ X.pairsAt ζ a, H p.1 = fun k => β p.1 * H' p.1 k) →
    chainNstar H Z X ζ a = fun k => pairScale β (X.pairsAt ζ a) * chainNstar H' Z X ζ a k
  | .nil, ζ, a, h => by
    funext k
    simp [chainNstar, pairScale, RegChain.pairsAt]
  | .pair m Qr Qg inner rest, ζ, a, h => by
    have hI := chainNstar_scale H H' β Z inner (slotSign ζ m.c) (addrExt a [m.c]) (fun p hp => h p (by
      simp only [RegChain.pairsAt, List.mem_append]; exact Or.inl (Or.inr hp)))
    have hR := chainNstar_scale H H' β Z rest (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) (fun p hp => h p (by
      simp only [RegChain.pairsAt, List.mem_append]; exact Or.inr hp))
    have hr : (if slotSign ζ m.red.1 = 1 then
        cplMstar H Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else cplMstar H Z Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) =
      fun k => pairScale β (if slotSign ζ m.red.1 = 1 then
          Qr.pairsAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        else Qr.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) *
        (if slotSign ζ m.red.1 = 1 then
          cplMstar H' Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        else cplMstar H' Z Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) k := by
      split_ifs with hc
      · exact cplMstar_scale H H' β Z Qr _ _ (fun p hp => h p (by
          simp only [RegChain.pairsAt, List.mem_append, hc, ite_true]; exact Or.inl (Or.inl (Or.inl hp))))
      · exact cplMstar_scale H H' β Z Qr _ _ (fun p hp => h p (by
          simp only [RegChain.pairsAt, List.mem_append, hc, ite_false]; exact Or.inl (Or.inl (Or.inl hp))))
    have hg : (if slotSign ζ m.green.1 = 1 then
        cplMstar H Z Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else cplMstar H Z Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) =
      fun k => pairScale β (if slotSign ζ m.green.1 = 1 then
          Qg.pairsAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        else Qg.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) *
        (if slotSign ζ m.green.1 = 1 then
          cplMstar H' Z Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        else cplMstar H' Z Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) k := by
      split_ifs with hc
      · exact cplMstar_scale H H' β Z Qg _ _ (fun p hp => h p (by
          simp only [RegChain.pairsAt, List.mem_append, hc, ite_true]; exact Or.inl (Or.inl (Or.inr hp))))
      · exact cplMstar_scale H H' β Z Qg _ _ (fun p hp => h p (by
          simp only [RegChain.pairsAt, List.mem_append, hc, ite_false]; exact Or.inl (Or.inl (Or.inr hp))))
    funext k
    simp only [chainNstar]
    rw [hI,hR]
    have hpsi : (fun k₁ k₂ k₃ => (if slotSign ζ m.red.1 = 1 then
        cplMstar H Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else cplMstar H Z Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1]))
        (![k₁, k₂, k₃] m.red.1) *
      (if slotSign ζ m.green.1 = 1 then
        cplMstar H Z Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else cplMstar H Z Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1]))
        (![k₁, k₂, k₃] m.green.1)) =
      fun k₁ k₂ k₃ => ((pairScale β (if slotSign ζ m.red.1 = 1 then
          Qr.pairsAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        else Qr.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1]))) * (pairScale β (if slotSign ζ m.green.1 = 1 then
          Qg.pairsAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        else Qg.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])))) * ((if slotSign ζ m.red.1 = 1 then
        cplMstar H' Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else cplMstar H' Z Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1]))
        (![k₁, k₂, k₃] m.red.1) *
      (if slotSign ζ m.green.1 = 1 then
        cplMstar H' Z Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else cplMstar H' Z Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1]))
        (![k₁, k₂, k₃] m.green.1)) := by
      funext k₁ k₂ k₃
      rw [hr,hg]
      ring
    rw [hpsi]
    have hps : pairScale β ((RegChain.pair m Qr Qg inner rest).pairsAt ζ a) =
        (pairScale β (if slotSign ζ m.red.1 = 1 then
          Qr.pairsAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        else Qr.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1]))) *
        (pairScale β (if slotSign ζ m.green.1 = 1 then
          Qg.pairsAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        else Qg.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1]))) *
        pairScale β (inner.pairsAt (slotSign ζ m.c) (addrExt a [m.c])) *
        pairScale β (rest.pairsAt (slotSign (slotSign ζ m.c) m.lone)
          (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))) := by
      simp only [pairScale, RegChain.pairsAt, List.map_append, List.prod_append]
    rw [hps]
    by_cases hz : a ∈ Z
    · rw [ite_eq_left hz,ite_eq_left hz,pvResonantIntegral_const_mul]
      ring
    · rw [ite_eq_right hz,ite_eq_right hz,resIntegral_const_mul]
      ring
  termination_by structural X => X
end

end WaveTurbulence.RA1Leafwise
