/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceMstarBound

/-! # Literal original source singular integral equals recursive Mstar -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Reg TTree ApproxNT

private theorem singInt_eq_eval_of_zero {d n : ℕ} (hn : n=0) (J : Finset (Fin n))
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) : singInt J W = W 0 0 := by
  subst n
  rfl

/-- DH23 Prop6.1 leading spatial identification at every order: the
ORIGINAL inputMomentum singular integral equals2 per original link times
the literal recursive Mstar. Empty, even unnormalized, codes are included. -/
theorem original_source_singInt_eq_Mstar {d : ℕ} (hd : 3 ≤ d)
    {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    (hdom : Q.dominant = true) {H : LGSpine.LeafProfiles 2 d} {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal B)
    (Z : Finset (Fin 2 × Path)) (hZ : IsSpecialSet Q.links Z) (k : Mom d) :
    singInt (markedLinkIndices Q Z) (fun x y =>
      ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) =
      (2:ℂ)^Q.links.length*(LGSpine.LeafApp.cplMstar H Z Q (0,[]) (1,[]) k:ℂ) := by
  by_cases hn : 0 < Q.links.length
  · rw [← addressAppAlong_source_eq_singInt hd hQ hG hn (by omega) (by omega) hB (fun a => hF _) Z k]
    change addressAppAlong Z ((Q.linksAt (0,[]) (1,[])).map Prod.fst)
      (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k) 0 = _
    rw [← ofReal_realCplFold hd Q (by omega) (by omega) hB hF Z _ _ indep_roots k 0,
      realCplFold_eq_Mstar hd hB hF Q hdom Z _ _ indep_roots
        (fun z _ hz => hZ z hz) k]
    simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,linksAt_length_eq_links]
  · have hn0 : Q.links.length = 0 := by omega
    have hnil : Q.linksAt (0,[]) (1,[]) = [] := List.eq_nil_of_length_eq_zero hn0
    rw [singInt_eq_eval_of_zero hn0]
    change (∏ a, addrFam H (plusLeafEquiv hQ hG a).val.1 ((coupleMomentumData hQ hG).inputMomentum k _ a)) = _
    rw [prod_source_input_eq_cplLeafProduct hQ hG (addrFam H) k]
    rw [cplLeafProduct_eq_input_of_links_nil _ _ Q _ _ k indep_roots hnil,
      Mstar_eq_input_of_links_nil H Q Z _ _ k hnil,hn0,pow_zero,one_mul]
    simp only [addrFam]

end WaveTurbulence.RA1Leafwise
