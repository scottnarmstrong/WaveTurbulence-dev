/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceChainProducts

/-! # Type2 factorization of the original constructed source leaf product -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Reg TTree

variable {V : Type*} [AddCommGroup V] {w : ℕ}

/-- The literal type2 leaf factors split into the two original chain
products and the lone-pair couple product. Continuation independence
removes the lone input from each chain without changing its paired leaves. -/
theorem cplLeafProduct_type2 (F : Fin w × Path → V → ℂ) (θ : Fin w × Path → V × V)
    (Xp Xm : RegChain) (Qlp : RegCpl) (a b : Fin w × Path) (r : V) (hab : Indep a b) :
    cplLeafProduct F θ (.type2 Xp Xm Qlp) a b r =
      chainLeafProduct F θ Xp 1 a r (fun _ => r) *
        chainLeafProduct F θ Xm (-1) b r (fun _ => r) *
          cplLeafProduct F θ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r := by
  let cont := cplVal θ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r
  have hp : ((Xp.pairsAt 1 a).map
      (fun p => F p.1 (cplVal θ (.type2 Xp Xm Qlp) a b r p.1))).prod =
      chainLeafProduct F θ Xp 1 a r cont := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hmem
    apply congrArg (F p.1)
    have ha := (chain_pair_fst_region Xp 1 a p hmem).1
    simp only [cplVal,ha,ite_true,cont]
  have hm : ((Xm.pairsAt (-1) b).map
      (fun p => F p.1 (cplVal θ (.type2 Xp Xm Qlp) a b r p.1))).prod =
      chainLeafProduct F θ Xm (-1) b r cont := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hmem
    apply congrArg (F p.1)
    have hb := (chain_pair_fst_region Xm (-1) b p hmem).1
    have ha : ¬ Under a p.1 := fun ha => hab.not_both ha hb
    simp only [cplVal,ha,ite_false,cont]
  have hl : ((Qlp.pairsAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)).map
      (fun p => F p.1 (cplVal θ (.type2 Xp Xm Qlp) a b r p.1))).prod =
      cplLeafProduct F θ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hmem
    apply congrArg (F p.1)
    rcases cpl_pair_fst_under Qlp _ _ p hmem with ha | hb
    · have ha' : Under a p.1 := under_trans (under_ext a Xp.lonePath) ha
      simp only [cplVal,ha',ite_true]
      exact chainVal_lone θ Xp 1 a r cont p.1 ha
    · have hb' : Under b p.1 := under_trans (under_ext b Xm.lonePath) hb
      have ha' : ¬ Under a p.1 := fun ha => hab.not_both ha hb'
      simp only [cplVal,ha',ite_false]
      exact chainVal_lone θ Xm (-1) b r cont p.1 hb
  have hfactor : cplLeafProduct F θ (.type2 Xp Xm Qlp) a b r =
      chainLeafProduct F θ Xp 1 a r cont * chainLeafProduct F θ Xm (-1) b r cont *
        cplLeafProduct F θ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r := by
    simp only [cplLeafProduct,RegCpl.pairsAt,List.map_append,List.prod_append] at hp hm hl ⊢
    rw [hp,hm,hl]
  rw [hfactor,chainLeafProduct_cont_independent F θ Xp 1 a r cont (fun _ => r),
    chainLeafProduct_cont_independent F θ Xm (-1) b r cont (fun _ => r)]

end WaveTurbulence.RA1Leafwise
