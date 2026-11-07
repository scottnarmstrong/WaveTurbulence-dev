/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103GoodSelectorSupport
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103PostBetaCut
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaRank
import Mathlib.Tactic

/-! # The actual seven-label good configuration produced by a post-R beta -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An actual permitted beta after R internally chooses the virtual
triple's OLD cut and orders both actual stars, with remaining pair in/out
and exact total circuit loss four. -/
theorem select_good_post_beta (M : Molecule V D) (hI : SearchInput M)
    {a : V} (ha : a ∈ M.atoms) (ha3 : M.deg a = 3)
    (hbeta : AdmitsBetaSplit (eraseAtoms M {a})) : ActualGoodConfiguration M a := by
  classical
  let N := eraseAtoms M {a}
  have hN := isMolecule_eraseAtoms M hI.molecule {a}
  have hloopN : ∀ z, N.atom z ≠ N.atom (N.mate z) := fun z => hI.loopless z.val
  obtain ⟨b,p,q,hd,hb4,hNb,hdisc⟩ := hbeta
  have hb : b ∈ N.atoms := by
    obtain ⟨u,hu,hub⟩ := mem_map.mp hd.1
    change some u = some b at hub
    exact Option.some.inj hub ▸ hu
  have hbOld := (mem_sdiff.mp hb).1
  have hba : b ≠ a := by simpa only [mem_singleton] using (mem_sdiff.mp hb).2
  have hp : M.atom p.val = b := Option.some.inj hd.2.2.1
  have hq : M.atom q.val = b := Option.some.inj hd.2.2.2.1
  have hpo : M.out p.val = false := hd.2.2.2.2.2.1
  have hqo : M.out q.val = true := hd.2.2.2.2.2.2
  obtain ⟨r,s,hr,hs,hro,hso,hpq,hpr,hps,hqr,hqs,hrs,hStarN⟩ :=
    exists_remaining_mixed_pair N hN hb hb4 hp hq hpo hqo
  obtain ⟨U,hU,hcutU,_,_⟩ := exists_old_cut_of_beta_split N hloopN hp hq hdisc
  let T := (N.atoms \ {b}) \ U
  have hT : T ⊆ N.atoms \ {b} := sdiff_subset
  have hcutT := beta_other_side_boundary N hloopN hp hq hr hs hpr hps hqr hqs hStarN U hU hcutU
  have hchoice := exists_old_virtual_triple_cut_of_post_mixed_sides M hI.molecule hI.loopless
    hI.bridgeless hI.noBeta a ha3 p q r s (hq.trans hp.symm) (hr.trans hp.symm) (hs.trans hp.symm)
    (by simpa only [hp] using hb4) hpo hqo hro hso U (by simpa only [hp] using hU) hcutU
    (by simpa only [hp] using hcutT)
  simp only [hp] at hchoice
  have hImage := old_star_eq_image_of_eraseAtoms_four M hI.molecule {a} hbOld hb4
  have hStarOld : M.dartsAt b = {p.val,q.val,r.val,s.val} := by
    rw [← hImage,hStarN,image_insert,image_insert,image_insert,image_singleton]
  have hne {u w : RetainedDart M {a}} (h : u ≠ w) : u.val ≠ w.val := fun he => h (Subtype.ext he)
  have hFirst := circuitRank_erase_three_of_bridgeless M hI.loopless hI.bridgeless ha ha3
  have hSecond := circuitRank_erase_beta_joint N hN hloopN hd hb4 hNb hdisc
  have hLoss : M.circuitRank - (eraseAtoms M {a,b}).circuitRank = 4 := by
    rw [← circuitRank_erase_erase_singleton_eq M a b]
    change M.circuitRank - (eraseAtoms N {b}).circuitRank = 4
    change N.circuitRank = M.circuitRank - 2 at hFirst
    omega
  rcases hchoice with ⟨x,hx,hcut⟩ | ⟨x,hx,hcut⟩
  · obtain ⟨A⟩ := exists_star3_remainder M ha3 hx
    let B : Star4Remainder M b p.val q.val :=
      ⟨r.val,s.val,hne hpq,hne hpr,hne hps,hne hqr,hne hqs,hne hrs,hStarOld⟩
    have hcut' : boundaryDarts M U = {M.mate x,M.mate p.val,M.mate q.val} := by
      rw [hcut]
      ext w
      simp only [mem_insert,mem_singleton]
      tauto
    exact .sevenLabelQuartic b hbOld (Ne.symm hba) x p.val q.val A B
      (Ne.symm (retained_ne_first_incidence M a p hx).1) (Ne.symm (retained_ne_first_incidence M a q hx).1)
      hpo hqo hro hso U (fun u hu => (mem_sdiff.mp (mem_sdiff.mp (hU hu)).1).1) hcut' hLoss
  · obtain ⟨A⟩ := exists_star3_remainder M ha3 hx
    have hStarRot : M.dartsAt b = {r.val,s.val,p.val,q.val} := by
      rw [hStarOld]
      ext w
      simp only [mem_insert,mem_singleton]
      tauto
    let B : Star4Remainder M b r.val s.val :=
      ⟨p.val,q.val,hne hrs,hne (Ne.symm hpr),hne (Ne.symm hqr),hne (Ne.symm hps),hne (Ne.symm hqs),hne hpq,hStarRot⟩
    have hcut' : boundaryDarts M T = {M.mate x,M.mate r.val,M.mate s.val} := by
      rw [hcut]
      ext w
      simp only [mem_insert,mem_singleton]
      tauto
    exact .sevenLabelQuartic b hbOld (Ne.symm hba) x r.val s.val A B
      (Ne.symm (retained_ne_first_incidence M a r hx).1) (Ne.symm (retained_ne_first_incidence M a s hx).1)
      hro hso hpo hqo T (fun u hu => (mem_sdiff.mp (mem_sdiff.mp (hT hu)).1).1) hcut' hLoss

end WaveTurbulence.MoleProp
