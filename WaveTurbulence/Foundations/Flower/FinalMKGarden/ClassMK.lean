/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKGarden.LoopDataMK
public import WaveTurbulence.Foundations.Flower.FinalMKGarden.HostF

/-! # C1c MK-GARDEN / ClassMK: `lowLoopClassHypsMK_unloop`

Main's `lowLoopClassHyps_unloop` (LowGardenLoopClass3) with survivors: from `LowLoopDataMK` on `M`, the class
premises `LowLoopClassHypsMK` on `M.unloop` with the collection data `unloopMK C` (`forb` unchanged), the survivors
`unloopE E`, `crit` unchanged and `Tm = lab.1`.
* the pool transports go through `PoolContained (poolF C)` (`poolContained_toF`) instead of `SubproOblG`;
* `oblE` is `SubproOblGMK.unloop`;
* `hostConn`/`hostConnFLE` are `hostConnLK_of`/`hostConnFK_of` with the survivor kills `KillS qs` at `C.forb`;
* `cnBound` is main's `cnBound_unloop_R` read on the first-stage pieces (`cnBoundF_of_cnBound`). -/

@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)

namespace WaveTurbulence.Flower.FinalMKGarden
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs

section generic
variable {V : Type*} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ} {M₀ : Molecule V D₀}

/-- `CnBoundF` on first-stage pieces from main's `CnBound` (first-stage objects are members of `C₁`, collected for
every pool). -/
theorem cnBoundF_of_cnBound {C : CollDataMK M₀} {Un Un0 : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)}
    {L γ η : ℝ} {w : Mom d} {A0 : Set (D₀ → (Fin d → ℤ))} {Rn : ℕ}
    (hFst : ∀ U ∈ Fst, ∃ i, U = C.collection i) (h : CnBound M₀ C.toCollData Un0 Fst L γ η w A0 Rn) :
    CnBoundF M₀ C Un Fst L γ η w A0 Rn := by
  intro κ hκ ps hps hpw
  exact h κ hκ ps (fun p hp => ⟨⟨Or.inl (hFst p.1 (hps p hp).2), (hps p hp).1.2⟩, (hps p hp).2⟩) hpw

end generic

section main
variable {V : Type} [DecidableEq V] [Infinite V] {D : Type} [Fintype D] [DecidableEq D] {d : ℕ}

/-- **The class premises with survivors on `M.unloop`** (main's `lowLoopClassHyps_unloop`). -/
theorem lowLoopClassHypsMK_unloop {M : Molecule V D} {R : ℕ} {Adm : (D → Fin d → ℤ) → Prop} {P0 : Finset V → ℝ}
    {C : CollDataMK M} {m : ℕ} {E : Fin m → Object M} {Un : (D → Fin d → ℤ) → Set (Object M)} {Fst : Set (Object M)}
    {crit : V → Prop} {kFix : Finset (Mom d)} {L γ η : ℝ} {mm : ℕ}
    (hD : LowLoopDataMK M R Adm P0 C E Un Fst crit kFix L γ η mm) (hL0 : L ≠ 0)
    (hkle : ((M.loopBonds.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ mm)
    {Un' : (NonLoop M → Fin d → ℤ) → Set (Object M.unloop)}
    (hUn' : ∀ κ, Adm κ → Un' (fun y : NonLoop M => κ y.1) = unloopSet M (Un κ))
    (lab : Finset V × (lowAtoms M → Option (Mom d)))
    (hne : ∃ κ, Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ) :
    LowLoopClassHypsMK (d := d) M R (heredScale' M.unloop P0)
      {κ' | unloopAdm M (fun κ => Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ) κ'} (unloopMK C) (unloopE E)
      Un' (unloopSet M Fst) crit (fun v => v ∈ lab.1) L γ η mm := by
  have hb : ∀ a ∈ M.atoms, M.deg a ≤ 4 := fun a ha => deg_le_four M (hD.hSL.bounds a ha)
  have hctx : ∀ κ, Adm κ → LoopCtx L (0 : Mom d) κ (R + M.loopBonds.card) M := fun κ hκ =>
    ⟨hD.hSL.unloop, hb, hD.hmate κ hκ, hD.heq κ hκ, h0_unloop hD.hSL (hD.hmate κ hκ) (hD.h0 κ hκ)⟩
  have hSU : SubHypL (R + M.loopBonds.card) M.unloop := hD.hSL.unloop
  have hMol' : M.unloop.IsMolecule := hSU.isMolecule
  have hnl' : ∀ z, M.unloop.atom z ≠ M.unloop.atom (M.unloop.mate z) := hSU.noloop
  have hP : ∀ κ, Adm κ → PoolContained (poolF C) L γ η (0 : Mom d) κ := fun κ hκ =>
    poolContained_toF hD.forbE (hD.oblE κ hκ)
  have hdec' : ∀ κ, Adm κ → ∃ c0, M.unloop.IsDecoration L (0 : Mom d) c0 (fun y : NonLoop M => κ y.1) ∧
      ∀ x ∈ M.unloop.atoms, M.unloop.deg x = 4 → c0 x = 0 := fun κ hκ => by
    obtain ⟨c0, hc, hc0⟩ := hD.hdec κ hκ
    exact ⟨c0, unloop_isDecoration M hc, fun x hx h4 => hc0 x hx (le_antisymm (hb x hx) (h4 ▸ unloop_deg_le M x))⟩
  have hlift : ∀ κ, Adm κ → ∀ U' : Object M.unloop,
      Collected (poolF C).unloop (Un' (fun y : NonLoop M => κ y.1)) L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1) U' →
      ∃ hlf : LoopFreeSet M U'.atoms, Coll2 (poolF C) (Un κ) L γ η (0 : Mom d) κ (U'.lift hlf) := by
    intro κ hκ U' h
    rw [hUn' κ hκ] at h
    exact collected_liftP (hctx κ hκ) (hP κ hκ) h
  have hc2lift : ∀ κ, Adm κ → ∀ U' ∈ (poolF C).unloop.C2Of L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1)
      (Un' (fun y : NonLoop M => κ y.1)),
      ∃ hlf : LoopFreeSet M U'.atoms, U'.lift hlf ∈ (poolF C).C2Of L γ η (0 : Mom d) κ (Un κ) := by
    intro κ hκ U' h
    rw [hUn' κ hκ] at h
    exact c2Of_liftP (hctx κ hκ) (hP κ hκ) h
  have hd22' : ∀ κ, Adm κ → ∀ O ∈ (poolF C).unloop.C2Of L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1)
      (Un' (fun y : NonLoop M => κ y.1)), ∀ O' ∈ (poolF C).unloop.C2Of L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1)
      (Un' (fun y : NonLoop M => κ y.1)), O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms := by
    intro κ hκ O hO O' hO'
    obtain ⟨h1, h2⟩ := hc2lift κ hκ O hO
    obtain ⟨h3, h4⟩ := hc2lift κ hκ O' hO'
    exact hD.hC22 κ hκ _ h2 _ h4
  have hvc' : ∀ κ, Adm κ → ∀ O ∈ (poolF C).unloop.C2Of L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1)
      (Un' (fun y : NonLoop M => κ y.1)), (∃ h, O.shape = VineLikeObject.vc h) →
      Vine.DoubleChain M.unloop O.atoms O.upper O.lower 1 ∨ Vine.DoubleChain M.unloop O.atoms O.upper O.lower 2 ∨
        M.unloop.IsVine .V O.atoms O.upper O.lower := by
    intro κ hκ O hO hvc
    obtain ⟨hlf, h2⟩ := hc2lift κ hκ O hO
    rcases hD.vc2 κ hκ _ h2 (lift_shape_vc O hlf hvc) with h | h | h
    · exact Or.inl (doubleChain_unloop h hlf)
    · exact Or.inr (Or.inl (doubleChain_unloop h hlf))
    · exact Or.inr (Or.inr (((unloopEmb M hlf).isVine_iff rfl).1 h))
  have hunsel' : ∀ κ, Adm κ → (poolF C).unloop.UnselOK L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1)
      (Un' (fun y : NonLoop M => κ y.1)) := by
    intro κ hκ
    rw [hUn' κ hκ]
    exact unselOK_unloopP (hctx κ hκ) (hP κ hκ) (hD.unsel κ hκ)
  have hFstC' : ∀ i, (∃ h, ((poolF C).unloop.collection i).shape = VineLikeObject.vc h) →
      (poolF C).unloop.collection i ∈ unloopSet M Fst :=
    fun i hvc => ⟨C.collection i, hD.hFstC i (unloop_shape_vc' _ (Object.loopFree _) hvc), rfl⟩
  have hC13' : ∀ i, ((poolF C).unloop.collection i).atoms.card ≠ 3 := hD.hC13
  have hFst' : ∀ U ∈ unloopSet M Fst, ∃ i, U = (unloopMK C).collection i := by
    rintro U ⟨U0, hU0, rfl⟩
    obtain ⟨i, rfl⟩ := hD.hFst U0 hU0
    exact ⟨i, rfl⟩
  have hF : C.forb ⊆ (poolF C).unloop.hinges := Finset.subset_union_right
  have hKx : ∀ qs : List (Object M.unloop × Quad (NonLoop M)), (∀ q ∈ qs, PieceDataS (unloopE E) q) →
      ∀ z ∈ KillS qs, M.unloop.atom z ∈ C.forb := by
    intro qs hqs z hz
    rw [hD.forbE]
    exact killS_surv_atom hqs hz
  have hF1 : ∀ i, Disjoint ((poolF C).unloop.collection i).atoms C.forb := by
    intro i
    rw [hD.forbE]
    exact disjoint_survAtomsM.2 fun j => hD.survC1 i j
  refine
    { subHypLoop := hD.hSL
      subHypL := hSU
      card_loopAtoms := card_loopAtoms_eq hD.hSL
      isMol := hMol'
      hP := ladderHered_heredScale' _ _
      hP0 := heredScale'_nonneg M.unloop (by rw [unloop_maximalLadders]; exact hD.hP0)
      pinned := ?_
      forbE := hD.forbE
      oblE := ?_
      trip := TripleDesig.unloop hD.hH hD.trip
      unsel := ?_
      degen := ?_
      h0 := ?_
      tameEq := ?_
      mate := ?_
      fixEff := ?_
      loopTame := ?_
      noLoopSG := ?_
      critSG := ?_
      card := hD.card
      kle := hkle
      srcGaps := ?_
      dec := ?_
      disj := ?_
      fst := ?_
      sgC := ?_
      desC := ?_
      shape := ?_
      hostConn := ?_
      critInt := ?_
      cnBound := cnBoundF_of_cnBound (Un0 := Un') hFst'
        (cnBound_unloop_R hD.hFst (fun κ' ⟨κ, ⟨hκ, _⟩, e⟩ => ⟨κ, hκ, e⟩) hD.cn)
      survDisjC := ?_
      survChain := hD.survChain
      survShape := fun i => objVine_unloop (E i) (Object.loopFree _) (hD.survShape i)
      survCritInt := hD.survCritInt
      survHinge := hD.survHinge
      survFst := ?_
      hostConnFLE := ?_ }
  · intro a ha
    obtain ⟨c, hc⟩ := hD.pin a ha
    refine ⟨c, fun k0 hk0 => ?_⟩
    obtain ⟨κ, ⟨hκ, -⟩, rfl⟩ := hk0
    unfold chargeAt
    rw [sum_unloop_kvec M (hD.hmate κ hκ) a]
    exact hc κ hκ
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩
    exact SubproOblGMK.unloop (hctx κ hκ) hD.hH (hD.oblE κ hκ)
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩
    exact (unselOKF_iff _ _).2 (hunsel' κ hκ)
  · rintro κ' ⟨κ, ⟨hκ, hcl⟩, rfl⟩
    refine DegenSGT.unloop (hctx κ hκ) ?_
    intro a ha x y hx hy hox hoy hxy hzg
    exact (hD.degen κ hκ a ha x y hx hy hox hoy hxy hzg).imp_right fun hT => (hcl.1 a ha).1 hT
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩
    exact h0_unloop hD.hSL (hD.hmate κ hκ) (hD.h0 κ hκ)
  · rintro k0 ⟨κ, ⟨hκ, hcl⟩, rfl⟩ v hv hvZ x y hx hy
    exact kvec_injective hL0 0 κ (((hcl.1 v hv).2 hvZ).1 x.1 y.1 hx hy)
  · rintro k0 ⟨κ, ⟨hκ, -⟩, rfl⟩ x
    exact hD.hmate κ hκ x.1
  · intro v hv hvZ hdeg
    have hdeg' : M.deg v < 4 := by rwa [← effDeg_eq_deg hD.hSL hv]
    obtain ⟨x0, hx0, -⟩ := hD.hSL.nonloop v hv
    obtain ⟨κ1, hκ1, hcl1⟩ := hne
    have hlow : v ∈ lowAtoms M := Finset.mem_filter.2 ⟨hv, hdeg'⟩
    refine ⟨κ1 x0, ?_⟩
    rintro k0 ⟨κ, ⟨hκ, hcl⟩, rfl⟩ x hx
    have e1 := hcl.2 ⟨v, hlow⟩ hvZ x.1 hx
    have e2 := hcl1.2 ⟨v, hlow⟩ hvZ x0 hx0
    rw [e1] at e2
    have e3 := Option.some.inj e2
    unfold Molecule.kvec at e3
    exact latticePoint_injective' hL0 (add_left_cancel e3)
  · intro v hv
    obtain ⟨κ1, hκ1, hcl1⟩ := hne
    exact (hcl1.1 v (Finset.mem_filter.1 hv).1).1 (loopAtom_tame hD.hSL (hD.heq κ1 hκ1) (hD.degen κ1 hκ1) hv)
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ U hU v hv hvB
    obtain ⟨-, z, hz1, hz2⟩ := Finset.mem_filter.1 hvB
    exact (hctx κ hκ).noLoop γ η U hU z (by rw [hz1]; exact hv) (hz1.trans hz2.symm)
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ a ha
    exact sgat_unloop (hctx κ hκ) (hD.critSG κ hκ a ha)
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩
    obtain ⟨c, hc, hc0⟩ := hdec' κ hκ
    exact sourceLadderGaps_hered hMol' hc hc0 (sourceLadderGaps_unloop (hD.gaps κ hκ))
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩
    exact hdec' κ hκ
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ U U' hU hU'
    exact desDisj_of_parts (C := (poolF C).unloop) (Un := Un' (fun y : NonLoop M => κ y.1))
      (fun i j hij => hD.hC1 i j hij) (fun U hU i => (Subpro.c2Of_disjoint_c1_hinges _ hU).1 i) (hd22' κ hκ)
      U U' hU hU'
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ U hU
    obtain ⟨U0, hU0, rfl⟩ := hU
    obtain ⟨i, rfl⟩ := hD.hFst U0 hU0
    exact Or.inl ⟨i, rfl⟩
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ U hU
    obtain ⟨hlf, hc2⟩ := hlift κ hκ U hU
    exact (Object.lift_hasGapKind U hlf L γ η (0 : Mom d) κ .SG).1 (hD.sg2 κ hκ _ hc2)
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ U hU
    obtain ⟨hlf, hc2⟩ := hlift κ hκ U hU
    exact hingeData_unloop hD.hH hlf (hD.des2 κ hκ _ hc2)
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ U hU
    obtain ⟨hlf, hc2⟩ := hlift κ hκ U hU
    rcases hD.shape2 κ hκ _ hc2 with h | h
    · exact Or.inl h
    · right
      have := objVine_unloop _ hlf h
      rwa [Object.unloop_lift U hlf hlf] at this
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ qs ps U a x b hqs hps hpw hdis hUc hUat hax hxb hab hclos
    obtain ⟨c, hc, hc0⟩ := hdec' κ hκ
    exact hostConnLK_of hMol' hc hc0 (hd22' κ hκ) (hvc' κ hκ) (hunsel' κ hκ) hnl' hC13' C.forb hF (KillS qs)
      (hKx qs hqs) ps U a x b hps hpw hdis hUc hUat hax hxb hab hclos
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ U hU a ha h1 h2
    obtain ⟨hlf, hc2⟩ := hlift κ hκ U hU
    exact hD.crit2 κ hκ _ hc2 a ha h1 h2
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ U hU i
    rcases hU with ⟨j, rfl⟩ | hU
    · exact hD.survC1 j i
    · have h := (Subpro.c2Of_disjoint_c1_hinges (poolF C).unloop (show U ∈ (poolF C).unloop.C2Of L γ η 0 _ _ from hU.1)).2
      have h' : Disjoint U.atoms C.forb := Finset.disjoint_of_subset_right hF h
      rw [hD.forbE] at h'
      exact disjoint_survAtomsM.1 h' i
  · intro i hi
    obtain ⟨B, hB, he⟩ := hi
    have e := Object.unloop_inj (Object.loopFree (E i)) (Object.loopFree B) he
    obtain ⟨j, rfl⟩ := hD.hFst B hB
    have hd := hD.survC1 j i
    rw [← e] at hd
    have hu := object_mem_of_joint (E i) (Or.inl rfl)
    exact Finset.disjoint_left.1 hd hu hu
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ qs ps p hqs hps hp hpF hpw - -
    obtain ⟨c, hc, hc0⟩ := hdec' κ hκ
    exact hostConnFK_of hMol' hc hc0 (hd22' κ hκ) (hvc' κ hκ) (hunsel' κ hκ) hnl' hFstC' C.forb hF hF1 (KillS qs)
      (hKx qs hqs) ps p hps hp hpF hpw

end main

end WaveTurbulence.Flower.FinalMKGarden
