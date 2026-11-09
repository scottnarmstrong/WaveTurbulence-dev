/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenUnloopMain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenUnloop
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Transport
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.VineLocalDartObjects
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowGardenUnloopMain`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (LOW-GARDEN, session 2): the class transport `lowClassHyps2_unloop`.** 

**Low-range change (L6-HDS).** The ordinary members of `C₂` are one or two double bonds or T-vines (`vc2`, TARGET
`subsetvc`′; main: a vine (V)); the T-vine is transported to the loop-free restriction by `DS.gEmb_isTVine_iff`.
-/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

section main
variable {V : Type} [DecidableEq V] [Infinite V] {D : Type} [Fintype D] [DecidableEq D] {d : ℕ}

/-- **The `M`-level data of the loop transport** (all of it holds on the molecule of a garden with loops: it is what the REG producers
supply, stated for the `C₁ ∪ C₂` collected objects, together with `SubHypLoop` and the `ε`-support `heq`). -/
structure LowLoopData (M : Molecule V D) (R : ℕ) (Adm : (D → Fin d → ℤ) → Prop) (P0 : Finset V → ℝ) (C : CollData M)
    (Un : (D → Fin d → ℤ) → Set (Src.Object Src.γL M)) (Fst : Set (Src.Object Src.γL M)) (crit : V → Prop) (kFix : Finset (Mom d))
    (L γ η : ℝ) (m : ℕ) : Prop where
  hSL : SubHypLoop R M
  hmate : ∀ κ, Adm κ → ∀ x, κ (M.mate x) = κ x
  heq : ∀ κ, Adm κ → ∀ y : D, M.atom y = M.atom (M.mate y) → ∀ z : D, M.atom z = M.atom y → κ z = κ y
  hdec : ∀ κ, Adm κ → ∃ c0, M.IsDecoration L (0 : Mom d) c0 κ ∧ ∀ x ∈ M.atoms, M.deg x = 4 → c0 x = 0
  h0 : ∀ κ, Adm κ → ∀ a ∈ M.atoms, M.deg a = 4 → ∑ x ∈ M.dartsAt a, M.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0
  pin : PinnedM0 (fun k => Adm k) L (0 : Mom d) M
  hP0 : ∀ S ∈ M.maximalLadders, 0 ≤ P0 S
  gaps : ∀ κ, Adm κ → SourceLadderGaps M L (0 : Mom d) P0 κ
  hH : HingeNoLoop C
  trip : TripleDesig C
  obl : ∀ κ, Adm κ → SubproOblG C L γ η (0 : Mom d) κ
  unsel : ∀ κ, Adm κ → C.UnselOK L γ η (0 : Mom d) κ (Un κ)
  degen : ∀ κ, Adm κ → DegenSGT M L γ η (0 : Mom d) κ (fun a => M.IsTame L (0 : Mom d) kFix κ a)
  critSG : ∀ κ, Adm κ → ∀ a, crit a → SGat M L γ η (0 : Mom d) κ a
  card : ((2 * M.atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m
  sg2 : ∀ κ, Adm κ → ∀ U, Coll2 C (Un κ) L γ η (0 : Mom d) κ U → U.HasGapKind L γ η (0 : Mom d) κ .SG
  des2 : ∀ κ, Adm κ → ∀ U, Coll2 C (Un κ) L γ η (0 : Mom d) κ U → HingeData C U
  shape2 : ∀ κ, Adm κ → ∀ U, Coll2 C (Un κ) L γ η (0 : Mom d) κ U → U.atoms.card = 3 ∨ ObjVine M U
  crit2 : ∀ κ, Adm κ → ∀ U, Coll2 C (Un κ) L γ η (0 : Mom d) κ U → ∀ a ∈ U.atoms, a ≠ U.upper → a ≠ U.lower → ¬ crit a
  hC1 : ∀ i j, i ≠ j → Disjoint (C.collection i).atoms (C.collection j).atoms
  hC12 : ∀ κ, Adm κ → ∀ U ∈ C.C2Of L γ η (0 : Mom d) κ (Un κ), ∀ i, Disjoint U.atoms (C.collection i).atoms
  hC22 : ∀ κ, Adm κ → ∀ O ∈ C.C2Of L γ η (0 : Mom d) κ (Un κ), ∀ O' ∈ C.C2Of L γ η (0 : Mom d) κ (Un κ),
    O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms
  vc2 : ∀ κ, Adm κ → ∀ O ∈ C.C2Of L γ η (0 : Mom d) κ (Un κ), (∃ h, O.shape = .vc h) →
    Vine.DoubleChain M O.atoms O.upper O.lower 1 ∨ Vine.DoubleChain M O.atoms O.upper O.lower 2 ∨
      M.IsTVine O.atoms O.upper O.lower
  hC13 : ∀ i, (C.collection i).atoms.card ≠ 3
  hFst : ∀ U ∈ Fst, ∃ i, U = C.collection i
  hFstC : ∀ i, (∃ h, (C.collection i).shape = .vc h) → C.collection i ∈ Fst
  cn : CnBound M C Un Fst L γ η (0 : Mom d) {κ | Adm κ} R

theorem lowClassHyps2_unloop {M : Molecule V D} {R : ℕ} {Adm : (D → Fin d → ℤ) → Prop} {P0 : Finset V → ℝ} {C : CollData M}
    {Un : (D → Fin d → ℤ) → Set (Src.Object Src.γL M)} {Fst : Set (Src.Object Src.γL M)} {crit : V → Prop} {kFix : Finset (Mom d)}
    {L γ η : ℝ} {m : ℕ} (hD : LowLoopData M R Adm P0 C Un Fst crit kFix L γ η m) (hk : 0 < M.loopBonds.card) (hL0 : L ≠ 0)
    {Un' : (NonLoop M → Fin d → ℤ) → Set (Src.Object Src.γL M.unloop)}
    (hUn' : ∀ κ, Adm κ → Un' (fun y : NonLoop M => κ y.1) = unloopSet M (Un κ))
    (lab : Finset V × (lowAtoms M.unloop → Option (Mom d)))
    (hne : ∃ κ', κ' ∈ {κ' | unloopAdm M Adm κ' ∧ InClass M.unloop L (0 : Mom d) kFix lab.1 lab.2 κ'}) :
    LowClassHyps2 (d := d) M.unloop (R + M.loopBonds.card) (heredScale' M.unloop P0)
      {κ' | unloopAdm M Adm κ' ∧ InClass M.unloop L (0 : Mom d) kFix lab.1 lab.2 κ'} C.unloop Un' (unloopSet M Fst) crit
      (fun v => v ∈ lab.1) L γ η m := by
  have hb : ∀ a ∈ M.atoms, M.deg a ≤ 4 := fun a ha => deg_le_four M (hD.hSL.bounds a ha)
  have hctx : ∀ κ, Adm κ → LoopCtx L (0 : Mom d) κ (R + M.loopBonds.card) M := fun κ hκ =>
    ⟨hD.hSL.unloop, hb, hD.hmate κ hκ, hD.heq κ hκ, h0_unloop hD.hSL (hD.hmate κ hκ) (hD.h0 κ hκ)⟩
  have hSU : SubHypL (R + M.loopBonds.card) M.unloop := hD.hSL.unloop
  have hMol' : M.unloop.IsMolecule := hSU.isMolecule
  have hnl' : ∀ z, M.unloop.atom z ≠ M.unloop.atom (M.unloop.mate z) := hSU.noloop
  have hdec' : ∀ κ, Adm κ → ∃ c0, M.unloop.IsDecoration L (0 : Mom d) c0 (fun y : NonLoop M => κ y.1) ∧
      ∀ x ∈ M.unloop.atoms, M.unloop.deg x = 4 → c0 x = 0 := fun κ hκ => by
    obtain ⟨c0, hc, hc0⟩ := hD.hdec κ hκ
    exact ⟨c0, unloop_isDecoration M hc, fun x hx h4 => hc0 x hx (le_antisymm (hb x hx) (h4 ▸ unloop_deg_le M x))⟩
  have hlift : ∀ κ, Adm κ → ∀ U' : Src.Object Src.γL M.unloop,
      Collected C.unloop (Un' (fun y : NonLoop M => κ y.1)) L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1) U' →
      ∃ hlf : LoopFreeSet M U'.atoms, Coll2 C (Un κ) L γ η (0 : Mom d) κ (U'.lift hlf) := by
    intro κ hκ U' h
    rw [hUn' κ hκ] at h
    exact collected_lift (hctx κ hκ) hD.hH (hD.obl κ hκ) h
  have hc2lift : ∀ κ, Adm κ → ∀ U' ∈ C.unloop.C2Of L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1)
      (Un' (fun y : NonLoop M => κ y.1)), ∃ hlf : LoopFreeSet M U'.atoms, U'.lift hlf ∈ C.C2Of L γ η (0 : Mom d) κ (Un κ) := by
    intro κ hκ U' h
    rw [hUn' κ hκ] at h
    exact C2Of_lift (hctx κ hκ) hD.hH (hD.obl κ hκ) h
  have hd22' : ∀ κ, Adm κ → ∀ O ∈ C.unloop.C2Of L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1) (Un' (fun y : NonLoop M => κ y.1)),
      ∀ O' ∈ C.unloop.C2Of L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1) (Un' (fun y : NonLoop M => κ y.1)),
      O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms := by
    intro κ hκ O hO O' hO'
    obtain ⟨h1, h2⟩ := hc2lift κ hκ O hO
    obtain ⟨h3, h4⟩ := hc2lift κ hκ O' hO'
    exact hD.hC22 κ hκ _ h2 _ h4
  have hvc' : ∀ κ, Adm κ → ∀ O ∈ C.unloop.C2Of L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1) (Un' (fun y : NonLoop M => κ y.1)),
      (∃ h, O.shape = Src.VineLikeObject.vc h) →
      Vine.DoubleChain M.unloop O.atoms O.upper O.lower 1 ∨ Vine.DoubleChain M.unloop O.atoms O.upper O.lower 2 ∨
        M.unloop.IsTVine O.atoms O.upper O.lower := by
    intro κ hκ O hO hvc
    obtain ⟨hlf, h2⟩ := hc2lift κ hκ O hO
    rcases hD.vc2 κ hκ _ h2 (lift_shape_vc O hlf hvc) with h | h | h
    · exact Or.inl (doubleChain_unloop h hlf)
    · exact Or.inr (Or.inl (doubleChain_unloop h hlf))
    · exact Or.inr (Or.inr ((DS.gEmb_isTVine_iff (unloopEmb M hlf) rfl).1 h))
  have hunsel' : ∀ κ, Adm κ → C.unloop.UnselOK L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1) (Un' (fun y : NonLoop M => κ y.1)) := by
    intro κ hκ
    rw [hUn' κ hκ]
    exact UnselOK.unloopL (hctx κ hκ) hD.hH (hD.obl κ hκ) (hD.unsel κ hκ)
  have hFstC' : ∀ i, (∃ h, (C.unloop.collection i).shape = Src.VineLikeObject.vc h) → C.unloop.collection i ∈ unloopSet M Fst :=
    fun i hvc => ⟨C.collection i, hD.hFstC i (unloop_shape_vc' _ (Src.Object.loopFree _) hvc), rfl⟩
  have hC13' : ∀ i, (C.unloop.collection i).atoms.card ≠ 3 := hD.hC13
  refine
    { subHypL := hSU
      isMol := hMol'
      hP := ladderHered_heredScale' _ _
      hP0 := heredScale'_nonneg M.unloop (by rw [unloop_maximalLadders]; exact hD.hP0)
      pinned := ?_
      obl := ?_
      trip := TripleDesig.unloopL hD.hH hD.trip
      unsel := ?_
      degen := ?_
      h0 := ?_
      tameEq := ?_
      mate := ?_
      fix := ?_
      critSG := ?_
      card := hD.card
      srcGaps := ?_
      dec := ?_
      disj := ?_
      fst := ?_
      sgC := ?_
      desC := ?_
      shape := ?_
      hostConn := ?_
      critInt := ?_
      cnBound := cnBound_unloop hk hD.hFst (fun κ' h => h.1) hD.cn
      hostConnFL := ?_ }
  · intro a ha
    obtain ⟨c, hc⟩ := hD.pin a ha
    refine ⟨c, fun k0 hk0 => ?_⟩
    obtain ⟨⟨κ, hκ, rfl⟩, -⟩ := hk0
    unfold chargeAt
    rw [sum_unloop_kvec M (hD.hmate κ hκ) a]
    exact hc κ hκ
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩
    exact SubproOblG.unloopL (hctx κ hκ) hD.hH (hD.obl κ hκ)
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩
    exact hunsel' κ hκ
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, hcl⟩
    have hdg := DegenSGT.unloopL (hctx κ hκ) (hD.degen κ hκ)
    intro a ha x y hx hy hox hoy hxy hzg
    rcases hdg a ha x y hx hy hox hoy hxy hzg with hsg | hT
    · exact Or.inl hsg
    · by_cases hl : ∃ z, M.atom z = a ∧ M.atom (M.mate z) = a
      · right; right
        obtain ⟨z, hz1, hz2⟩ := hl
        have hdeg2 := loop_deg_le M hz1 hz2 (hb a ha)
        have hzl : M.atom z = M.atom (M.mate z) := hz1.trans hz2.symm
        have hxy' : x ≠ y := fun e => by
          have : M.unloop.out x = M.unloop.out y := by rw [e]
          rw [hox, hoy] at this; exact Bool.false_ne_true this
        refine ⟨hdeg2, x, y, hx, hy, hox, hoy, hxy, ?_, ?_⟩
        · show κ x.1 = κ y.1
          rw [hD.heq κ hκ z hzl x.1 (hx.trans hz1.symm), hD.heq κ hκ z hzl y.1 (hy.trans hz1.symm)]
        · refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
          · intro u hu
            rcases Finset.mem_insert.1 hu with rfl | hu
            · exact (mem_dartsAt' M.unloop a _).2 hx
            · rw [Finset.mem_singleton.1 hu]; exact (mem_dartsAt' M.unloop a _).2 hy
          · rw [Finset.card_pair hxy']; exact hdeg2
      · right; left
        have hnlz : ∀ z, M.atom z = a → M.atom (M.mate z) ≠ a := fun z hz h => hl ⟨z, hz, h⟩
        refine (hcl.1 a ha).1 ⟨fun x1 x2 hx1 hx2 => hT.1 x1.1 x2.1 hx1 hx2, fun hlt x hx => ?_⟩
        refine hT.2 ?_ x.1 hx
        rw [← deg_unloop_eq M hnlz]; exact hlt
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩
    exact h0_unloop hD.hSL (hD.hmate κ hκ) (hD.h0 κ hκ)
  · intro k0 hk0 v hv hvZ x y hx hy
    have ht := (hk0.2.1 v hv).2 hvZ
    exact kvec_injective hL0 0 k0 (ht.1 x y hx hy)
  · rintro k0 ⟨⟨κ, hκ, rfl⟩, -⟩ x
    exact hD.hmate κ hκ x.1
  · intro v hv hvZ hdeg
    by_cases hx : ∃ x, M.unloop.atom x = v
    · obtain ⟨x0, hx0⟩ := hx
      obtain ⟨κ1, hκ1⟩ := hne
      refine ⟨κ1 x0, fun k0 hk0 x hx => ?_⟩
      have hlow : v ∈ lowAtoms M.unloop := Finset.mem_filter.2 ⟨hv, hdeg⟩
      have e1 := hk0.2.2 ⟨v, hlow⟩ hvZ x hx
      have e2 := hκ1.2.2 ⟨v, hlow⟩ hvZ x0 hx0
      rw [e1] at e2
      have e3 := Option.some.inj e2
      unfold Molecule.kvec at e3
      exact latticePoint_injective' hL0 (add_left_cancel e3)
    · push Not at hx
      exact ⟨0, fun k0 _ x hx' => absurd hx' (hx x)⟩
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩ a ha
    exact sgat_unloop (hctx κ hκ) (hD.critSG κ hκ a ha)
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩
    obtain ⟨c, hc, hc0⟩ := hdec' κ hκ
    exact sourceLadderGaps_hered hMol' hc hc0 (sourceLadderGaps_unloop (hD.gaps κ hκ))
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩
    exact hdec' κ hκ
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩ U U' hU hU'
    refine desDisj_of_parts (C := C.unloop) (Un := Un' (fun y : NonLoop M => κ y.1)) (fun i j hij => hD.hC1 i j hij)
      (fun U hU i => ?_) (hd22' κ hκ) U U' hU hU'
    obtain ⟨h1, h2⟩ := hc2lift κ hκ U hU
    exact hD.hC12 κ hκ _ h2 i
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩ U hU
    obtain ⟨U0, hU0, rfl⟩ := hU
    obtain ⟨i, rfl⟩ := hD.hFst U0 hU0
    exact Or.inl ⟨i, rfl⟩
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩ U hU
    obtain ⟨hlf, hc2⟩ := hlift κ hκ U hU
    exact (Src.Object.lift_hasGapKind U hlf L γ η (0 : Mom d) κ .SG).1 (hD.sg2 κ hκ _ hc2)
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩ U hU
    obtain ⟨hlf, hc2⟩ := hlift κ hκ U hU
    exact hingeData_unloop hD.hH hlf (hD.des2 κ hκ _ hc2)
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩ U hU
    obtain ⟨hlf, hc2⟩ := hlift κ hκ U hU
    rcases hD.shape2 κ hκ _ hc2 with h | h
    · exact Or.inl h
    · right
      have := objVine_unloop _ hlf h
      rwa [Src.Object.unloop_lift U hlf hlf] at this
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩ ps U a x b hps hpw hdis hUc hUat hax hxb hab hclos
    obtain ⟨c, hc, hc0⟩ := hdec' κ hκ
    exact hostConnL_of hMol' hc hc0 (hd22' κ hκ) (hvc' κ hκ) (hunsel' κ hκ) hnl' hC13' ps U a x b hps hpw hdis hUc hUat hax hxb
      hab hclos
  · rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩ U hU a ha h1 h2
    obtain ⟨hlf, hc2⟩ := hlift κ hκ U hU
    exact hD.crit2 κ hκ _ hc2 a ha h1 h2
  · refine hostConnFL_of ?_
    rintro κ' ⟨⟨κ, hκ, rfl⟩, -⟩ ps p hps hp hpF hpw
    obtain ⟨c, hc, hc0⟩ := hdec' κ hκ
    exact hostConnF_of hMol' hc hc0 (hd22' κ hκ) (hvc' κ hκ) (hunsel' κ hκ) hnl' hFstC' ps p hps hp hpF hpw

end main

end WaveTurbulence.GammaLow.FinalCount.H
