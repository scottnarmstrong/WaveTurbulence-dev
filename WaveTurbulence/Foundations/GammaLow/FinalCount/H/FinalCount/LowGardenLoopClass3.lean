/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenLoopClass3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenCn3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoopFacts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLift
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenUnloopMain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Transport
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.VineLocalDartObjects
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowGardenLoopClass3`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **LOW-GARDEN (session 3): `lowLoopClassHyps_unloop`, the original-class loop-provenance record (R79, treatment A).**

For a class `lab` of the ORIGINAL molecule `M` (original tame set `lab.1`, `InClass M`), the `M.unloop`-level data
`LowLoopClassHyps M R ...` with `Tm = lab.1`, the effective fixedness, `loopTame` (`loopAtom_tame`), `noLoopSG`, and `CnBound`
at the original `R` (`cnBound_unloop_R`). 

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

section main3
variable {V : Type} [DecidableEq V] [Infinite V] {D : Type} [Fintype D] [DecidableEq D] {d : ℕ}

theorem loopAtom_mem_class {M : Molecule V D} {R : ℕ} {Adm : (D → Fin d → ℤ) → Prop} {P0 : Finset V → ℝ} {C : CollData M}
    {Un : (D → Fin d → ℤ) → Set (Src.Object Src.γL M)} {Fst : Set (Src.Object Src.γL M)} {crit : V → Prop} {kFix : Finset (Mom d)}
    {L γ η : ℝ} {m : ℕ} (hD : LowLoopData M R Adm P0 C Un Fst crit kFix L γ η m) {lab : Finset V × (lowAtoms M → Option (Mom d))}
    {κ : D → Fin d → ℤ} (hκ : Adm κ) (hcl : InClass M L (0 : Mom d) kFix lab.1 lab.2 κ) {v : V} (hv : v ∈ loopAtoms M) :
    v ∈ lab.1 :=
  (hcl.1 v (Finset.mem_filter.1 hv).1).1 (loopAtom_tame hD.hSL (hD.heq κ hκ) (hD.degen κ hκ) hv)

theorem lowLoopClassHyps_unloop {M : Molecule V D} {R : ℕ} {Adm : (D → Fin d → ℤ) → Prop} {P0 : Finset V → ℝ} {C : CollData M}
    {Un : (D → Fin d → ℤ) → Set (Src.Object Src.γL M)} {Fst : Set (Src.Object Src.γL M)} {crit : V → Prop} {kFix : Finset (Mom d)}
    {L γ η : ℝ} {m : ℕ} (hD : LowLoopData M R Adm P0 C Un Fst crit kFix L γ η m) (hL0 : L ≠ 0)
    (hkle : ((M.loopBonds.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m)
    {Un' : (NonLoop M → Fin d → ℤ) → Set (Src.Object Src.γL M.unloop)}
    (hUn' : ∀ κ, Adm κ → Un' (fun y : NonLoop M => κ y.1) = unloopSet M (Un κ))
    (lab : Finset V × (lowAtoms M → Option (Mom d)))
    (hne : ∃ κ, Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ) :
    LowLoopClassHyps (d := d) M R (heredScale' M.unloop P0)
      {κ' | unloopAdm M (fun κ => Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ) κ'} C.unloop Un' (unloopSet M Fst) crit
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
    { subHypLoop := hD.hSL
      subHypL := hSU
      card_loopAtoms := card_loopAtoms_eq hD.hSL
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
      cnBound := cnBound_unloop_R hD.hFst (fun κ' ⟨κ, ⟨hκ, _⟩, e⟩ => ⟨κ, hκ, e⟩) hD.cn
      hostConnFL := ?_ }
  · intro a ha
    obtain ⟨c, hc⟩ := hD.pin a ha
    refine ⟨c, fun k0 hk0 => ?_⟩
    obtain ⟨κ, ⟨hκ, -⟩, rfl⟩ := hk0
    unfold chargeAt
    rw [sum_unloop_kvec M (hD.hmate κ hκ) a]
    exact hc κ hκ
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩
    exact SubproOblG.unloopL (hctx κ hκ) hD.hH (hD.obl κ hκ)
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩
    exact hunsel' κ hκ
  · rintro κ' ⟨κ, ⟨hκ, hcl⟩, rfl⟩
    refine DegenSGT.unloopL (hctx κ hκ) ?_
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
    exact loopAtom_mem_class hD hκ1 hcl1 hv
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
    refine desDisj_of_parts (C := C.unloop) (Un := Un' (fun y : NonLoop M => κ y.1)) (fun i j hij => hD.hC1 i j hij)
      (fun U hU i => ?_) (hd22' κ hκ) U U' hU hU'
    obtain ⟨h1, h2⟩ := hc2lift κ hκ U hU
    exact hD.hC12 κ hκ _ h2 i
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ U hU
    obtain ⟨U0, hU0, rfl⟩ := hU
    obtain ⟨i, rfl⟩ := hD.hFst U0 hU0
    exact Or.inl ⟨i, rfl⟩
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ U hU
    obtain ⟨hlf, hc2⟩ := hlift κ hκ U hU
    exact (Src.Object.lift_hasGapKind U hlf L γ η (0 : Mom d) κ .SG).1 (hD.sg2 κ hκ _ hc2)
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ U hU
    obtain ⟨hlf, hc2⟩ := hlift κ hκ U hU
    exact hingeData_unloop hD.hH hlf (hD.des2 κ hκ _ hc2)
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ U hU
    obtain ⟨hlf, hc2⟩ := hlift κ hκ U hU
    rcases hD.shape2 κ hκ _ hc2 with h | h
    · exact Or.inl h
    · right
      have := objVine_unloop _ hlf h
      rwa [Src.Object.unloop_lift U hlf hlf] at this
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ ps U a x b hps hpw hdis hUc hUat hax hxb hab hclos
    obtain ⟨c, hc, hc0⟩ := hdec' κ hκ
    exact hostConnL_of hMol' hc hc0 (hd22' κ hκ) (hvc' κ hκ) (hunsel' κ hκ) hnl' hC13' ps U a x b hps hpw hdis hUc hUat hax hxb
      hab hclos
  · rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ U hU a ha h1 h2
    obtain ⟨hlf, hc2⟩ := hlift κ hκ U hU
    exact hD.crit2 κ hκ _ hc2 a ha h1 h2
  · refine hostConnFL_of ?_
    rintro κ' ⟨κ, ⟨hκ, -⟩, rfl⟩ ps p hps hp hpF hpw
    obtain ⟨c, hc, hc0⟩ := hdec' κ hκ
    exact hostConnF_of hMol' hc hc0 (hd22' κ hκ) (hvc' κ hκ) (hunsel' κ hκ) hnl' hFstC' ps p hps hp hpF hpw


end main3

end WaveTurbulence.GammaLow.FinalCount.H
