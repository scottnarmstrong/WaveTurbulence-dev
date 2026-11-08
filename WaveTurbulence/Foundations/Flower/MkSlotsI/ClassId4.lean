/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassId3

/-! # B3s-HELPER7 ClassId (part 4): the consumed momenta and the superpositions of a member

* `ConsG` (non-centred slots: the lattice momenta at base `0` with the cap momentum on cap pairs and the root label on
  root chain slots), `ConsCG` (centred slots: the lattice momenta at base `0`);
* **`member_hcons`**: every skeleton decoration of a member consumes its outer slot momenta in `ConsG`
  (`genDec_capPair`, α's `isCapPair_iota`/`capTreeOf_iota`, the root labels of a decoration);
* **`member_hexp₀`**, **`member_hexpC`**: VBC4's `hexp₀`/`hexpC'` for the families `fam₀Of sd _`, `famCOfData sd` of
  `SlotDataOK` on the box `genBoxAt … ∩ TopCut …` (RSlot's `member_genSlot`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.Flower.MkSlots (anchProfiles chainW fixCore recLG IsCapPair capTreeOf)
open WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic

namespace WaveTurbulence.Flower.MkSlotsI

variable {w : ℕ}

/-- **The consumed momenta of a non-centred outer slot**: lattice points at base `0`, the cap momentum on a cap pair,
the root label on a root chain slot (the clauses of `SlotDataOK.hasSum`). -/
def ConsG {d : ℕ} (L : ℝ) (a : PrescribedPrimeGarden w) (J : Finset (Fin w)) (roots : Fin w → (Fin d → ℤ))
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G)
    (x : Mom d) : Prop :=
  ∃ n : Fin d → ℤ, x = 0 + latticePoint L n ∧
    (∀ q, iotaAt a Mk s' = .inl q → IsCapPair a.prime.skeleton a.prime.prime.1 J q →
      n = roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)) ∧
    (∀ β : GBranch a.prime.skeleton.tree, iotaAt a Mk s' = .inr β → β.1.2 = [] → n = roots β.1.1)

/-- The consumed momenta of a centred slot: lattice points at base `0`. -/
def ConsCG {d : ℕ} (L : ℝ) {G : Garden w} (_c : CentredSlot G) (x : Mom d) : Prop :=
  ∃ n : Fin d → ℤ, x = 0 + latticePoint L n

/-- The slot box of VBC4 for the slot obligation: `genBoxAt` and the top-pin cut of the representative's slot. -/
def boxG (p : ℕ) (a : PrescribedPrimeGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G) :
    Set (Fin 2 → ℝ) :=
  genBoxAt p a J pat t s (iotaAt a Mk s') ∩ {ts | TopCut a J pat t s (iotaAt a Mk s') ts}

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain) (J : Finset (Fin (2 * R)))

include hy hG in
/-- **Every skeleton decoration of a member consumes its outer slot momenta in `ConsG`.** -/
theorem member_hcons {d : ℕ} (L : ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (hcapS : ∀ j ∈ J, y.1.skeleton.tree j = TTree.leaf)
    (κ : GenDecoration y.1.skeleton d roots 0)
    (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) :
    ConsG L a J roots (mk a.prime) s'
      (0 + latticePoint L (κ.1 (slotNode y.1.plain ((memShape a mk y hy).iota y.1.plain hG s')))) := by
  refine ⟨_, rfl, ?_, ?_⟩
  · intro q' hq' hcap
    cases s' with
    | inl q =>
      have e : q' = pairOfLeaf a.prime.skeleton a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf (q.firstLeaf hG)) :=
        (Sum.inl_injective hq').symm
      subst e
      have hqG := (MkSlots.IntMember.isCapPair_iota
        (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) a.prime.prime.1 hG J q).mp hcap
      have hqy := (MkSlots.IntMember.isCapPair_iota (memShape a mk y hy) y.1.plain hG J q).mpr hqG
      show κ.1 ((pairOfLeaf y.1.skeleton y.1.plain ((memShape a mk y hy).leaf (q.firstLeaf hG))).firstLeaf
        y.1.plain).toNode = _
      rw [genDec_capPair y.1.skeleton y.1.plain J hcapS κ _ hqy,
        MkSlots.IntMember.capTreeOf_iota (memShape a mk y hy) y.1.plain hG J q,
        MkSlots.IntMember.capTreeOf_iota
          (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) a.prime.prime.1 hG J q]
    | inr c => cases hq'
  · intro β hβ hβr
    cases s' with
    | inl q => cases hβ
    | inr c =>
      have e : β = (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c :=
        (Sum.inr_injective hβ).symm
      subst e
      have hc := (MkSlotsB.br_root_iff _ c).mp hβr
      have hy0 := (MkSlotsB.br_root_iff (memShape a mk y hy) c).mpr hc
      show κ.1 ((memShape a mk y hy).br c).toNode = _
      have hn : ((memShape a mk y hy).br c).toNode = GNode.root y.1.skeleton.tree ((memShape a mk y hy).br c).1.1 :=
        Subtype.ext (Prod.ext rfl hy0)
      rw [hn, κ.2.2.1, MkSlots.IntCore.br_fst, MkSlots.IntCore.br_fst]

variable (hGeoA : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
    J p)
  (hGeoY : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p)
  (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
      (a.prime.data.coreBranch a.prime.prime.1 b) = none)

include hy hG hGeoA hGeoY hrepUP in
/-- **VBC4's `hexp₀`** for the leaf-pair / root-chain family `fam₀Of sd _` of `SlotDataOK`. -/
theorem member_hexp₀ {Kg : ℕ → ℝ → ℝ} {P : WTParams} {C : ℝ} (kSel σ : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (b : ℝ) (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (hstem : StemDep σ kSel → CleanPt J a)
    (sd : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → (Fin P.d → ℤ) → SlotDatum P.d)
    (hsd : SlotDataOK Kg P C p a J pat t s kSel σ Rs roots h b Rf dag (mk a.prime) sd)
    (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (hnc : ¬ IsCentred s')
    (ts : Fin 2 → ℝ) (hts : ts ∈ boxG p a J pat t s (mk a.prime) s') (x : Mom P.d)
    (hx : ConsG P.L a J roots (mk a.prime) s' x) :
    HasSum (fun l => ((fam₀Of sd hsd.supp).w s' l : ℂ) * (fam₀Of sd hsd.supp).a s' l x *
        fsPhase ((fam₀Of sd hsd.supp).m s' l) ts)
      (MkSlotsB.slotFnGWFRL y.1.data y.1.plain P.L P.γ P.δ
        (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) h P.L
          roots)
        (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
        (genΘs y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs)
        (stateLayer y.1) (stateLayer_isLayering y.1)
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)
        ((memShape a mk y hy).iota y.1.plain hG s') ts x) := by
  obtain ⟨n, rfl, hcap, hroot⟩ := hx
  rw [member_genSlot a mk y hy hG J hGeoA hGeoY pat t s hrepUP P.L P.γ P.δ σ kSel Rs h roots Rf dag hstem s',
    zero_add]
  refine hsd.hasSum s' 0 ts hts.1 hts.2 n hcap hroot ?_
  intro β hβ hβne
  exfalso
  cases s' with
  | inl q => cases hβ
  | inr c =>
    have e : β = (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c :=
      (Sum.inr_injective hβ).symm
    subst e
    have hc : c.1.2 = [] := by
      by_contra hc
      exact hnc hc
    exact hβne ((MkSlotsB.br_root_iff _ c).mpr hc)

include hy hG hGeoA hGeoY hrepUP in
/-- **VBC4's `hexpC'`** for the centred chain pieces `famCOfData sd` of `SlotDataOK`. -/
theorem member_hexpC {Kg : ℕ → ℝ → ℝ} {P : WTParams} {C : ℝ} (kSel σ : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (b : ℝ) (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (hstem : StemDep σ kSel → CleanPt J a)
    (sd : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → (Fin P.d → ℤ) → SlotDatum P.d)
    (hsd : SlotDataOK Kg P C p a J pat t s kSel σ Rs roots h b Rf dag (mk a.prime) sd)
    (c : CentredSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (y0 : Fin P.d → ℤ)
    (ts : Fin 2 → ℝ) (hts : ts ∈ boxG p a J pat t s (mk a.prime) (.inr c.1)) (x : Mom P.d)
    (hx : ConsCG P.L c x) (hball : ‖x - latPt P.d y0‖ ≤ 1) :
    HasSum (fun l => ((famCOfData sd c y0).w l : ℂ) * (famCOfData sd c y0).a l x *
        fsPhase ((famCOfData sd c y0).m l) ts)
      (MkSlotsB.slotFnGWFRL y.1.data y.1.plain P.L P.γ P.δ
        (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) h P.L
          roots)
        (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
        (genΘs y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs)
        (stateLayer y.1) (stateLayer_isLayering y.1)
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)
        ((memShape a mk y hy).iota y.1.plain hG (.inr c.1)) ts x) := by
  obtain ⟨n, rfl⟩ := hx
  rw [zero_add] at hball
  rw [member_genSlot a mk y hy hG J hGeoA hGeoY pat t s hrepUP P.L P.γ P.δ σ kSel Rs h roots Rf dag hstem (.inr c.1),
    zero_add]
  refine hsd.hasSum (.inr c.1) y0 ts hts.1 hts.2 n (fun q hq => by cases hq) ?_ (fun _ _ _ => hball)
  intro β hβ hβr
  exfalso
  have e : β = (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c.1 :=
    (Sum.inr_injective hβ).symm
  subst e
  exact c.2 ((MkSlotsB.br_root_iff _ c.1).mp hβr)

include hy hG hrepUP in
/-- **VBC4's `hbox`** for the box `boxG = genBoxAt … ∩ TopCut …`: on the pinned relaxed core domain of a member with
the lower bounds `lbS`, the slot times of every outer slot lie in the representative's general box and satisfy its
top-pin cut. -/
theorem member_hbox (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
    (hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf) (hst : s < t)
    (htt : t ∈ Set.Icc (p : ℝ) (p + 1))
    (hRP : MkSlotsB.RelaxPins
      (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)).layer (fun _ => t)
      (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s))
    (hlbclk : ∀ (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (i : Fin 2)
      (by' : GBranch y.1.skeleton.tree) (ba : GBranch a.prime.skeleton.tree),
      argSrc y.1.plain ((memShape a mk y hy).iota y.1.plain hG s') i = .inr by' →
      argSrc a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s') i
        = .inr ba →
      MkSlotsB.lbS y.1.data y.1.plain
          (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s
          by' =
        MkSlotsB.lbS a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) s ba) :
    ∀ τ, MkSlotsB.PinnedAt (fixCore y.1.data y.1.plain
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)) τ →
      τ ∈ MkSlotsB.coreTimeDomainWR (fun b => stateLayer y.1 (y.1.data.coreBranch y.1.plain b).toNode) (fun _ => t)
          (fixCore y.1.data y.1.plain
            (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)) ∩
        MkSlotsB.lbDomR (MkSlotsB.lbS y.1.data y.1.plain
          (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s) →
      ∀ s', slotTs y.1.plain (fun _ => t) τ ((memShape a mk y hy).iota y.1.plain hG s') ∈
        boxG p a J pat t s (mk a.prime) s' := by
  intro τ hpin hτ s'
  refine ⟨?_, member_topCut a mk y hy hG J hcapA hcapY pat t s hrepUP hst hlbclk τ hpin hτ.2 s'⟩
  show _ ∈ genSlotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1
    (fun _ => t) (fixCore a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s))
    ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s')
  rw [← genSlotBox_member a mk y hy hG J hcapA hcapY pat t s hrepUP (fun _ => t) s']
  exact slotTs_mem_genSlotBox p _ y.1.plain (fun _ => t) (fun _ => htt) _
    (fun b v hv => ⟨(hRP.val _ v hv).1, (hRP.val _ v hv).2.1⟩) τ hpin.pin hτ.1 _

end Class

end WaveTurbulence.Flower.MkSlotsI
