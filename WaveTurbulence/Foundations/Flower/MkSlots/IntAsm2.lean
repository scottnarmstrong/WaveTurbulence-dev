/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntAsm1
public import WaveTurbulence.Foundations.Flower.MkSlots.EngVN
public import WaveTurbulence.Foundations.Flower.MkSlots.SliceSb
public import WaveTurbulence.Foundations.Flower.MkSlots.GeoSb
public import WaveTurbulence.Foundations.Flower.MkSlots.Geo

/-! # B3s MK-SLOTS (integration, assembly 2): the cap pieces and the α piece's engine data

* `exists_capPieces`: `CapSlotObligationAt` at the representative gives, on every cap pair of `G_sb`, a slot piece
  whose value at the cap momentum is the representative's pinned cap slot kernel on the slot box, with the B3 slot
  mass times the protected loss `L^{31d+6}`;
* `pieceAtomW_pieceAt`: the atom weight of the α piece times the gap selection is the `G_sb` weight `ZwG`;
* `admissibleAt`: the pins of the α piece at any marked set equal to `classMk mkF a` are admissible (the engine's
  slice hypothesis by `SliceSb.mem_splicedTimeDomain_slice`);
* `rep_units_not_cfp`: no core of an atom of a unit of the representative is a capped flower parent
  (`Geo.fixCap_coreBranch_unit`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree MeasureTheory Set
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine WaveTurbulence.Flower.Stage1WNoVine
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.Flower.V5W
open WaveTurbulence.Flower.Stage1MKGate

namespace WaveTurbulence.Flower.MkSlots.IntAsm

open WaveTurbulence.Flower.MkSlots.IntMember WaveTurbulence.Flower.MkSlots.IntCore

/-- **The cap pieces of the representative** from the isolated cap-slot obligation. -/
theorem exists_capPieces (P : WTParams) (Kc : ℕ → ℝ → ℝ) (hob : CapSlotObligationAt Kc P) (C : ℝ)
    (hC : P.C₁ ≤ C) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain) (J : Finset (Fin (2 * R))) (t s : ℝ)
    (hp : p < P.D) (hcan : IsCanonGC (p + 1) a.layered) (hsz : a.prime.data.size ≤ P.N (p + 1) ^ 4)
    (hGeo : CapGeo a.layered J p) (hirr : a.layered.garden.Irreducible) (ht : t ∈ Ioo (p : ℝ) (p + 1))
    (hs : s ∈ Ioo (p : ℝ) t) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb : 1 ≤ b)
    (hB : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (Rf : Fin (2 * R) → Option ℝ) (hRf : ∀ j r, Rf j = some r → P.L / 2 ≤ r)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) :
    ∃ pc : SourcePair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → SlotPiece P.d,
      (∀ q, IsCapPair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G hG J q →
        ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
          a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
            (.inl q)),
        (pc q).val ts (latticePoint P.L (roots (capTreeOf _ hG J q))) =
          capSlotKer P.L P.γ P.δ p a J t s h roots Rf dag
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
              (.inl q)) ts (latticePoint P.L (roots (capTreeOf _ hG J q)))) ∧
      (∀ q, IsCapPair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G hG J q →
        ∑' l, maxBracketPow P.η (half ((pc q).m l)) * ENNReal.ofReal ((pc q).w l) ≤
          ENNReal.ofReal (Kc P.d P.η * (C * Real.sqrt P.δ) ^ slotSize a.prime.data
              ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
                (.inl q)) *
            P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
              ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
                (.inl q)) : ℝ)) *
            (frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1
                ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
                  (.inl q)) *
              (b⁻¹ * slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
                (fun _ => b.toNNReal)
                ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
                  (.inl q)))) *
            P.L ^ (31 * (P.d : ℝ) + 6))) := by
  have key : ∀ q : SourcePair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G, ∃ pcq : SlotPiece P.d,
      IsCapPair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G hG J q →
        (∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
          a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
            (.inl q)),
        pcq.val ts (latticePoint P.L (roots (capTreeOf _ hG J q))) =
          capSlotKer P.L P.γ P.δ p a J t s h roots Rf dag
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
              (.inl q)) ts (latticePoint P.L (roots (capTreeOf _ hG J q)))) ∧
        ∑' l, maxBracketPow P.η (half (pcq.m l)) * ENNReal.ofReal (pcq.w l) ≤
          ENNReal.ofReal (Kc P.d P.η * (C * Real.sqrt P.δ) ^ slotSize a.prime.data
              ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
                (.inl q)) *
            P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
              ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
                (.inl q)) : ℝ)) *
            (frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1
                ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
                  (.inl q)) *
              (b⁻¹ * slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
                (fun _ => b.toNNReal)
                ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
                  (.inl q)))) *
            P.L ^ (31 * (P.d : ℝ) + 6)) := by
    intro q
    by_cases hq : IsCapPair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G hG J q
    · have hqa := (isCapPair_iota (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
        a.prime.prime.1 hG J q).mpr hq
      obtain ⟨Λ, hΛ, wt, m, c, amp, hw, hws, ha1, has, hasupp, hsum, hmass⟩ :=
        hob C hC a J t s hp hcan hsz hGeo hirr ht hs roots h b hb hB Rf hRf dag _ hqa
      refine ⟨⟨Λ, hΛ, wt, m, c, amp, hw, hws, ha1, has, hasupp⟩, fun _ => ⟨fun ts hts => ?_, hmass⟩⟩
      rw [← capTreeOf_iota (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
        a.prime.prime.1 hG J q]
      exact (hsum ts hts).tsum_eq
    · exact ⟨SlotPiece.empty P.d, fun h' => absurd h' hq⟩
  choose pc hpc using key
  exact ⟨pc, fun q hq => (hpc q hq).1, fun q hq => (hpc q hq).2⟩

/-- **The atom weight of the α piece times the gap selection is `ZwG`.** -/
theorem pieceAtomW_pieceAt (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (t s : ℝ)
    (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (hL : P.L ≠ 0) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0) :
    pieceAtomW (pieceAt P J t s (fun _ => none) a (mk a.prime) dag)
        (cosetDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L 0 z.1) *
      (if selSkCMk a mk P.L P.γ P.η hL 0 roots z then 1 else 0) =
    ((ZwG a mk J P.L P.γ P.η hL roots dag z : ℝ) : ℂ) := by
  unfold pieceAtomW ZwG
  simp only [pieceAt, MkSubpro.stage1PieceMKOf, Option.elim, Finset.prod_const_one, one_mul]
  split_ifs <;> push_cast <;> ring

/-- **The pins of the α piece are admissible** at every marked set equal to the class marking. -/
theorem admissibleAt {R : ℕ} (J : Finset (Fin (2 * R))) (p : ℕ) (mkF : Stage1Mk.MarkFn (2 * R))
    (a : PrescribedPrimeGarden (2 * R)) (hG : CapGeo a.layered J p) (t s : ℝ) (hs : s ∈ Ioo (p : ℝ) t)
    (ht : t < p + 1) (Mk : Set (Stage1.CLVine a.prime.skeleton)) (hMk : Mk = classMk mkF a) :
    AdmissibleSb (stM a Mk).G (fun c => a.layered.layer (coreAt a Mk c).toNode) (fun _ => t)
      (fixAt J (fun _ => FixPat.plain) t s a Mk) := by
  subst hMk
  exact admissibleSb_plain J p mkF a hG t s hs ht

/-- **No core of an atom of a unit of the representative is a capped flower parent.** -/
theorem rep_units_not_cfp {R : ℕ} (J : Finset (Fin (2 * R))) (t s : ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG),
      markI J (fun _ => FixPat.plain) t s (fun _ => none) B ⊆ mkF B)
    (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) (hset : mk a.prime = mkAt mkF a)
    (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) (b : GBranch a.prime.skeleton.tree)
    (hb : b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms) :
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b) := by
  intro hcfp
  have hu : unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j ∈
      unitBlocks a.prime.skeleton a.totalSigma (classMk mkF a) := by
    show _ ∈ unitBlocks a.prime.skeleton a.totalSigma (mkAt mkF a)
    rw [← hset]
    exact List.get_mem _ _
  have h0 := fixCap_coreBranch_unit (fun _ => FixPat.plain) t s (fun _ => none) mkF hsub a hu hb
  rw [fixCap_plain, if_pos ((cfp_decoded_iff a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    a.layered (sourceLayer_reconstructs a) a.prime.decodes J b).mpr hcfp)] at h0
  exact Option.some_ne_none _ h0

end WaveTurbulence.Flower.MkSlots.IntAsm
