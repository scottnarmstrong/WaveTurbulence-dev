/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntMember3
public import WaveTurbulence.Foundations.Flower.MkSlots.IntT4
public import WaveTurbulence.Foundations.Flower.MkUnits.WClass

/-! # B3s MK-SLOTS (integration, class sum): the class value of a capped fine′ class as a mode sum

* `member_integ`, `member_hsm`: the integrability and decoration-summability hypotheses of the pinned T4 for a member
  of the run class (PVBInteg's `_fix` lemmas with B3's regional bound, rewritten to the representative's shape data
  and the member's unit kernels).
* **`class_modes`**: the sum over the fine′ output set `T` of the frozen class summands is the `G_sb` dagger constant
  times the mode sum, over the combined family `capFam`, of the pinned outer values of `G_sb` with the class kernels
  `unitHkFW` of the run assembly (the pinned T4 `weightedClassFactorizationμ` applied to the member identity
  `member_skelVal` + `member_hasSum`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine WaveTurbulence.Flower.Stage1WNoVine
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.Flower.V5W
open WaveTurbulence.Flower.Stage1MKGate

namespace WaveTurbulence.Flower.MkSlots.IntMember

section Facts
variable (P : WTParams) (hL1 : 1 ≤ P.L) (hd1 : 1 ≤ P.d) {R p : ℕ} {kind : Bool}
  (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb : 0 ≤ b)
  (hB : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (Rf : Fin (2 * R) → Option ℝ) (tt : Fin (2 * R) → ℝ)
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hcanY : IsCanonGC (p + 1) y.1.layered) (hlay : ∀ x, stateLayer y.1 x ≤ p)

theorem uFam_bound (hb : 0 ≤ b) (hB : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) :
    ∀ (i : (uFam P h b).ι) q j j', q ≤ p →
      SNormR (40 * P.d) (40 * P.d) ((uFam P h b).h i q j j') ≤ ENNReal.ofReal ((uFam P h b).b i : ℝ) := by
  intro i q j j' hq
  show SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal (b.toNNReal : ℝ)
  rw [Real.coe_toNNReal b hb]
  exact hB q hq j j'

theorem frontierG_norm_le (Rf : Fin (2 * R) → Option ℝ) (j : Fin (2 * R)) (x : Mom P.d) :
    ‖frontierG (d := P.d) (Rf j) x‖ ≤ 1 := by
  unfold frontierG
  rw [Complex.norm_real, Real.norm_eq_abs]
  cases Rf j with
  | none => simp
  | some r =>
    simp only [Option.elim]
    rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
    exact XChain.ProductCut.chi0_le_one _

include hL1 hd1 hb hB hy hcanY hlay in
/-- The integrability hypothesis of the pinned T4 for a member. -/
theorem member_integ (amp : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → Mom P.d → ℂ)
    (frq : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → Fin 2 → ℤ)
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0)
    (fixSb : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree → Option ℝ) :
    Integrable (outerIntegrandM (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ 0 roots tt
      (a.normalizedPiece 0 (mk a.prime)).layer hG amp frq
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG)
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
        (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
        (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
      (fun j lam t k => unitRecenteredFW p
        (frontierG (Rf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1))
        none y.1 (y.2 j) P.L P.γ P.δ
        (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j)
        0 (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z) (fixMeasure fixSb) := by
  have h1 := integrable_outerIntegrandMG_fix (memShape a mk y hy)
    (memberRBMk a mk y (uFam P h b) hd1 hL1 0 hlay (uFam_bound P h b hb hB) (fun j => frontierG (Rf j)) 1 le_rfl
      (fun j x => frontierG_norm_le P Rf j x) ())
    (source_disjMk a mk y hy) y.1.data hG P.γ P.δ (stateLayer y.1) tt amp frq z fixSb
  rw [memShape_lay_eq a mk y hy, memShape_route a mk y hy hG, memShape_hclk a mk y hy,
    memShape_hmom a mk y hy] at h1
  simp only [member_ker_eqWMk a mk y hy _ _ _ _ _ _ hcanY hlay] at h1
  exact h1

include hL1 hd1 hb hB hy hcanY hlay in
/-- The decoration-summability hypothesis of the pinned T4 for a member. -/
theorem member_hsm (amp : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → Mom P.d → ℂ)
    (frq : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → Fin 2 → ℤ)
    (hsum : Summable fun z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0 =>
      ampBound hG P.L 0 amp z)
    (Zw : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (fixSb : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree → Option ℝ) :
    Summable (fun z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0 =>
      (splicedEpsilon (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G
          (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges z.1 : ℂ) * Zw z *
        ∫ τ, outerIntegrandM (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ 0 roots tt
          (a.normalizedPiece 0 (mk a.prime)).layer hG amp frq
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG)
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
            (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
            (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
          (fun j lam t k => unitRecenteredFW p
            (frontierG (Rf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1))
            none y.1 (y.2 j) P.L P.γ P.δ
            (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j)
            0 (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z τ ∂(fixMeasure fixSb)) := by
  have h1 := summable_outer_decorationsG_fix (memShape a mk y hy)
    (memberRBMk a mk y (uFam P h b) hd1 hL1 0 hlay (uFam_bound P h b hb hB) (fun j => frontierG (Rf j)) 1 le_rfl
      (fun j x => frontierG_norm_le P Rf j x) ())
    (source_disjMk a mk y hy) y.1.data hG P.γ P.δ (stateLayer y.1) tt amp frq Zw hZw hsum fixSb
  rw [memShape_lay_eq a mk y hy, memShape_hinges a mk y hy, memShape_route a mk y hy hG, memShape_hclk a mk y hy,
    memShape_hmom a mk y hy] at h1
  simp only [member_ker_eqWMk a mk y hy _ _ _ _ _ _ hcanY hlay] at h1
  exact h1

end Facts

/-- Layers of a member are at most `p`. -/
theorem member_lay {R p : ℕ} {a : PrescribedPrimeGarden (2 * R)} {mk : Stage1Mk.MarkFn (2 * R)}
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (J : Finset (Fin (2 * R)))
    (hGeoY : CapGeo y.1.layered J p) : ∀ x, stateLayer y.1 x ≤ p := by
  have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p := by
    rw [stateLayer_spec y.1]; exact hGeoY
  exact fun x => hGeoR.layer_le x

/-- **The class value of a capped fine′ class as a mode sum** with the class kernels `unitHkFW`. -/
theorem class_modes (P : WTParams) (hL1 : 1 ≤ P.L) (hd1 : 1 ≤ P.d) {R p : ℕ}
    {A : Finset (LayeredGarden (2 * R))} {mk mkF : Stage1Mk.MarkFn (2 * R)}
    (hFT : ∀ c : PrescribedPrimeGarden (2 * R), c.FineTransportedAt mkF)
    (π : PcA R p (objKind (2 * R)) A mkF) (a : PrescribedPrimeGarden (2 * R)) (hπ : repPt π = a)
    (hout : a.outputs (p := p) (kind := objKind (2 * R)) mk = a.outputs (p := p) (kind := objKind (2 * R)) mkF)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (J : Finset (Fin (2 * R))) (t s : ℝ) (hs : s ∈ Set.Ioo (p : ℝ) t) (ht : t ≤ p + 1)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hB : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (Rf : Fin (2 * R) → Option ℝ) (Rs : Fin (2 * R) → ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
    (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
      ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))
    (hGeoA : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
      J p)
    (fam₀ : SlotFam (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d)
    (hexp₀ : ∀ s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s'),
      ∀ x, HasSum (fun l => (fam₀.w s' l : ℂ) * fam₀.a s' l x * fsPhase (fam₀.m s' l) ts)
        (slotFW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) P.L P.γ P.δ h p
          (fun j => frontierG (Rf j))
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s')
          ts x))
    (pc : SourcePair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → SlotPiece P.d)
    (hpc : ∀ q, IsCapPair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G hG J q →
      ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
          (.inl q)),
      (pc q).val ts (latticePoint P.L (roots (capTreeOf _ hG J q))) =
        capSlotKer P.L P.γ P.δ p a J t s h roots Rf dag
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
            (.inl q)) ts (latticePoint P.L (roots (capTreeOf _ hG J q))))
    (hmem : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)),
      y ∈ sourceClass a p (objKind (2 * R)) mk → CapGeo y.1.layered J p ∧ IsCanonGC (p + 1) y.1.layered)
    (T : Finset (LayeredGarden (2 * R)))
    (hT : (T : Set (LayeredGarden (2 * R))) = a.outputs (p := p) (kind := objKind (2 * R)) mkF) :
    ∑ LG ∈ T, kernelKgenSel P.L P.γ P.δ LG (fixCap LG J (fun _ => FixPat.plain) t s) (offCap LG J dag.isSome)
        (markedWt P J p (fun _ => none) h Rf (fun _ => none) Rs dag LG) (fun _ => t) 0 roots
        (selPMk p (objKind (2 * R)) A P 0 roots mkF π LG) =
      capConstO a mk J P.L P.γ P.δ s roots dag *
        ∑' ξ : ∀ sl, (capFam hG J fam₀ pc).Λ sl, ((modeWt (capFam hG J fam₀ pc) ξ : ℝ) : ℂ) *
          outerValMμ (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ 0 roots (fun _ => t)
            (a.normalizedPiece 0 (mk a.prime)).layer (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges
            (fun z => (ZwG a mk J P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' roots dag z : ℂ)) hG
            (fixMeasure (fixAt J (fun _ => FixPat.plain) t s a (mk a.prime)))
            (fun sl => (capFam hG J fam₀ pc).a sl (ξ sl)) (fun sl => (capFam hG J fam₀ pc).m sl (ξ sl))
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG)
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
              (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
              (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
            (fun j lam t' k => unitHkFW P p (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
              (sourceLayer_isLayering a) (fun j => frontierG (Rf j))
              (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j) 0 lam
              t' k) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hall : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)),
      y ∈ sourceClass a p (objKind (2 * R)) mk →
      ∃ selSk : GenDecoration y.1.skeleton P.d roots 0 → Prop,
        kernelKgenSel P.L P.γ P.δ y.1.layered (fixCap y.1.layered J (fun _ => FixPat.plain) t s)
            (offCap y.1.layered J dag.isSome) (markedWt P J p (fun _ => none) h Rf (fun _ => none) Rs dag y.1.layered)
            (fun _ => t) 0 roots (selPMk p (objKind (2 * R)) A P 0 roots mkF π y.1.layered) =
          capConstO a mk J P.L P.γ P.δ s roots dag *
            skelValF y.1.data y.1.plain P.L P.γ P.δ 0 roots (fun _ => t) (stateLayer y.1) selSk
              (slotFnNWF y.1.data y.1.plain P.L P.γ P.δ
                (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
                  (stateLayer_isLayering y.1)) h P.L roots)
                (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
                (stateLayer y.1) (stateLayer_isLayering y.1)
                (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
                  (fun _ => FixPat.plain) t s))
              (fixCore y.1.data y.1.plain
                (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
                  (fun _ => FixPat.plain) t s)) ∧
        HasSum (fun ξ : ∀ sl, (capFam hG J fam₀ pc).Λ sl => ((modeWt (capFam hG J fam₀ pc) ξ : ℝ) : ℂ) *
            outerValMμ (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ 0 roots (fun _ => t)
              (a.normalizedPiece 0 (mk a.prime)).layer (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges
              (fun z => (ZwG a mk J P.L P.γ P.η hL0.ne' roots dag z : ℂ)) hG
              (fixMeasure (fixAt J (fun _ => FixPat.plain) t s a (mk a.prime)))
              (fun sl => (capFam hG J fam₀ pc).a sl (ξ sl)) (fun sl => (capFam hG J fam₀ pc).m sl (ξ sl))
              ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG)
              ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
                (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
              ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
                (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
              (fun j lam t' k => unitRecenteredFW p
                (frontierG (Rf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
                  j).upper.1.1))
                none y.1 (y.2 j) P.L P.γ P.δ
                (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j)
                0 (modW lam) (t' 0) (t' 1) (t' 2) (k 0) (k 1) (k 2) (k 3)))
          (skelValF y.1.data y.1.plain P.L P.γ P.δ 0 roots (fun _ => t) (stateLayer y.1) selSk
            (slotFnNWF y.1.data y.1.plain P.L P.γ P.δ
              (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
                h P.L roots)
              (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
              (stateLayer y.1) (stateLayer_isLayering y.1)
              (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
                (fun _ => FixPat.plain) t s))
            (fixCore y.1.data y.1.plain
              (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
                (fun _ => FixPat.plain) t s))) := by
    intro y hy
    obtain ⟨hGeoY, hcanY⟩ := hmem y hy
    obtain ⟨selSk, hZ, hval⟩ := member_skelVal P hL1 hd1 hFT π a hπ hout hG J t s hs ht h b hb hB roots Rf Rs dag
      hcapA hrepU y hy hGeoY
    exact ⟨selSk, hval, member_hasSum P hL1 hd1 a mk hG J t s hs ht h b hb hB roots Rf dag hcapA hrepU hGeoA fam₀
      hexp₀ pc hpc y hy hGeoY hcanY selSk hZ⟩
  have key := weightedClassFactorizationμ a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    (sourceAssemblyMk a mk) (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
    a.prime.prime T (sourceClass_hTMk a mk T (hT.trans hout.symm))
    (fun LG => kernelKgenSel P.L P.γ P.δ LG (fixCap LG J (fun _ => FixPat.plain) t s) (offCap LG J dag.isSome)
        (markedWt P J p (fun _ => none) h Rf (fun _ => none) Rs dag LG) (fun _ => t) 0 roots
        (selPMk p (objKind (2 * R)) A P 0 roots mkF π LG))
    (fun _ : Unit => capConstO a mk J P.L P.γ P.δ s roots dag) (Ξ := ∀ sl, (capFam hG J fam₀ pc).Λ sl)
    (fun _ ξ => ((modeWt (capFam hG J fam₀ pc) ξ : ℝ) : ℂ))
    (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ 0 roots (fun _ => t)
    (a.normalizedPiece 0 (mk a.prime)).layer (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges
    (fun z => (ZwG a mk J P.L P.γ P.η hL0.ne' roots dag z : ℂ)) hG
    (fixMeasure (fixAt J (fun _ => FixPat.plain) t s a (mk a.prime)))
    (fun _ ξ sl x => (capFam hG J fam₀ pc).a sl (ξ sl) x) (fun _ ξ sl => (capFam hG J fam₀ pc).m sl (ξ sl))
    ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG)
    ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
      (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
    ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
      (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
    (fun _ j => unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j)
    (fun j => frontierG (Rf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1))
    (fun _ => none)
    (fun y hy => by
      obtain ⟨selSk, hval, hsum⟩ := hall y hy
      rw [hval, ← hsum.tsum_eq, Fintype.sum_unique])
    (fun _ y hy => by
      obtain ⟨selSk, -, hsum⟩ := hall y hy
      exact hsum.summable)
    (fun _ ξ y hy z => member_integ P hL1 hd1 a mk hG h b ((hmem y hy).1 |> fun _ => hb) hB roots Rf (fun _ => t) y hy
      (hmem y hy).2 (member_lay y J (hmem y hy).1) _ _ z _)
    (fun _ ξ y hy => member_hsm P hL1 hd1 a mk hG h b hb hB roots Rf (fun _ => t) y hy (hmem y hy).2
      (member_lay y J (hmem y hy).1) _ _ (tsum_ampBound_mode_le (capFam hG J fam₀ pc) hG P.L hL0 0 roots ξ).1 _
      (fun z => by
        rw [Complex.norm_real, Real.norm_of_nonneg (ZwG_mem a mk J P.L P.γ P.η hL0.ne' roots dag z).1]
        exact (ZwG_mem a mk J P.L P.γ P.η hL0.ne' roots dag z).2) _)
  rw [key, Fintype.sum_unique]
  rfl

end WaveTurbulence.Flower.MkSlots.IntMember
