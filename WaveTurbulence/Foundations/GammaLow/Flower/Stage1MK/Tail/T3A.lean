/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Bridge
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.Flower.MkSubpro.Survivors
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Assembly
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Pieces
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Prefix
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.SurvCount
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Unclean
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceTripleDesigMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossMK
public import WaveTurbulence.Foundations.Vine.A.VineHingePairMK
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK3
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK4
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK5
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK2
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK3
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvPairMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvSGMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupExtension
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkFn
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P6
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P7
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P8
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P9
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P10
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P11
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P12
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P13
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P14
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P15
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Iface

/-! # FLOWER-LOW item I tail (packet L8-I-TAIL), part 3A (helper wt-l6htv): marked Stage-1′ declarations over `𝒱_γ`

I-BASE/I-GATE declarations deferred by L8's generated waves (`tools/itool/tail.json` key `deferred`), copied by source
(sha256 in COPIED-SHA256SUMS) with L8's `gen_i_spec.py` (copy of wt-l5ag's `itail`) and fixed by hand; claim:
`Tail/PROGRESS.md` CLAIM wt-l6htv. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.RedSplice Finset
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable {G : Garden w} {S : Finset (GBranch G.tree)} {Mk : Set (Fama.CLVineG γF G)}

/-- **At most one survivor of a marked group is not a vine of `𝒱`**: two such have the same atoms. -/
theorem surv_nonV_fst_eqLow (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (U : Fama.MarkedGroupUnits γF G S Mk)
    {t t' : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ U.surv) (ht' : t' ∈ U.surv)
    (hn : ∀ c ∈ Fama.vinesVG γF G, c.atoms ≠ t.1) (hn' : ∀ c ∈ Fama.vinesVG γF G, c.atoms ≠ t'.1) : t.1 = t'.1 := by
  obtain ⟨D', _, _, N, L, a, b, -, hs, -, -, hv, hi, -, hsub, -⟩ := U.surv_spine
  have hblk : ∀ T p q, (T, p, q) ∈ L → G.molecule.IsBlock T p q :=
    fun T p q h => Src.isBlock_of_isSomeVine (hv (T, p, q) h)
  have htL := hsub.subset ht
  have htL' := hsub.subset ht'
  have hvt := hv t htL
  have hvt' := hv t' htL'
  have hit := hi t htL
  have hit' := hi t' htL'
  -- a non-(CN) non-𝒱 survivor gives a (CL) vine outside `𝒱`
  have clcase : ∀ u ∈ L, (∀ c ∈ Fama.vinesVG γF G, c.atoms ≠ u.1) → ¬ CNMem G u →
      ∃ c : Fama.CLVineG γF G, c.atoms = u.1 ∧ c ∉ Fama.vinesVG γF G := by
    intro u hu hnu hcn
    obtain ⟨c, hc, -⟩ := Fama.exists_clVine (hv u hu) hcn
    exact ⟨c, hc, fun hcV => hnu c hcV hc⟩
  have cnV : ∀ u ∈ L, CNMem G u → ∃ T, Fama.IsIngredientG γF G.molecule S T ∧ Fama.IsCNVineG γF G T :=
    fun u hu hcn => ⟨u.1, hi u hu, u.2.1, u.2.2, hv u hu, hcn.1, hcn.2⟩
  by_cases hc1 : CNMem G t <;> by_cases hc2 : CNMem G t'
  · exact congrArg Prod.fst (hs.cn_unique hblk htL htL' hc1 hc2)
  · obtain ⟨c', hc', hc'V⟩ := clcase t' htL' hn' hc2
    exact ((top_of_not_vinesVLow hS (hc' ▸ hit') hc'V).1 (cnV t htL hc1)).elim
  · obtain ⟨c, hc, hcV⟩ := clcase t htL hn hc1
    exact ((top_of_not_vinesVLow hS (hc ▸ hit) hcV).1 (cnV t' htL' hc2)).elim
  · obtain ⟨c, hc, hcV⟩ := clcase t htL hn hc1
    obtain ⟨c', hc', hc'V⟩ := clcase t' htL' hn' hc2
    have h1 := (top_of_not_vinesVLow hS (hc ▸ hit) hcV).2
    have h2 := (top_of_not_vinesVLow hS (hc' ▸ hit') hc'V).2
    by_contra hne
    exact Fama.top_unique h1 h2 (hc ▸ hit) (hc' ▸ hit') (by rw [hc, hc']; exact hne)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.RedSplice Finset
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable {G : Garden w} {S : Finset (GBranch G.tree)} {Mk : Set (Fama.CLVineG γF G)}

/-- **The survivors of one marked group**: at most `2·#(marked 𝒱-ingredients)`. -/
theorem surv_length_leLow (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (U : Fama.MarkedGroupUnits γF G S Mk)
    (hmk : Fama.markedGroup γF G Mk S) : U.surv.length ≤ 2 * (mkIngrLow G Mk S).card := by
  obtain ⟨c₀, hc₀, hc₀V, hc₀I⟩ := hmk
  have hc₀m : c₀ ∈ mkIngrLow G Mk S := by
    simp only [mkIngrLow, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hc₀, hc₀V, hc₀I⟩
  let P1 : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree → Prop :=
    fun t => ∃ c ∈ Mk, c ∈ Fama.vinesVG γF G ∧ c.atoms = t.1
  have hsplit := List.length_eq_countP_add_countP (fun t => decide (P1 t)) (l := U.surv)
  -- marked survivors inject into the marked ingredients
  have h1 : U.surv.countP (fun t => decide (P1 t)) ≤ (mkIngrLow G Mk S).card := by
    rw [List.countP_eq_length_filter]
    have hnd := (surv_nodupLow U).filter (fun t => decide (P1 t))
    rw [← List.toFinset_card_of_nodup hnd]
    let f : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree → Fama.CLVineG γF G :=
      fun t => if h : P1 t then h.choose else c₀
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro t ht
      have ht' := List.mem_toFinset.1 ht
      obtain ⟨htm, hp⟩ := List.mem_filter.1 ht'
      have hp' : P1 t := of_decide_eq_true hp
      simp only [f, hp', ↓reduceDIte]
      obtain ⟨hcMk, hcV, hca⟩ := hp'.choose_spec
      simp only [mkIngrLow, Finset.coe_filter, Set.Finite.mem_toFinset]
      exact ⟨hcMk, hcV, by rw [hca]; exact (U.surv_spec t htm).2.1⟩
    · intro t ht t' ht' he
      have hm := List.mem_filter.1 (List.mem_toFinset.1 ht)
      have hm' := List.mem_filter.1 (List.mem_toFinset.1 ht')
      have hp : P1 t := of_decide_eq_true hm.2
      have hp' : P1 t' := of_decide_eq_true hm'.2
      simp only [f, hp, hp', ↓reduceDIte] at he
      have e1 := hp.choose_spec.2.2
      have e2 := hp'.choose_spec.2.2
      by_contra hne
      exact surv_fst_neLow U hm.1 hm'.1 hne (by rw [← e1, ← e2, he])
  -- at most one survivor is not a vine of `𝒱`
  have h2 : U.surv.countP (fun t => decide ¬ (decide (P1 t)) = true) ≤ 1 := by
    rw [List.countP_eq_length_filter]
    have hpw : (U.surv.filter (fun t => decide ¬ (decide (P1 t)) = true)).Pairwise (fun t t' => t.1 ≠ t'.1) := by
      refine List.Pairwise.imp_of_mem ?_ ((surv_nodupLow U).sublist List.filter_sublist)
      intro a b ha hb hab
      exact surv_fst_neLow U (List.mem_filter.1 ha).1 (List.mem_filter.1 hb).1 hab
    have hnV : ∀ t ∈ U.surv.filter (fun t => decide ¬ (decide (P1 t)) = true), ∀ c ∈ Fama.vinesVG γF G, c.atoms ≠ t.1 := by
      intro t ht
      obtain ⟨htm, hnp⟩ := List.mem_filter.1 ht
      have hnp' : ¬ P1 t := by simpa using hnp
      rcases (U.surv_spec t htm).2.2 with hm | hm
      · exact (hnp' hm).elim
      · exact hm
    match hl : U.surv.filter (fun t => decide ¬ (decide (P1 t)) = true), hpw, hnV with
    | [], _, _ => simp
    | [_], _, _ => simp
    | a :: b :: l, hp, hn =>
      have hab := (List.pairwise_cons.1 hp).1 b (by simp)
      have ha : a ∈ U.surv := (List.mem_filter.1 (hl ▸ (by simp : a ∈ a :: b :: l))).1
      have hb : b ∈ U.surv := (List.mem_filter.1 (hl ▸ (by simp : b ∈ a :: b :: l))).1
      exact (hab (surv_nonV_fst_eqLow hS U ha hb (hn a (by simp)) (hn b (by simp)))).elim
  have hpos : 1 ≤ (mkIngrLow G Mk S).card := Finset.card_pos.2 ⟨c₀, hc₀m⟩
  omega

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.RedSplice Finset
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- **The survivor count (F-B4-6)**: the marked splice has at most `2·#Mk` survivors. -/
theorem survivorsMk_length_leLow (G : Garden w) (σ : Prescription G) (Mk : Set (Fama.CLVineG γF G)) :
    (Fama.survivorsMk γF G σ Mk).length ≤ 2 * Mk.ncard := by
  unfold Fama.survivorsMk
  rw [List.length_flatMap]
  have hgr : ∀ S ∈ Fama.sgGroups γF G σ, (if Fama.markedGroup γF G Mk S then (if h : Nonempty (Fama.MarkedGroupUnits γF G S Mk) then
      (Classical.choice h).surv else []) else []).length ≤ 2 * (mkIngrLow G Mk S).card := by
    intro S hS
    have hSm := (Fama.mem_sgGroups.1 hS).1
    split_ifs with hmk hne
    · exact surv_length_leLow hSm _ hmk
    · simp
    · simp
  refine (List.sum_le_sum hgr).trans ?_
  have hnd : (Fama.sgGroups γF G σ).Nodup := by
    unfold Fama.sgGroups
    exact (Finset.nodup_toList _).filter _
  rw [List.sum_map_mul_left, ← List.sum_toFinset _ hnd]
  have hdisj : ((Fama.sgGroups γF G σ).toFinset : Set (Finset (GBranch G.tree))).PairwiseDisjoint (mkIngrLow G Mk) := by
    intro S hS S' hS' hne
    exact mkIngr_disjointLow Mk (Fama.mem_sgGroups.1 (List.mem_toFinset.1 hS)).1
      (Fama.mem_sgGroups.1 (List.mem_toFinset.1 hS')).1 hne
  rw [← Finset.card_biUnion hdisj]
  have hsub : (Fama.sgGroups γF G σ).toFinset.biUnion (mkIngrLow G Mk) ⊆ (Set.toFinite Mk).toFinset := by
    intro c hc
    obtain ⟨S, -, hc⟩ := Finset.mem_biUnion.1 hc
    exact (Finset.mem_filter.1 hc).1
  have := Finset.card_le_card hsub
  rw [← Set.ncard_eq_toFinset_card Mk (Set.toFinite Mk)] at this
  omega

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- **The survivor count of a non-zero class piece**: `m ≤ 6·|Π(rep)|`. -/
theorem classPiece_surv_leLow (P : WTParams) [Fact (P.γ ≤ 1 / 2)] {R : ℕ} {J : Finset (Fin (2 * R))} {pat : Fin (2 * R) → FixPat}
    {t s : ℝ} {kSel σ : Fin (2 * R) → Option ℕ} {mkF : Fama.Stage1Mk.MarkFn P.γ (2 * R)}
    (hF : FineMarkingLow J pat t s kSel σ mkF) (a : Fama.VineA.PrescribedPrimeGarden P.γ (2 * R)) (hnz : ¬ StemDep σ kSel ∨ CleanPtLow J a)
    (prot : Finset (GBranch (Fama.stSt P.γ a.prime.skeleton a.totalSigma (classMkLow mkF a)).G.tree))
    (fix : GBranch (Fama.stSt P.γ a.prime.skeleton a.totalSigma (classMkLow mkF a)).G.tree → Option ℝ)
    (filt : GBranch (Fama.stSt P.γ a.prime.skeleton a.totalSigma (classMkLow mkF a)).G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode (Fama.stSt P.γ a.prime.skeleton a.totalSigma (classMkLow mkF a)).G.tree → Mom P.d) → ℝ)
    (lb : GBranch (Fama.stSt P.γ a.prime.skeleton a.totalSigma (classMkLow mkF a)).G.tree → Option ℝ) :
    (classPieceLow P mkF a prot (protI a.layered J pat t s kSel).card fix filt ind lb).surv.m ≤
      6 * (protI a.layered J pat t s kSel).card := by
  show (survObjsLow a.prime.skeleton a.totalSigma (classMkLow mkF a)).length ≤ _
  rw [survObjs_lengthLow]
  have h1 := survivorsMk_length_leLow a.prime.skeleton a.totalSigma (classMkLow mkF a)
  have h2 : (classMkLow mkF a).ncard ≤ (markILow (γF := P.γ) J pat t s kSel a.prime).ncard :=
    Set.ncard_le_ncard (classMk_sub_markILow hF a hnz) (Set.toFinite _)
  have h3 : (markILow (γF := P.γ) J pat t s kSel a.prime).ncard ≤ 3 * (protI a.layered J pat t s kSel).card :=
    markCountBoundLow a.prime (protI a.layered J pat t s kSel)
  omega

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.ClassCount
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable (P : WTParams) [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (p N : ℕ) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
  (kSel : Fin (2 * R) → Option ℕ) (t s : ℝ) (A : Finset (LayeredGarden (2 * R)))
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ)
  (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
  (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (cP cθ : ℝ) (mkF : Fama.Stage1Mk.MarkFn P.γ (2 * R))

/-- **A good piece of a fine′ class.** -/
structure GoodPieceLow (π : Fama.Represents.PcA P.γ R p (objKind (2 * R)) A mkF) where
  piece : Stage1PieceMKG P R
  selR : Finset (GBranch piece.Gsb.tree)
  Mk : Set (Fama.CLVineG P.γ (Fama.Represents.repPt P.γ π).prime.skeleton)
  hpiece : piece.toStage1PieceGD = Fama.VineA.NormalizedSplice.stage1PieceOf P.γ P.d (Fama.Represents.repPt P.γ π).prime.prime.1
    (Fama.Represents.repPt P.γ π).layered (Fama.Represents.repPt P.γ π).prime.decodes (Fama.Represents.repPt P.γ π).totalSigma Mk
  ok : ClassPieceOKLow piece selR N cP cθ t b roots kSel Rs (classValueLow P p J pat kSel t s A roots h Rf σ Rs dag mkF π)
  nprot : piece.nProt ≤ (protI (Fama.Represents.repPt P.γ π).layered J pat t s kSel).card
  sound : SoundMKFullG piece p 0 roots cθ

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- **The B3 + B3s hypothesis is large-constant monotone.** -/
theorem markedClassRepresentsMK_monoLow (cP cθ : ℝ) :
    LargeConstantMonotone (fun P => ∀ h : P.γ ≤ 1 / 2, haveI : Fact (P.γ ≤ 1 / 2) := ⟨h⟩;
      MarkedClassRepresentsMKLow cP cθ P) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ
  have : Fact (P.γ ≤ 1 / 2) := ⟨hγ⟩
  have h := h hγ
  intro p hp R hR hRmax N hN1 hNb J hJ pat kSel t ht s hs A hA hpl hTC roots hh b Rf σ Rs dag hb hhb hRf hRs hhigh
    mkF hF π hnz
  rw [R_largeConstants] at hRmax
  rw [N_largeConstants] at hNb
  obtain ⟨prot, fix, filt, ind, lb, selR, hok⟩ := h p hp R hR hRmax N hN1 hNb J hJ pat kSel t ht s hs A
    (fun LG hLG => carrier_largeConstants c₁ c₂ (hA LG hLG)) hpl hTC roots hh b Rf σ Rs dag hb hhb hRf hRs hhigh
    mkF hF π hnz
  have hL0 : 0 ≤ P.L := by linarith
  have hRs0 : ∀ j, 0 ≤ Rs j := fun j => hL0.trans (hRs j)
  refine ⟨prot, fix, filt, ind, lb, selR, ?_⟩
  have h1 := stage1MKGate_representsIntMKSel_largeConstantsLow (P := P) c₁ c₂ h₁ (by linarith) hL0
    (classPieceLow P mkF (Fama.Represents.repPt P.γ π) prot (protI (Fama.Represents.repPt P.γ π).layered J pat t s kSel).card fix filt ind lb) selR N cP
    (fun _ => t) 0 roots _ (selMassMK_nonneg N (zero_le_one.trans hb) hRs0 kSel _) _ hok.rep
  have h2 := pieceRestB3s_largeConstantsLow (P := P) c₁ c₂
    (classPieceLow P mkF (Fama.Represents.repPt P.γ π) prot (protI (Fama.Represents.repPt P.γ π).layered J pat t s kSel).card fix filt ind lb) cθ hok.rest
  have h3 := representsIntMK_largeConstantsLow (P := P) c₁ c₂ h₁ (by linarith) hL0
    (classPieceLow P mkF (Fama.Represents.repPt P.γ π) prot (protI (Fama.Represents.repPt P.γ π).layered J pat t s kSel).card fix filt ind lb) N (cP + 343)
    (fun _ => t) 0 roots _ (pow_nonneg (zero_le_one.trans hb) N) _ hok.repMK
  exact ⟨h1, h2, hok.sel_spec, hok.sel_inj, hok.sel_card, h3, hok.sel_lb⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Stage1 WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
open WaveTurbulence.RedSplice (Prescription vinesV0 mem_vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel σf : Fin w → Option ℕ)

/-- **One fine′ batch edge keeps stem-uncleanness** (stem-dependent weight, marking `fineMkLow (γF := γF)`). -/
theorem notClean_iff_of_batchReachLow (hS : StemDep σf kSel) {p : ℕ} {kind : Bool} {a b : Fama.VineA.PrescribedPrimeGarden γF w}
    (h : Fama.VineA.PrescribedPrimeGarden.BatchReach γF (p := p) (kind := kind) a b (fineMkLow (γF := γF) J pat t s kSel σf)) : ¬ CleanPtLow J a ↔ ¬ CleanPtLow J b := by
  obtain ⟨L, B, hb, -, rfl⟩ := h
  have hmk : ∀ {LG : LayeredGarden w} (A : PrimeData LG), fineMkLow (γF := γF) J pat t s kSel σf A = markIXLow (γF := γF) J pat t s kSel A :=
    fun A => by simp only [fineMkLow, hS, ↓reduceIte]
  have hX := markInvariantBatchV_markXLow J hb a.prime.prime
    (fun i => ⟨i.1, i.2.1.1, rfl, fun hx => (Fama.mem_vinesV0.mp i.2.1).2
      (by show (i.1 : Fama.CLVineG γF _) ∈ fineMkLow (γF := γF) J pat t s kSel σf a.prime; rw [hmk]; exact Or.inr hx)⟩) trivial
  have hV := batchIso_v0CorrLow (batchMolIso_spec hb) a.totalSigma _ (Fama.VineA.fineState_isV0FamMk a.prime a.totalSigma)
  have ht : transportPrescription (batchMolIso hb) a.totalSigma =
      Fama.VineA.extendGroupPrescription γF (Fama.VineA.transportGroupPrescription γF (batchMolIso hb) a.sigma) :=
    Fama.VineA.transport_extendGroupPrescription (batchMolIso hb) a.sigma
  rw [not_cleanPt_iffLow, not_cleanPt_iffLow]
  constructor
  · rintro ⟨c, hc, hcx⟩
    obtain ⟨c', hc', e⟩ := hV.1 c hc
    rw [ht] at hc'
    exact ⟨c', hc', (hX c c' e).mp hcx⟩
  · rintro ⟨c', hc', hcx⟩
    have hc'' : c' ∈ Fama.vinesV0 γF B.skeleton (transportPrescription (batchMolIso hb) a.totalSigma) := by
      rw [ht]; exact hc'
    obtain ⟨c, hc, e⟩ := hV.2 c' hc''
    exact ⟨c, hc, (hX c c' e).mpr hcx⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Stage1 WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
open WaveTurbulence.RedSplice (Prescription vinesV0 mem_vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel σf : Fin w → Option ℕ)

/-- **Stem-uncleanness is a fine′-class invariant** (stem-dependent weight, marking `fineMkLow (γF := γF)`). -/
theorem notClean_iff_of_relatedLow (hS : StemDep σf kSel) {p : ℕ} {kind : Bool} {a b : Fama.VineA.PrescribedPrimeGarden γF w}
    (h : Fama.VineA.PrescribedPrimeGarden.Related γF (p := p) (kind := kind) a b (fineMkLow (γF := γF) J pat t s kSel σf)) : ¬ CleanPtLow J a ↔ ¬ CleanPtLow J b := by
  induction h with
  | rel x y h => exact notClean_iff_of_batchReachLow J pat t s kSel σf hS h
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end

end WaveTurbulence.GammaLow.Flower
