/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.CoreW1
public import WaveTurbulence.Foundations.Flower.MkSlotsT.Top

/-! # B3s-HELPER7 WP7 (part 2): the core weight of a run-class member is class-common

For a member `y` of the run class of the representative `a` (B3's `sourceClass a p kind mk`, shape
`memShape a mk y hy` onto `G_sb = (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G`), with the hypotheses of α's
`IntCore2`/γ's `MemberRun`/δ's `SelClass` (single-leaf cap trees `hcapA`, `hcapY`, `G_sb` plain `hG`, no representative
unit atom is a capped flower parent `hrepU`, the representative stem-clean `CleanPt J a`, one capped flower per tree in
both reconstructions) and, for the selection shells, the per-tree existence of the selected vertex being the same at
the member and at the representative (`hex`; proved in `CoreW4.lean`, `selCap_isSome_member_iff`):

* `genNW_member`: the general stem node weight at the member's core of a `G_sb` atom is the representative's;
* **`zatom_member`** (item 2): the atom factor of `genCoreW` at the member is `zatomG` at the restricted decoration
  `(memShape a mk y hy).resDec … κ`;
* `radTGen`: the tree-indexed radii `radSigma ++ [Rs j | kSel j ≠ none]` of the unit tops;
  **`top_member`** (item 3): when every requested selected vertex of the member exists (`selOK = 1`) and no
  representative unit top is a selected vertex (`hrepS`, from the fine marking: `rep_units_not_sel`), the top factor of
  `genCoreW` at the member is B3-2's top weight `∏ j, nodeWeight (topFilterWeightL (SURep a mk J radTGen j)) L 0 …`;
  `unitTopFilters_gen`: γ's `unitTopFilters_stem` for this `SU`;
* `selOK_congr`, `selConst_congr` (item 4 given `hex`): `selOK` and the selection constant are those of the
  representative;
* **`genCoreW_member`**: the whole core multiplier of the member, `selConst(a) · zatomG (resDec κ) · topW`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.Stage1MKGate (CleanPt classMk)
open WaveTurbulence.Flower.MkSlots (recLG)

namespace WaveTurbulence.Flower.MkSlotsI

/-! ## Generic facts on the selected vertices -/

section Generic

variable {w : ℕ}

/-- The shell test of `radRaw`: a selected vertex exists in the tree of `b` and it is not `b`. -/
theorem shell_iff {LG : LayeredGarden w} {J : Finset (Fin w)} {kSel : Fin w → Option ℕ}
    (b : GBranch LG.garden.tree) :
    (∃ v, selCap LG J kSel b.1.1 = some v ∧ v ≠ b) ↔
      ((selCap LG J kSel b.1.1).isSome ∧ selCap LG J kSel b.1.1 ≠ some b) := by
  constructor
  · rintro ⟨v, hv, hne⟩
    exact ⟨by rw [hv]; rfl, fun h => hne (Option.some.inj (hv.symm.trans h))⟩
  · rintro ⟨hs, hne⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨v, hv, fun h => hne (h ▸ hv)⟩

/-- A selected vertex is only present where a selection is requested. -/
theorem kSel_isSome_of_selCap {LG : LayeredGarden w} {J : Finset (Fin w)} {kSel : Fin w → Option ℕ} {j : Fin w}
    (h : (selCap LG J kSel j).isSome) : (kSel j).isSome := by
  unfold selCap at h
  cases hk : kSel j with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k => rfl

/-- **Item 4 (given the per-tree existence)**: `selOK` only reads which selected vertices exist. -/
theorem selOK_congr {LG LG' : LayeredGarden w} (J : Finset (Fin w)) (kSel : Fin w → Option ℕ)
    (h : ∀ j, (selCap LG J kSel j).isSome ↔ (selCap LG' J kSel j).isSome) : selOK LG J kSel = selOK LG' J kSel := by
  unfold selOK
  congr 1
  exact propext (forall_congr' fun j => imp_congr_right fun _ => h j)

/-- **Item 4 (given the per-tree existence)**: the selection constant only reads which selected vertices exist. -/
theorem selConst_congr {LG LG' : LayeredGarden w} (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (h : ∀ j, (selCap LG J kSel j).isSome ↔ (selCap LG' J kSel j).isSome) :
    (∏ j, (selCap LG J kSel j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ))) =
      ∏ j, (selCap LG' J kSel j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ)) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj := h j
  rcases h1 : selCap LG J kSel j with _ | v <;> rcases h2 : selCap LG' J kSel j with _ | v'
  · rfl
  · rw [h1, h2] at hj; exact absurd (hj.2 rfl) (by simp)
  · rw [h1, h2] at hj; exact absurd (hj.1 rfl) (by simp)
  · rfl

/-- The selected vertex of every tree with a requested selection exists iff `selOK = 1`. -/
theorem selOK_eq_one_iff (LG : LayeredGarden w) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) :
    selOK LG J kSel = 1 ↔ ∀ j, (kSel j).isSome → (selCap LG J kSel j).isSome := by
  unfold selOK
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h1 => absurd h1 (by norm_num), fun h1 => absurd h1 h⟩

/-- The radii of the stem filters at a unit top: σ's dyadic radius and the selection shell of a selected tree. -/
def radTGen (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ) (j : Fin w) : List ℝ :=
  (σ j).elim [] (fun i => [2 ^ i * L]) ++ (if (kSel j).isSome then [Rs j] else [])

theorem one_le_radTGen {L : ℝ} {σ kSel : Fin w → Option ℕ} {Rs : Fin w → ℝ} (hL : 1 ≤ L) (hRs : ∀ j, L ≤ Rs j)
    (j : Fin w) : ∀ x ∈ radTGen L σ kSel Rs j, 1 ≤ x := by
  intro x hx
  unfold radTGen at hx
  rcases List.mem_append.1 hx with h | h
  · rcases hσ : σ j with _ | i
    · rw [hσ] at h; simp at h
    · rw [hσ] at h
      simp only [Option.elim, List.mem_singleton] at h
      subst h
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hL
  · split_ifs at h
    · rw [List.mem_singleton] at h; subst h; exact hL.trans (hRs j)
    · simp at h

/-- At a stem branch that is not a selected vertex of a garden with `selOK = 1`, `radRaw` is `radTGen` of its tree. -/
theorem radRaw_eq_radTGen {LG : LayeredGarden w} {J : Finset (Fin w)} {L : ℝ} {σ kSel : Fin w → Option ℕ}
    {Rs : Fin w → ℝ} (hok : ∀ j, (kSel j).isSome → (selCap LG J kSel j).isSome) (b : GBranch LG.garden.tree)
    (hb : b ∉ selSetCap LG J kSel) :
    MkSlotsG.radRaw LG J L σ kSel Rs b = radTGen L σ kSel Rs b.1.1 := by
  unfold MkSlotsG.radRaw MkSlotsG.shellRad radTGen MkSlotsT.radSigma
  congr 1
  have hne : selCap LG J kSel b.1.1 ≠ some b := fun h => hb (Finset.mem_filter.2 ⟨Finset.mem_univ _, _, h⟩)
  by_cases hk : (kSel b.1.1).isSome
  · rw [ite_eq_left ((shell_iff b).2 ⟨hok _ hk, hne⟩), ite_eq_left hk]
  · rw [ite_eq_right (fun h => hk (kSel_isSome_of_selCap ((shell_iff b).1 h).1)), ite_eq_right hk]

/-- At a stem branch that is not a selected vertex of a garden with `selOK = 1`, the stem node weight is the
filter `radProd` with the radii `radTGen` of its tree (none off the stem). -/
theorem genNW_top_aux {LG : LayeredGarden w} {J : Finset (Fin w)} {L : ℝ} {σ kSel : Fin w → Option ℕ}
    {Rs : Fin w → ℝ} (hok : ∀ j, (kSel j).isSome → (selCap LG J kSel j).isSome) (b : GBranch LG.garden.tree)
    (hb : b ∉ selSetCap LG J kSel) (x : ℝ) :
    genNW LG J L σ kSel Rs b.toNode x =
      (MkSlotsT.radProd (if ∃ j, b ∈ stemSetCap LG J j then radTGen L σ kSel Rs b.1.1 else []) x : ℂ) := by
  rw [genNW_toNode]
  by_cases h : ∃ j, b ∈ stemSetCap LG J j
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_right hb, mul_one, radRaw_eq_radTGen hok b hb]
  · rw [ite_eq_right h, ite_eq_right h]
    simp [MkSlotsT.radProd]

/-- **The stem node weight only reads**: the stem test, the selected test, the tree, whether the tree has a selected
vertex, and whether it is the branch (two branches of two gardens with the same data have the same weight). -/
theorem genNW_congr_data {LG LG' : LayeredGarden w} {J : Finset (Fin w)} {L : ℝ} {σ kSel : Fin w → Option ℕ}
    {Rs : Fin w → ℝ} (b : GBranch LG.garden.tree) (b' : GBranch LG'.garden.tree) (t : Fin w)
    (ht : b.1.1 = t) (ht' : b'.1.1 = t)
    (hst : (∃ j, b ∈ stemSetCap LG J j) ↔ ∃ j, b' ∈ stemSetCap LG' J j)
    (hsel : b ∈ selSetCap LG J kSel ↔ b' ∈ selSetCap LG' J kSel)
    (hsh : (selCap LG J kSel t).isSome ↔ (selCap LG' J kSel t).isSome)
    (hsc : selCap LG J kSel t = some b ↔ selCap LG' J kSel t = some b') (x : ℝ) :
    genNW LG J L σ kSel Rs b.toNode x = genNW LG' J L σ kSel Rs b'.toNode x := by
  have h1 := shell_iff (J := J) (kSel := kSel) b
  have h2 := shell_iff (J := J) (kSel := kSel) b'
  rw [ht] at h1
  rw [ht'] at h2
  have hshell : MkSlotsG.shellRad LG J kSel Rs b = MkSlotsG.shellRad LG' J kSel Rs b' := by
    unfold MkSlotsG.shellRad
    rw [ht, ht']
    by_cases h : ∃ v, selCap LG' J kSel t = some v ∧ v ≠ b'
    · rw [ite_eq_left (h1.2 ⟨hsh.2 (h2.1 h).1, fun e => (h2.1 h).2 (hsc.1 e)⟩), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (h2.2 ⟨hsh.1 (h1.1 h').1, fun e => (h1.1 h').2 (hsc.2 e)⟩)), ite_eq_right h]
  have hrad : MkSlotsG.radRaw LG J L σ kSel Rs b = MkSlotsG.radRaw LG' J L σ kSel Rs b' := by
    unfold MkSlotsG.radRaw
    rw [hshell]
    unfold MkSlotsT.radSigma
    rw [ht, ht']
  rw [genNW_toNode, genNW_toNode, hrad, ht, ht']
  by_cases h1 : ∃ j, b' ∈ stemSetCap LG' J j
  · rw [ite_eq_left (hst.2 h1), ite_eq_left h1]
    by_cases h2 : b' ∈ selSetCap LG' J kSel
    · rw [ite_eq_left (hsel.2 h2), ite_eq_left h2]
    · rw [ite_eq_right (fun h => h2 (hsel.1 h)), ite_eq_right h2]
  · rw [ite_eq_right (fun h => h1 (hst.1 h)), ite_eq_right h1]

theorem mem_selSetCap_iff' {LG : LayeredGarden w} {J : Finset (Fin w)} {kSel : Fin w → Option ℕ}
    (b : GBranch LG.garden.tree) : b ∈ selSetCap LG J kSel ↔ ∃ j, selCap LG J kSel j = some b := by
  simp [selSetCap]

end Generic

/-! ## The representative's unit tops are not selected -/

/-- **No core of an atom of a unit of the representative is a selected vertex** (the fine marking marks the vines
containing a selected vertex; α's `rep_units_not_cfp` for the selections). -/
theorem rep_units_not_sel {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) (hset : mk a.prime = classMk mkF a)
    (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) (b : GBranch a.prime.skeleton.tree)
    (hb : b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms) :
    a.prime.data.coreBranch a.prime.prime.1 b ∉ selSetCap (recLG a) J kSel := by
  have hu : unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j ∈
      unitBlocks a.prime.skeleton a.totalSigma (classMk mkF a) := by
    rw [← hset]
    exact List.get_mem _ _
  have h0 := MkSlotsS.coreBranch_unit_not_sel pat t s kSel mkF hsub a hu hb
  rwa [← mem_selSetCap_congr (sourceLayer_reconstructs a) J kSel
    (b := a.prime.data.coreBranch a.prime.prime.1 b) rfl] at h0

/-! ## The run class -/

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (J : Finset (Fin (2 * R)))
  (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
  (hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))
  (hc : CleanPt J a)
  (honeA : MkSlotsS.OneFlower (recLG a) J)
  (honeY : MkSlotsS.OneFlower (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J)
  (kSel : Fin (2 * R) → Option ℕ)

include hy hcapA hcapY hG hrepU hc honeA honeY in
/-- The member's core of a `G_sb` atom is a selected vertex iff the representative's is. -/
theorem coreY_mem_selSetCap_iff (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c) ∈
        selSetCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J kSel ↔
      coreRec a (mk a.prime) c ∈ selSetCap (recLG a) J kSel := by
  exact (mem_selSetCap_iff' _).trans ((exists_congr fun j =>
    MkSlotsS.selCap_member_core_iff a mk y hy J hcapA hcapY hG hrepU hc honeA honeY kSel j c).trans
      (mem_selSetCap_iff' _).symm)

variable (L : ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)

include hy hcapA hcapY hG hrepU hc honeA honeY in
/-- **The stem node weight at a `G_sb` atom is common to the run class** (given the per-tree existence of the
selected vertex, for the shells). -/
theorem genNW_member
    (hex : ∀ j, (selCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
      kSel j).isSome ↔ (selCap (recLG a) J kSel j).isSome)
    (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) (x : ℝ) :
    genNW (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J L σ kSel Rs
        (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).toNode x =
      genNW (recLG a) J L σ kSel Rs (coreRec a (mk a.prime) c).toNode x := by
  have htY : (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).1.1 = c.1.1 :=
    (MkSlots.IntRest.coreBranch_fst y.1.data y.1.plain _).trans (MkSlotsT.shape_br_fst (memShape a mk y hy) c)
  have htA : (coreRec a (mk a.prime) c).1.1 = c.1.1 :=
    (MkSlots.IntRest.coreBranch_fst a.prime.data a.prime.prime.1 _).trans
      (MkSlotsT.shape_br_fst (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) c)
  exact genNW_congr_data _ _ c.1.1 htY htA (MkSlotsT.stemB_member_iff a mk y hy J hcapA hcapY hG hrepU c)
    (coreY_mem_selSetCap_iff a mk y hy J hcapA hcapY hG hrepU hc honeA honeY kSel c) (hex c.1.1)
    (MkSlotsS.selCap_member_core_iff a mk y hy J hcapA hcapY hG hrepU hc honeA honeY kSel c.1.1 c) x

include hy hcapA hcapY hG hrepU hc honeA honeY in
/-- **Item 2: the member transfer of the atom part.** The atom factor of the member's core multiplier `genCoreW`
(over the non-hinge `G_sb` atoms, at the skeleton resonance factors of the coset decoration of `κ`) is the atom weight
`zatomG` of `G_sb` at the restricted decoration `(memShape a mk y hy).resDec … κ`. -/
theorem zatom_member
    (hex : ∀ j, (selCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
      kSel j).isSome ↔ (selCap (recLG a) J kSel j).isSome)
    {d : ℕ} {roots : Fin (2 * R) → (Fin d → ℤ)} (κ : GenDecoration y.1.skeleton d roots 0) :
    ∏ c ∈ univ.filter (fun c => c ∉ (memShape a mk y hy).hinges (source_disjMk a mk y hy)),
        genNW (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J L σ kSel Rs
          (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).toNode
          (omegaNode y.1.skeleton (cosetDecoration y.1.skeleton L 0 κ.1) ((memShape a mk y hy).br c)) =
      zatomG J L σ kSel Rs a (mk a.prime) ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ) := by
  rw [zatomG_eq, memShape_hinges]
  refine Finset.prod_congr rfl fun c hc' => ?_
  have hh : c ∉ (memShape a mk y hy).hinges (source_disjMk a mk y hy) := by
    rw [memShape_hinges]; exact (Finset.mem_filter.1 hc').2
  have hnu : ∀ j, (memShape a mk y hy).br c ≠ (unitClBlock (y.2 j)).upper := fun j h =>
    hh (((memShape a mk y hy).mem_hinges (source_disjMk a mk y hy) c).2 ⟨j, h⟩)
  rw [genNW_member a mk y hy J hcapA hcapY hG hrepU hc honeA honeY kSel L σ Rs hex c,
    MkSlotsT.omegaNode_shape (memShape a mk y hy) (cosetDecoration y.1.skeleton L 0 κ.1)
      (cosetDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G L 0
        ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ).1) (fun _ => rfl) c hnu]

end Class

/-! ## γ's unit top filters for the radii `radTGen` -/

end WaveTurbulence.Flower.MkSlotsI
