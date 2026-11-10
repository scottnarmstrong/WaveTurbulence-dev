/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKGarden.GardenF

/-! # C1c MK-GARDEN / LoopDataMK: the `M`-level data with survivors, for a garden

`LowLoopDataMK` is main's `LowLoopData` (LowGardenUnloopMain) with:
* the collection data `C : CollDataMK M` and the survivors `E`, `forbE : C.forb = survAtomsM E`;
* `oblE : SubproOblGMK` in place of `obl`;
* the pool facts (`unsel`, `sg2`, `des2`, `shape2`, `crit2`, `hC22`, `vc2`) on the forbidden pool `poolF C`;
* the survivor facts `survC1`, `survChain`, `survShape`, `survCritInt`, `survHinge`.

`lowLoopDataMK_garden` (main's `lowLoopData_garden`): it holds on `M = inlMol G.molecule` with `C0MK C S`
(`forb := survAtomsM (E0 S)`, R164 (a)), the survivors `E0 S`, the omitted vines `Un0F`, the first stage `Fst0 C`, and the
critical atoms `critMapMK` (`CriticalSGMK`, survivor interiors excluded). -/

@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical

namespace WaveTurbulence.Flower.FinalMKGarden
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.AtomTransport WaveTurbulence.MoleProp
  WaveTurbulence.Mole WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.MkDefs

section data
variable {V : Type} [DecidableEq V] [Infinite V] {D : Type} [Fintype D] [DecidableEq D] {d : ℕ}

/-- **The `M`-level data of the loop transport with survivors** (main's `LowLoopData`, R164 pool). -/
structure LowLoopDataMK (M : Molecule V D) (R : ℕ) (Adm : (D → Fin d → ℤ) → Prop) (P0 : Finset V → ℝ)
    (C : CollDataMK M) {m : ℕ} (E : Fin m → Object M) (Un : (D → Fin d → ℤ) → Set (Object M))
    (Fst : Set (Object M)) (crit : V → Prop) (kFix : Finset (Mom d)) (L γ η : ℝ) (mm : ℕ) : Prop where
  hSL : SubHypLoop R M
  hmate : ∀ κ, Adm κ → ∀ x, κ (M.mate x) = κ x
  heq : ∀ κ, Adm κ → ∀ y : D, M.atom y = M.atom (M.mate y) → ∀ z : D, M.atom z = M.atom y → κ z = κ y
  hdec : ∀ κ, Adm κ → ∃ c0, M.IsDecoration L (0 : Mom d) c0 κ ∧ ∀ x ∈ M.atoms, M.deg x = 4 → c0 x = 0
  h0 : ∀ κ, Adm κ → ∀ a ∈ M.atoms, M.deg a = 4 → ∑ x ∈ M.dartsAt a, M.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0
  pin : PinnedM0 (fun k => Adm k) L (0 : Mom d) M
  hP0 : ∀ S ∈ M.maximalLadders, 0 ≤ P0 S
  gaps : ∀ κ, Adm κ → SourceLadderGaps M L (0 : Mom d) P0 κ
  hH : HingeNoLoop C.toCollData
  trip : TripleDesig C.toCollData
  forbE : C.forb = survAtomsM E
  oblE : ∀ κ, Adm κ → SubproOblGMK C.toCollData E L γ η (0 : Mom d) κ
  unsel : ∀ κ, Adm κ → (poolF C).UnselOK L γ η (0 : Mom d) κ (Un κ)
  degen : ∀ κ, Adm κ → DegenSGT M L γ η (0 : Mom d) κ (fun a => M.IsTame L (0 : Mom d) kFix κ a)
  critSG : ∀ κ, Adm κ → ∀ a, crit a → SGat M L γ η (0 : Mom d) κ a
  card : ((2 * M.atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ mm
  sg2 : ∀ κ, Adm κ → ∀ U, Coll2 (poolF C) (Un κ) L γ η (0 : Mom d) κ U → U.HasGapKind L γ η (0 : Mom d) κ .SG
  des2 : ∀ κ, Adm κ → ∀ U, Coll2 (poolF C) (Un κ) L γ η (0 : Mom d) κ U → HingeData C.toCollData U
  shape2 : ∀ κ, Adm κ → ∀ U, Coll2 (poolF C) (Un κ) L γ η (0 : Mom d) κ U → U.atoms.card = 3 ∨ ObjVine M U
  crit2 : ∀ κ, Adm κ → ∀ U, Coll2 (poolF C) (Un κ) L γ η (0 : Mom d) κ U → ∀ a ∈ U.atoms, a ≠ U.upper →
    a ≠ U.lower → ¬ crit a
  hC1 : ∀ i j, i ≠ j → Disjoint (C.collection i).atoms (C.collection j).atoms
  hC22 : ∀ κ, Adm κ → ∀ O ∈ (poolF C).C2Of L γ η (0 : Mom d) κ (Un κ),
    ∀ O' ∈ (poolF C).C2Of L γ η (0 : Mom d) κ (Un κ), O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms
  vc2 : ∀ κ, Adm κ → ∀ O ∈ (poolF C).C2Of L γ η (0 : Mom d) κ (Un κ), (∃ h, O.shape = .vc h) →
    Vine.DoubleChain M O.atoms O.upper O.lower 1 ∨ Vine.DoubleChain M O.atoms O.upper O.lower 2 ∨
      M.IsVine .V O.atoms O.upper O.lower
  hC13 : ∀ i, (C.collection i).atoms.card ≠ 3
  hFst : ∀ U ∈ Fst, ∃ i, U = C.collection i
  hFstC : ∀ i, (∃ h, (C.collection i).shape = .vc h) → C.collection i ∈ Fst
  cn : CnBound M C.toCollData Un Fst L γ η (0 : Mom d) {κ | Adm κ} R
  survC1 : ∀ i j, Disjoint (C.collection i).atoms (E j).atoms
  survChain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
    (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1
  survShape : ∀ i, ObjVine M (E i)
  survCritInt : ∀ i, ∀ a ∈ (E i).atoms, a ≠ (E i).upper → a ≠ (E i).lower → ¬ crit a
  survHinge : ∀ v ∈ C.hinges, ∀ i, ¬ (E i).IsInterior v

end data

section generic
variable {V : Type*} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ} {M₀ : Molecule V D₀}
  {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {m : ℕ}

/-- A collection object satisfies `HingeData` (main's `hingeData_collection`, from the survivor-aware obligations). -/
theorem hingeData_collectionMK {C : CollData M₀} {E : Fin m → Object M₀} (obl : SubproOblGMK C E L γ η w κ)
    (i : Fin C.n) : HingeData C (C.collection i) := by
  intro v hv hvi
  obtain ⟨f, s, hf, hs, hP⟩ := obl.hingeJoint v hv i hvi
  obtain ⟨f', s', hf', hs', hT⟩ := obl.hingeSG v hv
  have e1 : f' = f := Option.some.inj (hf'.symm.trans hf)
  have e2 : s' = s := Option.some.inj (hs'.symm.trans hs)
  subst e1 e2
  exact ⟨f', s', hf, hs, hP.1, hP.2, hT.1.1, hT.1.2.1, hT.1.2.2.2⟩

/-- A member of the forbidden pool's `C₂` has no hinge joint. -/
theorem hingeData_c2OfF {C : CollDataMK M₀} {Unsel : Set (Object M₀)} {U : Object M₀}
    (hU : U ∈ (poolF C).C2Of L γ η w κ Unsel) : HingeData C.toCollData U := by
  intro v hv hvU
  exfalso
  have hdis := (Subpro.c2Of_disjoint_c1_hinges (poolF C) hU).2
  exact Finset.disjoint_left.mp hdis (object_mem_of_joint U hvU) (Finset.mem_union_left _ hv)

end generic

section inl
variable {R d : ℕ} {G : Garden (2 * R)}

/-- The survivors on `inlMol G.molecule`. -/
noncomputable abbrev E0 (S : SurvivorData G) : Fin S.m → Object (inlMol G.molecule) :=
  fun i => objMap (ι := inlEmb _) (S.surv i)

/-- **The MK collection data on `inlMol G.molecule`**: `C0 C` with `forb := survAtomsM (E0 S)` (R164 (a)). -/
noncomputable def C0MK (C : CountingChoices G d) (S : SurvivorData G) : CollDataMK (inlMol G.molecule) :=
  { C0 C with forb := survAtomsM (E0 S) }

/-- The omitted vines of the MK pool on `inlMol G.molecule`. -/
abbrev Un0F (C : CountingChoices G d) (S : SurvivorData G) (L γ η : ℝ) (κ : GardenDart G → (Fin d → ℤ)) :
    Set (Object (inlMol G.molecule)) :=
  objMap (ι := inlEmb _) '' unGF C S L γ η κ

theorem poolF_C0MK (C : CountingChoices G d) (S : SurvivorData G) :
    poolF (C0MK C S) = collMap (inlEmb _) (gColF C S) := by
  have h : C.subpro.hinges.map (inlEmb _) ∪ survAtomsM (E0 S) =
      (C.subpro.hinges ∪ survAtomsG S).map (inlEmb _) := by
    rw [survAtomsM_objMap (inlEmb _) S.surv, Finset.map_union]
    rfl
  exact congrArg (fun H => ({ C0 C with hinges := H } : CollData (inlMol G.molecule))) h

variable (C : CountingChoices G d) (S : SurvivorData G) {L γ η : ℝ} {κ : GardenDart G → (Fin d → ℤ)}

theorem coll2_mapF (U : Object (inlMol G.molecule))
    (hU : Coll2 (poolF (C0MK C S)) (Un0F C S L γ η κ) L γ η 0 κ U) :
    ∃ U0, U = objMap (ι := inlEmb _) U0 ∧ Coll2 (gColF C S) (unGF C S L γ η κ) L γ η 0 κ U0 := by
  rw [poolF_C0MK] at hU
  rcases hU with ⟨i, rfl⟩ | hU
  · exact ⟨_, rfl, Or.inl ⟨i, rfl⟩⟩
  · obtain ⟨U0, rfl⟩ := objMap_surjective (M := G.molecule) (ι := inlEmb _) U
    exact ⟨U0, rfl, Or.inr ((mem_collMap_c2Of (inlEmb _) (gColF C S) _ U0).1 hU)⟩

theorem c2OfF0_mem {U' : Object (inlMol G.molecule)}
    (h : U' ∈ (poolF (C0MK C S)).C2Of L γ η 0 κ (Un0F C S L γ η κ)) :
    ∃ U, U' = objMap (ι := inlEmb _) U ∧ U ∈ (gColF C S).C2Of L γ η 0 κ (unGF C S L γ η κ) := by
  rw [poolF_C0MK] at h
  obtain ⟨U, rfl⟩ := objMap_surjective (M := G.molecule) (ι := inlEmb _) U'
  exact ⟨U, rfl, (mem_collMap_c2Of (inlEmb _) (gColF C S) _ U).1 h⟩

variable {base : Mom d}

theorem oblE0 (hadm : AdmissibleMK C S L γ η base κ) :
    SubproOblGMK (C0MK C S).toCollData (E0 S) L γ η 0 κ :=
  collMap_subproOblGMK (inlEmb _) (gCol C) S.surv (subproOblGMK_base_indep (subproOblGMK_of_supportMK hadm.1))

theorem unselOK0F (hadm : AdmissibleMK C S L γ η base κ) :
    (poolF (C0MK C S)).UnselOK L γ η 0 κ (Un0F C S L γ η κ) := by
  rw [poolF_C0MK]
  exact (collMap_unselOK (inlEmb _) (gColF C S) _).2 (unselOK_GF hadm)

theorem hd22_0F {c : GBranch G.tree → Mom d} (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hadm : AdmissibleMK C S L γ η base κ) :
    ∀ O ∈ (poolF (C0MK C S)).C2Of L γ η 0 κ (Un0F C S L γ η κ),
      ∀ O' ∈ (poolF (C0MK C S)).C2Of L γ η 0 κ (Un0F C S L γ η κ), O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms := by
  intro O hO O' hO'
  obtain ⟨U, rfl, hU⟩ := c2OfF0_mem C S hO
  obtain ⟨U', rfl, hU'⟩ := c2OfF0_mem C S hO'
  rw [objMap_atoms, objMap_atoms, Finset.map_inj, Finset.disjoint_map]
  exact hd22_GF hκ hc hadm hU hU'

theorem vcShape0F {c : GBranch G.tree → Mom d} (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) :
    ∀ O ∈ (poolF (C0MK C S)).C2Of L γ η 0 κ (Un0F C S L γ η κ), (∃ h, O.shape = .vc h) →
      Vine.DoubleChain (inlMol G.molecule) O.atoms O.upper O.lower 1 ∨
        Vine.DoubleChain (inlMol G.molecule) O.atoms O.upper O.lower 2 ∨
        (inlMol G.molecule).IsVine .V O.atoms O.upper O.lower := by
  intro O hO hvc
  obtain ⟨U, rfl, hU⟩ := c2OfF0_mem C S hO
  rcases vcShape_GF hκ hc hU ((objMap_shape_vc_iff (inlEmb _) U).1 hvc) with h | h | h
  · exact Or.inl (doubleChain_map G.molecule (inlEmb _) h)
  · exact Or.inr (Or.inl (doubleChain_map G.molecule (inlEmb _) h))
  · exact Or.inr (Or.inr ((mapAtoms_isVine G.molecule (inlEmb _) _ _ _ _).2 h))

end inl

section main
variable {R d : ℕ} {G : Garden (2 * R)}
variable (hp : G.IsPlain) (hR : 1 ≤ R) {D : SplicedKernelData G d} {C : CountingChoices G d} {S : SurvivorData G}
  (hD : D.hinges = C.subpro.hinges) (hg : CountingGeometry G C) (hSt : S.Structural C.subpro) (hO : SurvChainOrder S)
  (h2a : 2 ≤ G.molecule.atoms.card) {L γ η : ℝ} (hL : 0 < L) {base : Mom d}
  {roots : Fin (2 * R) → (Fin d → ℤ)} {Adm : (GardenDart G → (Fin d → ℤ)) → Prop}
  (hA : ∀ κ, Adm κ → splicedCountingAdmissibleMK G D C S L γ η base roots κ) (hne : ∃ κ, Adm κ)

include hp hR hD hg hSt hO h2a hL hA hne

/-- **`LowLoopDataMK` for a garden** (main's `lowLoopData_garden` with survivors and the R164 pool). -/
theorem lowLoopDataMK_garden (m : ℕ)
    (hcard : ((2 * (inlMol G.molecule).atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m) :
    LowLoopDataMK (d := d) (inlMol G.molecule) R Adm (scaleMap (inlEmb _) C.ladderScale) (C0MK C S) (E0 S)
      (Un0F C S L γ η) (Fst0 C) (critMapMK (inlEmb _) C S) (kFix0 C base) L γ η m := by
  have hL0 : L ≠ 0 := hL.ne'
  have hSG : SubHypLoop R G.molecule := subHypLoop_of_geometry hg hR h2a
  have hS : SubHypLoop R (inlMol G.molecule) := subHypLoop_mapAtoms (inlEmb _) hSG
  have hadm : ∀ κ, Adm κ → AdmissibleMK C S L γ η base κ := fun κ hκ => (hA κ hκ).2
  have hgd : ∀ κ, Adm κ → ∃ c, G.molecule.IsDecoration L base c κ ∧
      ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0 :=
    fun κ hκ => gdec_z hp hL0 (hA κ hκ).1
  have hz : ∀ κ ∈ {κ | Adm κ}, ∃ z : GenDecoration G d roots 0, ∀ x, bondIndex G z.1 x = κ x := fun κ hκ => by
    obtain ⟨⟨z, hz, -, -⟩, -⟩ := hA κ hκ; exact ⟨z, hz⟩
  obtain ⟨hdec0, hh0, hpin⟩ := class_dec_facts G hp hL0 roots hz
  have hmate : ∀ κ, Adm κ → ∀ x, κ ((inlMol G.molecule).mate x) = κ x := fun κ hκ x => by
    obtain ⟨c, hc, -⟩ := hdec0 κ hκ; exact hc.1 x
  have hC13 : ∀ i, ((C0MK C S).collection i).atoms.card ≠ 3 := by
    intro i
    show ((C.subpro.collection i).atoms.map (inlEmb _)).card ≠ 3
    rw [Finset.card_map]
    exact Subpro.objVine_card_ne_three (Subpro.objVine_of_allowed (hg.subpro.1 i))
  have hgaps : ∀ κ, Adm κ → SourceLadderGaps (inlMol G.molecule) L 0 (scaleMap (inlEmb _) C.ladderScale) κ := by
    intro κ hκ
    rw [sourceLadderGaps_base_indep (inlMol G.molecule) L 0 base]
    exact (ladderGaps_mapAtoms (inlEmb _) C L γ η base κ).2 (hadm κ hκ).2.2.2.2.2.2.2.2.2
  have hsgc1 : ∀ κ, Adm κ → ∀ i, ((C0MK C S).collection i).HasGapKind L γ η 0 κ .SG := by
    intro κ hκ i
    show (objMap (ι := inlEmb _) (C.subpro.collection i)).HasGapKind L γ η 0 κ .SG
    rw [objMap_hasGapKind_iff, object_hasGapKind_base_indep _ L γ η 0 base κ]
    exact (hadm κ hκ).1.selectedSG i
  have hsgh : ∀ κ, Adm κ → ∀ U, Coll2 (poolF (C0MK C S)) (Un0F C S L γ η κ) L γ η 0 κ U →
      U.HasGapKind L γ η 0 κ .SG ∧ HingeData (C0MK C S).toCollData U := by
    intro κ hκ U hU
    rcases hU with ⟨i, rfl⟩ | hU
    · exact ⟨hsgc1 κ hκ i, hingeData_collectionMK (oblE0 C S (hadm κ hκ)) i⟩
    · exact ⟨hU.1.1.1, hingeData_c2OfF hU⟩
  refine
    { hSL := hS
      hmate := hmate
      heq := fun κ hκ => inl_loop_heqMK hg hD (hA κ hκ)
      hdec := hdec0
      h0 := hh0
      pin := hpin
      hP0 := ?_
      gaps := hgaps
      hH := ?_
      trip := tripleDesig_collMap (inlEmb _) (tripleDesig_LOW hg hR)
      forbE := rfl
      oblE := fun κ hκ => oblE0 C S (hadm κ hκ)
      unsel := fun κ hκ => unselOK0F C S (hadm κ hκ)
      degen := ?_
      critSG := ?_
      card := hcard
      sg2 := fun κ hκ U hU => (hsgh κ hκ U hU).1
      des2 := fun κ hκ U hU => (hsgh κ hκ U hU).2
      shape2 := ?_
      crit2 := ?_
      hC1 := ?_
      hC22 := fun κ hκ => by
        obtain ⟨c, hc, hc0⟩ := hgd κ hκ
        exact hd22_0F C S hc hc0 (hadm κ hκ)
      vc2 := fun κ hκ => by
        obtain ⟨c, hc, hc0⟩ := hgd κ hκ
        exact vcShape0F C S hc hc0
      hC13 := hC13
      hFst := ?_
      hFstC := ?_
      cn := ?_
      survC1 := ?_
      survChain := ?_
      survShape := ?_
      survCritInt := ?_
      survHinge := ?_ }
  · intro S' hS'
    obtain ⟨κ, hκ⟩ := hne
    rcases (hgaps κ hκ S' hS').1 with h | ⟨-, h, -⟩
    · rw [h]
    · exact le_trans (inv_nonneg.2 hL.le) h
  · intro v hv y hy hl
    obtain ⟨v0, hv0, rfl⟩ := Finset.mem_map.1 hv
    simp only [mapAtoms_atom, mapAtoms_mate, inlEmb_apply, Sum.inl.injEq] at hy hl
    exact hg.hingeNoLoop y (hy ▸ hv0) (hy.trans hl.symm)
  · intro κ hκ
    rw [mapAtoms_degenSGT (inlEmb _), degenSGT_base_indep G.molecule L γ η 0 base]
    refine degenSGT_mono (fun a ha => ?_) (degenSGT_of_supportMK (hadm κ hκ).1)
    exact (mapAtoms_isTame (inlEmb _) L 0 _ a).2 ((isTame_shift G.molecule L base _ κ a).1 ha)
  · intro κ hκ a ha
    obtain ⟨a0, rfl, hcr⟩ := ha
    rw [mapAtoms_sgat (inlEmb _), sgat_base_indep G.molecule L γ η 0 base]
    exact sgat_of_labelMK (hadm κ hκ).2.2.1 hcr.1.1
  · intro κ hκ U hU
    obtain ⟨U0, rfl, hU0⟩ := coll2_mapF C S U hU
    obtain ⟨c, hc, hc0⟩ := hgd κ hκ
    rw [objMap_atoms, Finset.card_map, objVine_objMap_iff]
    rcases hU0 with ⟨i, rfl⟩ | hU0
    · exact Or.inr (Subpro.objVine_of_allowed (hg.subpro.1 i))
    · exact shape_GF hc hc0 hU0
  · intro κ hκ U hU a ha h1 h2
    obtain ⟨U0, rfl, hU0⟩ := coll2_mapF C S U hU
    rw [objMap_atoms] at ha
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_map.1 ha
    rw [critMapMK_iff]
    exact crit_GF (hadm κ hκ) hU0 ⟨ha0, fun e => h1 (by rw [e]; rfl), fun e => h2 (by rw [e]; rfl)⟩
  · intro i j hij
    show Disjoint ((C.subpro.collection i).atoms.map (inlEmb _)) ((C.subpro.collection j).atoms.map (inlEmb _))
    rw [Finset.disjoint_map]
    exact hg.subpro.2.1 i j hij
  · intro U hU'
    obtain ⟨U0, ⟨⟨i, rfl⟩, -⟩, rfl⟩ := hU'
    exact ⟨i, rfl⟩
  · intro i hvc
    exact ⟨C.subpro.collection i, ⟨⟨i, rfl⟩, (objMap_shape_vc_iff (inlEmb _) _).1 hvc⟩, rfl⟩
  · intro κ hκ ps hps hpw
    refine cnBound_garden hp hR C.subpro hg.subpro ps (fun p hp' => ?_) hpw
    obtain ⟨⟨-, hCD, hJ, hN⟩, hF⟩ := hps p hp'
    exact ⟨hF, hCD, hJ, hN⟩
  · intro i j
    show Disjoint ((C.subpro.collection i).atoms.map (inlEmb _)) ((S.surv j).atoms.map (inlEmb _))
    rw [Finset.disjoint_map]
    exact hSt.2.1 i j
  · intro i j hij hnd
    have hnd0 : ¬ Disjoint (S.surv i).atoms (S.surv j).atoms := by
      intro h; apply hnd
      show Disjoint ((S.surv i).atoms.map (inlEmb _)) ((S.surv j).atoms.map (inlEmb _))
      rw [Finset.disjoint_map]; exact h
    refine ⟨hO i j hij hnd0, ?_⟩
    show ((S.surv i).atoms.map (inlEmb _) ∩ (S.surv j).atoms.map (inlEmb _)).card = 1
    rw [← Finset.map_inter, Finset.card_map]
    have h1 := hSt.2.2.1 i j hij
    have h2 : 0 < ((S.surv i).atoms ∩ (S.surv j).atoms).card :=
      Finset.card_pos.2 (Finset.not_disjoint_iff_nonempty_inter.1 hnd0)
    omega
  · intro i
    exact (objVine_objMap_iff G.molecule (inlEmb _) (S.surv i)).2 (hSt.1 i)
  · intro i a ha h1 h2 hcr
    show False
    rw [show (E0 S i).atoms = (S.surv i).atoms.map (inlEmb _) from rfl] at ha
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_map.1 ha
    rw [critMapMK_iff] at hcr
    exact hcr.2 i ⟨ha0, fun e => h1 (by rw [e]; rfl), fun e => h2 (by rw [e]; rfl)⟩
  · intro v hv i hint
    obtain ⟨v0, hv0, rfl⟩ := Finset.mem_map.1 hv
    exact hSt.2.2.2 v0 hv0 i ((objMap_isInterior_iff (S.surv i) v0).1 hint)

end main

end WaveTurbulence.Flower.FinalMKGarden
