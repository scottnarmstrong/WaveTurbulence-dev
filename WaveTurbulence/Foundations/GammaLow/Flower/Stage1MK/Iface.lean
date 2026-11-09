/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P6
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P7
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P8
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P9
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P10
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvMK2
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvMK4
public import WaveTurbulence.Foundations.Vine.A.VineSurvMK
public import WaveTurbulence.Foundations.Flower.MkSubpro.Survivors
public import WaveTurbulence.Foundations.Flower.MkSubpro.Piece
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Hyp
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkFn
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.VCMember

/-! # FLOWER-LOW (packet L8), item I: the interface statement of the marked Stage 1′ over `𝒱_γ`

`MarkedClassRepresentsMKLow cP cθ P` (main's `Stage1MKGate.MarkedClassRepresentsMK`, B3s: the class representation
of the marked Stage 1′ for one parameter record, over the family `𝒱_{P.γ}`, with the class piece `classPieceLow`)
and its gate form `MarkedClassRepresentsGateLow`. I-SLOTSI proves `MarkedClassRepresentsGateLow 452 cθ`; L8 derives
`Stage1MKGateLow` from it (main's `stage1ReductionAtMKFull_of_B3s`). Copied by source (sha256 in
COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
  {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {S : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {σ : Prescription G} {Mk : Set (Fama.CLVineG γF G)}

/-- **The residual decomposition of a survivor** (o75 Lemma 3): in the splice `Fama.stSt γF G σ Mk`, a survivor `t` of a
marked SG group is decomposed around the runs at its joints, inside the segment `UR` of the group's chain made of
`t` and these runs.  If `UR` contains both ends of the chain, it is the whole group and `t` is its only survivor. -/
theorem surv_sdecompMKLow (hN : N.IsMolecule) (hs : Fama.Spine γF N L S a b) (hB : N.IsBlock S a b)
    (hvineM : ∀ t ∈ L, Src.IsSomeVine γF G.molecule t.1 t.2.1 t.2.2)
    (hingr : ∀ t ∈ L, Fama.IsIngredientG γF G.molecule S t.1)
    (hmemb : ∀ T, Fama.IsIngredientG γF G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L)
    (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG) (h : Fama.markedGroup γF G Mk S)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ (markedUnitsOfMKLow h).surv) :
    ∃ UR L0 R0 a' b', SDecomp N (Fama.stSt γF G σ Mk).cls UR t.1 L0 R0 a' b' t.2.1 t.2.2 ∧ UR ⊆ S ∧
      (a ∈ UR ∧ b ∈ UR → UR = S ∧ s(a', b') = s(a, b) ∧ ∀ t' ∈ (markedUnitsOfMKLow h).surv, t'.1 = t.1) := by
  classical
  have hM := Mole.garden_isMolecule G
  set U := markedUnitsOfMKLow h with hU
  obtain ⟨P, RL, m, RR, Q, hL, hm1, hmg, hRLg, hRRg, hleft, hright, hmeet⟩ :=
    (Famc.MarkedGroupUnits.surv_localMK U) hs hvineM hingr hmemb ht
  have hmL : m ∈ L := by rw [hL]; simp
  have hs' : Fama.Spine γF N (P ++ (RL ++ m :: RR) ++ Q) S a b := by rw [hL] at hs; simpa using hs
  obtain ⟨UR, a', b', hsl, hBl, hURS, hPs, hQs⟩ := hs'.segMK hN hB (by simp)
  obtain ⟨L0, R0, HK, hL0, hR0⟩ := hsl.aroundMKLow hN hBl
  have hunits : ∀ u ∈ U.runs, u ∈ Fama.unitBlocks γF G σ Mk := fun u hu =>
    Fama.mem_unitBlocksMk.mpr ⟨S, hS, hσ, by rw [groupUnitsMk_of_markedMKLow h]; exact hu⟩
  -- the runs at the two joints are units, each one class
  have hside : ∀ (Rs : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)) (X : Finset _),
      (∀ v, v ∈ X ↔ ∃ r ∈ Rs, v ∈ r.1) →
      (Rs = [] ∨ Rs ≠ [] ∧ ∃ u ∈ U.runs, ∀ v, v ∈ u.atoms ↔ ∃ r ∈ Rs, v ∈ r.1) →
      (∀ p v, v ∈ X → ((Fama.stSt γF G σ Mk).cls p).getD p = ((Fama.stSt γF G σ Mk).cls v).getD v → p ∈ X) ∧
      (∀ p ∈ X, ∀ q ∈ X, ∃ r, (Fama.stSt γF G σ Mk).cls p = some r ∧ (Fama.stSt γF G σ Mk).cls q = some r) := by
    intro Rs X hX hRs
    rcases hRs with rfl | ⟨-, u, hu, hiff⟩
    · have hX0 : ∀ v, v ∉ X := fun v hv => by simpa using (hX v).mp hv
      exact ⟨fun p v hv => absurd hv (hX0 v), fun p hp => absurd hp (hX0 p)⟩
    · have hXu : ∀ v, v ∈ X ↔ v ∈ u.atoms := fun v => (hX v).trans (hiff v).symm
      refine ⟨fun p v hv hpv => (hXu p).mpr (class_in_unitMKLow (hunits u hu) ((hXu v).mp hv) hpv), ?_⟩
      intro p hp q hq
      exact ⟨u.upper, Fama.stSt_cls_memMk hM σ Mk (hunits u hu) ((hXu p).mp hp),
        Fama.stSt_cls_memMk hM σ Mk (hunits u hu) ((hXu q).mp hq)⟩
  have hl := hside RL L0 hL0 (by rcases hleft with ⟨h0, -⟩ | ⟨h1, h2⟩ <;> [exact Or.inl h0; exact Or.inr ⟨h1, h2.imp
    fun u hu => ⟨hu.1, hu.2.2⟩⟩])
  have hr := hside RR R0 hR0 (by rcases hright with ⟨h0, -⟩ | ⟨h1, h2⟩ <;> [exact Or.inl h0; exact Or.inr ⟨h1, h2.imp
    fun u hu => ⟨hu.1, hu.2.2⟩⟩])
  have hmS : m.1 ⊆ S := ((Famc.SpineG.mem_vine'MK hs) hmL).2
  have H : SDecomp N (Fama.stSt γF G σ Mk).cls UR m.1 L0 R0 a' b' m.2.1 m.2.2 :=
    { toSkelDecomp := HK
      hcls := (Fama.stSt γF G σ Mk).hcls
      hLcl := hl.1
      hRcl := hr.1
      hLc := hl.2
      hRc := hr.2
      hNone := by
        intro v hvU hvL hvR
        have hvm : v ∈ m.1 := by
          rw [HK.hS] at hvU
          simp only [mem_union] at hvU
          rcases hvU with (h1 | h1) | h1
          · exact absurd h1 hvL
          · exact h1
          · exact absurd h1 hvR
        apply Fama.stSt_cls_noneMk hM σ Mk
        intro u hu hvu
        have hu' : u ∈ U.runs := by
          have := unit_in_groupMKLow hS hu hvu (hmS hvm)
          rwa [groupUnitsMk_of_markedMKLow h] at this
        rcases hmeet u hu' v hvu hvm with h1 | h1
        · exact hvL ((hL0 v).mpr h1)
        · exact hvR ((hR0 v).mpr h1) }
  -- orient the joints as in `t`
  have hjt : ({t.2.1, t.2.2} : Finset (GBranch G.tree)) = {m.2.1, m.2.2} := by
    have h1 := (Src.isBlock_of_isSomeVine (U.surv_spec t ht).1)
    have h2 := (Src.isBlock_of_isSomeVine (hvineM m hmL))
    rw [← hm1] at h1
    exact Vine.block_joints_unique G.molecule h1 h2
  have hfin : a ∈ UR ∧ b ∈ UR → UR = S ∧ a' = a ∧ b' = b ∧ ∀ t' ∈ U.surv, t'.1 = t.1 := by
    rintro ⟨ha, hb⟩
    have hP : P = [] := by
      by_contra hP
      obtain ⟨P', s, hPs'⟩ := (List.eq_nil_or_concat P).resolve_left hP
      rw [List.concat_eq_append] at hPs'
      exact (hPs P' s hPs').2.2 ha
    have hQ : Q = [] := by
      by_contra hQ
      obtain ⟨s, Q', hQs'⟩ := List.exists_cons_of_ne_nil hQ
      exact (hQs s Q' hQs').2.2 hb
    subst hP hQ
    have hsl' : Fama.Spine γF N L UR a' b' := by rw [hL]; simpa using hsl
    have hUR : UR = S := by
      ext v; rw [hsl'.mem_iff v, hs.mem_iff v]
    obtain ⟨t0, L', hL'⟩ := List.exists_cons_of_ne_nil hs.ne_nilMK
    obtain ⟨L'', tl, hL''⟩ := (List.eq_nil_or_concat L).resolve_left hs.ne_nilMK
    rw [List.concat_eq_append] at hL''
    refine ⟨hUR, ?_, ?_, ?_⟩
    · rw [hL'] at hs hsl'
      rw [← hsl'.cons_fstMK, hs.cons_fstMK]
    · rw [hL''] at hs hsl'
      rw [← hsl'.last_sndMK, hs.last_sndMK]
    · intro t' ht'
      obtain ⟨-, hit', hmk'⟩ := U.surv_spec t' ht'
      have hng : ∀ x y, ¬ Fama.UnmMemMK γF G Mk (t'.1, x, y) := by
        rintro x y ⟨c, hcV, hcMk, hc⟩
        rcases hmk' with ⟨c', hc'Mk, -, hc't⟩ | hno
        · exact hcMk ((Fama.clvine_eq_of_atomsMK (hc.trans hc't.symm)) ▸ hc'Mk)
        · exact hno c hcV hc
      obtain ⟨p, q, hm' | hm'⟩ := hmemb _ hit' <;>
      · have hmL' := hm'
        rw [hL] at hmL'
        simp only [List.nil_append, List.append_nil, List.mem_append, List.mem_cons] at hmL'
        rcases hmL' with hr' | heq | hr'
        · exact absurd (hRLg _ hr') (hng _ _)
        · rw [← hm1, ← heq]
        · exact absurd (hRRg _ hr') (hng _ _)
  rcases Mole.finset_pair_eq_pair_iff.mp hjt with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine ⟨UR, L0, R0, a', b', ?_, hURS, fun hab => ?_⟩
    · rw [← hm1, e1, e2]
      exact H
    · obtain ⟨h1, h2, h3, h4⟩ := hfin hab
      exact ⟨h1, by rw [h2, h3], h4⟩
  · refine ⟨UR, R0, L0, b', a', ?_, hURS, fun hab => ?_⟩
    · rw [← hm1, e1, e2]
      exact H.symm
    · obtain ⟨h1, h2, h3, h4⟩ := hfin hab
      exact ⟨h1, by rw [h2, h3, Sym2.eq_swap], h4⟩

end

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **o75 Lemma 3 (ii), with 75-W1**: the image of a survivor of a marked SG group in `G_sb`. -/
theorem survivor_imageMK'Low {σ : Prescription G} {Mk : Set (Fama.CLVineG γF G)} {S : Finset (GBranch G.tree)}
    (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG) (h : Fama.markedGroup γF G Mk S)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ (markedUnitsOfMKLow h).surv) :
    ∃ O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule,
      O.atoms = t.1.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∧
      O.upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1 ∧
      O.lower = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.2 ∧
      Set.InjOn ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) t.1 ∧
      (∀ c, (Fama.stSt γF G σ Mk).cls ((Fama.stSt γF G σ Mk).M.ob c) ≠ none → c ∈ O.atoms → c = O.upper ∨ c = O.lower) ∧
      (∀ z ∈ t.1, z ≠ t.2.1 → z ≠ t.2.2 → (Fama.stSt γF G σ Mk).cls z = none) ∧
      ((Src.IsSomeVine γF (Fama.stSt γF G σ Mk).G.molecule O.atoms O.upper O.lower ∧
          ∃ hvc, O.shape = Src.VineLikeObject.vc hvc) ∨
        (Src.AllowedCollectionObject γF (Fama.stSt γF G σ Mk).G O ∧
          (∃ R, O.shape = Src.VineLikeObject.hyper R ∧ ¬ G.molecule.InGroup t.1 ((Fama.stSt γF G σ Mk).M.od R.added)) ∧
          ∀ t' ∈ (markedUnitsOfMKLow h).surv, t'.1 = t.1)) := by
  classical
  have hM : G.molecule.IsMolecule := Mole.garden_isMolecule G
  have hvt : Src.IsSomeVine γF G.molecule t.1 t.2.1 t.2.2 := ((markedUnitsOfMKLow h).surv_spec t ht).1
  -- the common conclusion from a decomposition in the garden molecule
  have fromVine : ∀ (UR L0 R0 : Finset (GBranch G.tree)) (a' b' : GBranch G.tree),
      SDecomp G.molecule (Fama.stSt γF G σ Mk).cls UR t.1 L0 R0 a' b' t.2.1 t.2.2 → ∃ O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule,
      O.atoms = t.1.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∧
      O.upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1 ∧
      O.lower = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.2 ∧
      Set.InjOn ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) t.1 ∧
      (∀ c, (Fama.stSt γF G σ Mk).cls ((Fama.stSt γF G σ Mk).M.ob c) ≠ none → c ∈ O.atoms → c = O.upper ∨ c = O.lower) ∧
      (∀ z ∈ t.1, z ≠ t.2.1 → z ≠ t.2.2 → (Fama.stSt γF G σ Mk).cls z = none) ∧
      ((Src.IsSomeVine γF (Fama.stSt γF G σ Mk).G.molecule O.atoms O.upper O.lower ∧
          ∃ hvc, O.shape = Src.VineLikeObject.vc hvc) ∨
        (Src.AllowedCollectionObject γF (Fama.stSt γF G σ Mk).G O ∧
          (∃ R, O.shape = Src.VineLikeObject.hyper R ∧ ¬ G.molecule.InGroup t.1 ((Fama.stSt γF G σ Mk).M.od R.added)) ∧
          ∀ t' ∈ (markedUnitsOfMKLow h).surv, t'.1 = t.1)) := by
    intro UR L0 R0 a' b' H
    obtain ⟨O, hOa, hOu, hOl, hOv, hOs⟩ := vine_objectStMKLow (Fama.stSt γF G σ Mk) H hvt
    refine ⟨O, hOa, hOu, hOl, H.injOn_piMK _, fun c hcn hcO => ?_, H.interior_noneMK, Or.inl ⟨hOv, hOs⟩⟩
    rw [hOu, hOl]
    exact H.hinge_imageMK _ c hcn (hOa ▸ hcO)
  have h' := h
  obtain ⟨c, -, -, hci⟩ := h'
  rcases hci with ⟨a, b, n, x, y, hB, hI⟩ | ⟨a, b, e, n, x, y, hends, hn2, hBe, hI⟩
  · -- a VC
    obtain ⟨L, hs⟩ := Fama.Spine.of_chain (Fama.chainIngredientG_spec hI).1
    obtain ⟨UR, L0, R0, a', b', H, -, -⟩ := surv_sdecompMKLow hM hs hB (fun t ht => ((Famc.SpineG.mem_vine'MK hs) ht).1)
      (fun t ht => Or.inl ⟨a, b, L.length, t.2.1, t.2.2, hB, hs.ingredient_of_mem ht⟩)
      (fun T hT => Fama.isIngredient_vc hM hB hs hT) hS hσ h ht
    exact fromVine UR L0 R0 a' b' H
  · -- an HVC
    have hab : a ≠ b := hBe.2.2.2.1
    have hne : G.molecule.atom e ≠ G.molecule.atom (G.molecule.mate e) := by
      intro h0
      unfold Molecule.ends at hends
      rw [h0] at hends
      rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hab (h1.symm.trans h2)
      · exact hab (h2.symm.trans h1)
    have hN := Vine.eraseBond_isMolecule G.molecule hM e hne
    obtain ⟨L, hs, hlen⟩ := Fama.Spine.of_chain_len (Fama.chainIngredientG_spec hI).1
    have hlen2 : 2 ≤ L.length := hlen ▸ hn2
    have hmemb : ∀ T, Fama.IsIngredientG γF G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L :=
      fun T hT => Fama.isIngredient_hvc hM hends hBe hs hlen2 hT
    obtain ⟨UR, L0, R0, a', b', H, hURS, hfin⟩ := surv_sdecompMKLow hN hs hBe
      (fun t ht => (Fama.vine_transfer G.molecule hends (hs.not_both hlen2 ht) t.2.1 t.2.2).mp ((Famc.SpineG.mem_vine'MK hs) ht).1)
      (fun t ht => Or.inr ⟨a, b, e, L.length, t.2.1, t.2.2, hends, hlen2, hBe, hs.ingredient_of_mem ht⟩)
      hmemb hS hσ h ht
    by_cases hab' : a ∈ UR ∧ b ∈ UR
    · -- 75-W1: the only survivor of an HVC; its image is an HV
      obtain ⟨-, hab'', hsame⟩ := hfin hab'
      have hnot : ¬ (a ∈ t.1 ∧ b ∈ t.1) := by
        obtain ⟨p, q, hm | hm⟩ := hmemb _ ((markedUnitsOfMKLow h).surv_spec t ht).2.1
        · exact hs.not_both hlen2 hm
        · exact hs.not_both hlen2 hm
      have hvN : Src.IsSomeVine γF (Mole.eraseBond G.molecule e) t.1 t.2.1 t.2.2 :=
        (Fama.vine_transfer G.molecule hends hnot t.2.1 t.2.2).mpr hvt
      obtain ⟨O, hOA, hOa, hOu, hOl, R, hR, hod⟩ :=
        hyper_objectStMKLow (Fama.stSt γF G σ Mk) H (hends.trans hab''.symm) hvN
      have hnin : ¬ G.molecule.InGroup t.1 ((Fama.stSt γF G σ Mk).M.od R.added) := by
        rw [hod]
        rintro ⟨h1, h2⟩
        unfold Molecule.ends at hends
        rcases Sym2.eq_iff.mp hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact hnot ⟨e1 ▸ h1, e2 ▸ h2⟩
        · exact hnot ⟨e2 ▸ h2, e1 ▸ h1⟩
      refine ⟨O, hOa, hOu, hOl, H.injOn_piMK _, fun c hcn hcO => ?_, H.interior_noneMK,
        Or.inr ⟨hOA, ⟨R, hR, hnin⟩, hsame⟩⟩
      rw [hOu, hOl]
      exact H.hinge_imageMK _ c hcn (hOa ▸ hcO)
    · -- the decomposition lives in the garden molecule
      have htr : ∀ X x' y', X ⊆ UR → (Mole.eraseBond G.molecule e).IsBlock X x' y' → G.molecule.IsBlock X x' y' :=
        fun X x' y' hX hb => (block_transfer G.molecule hends (fun hh => hab' ⟨hX hh.1, hX hh.2⟩) x' y').mp hb
      exact fromVine UR L0 R0 a' b'
        { toSkelDecomp := H.toSkelDecomp.transferMK hM htr
          hcls := H.hcls
          hLcl := H.hLcl
          hRcl := H.hRcl
          hLc := H.hLc
          hRc := H.hRc
          hNone := H.hNone }

end

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **o75 Lemma 3 for the survivor list `𝒞_E`** (`Fama.survivorsMk γF`): every survivor has its residual image in `G_sb`,
a vine or (75-W1) an HV. -/
theorem survivorsMk_imageMK'Low {σ : Prescription G} {Mk : Set (Fama.CLVineG γF G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ Fama.survivorsMk γF G σ Mk) :
    ∃ O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule,
      O.atoms = t.1.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∧
      O.upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1 ∧
      O.lower = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.2 ∧
      Set.InjOn ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) t.1 ∧
      (∀ c, (Fama.stSt γF G σ Mk).cls ((Fama.stSt γF G σ Mk).M.ob c) ≠ none → c ∈ O.atoms → c = O.upper ∨ c = O.lower) ∧
      (∀ z ∈ t.1, z ≠ t.2.1 → z ≠ t.2.2 → (Fama.stSt γF G σ Mk).cls z = none) ∧
      ((Src.IsSomeVine γF (Fama.stSt γF G σ Mk).G.molecule O.atoms O.upper O.lower ∧
          ∃ hvc, O.shape = Src.VineLikeObject.vc hvc) ∨
        (Src.AllowedCollectionObject γF (Fama.stSt γF G σ Mk).G O ∧
          ∃ R, O.shape = Src.VineLikeObject.hyper R ∧ ¬ G.molecule.InGroup t.1 ((Fama.stSt γF G σ Mk).M.od R.added))) := by
  obtain ⟨S, hS, hσ, h, ht'⟩ := mem_survivorsMk_iffMKLow.mp ht
  obtain ⟨O, h1, h2, h3, h4, h5, h6, h7⟩ := survivor_imageMK'Low hS hσ h ht'
  exact ⟨O, h1, h2, h3, h4, h5, h6, h7.imp id fun hh => ⟨hh.1, hh.2.1⟩⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **The image of a survivor in `G_sb`** (B2a's `survivorsMk_imageMK`, in the form `survivorsMk_imageMK'Low` that
records the added bond of a 75-W1 HV). -/
noncomputable def survObjLow {σ : Prescription G} {Mk : Set (Fama.CLVineG γF G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ Fama.survivorsMk γF G σ Mk) :
    Src.Object γF (Fama.stSt γF G σ Mk).G.molecule :=
  Classical.choose (survivorsMk_imageMK'Low ht)

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- The survivor Fama.VineA.NormalizedSplice.objects γF of `G_sb`, in the order of `Fama.survivorsMk γF`. -/
noncomputable def survObjsLow (G : Garden w) (σ : Prescription G) (Mk : Set (Fama.CLVineG γF G)) :
    List (Src.Object γF (Fama.stSt γF G σ Mk).G.molecule) :=
  (Fama.survivorsMk γF G σ Mk).attach.map fun t => survObjLow t.2

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkSubpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset
open WaveTurbulence.RedSplice (Prescription stSt survivorsMk)
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- **The survivors of the marked splice** as world `SurvivorDataG γF` (`m` = their number, `surv` = main's `survObjs`,
`prot` = the protected set from B4). -/
noncomputable def survDataLow (G : Garden w) (σ : Prescription G) (Mk : Set (Fama.CLVineG γF G))
    (prot : Finset (GBranch (Fama.stSt γF G σ Mk).G.tree)) : SurvivorDataG γF (Fama.stSt γF G σ Mk).G :=
  ⟨(survObjsLow G σ Mk).length, (survObjsLow G σ Mk).get, prot⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkSubpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset WaveTurbulence.Reg.Skeleton
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- **The marked Stage-1′ piece of the construction** (main's `Fama.stage1PieceOf P.γ` at the marking `Mk`, the survivors,
and B4's protected set, pins, filters and indicator). Ruling R187: the optional last argument `lb` (constant lower
bounds, default none). -/
noncomputable def stage1PieceMKOfLow (P : WTParams) [Fact (P.γ ≤ 1 / 2)] {R : ℕ} {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S)
    (Mk : Set (Fama.CLVineG P.γ S)) (prot : Finset (GBranch (Fama.stSt P.γ S σ Mk).G.tree)) (nProt : ℕ)
    (fix : GBranch (Fama.stSt P.γ S σ Mk).G.tree → Option ℝ)
    (filt : GBranch (Fama.stSt P.γ S σ Mk).G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode (Fama.stSt P.γ S σ Mk).G.tree → Mom P.d) → ℝ)
    (lb : GBranch (Fama.stSt P.γ S σ Mk).G.tree → Option ℝ := fun _ => none) : Stage1PieceMKG P R where
  toStage1PieceGD := Fama.VineA.NormalizedSplice.stage1PieceOf P.γ P.d hS LG hd σ Mk
  surv := survDataLow S σ Mk prot
  nProt := nProt
  fix := fix
  filt := filt
  ind := ind
  lb := lb

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
variable {w : ℕ}

/-- **The marked piece of a prescribed point** (B2c's `stage1PieceMKOf` at the point, marked set `classMkLow mkF a`).
Ruling R187: the optional last argument `lb` (constant lower bounds on free atoms, default none). -/
def classPieceLow (P : WTParams) [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (mkF : Fama.Stage1Mk.MarkFn P.γ (2 * R)) (a : Fama.VineA.PrescribedPrimeGarden P.γ (2 * R))
    (prot : Finset (GBranch (Fama.stSt P.γ a.prime.skeleton a.totalSigma (classMkLow mkF a)).G.tree)) (nProt : ℕ)
    (fix : GBranch (Fama.stSt P.γ a.prime.skeleton a.totalSigma (classMkLow mkF a)).G.tree → Option ℝ)
    (filt : GBranch (Fama.stSt P.γ a.prime.skeleton a.totalSigma (classMkLow mkF a)).G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode (Fama.stSt P.γ a.prime.skeleton a.totalSigma (classMkLow mkF a)).G.tree → Mom P.d) → ℝ)
    (lb : GBranch (Fama.stSt P.γ a.prime.skeleton a.totalSigma (classMkLow mkF a)).G.tree → Option ℝ := fun _ => none) :
    Stage1PieceMKG P R :=
  stage1PieceMKOfLow P a.prime.prime.1 a.layered a.prime.decodes a.totalSigma (classMkLow mkF a) prot nProt fix
    filt ind lb

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
variable {w : ℕ}

/-- **`MarkedClassRepresentsMKLow cP cθ P`** (B3 + B3s; ruling R177, B4 design step 7). Binders: those of
`Stage1ReductionAtMKFullG` (coset base `0`), then a fine marking `mkF` (`FineMarkingLow`), then a fine′ class `π` that is
non-zero (stem-free weight, or every point of the class is stem-clean). Conclusion: for the piece of `Fama.Represents.repPt P.γ π` at
the marked set `classMkLow mkF (Fama.Represents.repPt P.γ π)` and `nProt = |Π(Fama.Represents.repPt P.γ π)|`, B3s's data `prot, fix, filt, ind, selR` exist with
`ClassPieceOKLow` for the class value `classValueLow`. Ruling R185 (F-B3s-8): `J.card = R` after the cap set, as in
`MarkedComponentBoundAtILow` (at `J = ∅` the class value has degree `N + R` in the profiles, the mass only `b ^ N`).
Ruling R187 (F-H3-1): the data also include the constant lower bounds `lb` (`lb π = some s` at the free parents of
`dParent`-pinned object tops), with `PieceRestB3sLow.lb_*` and `ClassPieceOKLow.sel_lb`. -/
def MarkedClassRepresentsMKLow (cP cθ : ℝ) (P : WTParams) [Fact (P.γ ≤ 1 / 2)] : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (J : Finset (Fin (2 * R))), J.card = R → ∀ (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ),
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t,
  ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    1 ≤ b → (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) → (∀ j, P.L ≤ Rs j) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∀ (mkF : Fama.Stage1Mk.MarkFn P.γ (2 * R)), FineMarkingLow J pat t s kSel σ mkF →
  ∀ π : Fama.Represents.PcA P.γ R p (objKind (2 * R)) A mkF,
    (¬ StemDep σ kSel ∨ ∀ a : Fama.VineA.PrescribedPrimeGarden P.γ (2 * R),
      Fama.VineA.PrescribedPrimeGarden.Related P.γ (p := p) (kind := objKind (2 * R)) (Fama.Represents.repPt P.γ π) a mkF → CleanPtLow J a) →
  ∃ (prot : Finset (GBranch (Fama.stSt P.γ (Fama.Represents.repPt P.γ π).prime.skeleton (Fama.Represents.repPt P.γ π).totalSigma (classMkLow mkF (Fama.Represents.repPt P.γ π))).G.tree))
    (fix : GBranch (Fama.stSt P.γ (Fama.Represents.repPt P.γ π).prime.skeleton (Fama.Represents.repPt P.γ π).totalSigma (classMkLow mkF (Fama.Represents.repPt P.γ π))).G.tree → Option ℝ)
    (filt : GBranch (Fama.stSt P.γ (Fama.Represents.repPt P.γ π).prime.skeleton (Fama.Represents.repPt P.γ π).totalSigma (classMkLow mkF (Fama.Represents.repPt P.γ π))).G.tree →
      Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode (Fama.stSt P.γ (Fama.Represents.repPt P.γ π).prime.skeleton (Fama.Represents.repPt P.γ π).totalSigma (classMkLow mkF (Fama.Represents.repPt P.γ π))).G.tree → Mom P.d) →
      ℝ)
    (lb : GBranch (Fama.stSt P.γ (Fama.Represents.repPt P.γ π).prime.skeleton (Fama.Represents.repPt P.γ π).totalSigma (classMkLow mkF (Fama.Represents.repPt P.γ π))).G.tree → Option ℝ)
    (selR : Finset (GBranch (Fama.stSt P.γ (Fama.Represents.repPt P.γ π).prime.skeleton (Fama.Represents.repPt P.γ π).totalSigma (classMkLow mkF (Fama.Represents.repPt P.γ π))).G.tree)),
    ClassPieceOKLow (classPieceLow P mkF (Fama.Represents.repPt P.γ π) prot (protI (Fama.Represents.repPt P.γ π).layered J pat t s kSel).card fix filt ind lb) selR
      N cP cθ t b roots kSel Rs (classValueLow P p J pat kSel t s A roots h Rf σ Rs dag mkF π)

end

/-- **The B3s statement over `𝒱_γ`, gate form** (interface of item I; `status/L8-split.txt`): main's
`WTPrefix (Stage1MKGate.MarkedClassRepresentsMK cP cθ)` at `P.γ ≤ 1 / 2`, the family being `P.γ`. -/
def MarkedClassRepresentsGateLow (cP cθ : ℝ) : Prop :=
  WTPrefix fun P => ∀ h : P.γ ≤ 1 / 2, haveI : Fact (P.γ ≤ 1 / 2) := ⟨h⟩; MarkedClassRepresentsMKLow cP cθ P

end WaveTurbulence.GammaLow.Flower
