/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvMK
public import WaveTurbulence.Foundations.FinalCount.RedSpliceStage
public import WaveTurbulence.Foundations.FinalCount.RedSpliceRes4
import Mathlib.Tactic

/-!
# B2a MK-RUNS: the chosen runs and survivors, and the residual decomposition of a survivor

* `markedUnitsOfMK h`: the `MarkedGroupUnits` chosen by `groupUnitsMk` for a marked group
  (`groupUnitsMk_of_markedMK`, `mem_survivorsMk_iffMK`);
* `groupUnitsMk_spineMK`, `unitBlocks_chainMK'`: every run is a spine of unmarked `𝒱`-ingredients;
* `Spine.aroundMK`: a block chain cut around one member is a `SkelDecomp`;
* `surv_sdecompMK`: **every survivor `t` of a marked SG group is decomposed (`SDecomp`) in the splice
  `stSt G σ Mk`** around the runs at its two joints, exactly as main's skipped ingredient is (`skip_sdecomp`): in the
  garden molecule, or (75-W1) in the adjoint of an HVC whose only survivor is `t`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1

section generic
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- **A block chain cut around one member.** -/
theorem Spine.aroundMK (hM : M.IsMolecule) {RL RR : List (Finset V × V × V)} {m : Finset V × V × V}
    {U : Finset V} {a b : V} (hs : Spine M (RL ++ m :: RR) U a b) (hB : M.IsBlock U a b) :
    ∃ L0 R0, SkelDecomp M U m.1 L0 R0 a b m.2.1 m.2.2 ∧ (∀ v, v ∈ L0 ↔ ∃ r ∈ RL, v ∈ r.1) ∧
      (∀ v, v ∈ R0 ↔ ∃ r ∈ RR, v ∈ r.1) := by
  -- the member itself
  obtain ⟨UA, x, y, hsA, hBA, -, hPA, hQA⟩ :=
    (show Spine M (RL ++ [m] ++ RR) U a b by simpa using hs).segMK hM hB (by simp)
  obtain ⟨hmA, -⟩ := hsA.singletonMK
  subst hmA
  simp only at hPA hQA ⊢
  -- the left part
  obtain ⟨L0, hL0, hLiff⟩ : ∃ L0, (L0 = ∅ ∧ x = a ∨ (x ≠ a ∧ M.IsBlock L0 a x ∧ L0 ∩ UA = {x})) ∧
      ∀ v, v ∈ L0 ↔ ∃ r ∈ RL, v ∈ r.1 := by
    by_cases hRL : RL = []
    · subst hRL
      refine ⟨∅, Or.inl ⟨rfl, hs.cons_fstMK⟩, fun v => by simp⟩
    · obtain ⟨UL, a', p, hsL, hBL, -, hPL, hQL⟩ :=
        (show Spine M ([] ++ RL ++ (UA, x, y) :: RR) U a b by simpa using hs).segMK hM hB hRL
      have ha' : a' = a := by
        obtain ⟨r0, R', rfl⟩ := List.exists_cons_of_ne_nil hRL
        rw [← hsL.cons_fstMK]
        exact (show Spine M (r0 :: (R' ++ (UA, x, y) :: RR)) U a b by simpa using hs).cons_fstMK
      subst ha'
      obtain ⟨h1, h2, -⟩ := hQL (UA, x, y) RR rfl
      simp only at h1
      subst h1
      exact ⟨UL, Or.inr ⟨hsL.ends.2.2.symm, hBL, h2⟩, hsL.mem_iff⟩
  -- the right part
  obtain ⟨R0, hR0, hRiff⟩ : ∃ R0, (R0 = ∅ ∧ y = b ∨ (y ≠ b ∧ M.IsBlock R0 y b ∧ R0 ∩ UA = {y})) ∧
      ∀ v, v ∈ R0 ↔ ∃ r ∈ RR, v ∈ r.1 := by
    by_cases hRR : RR = []
    · subst hRR
      refine ⟨∅, Or.inl ⟨rfl, (show Spine M (RL ++ [(UA, x, y)]) U a b by simpa using hs).last_sndMK⟩,
        fun v => by simp⟩
    · obtain ⟨UR, q, b', hsR, hBR, -, hPR, hQR⟩ :=
        (show Spine M ((RL ++ [(UA, x, y)]) ++ RR ++ []) U a b by simpa using hs).segMK hM hB hRR
      have hb' : b' = b := by
        obtain ⟨R', rl, hR'⟩ := (List.eq_nil_or_concat RR).resolve_left hRR
        subst hR'
        rw [← (show Spine M (R' ++ [rl]) UR q b' by simpa using hsR).last_sndMK]
        exact (show Spine M ((RL ++ (UA, x, y) :: R') ++ [rl]) U a b by simpa using hs).last_sndMK
      subst hb'
      obtain ⟨h1, h2, -⟩ := hPR RL (UA, x, y) rfl
      simp only at h1
      subst h1
      exact ⟨UR, Or.inr ⟨hsR.ends.2.2, hBR, by rw [inter_comm]; exact h2⟩, hsR.mem_iff⟩
  refine ⟨L0, R0, ⟨hM, ?_, hB, hBA, hL0, hR0, ?_⟩, hLiff, hRiff⟩
  · ext v
    rw [hs.mem_iff v, mem_union, mem_union, hLiff, hRiff]
    simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro ⟨r, hr | rfl | hr, hv⟩
      · exact Or.inl (Or.inl ⟨r, hr, hv⟩)
      · exact Or.inl (Or.inr hv)
      · exact Or.inr ⟨r, hr, hv⟩
    · rintro ((⟨r, hr, hv⟩ | hv) | ⟨r, hr, hv⟩)
      · exact ⟨r, Or.inl hr, hv⟩
      · exact ⟨_, Or.inr (Or.inl rfl), hv⟩
      · exact ⟨r, Or.inr (Or.inr hr), hv⟩
  · rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨r, hr, hvr⟩ := (hLiff v).mp hv
    obtain ⟨r', hr', hvr'⟩ := (hRiff v).mp hv'
    exact Finset.disjoint_left.mp (hs.sepMK hr hr') hvr hvr'

/-- A decomposition whose blocks are blocks of another molecule is a decomposition there. -/
theorem SkelDecomp.transferMK {D₂ : Type*} [Fintype D₂] [DecidableEq D₂] {N : Molecule V D₂}
    {S A L0 R0 : Finset V} {a b x y : V} (H : SkelDecomp N S A L0 R0 a b x y) (hM : M.IsMolecule)
    (htr : ∀ X x' y', X ⊆ S → N.IsBlock X x' y' → M.IsBlock X x' y') : SkelDecomp M S A L0 R0 a b x y where
  mol := hM
  hS := H.hS
  hSB := htr S a b (subset_refl _) H.hSB
  hA := htr A x y (by rw [H.hS]; intro v hv; simp [hv]) H.hA
  hL := by
    rcases H.hL with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, htr L0 a x (by rw [H.hS]; intro v hv; simp [hv]) h2, h3⟩
  hR := by
    rcases H.hR with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, htr R0 y b (by rw [H.hS]; intro v hv; simp [hv]) h2, h3⟩
  hd := H.hd

end generic

variable {w : ℕ} {G : Garden w}

/-- The runs and survivors chosen for a marked group (those of `groupUnitsMk` and `survivorsMk`). -/
noncomputable def markedUnitsOfMK {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)} (h : markedGroup G Mk S) :
    MarkedGroupUnits G S Mk :=
  Classical.choice (exists_markedGroupUnits h)

/-- The units of a marked group are the chosen runs. -/
theorem groupUnitsMk_of_markedMK {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)} (h : markedGroup G Mk S) :
    groupUnitsMk G Mk S = (markedUnitsOfMK h).runs := by
  classical
  unfold groupUnitsMk
  simp only [h, exists_markedGroupUnits h, ↓reduceIte, ↓reduceDIte]
  rfl

/-- The survivors are the chosen survivors of the marked SG groups. -/
theorem mem_survivorsMk_iffMK {σ : Prescription G} {Mk : Set (CLVine G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} :
    t ∈ survivorsMk G σ Mk ↔ ∃ S, S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧
      ∃ h : markedGroup G Mk S, t ∈ (markedUnitsOfMK h).surv := by
  classical
  unfold survivorsMk
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨S, hS, ht⟩
    obtain ⟨hSm, hσ⟩ := mem_sgGroups.mp hS
    by_cases h : markedGroup G Mk S
    · simp only [h, exists_markedGroupUnits h, ↓reduceIte, ↓reduceDIte] at ht
      exact ⟨S, hSm, hσ, h, ht⟩
    · simp [h] at ht
  · rintro ⟨S, hSm, hσ, h, ht⟩
    refine ⟨S, mem_sgGroups.mpr ⟨hSm, hσ⟩, ?_⟩
    simp only [h, exists_markedGroupUnits h, ↓reduceIte, ↓reduceDIte]
    exact ht

/-- **Every run of a marked group has a spine of unmarked `𝒱`-ingredients** (B0 §5: `unitBlocks_selected_spine`
for runs). -/
theorem groupUnitsMk_spine_of_markedMK {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)}
    (h : markedGroup G Mk S) {u : CLBlock G} (hu : u ∈ groupUnitsMk G Mk S) :
    ∃ L, Spine G.molecule L u.atoms u.upper u.lower ∧ ∀ t ∈ L, ∃ c : CLVine G,
      c ∈ vinesV G ∧ c ∉ Mk ∧ IsIngredient G.molecule S c.atoms ∧ c.atoms = t.1 := by
  rw [groupUnitsMk_of_markedMK h] at hu
  exact (markedUnitsOfMK h).spine u hu

section units
variable {σ : Prescription G} {Mk : Set (CLVine G)}

/-- A unit meeting a group of `𝒞` is a unit of that group. -/
theorem unit_in_groupMK {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) {u : CLBlock G}
    (hu : u ∈ unitBlocks G σ Mk) {v : GBranch G.tree} (hvu : v ∈ u.atoms) (hvS : v ∈ S) :
    u ∈ groupUnitsMk G Mk S := by
  obtain ⟨S', hS', -, hu'⟩ := mem_unitBlocksMk.mp hu
  by_cases hSS : S' = S
  · exact hSS ▸ hu'
  · exact absurd hvS (Finset.disjoint_left.mp (groups_disjoint' (Mole.garden_isMolecule G) hS' hS hSS)
      (groupUnitsMk_sub hu' hvu))

/-- The class of an atom of a unit lies in the unit (`class_in_unit` for every marked set). -/
theorem class_in_unitMK {u : CLBlock G} (hu : u ∈ unitBlocks G σ Mk) {v p : GBranch G.tree}
    (hv : v ∈ u.atoms) (h : ((stSt G σ Mk).cls p).getD p = ((stSt G σ Mk).cls v).getD v) : p ∈ u.atoms := by
  have hM := Mole.garden_isMolecule G
  rw [stSt_cls_memMk hM σ Mk hu hv, Option.getD_some] at h
  by_cases hp : ∃ u' ∈ unitBlocks G σ Mk, p ∈ u'.atoms
  · obtain ⟨u', hu', hpu'⟩ := hp
    rw [stSt_cls_memMk hM σ Mk hu' hpu', Option.getD_some] at h
    by_cases huu : u' = u
    · exact huu ▸ hpu'
    · exfalso
      have hdj := pairwise_symm_forallMK (fun x y h => Disjoint.symm h) (unitBlocks_pairwiseMk hM σ Mk)
        hu' hu huu
      exact Finset.disjoint_left.mp hdj u'.isBlock.2.1 (h ▸ u.isBlock.2.1)
  · push Not at hp
    rw [stSt_cls_noneMk hM σ Mk hp, Option.getD_none] at h
    exact h ▸ u.isBlock.2.1

end units

section sdecomp
variable {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
  {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {S : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {σ : Prescription G} {Mk : Set (CLVine G)}

/-- **The residual decomposition of a survivor** (o75 Lemma 3): in the splice `stSt G σ Mk`, a survivor `t` of a
marked SG group is decomposed around the runs at its joints, inside the segment `UR` of the group's chain made of
`t` and these runs.  If `UR` contains both ends of the chain, it is the whole group and `t` is its only survivor. -/
theorem surv_sdecompMK (hN : N.IsMolecule) (hs : Spine N L S a b) (hB : N.IsBlock S a b)
    (hvineM : ∀ t ∈ L, IsSomeVine G.molecule t.1 t.2.1 t.2.2)
    (hingr : ∀ t ∈ L, IsIngredient G.molecule S t.1)
    (hmemb : ∀ T, IsIngredient G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L)
    (hS : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG) (h : markedGroup G Mk S)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ (markedUnitsOfMK h).surv) :
    ∃ UR L0 R0 a' b', SDecomp N (stSt G σ Mk).cls UR t.1 L0 R0 a' b' t.2.1 t.2.2 ∧ UR ⊆ S ∧
      (a ∈ UR ∧ b ∈ UR → UR = S ∧ s(a', b') = s(a, b) ∧ ∀ t' ∈ (markedUnitsOfMK h).surv, t'.1 = t.1) := by
  classical
  have hM := Mole.garden_isMolecule G
  set U := markedUnitsOfMK h with hU
  obtain ⟨P, RL, m, RR, Q, hL, hm1, hmg, hRLg, hRRg, hleft, hright, hmeet⟩ :=
    U.surv_localMK hs hvineM hingr hmemb ht
  have hmL : m ∈ L := by rw [hL]; simp
  have hs' : Spine N (P ++ (RL ++ m :: RR) ++ Q) S a b := by rw [hL] at hs; simpa using hs
  obtain ⟨UR, a', b', hsl, hBl, hURS, hPs, hQs⟩ := hs'.segMK hN hB (by simp)
  obtain ⟨L0, R0, HK, hL0, hR0⟩ := hsl.aroundMK hN hBl
  have hunits : ∀ u ∈ U.runs, u ∈ unitBlocks G σ Mk := fun u hu =>
    mem_unitBlocksMk.mpr ⟨S, hS, hσ, by rw [groupUnitsMk_of_markedMK h]; exact hu⟩
  -- the runs at the two joints are units, each one class
  have hside : ∀ (Rs : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)) (X : Finset _),
      (∀ v, v ∈ X ↔ ∃ r ∈ Rs, v ∈ r.1) →
      (Rs = [] ∨ Rs ≠ [] ∧ ∃ u ∈ U.runs, ∀ v, v ∈ u.atoms ↔ ∃ r ∈ Rs, v ∈ r.1) →
      (∀ p v, v ∈ X → ((stSt G σ Mk).cls p).getD p = ((stSt G σ Mk).cls v).getD v → p ∈ X) ∧
      (∀ p ∈ X, ∀ q ∈ X, ∃ r, (stSt G σ Mk).cls p = some r ∧ (stSt G σ Mk).cls q = some r) := by
    intro Rs X hX hRs
    rcases hRs with rfl | ⟨-, u, hu, hiff⟩
    · have hX0 : ∀ v, v ∉ X := fun v hv => by simpa using (hX v).mp hv
      exact ⟨fun p v hv => absurd hv (hX0 v), fun p hp => absurd hp (hX0 p)⟩
    · have hXu : ∀ v, v ∈ X ↔ v ∈ u.atoms := fun v => (hX v).trans (hiff v).symm
      refine ⟨fun p v hv hpv => (hXu p).mpr (class_in_unitMK (hunits u hu) ((hXu v).mp hv) hpv), ?_⟩
      intro p hp q hq
      exact ⟨u.upper, stSt_cls_memMk hM σ Mk (hunits u hu) ((hXu p).mp hp),
        stSt_cls_memMk hM σ Mk (hunits u hu) ((hXu q).mp hq)⟩
  have hl := hside RL L0 hL0 (by rcases hleft with ⟨h0, -⟩ | ⟨h1, h2⟩ <;> [exact Or.inl h0; exact Or.inr ⟨h1, h2.imp
    fun u hu => ⟨hu.1, hu.2.2⟩⟩])
  have hr := hside RR R0 hR0 (by rcases hright with ⟨h0, -⟩ | ⟨h1, h2⟩ <;> [exact Or.inl h0; exact Or.inr ⟨h1, h2.imp
    fun u hu => ⟨hu.1, hu.2.2⟩⟩])
  have hmS : m.1 ⊆ S := (hs.mem_vine'MK hmL).2
  have H : SDecomp N (stSt G σ Mk).cls UR m.1 L0 R0 a' b' m.2.1 m.2.2 :=
    { toSkelDecomp := HK
      hcls := (stSt G σ Mk).hcls
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
        apply stSt_cls_noneMk hM σ Mk
        intro u hu hvu
        have hu' : u ∈ U.runs := by
          have := unit_in_groupMK hS hu hvu (hmS hvm)
          rwa [groupUnitsMk_of_markedMK h] at this
        rcases hmeet u hu' v hvu hvm with h1 | h1
        · exact hvL ((hL0 v).mpr h1)
        · exact hvR ((hR0 v).mpr h1) }
  -- orient the joints as in `t`
  have hjt : ({t.2.1, t.2.2} : Finset (GBranch G.tree)) = {m.2.1, m.2.2} := by
    have h1 := (U.surv_spec t ht).1.choose_spec.1
    have h2 := (hvineM m hmL).choose_spec.1
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
    have hsl' : Spine N L UR a' b' := by rw [hL]; simpa using hsl
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
      have hng : ∀ x y, ¬ UnmMemMK G Mk (t'.1, x, y) := by
        rintro x y ⟨c, hcV, hcMk, hc⟩
        rcases hmk' with ⟨c', hc'Mk, -, hc't⟩ | hno
        · exact hcMk ((clvine_eq_of_atomsMK (hc.trans hc't.symm)) ▸ hc'Mk)
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

end sdecomp

end WaveTurbulence.RedSplice
