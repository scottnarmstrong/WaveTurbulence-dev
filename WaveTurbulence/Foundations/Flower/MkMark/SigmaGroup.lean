/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceV0
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedGroupGap
public import WaveTurbulence.Foundations.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.Vine.A.VineHVCObjectGap
public import WaveTurbulence.Foundations.Vine.A.VineGapJointChoice
public import WaveTurbulence.Foundations.FinalCount.S1Gaps
public import WaveTurbulence.Foundations.FinalCount.RedSpliceHVC
public import WaveTurbulence.Foundations.Molecule.VineEraseBondDecoration
public import WaveTurbulence.Foundations.Molecule.VineLocalDartGaps

/-! # B2b-3 MK-MARK σ-bridge, group level: from a group gap kind to the block gap of an ingredient

Main's σ-restriction (`VineA.NormalizedSplice.selDarts` / `selOf`) prescribes the gap kind of the designated object of
every group of `𝒞 = maximalGroups`. Here that kind is carried to the block gap of every ingredient:

* **(D)** `isIngredient_vc_or_hvc`: `IsIngredient M S T` forces `S` to be a VC or an HVC (the two cases of the
  definition); so an HV-only or pure-DV group has no ingredient at all (`not_isIngredient_of_not_vc_hvc`). No CL
  `𝒱`-vine meets the HV/DV branches of the gap-kind case split.
* `desig_atoms_eq`: the designated object of a VC/HVC group has the atoms of the whole group.
* `ingredient_not_both`: an ingredient of a chain of length `≥ 2` does not contain both end joints (main
  `Spine.not_both`), so the deleted bond of an HVC is not internal to any ingredient.
* **(B)+(C)** `ingredient_blockGap_kind`, `ingredient_blockGap_of_groupGapKind`: if the group has kind `k`, then every
  block presentation `(T, p, q)` of an ingredient `T` has a gap of kind `k` at `p`. VC: main `ingredient_gap_eq` in
  the molecule; HVC: the same in the adjoint (`eraseBond_isMolecule`, `eraseBond_decoration_exists`), the designation
  fixed up to mates (`objects_gapKind_iff_of_HVC`), and the gap carried back to the molecule
  (`eraseBond_local_embedding`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace WaveTurbulence.Flower.MkMark
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

section Molecule
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- **(D).** An ingredient certificate makes its group a VC (case 1) or an HVC (case 2). -/
theorem isIngredient_vc_or_hvc {S T : Finset V} (h : IsIngredient M S T) :
    (∃ a b, IsVC M S a b) ∨ (∃ a b, IsHVC M S a b) := by
  rcases h with ⟨a, b, n, x, y, hB, hI⟩ | ⟨a, b, e, n, x, y, he, hn, hB, hI⟩
  · exact Or.inl ⟨a, b, hB, n, VineA.NormalizedSplice.chain_ofVine (Vine.chainIngredient_spec hI).1⟩
  · exact Or.inr ⟨a, b, e, he, hB, n, hn, VineA.NormalizedSplice.chain_ofVine (Vine.chainIngredient_spec hI).1⟩

/-- **(D), exclusion.** A group that is neither a VC nor an HVC (an HV-only or a pure DV group) has no ingredient. -/
theorem not_isIngredient_of_not_vc_hvc {S : Finset V} (hvc : ¬ ∃ a b, IsVC M S a b)
    (hhvc : ¬ ∃ a b, IsHVC M S a b) (T : Finset V) : ¬ IsIngredient M S T :=
  fun h => (isIngredient_vc_or_hvc h).elim hvc hhvc

theorem isBlock_swap {S : Finset V} {a b : V} (h : M.IsBlock S a b) : M.IsBlock S b a := by
  obtain ⟨h0, ha, hb, hab, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h0, hb, ha, fun e => hab e.symm, h3, h4, h1, h2, fun v hv hvb hva => h5 v hv hva hvb, h6⟩

theorem spine_length_pos {L : List (Finset V × V × V)} {U : Finset V} {a c : V}
    (h : RedSplice.Spine M L U a c) : 0 < L.length := by
  cases h with
  | one _ => simp
  | snoc _ _ _ _ => simp

/-- An ingredient of a chain of at least two vines does not contain both end joints. -/
theorem ingredient_not_both {U A : Finset V} {a b x y : V} {n : ℕ}
    (h : Vine.ChainIngredient M U a b n A x y) (hn : 2 ≤ n) : ¬ (a ∈ A ∧ b ∈ A) := by
  cases h with
  | single _ => omega
  | append_left h' hT hi hne =>
    obtain ⟨L, hL, hm⟩ := RedSplice.Spine.mem_of_ingredient h'
    have h1 := spine_length_pos hL
    exact RedSplice.Spine.not_both (RedSplice.Spine.snoc hL hT hi hne)
      (by rw [List.length_append, List.length_singleton]; omega) (List.mem_append_left _ hm)
  | append_last hS hT hi hne =>
    obtain ⟨L, hL⟩ := RedSplice.Spine.of_chain hS
    have h1 := spine_length_pos hL
    exact RedSplice.Spine.not_both (RedSplice.Spine.snoc hL hT hi hne)
      (by rw [List.length_append, List.length_singleton]; omega)
      (List.mem_append_right _ (List.mem_singleton_self _))

theorem atom_ne_of_ends {e : D} {a b : V} (he : M.ends e = s(a, b)) (hab : a ≠ b) :
    M.atom e ≠ M.atom (M.mate e) := by
  intro h
  unfold Molecule.ends at he
  rw [h] at he
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hab (h1.symm.trans h2)
  · exact hab (h2.symm.trans h1)

/-- **(B)+(C), molecule level.** Let `O` be an object on the atoms of a group `S` whose gap has kind `kind`. Then every
block presentation `(T, p, q)` of an ingredient `T` of `S` has a gap of kind `kind` at `p`. -/
theorem ingredient_blockGap_kind (hM : M.IsMolecule) {d : ℕ} (L γ η : ℝ) (base : Mom d) (c : V → Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L base c κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    {S T : Finset V} (O : Object M) (hOS : O.atoms = S) {kind : Molecule.GapKind}
    (hO : O.HasGapKind L γ η base κ kind) (hI : IsIngredient M S T) {p q : V} (hT : M.IsBlock T p q) :
    ∃ r, M.IsBlockGap L base κ T p r ∧ Molecule.gapKind L γ η r = kind := by
  rcases hI with ⟨a, b, n, x, y, hB, hI⟩ | ⟨a, b, e, n, x, y, he, hn, hB, hI⟩
  · -- VC: the designated object is the ordinary block `S`
    obtain ⟨_, ⟨X, hX⟩, _⟩ := Vine.chainIngredient_spec hI
    have hTxy : M.IsBlock T x y := hX.1
    obtain ⟨r, hr, hk⟩ := hO
    unfold VineLikeObject.IsGap at hr
    rcases O with ⟨OA, Ou, Ol, Osh⟩
    change OA = S at hOS
    subst hOS
    cases Osh with
    | hyper R => exact (VineA.block_not_hyper hB R.added R.ends_eq R.adjoint.1).elim
    | vc hv =>
      obtain ⟨rU, hrU, hkU⟩ :=
        (VineA.block_gapKind_joint_iff hM hv.1 hB L γ η base c κ hκ hc0 kind).mp ⟨r, hr, hk⟩
      obtain ⟨rx, hrx⟩ := LGSpine.source_block_joint_gap_exists M hTxy (Or.inl rfl) L base κ
      obtain ⟨ry, hry⟩ := LGSpine.source_block_joint_gap_exists M hTxy (Or.inr rfl) L base κ
      obtain ⟨hx, -⟩ := Stage1.ingredient_gap_eq hM hI hB hκ hc0 hrU hrx hry
      exact (VineA.block_gapKind_joint_iff hM hTxy hT L γ η base c κ hκ hc0 kind).mp ⟨rx, hrx, hx ▸ hkU⟩
  · -- HVC: the designated object is the hyper object with the same deleted bond up to mates
    obtain ⟨_, ⟨X, hX⟩, _⟩ := Vine.chainIngredient_spec hI
    have hch := VineA.NormalizedSplice.chain_ofVine (Vine.chainIngredient_spec hI).1
    have hHVC : IsHVC M S a b := ⟨e, he, hB, n, hn, hch⟩
    let Q : Object M := ⟨S, a, b, .hyper ⟨e, he, ⟨hB, n, hch⟩⟩⟩
    have hQ : Q.HasGapKind L γ η base κ kind :=
      (VineA.objects_gapKind_iff_of_HVC hM O Q hOS (hOS ▸ hHVC) L γ η base c κ hκ hc0 kind).mp hO
    obtain ⟨rU, hrU, hkU⟩ := hQ
    have hne := atom_ne_of_ends he hB.2.2.2.1
    have hN := Vine.eraseBond_isMolecule M hM e hne
    obtain ⟨cN, hκN, hcN⟩ := Vine.eraseBond_decoration_exists M hM e hne L base c κ hκ hc0
    obtain ⟨rx, hrx⟩ := LGSpine.source_block_joint_gap_exists _ hX.1 (Or.inl rfl) L base (fun z => κ z.1)
    obtain ⟨ry, hry⟩ := LGSpine.source_block_joint_gap_exists _ hX.1 (Or.inr rfl) L base (fun z => κ z.1)
    obtain ⟨hx, -⟩ := Stage1.ingredient_gap_eq hN hI hB hκN hcN hrU hrx hry
    have hnot : ¬ M.InGroup T e := RedSplice.not_inGroup_of_ends M he (ingredient_not_both hI hn)
    let F := Vine.eraseBond_local_embedding M e T hnot
    have hTxyM : M.IsBlock T x y := (F.isBlock_iff T (subset_refl T) x y).mp hX.1
    have hrxM : M.IsBlockGap L base κ T x rx := (F.blockGap_iff T (subset_refl T) L base κ x rx).mp hrx
    exact (VineA.block_gapKind_joint_iff hM hTxyM hT L γ η base c κ hκ hc0 kind).mp ⟨rx, hrxM, hx ▸ hkU⟩

end Molecule

section Group
variable {w : ℕ} {G : Garden w}

/-- The designated object of a group with a joint of the kind HV, VC or HVC has the atoms of the whole group
(the clauses of the successor `IsDesig`). -/
theorem desig_atoms_eq {S : Finset (GBranch G.tree)} {a : GBranch G.tree} {O : Object G.molecule}
    (hdes : VineA.NormalizedSplice.IsDesig G S a O)
    (hvl : ∃ a b, IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b) : O.atoms = S := by
  rcases hsk : (RedSplice.groupUnitsOf G S).skip with _ | sk
  · by_cases hu : (RedSplice.groupUnitsOf G S).units = []
    · exact hdes.2.2.2.2.2.2.1 hsk hu hvl
    · exact (hdes.2.2.2.2.1 hsk hu).1
  · rcases hb : sk.bond with _ | e
    · exact (hdes.2.2.1 sk hsk hb).1
    · exact (hdes.2.2.2.1 sk e hsk hb).1

/-- The designated object of a group of `𝒞` has the group's gap kind. -/
theorem designated_hasGapKind {d : ℕ} (L γ η : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ))
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) :
    ∃ a O, VineA.NormalizedSplice.IsDesig G S a O ∧
      O.HasGapKind L γ η base κ (VineA.NormalizedSplice.groupGapKind G L γ η base κ S) := by
  obtain ⟨a, O, -, hO, hdes⟩ := VineA.NormalizedSplice.designatedObject_spec hS
  obtain ⟨k, hk⟩ := Represents.exists_hasGapKind O L γ η base κ
  have he := VineA.NormalizedSplice.groupGapKind_eq L γ η base κ hO hk
  exact ⟨a, O, hdes, he ▸ hk⟩

/-- **(B)+(C), group level.** If a group `S` of `𝒞` has gap kind `kind` (its designated object, main's
`groupGapKind`), then every block presentation `(T, p, q)` of an ingredient `T` of `S` has a gap of kind `kind` at `p`.
-/
theorem ingredient_blockGap_of_groupGapKind (hM : G.molecule.IsMolecule) {d : ℕ} (L γ η : ℝ) (base : Mom d)
    (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ)) (hκ : G.molecule.IsDecoration L base c κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    {S T : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) {kind : Molecule.GapKind}
    (hk : VineA.NormalizedSplice.groupGapKind G L γ η base κ S = kind) (hI : IsIngredient G.molecule S T)
    {p q : GBranch G.tree} (hT : G.molecule.IsBlock T p q) :
    ∃ r, G.molecule.IsBlockGap L base κ T p r ∧ Molecule.gapKind L γ η r = kind := by
  obtain ⟨a, O, hdes, hO⟩ := designated_hasGapKind L γ η base κ hS
  rw [hk] at hO
  have hvl : ∃ a b, IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b := by
    rcases isIngredient_vc_or_hvc hI with ⟨a, b, h⟩ | ⟨a, b, h⟩
    · exact ⟨a, b, Or.inr (Or.inl h)⟩
    · exact ⟨a, b, Or.inr (Or.inr h)⟩
  exact ingredient_blockGap_kind hM L γ η base c κ hκ hc0 O (desig_atoms_eq hdes hvl) hO hI hT

end Group

end WaveTurbulence.Flower.MkMark
