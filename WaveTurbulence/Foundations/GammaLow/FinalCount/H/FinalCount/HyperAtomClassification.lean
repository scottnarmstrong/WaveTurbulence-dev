/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.HyperAtomClassification
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineCapAdjointClassification
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineCapShortAdjoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainJointNorm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVDegrees
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVHyper
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVMissingJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVOrdinary
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapProperness
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperInVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperMissingJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperSingleVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperVertexConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLocalDartHyper
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGNonVII
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGSingleVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGVCInHyperLike
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGVCInVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSideVIILength
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineStemStarts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSubsetVCClassification
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSubsetVCVineLike
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCInTypeV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCJointEdge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCLocalization
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.HyperAtomClassification`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Atom-set versions of the subsetvc classification for hyper objects (COVER-HYPER)

TARGET Lemma subsetvc / DH23 `subsetvc` (L2128) are statements about *subsets* of atoms. The universe's
`SG_hyperLike_in_hyperLike_adjoint` needs designation-level containment (`HyperLikeRealization.IsContained`,
which for equal atom groups requires the same deleted bond up to mates).

Here: if `A ⊆ U` and the two hyper objects have EQUAL atom groups but different designations `f ∉ {e, mate e}`,
then the designated bond `f` is a second bond between the common joints, and the conclusion holds for `f`
unless the joints carry a triple bond (the audit example `HyperGapAudit.triple`, `no_listed_adjoint`).
The hypothesis `bondsBetween a b ≠ 3` is exactly the source's subpro(2) (every triple bond has a hinge atom)
combined with "the container is disjoint from the hinges".  No gap hypothesis is needed in that case. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine.HyperAtoms
open WaveTurbulence.Vine Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- Two hyper realizations on the same atom group with different designated bonds: either the adjoint of
the second one is a T-vine (low family; main: a type-V vine), or the joints carry three bonds. -/
theorem hyper_equal_atoms_other_designation (M : Molecule V D)
    {U : Finset V} {a b x y : V}
    (R : Src.HyperLikeRealization Src.γL M U a b) (P : Src.HyperLikeRealization Src.γL M U x y)
    (hdes : ¬(P.added = R.added ∨ P.added = M.mate R.added))
    (hno3 : M.bondsBetween a b ≠ 3) :
    (Mole.eraseBond M P.added).IsTVine U x y := by
  classical
  have hHR : Mole.IsHyperBlock M U a b := ⟨R.added, R.ends_eq, R.adjoint.1⟩
  have hHP : Mole.IsHyperBlock M U x y := ⟨P.added, P.ends_eq, P.adjoint.1⟩
  have hdU := Mole.hyperBlock_degrees M hHR
  have hdP := Mole.hyperBlock_degrees M hHP
  have hBR := R.adjoint.1
  have hBP := P.adjoint.1
  have hab : a ≠ b := hBR.2.2.2.1
  have hxy : x ≠ y := hBP.2.2.2.1
  have hj : ({x, y} : Finset V) = {a, b} :=
    joints_eq_of_two_low_degrees M (Finset.Subset.refl U) hBR.2.1 hBR.2.2.1 hab hxy
      hdU.1.le hdU.2.1.le hdP.2.2
  have hs : s(x, y) = s(a, b) := by
    have hxa : x ∈ ({a, b} : Finset V) := hj ▸ mem_insert_self _ _
    have hya : y ∈ ({a, b} : Finset V) := hj ▸ mem_insert_of_mem (mem_singleton_self _)
    simp only [mem_insert, mem_singleton] at hxa hya
    rcases hxa with rfl | rfl <;> rcases hya with rfl | rfl
    all_goals first | exact absurd rfl hxy | rfl | exact Sym2.eq_swap
  set e := R.added with he
  set f := P.added with hf
  have hef : e ≠ f := fun h => hdes (Or.inl h.symm)
  have hemf : e ≠ M.mate f := fun h => hdes (Or.inr (by rw [h, M.mate_mate]))
  have hmef : M.mate e ≠ f := fun h => hdes (Or.inr h.symm)
  have hmemf : M.mate e ≠ M.mate f := fun h => hef (Mole.mate_injective M h)
  -- the other designated bond survives in the adjoint of `P`
  have hendsE : M.ends e = s(x, y) := R.ends_eq.trans hs.symm
  have hAdj : (Mole.eraseBond M f).Adj x y := by
    have h2 := Sym2.eq_iff.mp hendsE
    change (M.atom e = x ∧ M.atom (M.mate e) = y) ∨ (M.atom e = y ∧ M.atom (M.mate e) = x) at h2
    rcases h2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨e, hef, hemf⟩, h1, h2⟩
    · refine ⟨⟨M.mate e, hmef, hmemf⟩, h2, ?_⟩
      change M.atom (M.mate (M.mate e)) = y
      rw [M.mate_mate]; exact h1
  have hX := VC_with_joint_adj_isSomeVine (Mole.eraseBond M f) P.adjoint hAdj
  -- lower bound: the surviving bond is a dart in the pair group
  have hpos : 0 < (Mole.eraseBond M f).degIn {x, y} x := by
    obtain ⟨dd, h1, h2⟩ := hAdj
    apply Finset.card_pos.mpr
    refine ⟨dd, Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt _ _ _).mpr h1, ?_, ?_⟩⟩
    · rw [h1]; exact mem_insert_self _ _
    · rw [h2]; exact mem_insert_of_mem (mem_singleton_self _)
  -- low family: (I) contradicts `hno3`, (II) has no joint-to-joint bond, a T-vine is the conclusion
  rcases hX.cases with hXI | hXII | hXT
  · have hpair := (isVine_joint_pair_degrees hXI).1
    rw [template_sigma] at hpair
    exfalso
    apply hno3
    have h2 : (Mole.eraseBond M f).degIn {x, y} x = 2 := by simpa using hpair
    -- M has three bonds between x and y
    have h3 : M.degIn {x, y} x = 3 := by
      have h2e := Sym2.eq_iff.mp P.ends_eq
      change (M.atom f = x ∧ M.atom (M.mate f) = y) ∨ (M.atom f = y ∧ M.atom (M.mate f) = x) at h2e
      rcases h2e with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
      · have := Mole.eraseBond_degIn_endpoint M f h1 h2' hxy (S := {x, y})
          (mem_insert_self _ _) (mem_insert_of_mem (mem_singleton_self _))
        omega
      · have := Mole.eraseBond_degIn_endpoint M (M.mate f) h2' (by rw [M.mate_mate]; exact h1) hxy
          (S := {x, y}) (mem_insert_self _ _) (mem_insert_of_mem (mem_singleton_self _))
        rw [Mole.eraseBond_mate_degIn] at this
        omega
    have hloop : ∀ dd, M.atom dd = x → M.atom (M.mate dd) ≠ x := by
      intro dd hdd hl
      by_cases hd1 : dd = f ∨ dd = M.mate f
      · have hee : M.ends dd = s(x, y) := by
          rcases hd1 with rfl | rfl
          · exact P.ends_eq
          · change s(M.atom (M.mate f), M.atom (M.mate (M.mate f))) = s(x, y)
            rw [M.mate_mate]
            have := P.ends_eq
            change s(M.atom f, M.atom (M.mate f)) = s(x, y) at this
            rw [Sym2.eq_swap]; exact this
        have h2e := Sym2.eq_iff.mp hee
        change (M.atom dd = x ∧ M.atom (M.mate dd) = y) ∨ (M.atom dd = y ∧ M.atom (M.mate dd) = x) at h2e
        rcases h2e with ⟨_, h⟩ | ⟨h, _⟩
        · exact hxy (hl.symm.trans h)
        · exact hxy (hdd.symm.trans h)
      · replace hd1 := not_or.mp hd1
        exact connected_degree_two_no_loop (Mole.eraseBond M f) ((Src.IsSomeVine.vconnected hX)) hBP.2.1 hBP.2.2.1
          hxy (Mole.block_joint_degrees (Mole.eraseBond M f) hBP).1 ⟨⟨dd, hd1.1, hd1.2⟩, hdd, hl⟩
    -- bondsBetween a b = bondsBetween x y
    have hbb : M.bondsBetween a b = M.bondsBetween x y := by
      unfold Molecule.bondsBetween; rw [hs]
    rw [hbb, ← Mole.degIn_pair_eq_bondsBetween M hxy hloop]
    exact h3
  · have hpair := (isVine_joint_pair_degrees hXII).1
    rw [template_sigma] at hpair
    exfalso; simp only at hpair; omega
  · exact hXT

/-- ATOM-SET version of `SG_hyperLike_in_hyperLike_adjoint` (TARGET subsetvc, "subset"): containment is
`A ⊆ U` only.  The universe's version needs designation-level containment; for equal atom groups with
different designations the extra hypothesis `bondsBetween a b ≠ 3` is needed and sufficient. -/
theorem SG_hyperLike_in_hyperLike_adjoint_atoms (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V}
    (R : Src.HyperLikeRealization Src.γL M U a b) (P : Src.HyperLikeRealization Src.γL M A x y) (hAU : A ⊆ U)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    {r r' : Mom d} (hr : R.IsGap L w κ r) (hr' : P.IsGap L w κ r')
    (houter : Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG)
    (hsmall : Molecule.gapKind L γ η r' = .SG) (hno3 : M.bondsBetween a b ≠ 3) :
    ∃ f : D, M.ends f = s(x, y) ∧
      (DoubleChain (Mole.eraseBond M f) A x y 2 ∨ (Mole.eraseBond M f).IsTVine A x y) := by
  by_cases hcont : P.IsContained R
  · exact SG_hyperLike_in_hyperLike_adjoint M hM R P hcont L γ η w c κ hκ hc hr hr' houter hsmall
  · have hAU' : A = U := by
      by_contra hne
      exact hcont ⟨hAU, fun h => absurd h hne⟩
    subst hAU'
    have hdes : ¬(P.added = R.added ∨ P.added = M.mate R.added) := fun h => hcont ⟨hAU, fun _ => h⟩
    exact ⟨P.added, P.ends_eq, Or.inr (hyper_equal_atoms_other_designation M R P hdes hno3)⟩

/-- Atom-set version of `subsetvc_vineLike_classification`. -/
theorem subsetvc_vineLike_classification_atoms (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V}
    (C : Src.VineLikeObject Src.γL M U a b) (P : Src.VineLikeObject Src.γL M A x y) (hAU : A ⊆ U)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    {r r' : Mom d} (hr : C.IsGap L w κ r) (hr' : P.IsGap L w κ r')
    (houter : Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG)
    (hsmall : Molecule.gapKind L γ η r' = .SG) (hno3 : M.bondsBetween a b ≠ 3) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsTVine A x y ∨
      ∃ f : D, M.ends f = s(x, y) ∧
        (DoubleChain (Mole.eraseBond M f) A x y 2 ∨ (Mole.eraseBond M f).IsTVine A x y) := by
  cases C with
  | vc hU =>
    cases P with
    | vc hA =>
      exact subsetvc_vineLike_classification M hM (.vc hU) (.vc hA) hAU L γ η w c κ hκ hc hr hr' houter hsmall
    | hyper P =>
      exact subsetvc_vineLike_classification M hM (.vc hU) (.hyper P) hAU L γ η w c κ hκ hc hr hr' houter hsmall
  | hyper C =>
    cases P with
    | vc hA =>
      exact subsetvc_vineLike_classification M hM (.hyper C) (.vc hA) hAU L γ η w c κ hκ hc hr hr' houter hsmall
    | hyper P =>
      exact Or.inr (Or.inr (Or.inr (SG_hyperLike_in_hyperLike_adjoint_atoms M hM C P hAU
        L γ η w c κ hκ hc hr hr' houter hsmall hno3)))

/-- Atom-set version of `subsetvc_classification`: container is a DV, or a vine-like object (atom-set
containment `A ⊆ U`, no triple bond between its joints) with an LG/ZG gap. -/
theorem subsetvc_classification_atoms (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (P : Src.VineLikeObject Src.γL M A x y) (hAU : A ⊆ U)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    {r' : Mom d} (hr' : P.IsGap L w κ r') (hsmall : Molecule.gapKind L γ η r' = .SG)
    (houter : Src.IsDV Src.γL M U a b ∨ ∃ C : Src.VineLikeObject Src.γL M U a b, M.bondsBetween a b ≠ 3 ∧
      ∃ r : Mom d, C.IsGap L w κ r ∧
        (Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG)) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsTVine A x y ∨
      ∃ e : D, M.ends e = s(x, y) ∧
        (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsTVine A x y) := by
  rcases houter with hDV | ⟨C, hno3, r, hr, hkind⟩
  · exact subsetvc_DV_classification M hM hDV P hAU
  · exact subsetvc_vineLike_classification_atoms M hM C P hAU L γ η w c κ hκ hc hr hr' hkind hsmall hno3

end WaveTurbulence.GammaLow.FinalCount.H
