/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.SubproShapeDV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeHost
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Removal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.SubproShapeDV`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# S4-SHAPE: an ordinary collected object inside a double-vine host lies in one of its two vines

The vines of a DV (two type-V vines) have a joint-to-joint bond (`σ = 1`). An ordinary block `U` meeting such a vine `A` without
being nested in it would be in the interleaved case of the overlap classification, where `A = C₁ ∪ C₂` is cut at an interior atom;
the joint bond of `A` joins `C₁ ∖ C₂` to `C₂ ∖ C₁`, so it is neither in `C₁` nor in `C₂`, and the joint of `A` would have internal degree
three. The one- and two-joint cases leave `U` inside the other vine.


**Low-range change (L6-HDS).** The double vines are DV′s of the low family (`σ = 1`, two members of `𝒱_{γL}`;
main: two vines (V)); the joint dart is that of the joint bond (`DS.exists_joint_dart`).
-/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.FinalCountG3 Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- **An ordinary object inside a double vine lies in one of its vines**, unless it contains a whole vine. -/
theorem ordinary_in_dv_vine {M : Molecule V D} (hM : M.IsMolecule) (U : Src.Object Src.γL M)
    {A B : Finset V} {a b : V} (hσ : M.sigma a b = 1) (hA : Src.IsSomeVine Src.γL M A a b)
    (hB : Src.IsSomeVine Src.γL M B a b) (hUD : U.atoms ⊆ A ∪ B) (hAU : ¬ A ⊆ U.atoms) : U.atoms ⊆ A ∨ U.atoms ⊆ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hnA, hnB⟩ := hcon
  have hne : (U.atoms ∩ A).Nonempty := by
    obtain ⟨y, hy, hyB⟩ := Finset.not_subset.mp hnB
    rcases mem_union.mp (hUD hy) with h | h
    · exact ⟨y, mem_inter.mpr ⟨hy, h⟩⟩
    · exact absurd h hyB
  obtain ⟨⟨RU⟩, hdU, hiU⟩ := object_overlap_premises U
  obtain ⟨⟨RA⟩, hdA, hiA⟩ := object_overlap_premises (Src.Object.ofVine hA)
  obtain ⟨hUblk, hAblk, hcl⟩ := Mole.molecule_overlap_classification M hM RU RA hne hnA hAU hdU hdA hiU hiA
  have haB : a ∈ B := hB.block.2.1
  have hbB : b ∈ B := hB.block.2.2.1
  have haA : a ∈ A := hA.block.2.1
  have hbA : b ∈ A := hA.block.2.2.1
  rcases hcl with ⟨h1, hint, _, _⟩ | ⟨_, _, a', b', c, h2, h3, _, _, _, h5, _⟩ | ⟨_, ⟨T⟩⟩
  · apply hnB
    intro y hy
    by_cases hyA : y ∈ A
    · have hy' : y ∈ U.atoms ∩ (Src.Object.ofVine hA).atoms := mem_inter.mpr ⟨hy, hyA⟩
      rw [hint, h1] at hy'
      simp only [Src.Object.ofVine, mem_insert, mem_singleton] at hy'
      rcases hy' with rfl | rfl
      · exact haB
      · exact hbB
    · rcases mem_union.mp (hUD hy) with h | h
      · exact absurd h hyA
      · exact h
  · apply hnB
    intro y hy
    by_cases hyA : y ∈ A
    · have hy' : y ∈ U.atoms ∩ (Src.Object.ofVine hA).atoms := mem_inter.mpr ⟨hy, hyA⟩
      rw [h5] at hy'
      have hc : c ∈ ({(Src.Object.ofVine hA).upper, (Src.Object.ofVine hA).lower} : Finset V) := by rw [h3]; simp
      simp only [Src.Object.ofVine, mem_insert, mem_singleton] at hc
      rw [mem_singleton.mp hy']
      rcases hc with rfl | rfl
      · exact haB
      · exact hbB
    · rcases mem_union.mp (hUD hy) with h | h
      · exact absurd h hyA
      · exact h
  · exfalso
    -- the joint bond of the DV′ (`σ = 1`)
    obtain ⟨z, hza, hzb⟩ := DS.exists_joint_dart hσ
    have hjoints : ({a, b} : Finset V) = {T.p1, T.p3} := T.right_joints
    obtain ⟨y, hy1, hy3⟩ : ∃ y, M.atom y = T.p1 ∧ M.atom (M.mate y) = T.p3 := by
      rcases Mole.finset_pair_eq_pair_iff.mp hjoints with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact ⟨z, hza.trans e1, hzb.trans e2⟩
      · refine ⟨M.mate z, ?_, ?_⟩
        · exact hzb.trans e2
        · rw [M.mate_mate]; exact hza.trans e1
    have hp1A : T.p1 ∈ A := by
      have : T.p1 ∈ ({T.p1, T.p3} : Finset V) := by simp
      rw [← hjoints] at this
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h
      · rw [h]; exact haA
      · rw [h]; exact hbA
    have hp3A : T.p3 ∈ A := by
      have : T.p3 ∈ ({T.p1, T.p3} : Finset V) := by simp
      rw [← hjoints] at this
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h
      · rw [h]; exact haA
      · rw [h]; exact hbA
    have hdegA : M.degIn A T.p1 = 2 := by
      have : T.p1 ∈ ({a, b} : Finset V) := by rw [hjoints]; simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h
      · rw [h]; exact (Mole.block_joint_degrees M hA.block).1
      · rw [h]; exact (Mole.block_joint_degrees M hA.block).2
    have hdeg1 : M.degIn T.C1 T.p1 = 2 := (Mole.block_joint_degrees M T.block1).1
    have hC1A : T.C1 ⊆ A := fun v hv => (Finset.ext_iff.mp T.right_union v).mpr (mem_union_left _ hv)
    have hp3C1 : T.p3 ∉ T.C1 := by
      intro h
      have : T.p3 ∈ T.C1 ∩ T.C2 := mem_inter.mpr ⟨h, T.block2.2.2.1⟩
      rw [T.right_inter] at this
      exact T.block2.2.2.2.1 (mem_singleton.mp this).symm
    have hsub : ((M.dartsAt T.p1).filter fun x => M.InGroup T.C1 x) ⊂ (M.dartsAt T.p1).filter fun x => M.InGroup A x := by
      refine ⟨fun x hx => ?_, fun hall => ?_⟩
      · obtain ⟨h1, h2⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨h1, hC1A h2.1, hC1A h2.2⟩
      · have hy : y ∈ (M.dartsAt T.p1).filter fun x => M.InGroup A x :=
          mem_filter.mpr ⟨(Mole.mem_dartsAt M _ y).mpr hy1, hy1 ▸ hp1A, hy3 ▸ hp3A⟩
        have := (mem_filter.mp (hall hy)).2
        exact hp3C1 (hy3 ▸ this.2)
    have := Finset.card_lt_card hsub
    change M.degIn T.C1 T.p1 < M.degIn A T.p1 at this
    omega

/-- A vine `A` of a valid DV host `A ∪ B` that contains `U ∈ C₂` is an LG/ZG object host of `U`, or is (as an atom set) a member of `C₂`
(`U` itself), or is unselected, in which case its partner vine is a member of `C₂` (G3's `UnselOK`) and gives a new DV host. -/
theorem dv_vine_case {M : Molecule V D} {L γ η : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} (C : CollData M)
    (Unsel : Set (Src.Object Src.γL M)) (hUO : C.UnselOK L γ η w κ Unsel)
    {U : Src.Object Src.γL M} (hU : U ∈ C.C2Of L γ η w κ Unsel)
    {A B : Finset V} {a b : V} (hσ : M.sigma a b = 1) (hA : Src.IsSomeVine Src.γL M A a b)
    (hB : Src.IsSomeVine Src.γL M B a b) (hAB : A ∩ B = {a, b}) (hUA : U.atoms ⊆ A) (hh : Disjoint (A ∪ B) C.hinges) (hC : ∀ i, Disjoint (A ∪ B) (C.collection i).atoms) :
    (∃ (A' B' : Finset V) (a' b' : V), M.sigma a' b' = 1 ∧ Src.IsSomeVine Src.γL M A' a' b' ∧
      Src.IsSomeVine Src.γL M B' a' b' ∧ A' ∩ B' = {a', b'} ∧
      U.atoms ⊆ A' ∪ B' ∧ Disjoint (A' ∪ B') C.hinges ∧ (∀ i, Disjoint (A' ∪ B') (C.collection i).atoms) ∧
      ∃ O ∈ C.C2Of L γ η w κ Unsel, O.atoms = A' ∨ O.atoms = B') ∨
      ∃ Q : Src.Object Src.γL M, (Q.HasGapKind L γ η w κ .LG ∨ Q.HasGapKind L γ η w κ .ZG) ∧ U.atoms ⊆ Q.atoms ∧
        Disjoint Q.atoms C.hinges ∧ ∀ i, Disjoint Q.atoms (C.collection i).atoms := by
  classical
  have hAh : Disjoint A C.hinges := Finset.disjoint_of_subset_left subset_union_left hh
  have hAC : ∀ i, Disjoint A (C.collection i).atoms := fun i => Finset.disjoint_of_subset_left subset_union_left (hC i)
  obtain ⟨r, hr⟩ := source_block_joint_gap_exists M hA.block (Or.inl rfl) L w κ
  have hvc : ∃ h, (Src.Object.ofVine hA).shape = .vc h := ⟨_, rfl⟩
  have hkind : ∀ k, Molecule.gapKind L γ η r = k → (Src.Object.ofVine hA).HasGapKind L γ η w κ k := fun k hk =>
    (object_vc_hasGapKind_iff _ hvc L γ η w κ k).mpr ⟨r, hr, hk⟩
  cases hk : Molecule.gapKind L γ η r with
  | LG => exact Or.inr ⟨Src.Object.ofVine hA, Or.inl (hkind _ hk), hUA, hAh, hAC⟩
  | ZG => exact Or.inr ⟨Src.Object.ofVine hA, Or.inr (hkind _ hk), hUA, hAh, hAC⟩
  | SG =>
    have hsg := hkind _ hk
    have hpool : C.InP L γ η w κ (Src.Object.ofVine hA) := by
      refine ⟨hsg, ?_, hAh, Or.inl ⟨A ∪ B, a, b, ⟨hσ, A, B, hA, hB, hAB, rfl⟩, subset_union_left, hh, hC⟩⟩
      intro i hsub
      have := Finset.disjoint_of_subset_left subset_union_left (hC i)
      exact Finset.disjoint_left.mp this hA.block.2.1 (hsub hA.block.2.1)
    by_cases hmem : Src.Object.ofVine hA ∈ Unsel
    · rcases (hUO.dv _ hmem).2 with ⟨U'', hU'', hsubA⟩ | ⟨A'', a', b', hσ'', hA'', hAv, hAA'', U', hU', hU'A, -⟩
      · -- the unselected vine `A` is covered by a member of `C₂`: by maximality of `U`, `A = U.atoms`
        have hAU : A ⊆ U.atoms := hsubA.trans (hU.2 U'' hU''.1.1 (hUA.trans hsubA))
        exact Or.inl ⟨A, B, a, b, hσ, hA, hB, hAB, hUA.trans subset_union_left, hh, hC, U, hU,
          Or.inl (hUA.antisymm hAU)⟩
      have hU'2 : U' ∈ C.C2Of L γ η w κ Unsel := hU'.1
      have hd := c2Of_disjoint_c1_hinges C hU'2
      refine Or.inl ⟨A'', A, a', b', hσ'', hA'', hAv, hAA'', hUA.trans subset_union_right, ?_, ?_, U', hU'2, Or.inl hU'A⟩
      · exact Finset.disjoint_union_left.mpr ⟨hU'A ▸ hd.2, hAh⟩
      · exact fun i => Finset.disjoint_union_left.mpr ⟨hU'A ▸ hd.1 i, hAC i⟩
    · have hAU : A ⊆ U.atoms := hU.2 _ ⟨hpool, hmem⟩ hUA
      exact Or.inl ⟨A, B, a, b, hσ, hA, hB, hAB, hUA.trans subset_union_left, hh, hC, U, hU,
        Or.inl (hUA.antisymm hAU)⟩

/-- **The double-vine witness reduction, discharged.** For a member `U` of `C₂` with an ordinary shape and fewer than four atoms
(a vine contained in `U` would be a double bond, with `σ = 2`; the DV′ has `σ = 1`), given G3's `UnselOK`: a DV host of `U` reduces to a DV host with a
collected vine, or to an LG/ZG object host. -/
theorem dvWitnessReduction_of_unselOK {M : Molecule V D} (hM : M.IsMolecule) {L γ η : ℝ} {w : Mom d}
    {κ : D → (Fin d → ℤ)} (C : CollData M) (Unsel : Set (Src.Object Src.γL M)) (hUO : C.UnselOK L γ η w κ Unsel)
    {U : Src.Object Src.γL M} (hU : U ∈ C.C2Of L γ η w κ Unsel) (hU4 : U.atoms.card < 4) :
    DVWitnessReduction L γ η w κ C Unsel U := by
  intro A B a b hσ hA hB hAB hUD hh hC
  have hnV : ∀ {S : Finset V}, Src.IsSomeVine Src.γL M S a b → ¬ S ⊆ U.atoms := by
    intro S hS hsub
    have hI := DS.typeI_of_card_lt_four hS (lt_of_le_of_lt (Finset.card_le_card hsub) hU4)
    have h2 : M.bondsBetween a b = 2 := LGSpine.isVine_bondsBetween hI
    unfold Molecule.sigma at hσ
    omega
  rcases ordinary_in_dv_vine hM U hσ hA hB hUD (hnV hA) with hUA | hUB
  · exact dv_vine_case C Unsel hUO hU hσ hA hB hAB hUA hh hC
  · have := dv_vine_case C Unsel hUO hU hσ hB hA (by rw [Finset.inter_comm]; exact hAB) hUB
      (by rwa [Finset.union_comm]) (by simpa [Finset.union_comm] using hC)
    exact this

end WaveTurbulence.GammaLow.FinalCount.H
