/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineBridge
public import WaveTurbulence.Foundations.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.FinalCount.G3DPRun
public import WaveTurbulence.Foundations.FinalCount.G3Range
/-! **FINALCOUNT-G3: `vineLG`, part 1: the collection data, the obligations of TARGET `subpro`, and `C₂`.**

* `CollData`: the collection `C₁`, the hinge atoms and the designated pairs `(first v, second v)` of TARGET `subpro` (2), (5)
  (a generic-molecule copy of lg-spine's `SubproChoices`).
* `SubproOblG`: the four statements of TARGET `subpro` (4), (5), (6) (TARGET L2042--L2047, L2101 = `contained`, `hingeSG`,
  `hingeJoint`, `crossing`), literally as lg-spine's `SubproSupport`; the named obligations (S4 proves them).
* `C2Of`: the collection `C₂` of TARGET L2101 as a *definition*: the maximal SG vine-like objects of `subpro` (4) (hosts disjoint from
  `C₁` and the hinges), where in a DV whose two vines are both SG exactly one (a VC that is itself selected, `UnselOK`) is selected.
  READING (candidate exposition gap, HANDOFF): L2101 does not say what is selected when the chosen vine is not maximal; we apply the DV rule
  among the maximal objects: the partner of an unselected vine is a member of `C₂`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {M₀ : Molecule V D₀}

/-! ### `IsVine` is symmetric in the joints -/

theorem _root_.WaveTurbulence.Molecule.IsBlock.symm' {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D}
    {S : Finset V} {j₁ j₂ : V} (h : M.IsBlock S j₁ j₂) : M.IsBlock S j₂ j₁ := by
  obtain ⟨h0, h1, h2, h3, o1, i1, o2, i2, h4, h5⟩ := h
  exact ⟨h0, h2, h1, h3.symm, o2, i2, o1, i1, fun v hv a b => h4 v hv b a, h5⟩

theorem isVine_symm {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} {X : VineType} {S : Finset V}
    {j₁ j₂ : V} (h : M.IsVine X S j₁ j₂) : M.IsVine X S j₂ j₁ := by
  obtain ⟨hb, k, hk, f, hf, himg, hj, hbd⟩ := h
  exact ⟨hb.symm', k, hk, f, hf, himg, by rw [Finset.pair_comm]; exact hj, hbd⟩

theorem FinalJoints.symm {hf : HSt V D₀} {a₀ j₁ j₂ : V} (J : FinalJoints hf a₀ j₁ j₂) : FinalJoints hf a₀ j₂ j₁ where
  m1 := J.m2
  m2 := J.m1
  ne := J.ne.symm
  c1 := J.c2
  c2 := J.c1
  d1 := J.d2
  d2 := J.d1
  n1 := J.n2
  n2 := J.n1
  comp := fun b hb hbc => by
    rcases J.comp b hb hbc with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-! ### The collection data and the named obligations of `subpro` -/

/-- The choices of TARGET `subpro` (2), (5): the collection `C₁`, the hinge atoms, the designated bond pair `(first v, second v)`. -/
structure CollData (M₀ : Molecule V D₀) where
  n : ℕ
  collection : Fin n → Object M₀
  hinges : Finset V
  first : V → Option D₀
  second : V → Option D₀

/-- Two distinct bonds of opposite directions at the atom `v`. -/
def TripleAtM (M : Molecule V D₀) (v : V) (x y : D₀) : Prop :=
  M.atom x = v ∧ M.atom y = v ∧ y ≠ M.mate x ∧ M.out x ≠ M.out y

/-- A small-gap object lies outside every object of `C₁`. -/
def CollData.Outside (C : CollData M₀) (P : Object M₀) : Prop := ∀ i, ¬ P.atoms ⊆ (C.collection i).atoms

/-- The conclusion of TARGET `subpro` (4) (L2101 area: "must be a subset of a DV or an LG or ZG vine-like object, which is disjoint
with the vine-like objects in `C₁` and does not contain any hinge atom"). -/
def CollData.Host (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (P : Object M₀) : Prop :=
  (∃ S a b, IsDV M₀ S a b ∧ P.atoms ⊆ S ∧ Disjoint S C.hinges ∧ ∀ i, Disjoint S (C.collection i).atoms) ∨
    ∃ Q : Object M₀, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ η w κ .LG ∨ Q.HasGapKind L γ η w κ .ZG) ∧
      Disjoint Q.atoms C.hinges ∧ ∀ i, Disjoint Q.atoms (C.collection i).atoms

/-- **The named obligations: TARGET `subpro` (4), (5), (6)** (TARGET L2042--L2047), over a generic molecule.  Not proved here
(S4 proves them for the molecule of the garden; lg-spine's `SubproSupport` has the same four fields). -/
structure SubproOblG (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : Prop where
  /-- `subpro` (4) -/
  contained : ∀ P : Object M₀, P.HasGapKind L γ η w κ .SG → C.Outside P → Disjoint P.atoms C.hinges →
    C.Host L γ η w κ P
  /-- `subpro` (5) -/
  hingeSG : ∀ v ∈ C.hinges, HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAtM M₀ v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG)
  /-- `subpro` (5), second sentence -/
  hingeJoint : ∀ v ∈ C.hinges, ∀ i, (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
    HasChosenPair (C.first v) (C.second v) (fun x y => (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)
  /-- `subpro` (6) -/
  crossing : ∀ P : Object M₀, P.HasGapKind L γ η w κ .SG → C.Outside P → ¬ Disjoint P.atoms C.hinges →
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧ ((v ≠ P.upper ∧ v ≠ P.lower) ∨
      ((v = P.upper ∨ v = P.lower) ∧
        HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))

/-! ### `C₂` as a definition (TARGET L2101) -/

/-- The SG vine-like objects of `subpro` (4): outside `C₁`, disjoint from the hinges, contained in a DV or an LG/ZG host. -/
def CollData.InP (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (P : Object M₀) : Prop :=
  P.HasGapKind L γ η w κ .SG ∧ C.Outside P ∧ Disjoint P.atoms C.hinges ∧ C.Host L γ η w κ P

/-- `C₂`: the maximal elements of the pool minus the unselected vines. -/
def CollData.C2Of (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (Unsel : Set (Object M₀)) :
    Set (Object M₀) :=
  {U | (C.InP L γ η w κ U ∧ U ∉ Unsel) ∧ ∀ Q, (C.InP L γ η w κ Q ∧ Q ∉ Unsel) → U.atoms ⊆ Q.atoms → Q.atoms ⊆ U.atoms}

/-! ### One designation per atom set (R50 F-DESIG) -/

/-- A fixed injective rank on the darts. -/
noncomputable def dartRankG (D : Type*) [Fintype D] : D → ℕ := fun x => (Fintype.equivFin D x : ℕ)

theorem dartRankG_injective (D : Type*) [Fintype D] : Function.Injective (dartRankG D) := fun x y h =>
  (Fintype.equivFin D).injective (Fin.ext h)

/-- Rank of the deleted bond of a hyper object (`0` for an ordinary one); as lg-spine's `Object.hyperRank`. -/
noncomputable def _root_.WaveTurbulence.LGSpine.SourceVine.Object.hyperRankG (P : Object M₀) : ℕ :=
  match P.shape with
  | .vc _ => 0
  | .hyper R => min (dartRankG D₀ R.added) (dartRankG D₀ (M₀.mate R.added))

/-- `C₂` with ONE designation per atom set: among the members of `C2Of` with one hyper atom set, only those whose deleted bond has
least rank (lg-spine's `canonicalSub`, R50 F-DESIG). -/
def CollData.C2Can (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (Unsel : Set (Object M₀)) :
    Set (Object M₀) :=
  {U | U ∈ C.C2Of L γ η w κ Unsel ∧ ∀ Q ∈ C.C2Of L γ η w κ Unsel, Q.atoms = U.atoms → (∃ R, U.shape = .hyper R) →
    (∃ R, Q.shape = .hyper R) → U.hyperRankG ≤ Q.hyperRankG}

theorem CollData.C2Can_subset {C : CollData M₀} {Unsel : Set (Object M₀)} : C.C2Can L γ η w κ Unsel ⊆ C.C2Of L γ η w κ Unsel :=
  fun _ h => h.1

theorem CollData.mem_C2Can_of_vc {C : CollData M₀} {Unsel : Set (Object M₀)} {U : Object M₀}
    (hU : U ∈ C.C2Of L γ η w κ Unsel) (hvc : ∃ h, U.shape = VineLikeObject.vc h) : U ∈ C.C2Can L γ η w κ Unsel := by
  refine ⟨hU, fun Q _ _ hh _ => ?_⟩
  obtain ⟨h, hh'⟩ := hvc
  obtain ⟨R, hR⟩ := hh
  rw [hh'] at hR
  exact absurd hR (by simp)

/-- The selection rule for DV's whose two vines are both SG (L2101), applied among the maximal objects: an unselected vine `B` of a
DV `A ∪ B` is covered by a member of `C₂` (then `B` is not maximal and the DV rule does not apply to it), or has its partner `A`
selected, as a VC member of `C₂`.  (FINALCOUNT-ASM session 19: the first disjunct is added; it replaces the named input
`DVNotInsideObject` of R50.) -/
structure CollData.UnselOK (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (Unsel : Set (Object M₀)) :
    Prop where
  dv : ∀ B ∈ Unsel, C.InP L γ η w κ B ∧ ((∃ U ∈ C.C2Can L γ η w κ Unsel, B.atoms ⊆ U.atoms) ∨
    ∃ A a b, M₀.IsVine .V A a b ∧ M₀.IsVine .V B.atoms a b ∧ A ∩ B.atoms = {a, b} ∧
    ∃ U ∈ C.C2Can L γ η w κ Unsel, U.atoms = A ∧ ∃ h, U.shape = VineLikeObject.vc h)

theorem objectAtoms_sub' (P : Object M₀) : P.atoms ⊆ M₀.atoms := objectAtoms_sub P

theorem IsContained.symm_of_atoms_eq {P Q : Object M₀} (h : P.IsContained Q) (he : P.atoms = Q.atoms) : Q.IsContained P := by
  unfold Object.IsContained at *
  rcases hP : P.shape with hp | hp <;> rcases hQ : Q.shape with hq | hq <;>
    simp only [hP, hQ, VineLikeObject.IsContained] at h ⊢
  · exact he.symm.subset
  · exact he.symm.subset
  · exact he.symm.subset
  · refine ⟨he.symm.subset, fun _ => ?_⟩
    rcases h.2 he with e | e
    · exact Or.inl e.symm
    · right; rw [e, M₀.mate_mate]

/-- **Cover.** Every pool object is unselected or its atoms lie in a member of `C₂`. -/
theorem CollData.cover (C : CollData M₀) (Unsel : Set (Object M₀)) {P : Object M₀}
    (hP : C.InP L γ η w κ P) : P ∈ Unsel ∨ ∃ U ∈ C.C2Of L γ η w κ Unsel, P.atoms ⊆ U.atoms := by
  by_cases hU : P ∈ Unsel
  · exact Or.inl hU
  right
  let T : Set (Object M₀) := {Q | (C.InP L γ η w κ Q ∧ Q ∉ Unsel) ∧ P.atoms ⊆ Q.atoms}
  have hTne : P ∈ T := ⟨⟨hP, hU⟩, Finset.Subset.refl _⟩
  classical
  obtain ⟨U, hUT, hmax⟩ : ∃ U ∈ T, ∀ Q ∈ T, Q.atoms.card ≤ U.atoms.card := by
    by_contra hcon
    push Not at hcon
    -- build a strictly increasing chain bounded by `M₀.atoms.card`
    have key : ∀ n : ℕ, ∃ Q ∈ T, n ≤ Q.atoms.card := by
      intro n
      induction n with
      | zero => exact ⟨P, hTne, Nat.zero_le _⟩
      | succ n ih =>
        obtain ⟨Q, hQ, hn⟩ := ih
        obtain ⟨Q', hQ', hlt⟩ := hcon Q hQ
        exact ⟨Q', hQ', by omega⟩
    obtain ⟨Q, hQ, hn⟩ := key (M₀.atoms.card + 1)
    have := Finset.card_le_card (objectAtoms_sub Q)
    omega
  refine ⟨U, ⟨hUT.1, fun Q hQ hUQ => ?_⟩, hUT.2⟩
  have hQT : Q ∈ T := ⟨hQ, hUT.2.trans hUQ⟩
  have heq : U.atoms = Q.atoms := Finset.eq_of_subset_of_card_le hUQ (hmax Q hQT)
  exact heq.symm.subset

/-- **Cover, canonical form.** Every pool object is unselected or its atoms lie in a member of the canonical `C₂`. -/
theorem CollData.coverCan (C : CollData M₀) (Unsel : Set (Object M₀)) {P : Object M₀}
    (hP : C.InP L γ η w κ P) : P ∈ Unsel ∨ ∃ U ∈ C.C2Can L γ η w κ Unsel, P.atoms ⊆ U.atoms := by
  rcases C.cover Unsel hP with h | ⟨U, hU, hsub⟩
  · exact Or.inl h
  right
  by_cases hh : ∃ R, U.shape = .hyper R
  · let S : Set ℕ := {n | ∃ Q ∈ C.C2Of L γ η w κ Unsel, Q.atoms = U.atoms ∧ (∃ R, Q.shape = .hyper R) ∧ Q.hyperRankG = n}
    have hne : ∃ n, n ∈ S := ⟨_, U, hU, rfl, hh, rfl⟩
    obtain ⟨Q, hQ, hQat, hQh, hQn⟩ := Nat.find_spec hne
    refine ⟨Q, ⟨hQ, fun Q' hQ' hat _ hQ'h => ?_⟩, hQat ▸ hsub⟩
    have := Nat.find_min' hne (show Q'.hyperRankG ∈ S from ⟨Q', hQ', hat.trans hQat, hQ'h, rfl⟩)
    rw [hQn]; exact this
  · exact ⟨U, ⟨hU, fun _ _ _ h => absurd h hh⟩, hsub⟩

end WaveTurbulence.FinalCountG3
