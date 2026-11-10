/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineLG1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3DPInv2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Dart
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3FinalCopy
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3VineLG1`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: `vineLG`, part 1: the collection data, the obligations of TARGET `subpro`, and `C₂`.**

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
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {M₀ : Molecule V D₀}

/-! ### `IsVine` is symmetric in the joints -/

/-! ### The collection data and the named obligations of `subpro` -/

/-- The choices of TARGET `subpro` (2), (5): the collection `C₁`, the hinge atoms, the designated bond pair `(first v, second v)`. -/
structure CollData (M₀ : Molecule V D₀) where
  n : ℕ
  collection : Fin n → Src.Object Src.γL M₀
  hinges : Finset V
  first : V → Option D₀
  second : V → Option D₀

/-- A small-gap object lies outside every object of `C₁`. -/
def CollData.Outside (C : CollData M₀) (P : Src.Object Src.γL M₀) : Prop := ∀ i, ¬ P.atoms ⊆ (C.collection i).atoms

/-- The conclusion of TARGET `subpro` (4) (L2101 area: "must be a subset of a DV or an LG or ZG vine-like object, which is disjoint
with the vine-like objects in `C₁` and does not contain any hinge atom"). -/
def CollData.Host (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (P : Src.Object Src.γL M₀) : Prop :=
  (∃ S a b, Src.IsDV Src.γL M₀ S a b ∧ P.atoms ⊆ S ∧ Disjoint S C.hinges ∧ ∀ i, Disjoint S (C.collection i).atoms) ∨
    ∃ Q : Src.Object Src.γL M₀, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ η w κ .LG ∨ Q.HasGapKind L γ η w κ .ZG) ∧
      Disjoint Q.atoms C.hinges ∧ ∀ i, Disjoint Q.atoms (C.collection i).atoms

/-- **The named obligations: TARGET `subpro` (4), (5), (6)** (TARGET L2042--L2047), over a generic molecule.  Not proved here
(S4 proves them for the molecule of the garden; lg-spine's `Src.SubproSupport` has the same four fields). -/
structure SubproOblG (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : Prop where
  /-- `subpro` (4) -/
  contained : ∀ P : Src.Object Src.γL M₀, P.HasGapKind L γ η w κ .SG → C.Outside P → Disjoint P.atoms C.hinges →
    C.Host L γ η w κ P
  /-- `subpro` (5) -/
  hingeSG : ∀ v ∈ C.hinges, HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAtM M₀ v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG)
  /-- `subpro` (5), second sentence -/
  hingeJoint : ∀ v ∈ C.hinges, ∀ i, (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
    HasChosenPair (C.first v) (C.second v) (fun x y => (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)
  /-- `subpro` (6) -/
  crossing : ∀ P : Src.Object Src.γL M₀, P.HasGapKind L γ η w κ .SG → C.Outside P → ¬ Disjoint P.atoms C.hinges →
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧ ((v ≠ P.upper ∧ v ≠ P.lower) ∨
      ((v = P.upper ∨ v = P.lower) ∧
        HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))

/-! ### `C₂` as a definition (TARGET L2101) -/

/-- The SG vine-like objects of `subpro` (4): outside `C₁`, disjoint from the hinges, contained in a DV or an LG/ZG host. -/
def CollData.InP (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (P : Src.Object Src.γL M₀) : Prop :=
  P.HasGapKind L γ η w κ .SG ∧ C.Outside P ∧ Disjoint P.atoms C.hinges ∧ C.Host L γ η w κ P

/-- `C₂`: the maximal elements of the pool minus the unselected vines. -/
def CollData.C2Of (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (Unsel : Set (Src.Object Src.γL M₀)) :
    Set (Src.Object Src.γL M₀) :=
  {U | (C.InP L γ η w κ U ∧ U ∉ Unsel) ∧ ∀ Q, (C.InP L γ η w κ Q ∧ Q ∉ Unsel) → U.atoms ⊆ Q.atoms → Q.atoms ⊆ U.atoms}

/-! ### One designation per atom set (R50 F-DESIG) -/

/-- Rank of the deleted bond of a hyper object (`0` for an ordinary one); as lg-spine's `Src.Object.hyperRank`. -/
noncomputable def _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.hyperRankG (P : Src.Object Src.γL M₀) : ℕ :=
  match P.shape with
  | .vc _ => 0
  | .hyper R => min (dartRankG D₀ R.added) (dartRankG D₀ (M₀.mate R.added))

/-- `C₂` with ONE designation per atom set: among the members of `C2Of` with one hyper atom set, only those whose deleted bond has
least rank (lg-spine's `Src.canonicalSub`, R50 F-DESIG). -/
def CollData.C2Can (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (Unsel : Set (Src.Object Src.γL M₀)) :
    Set (Src.Object Src.γL M₀) :=
  {U | U ∈ C.C2Of L γ η w κ Unsel ∧ ∀ Q ∈ C.C2Of L γ η w κ Unsel, Q.atoms = U.atoms → (∃ R, U.shape = .hyper R) →
    (∃ R, Q.shape = .hyper R) → U.hyperRankG ≤ Q.hyperRankG}

theorem CollData.C2Can_subset {C : CollData M₀} {Unsel : Set (Src.Object Src.γL M₀)} : C.C2Can L γ η w κ Unsel ⊆ C.C2Of L γ η w κ Unsel :=
  fun _ h => h.1

theorem CollData.mem_C2Can_of_vc {C : CollData M₀} {Unsel : Set (Src.Object Src.γL M₀)} {U : Src.Object Src.γL M₀}
    (hU : U ∈ C.C2Of L γ η w κ Unsel) (hvc : ∃ h, U.shape = Src.VineLikeObject.vc h) : U ∈ C.C2Can L γ η w κ Unsel := by
  refine ⟨hU, fun Q _ _ hh _ => ?_⟩
  obtain ⟨h, hh'⟩ := hvc
  obtain ⟨R, hR⟩ := hh
  rw [hh'] at hR
  exact absurd hR (by simp)

/-- The selection rule for DV′'s whose two vines are both SG (L2101), applied among the maximal objects: an unselected vine `B`
of a DV′ `A ∪ B` is covered by a member of `C₂` (then `B` is not maximal and the DV rule does not apply to it), or has its partner
`A` selected, as a VC member of `C₂`.  (FINALCOUNT-ASM session 19: the first disjunct is added; it replaces the named input
`DVNotInsideObject` of R50.)

**Low-range change (L6-HDS).** Main's DV is two vines (V); here the pair `A, B` is a DV′ of the low family (D11
`Molecule.IsDVPrime`, the fields of `Src.DoubleVine`): `σ(a, b) = 1` and two members of `𝒱_{γL}` sharing exactly their
joints. -/
structure CollData.UnselOK (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (Unsel : Set (Src.Object Src.γL M₀)) :
    Prop where
  dv : ∀ B ∈ Unsel, C.InP L γ η w κ B ∧ ((∃ U ∈ C.C2Can L γ η w κ Unsel, B.atoms ⊆ U.atoms) ∨
    ∃ A a b, M₀.sigma a b = 1 ∧ Src.IsSomeVine Src.γL M₀ A a b ∧ Src.IsSomeVine Src.γL M₀ B.atoms a b ∧
    A ∩ B.atoms = {a, b} ∧
    ∃ U ∈ C.C2Can L γ η w κ Unsel, U.atoms = A ∧ ∃ h, U.shape = Src.VineLikeObject.vc h)

theorem objectAtoms_sub' (P : Src.Object Src.γL M₀) : P.atoms ⊆ M₀.atoms := Step1.objectAtoms_sub P

/-- **Cover.** Every pool object is unselected or its atoms lie in a member of `C₂`. -/
theorem CollData.cover (C : CollData M₀) (Unsel : Set (Src.Object Src.γL M₀)) {P : Src.Object Src.γL M₀}
    (hP : C.InP L γ η w κ P) : P ∈ Unsel ∨ ∃ U ∈ C.C2Of L γ η w κ Unsel, P.atoms ⊆ U.atoms := by
  by_cases hU : P ∈ Unsel
  · exact Or.inl hU
  right
  let T : Set (Src.Object Src.γL M₀) := {Q | (C.InP L γ η w κ Q ∧ Q ∉ Unsel) ∧ P.atoms ⊆ Q.atoms}
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
    have := Finset.card_le_card (Step1.objectAtoms_sub Q)
    omega
  refine ⟨U, ⟨hUT.1, fun Q hQ hUQ => ?_⟩, hUT.2⟩
  have hQT : Q ∈ T := ⟨hQ, hUT.2.trans hUQ⟩
  have heq : U.atoms = Q.atoms := Finset.eq_of_subset_of_card_le hUQ (hmax Q hQT)
  exact heq.symm.subset

/-- **Cover, canonical form.** Every pool object is unselected or its atoms lie in a member of the canonical `C₂`. -/
theorem CollData.coverCan (C : CollData M₀) (Unsel : Set (Src.Object Src.γL M₀)) {P : Src.Object Src.γL M₀}
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

end WaveTurbulence.GammaLow.FinalCount.H
