/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.S2ST.AnchorFamilyB
public import WaveTurbulence.Foundations.FlowerTop.Port.Stage1GateST
/-! R97: `Stage1ReductionAtSTB2`, the both-member successor of the adopted ST gate.

Profiles (`typeProfilesAnchB`), boundedness (`BoundedAnchB`), size (`toLFAnchB`) and the garden-side
representation value (`gardenValueB`) all use the both-member convention. The no-stub, no-anchor case is the
plain `Stage1ReductionAt` (`stage1ReductionAt_of_STB2`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.S2ST
open LGSpine MeasureTheory Set Finset
open scoped Classical

/-- The garden-side value of the both-member anchored family with stubs. -/
noncomputable def gardenValueB {P : WTParams} {R : ℕ} (U : TypeFamily P (2 * R))
    (J : Finset (Fin (2 * R))) (tt : Fin (2 * R) → ℝ) (ts : ℝ)
    (stubs : ∀ LG : LayeredGarden (2 * R), Finset (GBranch LG.garden.tree)) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (members : Finset (LayeredGarden (2 * R)))
    (sel : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop) : ℂ :=
  ∑ LG ∈ members, (toLFAnchB U J).valueSelFix tt (fun LG' => FlowerP1.stubFix (stubs LG') ts) base roots LG
    (sel LG)

/-- `Represents` with stubs and both-member anchors: the garden-side identity and `RepresentsIntST`. -/
def RepresentsSTB2 {P : WTParams} {R : ℕ} (π : Stage1PieceST P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (ts : ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (members : Finset (LayeredGarden (2 * R)))
    (sel : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (U : TypeFamily P (2 * R)) (J : Finset (Fin (2 * R)))
    (stubs : ∀ LG : LayeredGarden (2 * R), Finset (GBranch LG.garden.tree))
    (s : ℝ) (val : ℂ) : Prop :=
  val = gardenValueB U J tt ts stubs base roots members sel ∧ π.RepresentsIntST n tt ts base roots s val

/-- **STB2** (R97): the Stage-1 reduction gate with stubs and both-member anchors. -/
def Stage1ReductionAtSTB2 (C₀ : ℕ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Carries P p N LG) → TwistClosed p A →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (J : Finset (Fin (2 * R))) (stubs : ∀ LG : LayeredGarden (2 * R), Finset (GBranch LG.garden.tree))
    (ts : ℝ),
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → BoundedAnchB U J p →
    (∀ LG ∈ A, (toLFAnchB U J).size LG ≤ s) →
  ∃ (S : Stage1DataST P R) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl)
    (members : Cl → Finset (LayeredGarden (2 * R)))
    (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop),
    Stage1Partition roots A members cls sel ∧
    (∀ π, RepresentsSTB2 (S.piece π) N tt ts base roots (members (cls π)) (sel π) U J stubs s (S.val π)) ∧
    (∀ π, (S.piece π).Sound p base roots) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧
    Stage1Counts C₀ P R N S.toData Cl hCl cls ∧
    (∀ π, (∀ LG ∈ members (cls π), stubs LG = ∅) → (S.piece π).stubs = ∅)

/-- **Bridge** (R97): the no-stub, no-anchor case of STB2 is the plain gate; STB2 implies
`Stage1ReductionAt`. -/
theorem stage1ReductionAt_of_STB2 (C₀ : ℕ) (P : WTParams) (h : Stage1ReductionAtSTB2 C₀ P) :
    Stage1ReductionAt C₀ P := by
  intro p hp R h1 h2 N hN1 hN2 A hA hTC tt htt base roots U s hs hU hsz
  have hsz' : ∀ LG ∈ A, (toLFAnchB U ∅).size LG ≤ s := by
    intro LG hLG
    have := hsz LG hLG
    rwa [toLFAnchB, toLeafFamilyAnchB_empty]
  obtain ⟨S, Cl, hCl, cls, members, sel, hpart, hrep, hsound, hord, hcnt, hstub⟩ :=
    h p hp R h1 h2 N hN1 hN2 A hA hTC tt htt base roots ∅ (fun _ => ∅) 0 U s hs
      ((boundedAnchB_empty_iff U p).mpr hU) hsz'
  refine ⟨S.toData, Cl, hCl, cls, members, sel, hpart, fun π => ?_, fun π => (hsound π).toOld, hord, hcnt⟩
  obtain ⟨hval, hint⟩ := hrep π
  refine ⟨?_, hint.toOld (S.piece π) (hstub π fun _ _ => rfl)⟩
  refine hval.trans ?_
  unfold gardenValueB
  refine Finset.sum_congr rfl fun LG hLG => ?_
  have hLGA : LG ∈ A := (hpart.1 LG).2 ⟨_, hLG⟩
  have hfix : (fun LG' : LayeredGarden (2 * R) => FlowerP1.stubFix (∅ : Finset (GBranch LG'.garden.tree)) (0 : ℝ)) =
      fun _ _ => none := by
    funext LG' b
    exact stubFix_empty _ b
  rw [hfix, toLFAnchB, toLeafFamilyAnchB_empty]
  exact FlowerP1.LeafFamily.valueSelFix_noStubs U.toLF tt base roots LG (hA LG hLGA).1.1 (sel π LG)

end WaveTurbulence.S2ST
