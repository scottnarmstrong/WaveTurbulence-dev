/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1Gate
public import WaveTurbulence.Foundations.FlowerTop.Port.Stage1InterfaceST
/-! AMEND-ST (R61 X4): the Stage 1 reduction gate with STUBS and ANCHORS, `Stage1ReductionAtST`, as a
generalization of `Stage1ReductionAt` with the proved bridge `stage1ReductionAt_of_ST` (no anchors, no stubs).

New data of the gate: the anchor trees `J` (trivial trees of the garden; anchored pairs have profile `1`, are
exempt from `BoundedAnch` and from the leaf size), the stub branches `stubs LG` of every garden at the stub time
`ts`, and, in the conclusion, the stub set of each piece (`Stage1PieceDST.stubs`) with `stub_pendant` in `Sound`.
The last conjunct says that a piece of a class of stub-free gardens has no stubs. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped Classical

/-- All pieces of one instance of the sum, with stubs. -/
structure Stage1DataST (P : WTParams) (R : ℕ) where
  Pc : Type
  fin : Fintype Pc
  piece : Pc → Stage1PieceST P R
  val : Pc → ℂ

/-- The data without the stub sets. -/
def Stage1DataST.toData {P : WTParams} {R : ℕ} (S : Stage1DataST P R) : Stage1Data P R :=
  ⟨S.Pc, S.fin, fun π => (S.piece π).toStage1PieceD, S.val⟩

/-- The Stage 1 reduction gate with anchors `J` and stubs (AMEND-ST, R61 X4). -/
def Stage1ReductionAtST (C₀ : ℕ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Carries P p N LG) → TwistClosed p A →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (J : Finset (Fin (2 * R))) (stubs : ∀ LG : LayeredGarden (2 * R), Finset (GBranch LG.garden.tree))
    (ts : ℝ),
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.BoundedAnch J p →
    (∀ LG ∈ A, (U.toLFAnch J).size LG ≤ s) →
  ∃ (S : Stage1DataST P R) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl)
    (members : Cl → Finset (LayeredGarden (2 * R)))
    (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop),
    Stage1Partition roots A members cls sel ∧
    (∀ π, (S.piece π).RepresentsST N tt ts base roots (members (cls π)) (sel π) U J stubs s (S.val π)) ∧
    (∀ π, (S.piece π).Sound p base roots) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧
    Stage1Counts C₀ P R N S.toData Cl hCl cls ∧
    (∀ π, (∀ LG ∈ members (cls π), stubs LG = ∅) → (S.piece π).stubs = ∅)

/-- **Bridge** (AMEND-ST): the gate with stubs and anchors implies the current gate (no anchors, no stubs). -/
theorem stage1ReductionAt_of_ST (C₀ : ℕ) (P : WTParams) (h : Stage1ReductionAtST C₀ P) :
    Stage1ReductionAt C₀ P := by
  intro p hp R h1 h2 N hN1 hN2 A hA hTC tt htt base roots U s hs hU hsz
  have hsz' : ∀ LG ∈ A, (U.toLFAnch ∅).size LG ≤ s := by
    intro LG hLG
    have := hsz LG hLG
    rwa [TypeFamily.toLFAnch, toLeafFamilyAnch_empty]
  obtain ⟨S, Cl, hCl, cls, members, sel, hpart, hrep, hsound, hord, hcnt, hstub⟩ :=
    h p hp R h1 h2 N hN1 hN2 A hA hTC tt htt base roots ∅ (fun _ => ∅) 0 U s hs
      ((boundedAnch_empty_iff U p).mpr hU) hsz'
  refine ⟨S.toData, Cl, hCl, cls, members, sel, hpart, fun π => ?_, fun π => (hsound π).toOld, hord, hcnt⟩
  obtain ⟨hval, hint⟩ := hrep π
  refine ⟨?_, hint.toOld (S.piece π) (hstub π fun _ _ => rfl)⟩
  refine hval.trans ?_
  unfold Stage1PieceDST.gardenValue
  refine Finset.sum_congr rfl fun LG hLG => ?_
  have hLGA : LG ∈ A := (hpart.1 LG).2 ⟨_, hLG⟩
  have hfix : (fun LG' : LayeredGarden (2 * R) => FlowerP1.stubFix (∅ : Finset (GBranch LG'.garden.tree)) (0 : ℝ)) =
      fun _ _ => none := by
    funext LG' b
    exact stubFix_empty _ b
  rw [hfix, TypeFamily.toLFAnch, toLeafFamilyAnch_empty]
  exact FlowerP1.LeafFamily.valueSelFix_noStubs U.toLF tt base roots LG (hA LG hLGA).1.1 (sel π LG)

end WaveTurbulence.LGSpine
