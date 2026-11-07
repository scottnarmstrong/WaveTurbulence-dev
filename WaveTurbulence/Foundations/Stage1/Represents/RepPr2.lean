/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepPr1
public import WaveTurbulence.Foundations.Stage1.Represents.RepCountB
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the producer, part 2 (carrier and `Stage1Partition`)

For a finite set `A` of plain layered gardens: the prescribed points `PtA` over `A`, the pieces `PcA` = fine tau classes
of prescribed points (`Related`, the equivalence of VINE-A's `Related`), the coarse classes `ClA`
(`PrimeData.coarseState.allCoreOutputs`), `members c = A ∩ c`, and the selection
`selP π LG κ := ∃ b over LG, b ~ rep π ∧ selAt b κ` (TARGET L1950: `σ`-restriction and tau class).

B1a (ruling F-1): the fine classes (`ptSetoid`, `PcA`, `repPt`, `selP`) take the trailing fine marking `mk` and the
coarse classes (`coarseOf`, `ClA`, `membersP`) the coarse marking (both default `fun _ => ∅`); `clsP` maps fine to
coarse classes.  At the default they are main's (`coarseOf_empty`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineA WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.VineA.PrescribedPrimeGarden

variable {R : ℕ}

theorem finite_groupPrescription {w : ℕ} (G : Garden w) : Finite (GroupPrescription G) := by
  classical
  have hfin : (Stage1.maximalGroups G.molecule).Finite := Set.toFinite _
  have : Finite (Stage1.maximalGroups G.molecule) := hfin
  have : Finite Molecule.GapKind := inferInstance
  unfold GroupPrescription
  infer_instance

/-- Prescribed points over `A`. -/
abbrev PtA (R : ℕ) (A : Finset (LayeredGarden (2 * R))) := {b : PrescribedPrimeGarden (2 * R) // b.layered ∈ A}

theorem finite_ptA (A : Finset (LayeredGarden (2 * R))) : Finite (PtA R A) := by
  classical
  let T : LayeredGarden (2 * R) → Set (PrescribedPrimeGarden (2 * R)) := fun LG =>
    ⋃ hp : LG.garden.IsPlain, Set.range (fun σ : GroupPrescription (primeDataOf LG hp).skeleton =>
      (⟨LG, primeDataOf LG hp, σ⟩ : PrescribedPrimeGarden (2 * R)))
  have hf : Set.Finite {b : PrescribedPrimeGarden (2 * R) | b.layered ∈ A} := by
    refine Set.Finite.subset (Set.Finite.biUnion (t := T) A.finite_toSet fun LG _ =>
      Set.finite_iUnion fun hp : LG.garden.IsPlain => ?_) ?_
    · have := finite_groupPrescription (primeDataOf LG hp).skeleton
      exact Set.finite_range _
    · rintro ⟨LG, pr, σ⟩ hb
      have hp : LG.garden.IsPlain := pr.decodes.1
      have e : pr = primeDataOf LG hp := primeData_unique _ _
      subst e
      exact Set.mem_biUnion (x := LG) hb (Set.mem_iUnion.2 ⟨hp, ⟨σ, rfl⟩⟩)
  exact hf.to_subtype

def ptSetoid (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R)))
    (mk : Stage1Mk.MarkFn (2 * R) := fun _ => ∅) : Setoid (PtA R A) where
  r a b := Related (p := p) (kind := kind) a.1 b.1 mk
  iseqv := ⟨fun a => (Relation.EqvGen.is_equivalence _).refl a.1,
    fun h => (Relation.EqvGen.is_equivalence _).symm h,
    fun h h' => (Relation.EqvGen.is_equivalence _).trans h h'⟩

/-- The pieces: fine tau classes of prescribed points over `A`. -/
abbrev PcA (R : ℕ) (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R)))
    (mk : Stage1Mk.MarkFn (2 * R) := fun _ => ∅) :=
  Quotient (ptSetoid (R := R) p kind A mk)

noncomputable instance (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R))) (mk : Stage1Mk.MarkFn (2 * R)) :
    Fintype (PcA R p kind A mk) :=
  have := finite_ptA A
  have : Finite (PcA R p kind A) := Quotient.finite _
  Fintype.ofFinite _

/-- A representative prescribed point of a piece. -/
noncomputable def repPt {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))} {mk : Stage1Mk.MarkFn (2 * R)}
    (π : PcA R p kind A mk) : PrescribedPrimeGarden (2 * R) := (Quotient.out π).1

theorem repPt_layered_mem {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))} (π : PcA R p kind A) :
    (repPt π).layered ∈ A := (Quotient.out π).2

/-- B1a: `repPt_layered_mem` for every fine marking. -/
theorem repPt_layered_memMk {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))}
    {mk : Stage1Mk.MarkFn (2 * R)} (π : PcA R p kind A mk) : (repPt π).layered ∈ A := (Quotient.out π).2

/-- The coarse class of a prescribed point.  B1a: with the coarse marking `mk` (default `fun _ => ∅`), the coarse′
class of twists at the unmarked vines of `𝒱` (`coarseStateMk`). -/
def coarseOf (p : ℕ) (kind : Bool) (b : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R) := fun _ => ∅) :
    Set (LayeredGarden (2 * R)) :=
  (coarseStateMk b.prime (mk b.prime)).allCoreOutputs (p := p) (kind := kind)

/-- B1a bridge: at the default marking the coarse class is main's. -/
theorem coarseOf_empty (p : ℕ) (kind : Bool) (b : PrescribedPrimeGarden (2 * R)) :
    coarseOf p kind b = b.prime.coarseState.allCoreOutputs (p := p) (kind := kind) :=
  coarseStateMk_empty_outputs b.prime

/-- The coarse classes of `A`. -/
abbrev ClA (R : ℕ) (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R)))
    (mk : Stage1Mk.MarkFn (2 * R) := fun _ => ∅) :=
  ↥(Set.range fun b : PtA R A => coarseOf p kind b.1 mk)

noncomputable instance (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R))) (mk : Stage1Mk.MarkFn (2 * R)) :
    Fintype (ClA R p kind A mk) :=
  have := finite_ptA A
  have : Finite (ClA R p kind A) := (Set.finite_range _).to_subtype
  Fintype.ofFinite _

/-- B1a: the coarse′ class (coarse marking `mkC`) of a fine′ piece (fine marking `mkF`). -/
noncomputable def clsPMk {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))} {mkF : Stage1Mk.MarkFn (2 * R)}
    (mkC : Stage1Mk.MarkFn (2 * R)) (π : PcA R p kind A mkF) : ClA R p kind A mkC :=
  ⟨coarseOf p kind (repPt π) mkC, ⟨Quotient.out π, rfl⟩⟩

/-- The coarse class of a piece (main's classes; B1a: `clsPMk` at the empty fine and coarse markings). -/
noncomputable abbrev clsP {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))}
    (π : PcA R p kind A) : ClA R p kind A := clsPMk (fun _ => ∅) π

open scoped Classical in
noncomputable def membersP {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))} {mk : Stage1Mk.MarkFn (2 * R)}
    (c : ClA R p kind A mk) : Finset (LayeredGarden (2 * R)) := A.filter (· ∈ c.1)

/-- The selection of a piece: the garden `LG` carries a prescribed point of the tau class whose `σ` holds at `κ`.
B1a: for the fine marking `mk`. -/
def selPMk (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R))) (P : WTParams) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (mk : Stage1Mk.MarkFn (2 * R)) (π : PcA R p kind A mk)
    (LG : LayeredGarden (2 * R)) (κ : GenDecoration LG.garden P.d roots 0) : Prop :=
  ∃ (b : PrescribedPrimeGarden (2 * R)) (h : b.layered = LG), Related (p := p) (kind := kind) (repPt π) b mk ∧
    selAt P base b.prime b.sigma (h ▸ κ)

/-- The selection of a piece (main's: `selPMk` at the empty fine marking). -/
abbrev selP (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R))) (P : WTParams) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) : (π : PcA R p kind A) → (LG : LayeredGarden (2 * R)) →
      GenDecoration LG.garden P.d roots 0 → Prop :=
  selPMk p kind A P base roots fun _ => ∅

theorem coarse_eq_of_related {p : ℕ} {kind : Bool} {a b : PrescribedPrimeGarden (2 * R)}
    (h : Related (p := p) (kind := kind) a b) : coarseOf p kind a = coarseOf p kind b := by
  have hb : b.layered ∈ a.outputs (p := p) (kind := kind) := by
    rw [← tauClass_image a]; exact ⟨b, h, rfl⟩
  have hb2 : b.layered ∈ a.prime.coarseState.allCoreOutputs (p := p) (kind := kind) :=
    a.prime.fine_outputs_subset_coarse a.totalSigma hb
  rw [coarseOf_empty, coarseOf_empty]
  exact a.prime.coarse_outputs_rebase b.prime hb2

end WaveTurbulence.Represents
