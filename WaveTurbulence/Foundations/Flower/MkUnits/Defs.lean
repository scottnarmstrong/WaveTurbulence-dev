/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1W.Bridge
public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Crude
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD12
public import WaveTurbulence.Foundations.Stage1.Shared.CarriesW

/-! # MK-UNITS (B3): the statements of the marked producer for the unmarked units

Stage 1′ (o75 §2.5 with U-clock, enlarged marking, B0 §2) splices the **runs** of the marked groups and the units of
the unmarked groups: `unitBlocks G σ Mk` (main, B1a/B2a).  Each run is a unit of main's on-chain U-clock chain, and the
world's weighted pieces (O3′ = `Stage1WVine`, O4′ = `Stage1WNoVine`) are reused over runs.  With the enlarged marking no
lower slot of a unit contains a protected vertex, so no protected-slot input enters here (B3s adds the protected
non-lower slots and the `G_sb` pins).

* `MarkingOK mkF mkC`: the marking data consumed (fine marking `mkF`, coarse marking `mkC ⊆ mkF`, fine transport,
  member markings).  B4 supplies them from B2b (`markInvariantBatchV_markI`, `markInvariantBatchV_markI0`).
* `VineCaseRepresentsFWMk`, `NoVineRepresentsFWMk`: O3′/O4′ for the fine′ pieces `PcA R p kind A mkF` of the marked
  producer, with the coarse′ classes `clsPMk mkC`, the twist closure `TwistClosedAdm` and the truncation-free
  carrier `Stage1CarriesW` (R156).
* `pieceMK`: a producer piece as a world `Stage1PieceMK` with no pins, no filters and indicator `1`;
  `MarkedUnitsRepresentsFW`: both cases in `RepresentsIntMK` form (the B3 export consumed by B3s/B4).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.MkUnits
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
  WaveTurbulence.Represents WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
  WaveTurbulence.RedSplice WaveTurbulence.VineC WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.MkDefs

/-! ## The marking data -/

/-- **The marking data of the marked producer** (consumed by B3; supplied by B4).
* `sub`: the coarse marking is contained in the fine one (`Π₀ ⊆ Π`);
* `fine`: every fine′ batch carries the fine marking (B1b-2's `FineTransportedAt`; Lemma 2⁺(a) at the points where it
  is used).
No member marking is needed: a run-class member's shape uses the image marking along one trace (`Member0.memShape`). -/
structure MarkingOK {w : ℕ} (mkF mkC : Stage1Mk.MarkFn w) : Prop where
  sub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), mkC B ⊆ mkF B
  fine : ∀ c : PrescribedPrimeGarden w, c.FineTransportedAt mkF

/-- The empty markings satisfy `MarkingOK` (main's unmarked Stage 1). -/
theorem markingOK_empty {w : ℕ} : MarkingOK (w := w) (fun _ => ∅) (fun _ => ∅) where
  sub _ := subset_rfl
  fine c := c.fineTransportedAt_empty

/-! ## The R173 instance at a piece (ruling R177, F-B4-3) -/

/-- **The marking of the piece of a prescribed point** (R177, F-B4-3): the fine marking restricted to `𝒱₀(σ)`, so
that every marked vine of the piece lies in an SG group (R173).  A `MarkFn` cannot see `σ`; the restriction is made
at the piece. -/
def mkAt {w : ℕ} (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) : Set (Stage1.CLVine a.prime.skeleton) :=
  mkF a.prime ∩ vinesV0 a.prime.skeleton a.totalSigma

/-- The start state of the run assembly of `a` at the marked set `Mk` (`sourceStart a mk` is `startAt a (mk a.prime)`
definitionally). -/
noncomputable abbrev startAt {w : ℕ} (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton)) :=
  unitsStart (alignedAssemblyMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk)
    (VineB.unitBlkMk_disj (Mole.garden_isMolecule _) a.totalSigma Mk) a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a)

/-- A marking function taking the value `Mk` at `a.prime` (used internally to run main's `MarkFn`-level run
assembly at a marked set of the representative). -/
def fixMark {w : ℕ} (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton)) : Stage1Mk.MarkFn w :=
  fun _ => {c | ∃ c₀ ∈ Mk, HEq c₀ c}

theorem fixMark_self {w : ℕ} (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton)) :
    fixMark a Mk a.prime = Mk := by
  ext c
  constructor
  · rintro ⟨c₀, h₀, he⟩
    rw [← eq_of_heq he]
    exact h₀
  · intro hc
    exact ⟨c, hc, HEq.rfl⟩

/-- Restricting the fine marking to `𝒱₀(σ)` does not change the unmarked `𝒱₀`. -/
theorem vinesV0_mkAt {w : ℕ} (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    vinesV0 a.prime.skeleton a.totalSigma (mkAt mkF a) = vinesV0 a.prime.skeleton a.totalSigma (mkF a.prime) := by
  ext c
  rw [mem_vinesV0 (Mk := mkAt mkF a), mem_vinesV0 (Mk := mkF a.prime)]
  constructor
  · rintro ⟨h0, hn⟩
    exact ⟨h0, fun hm => hn ⟨hm, h0⟩⟩
  · rintro ⟨h0, hn⟩
    exact ⟨h0, fun hm => hn hm.1⟩

/-- Markings with the same unmarked `𝒱₀` have the same fine′ outputs. -/
theorem outputs_congr_of_vinesV0 {w p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden w) {mk mk' : Stage1Mk.MarkFn w}
    (h : vinesV0 a.prime.skeleton a.totalSigma (mk a.prime) = vinesV0 a.prime.skeleton a.totalSigma (mk' a.prime)) :
    a.outputs (p := p) (kind := kind) mk = a.outputs (p := p) (kind := kind) mk' := by
  unfold PrescribedPrimeGarden.outputs PrescribedPrimeGarden.state PrimeData.fineState
  exact PrimeData.state_allCoreOutputs_congr _ h _ _

/-- The internal units marking of the piece of `a` has the fine′ outputs of the fine marking. -/
theorem outputs_fixMark_mkAt {w p : ℕ} {kind : Bool} (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    a.outputs (p := p) (kind := kind) (fixMark a (mkAt mkF a)) = a.outputs (p := p) (kind := kind) mkF :=
  outputs_congr_of_vinesV0 a (by rw [fixMark_self]; exact vinesV0_mkAt mkF a)

/-- No unit at a marked set iff no unmarked `𝒱₀` vine. -/
theorem unitBlocks_nil_iff {w : ℕ} (G : Garden w) (σ : Prescription G) (Mk : Set (Stage1.CLVine G)) :
    unitBlocks G σ Mk = [] ↔ vinesV0 G σ Mk = ∅ := by
  constructor
  · intro h
    ext c
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hc
    obtain ⟨-, -, u, hu, -⟩ := (vinesV0_iff_unit_coverMk G σ c).mp hc
    rw [h] at hu
    exact absurd hu (List.not_mem_nil)
  · intro h
    by_contra hne
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨c, hc, -⟩ := unitBlocks_soundMk hu u.upper u.isBlock.2.1
    rw [h] at hc
    exact hc

/-- `unitBlocks` is empty at the piece marking iff it is empty at the fine marking. -/
theorem unitBlocks_mkAt_nil_iff {w : ℕ} (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    unitBlocks a.prime.skeleton a.totalSigma (mkAt mkF a) = [] ↔
      unitBlocks a.prime.skeleton a.totalSigma (mkF a.prime) = [] := by
  rw [unitBlocks_nil_iff, unitBlocks_nil_iff, vinesV0_mkAt]

/-! ## O3′ and O4′ at a marking -/

/-- **O3′ at a marking (B3)**: the weighted vine pieces of the marked producer.  The fine′ piece `π` of the fine
marking `mkF` has a unit (a run of a marked group or a unit of an unmarked group); its weighted class sum over the
coarse′ class `clsPMk mkC π` is `RepresentsInt` of the producer piece at the marking `mkAt mkF (repPt π)` (the fine marking restricted to `𝒱₀(σ)`, R177). -/
def VineCaseRepresentsFWMk (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Mk.Stage1CarriesW P p N LG) →
  ∀ (Adm : ∀ {ι : Type}, LFTwist.FamilyReconstruction (2 * R) ι → Prop), TwistClosedAdm p A Adm →
  ∀ (mkF mkC : Stage1Mk.MarkFn (2 * R)), MarkingOK mkF mkC →
    (∀ a : PrescribedPrimeGarden (2 * R), a.layered ∈ A → Adm (startAt a (mkAt mkF a))) →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
    (∀ j x, (g j x).im = 0) →
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∀ π : PcA R p (objKind (2 * R)) A mkF,
    unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mkAt mkF (repPt π)) ≠ [] →
    Stage1Piece.RepresentsInt (P := P) ((repPt π).normalizedPiece P.d (mkAt mkF (repPt π))) N tt base roots
      (cψ ^ (16 * N) * s)
      (∑ LG ∈ membersP (clsPMk mkC π), valueSelW U.toLF tt base roots LG
        (selPMk p (objKind (2 * R)) A P base roots mkF π LG) (fwWeight p g base LG))

/-- **O4′ at a marking (B3)**: as `VineCaseRepresentsFWMk`, for the fine′ pieces with no unit at `mkF` (every vine
of `𝒱₀` of the representative is marked, or there is none). -/
def NoVineRepresentsFWMk (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Mk.Stage1CarriesW P p N LG) →
  ∀ (mkF mkC : Stage1Mk.MarkFn (2 * R)), MarkingOK mkF mkC →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∀ π : PcA R p (objKind (2 * R)) A mkF,
    unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mkAt mkF (repPt π)) = [] →
    Stage1Piece.RepresentsInt (P := P) ((repPt π).normalizedPiece P.d (mkAt mkF (repPt π))) N tt base roots
      (cψ ^ (16 * N) * s)
      (∑ LG ∈ membersP (clsPMk mkC π), valueSelW U.toLF tt base roots LG
        (selPMk p (objKind (2 * R)) A P base roots mkF π LG) (fwWeight p g base LG))

/-! ## The `RepresentsIntMK` form -/

/-- A producer piece as a world Stage-1′ piece: no pins, no filters, indicator `1`, with given survivor data and
`nProt` (B3s adds pins and filters; B4 supplies `surv` and `nProt`). -/
def pieceMK {d R : ℕ} (π : Stage1PieceD d R) (surv : SurvivorData π.Gsb) (nProt : ℕ) : Stage1PieceMK d R :=
  { π with surv := surv, nProt := nProt, fix := fun _ => none, filt := fun _ => none, ind := fun _ => 1 }

/-- **The marked producer for the unmarked units in `RepresentsIntMK` form (B3 main export)**: every fine′ piece of
the marked producer (vine case and vine-free case), as `pieceMK` with arbitrary survivor data and `nProt`, represents
its weighted class sum with the protected-object loss `L^{cP·d·nProt}` (any `cP ≥ 0`). -/
def MarkedUnitsRepresentsFW (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Mk.Stage1CarriesW P p N LG) →
  ∀ (Adm : ∀ {ι : Type}, LFTwist.FamilyReconstruction (2 * R) ι → Prop), TwistClosedAdm p A Adm →
  ∀ (mkF mkC : Stage1Mk.MarkFn (2 * R)), MarkingOK mkF mkC →
    (∀ a : PrescribedPrimeGarden (2 * R), a.layered ∈ A → Adm (startAt a (mkAt mkF a))) →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
    (∀ j x, (g j x).im = 0) →
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∀ π : PcA R p (objKind (2 * R)) A mkF,
  ∀ (surv : SurvivorData ((repPt π).normalizedPiece P.d (mkAt mkF (repPt π))).Gsb) (nProt : ℕ) (cP : ℝ), 0 ≤ cP →
    (pieceMK ((repPt π).normalizedPiece P.d (mkAt mkF (repPt π))) surv nProt).RepresentsIntMK N cP tt base roots
      (cψ ^ (16 * N) * s)
      (∑ LG ∈ membersP (clsPMk mkC π), valueSelW U.toLF tt base roots LG
        (selPMk p (objKind (2 * R)) A P base roots mkF π LG) (fwWeight p g base LG))

end WaveTurbulence.Flower.MkUnits
