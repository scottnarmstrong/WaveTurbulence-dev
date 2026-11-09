/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1Gate
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1CoreBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1Interface
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1PieceBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.Stage1Gate`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 The Stage 1 reduction gate (TARGET L1927-L1976, L2040-L2051, L2236-L2255): for every finite set `A` of
canonical layered gardens of one width and order, and every leaf-modified kernel family `F` that is
leafwise controlled with total size at most `s`, the sum of `F` over `A` is the sum of the values of a
Stage 1 piece family `S` (a partition of `A` into classes) whose pieces represent the class sums leafwise
(row 7: `Represents`), are sound (rows 8, 9: `Sound`, order) and obey the class counts (row 10).
The class `S` depends only on `A`, never on `F`: this is the reading of the source, where the Stage 1
reduction is applied leafwise (L2065-L2067), and it is a separately named spine input (RULINGS R9b). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset
open scoped Classical

/-- Row 10 (AMEND10, R56): the piece counts of TARGET (finalprooffin), L2241-L2252: the number of PIECES with data
`(g, r)` is at most `3^N C_0^N (C_0 r)! (C_0 R)! C_2^{g+r}` (a direct count; `stage1_core_bound` absorbs the
constants into `6 * C₀`). The classes `Cl`, `cls` are kept only for `Stage1Partition`. -/
def Stage1Counts (C₀ : ℕ) (P : WTParams) (R N : ℕ) (S : Stage1Data P R) (Cl : Type) (hCl : Fintype Cl)
    (cls : S.Pc → Cl) : Prop :=
  (∀ π, 1 ≤ (S.piece π).rbar ∧ (S.piece π).rbar ≤ N) ∧ (∀ π, (S.piece π).gbar ≤ N) ∧
  ∀ g r, ((((@univ S.Pc S.fin).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r).card : ℕ) : ℝ) ≤
      (3 : ℝ) ^ N * (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r)

/-- The PRE-AMEND6' Stage 1 reduction gate (arbitrary leaf family and arbitrary `A`): kept only as the old gate that
implies the new one (`stage1ReductionAt_of_old`); R44 shows it is not derivable from TARGET. -/
def Stage1ReductionAtOld (C₀ : ℕ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Carries P p N LG) →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (F : LeafFamily P (2 * R)) (s : ℝ), 0 < s → (∀ LG ∈ A, F.Controlled LG) →
    (∀ LG ∈ A, F.size LG ≤ s) →
  ∃ (S : Stage1Data P R) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl)
    (members : Cl → Finset (LayeredGarden (2 * R)))
    (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop),
    Stage1Partition roots A members cls sel ∧
    (∀ π, (S.piece π).Represents N tt base roots (members (cls π)) (sel π) F s (S.val π)) ∧
    (∀ π, (S.piece π).Sound p base roots) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧
    Stage1Counts C₀ P R N S Cl hCl cls


/-- The Stage 1 reduction gate at `P` with class-count constant `C₀` (AMEND6', R47-FINAL, design P*): the leaf data
is a pair-type family `U` (`TypeFamily`, with `U.Bounded p`), `U.toLF` is the induced leaf family in `Represents`,
and `A` is twist-closed (`TwistClosed`, R44 (i)). -/
def Stage1ReductionAt (C₀ : ℕ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Carries P p N LG) → TwistClosed p A →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∃ (S : Stage1Data P R) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl)
    (members : Cl → Finset (LayeredGarden (2 * R)))
    (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop),
    Stage1Partition roots A members cls sel ∧
    (∀ π, (S.piece π).Represents N tt base roots (members (cls π)) (sel π) U.toLF s (S.val π)) ∧
    (∀ π, (S.piece π).Sound p base roots) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧
    Stage1Counts C₀ P R N S Cl hCl cls

/-- The old gate implies the new one (it quantifies over every leaf family): AMEND6' only weakens the gate. -/
theorem stage1ReductionAtT_of_old (C₀ : ℕ) (P : WTParams) (h : Stage1ReductionAtOld C₀ P) :
    Stage1ReductionAt C₀ P := by
  intro p hp R h1 h2 N hN1 hN2 A hA _ tt htt base roots U s hs hU hsz
  refine h p hp R h1 h2 N hN1 hN2 A hA tt htt base roots U.toLF s hs (fun LG hLG => ?_) hsz
  intro i ℓ _
  have hlay : LG.layer ℓ.toNode ≤ p := by
    have hc := (hA LG hLG).1
    exact Canon.layer_le_of_isCanonGC hc _
  rw [show (U.toLF.H LG i) ℓ.1 = U.h i (LG.layer ℓ.toNode) ℓ.1.1 (LG.garden.pair ℓ).1.1 from
    typeProfiles_leaf LG (U.h i) ℓ]
  exact hU i _ _ _ hlay

end WaveTurbulence.GammaLow.FinalCount.H
