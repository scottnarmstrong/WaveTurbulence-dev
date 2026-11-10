/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1CoreBound
public import WaveTurbulence.Foundations.Spine.PrefixPieceSmall
public import WaveTurbulence.Foundations.Spine.GardenPartition
public import WaveTurbulence.Foundations.Spine.Stage1Sigma
public import WaveTurbulence.Foundations.Spine.TypeFamily
/-! The Stage 1 reduction gate (TARGET L1927-L1976, L2040-L2051, L2236-L2255): for every finite set `A` of
canonical layered gardens of one width and order, and every leaf-modified kernel family `F` that is
leafwise controlled with total size at most `s`, the sum of `F` over `A` is the sum of the values of a
Stage 1 piece family `S` (a partition of `A` into classes) whose pieces represent the class sums leafwise
(row 7: `Represents`), are sound (rows 8, 9: `Sound`, order) and obey the class counts (row 10).
The class `S` depends only on `A`, never on `F`: this is the reading of the source, where the Stage 1
reduction is applied leafwise (L2065-L2067), and it is a separately named spine input (RULINGS R9b). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset
open scoped Classical

/-- The gardens summed in (a),(b): canonical of width `w` (width `2`: nonregular couples), truncated,
of order `N`, balanced signature. -/
def Stage1Carries (P : WTParams) (p N : ℕ) {w : ℕ} (LG : LayeredGarden w) : Prop :=
  IsCanonGC (p + 1) LG ∧ LG.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
    LG.garden.order = N ∧ IsBalancedSig LG.garden.sig ∧
    (∀ h : w = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2))

/-- The pieces are indexed by (congruence class, prescription `sigma` on the groups, finer class `tau`)
(RULINGS R19 (1), R24 D1, D2; TARGET L1950). The piece type `Pc` of `Stage1Data` is an arbitrary finite type,
so a producer may index by the prescriptions restricted to the groups; the `∃! π` below refers to that index.
`sel π LG κ` may depend on `LG`, so it can carry both `sigma` and the membership `LG ∈ tau`.
`members c` are the gardens of the class `c`; they partition `A`. The `sigma`-split partitions the
DECORATION sum, not the gardens: `cls π` is the class of the piece `π`, and `sel π LG` is the decoration
restriction `Z` of its prescription, so that for every garden of a class and every decoration there is
exactly one piece of that class whose restriction holds. Hence "garden sum = sum over classes, sum over
`sigma`, of piece values" (`sum_eq_sum_pieces`). -/
def Stage1Partition {R d : ℕ} {Pc Cl : Type} (roots : Fin (2 * R) → (Fin d → ℤ))
    (A : Finset (LayeredGarden (2 * R))) (members : Cl → Finset (LayeredGarden (2 * R)))
    (cls : Pc → Cl)
    (sel : Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden d roots 0 → Prop) : Prop :=
  (∀ LG, LG ∈ A ↔ ∃ c, LG ∈ members c) ∧ (∀ c c', c ≠ c' → Disjoint (members c) (members c')) ∧
  ∀ c, ∀ LG ∈ members c, ∀ κ, ∃! π, cls π = c ∧ sel π LG κ

/-- Row 10 (AMEND10, R56): the piece counts of TARGET (finalprooffin), L2241-L2252: the number of PIECES with data
`(g, r)` is at most `3^N C_0^N (C_0 r)! (C_0 R)! C_2^{g+r}` (a direct count; `stage1_core_bound` absorbs the
constants into `6 * C₀`). The classes `Cl`, `cls` are kept only for `Stage1Partition`. -/
def Stage1Counts (C₀ : ℕ) (P : WTParams) (R N : ℕ) (S : Stage1Data P R) (Cl : Type) (hCl : Fintype Cl)
    (cls : S.Pc → Cl) : Prop :=
  (∀ π, 1 ≤ (S.piece π).rbar ∧ (S.piece π).rbar ≤ N) ∧ (∀ π, (S.piece π).gbar ≤ N) ∧
  ∀ g r, ((((@univ S.Pc S.fin).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r).card : ℕ) : ℝ) ≤
      (3 : ℝ) ^ N * (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r)


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

/-- The garden sum is the sum over (class, prescription) pieces of the restricted family values, given
convergence of the decoration sums (the sigma-indicator partition, `LeafFamily.sum_valueSel`). -/
theorem sum_eq_sum_pieces {R : ℕ} {P : WTParams} {Pc Cl : Type} [Fintype Pc]
    (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (A : Finset (LayeredGarden (2 * R))) (members : Cl → Finset (LayeredGarden (2 * R)))
    (cls : Pc → Cl)
    (sel : Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    [Fintype Cl] (h : Stage1Partition roots A members cls sel)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (F : LeafFamily P (2 * R))
    (hsum : ∀ LG ∈ A, ∀ j, Summable fun κ : GenDecoration LG.garden P.d roots 0 =>
      kernelLeavesTerm P.L P.γ P.δ LG (F.H LG j) (fun b => tt b.1.1) 0 base κ) :
    ∑ LG ∈ A, F.value tt base roots LG =
      ∑ π, ∑ LG ∈ members (cls π), F.valueSel tt base roots LG (sel π LG) := by
  have hA : A = Finset.univ.biUnion members := by
    ext LG; simp [h.1 LG]
  have e1 : ∑ LG ∈ A, F.value tt base roots LG = ∑ c, ∑ LG ∈ members c, F.value tt base roots LG := by
    rw [hA, Finset.sum_biUnion]
    intro c _ c' _ hne
    exact h.2.1 c c' hne
  rw [e1, ← Finset.sum_fiberwise (s := Finset.univ) (g := cls)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hmem : ∀ LG ∈ members c, LG ∈ A := fun LG hLG => (h.1 LG).2 ⟨c, hLG⟩
  calc ∑ LG ∈ members c, F.value tt base roots LG
      = ∑ LG ∈ members c, ∑ π ∈ Finset.univ.filter (fun π => cls π = c),
          F.valueSel tt base roots LG (sel π LG) := by
        refine Finset.sum_congr rfl fun LG hLG => ?_
        symm
        refine F.sum_valueSel tt base roots LG (Finset.univ.filter (fun π => cls π = c))
          (fun π => sel π LG) (fun κ => ?_) (hsum LG (hmem LG hLG))
        obtain ⟨π, ⟨hπ1, hπ2⟩, hu⟩ := h.2.2 c LG hLG κ
        exact ⟨π, ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hπ1⟩, hπ2⟩,
          fun π' ⟨hπ', hs'⟩ => hu π' ⟨(Finset.mem_filter.mp hπ').2, hs'⟩⟩
    _ = ∑ π ∈ Finset.univ.filter (fun π => cls π = c), ∑ LG ∈ members (cls π),
          F.valueSel tt base roots LG (sel π LG) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun π hπ => ?_
        rw [(Finset.mem_filter.mp hπ).2]

end WaveTurbulence.LGSpine
