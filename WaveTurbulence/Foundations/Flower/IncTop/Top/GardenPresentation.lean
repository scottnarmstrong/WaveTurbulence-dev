/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Top.StarPresentation
public import WaveTurbulence.Foundations.IncohInst.CoupleRows
public import WaveTurbulence.Foundations.IncohInst.TreeRows
public import WaveTurbulence.Foundations.IncohInst.CosetDecorationIdentity

/-! Ported by source from C2-B-TOP `C2BTop.GardenPresentation` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Star weights of a decoded regular object as a root-modulated internal measure

For a decoded couple (resp. paired tree), every node momentum of the coset decoration of the lattice
parameter `p` is `k + Σ_{ij} row(b) ij • latticePoint L (p ij)` (root coefficient one, main's
`coupleNodeRow`/`treeNodeRow`).  Choosing a star presentation for each weighted node, `starProduct`
gives a `RootMeasure` whose value at `pairedLattice L p` is the star weight of the coset decoration
(`couple_starWeight_eq_value`, `tree_starWeight_eq_value`) and whose moment is `≤ ∏_{a ∈ S} c a`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped ENNReal
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.IncohInst WaveTurbulence.Incoh WaveTurbulence.Links WaveTurbulence.Cut2A

section Choice

variable {d : ℕ} {J : ℕ} {ω : Star d → ℂ} {c : ℝ}

/-- The parameter type of a chosen star presentation. -/
def presType (h : StarPresented J ω c) : Type := h.choose

instance presInst (h : StarPresented J ω c) : MeasurableSpace (presType h) := h.choose_spec.choose

/-- The chosen star presentation. -/
def presMeasure (h : StarPresented J ω c) : SpatialMeasure (Star d) (presType h) :=
  h.choose_spec.choose_spec.choose

theorem presMeasure_moment (h : StarPresented J ω c) : starMoment J (presMeasure h) ≤ ENNReal.ofReal c :=
  h.choose_spec.choose_spec.choose_spec.1

theorem presMeasure_value (h : StarPresented J ω c) (y : Star d) : (presMeasure h).value y = ω y :=
  h.choose_spec.choose_spec.choose_spec.2 y

end Choice

variable {d n : ℕ} {w : ℕ} {T : Fin w → TTree}

/-- The root-modulated internal measure of the star weights on `S`, along integer node rows. -/
def starRootMeasure (J : ℕ) (S : Finset (GNode T)) (ω : GNode T → Star d → ℂ) (c : GNode T → ℝ)
    (h : ∀ a ∈ S, StarPresented J (ω a) (c a)) (row : GNode T → (Fin n × Fin 2) → ℤ) :
    RootMeasure d n ((i : S) → presType (h i.1 i.2)) :=
  starProduct (fun i => measurableDensity (presMeasure (h i.1 i.2)))
    (fun i => measurable_measurableDensity _) (fun i s => row (starNode i.1 s))

theorem starRootMeasure_value (J : ℕ) (S : Finset (GNode T)) (ω : GNode T → Star d → ℂ)
    (c : GNode T → ℝ) (h : ∀ a ∈ S, StarPresented J (ω a) (c a))
    (row : GNode T → (Fin n × Fin 2) → ℤ) (k : Mom d) (x : PairedMomentum d n) :
    ((starRootMeasure J S ω c h row).at k).value x =
      ∏ a ∈ S, ω a (rowStar (fun s => row (starNode a s)) k x) := by
  unfold starRootMeasure
  rw [starProduct_at_value]
  simp_rw [starValue_measurableDensity, presMeasure_value]
  exact Finset.prod_coe_sort S (fun a => ω a (rowStar (fun s => row (starNode a s)) k x))

theorem starRootMeasure_momentMass_le (J : ℕ) (S : Finset (GNode T)) (ω : GNode T → Star d → ℂ)
    (c : GNode T → ℝ) (h : ∀ a ∈ S, StarPresented J (ω a) (c a))
    (row : GNode T → (Fin n × Fin 2) → ℤ) :
    (starRootMeasure J S ω c h row).momentMass J ≤ ∏ a ∈ S, ENNReal.ofReal (c a) := by
  unfold starRootMeasure
  refine (starProduct_momentMass_le _ _ _ J fun i => ?_).trans ?_
  · rw [starMoment_measurableDensity]
    exact (presMeasure_moment (h i.1 i.2)).trans_lt ENNReal.ofReal_lt_top
  · simp_rw [starMoment_measurableDensity]
    refine (Finset.prod_le_prod' fun i _ => presMeasure_moment (h i.1 i.2)).trans_eq ?_
    exact Finset.prod_coe_sort S (fun a => ENNReal.ofReal (c a))

/-- Integer-row evaluation in root/internal form. -/
theorem momentumRowEval_rootLink {m : ℕ} (row : MomentumCoordinate m → ℤ) (hrow : row none = 1)
    (k : Mom d) (p : (Fin m × Fin 2) → Fin d → ℤ) (L : ℝ) :
    momentumRowEval (rootLinkMomenta k (fun i j => latticePoint L (p (i, j)))) row =
      k + rowLinear (fun ij => row (some ij)) (pairedLattice L p) := by
  change (∑ j, row j • rootLinkMomenta k (fun i j => latticePoint L (p (i, j))) j) = _
  rw [Fintype.sum_option, hrow, one_smul]
  congr 1
  unfold rowLinear
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  rfl

/-- Couple rows. -/
def coupleRow {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (b : GNode G.tree) :
    (Fin Q.links.length × Fin 2) → ℤ :=
  fun ij => coupleNodeRow hQ b (some ij)

theorem couple_coset_eq_row {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (L : ℝ) (k : Mom d)
    (p : Fin Q.links.length × Fin 2 → Fin d → ℤ) (b : GNode G.tree) :
    cosetDecoration G L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 b =
      k + rowLinear (coupleRow hQ b) (pairedLattice L p) := by
  rw [← couple_decOfParams_eq_coset hQ L k (fun j => (p (j, 0), p (j, 1)))]
  have he := coupleNodeRow_eval hQ b (rootLinkMomenta k (fun i j => latticePoint L (p (i, j))))
  rw [momentumRowEval_rootLink _ rfl] at he
  exact he.symm

theorem couple_starWeight_eq_value {LG : LayeredGarden 2} {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    (J : ℕ) (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
    (c : GNode LG.garden.tree → ℝ) (h : ∀ a ∈ S, StarPresented J (ω a) (c a)) (L : ℝ) (k : Mom d)
    (p : Fin Q.links.length × Fin 2 → Fin d → ℤ) :
    starWeight S ω
        (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
      ((starRootMeasure J S ω c h (coupleRow hQ)).at k).value (pairedLattice L p) := by
  rw [starRootMeasure_value]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  unfold starMomenta rowStar
  congr 1
  funext s
  exact couple_coset_eq_row hQ L k p (starNode a s)

/-- Paired-tree rows. -/
def treeRow {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) (b : GNode G.tree) :
    (Fin (X.treeLinks (G.sig 0)).length × Fin 2) → ℤ :=
  fun ij => treeNodeRow hX b (some ij)

theorem tree_coset_eq_row {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) (L : ℝ) (k : Mom d)
    (p : Fin (X.treeLinks (G.sig 0)).length × Fin 2 → Fin d → ℤ) (b : GNode G.tree) :
    cosetDecoration G L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 b =
      k + rowLinear (treeRow hX b) (pairedLattice L p) := by
  rw [← tree_decOfParams_eq_coset hX L k (fun j => (p (j, 0), p (j, 1)))]
  have he := treeNodeRow_eval hX b (rootLinkMomenta k (fun i j => latticePoint L (p (i, j))))
  rw [momentumRowEval_rootLink _ rfl] at he
  exact he.symm

theorem tree_starWeight_eq_value {LG : LayeredGarden 1} {X : RegChain} (hX : X.DecodesTree LG.garden)
    (J : ℕ) (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
    (c : GNode LG.garden.tree → ℝ) (h : ∀ a ∈ S, StarPresented J (ω a) (c a)) (L : ℝ) (k : Mom d)
    (p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ) :
    starWeight S ω
        (cosetDecoration LG.garden L k
          (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
      ((starRootMeasure J S ω c h (treeRow hX)).at k).value (pairedLattice L p) := by
  rw [starRootMeasure_value]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  unfold starMomenta rowStar
  congr 1
  funext s
  exact tree_coset_eq_row hX L k p (starNode a s)

end WaveTurbulence.Flower.IncTop