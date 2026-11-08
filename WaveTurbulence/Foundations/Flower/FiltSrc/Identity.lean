/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltSrc.Phase
public import WaveTurbulence.Foundations.Flower.FiltLink.Bridge
public import WaveTurbulence.Foundations.Flower.IncTop.Top.GardenPresentation
public import WaveTurbulence.Foundations.IncohInst.LinkParameterValues
public import WaveTurbulence.Foundations.IncohInst.CosetDecorationIdentity
public import WaveTurbulence.Foundations.IncohInst.Links.TreeLinks

/-! # D5b-1 FILT-SRC: the filter identity `hW'` (D5B-MAP K1)

On the coset decoration of a lattice link array `p` (the decoration at which `kernelLeavesW` reads its multiplier),
the D5 filter layers factor over the links:
`filtWeight F ann M κ * filtWeight Fu false Mu κ = arrayFiltWeight L φ p`, with link `j` carrying
`φ j = linkFiltWeight (E j) F Fu ann M Mu` and `E j` its two branches (`coupleLinkBlock`, `treeLinkBlock`).

Proof: `Ω_b = 2⟨x_b, y_b⟩` (`Links.omegaNode_eq`); at the chosen branch of link `j`, `(x, y) = (x_j, y_j)`, the lattice
points of `p (j, 0), p (j, 1)` (`couple_xNode_decOfParams`, `couple_decOfParams_eq_coset`); the partner has the same
`|Ω|` (`zeta_omega_link` + D5a `abs_omega_eq_of_signed`); the link blocks partition the branches
(`coupleLinkBranch_injective`/`_surjective`); then D5a `filtWeight_two_eq_prod_links`. Trees: the `tree_…` forms.

With INC-TOP's star presentation (`couple_starWeight_eq_value`, `tree_starWeight_eq_value`) this is `hW'` for the
D5 multiplier `starWeight S ω · filtWeight F ann M · filtWeight Fu false Mu` (`couple_starFiltWeight_eq`,
`tree_starFiltWeight_eq`), the premise of the `TopIdentity` twins. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Flower.FiltSrc
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.Links
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop

/-! ### Couples -/

section Couple

variable {G : Garden 2} {Q : RegCpl}

/-- The two branches of couple link `j`. -/
def coupleLinkBlock (hQ : Q.Decodes G) (j : Fin Q.links.length) : Finset (GBranch G.tree) :=
  Finset.univ.image (coupleLinkBranch hQ j)

theorem card_coupleLinkBlock_le (hQ : Q.Decodes G) (j : Fin Q.links.length) : (coupleLinkBlock hQ j).card ≤ 2 :=
  Finset.card_image_le.trans (by simp)

/-- **The filter multiplier of couple link `j`**: the two filter layers on its two branches. -/
def coupleLinkFilt (hQ : Q.Decodes G) (F Fu : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool)
    (M Mu : GBranch G.tree → ℝ) (j : Fin Q.links.length) : ℝ → ℂ :=
  linkFiltWeight (coupleLinkBlock hQ j) F Fu ann M Mu

/-- Both branches of link `j` have `|Ω| = |2⟨x_j, y_j⟩|` on the coset decoration of `p`. -/
theorem couple_abs_omega_linkBlock (hQ : Q.Decodes G) {d : ℕ} (L : ℝ) (k : Mom d)
    (p : Fin Q.links.length × Fin 2 → Fin d → ℤ) (j : Fin Q.links.length) (b : GBranch G.tree)
    (hb : b ∈ coupleLinkBlock hQ j) :
    |omegaNode G (cosetDecoration G L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) b| =
      |2 * linkBilinear L (p (j, 0), p (j, 1))| := by
  let θ := fun j : Fin Q.links.length => (latticePoint L (p (j, 0)), latticePoint L (p (j, 1)))
  have hκe : cosetDecoration G L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 =
      (decOfParams hQ k θ).1 :=
    (couple_decOfParams_eq_coset hQ L k (fun j => (p (j, 0), p (j, 1)))).symm
  have hκ : IsDecoration G (decOfParams hQ k θ).1 := (decOfParams hQ k θ).2.1
  rw [hκe]
  have h0 : |omegaNode G (decOfParams hQ k θ).1 (chosenBranch hQ j)| =
      |2 * linkBilinear L (p (j, 0), p (j, 1))| := by
    rw [omegaNode_eq hκ, couple_xNode_decOfParams hQ k θ j, couple_yNode_decOfParams hQ k θ j]
    rfl
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hb
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  rcases ha with rfl | rfl
  · exact h0
  · have hb' : (coupleLinkBranch hQ j 1).1 = (Q.links.get j).2 := by simp [coupleLinkBranch]
    rw [abs_omega_eq_of_signed (zeta_omega_link hQ hQ.1 hκ (List.get_mem Q.links j) (chosenBranch hQ j)
      (coupleLinkBranch hQ j 1) rfl hb')]
    exact h0

/-- **K1 for couples**: the two filter layers at the coset decoration of `p` are the array filter factor. -/
theorem couple_filtWeight_eq_arrayFiltWeight (hQ : Q.Decodes G) {d : ℕ} (L : ℝ) (k : Mom d)
    (F Fu : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ)
    (p : Fin Q.links.length × Fin 2 → Fin d → ℤ) :
    ProtDefs.filtWeight F ann M
        (cosetDecoration G L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
      ProtDefs.filtWeight Fu (fun _ => false) Mu
        (cosetDecoration G L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
      arrayFiltWeight L (coupleLinkFilt hQ F Fu ann M Mu) p := by
  have hcov (T : Finset (GBranch G.tree)) : T ⊆ Finset.univ.biUnion (coupleLinkBlock hQ) := by
    intro b _
    obtain ⟨⟨j, a⟩, hja⟩ := coupleLinkBranch_surjective hQ b
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, hja⟩⟩
  have hdisj : ((Finset.univ : Finset (Fin Q.links.length)) : Set (Fin Q.links.length)).PairwiseDisjoint
      (coupleLinkBlock hQ) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun b hbi hbj => hij ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hbi
    obtain ⟨a', -, he⟩ := Finset.mem_image.mp hbj
    exact (congrArg Prod.fst (coupleLinkBranch_injective hQ (a₁ := (j, a')) (a₂ := (i, a)) he)).symm
  rw [filtWeight_two_eq_prod_links _ F Fu ann M Mu Finset.univ (coupleLinkBlock hQ)
    (fun j => linkBilinear L (p (j, 0), p (j, 1))) hdisj (hcov F) (hcov Fu)
    (fun j _ b hb => couple_abs_omega_linkBlock hQ L k p j b hb)]
  rfl

/-- **`hW'` for couples**: the D5 multiplier at the coset decoration of `p` is the star presentation's value
times the array filter factor. -/
theorem couple_starFiltWeight_eq {LG : LayeredGarden 2} (hQ : Q.Decodes LG.garden) {d : ℕ}
    (J : ℕ) (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
    (c : GNode LG.garden.tree → ℝ) (h : ∀ a ∈ S, StarPresented J (ω a) (c a)) (L : ℝ) (k : Mom d)
    (F Fu : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
    (M Mu : GBranch LG.garden.tree → ℝ) (p : Fin Q.links.length × Fin 2 → Fin d → ℤ) :
    starWeight S ω
        (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
      ProtDefs.filtWeight F ann M
        (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
      ProtDefs.filtWeight Fu (fun _ => false) Mu
        (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
      ((starRootMeasure J S ω c h (coupleRow hQ)).at k).value (pairedLattice L p) *
        arrayFiltWeight L (coupleLinkFilt hQ F Fu ann M Mu) p := by
  rw [mul_assoc, couple_starWeight_eq_value hQ J S ω c h L k p,
    couple_filtWeight_eq_arrayFiltWeight hQ L k F Fu ann M Mu p]

end Couple

/-! ### Paired trees -/

section Tree

variable {G : Garden 1} {X : RegChain}

/-- The two branches of tree link `j`. -/
def treeLinkBlock (hX : X.DecodesTree G) (j : Fin (X.treeLinks (G.sig 0)).length) : Finset (GBranch G.tree) :=
  Finset.univ.image (treeLinkBranch hX j)

theorem card_treeLinkBlock_le (hX : X.DecodesTree G) (j : Fin (X.treeLinks (G.sig 0)).length) :
    (treeLinkBlock hX j).card ≤ 2 :=
  Finset.card_image_le.trans (by simp)

/-- **The filter multiplier of tree link `j`**. -/
def treeLinkFilt (hX : X.DecodesTree G) (F Fu : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool)
    (M Mu : GBranch G.tree → ℝ) (j : Fin (X.treeLinks (G.sig 0)).length) : ℝ → ℂ :=
  linkFiltWeight (treeLinkBlock hX j) F Fu ann M Mu

theorem tree_abs_omega_linkBlock (hX : X.DecodesTree G) {d : ℕ} (L : ℝ) (k : Mom d)
    (p : Fin (X.treeLinks (G.sig 0)).length × Fin 2 → Fin d → ℤ) (j : Fin (X.treeLinks (G.sig 0)).length)
    (b : GBranch G.tree) (hb : b ∈ treeLinkBlock hX j) :
    |omegaNode G (cosetDecoration G L k
        (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) b| =
      |2 * linkBilinear L (p (j, 0), p (j, 1))| := by
  let θ := fun j : Fin (X.treeLinks (G.sig 0)).length => (latticePoint L (p (j, 0)), latticePoint L (p (j, 1)))
  have hκe : cosetDecoration G L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 =
      (treeDecOfParams hX k θ).1 :=
    (tree_decOfParams_eq_coset hX L k (fun j => (p (j, 0), p (j, 1)))).symm
  have hκ : IsDecoration G (treeDecOfParams hX k θ).1 := (treeDecOfParams hX k θ).2.1
  rw [hκe]
  have h0 : |omegaNode G (treeDecOfParams hX k θ).1 (treeChosenBranch hX j)| =
      |2 * linkBilinear L (p (j, 0), p (j, 1))| := by
    rw [omegaNode_eq hκ, tree_xNode_decOfParams hX k θ j, tree_yNode_decOfParams hX k θ j]
    rfl
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hb
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  rcases ha with rfl | rfl
  · exact h0
  · have hb' : (treeLinkBranch hX j 1).1 = ((X.treeLinks (G.sig 0)).get j).2 := by simp [treeLinkBranch]
    rw [abs_omega_eq_of_signed (tree_zeta_omega_link hX hκ (List.get_mem (X.treeLinks (G.sig 0)) j)
      (treeChosenBranch hX j) (treeLinkBranch hX j 1) rfl hb')]
    exact h0

/-- **K1 for paired trees**. -/
theorem tree_filtWeight_eq_arrayFiltWeight (hX : X.DecodesTree G) {d : ℕ} (L : ℝ) (k : Mom d)
    (F Fu : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ)
    (p : Fin (X.treeLinks (G.sig 0)).length × Fin 2 → Fin d → ℤ) :
    ProtDefs.filtWeight F ann M
        (cosetDecoration G L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
      ProtDefs.filtWeight Fu (fun _ => false) Mu
        (cosetDecoration G L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
      arrayFiltWeight L (treeLinkFilt hX F Fu ann M Mu) p := by
  have hcov (T : Finset (GBranch G.tree)) : T ⊆ Finset.univ.biUnion (treeLinkBlock hX) := by
    intro b _
    obtain ⟨⟨j, a⟩, hja⟩ := treeLinkBranch_surjective hX b
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, hja⟩⟩
  have hdisj : ((Finset.univ : Finset (Fin (X.treeLinks (G.sig 0)).length)) :
      Set (Fin (X.treeLinks (G.sig 0)).length)).PairwiseDisjoint (treeLinkBlock hX) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun b hbi hbj => hij ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hbi
    obtain ⟨a', -, he⟩ := Finset.mem_image.mp hbj
    exact (congrArg Prod.fst (treeLinkBranch_injective hX (a₁ := (j, a')) (a₂ := (i, a)) he)).symm
  rw [filtWeight_two_eq_prod_links _ F Fu ann M Mu Finset.univ (treeLinkBlock hX)
    (fun j => linkBilinear L (p (j, 0), p (j, 1))) hdisj (hcov F) (hcov Fu)
    (fun j _ b hb => tree_abs_omega_linkBlock hX L k p j b hb)]
  rfl

/-- **`hW'` for paired trees**. -/
theorem tree_starFiltWeight_eq {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden) {d : ℕ}
    (J : ℕ) (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
    (c : GNode LG.garden.tree → ℝ) (h : ∀ a ∈ S, StarPresented J (ω a) (c a)) (L : ℝ) (k : Mom d)
    (F Fu : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
    (M Mu : GBranch LG.garden.tree → ℝ) (p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ) :
    starWeight S ω (cosetDecoration LG.garden L k
        (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
      ProtDefs.filtWeight F ann M (cosetDecoration LG.garden L k
        (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
      ProtDefs.filtWeight Fu (fun _ => false) Mu (cosetDecoration LG.garden L k
        (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
      ((starRootMeasure J S ω c h (treeRow hX)).at k).value (pairedLattice L p) *
        arrayFiltWeight L (treeLinkFilt hX F Fu ann M Mu) p := by
  rw [mul_assoc, tree_starWeight_eq_value hX J S ω c h L k p,
    tree_filtWeight_eq_arrayFiltWeight hX L k F Fu ann M Mu p]

end Tree

/-! ### The sup bound of the link multipliers (for the `‖φ i u‖ ≤ Bφ` premises) -/

/-- One constant bounds every couple and tree link multiplier (D5a `exists_linkFiltWeight_bound`, `#E ≤ 2`). -/
theorem exists_linkFilt_bound : ∃ B : ℝ, 1 ≤ B ∧
    (∀ {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (F Fu : Finset (GBranch G.tree))
      (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ) (j : Fin Q.links.length) (u : ℝ),
      ‖coupleLinkFilt hQ F Fu ann M Mu j u‖ ≤ B) ∧
    (∀ {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) (F Fu : Finset (GBranch G.tree))
      (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ) (j : Fin (X.treeLinks (G.sig 0)).length)
      (u : ℝ), ‖treeLinkFilt hX F Fu ann M Mu j u‖ ≤ B) := by
  obtain ⟨B, hB, hb⟩ := exists_linkFiltWeight_bound
  exact ⟨B, hB, fun hQ F Fu ann M Mu j u => hb _ F Fu ann M Mu (card_coupleLinkBlock_le hQ j) u,
    fun hX F Fu ann M Mu j u => hb _ F Fu ann M Mu (card_treeLinkBlock_le hX j) u⟩

end WaveTurbulence.Flower.FiltSrc
