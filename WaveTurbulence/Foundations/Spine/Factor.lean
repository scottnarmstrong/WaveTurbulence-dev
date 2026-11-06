/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Locality
/-! # The spliced integrand factors over a family of disjoint ladders (S3c) -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay Finset
open scoped Classical

variable {w d : ℕ} {G : Garden w} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Union of the atom sets of the ladders. -/
def Uni (S : ι → Finset (GBranch G.tree)) : Finset (GBranch G.tree) := univ.biUnion S

/-- A dart internal to some ladder. -/
def IntDart (S : ι → Finset (GBranch G.tree)) (x : GardenDart G) : Prop :=
  ∃ i, G.molecule.InGroup (S i) x

/-- The part of the spliced momentum amplitude not belonging to any ladder. -/
noncomputable def restAmp (D : SplicedKernelData G d) (S : ι → Finset (GBranch G.tree))
    (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) : ℂ :=
  outerLadderMomentumAmplitude G D (Uni S) L γ η base z *
    ∏ x ∈ G.molecule.bonds.filter (fun x => G.molecule.InGroup (Uni S) x ∧ ¬ IntDart S x),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G z x))

lemma pairwiseDisjoint_S (S : ι → Finset (GBranch G.tree))
    (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    ((univ : Finset ι) : Set ι).PairwiseDisjoint S := fun i _ j _ hij => hS i j hij

lemma inGroup_sub_uni (S : ι → Finset (GBranch G.tree)) (i : ι) (x : GardenDart G)
    (h : G.molecule.InGroup (S i) x) : G.molecule.InGroup (Uni S) x :=
  ⟨mem_biUnion.mpr ⟨i, mem_univ _, h.1⟩, mem_biUnion.mpr ⟨i, mem_univ _, h.2⟩⟩

lemma inGroup_unique (S : ι → Finset (GBranch G.tree)) (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (i j : ι) (x : GardenDart G) (hi : G.molecule.InGroup (S i) x)
    (hj : G.molecule.InGroup (S j) x) : i = j := by
  by_contra hne
  exact Finset.disjoint_left.mp (hS i j hne) hi.1 hj.1

theorem momAmp_factor (D : SplicedKernelData G d) (S : ι → Finset (GBranch G.tree))
    (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (hH : ∀ i, Disjoint (S i) D.hinges)
    (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) :
    splicedMomentumAmplitude G D L γ η base z =
      restAmp D S L γ η base z * ∏ i, ladderWeight D (S i) L γ η base z := by
  have hU : Disjoint (Uni S) D.hinges := by
    rw [Uni, Finset.disjoint_biUnion_left]
    exact fun i _ => hH i
  rw [splicedMomentumAmplitude_split G D (Uni S) hU L γ η base z]
  unfold localLadderMomentumAmplitude restAmp ladderWeight
  have hpd := pairwiseDisjoint_S (G := G) S hS
  have heps : (∏ v ∈ Uni S, ((epsCoef (z (v.child 0)) (z (v.child 1)) (z (v.child 2)) : ℝ) : ℂ)) =
      ∏ i, ∏ v ∈ S i, ((epsCoef (z (v.child 0)) (z (v.child 1)) (z (v.child 2)) : ℝ) : ℂ) :=
    Finset.prod_biUnion hpd
  have hgapU : localLadderGapIndicator G D (Uni S) L γ η base z =
      ∏ i, localLadderGapIndicator G D (S i) L γ η base z := by
    unfold localLadderGapIndicator
    exact Finset.prod_biUnion hpd
  have hedgeA : ((G.molecule.bonds.filter (G.molecule.InGroup (Uni S))) =
      (univ.biUnion fun i => G.molecule.bonds.filter (G.molecule.InGroup (S i))) ∪
        G.molecule.bonds.filter (fun x => G.molecule.InGroup (Uni S) x ∧ ¬ IntDart S x)) := by
    ext x
    simp only [mem_filter, mem_union, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨hb, hx⟩
      by_cases hi : IntDart S x
      · obtain ⟨i, hi⟩ := hi
        exact Or.inl ⟨i, hb, hi⟩
      · exact Or.inr ⟨hb, hx, hi⟩
    · rintro (⟨i, hb, hi⟩ | ⟨hb, hx, -⟩)
      · exact ⟨hb, inGroup_sub_uni S i x hi⟩
      · exact ⟨hb, hx⟩
  have hedgeD : Disjoint (univ.biUnion fun i => G.molecule.bonds.filter (G.molecule.InGroup (S i)))
      (G.molecule.bonds.filter (fun x => G.molecule.InGroup (Uni S) x ∧ ¬ IntDart S x)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_biUnion, mem_univ, true_and, mem_filter] at hx hx'
    obtain ⟨i, -, hi⟩ := hx
    exact hx'.2.2 ⟨i, hi⟩
  have hedgeP : (∏ x ∈ G.molecule.bonds.filter (G.molecule.InGroup (Uni S)),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G z x))) =
      (∏ i, ∏ x ∈ G.molecule.bonds.filter (G.molecule.InGroup (S i)),
        D.edgeAmplitude x (base + latticePoint L (bondIndex G z x))) *
      ∏ x ∈ G.molecule.bonds.filter (fun x => G.molecule.InGroup (Uni S) x ∧ ¬ IntDart S x),
        D.edgeAmplitude x (base + latticePoint L (bondIndex G z x)) := by
    rw [hedgeA, Finset.prod_union hedgeD, Finset.prod_biUnion]
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_filter] at hx hx'
    exact hij (inGroup_unique S hS i j x hx.2 hx'.2)
  rw [heps, hgapU, hedgeP]
  push_cast
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  push_cast
  ring

end WaveTurbulence.CoarseSpliced
