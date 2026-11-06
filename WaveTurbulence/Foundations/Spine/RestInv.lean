/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Factor
/-! # Invariance of the non-ladder part of the integrand along fibres (S3c) -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay Finset
open scoped Classical

variable {w d : ℕ} {G : Garden w} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Two decorations agree off the internal darts of the ladders. -/
def AgreeOff (S : ι → Finset (GBranch G.tree)) {roots : Fin w → (Fin d → ℤ)}
    (z z' : GenDecoration G d roots 0) : Prop :=
  ∀ x, ¬ IntDart S x → bondIndex G z.1 x = bondIndex G z'.1 x

lemma not_intDart_of_atom_notMem (S : ι → Finset (GBranch G.tree)) (x : GardenDart G)
    (h : G.molecule.atom x ∉ Uni S) : ¬ IntDart S x := by
  rintro ⟨i, hi⟩
  exact h (mem_biUnion.mpr ⟨i, mem_univ _, hi.1⟩)

lemma agree_atom (S : ι → Finset (GBranch G.tree)) {roots : Fin w → (Fin d → ℤ)}
    {z z' : GenDecoration G d roots 0} (h : AgreeOff S z z') (v : GBranch G.tree) (hv : v ∉ Uni S) :
    ∀ x, G.molecule.atom x = v → bondIndex G z.1 x = bondIndex G z'.1 x :=
  fun x hx => h x (not_intDart_of_atom_notMem S x (by rw [hx]; exact hv))

theorem splicedFrequency_rest (hP : G.IsPlain) (D : SplicedKernelData G d) (S : ι → Finset (GBranch G.tree))
    (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z z' : GenDecoration G d roots 0) (h : AgreeOff S z z') (v : GBranch G.tree) (hv : v ∉ Uni S) :
    splicedFrequency G D L γ δ base z.1 v = splicedFrequency G D L γ δ base z'.1 v := by
  obtain ⟨hr, h0, h1, h2⟩ := slot_eq_of_atom hP roots z z' v (agree_atom S h v hv)
  unfold splicedFrequency omegaNode resFactor cosetDecoration
  rw [hr, h0, h1, h2]

theorem restAmp_congr (hP : G.IsPlain) (D : SplicedKernelData G d) (S : ι → Finset (GBranch G.tree))
    (hH : ∀ i, Disjoint (S i) D.hinges)
    (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z z' : GenDecoration G d roots 0) (h : AgreeOff S z z') :
    restAmp D S L γ η base z.1 = restAmp D S L γ η base z'.1 := by
  unfold restAmp outerLadderMomentumAmplitude
  have heps : ∀ v ∈ (univ.filter fun v => v ∉ D.hinges) \ Uni S,
      epsCoef (z.1 (v.child 0)) (z.1 (v.child 1)) (z.1 (v.child 2)) =
      epsCoef (z'.1 (v.child 0)) (z'.1 (v.child 1)) (z'.1 (v.child 2)) := by
    intro v hv
    obtain ⟨-, h0, h1, h2⟩ := slot_eq_of_atom hP roots z z' v (agree_atom S h v (mem_sdiff.mp hv).2)
    rw [h0, h1, h2]
  have hgap : ∀ v ∈ univ \ Uni S, splicedVertexGapFactor G D L γ η base z.1 v =
      splicedVertexGapFactor G D L γ η base z'.1 v := by
    intro v hv
    have hvU := (mem_sdiff.mp hv).2
    unfold splicedVertexGapFactor
    cases hq : D.gapSpecification v with
    | none => rfl
    | some q =>
      dsimp only
      have h1 := agree_atom S h v hvU q.first q.at_first
      have h2 := agree_atom S h v hvU q.second q.at_second
      rw [h1, h2]
  have hedge : ∀ x ∈ G.molecule.bonds \ (G.molecule.bonds.filter (G.molecule.InGroup (Uni S))),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x)) =
      D.edgeAmplitude x (base + latticePoint L (bondIndex G z'.1 x)) := by
    intro x hx
    have hn : ¬ G.molecule.InGroup (Uni S) x := fun hh =>
      (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨(mem_sdiff.mp hx).1, hh⟩)
    have : ¬ IntDart S x := fun ⟨i, hi⟩ => hn (inGroup_sub_uni S i x hi)
    rw [h x this]
  have hcross : ∀ x ∈ G.molecule.bonds.filter (fun x => G.molecule.InGroup (Uni S) x ∧ ¬ IntDart S x),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x)) =
      D.edgeAmplitude x (base + latticePoint L (bondIndex G z'.1 x)) := by
    intro x hx
    rw [h x (mem_filter.mp hx).2.2]
  have hhinge : (fun x : HingeDarts G D.hinges => base + latticePoint L (bondIndex G z.1 x.1)) =
      (fun x : HingeDarts G D.hinges => base + latticePoint L (bondIndex G z'.1 x.1)) := by
    funext x
    have hn : ¬ IntDart S x.1 := by
      rintro ⟨i, hi⟩
      rcases x.2 with hx | hx
      · exact Finset.disjoint_left.mp (hH i) hi.1 hx
      · exact Finset.disjoint_left.mp (hH i) hi.2 hx
    rw [h x.1 hn]
  rw [Finset.prod_congr rfl (fun v hv => congrArg (fun r : ℝ => (r : ℂ)) (heps v hv)),
    Finset.prod_congr rfl (fun v hv => congrArg (fun r : ℝ => (r : ℂ)) (hgap v hv)),
    Finset.prod_congr rfl hedge, Finset.prod_congr rfl hcross, hhinge]

end WaveTurbulence.CoarseSpliced
