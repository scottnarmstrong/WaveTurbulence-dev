/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUpperJointPair
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Spine.SourceUpperJointPair
public import WaveTurbulence.Foundations.Spine.SourceBlockJointGaps
public import WaveTurbulence.Foundations.Spine.SplicedMoleculeDecoration
/-! Joint SG pairs for actual decorated ordinary blocks of the spliced garden. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceOrdinaryJointPairs` (sha256 dfe756c73004df8553c6c56a3b99e6dfdc970c61d405485e949bd351521a6888) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open WaveTurbulence.Mole

theorem source_actual_block_lower_sg_pair {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    {r : Mom d} (hr : G.molecule.IsBlockGap L base (bondIndex G z.1) S a r)
    (hsg : Molecule.gapKind L γ η r = .SG) :
    ∃ x y, TripleAt G b x y ∧ G.molecule.InGroup S x ∧ G.molecule.InGroup S y ∧
      Molecule.gapKind L γ η (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG := by
  have hk := spliced_molecule_decoration G hp hL base roots z
  have hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 →
      ∑ x ∈ G.molecule.dartsAt v, G.molecule.dartSign x • Molecule.kvec L base (bondIndex G z.1) x = 0 := by
    intro v hv hdeg
    exact (hk.2 v hv).trans (gardenSource_eq_zero_of_deg_four G hp _ v hdeg)
  obtain ⟨r', hr', hkind⟩ := source_block_lower_SG_gap G.molecule hM hB L γ η base
    (bondIndex G z.1) hk.1 hc hr hsg
  obtain ⟨x, y, hx, hy, hgx, hgy, hox, hoy, hgap⟩ := hr'
  have hnonzero := ((Vine.gapKind_eq_SG_iff L γ η r').mp hkind).1
  have hne : y ≠ G.molecule.mate x := by
    intro he
    apply hnonzero
    rw [hgap, he]
    simp only [Molecule.gapAt, Molecule.kvec, hk.1 x, sub_self]
  refine ⟨x, y, ⟨hx, hy, hne, ?_⟩, hgx, hgy, ?_⟩
  · rw [hox, hoy]
    decide
  · simpa only [hgap] using hkind

end WaveTurbulence.GammaLow.Famc
