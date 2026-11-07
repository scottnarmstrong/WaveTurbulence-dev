/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedOrdinaryGroupGap
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedHingeChoiceFields
/-! All proper hinge pairs at one actual hinge have the same gap kind on
source-conserving labels, independently of the ordered pair choice. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset Stage1 RedSplice LGSpine.SourceVine
variable {w d : ℕ} {G : Garden w}

/-- External pairs at the two possible unit joints give exactly the same gap kind. -/
theorem properPairs_gapKind_eq (σ : Prescription G) {v : GBranch (stSt G σ).G.tree}
    {x y p q : GardenDart (stSt G σ).G}
    (hP : ProperPair G σ v x y) (hQ : ProperPair G σ v p q)
    (scale γ η : ℝ) (base : Mom d) (charge : GBranch G.tree → Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (hκ : G.molecule.IsDecoration scale base charge κ)
    (hc0 : ∀ b ∈ G.molecule.atoms, G.molecule.deg b = 4 → charge b = 0)
    (κsb : GardenDart (stSt G σ).G → (Fin d → ℤ))
    (hlab : ∀ z, κsb z = κ ((stSt G σ).M.od z)) :
    Molecule.gapKind scale γ η (Molecule.gapAt scale base κsb x y) =
      Molecule.gapKind scale γ η (Molecule.gapAt scale base κsb p q) := by
  obtain ⟨hT, u, hu, hv, j, hj, hx, hy, hnx, hny⟩ := hP
  obtain ⟨hU, t, ht, hw, k, hk, hp, hq, hnp, hnq⟩ := hQ
  have he : u = t := unit_eq_of_mem (Mole.garden_isMolecule G) σ hu ht u.isBlock.2.1
    (by have hh : u.upper = t.upper := hv.symm.trans hw; rw [hh]; exact t.isBlock.2.1)
  subst t
  have hc := kvec_cons scale base charge κ hκ hc0
  let K := Molecule.kvec scale base κ
  have hop : G.molecule.out ((stSt G σ).M.od x) ≠ G.molecule.out ((stSt G σ).M.od y) := by
    rw [(stSt G σ).M.od_out, (stSt G σ).M.od_out]
    exact hT.2.2.2
  have hoq : G.molecule.out ((stSt G σ).M.od p) ≠ G.molecule.out ((stSt G σ).M.od q) := by
    rw [(stSt G σ).M.od_out, (stSt G σ).M.od_out]
    exact hU.2.2.2
  have h1 := ext_pair_norm' G.molecule (Mole.garden_isMolecule G) u.isBlock hj K hc.1 hc.2 hx hy hnx hny hop
  have h2 := ext_pair_norm' G.molecule (Mole.garden_isMolecule G) u.isBlock hk K hc.1 hc.2 hp hq hnp hnq hoq
  have ep : Molecule.gapAt scale base κsb x y = K ((stSt G σ).M.od x) - K ((stSt G σ).M.od y) := by
    simp only [Molecule.gapAt, Molecule.kvec, hlab, K]
  have eq : Molecule.gapAt scale base κsb p q = K ((stSt G σ).M.od p) - K ((stSt G σ).M.od q) := by
    simp only [Molecule.gapAt, Molecule.kvec, hlab, K]
  rw [ep, eq]
  exact Vine.gapKind_eq_of_norm_eq scale γ η (h1.trans h2.symm)

/-- The actual first/second hinge choices have the gap kind of any proper pair at that hinge. -/
theorem collectionChoices_hinge_gapKind (σ : Prescription G)
    {v : GBranch (stSt G σ).G.tree} (hv : v ∈ (collectionChoices G σ).hinges)
    {p q : GardenDart (stSt G σ).G} (hQ : ProperPair G σ v p q)
    (scale γ η : ℝ) (base : Mom d) (charge : GBranch G.tree → Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (hκ : G.molecule.IsDecoration scale base charge κ)
    (hc0 : ∀ b ∈ G.molecule.atoms, G.molecule.deg b = 4 → charge b = 0)
    (κsb : GardenDart (stSt G σ).G → (Fin d → ℤ))
    (hlab : ∀ z, κsb z = κ ((stSt G σ).M.od z)) :
    ∃ x y, (collectionChoices G σ).first v = some x ∧ (collectionChoices G σ).second v = some y ∧
      Molecule.gapKind scale γ η (Molecule.gapAt scale base κsb x y) =
        Molecule.gapKind scale γ η (Molecule.gapAt scale base κsb p q) := by
  obtain ⟨x, y, hxy, hP, _⟩ := hingePair_spec (Mole.garden_isMolecule G) σ hv
  exact ⟨x, y, collectionChoices_first_of_pair hxy, collectionChoices_second_of_pair hxy,
    properPairs_gapKind_eq σ hP hQ scale γ η base charge κ hκ hc0 κsb hlab⟩

end WaveTurbulence.VineA.NormalizedSplice
