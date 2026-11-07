/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineHyperGapChoice
/-! HVC supports have an intrinsic designated bond up to mates, so the actual
hyper-object gap kind is independent of both designation and joint choices. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 LGSpine.SourceVine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {d : ℕ}

/-- Two arbitrary hyper presentations on an HVC support use the same actual bond. -/
theorem hyper_designations_unique_of_HVC (hM : M.IsMolecule) {S : Finset V} {a b c e f g : V}
    (hHVC : IsHVC M S a b) (P : HyperLikeRealization M S c e) (Q : HyperLikeRealization M S f g) :
    P.added = Q.added ∨ P.added = M.mate Q.added := by
  obtain ⟨r, hr, hR, n, hn, hc⟩ := hHVC
  have hP := hyper_added_unique_of_chain hM r P.added hr P.ends_eq hR P.adjoint.1 hn hc
  have hQ := hyper_added_unique_of_chain hM r Q.added hr Q.ends_eq hR Q.adjoint.1 hn hc
  rcases hP with hp | hp <;> rcases hQ with hq | hq
  · exact Or.inl (hp.symm.trans hq)
  · exact Or.inr (hp.symm.trans hq)
  · right
    have he := congrArg M.mate (hp.symm.trans hq)
    rwa [M.mate_mate] at he
  · left
    have he := congrArg M.mate (hp.symm.trans hq)
    simpa only [M.mate_mate] using he

/-- No independent choice of a designated object changes the gap-kind predicate on an HVC support. -/
theorem objects_gapKind_iff_of_HVC (hM : M.IsMolecule) (P Q : Object M) (hat : P.atoms = Q.atoms)
    {a b : V} (hHVC : IsHVC M P.atoms a b)
    (scale γ η : ℝ) (base : Mom d) (charge : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration scale base charge κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → charge v = 0)
    (kind : Molecule.GapKind) : P.HasGapKind scale γ η base κ kind ↔ Q.HasGapKind scale γ η base κ kind := by
  rcases P with ⟨S, u, v, ps⟩
  rcases Q with ⟨T, x, y, qs⟩
  change S = T at hat
  subst T
  have hex : ∃ e : D, M.ends e = s(a, b) ∧ (Mole.eraseBond M e).IsBlock S a b := by
    obtain ⟨e, he, hb, _⟩ := hHVC
    exact ⟨e, he, hb⟩
  cases ps with
  | vc hP =>
    obtain ⟨e, he, hb⟩ := hex
    exact (block_not_hyper hP.1 e he hb).elim
  | hyper R =>
    cases qs with
    | vc hQ =>
      obtain ⟨e, he, hb⟩ := hex
      exact (block_not_hyper hQ.1 e he hb).elim
    | hyper U =>
      exact hyper_gapKind_iff_of_same_bond hM R U (hyper_designations_unique_of_HVC hM hHVC R U)
        scale γ η base charge κ hκ hc0 kind

end WaveTurbulence.VineA
