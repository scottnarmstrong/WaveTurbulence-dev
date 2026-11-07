/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineRank
/-! Vine removal, part 6 (FINALCOUNT-G2): `Δχ = -m` (DH23 L1798: "If 𝕍ℂ contains `m` atoms (including the
joints) then it is easy to verify that `Δχ = -m`"). The removed molecule has the atoms of the vine, `m = |C.atoms|`,
and `2(m-1)` bonds (the vine bond count, `FullVineChart.bond_count`: `2n = 2(m-1)`); `ΔF = 0` is the source
fact of L1798 ("`ΔF = ΔV_β = 0` by Props block_clcn, subpro (a)(e), subsetvc"). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace VineCut
variable {M : Molecule V D} (K : VineCut M)

theorem vc_atoms : K.vc.atoms = K.C.atoms := by
  ext z
  show z ∈ K.cutMol.atoms.filter (fun a => ¬ (a ∉ K.C.atoms)) ↔ z ∈ K.C.atoms
  simp only [Finset.mem_filter, not_not]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have : z ∈ M.atoms := objectAtoms_sub K.C h
  show z ∈ insert K.fb (insert K.fa M.atoms)
  simp [this]

theorem vc_atoms_card : K.vc.atoms.card = K.C.atoms.card := by rw [K.vc_atoms]

/-- `Δχ = B_VC - m + 2` when `ΔF = 0`. -/
theorem circuitRank_diff_gen (hF : K.post.numComponents = M.numComponents) :
    M.circuitRank - K.post.circuitRank = (K.vc.bonds.card : ℤ) - K.C.atoms.card + 2 := by
  have h := K.circuitRank_diff
  have h2 : K.vc.circuitRank = (K.vc.bonds.card : ℤ) - K.vc.atoms.card + K.vc.numComponents := rfl
  rw [h2, K.vc_atoms_card, hF] at h
  rw [h]; simp; ring

/-- **`Δχ = -m` (L1798).** -/
theorem circuitRank_diff_card (hF : K.post.numComponents = M.numComponents)
    (hB : K.vc.bonds.card = 2 * (K.C.atoms.card - 1)) (hm : 1 ≤ K.C.atoms.card) :
    M.circuitRank - K.post.circuitRank = (K.C.atoms.card : ℤ) := by
  have h := K.circuitRank_diff
  have h2 : K.vc.circuitRank = (K.vc.bonds.card : ℤ) - K.vc.atoms.card + K.vc.numComponents := rfl
  rw [h2, K.vc_atoms_card, hB, hF] at h
  rw [h]
  have : ((2 * (K.C.atoms.card - 1) : ℕ) : ℤ) = 2 * (K.C.atoms.card : ℤ) - 2 := by
    push_cast [Nat.cast_sub hm]; ring
  rw [this]
  simp
  ring

end VineCut
end WaveTurbulence.FinalCount
