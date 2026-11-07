/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3EraseDev4
public import WaveTurbulence.Foundations.FinalCount.RemovalDev
/-! **FINALCOUNT-G3: `Δχ = c - deg v` and the erasure deviation of `𝔄`** (R27).

`c = F(M - v) - F(M) + 1` is the number of components of `M - v` that meet `v`.  With the count `𝔈(M) ≤ N 𝔈(M - v)`
(`G3EraseDev4`) and the ladder ratio `Λ` this gives
`𝔄(M) ≤ N · rankFactor(deg v - c) · Λ · 𝔄(M - v)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
variable {M : Molecule V D} {v : V}

/-- The number of components of `M - v` meeting `v`, as an integer: `F(M - v) - F(M) + 1`. -/
noncomputable def cEr (M : Molecule V D) (v : V) : ℤ := ((eraseAt M v).numComponents : ℤ) - M.numComponents + 1

theorem circuitRank_erase (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) :
    M.circuitRank = (eraseAt M v).circuitRank + (M.deg v : ℤ) - cEr M v := by
  have h1 := card_darts_eq_two_bonds M
  have h2 := card_darts_eq_two_bonds (eraseAt M v)
  have h3 := card_edart (M := M) (v := v) hnl
  have h4 : ((eraseAt M v).atoms.card : ℤ) + 1 = M.atoms.card := by
    show ((M.atoms.erase v).card : ℤ) + 1 = _
    rw [Finset.card_erase_of_mem hv]
    have : 1 ≤ M.atoms.card := Finset.card_pos.2 ⟨v, hv⟩
    omega
  unfold Molecule.circuitRank cEr
  have h5 : (M.bonds.card : ℤ) = (eraseAt M v).bonds.card + M.deg v := by
    have : (Fintype.card (EDart M v) : ℤ) + 2 * M.deg v = Fintype.card D := by exact_mod_cast h3
    have h2' : (Fintype.card (EDart M v) : ℤ) = 2 * (eraseAt M v).bonds.card := by exact_mod_cast h2
    have h1' : (Fintype.card D : ℤ) = 2 * M.bonds.card := by exact_mod_cast h1
    omega
  omega

theorem cEr_pos (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) (hd : 1 ≤ M.deg v) : 1 ≤ cEr M v := by
  have := numComponents_le_erase hnl hv hd
  unfold cEr; omega

theorem cEr_le_card (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) : cEr M v ≤ (Cs M v).card := by
  have := numComponents_erase_le hnl hv
  unfold cEr; omega

theorem cEr_le_deg (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) : cEr M v ≤ M.deg v :=
  (cEr_le_card hnl hv).trans (by exact_mod_cast cs_card_le_deg hnl hv)

/-- **The deviation of an erasure of `𝔄`.** -/
theorem erase0_isDeviation {L γ δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C₁) {w : Mom d}
    (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (EDart M v → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (hX : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (P S)) (Nn : ℕ∞) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hE : M.countE L γ δ w Adm ≤ Nn * (eraseAt M v).countE L γ δ w Adm')
    (hlad : ∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S ≤
      Λ * ∏ S ∈ (eraseAt M v).maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((eraseAt M v).countA L γ δ C₁ w Adm' P)
      ((Nn : ℝ≥0∞) * ENNReal.ofReal (rankFactor d L γ δ C₁ ((M.deg v : ℤ) - cEr M v) * Λ)) := by
  rw [countA_eq, countA_eq]
  have hrk := circuitRank_erase hnl hv
  have hrf : rankFactor d L γ δ C₁ M.circuitRank = rankFactor d L γ δ C₁ (eraseAt M v).circuitRank *
      rankFactor d L γ δ C₁ ((M.deg v : ℤ) - cEr M v) := by
    rw [← rankFactor_add d hL hδ hC.ne', hrk]; congr 1; ring
  have hnn : 0 ≤ rankFactor d L γ δ C₁ ((M.deg v : ℤ) - cEr M v) * Λ :=
    mul_nonneg (rankFactor_nonneg d (γ := γ) hL.le hδ.le hC.le _) hΛ
  refine countA_dev_of_parts _ _ _ _ Nn _ hnn hE ?_
  rw [hrf]
  have hrn := rankFactor_nonneg d (γ := γ) hL.le hδ.le hC.le (eraseAt M v).circuitRank
  have hrn2 := rankFactor_nonneg d (γ := γ) hL.le hδ.le hC.le ((M.deg v : ℤ) - cEr M v)
  calc _ ≤ rankFactor d L γ δ C₁ (eraseAt M v).circuitRank * rankFactor d L γ δ C₁ ((M.deg v : ℤ) - cEr M v) *
          (Λ * ∏ S ∈ (eraseAt M v).maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) := by
        gcongr
    _ = _ := by ring

end WaveTurbulence.FinalCountG3
