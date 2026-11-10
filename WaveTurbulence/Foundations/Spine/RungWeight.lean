/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.AtomSlots
public import WaveTurbulence.Foundations.Spine.AtomWeight
public import WaveTurbulence.Foundations.Spine.FibreGarden
/-! # The weight of an interior rung in chart coordinates (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Finset

variable {n d : ℕ}

/-- Per-slot constant shifts at the `v` atom of rung `i`. -/
def csv (S : ChainSigns n) (i : Fin n) (q : Fin d → ℤ) : Fin 4 → (Fin d → ℤ) :=
  ![0, 0, S.epsF i.castSucc • q, S.epsF i.succ • q]

lemma inv_vSlot (S : ChainSigns n) (a0 b0 : Fin d → ℤ) (P : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (i : Fin n) (s : Fin 4) :
    (S.inv a0 b0 P).vSlot i s = S.railU a0 P i.castSucc + S.tau P i 2 - S.tau P i s -
      csv S i (a0 - b0) s := by
  fin_cases s
  · simp [ChainLab.vSlot, ChainSigns.inv, ChainSigns.rungSlot, csv]
  · simp [ChainLab.vSlot, ChainSigns.inv, ChainSigns.rungSlot, csv]
  · simp [ChainLab.vSlot, ChainSigns.inv, csv]
  · simp [ChainLab.vSlot, ChainSigns.inv, csv, ChainSigns.railU_succ]; abel

/-- The gap indicator at an atom, from the slot labels. -/
noncomputable def gapFactor (L γ η : ℝ) (base : Mom d) (labs : Fin 4 → (Fin d → ℤ))
    (gap : Option (Fin 4 × Fin 4 × Molecule.GapKind)) : ℝ :=
  match gap with
  | none => 1
  | some g => if Molecule.gapKind L γ η (base + latticePoint L (labs g.1) -
      (base + latticePoint L (labs g.2.1))) = g.2.2 then 1 else 0

/-- Anchors cancel in the epsilon and gap factors. -/
lemma atom_factor_eq (L γ η : ℝ) (base : Mom d) (labs rel : Fin 4 → (Fin d → ℤ)) (A : Fin d → ℤ)
    (h : ∀ s, labs s = A + rel s) (k : Fin 3 → Fin 4) (S : ChainSigns n) (i : Fin n)
    (cs : Fin 4 → (Fin d → ℤ)) (p : Pt d) (hrel : ∀ s, rel s = relLab S i cs s p)
    (gap : Option (Fin 4 × Fin 4 × Molecule.GapKind)) :
    epsCoef (labs (k 0)) (labs (k 1)) (labs (k 2)) * gapFactor L γ η base labs gap =
      epsCoef (relLab S i cs (k 0) p) (relLab S i cs (k 1) p) (relLab S i cs (k 2) p) *
        gapW L γ η S i cs gap p := by
  have e : ∀ s, labs s = relLab S i cs s p + A := fun s => by rw [h, hrel, add_comm]
  simp only [e]
  rw [epsCoef_translate]
  congr 1
  rcases gap with _ | ⟨kf, ks, kd⟩
  · rfl
  · simp only [gapFactor, gapW]
    have : base + latticePoint L (labs kf) - (base + latticePoint L (labs ks)) =
        latticePoint L (relLab S i cs kf p - relLab S i cs ks p) := by
      rw [e kf, e ks]; ext j; simp [latticePoint, add_div, sub_div]
    rw [this]

end WaveTurbulence.LadderDecay
