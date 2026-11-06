/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Molecule.GardenIncidence
/-! All source gap classifications are encoded by at most sixteen local dart pairs per atom.
This is the finite exponential source-choice carrier, independent of momentum values. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset
open scoped Classical

/-- The three source gap tags, with an explicit finite encoding. -/
def sourceGapKindEquiv : Molecule.GapKind ≃ Fin 3 where
  toFun | .ZG => 0 | .SG => 1 | .LG => 2
  invFun i := if i = 0 then .ZG else if i = 1 then .SG else .LG
  left_inv k := by cases k <;> rfl
  right_inv i := by fin_cases i <;> rfl

noncomputable instance instFintypeSourceGapKind : Fintype Molecule.GapKind :=
  Fintype.ofEquiv (Fin 3) sourceGapKindEquiv.symm

 theorem card_sourceGapKind : Fintype.card Molecule.GapKind = 3 :=
  (Fintype.card_congr sourceGapKindEquiv).trans (Fintype.card_fin 3)

abbrev SourceAtomPair {w : ℕ} (G : Garden w) :=
  Σ v : GBranch G.tree, ({x : GardenDart G // x ∈ G.molecule.dartsAt v} ×
    {y : GardenDart G // y ∈ G.molecule.dartsAt v})

 theorem card_sourceAtomPair_le {w : ℕ} (G : Garden w) :
    Fintype.card (SourceAtomPair G) ≤ 16 * G.order := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_coe]
  calc
    _ ≤ ∑ _v : GBranch G.tree, 16 := by
      apply sum_le_sum
      intro v _
      have hh := WaveTurbulence.Mole.garden_molecule_deg_le_four G v
      change (G.molecule.dartsAt v).card ≤ 4 at hh
      nlinarith
    _ = _ := by
      simp only [sum_const, card_univ, smul_eq_mul, card_gbranch]
      exact Nat.mul_comm _ _

noncomputable def sourceGapTable {w d : ℕ} (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) : SourceAtomPair G → Molecule.GapKind :=
  fun a => Molecule.gapKind L γ η (Molecule.gapAt L base κ a.2.1.1 a.2.2.1)

 theorem sourceGapTable_eq_apply {w d : ℕ} (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (κ κ' : GardenDart G → (Fin d → ℤ))
    (h : sourceGapTable G L γ η base κ = sourceGapTable G L γ η base κ')
    (x y : GardenDart G) (hxy : G.molecule.atom x = G.molecule.atom y) :
    Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) =
      Molecule.gapKind L γ η (Molecule.gapAt L base κ' x y) := by
  have hx : x ∈ G.molecule.dartsAt (G.molecule.atom x) := by
    exact (Mole.mem_dartsAt G.molecule _ x).mpr rfl
  have hy : y ∈ G.molecule.dartsAt (G.molecule.atom x) :=
    (Mole.mem_dartsAt G.molecule _ y).mpr hxy.symm
  exact congrFun h ⟨G.molecule.atom x, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩⟩

 theorem card_sourceGapTables_le {w : ℕ} (G : Garden w) :
    Fintype.card (SourceAtomPair G → Molecule.GapKind) ≤ (3 ^ 16) ^ G.order := by
  rw [Fintype.card_fun, card_sourceGapKind, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (card_sourceAtomPair_le G)

end WaveTurbulence.LGSpine
