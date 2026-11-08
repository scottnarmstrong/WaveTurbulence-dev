/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK4
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedGapIndicator
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO (ruling R171): the gap product on dart labels with marked groups

`gapValue_eq_selDartsMk`: main's `gapValue_eq_selDarts` for every marked vine set `Mk` (the proof of
`splicedGapIndicator_eq_selOfMk` with `bondIndex G z` replaced by conserving dart labels `κ`).  Its statement is
B1b-3's hypothesis `GapValueSelDartsAt G σ Mk` (twist invariance of the gap profile), which the joint landing
discharges by `fun L γ η base c κ hκ hc0 zsb hlab => gapValue_eq_selDartsMk (Mole.garden_isMolecule G) σ L γ η base c
κ hκ hc0 zsb hlab`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1
  WaveTurbulence.LGSpine

variable {w : ℕ} {G : Garden w}

open scoped Classical in
/-- **Main's `gapValue_eq_selDarts` with marked groups** (R171; the dart-label form of
`splicedGapIndicator_eq_selOfMk`): the gap product of `gapSpecificationMk G σ Mk` on spliced labels pulled back from
original conserving dart labels `κ` is the indicator of `selDarts`.  Its statement is B1b-3's hypothesis
`GapValueSelDartsAt G σ Mk` (w/stage1mk, Vine/A/VineNormalizedGapIndicator), with `gapValueMk G σ Mk` unfolded to
`gapProduct (stSt G σ Mk).G (gapSpecificationMk G σ Mk)`. -/
theorem gapValue_eq_selDartsMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    {d : ℕ} (L γ η : ℝ) (base : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (zsb : GNode (stSt G σ Mk).G.tree → (Fin d → ℤ))
    (hlab : ∀ y, bondIndex (stSt G σ Mk).G zsb y = κ ((stSt G σ Mk).M.od y)) :
    gapProduct (stSt G σ Mk).G (gapSpecificationMk G σ Mk) L γ η base zsb =
      if selDarts (GroupPrescription.ofPrescription σ) L γ η base κ then 1 else 0 := by
  classical
  set Q : GBranch (stSt G σ Mk).G.tree → Prop := fun v => ∀ q, gapSpecificationMk G σ Mk v = some q →
        Molecule.gapKind L γ η ((base + latticePoint L (bondIndex (stSt G σ Mk).G zsb q.first)) -
          (base + latticePoint L (bondIndex (stSt G σ Mk).G zsb q.second))) = q.kind with hQ
  have hf : gapProduct (stSt G σ Mk).G (gapSpecificationMk G σ Mk) L γ η base zsb =
      if ∀ v, Q v then 1 else 0 := by
    unfold gapProduct
    have hb := Finset.prod_boole (M₀ := ℝ) (s := (Finset.univ : Finset (GBranch (stSt G σ Mk).G.tree)))
      (p := fun v => Q v)
    simp only [Finset.mem_univ, true_implies] at hb
    rw [← hb]
    refine Finset.prod_congr rfl fun v _ => ?_
    split
    next heq =>
      have hQv : Q v := fun q hq => by rw [heq] at hq; cases hq
      simp [hQv]
    next q heq =>
      have hiff : Q v ↔ Molecule.gapKind L γ η ((base + latticePoint L (bondIndex (stSt G σ Mk).G zsb q.first)) -
          (base + latticePoint L (bondIndex (stSt G σ Mk).G zsb q.second))) = q.kind := by
        constructor
        · intro h; exact h q heq
        · intro h q' hq'; rw [heq] at hq'; cases hq'; exact h
      simp only [hiff]
  rw [hf]
  have key : (∀ v, Q v) ↔ selDarts (GroupPrescription.ofPrescription σ) L γ η base κ := by
    constructor
    · intro hall
      unfold selDarts
      intro S
      by_cases hmk : markedGroup G Mk S.1
      · obtain ⟨t, -, ht⟩ := groupSurvMk_head hmk
        obtain ⟨O, hO, e, he, hind⟩ := gapSpecificationMk_marked_indicator_iff hM σ S.2 hmk ht L γ η base c _
          hκ hc0 (bondIndex (stSt G σ Mk).G zsb) hlab
        obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ η base κ hO
        exact hgk.trans ((hind k hk).mp (hall _ e he))
      · obtain ⟨a, O, -, hO, e, he, hind⟩ := gapSpecificationMk_indicator_iff hM σ S.2 hmk L γ η base c _
          hκ hc0 (bondIndex (stSt G σ Mk).G zsb) hlab
        obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ η base κ hO
        exact hgk.trans ((hind k hk).mp (hall _ e he))
    · intro hsel v q hq
      have hsome : (gapSpecificationMk G σ Mk v).isSome := by rw [hq]; rfl
      rcases gapSpecificationMk_isSome hM σ hsome with ⟨S, hS, hSv⟩ | ⟨S, t, hS, hSv⟩
      · obtain ⟨hnm, -, -, -, -⟩ := groupAtom_mem hM σ hSv
        obtain ⟨a, O, ha, hO, e, he, hind⟩ := gapSpecificationMk_indicator_iff hM σ hS hnm L γ η base c _
          hκ hc0 (bondIndex (stSt G σ Mk).G zsb) hlab
        have hat : groupAtom G σ S Mk = some ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) := by
          unfold groupAtom; rw [groupJoint_of_not_marked hnm, ha]; rfl
        rw [hat] at hSv
        cases hSv
        rw [he] at hq
        cases hq
        obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ η base κ hO
        exact (hind k hk).mpr (hgk.symm.trans (hsel ⟨S, hS⟩))
      · obtain ⟨hmk, ht, -⟩ := markedEntryAt_mem hM σ hSv
        obtain ⟨O, hO, e, he, hind⟩ := gapSpecificationMk_marked_indicator_iff hM σ hS hmk ht L γ η base c _
          hκ hc0 (bondIndex (stSt G σ Mk).G zsb) hlab
        obtain ⟨-, hvv⟩ := hSv
        subst hvv
        rw [he] at hq
        cases hq
        obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ η base κ hO
        exact (hind k hk).mpr (hgk.symm.trans (hsel ⟨S, hS⟩))
  simp only [key]

end WaveTurbulence.VineA.NormalizedSplice
