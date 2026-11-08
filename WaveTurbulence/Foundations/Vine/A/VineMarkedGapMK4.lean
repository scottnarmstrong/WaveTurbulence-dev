/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK3
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO (ruling R171): the spliced gap indicator with marked groups

`splicedGapIndicator_eq_selOfMk`: main's `splicedGapIndicator_eq_selOf` for every marked vine set `Mk`.  With R171's
marked branch of `gapSpecificationMk`, every group of `𝒞` (marked or not) has its factor in the indicator, so the
indicator is again the indicator of the `σ`-restriction `selOf` (o75 (2.3); TARGET L1950, L1956).  Without the marked
entries the statement is false (a marked SG group with an LG gap is not checked by the indicator).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1
  WaveTurbulence.LGSpine

variable {w : ℕ} {G : Garden w}

open scoped Classical in
/-- **`splicedGapIndicator_eq_selOf` with marked groups** (R171). -/
theorem splicedGapIndicator_eq_selOfMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    {d : ℕ} (L γ η : ℝ) (base : Mom d) (c : GBranch G.tree → Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c (bondIndex G z))
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (zsb : GNode (stSt G σ Mk).G.tree → (Fin d → ℤ))
    (hlab : ∀ y, bondIndex (stSt G σ Mk).G zsb y = bondIndex G z ((stSt G σ Mk).M.od y))
    (D : SplicedKernelData (stSt G σ Mk).G d) (hD : D.gapSpecification = gapSpecificationMk G σ Mk) :
    splicedGapIndicator (stSt G σ Mk).G D L γ η base zsb =
      if selOf (GroupPrescription.ofPrescription σ) L γ η base z then 1 else 0 := by
  classical
  set Q : GBranch (stSt G σ Mk).G.tree → Prop := fun v => ∀ q, gapSpecificationMk G σ Mk v = some q →
        Molecule.gapKind L γ η ((base + latticePoint L (bondIndex (stSt G σ Mk).G zsb q.first)) -
          (base + latticePoint L (bondIndex (stSt G σ Mk).G zsb q.second))) = q.kind with hQ
  have hf : splicedGapIndicator (stSt G σ Mk).G D L γ η base zsb = if ∀ v, Q v then 1 else 0 := by
    unfold splicedGapIndicator
    rw [hD]
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
  have key : (∀ v, Q v) ↔ selOf (GroupPrescription.ofPrescription σ) L γ η base z := by
    constructor
    · intro hall
      unfold selOf
      intro S
      by_cases hmk : markedGroup G Mk S.1
      · obtain ⟨v, O, -, hO, e, he, hind⟩ := gapSpecificationMk_marked_indicator_iff hM σ S.2 hmk L γ η base c _
          hκ hc0 (bondIndex (stSt G σ Mk).G zsb) hlab
        obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ η base (bondIndex G z) hO
        exact hgk.trans ((hind k hk).mp (hall _ e he))
      · obtain ⟨a, O, -, hO, e, he, hind⟩ := gapSpecificationMk_indicator_iff hM σ S.2 hmk L γ η base c _
          hκ hc0 (bondIndex (stSt G σ Mk).G zsb) hlab
        obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ η base (bondIndex G z) hO
        exact hgk.trans ((hind k hk).mp (hall _ e he))
    · intro hsel v q hq
      have hsome : (gapSpecificationMk G σ Mk v).isSome := by rw [hq]; rfl
      rcases gapSpecificationMk_isSome hM σ hsome with ⟨S, hS, hSv⟩ | ⟨S, hS, hSv⟩
      · obtain ⟨hnm, -, -, -, -⟩ := groupAtom_mem hM σ hSv
        obtain ⟨a, O, ha, hO, e, he, hind⟩ := gapSpecificationMk_indicator_iff hM σ hS hnm L γ η base c _
          hκ hc0 (bondIndex (stSt G σ Mk).G zsb) hlab
        have hat : groupAtom G σ S Mk = some ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) := by
          unfold groupAtom; rw [groupJoint_of_not_marked hnm, ha]; rfl
        rw [hat] at hSv
        cases hSv
        rw [he] at hq
        cases hq
        obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ η base (bondIndex G z) hO
        exact (hind k hk).mpr (hgk.symm.trans (hsel ⟨S, hS⟩))
      · obtain ⟨hmk, -⟩ := markedAtom_mem hM σ hSv
        obtain ⟨v', O, hv', hO, e, he, hind⟩ := gapSpecificationMk_marked_indicator_iff hM σ hS hmk L γ η base c _
          hκ hc0 (bondIndex (stSt G σ Mk).G zsb) hlab
        rw [hv'] at hSv
        cases hSv
        rw [he] at hq
        cases hq
        obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ η base (bondIndex G z) hO
        exact (hind k hk).mpr (hgk.symm.trans (hsel ⟨S, hS⟩))
  simp only [key]

open scoped Classical in
/-- `splicedGapIndicator_eq_selOfMk` for a garden decoration `z` with root values `roots` of a plain garden. -/
theorem splicedGapIndicator_eq_selOf_genMk (hM : G.molecule.IsMolecule) (hp : G.IsPlain) (σ : Prescription G)
    {Mk : Set (CLVine G)} {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) (zsb : GNode (stSt G σ Mk).G.tree → (Fin d → ℤ))
    (hlab : ∀ y, bondIndex (stSt G σ Mk).G zsb y = bondIndex G z.1 ((stSt G σ Mk).M.od y))
    (D : SplicedKernelData (stSt G σ Mk).G d) (hD : D.gapSpecification = gapSpecificationMk G σ Mk) :
    splicedGapIndicator (stSt G σ Mk).G D L γ η base zsb =
      if selOf (GroupPrescription.ofPrescription σ) L γ η base z.1 then 1 else 0 :=
  splicedGapIndicator_eq_selOfMk hM σ L γ η base _ z.1 (spliced_molecule_decoration G hp hL base roots z)
    (fun v _ hv => gardenSource_eq_zero_of_deg_four G hp _ v hv) zsb hlab D hD

end WaveTurbulence.VineA.NormalizedSplice
