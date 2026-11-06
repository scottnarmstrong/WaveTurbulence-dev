/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedContractDifferences
public import WaveTurbulenceVineParam.VineParamRetainedRungPhases
public import WaveTurbulenceVineParam.VineParamRetainedCorePhases
public import WaveTurbulenceVineParam.VineParamSpliceBondCounts
public import WaveTurbulenceVineParam.VineParamSpliceCardinality
import Mathlib.Tactic

/-! # Exact full contract chart after one geometric rung insertion

This conditional composition helper is used by the expanded-template source
induction. Its geometric support premises must be proved by that induction.
-/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- Append the new ternary gap coefficients after all existing rung slots. -/
@[expose] def insertedZeta {m : ℕ} (ζ : Fin m → Fin 3 → ℤ) (a b : V) :
    Fin (m+1) → Fin 3 → ℤ :=
  Fin.lastCases (G.pattern.contractCorrection (G.gapSign a b)) ζ

/-- The old distinguished junction is never the newly appended doubled rung. -/
theorem map_junction_ne_last {m : ℕ} (j : Option (Fin m)) :
    Option.map Fin.castSucc j ≠ some (Fin.last m) := by
  cases j with
  | none => simp
  | some j =>
    intro h
    have hh := congrArg Fin.val (Option.some.inj h)
    change j.1=m at hh
    omega

/-- The full contract is stable under one actual source splice. No analytic
premise or assumed new chart occurs among the geometric induction inputs. -/
@[expose] noncomputable def insertedFullChart {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b)
    (hcap : P.CapSupported G.cap)
    (hpairs : ∀ j : Fin P.full.indexing.shape.m,
      (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ G.cap ↔
        (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ G.cap)
    (hbad : X.IsBad=true → G.gapSign a b ≠ 0) :
    FullVineChart (graphMolecule G.newEnds) X univ (.inl a) (.inl b) where
  indexing := G.insertedIndexing P.full.indexing hX ha hb
  bond_count := by
    have ho := Fintype.card_congr (graphBondEquiv G.ends)
    have hn := Fintype.card_congr (graphBondEquiv G.newEnds)
    simp only [Fintype.card_coe] at ho hn
    rw [← hn]
    apply spliceEdge_card_of_chart P.full.indexing.shape hX G.i G.j G.distinct
    exact ho.trans P.full.bond_count
  junction := Option.map Fin.castSucc P.full.junction
  junction_type := by
    cases h : P.full.junction <;> simpa only [h,Option.map,Option.isSome] using P.full.junction_type
  rung_bonds := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · erw [G.insertedIndexing_new_x,G.insertedIndexing_new_y,G.new_rung_bonds]
      erw [ite_eq_right (map_junction_ne_last P.full.junction)]
    · erw [G.insertedIndexing_old P.full.indexing hX ha hb _ _
        (slotInsertionEquiv_old_x P.full.indexing.shape hX j),
        G.insertedIndexing_old P.full.indexing hX ha hb _ _
        (slotInsertionEquiv_old_y P.full.indexing.shape hX j),
        G.old_pair_bonds_of_uniform _ _ (hpairs j),P.full.rung_bonds]
      congr 1
      apply propext
      cases P.full.junction with
      | none => constructor <;> intro h <;> cases h
      | some k =>
        constructor
        · intro h; exact congrArg (Option.map Fin.castSucc) h
        · intro h; exact congrArg some (Fin.castSucc_injective _ (Option.some.inj h))

  decodeFree := G.contractInsertedFree P.full hX (decide (b ∈ G.cap))
  decodeGap := G.contractInsertedGap P.full (decide (b ∈ G.cap))
  free_unit := G.contractInsertedFree_unit P.full hX (decide (b ∈ G.cap))
  chart := G.insertedContractChart P.full P.distinct hX ha hb (decide (b ∈ G.cap))
  decode_eq := G.contractInserted_decode_eq P.full P.distinct hX ha hb
    (decide (b ∈ G.cap)) P.reference_column
  difference := G.insertedContractChart_difference P hcap hX ha hb
  ζc := G.insertedZeta P.full.ζc a b
  ζ_unit := by
    intro j c
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [insertedZeta,Fin.lastCases_last]
      have h := G.pattern.contractCorrection_unit (G.gapSign a b) (G.gapSign_unit a b) c
      rcases mem_insert.mp h with h | h
      · exact Or.inr (Or.inr h)
      · rcases mem_insert.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (mem_singleton.mp h))
    · simpa only [insertedZeta,Fin.lastCases_castSucc] using P.full.ζ_unit j c
  ζ_bad_nonzero := by
    intro h j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [insertedZeta,Fin.lastCases_last] using G.pattern.contractCorrection_nonzero (G.gapSign a b) (G.gapSign_unit a b) (hbad h)
    · simpa only [insertedZeta,Fin.lastCases_castSucc] using P.full.ζ_bad_nonzero h j
  coreLinear := P.full.coreLinear
  coreFirstSign := P.full.coreFirstSign
  coreSign := P.full.coreSign
  ξc := P.full.ξc
  ξ_unit := P.full.ξ_unit
  joint_phase := G.insertedContractChart_joint_phase P.full P.distinct hX ha hb
  rung_t_phase := by
    intro d g r x j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [insertedZeta,Fin.lastCases_last] using G.insertedContractChart_t_phase P.full P.distinct hX ha hb (decide (b ∈ G.cap)) d g r x
    · simpa only [insertedZeta,Fin.lastCases_castSucc] using G.retained_t_phase P.full P.distinct hX ha hb (decide (b ∈ G.cap)) d g r x j
  rung_s_phase := by
    intro d g r x j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · exact G.insertedContractChart_s_phase P.full P.distinct hX ha hb (decide (b ∈ G.cap)) d g r x
    · exact G.retained_s_phase P.full P.distinct hX ha hb (decide (b ∈ G.cap)) d g r x j
  core_first_phase := G.retained_core_first_phase P.full P.distinct hX ha hb (decide (b ∈ G.cap))
  core_second_phase := G.retained_core_second_phase P.full P.distinct hX ha hb (decide (b ∈ G.cap))
  core_sum_phase := G.retained_core_sum_phase P.full P.distinct hX ha hb (decide (b ∈ G.cap))

end WaveTurbulence.Vine.Param.RungSpliceGeometry
