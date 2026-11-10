/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerIndex

/-!
# X2E-3, step 7: the moment expansion at fixed flower trees, as gate kernels

`gateSummand`: the summand of B1.12's `flowerSumP` (constant pattern, constant `†` labels). `CutWeightsOK`: the
cutoff weights of a flower graft are the products of the tree cutoff weights (void without cutoffs).

**Statements** (non-trivial flower trees `tops` of flower sign `ζ`, patterns `plain`/`dRoot`, `p ≤ s, t`):
- `gateSummand_flowerGraft`: the gate summand of the flower graft of `x : FlowerAt` is
  `∑'_{kt} (∏_j σ_j fkCoef_j) ∏_B 𝕂_B`.
- `sum_gateSummand_mk`: for a partition `P` with the pair blocks, the sum over the lower-data families of the gate
  summands is X2E-1's `∑'_κ flowerKerIntegrand` at `Q = P ∖ pair blocks`.
- `sum_flowerKer_eq_sum_gate`: X2E-1's `∑_Q ∑'_κ flowerKerIntegrand` is the sum of the gate summands over the
  partitions with pair blocks and the lower-data families.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct SysAPI Cpl
open scoped Classical

variable (L γ δ : ℝ) {d : ℕ}

/-- **The summand of `flowerSumP`** with constant pattern `pat` and constant `†` labels. -/
noncomputable def gateSummand (F : ℕ → Mom d → ℝ) (p : ℕ) (pat : FixPat) (dagger : Option (Fin 3 → Mom d))
    (cut1 cut2 : Option ℕ) (t s : ℝ) (n n' : Fin d → ℤ) {w : ℕ} (LG : LayeredGarden w) : ℂ :=
  kernelKgen L γ δ F LG (LG.fixPat (fun _ => pat) t s)
    (if (dagger.map fun c (_ : Fin w) => c).isSome then univ.filter LG.garden.IsFlowerParent else ∅)
    (fun k => (cut1.elim 1 fun j₁ => LG.cutWeight1P p L j₁ k) * (cut2.elim 1 fun j₂ => LG.cutWeight2P L j₂ k) *
      ((dagger.map fun c (_ : Fin w) => c).elim 1 fun c => LG.sibWeight c k))
    (fun _ => t) 0 (fun _ => n) n'

section Datum

variable {Pm p : ℕ} {ζ : ℤˣ} {tops : Fin (2 * Pm) → FTree} (hF : ∀ j, tops j ≠ FTree.flower)
  (x : FlowerAt Pm p tops) (hsign : ∀ j, (tops j).sign = ζ)

/-- The cutoff weights of the flower graft are the products of the tree cutoff weights. -/
def CutWeightsOK (cut1 cut2 : Option ℕ) : Prop :=
  (∀ j₁ ∈ cut1, ∀ k : GNode (x.toData hsign).flowerGraft.garden.tree → Mom d,
    (x.toData hsign).flowerGraft.cutWeight1P p L j₁ k =
      ∏ j, treeCut1K L (tops j) j₁ (fun a => k (topNodeEmbedding (ftop tops) x.partition
        (fun B => ((x.toData hsign).lowFl B).garden) (singleNodeToForest (ftop tops) j a)))) ∧
  (∀ j₂ ∈ cut2, ∀ k : GNode (x.toData hsign).flowerGraft.garden.tree → Mom d,
    (x.toData hsign).flowerGraft.cutWeight2P L j₂ k =
      ∏ j, treeCut2K L (tops j) (hF j) j₂ (fun a => k (topNodeEmbedding (ftop tops) x.partition
        (fun B => ((x.toData hsign).lowFl B).garden) (singleNodeToForest (ftop tops) j a))))

/-- **The gate summand of a flower graft.** -/
theorem gateSummand_flowerGraft (F : ℕ → Mom d → ℝ)
    (hFs : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|)
    (pat : FixPat) (hpat : pat = .plain ∨ pat = .dRoot) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ)
    (hcut : CutWeightsOK L (d := d) hF x hsign cut1 cut2) {t s : ℝ} (hpt : (p : ℝ) ≤ t) (hps : (p : ℝ) ≤ s)
    (n n' : Fin d → ℤ) :
    gateSummand L γ δ F p pat dagger cut1 cut2 t s n n' (x.toData hsign).flowerGraft =
      ∑' kt : ForestDecoration (ftop tops) d (fun _ => n),
        (∏ j, zpowSign (altFlowerSig Pm j) (fkCoef L γ δ p pat dagger cut1 cut2 t s (tops j)
          (fun a => kt.1 (singleNodeToForest (ftop tops) j a)))) *
        ∏ B : x.partition.parts, kernelK L γ δ F ((x.toData hsign).lowFl B) (fun _ => p) s 0
          (fun k => kt.1 ((blockRootEquiv (ftop tops) x.partition).symm ⟨B, k⟩).toNode) n' := by
  unfold gateSummand
  rw [Option.isSome_map]
  exact kernelKgen_flowerGraft L γ δ hF x hsign F hFs pat hpat dagger cut1 cut2 _
    (gateWeight_eq L hF x hsign dagger cut1 cut2 hcut.1 hcut.2) hpt hps n n'

include hF in
/-- The series of `gateSummand_flowerGraft` is summable. -/
theorem summable_flowerGraft_series (F : ℕ → Mom d → ℝ)
    (hFs : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|)
    (pat : FixPat) (hpat : pat = .plain ∨ pat = .dRoot) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ)
    {t s : ℝ} (hpt : (p : ℝ) ≤ t) (hps : (p : ℝ) ≤ s) (n n' : Fin d → ℤ) :
    Summable fun kt : ForestDecoration (ftop tops) d (fun _ => n) =>
      (∏ j, zpowSign (altFlowerSig Pm j) (fkCoef L γ δ p pat dagger cut1 cut2 t s (tops j)
          (fun a => kt.1 (singleNodeToForest (ftop tops) j a)))) *
        ∏ B : x.partition.parts, kernelK L γ δ F ((x.toData hsign).lowFl B) (fun _ => p) s 0
          (fun k => kt.1 ((blockRootEquiv (ftop tops) x.partition).symm ⟨B, k⟩).toNode) n' := by
  have hfixv : ∀ b v, fixFl tops hF pat t s b = some v → (p : ℝ) ≤ v :=
    fun b v h => treeFixPat_ge (hF b.1.1) hpat hpt hps h
  have hF' : ∀ q, Summable fun m : Fin d → ℤ => |F q ((0 : Mom d) + latticePoint L m)| := by
    simpa only [zero_add] using hFs
  have hs := GraftGen.summable_kernelKgen_graft_series L γ δ (sig := altFlowerSig Pm) (top := ftop tops)
    (P := x.partition) (low := (x.toData hsign).lowFl) (p := p) (hsig := (x.toData hsign).lowFl_sig)
    (hbound := (x.toData hsign).lowFl_bound) F
    (x.toData hsign).lowFl_branch_layer_lt (x.toData hsign).lowFl_mark_ne_lower
    (x.toData hsign).lowFl_not_isFlowerParent
    _ (fixFl tops hF pat t s)
    (fixPat_top hF x hsign pat hpat t s) (fun z => fixPat_lower hF x hsign pat hpat t s z.1 z.2) hfixv
    _ (offFl tops hF dagger) (off_top hF x hsign dagger) (fun z => off_lower x hsign dagger z.1 z.2)
    (wtopFl tops hF L dagger cut1 cut2) (abs_wtopFl_le_one L tops hF dagger cut1 cut2) t s hpt 0 (fun _ => n) n' hF'
  refine (hs.mul_left ((coupling d L γ δ : ℂ) ^ (∑ j, (ftop tops j).order) *
    ∏ b : GBranch (ftop tops), Complex.I * (((nodeSign (altFlowerSig Pm) b.toNode.1 : ℤˣ) : ℤ) : ℂ))).congr
      fun kt => ?_
  rw [← mul_assoc, prefactor_mul_topGenFactor_flower L γ δ p pat dagger cut1 cut2 t s tops hF (altFlowerSig Pm) kt]

end Datum

/-! ## Fixed flower trees -/

section Tops

variable {Pm p : ℕ} (Natt : ℕ) {ζ : ℤˣ} {tops : Fin (2 * Pm) → FTree} (hF : ∀ j, tops j ≠ FTree.flower)
  (hsign : ∀ j, (tops j).sign = ζ)

/-- The block factor on a finite set of leaves: on a pair block, the indicator of the flower label; otherwise the
lower kernel sum. -/
noncomputable def blockFactor (F : ℕ → Mom d → ℝ) (n' : Fin d → ℤ) (kt : GNode (ftop tops) → (Fin d → ℤ))
    (B : Finset (GLeaf (ftop tops))) : ℂ :=
  if B ∈ pairSet tops then (if ∀ k : Fin B.card, kt (B.equivFin.symm k).1.toNode = n' then 1 else 0) else
    lowerKernelSum L γ δ F (fun k => nodeSign (altFlowerSig Pm) (B.equivFin.symm k).1.1) p Natt
      (fun k => kt (B.equivFin.symm k).1.toNode)

omit hF in
include hsign in
theorem kernelK_lowFl_mk (P : Finpartition (univ : Finset (GLeaf (ftop tops)))) (hP : ∀ j, pbF tops j ∈ P.parts)
    (fam : (B : P.parts) → LowerGraftData (sigP tops P B) p Natt) (F : ℕ → Mom d → ℝ) (s : ℝ) (n' : Fin d → ℤ)
    (B : P.parts) (kt : GNode (ftop tops) → (Fin d → ℤ)) :
    kernelK L γ δ F (((mkFlowerAt P hP fam).toData hsign).lowFl B) (fun _ => p) s 0
        (fun k => kt ((blockRootEquiv (ftop tops) P).symm ⟨B, k⟩).toNode) n' =
      if B.1 ∈ pairSet tops then (if ∀ k : Fin B.1.card, kt (B.1.equivFin.symm k).1.toNode = n' then 1 else 0)
      else KG L γ δ F (fam B).low p (fun k => kt ((blockRootEquiv (ftop tops) P).symm ⟨B, k⟩).toNode) := by
  by_cases hB : B.1 ∈ pairSet tops
  · have hPB : ((mkFlowerAt P hP fam).toData hsign).IsPairBlock B.1 := by
      obtain ⟨j, -, hj⟩ := mem_image.mp hB
      exact ⟨j, hj.symm⟩
    rw [FlowerGraftData.kernelK_lowFl_pair L γ δ _ F hPB (p : ℝ) s 0 _ n', ite_eq_left hB]
    rfl
  · have hPB : ¬ ((mkFlowerAt P hP fam).toData hsign).IsPairBlock B.1 := by
      rintro ⟨j, hj⟩
      exact hB (hj ▸ pbF_mem_pairSet tops j)
    rw [FlowerGraftData.kernelK_lowFl_of_not L γ δ _ F hPB (p : ℝ) s _ n', ite_eq_right hB]
    rfl

omit hF hsign in
theorem prod_pairSet_indicator (kt : GNode (ftop tops) → (Fin d → ℤ)) (n' : Fin d → ℤ) :
    ∏ B ∈ pairSet tops, (if ∀ k : Fin B.card, kt (B.equivFin.symm k).1.toNode = n' then (1 : ℂ) else 0) =
      if ∀ j, kt (flowerAt tops j).toNode = n' then 1 else 0 := by
  by_cases h : ∀ j, kt (flowerAt tops j).toNode = n'
  · rw [ite_eq_left h]
    refine prod_eq_one fun B hB => ?_
    obtain ⟨j', -, rfl⟩ := mem_image.mp hB
    refine ite_eq_left fun k => ?_
    rcases (mem_pbF tops j' _).mp ((pbF tops j').equivFin.symm k).2 with h' | h'
    · rw [h']
      exact h j'
    · rw [h']
      exact h _
  · rw [ite_eq_right h]
    simp only [not_forall] at h
    obtain ⟨j, hj⟩ := h
    refine prod_eq_zero (pbF_mem_pairSet tops j) (ite_eq_right fun hall => hj ?_)
    have hk := hall ((pbF tops j).equivFin ⟨flowerAt tops j, flowerAt_mem_pbF tops j⟩)
    rwa [Equiv.symm_apply_apply] at hk

include hF hsign in
/-- **The lower-data families at a partition with pair blocks.** -/
theorem sum_gateSummand_mk (P : Finpartition (univ : Finset (GLeaf (ftop tops)))) (hP : ∀ j, pbF tops j ∈ P.parts)
    (F : ℕ → Mom d → ℝ) (hFs : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|)
    (pat : FixPat) (hpat : pat = .plain ∨ pat = .dRoot) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ)
    (hcut : ∀ fam : (B : P.parts) → LowerGraftData (sigP tops P B) p Natt,
      CutWeightsOK L (d := d) hF (mkFlowerAt P hP fam) hsign cut1 cut2)
    {t s : ℝ} (hpt : (p : ℝ) ≤ t) (hps : (p : ℝ) ≤ s) (n n' : Fin d → ℤ) :
    ∑ fam : (B : P.parts) → LowerGraftData (sigP tops P B) p Natt,
        gateSummand L γ δ F p pat dagger cut1 cut2 t s n n' ((mkFlowerAt P hP fam).toData hsign).flowerGraft =
      ∑' κ : FlowerForestDec tops d (fun _ => n) (fun _ => n'),
        flowerKerIntegrand L γ δ F (altFlowerSig Pm) tops (fun j => fkCoef L γ δ p pat dagger cut1 cut2 t s (tops j))
          (dropPairs tops P hP) p Natt κ := by
  let c := fun kt : ForestDecoration (ftop tops) d (fun _ => n) => ∏ j, zpowSign (altFlowerSig Pm j)
    (fkCoef L γ δ p pat dagger cut1 cut2 t s (tops j) (fun a => kt.1 (singleNodeToForest (ftop tops) j a)))
  let g := fun (B : P.parts) (D : LowerGraftData (sigP tops P B) p Natt)
      (kt : ForestDecoration (ftop tops) d (fun _ => n)) =>
    if B.1 ∈ pairSet tops then (if ∀ k : Fin B.1.card, kt.1 (B.1.equivFin.symm k).1.toNode = n' then (1 : ℂ) else 0)
    else KG L γ δ F D.low p (fun k => kt.1 ((blockRootEquiv (ftop tops) P).symm ⟨B, k⟩).toNode)
  have hrw : ∀ (fam : (B : P.parts) → LowerGraftData (sigP tops P B) p Natt)
      (kt : ForestDecoration (ftop tops) d (fun _ => n)),
      c kt * ∏ B : P.parts, kernelK L γ δ F (((mkFlowerAt P hP fam).toData hsign).lowFl B) (fun _ => p) s 0
        (fun k => kt.1 ((blockRootEquiv (ftop tops) P).symm ⟨B, k⟩).toNode) n' = c kt * ∏ B, g B (fam B) kt :=
    fun fam kt => congrArg (c kt * ·) (prod_congr rfl fun B _ =>
      kernelK_lowFl_mk L γ δ Natt hsign P hP fam F s n' B kt.1)
  have hk : ∀ fam : (B : P.parts) → LowerGraftData (sigP tops P B) p Natt,
      gateSummand L γ δ F p pat dagger cut1 cut2 t s n n' ((mkFlowerAt P hP fam).toData hsign).flowerGraft =
        ∑' kt, c kt * ∏ B, g B (fam B) kt := fun fam =>
    (gateSummand_flowerGraft L γ δ hF (mkFlowerAt P hP fam) hsign F hFs pat hpat dagger cut1 cut2 (hcut fam)
      hpt hps n n').trans (tsum_congr (hrw fam))
  have hs : ∀ fam : (B : P.parts) → LowerGraftData (sigP tops P B) p Natt,
      Summable fun kt => c kt * ∏ B, g B (fam B) kt := fun fam =>
    (summable_flowerGraft_series L γ δ hF (mkFlowerAt P hP fam) hsign F hFs pat hpat dagger cut1 cut2 hpt hps n
      n').congr (hrw fam)
  rw [sum_congr rfl fun fam _ => hk fam, ← Summable.tsum_finsetSum fun fam _ => hs fam]
  -- the inner finite sum
  have hinner : ∀ kt : ForestDecoration (ftop tops) d (fun _ => n),
      ∑ fam : (B : P.parts) → LowerGraftData (sigP tops P B) p Natt, c kt * ∏ B, g B (fam B) kt =
        c kt * ((if ∀ j, kt.1 (flowerAt tops j).toNode = n' then 1 else 0) *
          ∏ B ∈ P.parts \ pairSet tops,
            lowerKernelSum L γ δ F (fun k => nodeSign (altFlowerSig Pm) (B.equivFin.symm k).1.1) p Natt
            (fun k => kt.1 (B.equivFin.symm k).1.toNode)) := by
    intro kt
    rw [← mul_sum, (Fintype.prod_sum (fun B D => g B D kt)).symm]
    congr 1
    have hB : ∀ B : P.parts, ∑ D : LowerGraftData (sigP tops P B) p Natt, g B D kt =
        blockFactor L γ δ (p := p) Natt F n' kt.1 B.1 := by
      intro B
      by_cases hB : B.1 ∈ pairSet tops
      · obtain ⟨u⟩ := lowerData_unique_of_pair hsign P B hB p Natt
        rw [Fintype.sum_unique]
        unfold blockFactor
        simp only [g, hB, ite_true]
      · unfold blockFactor
        simp only [g, hB, ite_false]
        rfl
    rw [prod_congr rfl fun B _ => hB B, prod_coe_sort P.parts (blockFactor L γ δ (p := p) Natt F n' kt.1)]
    unfold blockFactor
    rw [prod_ite, filter_mem_eq_inter, inter_eq_right.mpr (pairSet_subset tops P hP), filter_notMem_eq_sdiff,
      prod_pairSet_indicator]
  rw [tsum_congr hinner]
  -- restrict to the flower decorations
  let S := {kt : ForestDecoration (ftop tops) d (fun _ => n) | ∀ j, kt.1 (flowerAt tops j).toNode = n'}
  let f := fun kt : ForestDecoration (ftop tops) d (fun _ => n) => c kt * ∏ B ∈ P.parts \ pairSet tops,
    lowerKernelSum L γ δ F (fun k => nodeSign (altFlowerSig Pm) (B.equivFin.symm k).1.1) p Natt
      (fun k => kt.1 (B.equivFin.symm k).1.toNode)
  have hfin : ∑' κ : FlowerForestDec tops d (fun _ => n) (fun _ => n'),
      flowerKerIntegrand L γ δ F (altFlowerSig Pm) tops (fun j => fkCoef L γ δ p pat dagger cut1 cut2 t s (tops j))
        (dropPairs tops P hP) p Natt κ = ∑' x : S, f x := rfl
  rw [hfin, tsum_subtype S f]
  refine tsum_congr fun kt => ?_
  rw [Set.indicator_apply]
  by_cases hkt : ∀ j, kt.1 (flowerAt tops j).toNode = n'
  · rw [ite_eq_left hkt, one_mul, ite_eq_left (show kt ∈ S from hkt)]
  · rw [ite_eq_right hkt, zero_mul, mul_zero, ite_eq_right (show kt ∉ S from hkt)]

include hF hsign in
/-- **The moment expansion at fixed flower trees, as gate kernels.** -/
theorem sum_flowerKer_eq_sum_gate (F : ℕ → Mom d → ℝ)
    (hFs : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|)
    (pat : FixPat) (hpat : pat = .plain ∨ pat = .dRoot) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ)
    (hcut : ∀ (P : Finpartition (univ : Finset (GLeaf (ftop tops)))) (hP : ∀ j, pbF tops j ∈ P.parts)
      (fam : (B : P.parts) → LowerGraftData (sigP tops P B) p Natt),
      CutWeightsOK L (d := d) hF (mkFlowerAt P hP fam) hsign cut1 cut2)
    {t s : ℝ} (hpt : (p : ℝ) ≤ t) (hps : (p : ℝ) ≤ s) (n n' : Fin d → ℤ) :
    ∑ Q : Finpartition (nfLeaves tops), ∑' κ : FlowerForestDec tops d (fun _ => n) (fun _ => n'),
        flowerKerIntegrand L γ δ F (altFlowerSig Pm) tops (fun j => fkCoef L γ δ p pat dagger cut1 cut2 t s (tops j))
          Q p Natt κ =
      ∑ P : {P : Finpartition (univ : Finset (GLeaf (ftop tops))) // ∀ j, pbF tops j ∈ P.parts},
        ∑ fam : (B : P.1.parts) → LowerGraftData (sigP tops P.1 B) p Natt,
          gateSummand L γ δ F p pat dagger cut1 cut2 t s n n' ((mkFlowerAt P.1 P.2 fam).toData hsign).flowerGraft := by
  rw [← (pairPartitionEquiv tops).symm.sum_comp]
  exact sum_congr rfl fun P _ =>
    (sum_gateSummand_mk L γ δ Natt hF hsign P.1 P.2 F hFs pat hpat dagger cut1 cut2 (hcut P.1 P.2) hpt hps n n').symm

end Tops

end WaveTurbulence.X2E
