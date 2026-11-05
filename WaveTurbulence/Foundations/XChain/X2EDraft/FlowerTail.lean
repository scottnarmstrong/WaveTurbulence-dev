/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerBracket
public import WaveTurbulence.Foundations.XChain.AnsatzInputOrderBound
public import WaveTurbulence.Foundations.XChain.FiniteProductTailBound
public import WaveTurbulence.Foundations.XChain.FiniteOrderGrouping
public import WaveTurbulence.Foundations.XChain.PartitionWeightProduct
public import WaveTurbulence.Foundations.XChain.GardenGraftOrder

/-!
# X2E-4, step 2: the order tail at fixed flower trees

For a partition `P` with the pair blocks and `J : ℕ`, the gate summands of the flower grafts whose lower components
have total order `≥ J`:
- `sum_gateSummand_mk_tail`: grouped by the orders of the lower components (INDUCT's `sum_pi_by_orders`);
- `norm_sum_gateSummand_mk_tail_le`: bounded by `C^{|P|} (δ^{ν/2})^J 2^{|P|}` times the flower forest bracket bound
  (`⟨n − ζ n'⟩^{−Λ_p/4}` per tree), under `AnsatzAt`.

`order_flowerGraft`: the order of a flower graft is the top order plus the lower orders.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset MeasureTheory Induct SysAPI Cpl
open scoped Classical

theorem FlowerGraftData.order_flowerGraft {Pm p : ℕ} {ζ : ℤˣ} (D : FlowerGraftData Pm p ζ) :
    D.flowerGraft.garden.order = (∑ j, (D.base.top j).order) + ∑ B, (D.base.low B).garden.order := by
  have h1 : D.flowerGraft.garden.order = D.base.graft.garden.order := by
    unfold Garden.order
    rw [D.flowerGraft_tree]
  rw [h1]
  exact gardenGraft_order (altFlowerSig Pm) D.base.top D.base.partition (fun B => (D.base.low B).garden)
    D.base.plain D.base.sign

variable (L γ δ : ℝ) {d : ℕ}

/-- The signed top coefficients of a decoration of the top forest. -/
noncomputable def topCoefK (p : ℕ) (pat : FixPat) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ)
    (t s : ℝ) {Pm : ℕ} (tops : Fin (2 * Pm) → FTree) (κ : GNode (ftop tops) → (Fin d → ℤ)) : ℂ :=
  ∏ j, zpowSign (altFlowerSig Pm j) (fkCoef L γ δ p pat dagger cut1 cut2 t s (tops j)
    (fun a => κ (singleNodeToForest (ftop tops) j a)))

/-- The block factor of a lower datum: the flower-label indicator on a pair block, `KG` otherwise. -/
noncomputable def blockG (F : ℕ → Mom d → ℝ) (p Natt : ℕ) (n' : Fin d → ℤ) {Pm : ℕ} (tops : Fin (2 * Pm) → FTree)
    (P : Finpartition (univ : Finset (GLeaf (ftop tops)))) (B : P.parts) (D : LowerGraftData (sigP tops P B) p Natt)
    (κ : GNode (ftop tops) → (Fin d → ℤ)) : ℂ :=
  if B.1 ∈ pairSet tops then (if ∀ k : Fin B.1.card, κ (B.1.equivFin.symm k).1.toNode = n' then 1 else 0)
  else KG L γ δ F D.low p (fun k => κ ((blockRootEquiv (ftop tops) P).symm ⟨B, k⟩).toNode)

/-- The order of a lower datum. -/
def lowOrd {w p Natt : ℕ} {sig : Fin w → ℤˣ} (D : LowerGraftData sig p Natt) : Fin (Natt + 1) :=
  ⟨D.low.garden.order, Nat.lt_succ_of_le D.order_le⟩

section Tops

variable {Pm p : ℕ} (Natt : ℕ) {ζ : ℤˣ} {tops : Fin (2 * Pm) → FTree} (hF : ∀ j, tops j ≠ FTree.flower)
  (hsign : ∀ j, (tops j).sign = ζ)

include hF hsign in
/-- **The order tail at a partition with pair blocks**, grouped by orders. -/
theorem sum_gateSummand_mk_tail (P : Finpartition (univ : Finset (GLeaf (ftop tops))))
    (hP : ∀ j, pbF tops j ∈ P.parts) (F : ℕ → Mom d → ℝ)
    (hFs : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|)
    (pat : FixPat) (hpat : pat = .plain ∨ pat = .dRoot) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ)
    (hcut : ∀ fam : (B : P.parts) → LowerGraftData (sigP tops P B) p Natt,
      CutWeightsOK L (d := d) hF (mkFlowerAt P hP fam) hsign cut1 cut2)
    {t s : ℝ} (hpt : (p : ℝ) ≤ t) (hps : (p : ℝ) ≤ s) (n n' : Fin d → ℤ) (J : ℕ) :
    ∑ fam : (B : P.parts) → LowerGraftData (sigP tops P B) p Natt,
        (if J ≤ ∑ B, (fam B).low.garden.order then
          gateSummand L γ δ F p pat dagger cut1 cut2 t s n n' ((mkFlowerAt P hP fam).toData hsign).flowerGraft
        else 0) =
      ∑' kt : ForestDecoration (ftop tops) d (fun _ => n),
        topCoefK L γ δ p pat dagger cut1 cut2 t s tops kt.1 *
          ∑ orders : P.parts → Fin (Natt + 1), if J ≤ ∑ B, (orders B).1 then
            ∏ B : P.parts, ∑ D : LowerGraftData (sigP tops P B) p Natt,
              (if lowOrd D = orders B then blockG L γ δ F p Natt n' tops P B D kt.1 else 0)
          else 0 := by
  let c := fun kt : ForestDecoration (ftop tops) d (fun _ => n) => topCoefK L γ δ p pat dagger cut1 cut2 t s tops kt.1
  let g := fun (B : P.parts) (D : LowerGraftData (sigP tops P B) p Natt)
    (kt : ForestDecoration (ftop tops) d (fun _ => n)) => blockG L γ δ F p Natt n' tops P B D kt.1
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
  have he : ∀ fam : (B : P.parts) → LowerGraftData (sigP tops P B) p Natt,
      (if J ≤ ∑ B, (fam B).low.garden.order then
        gateSummand L γ δ F p pat dagger cut1 cut2 t s n n' ((mkFlowerAt P hP fam).toData hsign).flowerGraft
      else 0) = ∑' kt, (if J ≤ ∑ B, (fam B).low.garden.order then c kt * ∏ B, g B (fam B) kt else 0) := by
    intro fam
    by_cases hJ : J ≤ ∑ B, (fam B).low.garden.order
    · simp only [hJ, ite_true]
      exact hk fam
    · simp only [hJ, ite_false, tsum_zero]
  have hs' : ∀ fam : (B : P.parts) → LowerGraftData (sigP tops P B) p Natt,
      Summable fun kt => if J ≤ ∑ B, (fam B).low.garden.order then c kt * ∏ B, g B (fam B) kt else 0 := by
    intro fam
    by_cases hJ : J ≤ ∑ B, (fam B).low.garden.order
    · simpa only [hJ, ite_true] using hs fam
    · simpa only [hJ, ite_false] using (summable_zero : Summable fun _ : ForestDecoration (ftop tops) d
        (fun _ => n) => (0 : ℂ))
  rw [sum_congr rfl fun fam _ => he fam, ← Summable.tsum_finsetSum fun fam _ => hs' fam]
  refine tsum_congr fun kt => ?_
  let W : (P.parts → Fin (Natt + 1)) → ℂ := fun o => if J ≤ ∑ B, (o B).1 then 1 else 0
  have hW : ∀ fam : (B : P.parts) → LowerGraftData (sigP tops P B) p Natt,
      (if J ≤ ∑ B, (fam B).low.garden.order then c kt * ∏ B, g B (fam B) kt else 0) =
        c kt * (W (fun B => lowOrd (fam B)) * ∏ B, g B (fam B) kt) := by
    intro fam
    by_cases hJ : J ≤ ∑ B, (fam B).low.garden.order
    · have hJ' : J ≤ ∑ B, (lowOrd (fam B)).1 := hJ
      simp only [hJ, hJ', W, ite_true, one_mul]
    · have hJ' : ¬ J ≤ ∑ B, (lowOrd (fam B)).1 := hJ
      simp only [hJ, hJ', W, ite_false, zero_mul, mul_zero]
  rw [sum_congr rfl fun fam _ => hW fam, ← mul_sum]
  congr 1
  rw [sum_pi_by_orders (fun B (D : LowerGraftData (sigP tops P B) p Natt) => lowOrd D) (fun B D => g B D kt) W]
  refine sum_congr rfl fun orders _ => ?_
  by_cases hJ : J ≤ ∑ B, (orders B).1
  · simp only [W, hJ, ite_true, one_mul]
    rfl
  · simp only [W, hJ, ite_false, zero_mul]

end Tops

/-! ## The bound -/

section Bound

variable (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : (Fin Q.d → ℤ) → Ω → ℂ) (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom Q.d → ℝ)
    (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ) (p : ℕ)
    (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hL : 1 ≤ Q.L) (hδ : 0 < Q.δ) (hsmall' : Q.δ ^ (Q.ν / 2) ≤ 1 / 2) (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤ C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))
    {Pm : ℕ} {ζ : ℤˣ} {tops : Fin (2 * Pm) → FTree} (hsign : ∀ j, (tops j).sign = ζ)
    (hR : (nfLeaves tops).card ≤ 2 * Q.R p)

/-- The block weight: `⟨k_ℓ⟩` on the non-flower leaves, `1` on the flowers. -/
noncomputable def nfWt (tops : Fin (2 * Pm) → FTree) (κ : GNode (ftop tops) → (Fin Q.d → ℤ))
    (l : GLeaf (ftop tops)) : ℝ :=
  if l ∈ nfLeaves tops then jbr (latticePoint Q.L (κ l.toNode)) else 1

theorem subset_nfLeaves_of_not_pair (P : Finpartition (univ : Finset (GLeaf (ftop tops))))
    (hP : ∀ j, pbF tops j ∈ P.parts) (B : P.parts) (hB : B.1 ∉ pairSet tops) : B.1 ⊆ nfLeaves tops := by
  intro l hl
  by_contra hn
  exact hB (P.eq_of_mem_parts B.2 (hP l.1.1) hl (mem_pbF_self_of_notMem tops l hn) ▸ pbF_mem_pairSet tops _)

theorem order_eq_zero_of_card_two {w p N : ℕ} {sig : Fin w → ℤˣ} (hw : w = 2) (D : LowerGraftData sig p N) :
    D.low.garden.order = 0 := by
  rcases D.component with h | h
  · have := isCanonG_width h
    omega
  · exact leafForest_garden_order _ h.2.1

include ha hL hδ hsmall' hC hF hsign hR in
/-- **The inner order tail at a decoration.** -/
theorem norm_inner_tail_le (P : Finpartition (univ : Finset (GLeaf (ftop tops))))
    (hP : ∀ j, pbF tops j ∈ P.parts) (n' : Fin Q.d → ℤ) (κ : GNode (ftop tops) → (Fin Q.d → ℤ)) (J : ℕ) :
    ‖∑ orders : P.parts → Fin (Q.N p + 1), if J ≤ ∑ B, (orders B).1 then
        ∏ B : P.parts, ∑ D : LowerGraftData (sigP tops P B) p (Q.N p),
          (if lowOrd D = orders B then blockG Q.L Q.γ Q.δ (inputsF Q R) p (Q.N p) n' tops P B D κ else 0)
      else 0‖ ≤
      (if ∀ j, κ (flowerAt tops j).toNode = n' then 1 else 0) *
        ((C ^ P.parts.card * (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ l.toNode))) ^
          (-(Q.Lambda p : ℝ) / 2)) * ((Q.δ ^ (Q.ν / 2)) ^ J * 2 ^ P.parts.card)) := by
  set Λ := (Q.Lambda p : ℝ)
  set h := fun (B : P.parts) (N : Fin (Q.N p + 1)) => ∑ D : LowerGraftData (sigP tops P B) p (Q.N p),
    (if lowOrd D = N then blockG Q.L Q.γ Q.δ (inputsF Q R) p (Q.N p) n' tops P B D κ else 0) with hh
  by_cases hind : ∀ j, κ (flowerAt tops j).toNode = n'
  · rw [ite_eq_left hind, one_mul]
    have hq0 : 0 ≤ Q.δ ^ (Q.ν / 2) := Real.rpow_nonneg hδ.le _
    have hbound : ∀ B N, ‖h B N‖ ≤ (C * (∏ l ∈ B.1, nfWt Q tops κ l) ^ (-Λ / 2)) * (Q.δ ^ (Q.ν / 2)) ^ (2 * N.1) := by
      intro B N
      by_cases hB : B.1 ∈ pairSet tops
      · obtain ⟨j, -, hj⟩ := mem_image.mp hB
        have hc : B.1.card = 2 := hj ▸ card_pbF tops j
        obtain ⟨u⟩ := lowerData_unique_of_pair hsign P B hB p (Q.N p)
        have hw1 : ∏ l ∈ B.1, nfWt Q tops κ l = 1 := prod_eq_one fun l hl => by
          unfold nfWt
          exact ite_eq_right (notMem_nfLeaves_of_mem_pairSet tops hB hl)
        have hind' : ∀ k : Fin B.1.card, κ (B.1.equivFin.symm k).1.toNode = n' := by
          intro k
          have hk : (B.1.equivFin.symm k).1 ∈ pbF tops j := by
            rw [hj]
            exact (B.1.equivFin.symm k).2
          rcases (mem_pbF tops j _).mp hk with h' | h'
          · rw [h']
            exact hind j
          · rw [h']
            exact hind _
        have hval : h B N = if lowOrd (default : LowerGraftData (sigP tops P B) p (Q.N p)) = N then 1 else 0 := by
          rw [hh]
          dsimp only
          rw [Fintype.sum_unique]
          unfold blockG
          rw [ite_eq_left hB, ite_eq_left hind']
        rw [hval, hw1, Real.one_rpow, mul_one]
        by_cases hN : lowOrd (default : LowerGraftData (sigP tops P B) p (Q.N p)) = N
        · rw [ite_eq_left hN, norm_one]
          have hN0 : N.1 = 0 := by
            rw [← hN]
            exact order_eq_zero_of_card_two hc _
          rw [hN0, mul_zero, pow_zero, mul_one]
          linarith
        · rw [ite_eq_right hN, norm_zero]
          exact mul_nonneg (by linarith) (pow_nonneg hq0 _)
      · have hsub := subset_nfLeaves_of_not_pair P hP B hB
        have hcard : 1 ≤ B.1.card := card_pos.mpr (P.nonempty_of_mem_parts B.2)
        have hR' : B.1.card ≤ 2 * Q.R p := (card_le_card hsub).trans hR
        have hval : h B N = lowerOrderKernelSum Q.L Q.γ Q.δ (inputsF Q R) (sigP tops P B) p (Q.N p) N
            (fun k => κ ((blockRootEquiv (ftop tops) P).symm ⟨B, k⟩).toNode) := by
          rw [hh]
          unfold lowerOrderKernelSum
          refine sum_congr rfl fun D _ => ?_
          unfold blockG lowOrd
          rw [ite_eq_right hB]
          by_cases hD : D.low.garden.order = N.1
          · rw [ite_eq_left (Fin.ext hD), ite_eq_left hD]
          · rw [ite_eq_right (fun h' => hD (congrArg Fin.val h')), ite_eq_right hD]
        rw [hval]
        have hk := ansatz_input_order_kernel_bound Q μ g a Fev R E Et p N ha hL hδ C hC hF hcard hR' (sigP tops P B)
          (fun k => κ ((blockRootEquiv (ftop tops) P).symm ⟨B, k⟩).toNode)
        have hprod :
            ∏ k : Fin B.1.card, jbr (latticePoint Q.L (κ ((blockRootEquiv (ftop tops) P).symm ⟨B, k⟩).toNode)) =
            ∏ l ∈ B.1, nfWt Q tops κ l := by
          rw [← prod_coe_sort B.1 (nfWt Q tops κ)]
          refine Fintype.prod_equiv B.1.equivFin.symm
            (fun k => jbr (latticePoint Q.L (κ ((blockRootEquiv (ftop tops) P).symm ⟨B, k⟩).toNode)))
            (fun l => nfWt Q tops κ l.1) (fun k => ?_)
          unfold nfWt
          rw [ite_eq_left (hsub (B.1.equivFin.symm k).2)]
          rfl
        have hδN : Q.δ ^ (Q.ν * N.1) = (Q.δ ^ (Q.ν / 2)) ^ (2 * N.1) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
          congr 1
          push_cast
          ring
        rw [hprod, hδN] at hk
        exact hk
    have he := norm_sum_pi_product_tail_le (ι := P.parts) (Q.N p + 1) J h
      (fun B => C * (∏ l ∈ B.1, nfWt Q tops κ l) ^ (-Λ / 2))
      (fun B => mul_nonneg (by linarith) (Real.rpow_nonneg (prod_nonneg fun l _ => by
        unfold nfWt
        split_ifs
        · exact (jbr_pos _).le
        · exact zero_le_one) _)) hq0 hsmall' hbound
    rw [prod_finpartition_rpow P (nfWt Q tops κ) (fun l _ => by
        unfold nfWt
        split_ifs
        · exact (jbr_pos _).le
        · exact zero_le_one) C (-Λ / 2)] at he
    have hnf : ∏ l ∈ (univ : Finset (GLeaf (ftop tops))), nfWt Q tops κ l =
        ∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ l.toNode)) := by
      unfold nfWt
      rw [prod_ite_mem, univ_inter]
    rw [hnf] at he
    simpa only [Fintype.card_coe] using he
  · rw [ite_eq_right hind, zero_mul]
    simp only [not_forall] at hind
    obtain ⟨j, hj⟩ := hind
    have hB0 : pbF tops j ∈ P.parts := hP j
    have hnot : ¬ ∀ k : Fin (pbF tops j).card, κ ((pbF tops j).equivFin.symm k).1.toNode = n' := by
      intro hall
      have hk := hall ((pbF tops j).equivFin ⟨flowerAt tops j, flowerAt_mem_pbF tops j⟩)
      rw [Equiv.symm_apply_apply] at hk
      exact hj hk
    have hzero : ∀ N, h ⟨pbF tops j, hB0⟩ N = 0 := by
      intro N
      rw [hh]
      refine sum_eq_zero fun D _ => ?_
      have hX : blockG Q.L Q.γ Q.δ (inputsF Q R) p (Q.N p) n' tops P ⟨pbF tops j, hB0⟩ D κ = 0 := by
        unfold blockG
        exact (ite_eq_left (pbF_mem_pairSet tops j)).trans (ite_eq_right hnot)
      rw [hX, ite_self]
    rw [norm_le_zero_iff]
    refine sum_eq_zero fun orders _ => ?_
    refine ite_eq_right_iff.mpr fun _ => ?_
    exact prod_eq_zero (mem_univ ⟨pbF tops j, hB0⟩) (hzero _)

end Bound

end WaveTurbulence.X2E
