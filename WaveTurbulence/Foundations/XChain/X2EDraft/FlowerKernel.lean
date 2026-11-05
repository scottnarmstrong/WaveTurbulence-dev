/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerFix

/-!
# X2E-3, step 5: the kernel of a flower graft

**Block kernels.**
- `kernelK_markedLeafLG`: the kernel of a marked leaf garden is the indicator that its roots carry the flower
  label.
- `kernelK_plain_eq_KG`: on a plain garden, `kernelK` does not see `s` or the flower label; it is `KG`.
- For flower graft data: `kernelK_lowFl_pair` (pair blocks), `kernelK_lowFl_of_not` (the other blocks).

**The weight** (`gateWeight_eq`). On the flower graft of `x : FlowerAt`, the gate's weight (cutoffs, `†` labels) is
the top weight `wtopFl` of X2E-3 step 2, given the identification of the cutoff weights (`sibWeight_flowerGraft`:
the `†` weight is always identified).

**The kernel** (`kernelKgen_flowerGraft`). The gate kernel of the flower graft of `x` (patterns `plain`, `dRoot`) is
`∑'_{kt} (∏_j σ_j fkCoef_j(kt_j)) ∏_B 𝕂_B(kt)`, by graftgen's `kernelKgen_graft` and
`prefactor_mul_topGenFactor_flower`.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset MeasureTheory Induct SysAPI Cpl
open scoped Classical

variable (L γ δ : ℝ) {d : ℕ}

/-! ## Block kernels -/

section Blocks

/-- **The kernel of a marked leaf garden** is the indicator that its roots carry the flower label. -/
theorem kernelK_markedLeafLG (F : ℕ → Mom d → ℝ) (m : ℕ) (sg : Fin m → ℤˣ) (p : ℕ)
    (up : GBranch (markedLeafLG m sg p).garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (n : Fin m → (Fin d → ℤ))
    (nfl : Fin d → ℤ) :
    kernelK L γ δ F (markedLeafLG m sg p) up s k₀ n nfl = if ∀ j, n j = nfl then 1 else 0 := by
  have ht : ∀ j, (markedLeafLG m sg p).garden.tree j = TTree.leaf := fun _ => rfl
  have := leafForest_no_branch _ ht
  have : IsEmpty (markedLeafLG m sg p).garden.FreeBranch := ⟨fun b => isEmptyElim b.1⟩
  have hz : (markedLeafLG m sg p).garden.zeta = 1 := by simp [Garden.zeta]
  have heps : ∀ κ : GNode (markedLeafLG m sg p).garden.tree → (Fin d → ℤ),
      epsDec (markedLeafLG m sg p).garden κ = 1 := fun κ => by simp [epsDec]
  have hph : ∀ k : GNode (markedLeafLG m sg p).garden.tree → Mom d,
      phaseIntegral L γ δ (markedLeafLG m sg p).garden (kDomain (markedLeafLG m sg p) up s) s k = 1 := by
    intro k
    have hD : kDomain (markedLeafLG m sg p) up s = Set.univ := by
      ext τ
      simp only [kDomain, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro b
      exact isEmptyElim b
    have hv : (volume : Measure ((markedLeafLG m sg p).garden.FreeBranch → ℝ)).real Set.univ = 1 := by
      change (Measure.pi fun _ : (markedLeafLG m sg p).garden.FreeBranch => (volume : Measure ℝ)).real
        Set.univ = 1
      simp only [measureReal_def, Measure.pi_univ, Finset.univ_eq_empty, prod_empty, ENNReal.toReal_one]
    unfold phaseIntegral
    rw [hD, Set.indicator_univ]
    simp only [phaseProd, Finset.univ_eq_empty, prod_empty, integral_const, hv, one_smul]
  have hin : inputLeaves (markedLeafLG m sg p).garden = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro ℓ hℓ
    unfold inputLeaves at hℓ
    rw [Finset.mem_filter] at hℓ
    exact absurd hℓ.2.2 (by simp [markedLeafLG, markedLeafGarden])
  rw [kernelK, leafForest_garden_order _ ht, pow_zero, hz, hin]
  simp only [heps, hph, prod_empty, Complex.ofReal_one, one_mul, mul_one]
  by_cases hm : ∀ j, n j = nfl
  · rw [ite_eq_left hm]
    let κ : GenDecoration (markedLeafLG m sg p).garden d n nfl :=
      ⟨fun a => n a.1.1, ⟨fun b => isEmptyElim b, fun _ => rfl⟩, fun _ => rfl, fun ℓ _ => hm ℓ.1.1⟩
    have hsub : ∀ κ' : GenDecoration (markedLeafLG m sg p).garden d n nfl, κ' = κ := by
      intro κ'
      apply Subtype.ext
      funext a
      rw [leafForest_node_eq_root _ ht a]
      exact κ'.2.2.1 a.1.1
    rw [tsum_eq_single κ (fun b hb => absurd (hsub b) hb)]
  · have : IsEmpty (GenDecoration (markedLeafLG m sg p).garden d n nfl) := by
      refine ⟨fun κ => hm fun j => ?_⟩
      have h1 := κ.2.2.1 j
      have h2 := κ.2.2.2 ⟨(j, []), by simp [markedLeafLG, markedLeafGarden, TTree.leaves]⟩ rfl
      exact h1.symm.trans h2
    rw [tsum_empty, ite_eq_right hm]

/-- **On a plain garden**, `kernelK` does not see `s` or the flower label. -/
theorem kernelK_plain_eq_KG (F : ℕ → Mom d → ℝ) {m : ℕ} (LG : LayeredGarden m) (hplain : LG.garden.IsPlain)
    (t s : ℝ) (n : Fin m → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelK L γ δ F LG (fun _ => t) s 0 n nfl = KG L γ δ F LG t n := by
  have hnf : ∀ ℓ : GLeaf LG.garden.tree, ¬ LG.garden.IsFlower ℓ := by
    intro ℓ h
    have h' := (hplain ℓ).symm.trans h
    cases h'
  have hlone : ∀ b, ¬ LG.garden.IsLoneParent b := by
    rintro b ⟨ℓ, hl, -⟩
    have h' := (hplain ℓ).symm.trans hl
    cases h'
  have hD : kDomain LG (fun _ => t) s = kDomain LG (fun _ => t) 0 := by
    ext τ
    simp only [kDomain, Set.mem_ofPred_eq, hlone, false_implies, and_true]
  let e : GenDecoration LG.garden d n nfl ≃ GenDecoration LG.garden d n 0 :=
    Equiv.subtypeEquivRight fun κ => by simp only [hnf, false_implies, implies_true, and_true]
  unfold KG kernelK
  congr 1
  refine Eq.trans ?_ (e.tsum_eq _)
  refine tsum_congr fun κ => ?_
  rw [hD, phaseIntegral_of_plain L γ δ _ hplain, phaseIntegral_of_plain L γ δ _ hplain]
  rfl

end Blocks

/-! ## Flower graft data -/

namespace FlowerGraftData

variable {Pm p : ℕ} {ζ : ℤˣ} (D : FlowerGraftData Pm p ζ)

theorem lowFl_branch_layer_lt (B : D.base.partition.parts) (b : GBranch (D.lowFl B).garden.tree) :
    (D.lowFl B).layer b.toNode < p := by
  by_cases hB : D.IsPairBlock B.1
  · exfalso
    have hb : b.1.2 ∈ ((D.lowFl B).garden.tree b.1.1).branching := b.2
    rw [congrFun (D.lowFl_tree_leaf hB) b.1.1, TTree.branching] at hb
    exact notMem_empty _ hb
  · have key : ∀ LG : LayeredGarden B.1.card, LG = D.base.low B →
        ∀ c : GBranch LG.garden.tree, LG.layer c.toNode < p := by
      rintro _ rfl c
      exact D.base.lower_branch_layer_lt B c
    exact key _ (D.lowFl_of_not hB) b

theorem lowFl_mark_ne_lower (B : D.base.partition.parts) (ℓ : GLeaf (D.lowFl B).garden.tree) :
    (D.lowFl B).garden.mark ℓ ≠ some MarkTag.lower := by
  by_cases hB : D.IsPairBlock B.1
  · have key : ∀ LG : LayeredGarden B.1.card, LG = markedLeafLG B.1.card (D.base.low B).garden.sig p →
        ∀ c : GLeaf LG.garden.tree, LG.garden.mark c ≠ some MarkTag.lower := by
      rintro _ rfl c h
      simp [markedLeafLG, markedLeafGarden] at h
    exact key _ (D.lowFl_of_pair hB) ℓ
  · have key : ∀ LG : LayeredGarden B.1.card, LG = D.base.low B →
        ∀ c : GLeaf LG.garden.tree, LG.garden.mark c ≠ some MarkTag.lower := by
      rintro _ rfl c h
      rw [D.base.plain B c] at h
      cases h
    exact key _ (D.lowFl_of_not hB) ℓ

theorem lowFl_not_isFlowerParent (B : D.base.partition.parts) (b : GBranch (D.lowFl B).garden.tree) :
    ¬ (D.lowFl B).garden.IsFlowerParent b := by
  by_cases hB : D.IsPairBlock B.1
  · have hb : b.1.2 ∈ ((D.lowFl B).garden.tree b.1.1).branching := b.2
    rw [congrFun (D.lowFl_tree_leaf hB) b.1.1, TTree.branching] at hb
    exact absurd hb (notMem_empty _)
  · have key : ∀ LG : LayeredGarden B.1.card, LG = D.base.low B →
        ∀ c : GBranch LG.garden.tree, ¬ LG.garden.IsFlowerParent c := by
      rintro _ rfl c
      exact not_flowerParent_of_plain _ (D.base.plain B) c
    exact key _ (D.lowFl_of_not hB) b

/-- The pair-block kernel. -/
theorem kernelK_lowFl_pair (F : ℕ → Mom d → ℝ) {B : D.base.partition.parts} (hB : D.IsPairBlock B.1)
    (t s : ℝ) (k₀ : Mom d) (n : Fin B.1.card → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelK L γ δ F (D.lowFl B) (fun _ => t) s k₀ n nfl = if ∀ k, n k = nfl then 1 else 0 := by
  rw [D.lowFl_of_pair hB]
  exact kernelK_markedLeafLG L γ δ F _ _ p _ s k₀ n nfl

/-- The other block kernels. -/
theorem kernelK_lowFl_of_not (F : ℕ → Mom d → ℝ) {B : D.base.partition.parts} (hB : ¬ D.IsPairBlock B.1)
    (t s : ℝ) (n : Fin B.1.card → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelK L γ δ F (D.lowFl B) (fun _ => t) s 0 n nfl = KG L γ δ F (D.base.low B) t n := by
  rw [D.lowFl_of_not hB]
  exact kernelK_plain_eq_KG L γ δ F _ (D.base.plain B) t s n nfl

/-- A flower node of the flower graft is a flower leaf. -/
theorem isFlowerNode_iff (a : GNode D.flowerGraft.garden.tree) :
    D.flowerGraft.IsFlowerNode a ↔ a.1.2 = D.fl a.1.1 := by
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    exact (D.isFlower_iff ℓ).mp hℓ
  · intro h
    refine ⟨D.flLeaf a.1.1, (D.isFlower_iff _).mpr ?_, Subtype.ext ?_⟩
    · rw [D.flLeaf_val]
    · change (D.flLeaf a.1.1).1 = a.1
      rw [D.flLeaf_val, ← h]

/-- Products over the branches of the flower graft split into top and lower branches. -/
theorem prod_branch {M : Type*} [CommMonoid M] (f : GBranch D.flowerGraft.garden.tree → M) :
    ∏ b, f b = (∏ b : GBranch D.base.top,
        f (gardenBranchEquiv D.base.top D.base.partition (fun B => (D.lowFl B).garden) (.inl b))) *
      ∏ z, f (gardenBranchEquiv D.base.top D.base.partition (fun B => (D.lowFl B).garden) (.inr z)) := by
  rw [← Fintype.prod_sum_type (fun z => f (gardenBranchEquiv D.base.top D.base.partition
    (fun B => (D.lowFl B).garden) z))]
  exact (Fintype.prod_equiv (gardenBranchEquiv D.base.top D.base.partition (fun B => (D.lowFl B).garden)) _ f
    (fun _ => rfl)).symm

theorem prod_branch_top {M : Type*} [CommMonoid M] (f : GBranch D.flowerGraft.garden.tree → M)
    (hf : ∀ B c, f (gardenBranchEquiv D.base.top D.base.partition (fun B => (D.lowFl B).garden) (.inr ⟨B, c⟩)) = 1) :
    ∏ b, f b = ∏ b : GBranch D.base.top,
      f (gardenBranchEquiv D.base.top D.base.partition (fun B => (D.lowFl B).garden) (.inl b)) := by
  rw [D.prod_branch f, Fintype.prod_eq_one (fun z => f (gardenBranchEquiv D.base.top D.base.partition
    (fun B => (D.lowFl B).garden) (.inr z))) (fun z => hf z.1 z.2), mul_one]

end FlowerGraftData

/-! ## The weight -/

section Weight

theorem abs_treeWeightK_le_one (F : FTree) (hF : F ≠ FTree.flower) (dagger : Option (Fin 3 → Mom d))
    (cut1 cut2 : Option ℕ) (k : GNode (single F.toTree) → Mom d) : |treeWeightK L F hF dagger cut1 cut2 k| ≤ 1 := by
  unfold treeWeightK
  rw [abs_mul, abs_mul]
  have h1 : |cut1.elim 1 fun j₁ => treeCut1K L F j₁ k| ≤ 1 := by
    cases cut1 with
    | none => simp
    | some j => exact Fixedpt.abs_dyadicCut_le_one L j _
  have h2 : |cut2.elim 1 fun j₂ => treeCut2K L F hF j₂ k| ≤ 1 := by
    cases cut2 with
    | none => simp
    | some j => exact Fixedpt.abs_dyadicCut_le_one L j _
  have h3 : |dagger.elim 1 fun c => treeSibK F hF c k| ≤ 1 := by
    cases dagger with
    | none => simp
    | some c =>
      change |treeSibK F hF c k| ≤ 1
      unfold treeSibK
      rw [Finset.abs_prod]
      refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
      split_ifs <;> simp
  calc |cut1.elim 1 fun j₁ => treeCut1K L F j₁ k| * |cut2.elim 1 fun j₂ => treeCut2K L F hF j₂ k| *
        |dagger.elim 1 fun c => treeSibK F hF c k| ≤ 1 * 1 * 1 := by
        gcongr
    _ = 1 := by ring

theorem abs_wtopFl_le_one {w : ℕ} (tops : Fin w → FTree) (hF : ∀ j, tops j ≠ FTree.flower)
    (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (k : GNode (ftop tops) → Mom d) :
    |wtopFl tops hF L dagger cut1 cut2 k| ≤ 1 := by
  unfold wtopFl
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => abs_treeWeightK_le_one L _ _ _ _ _ _

variable {Pm p : ℕ} {ζ : ℤˣ} {tops : Fin (2 * Pm) → FTree} (hF : ∀ j, tops j ≠ FTree.flower)
  (x : FlowerAt Pm p tops) (hsign : ∀ j, (tops j).sign = ζ)

omit hF in
theorem topChild_eq (j : Fin (2 * Pm)) (c : GBranch (single (tops j).toTree)) (i : Fin 3) :
    (gardenBranchEquiv (ftop tops) x.partition (fun B => ((x.toData hsign).lowFl B).garden)
      (.inl (singleBranchToForest (ftop tops) j c))).child i =
    topNodeEmbedding (ftop tops) x.partition (fun B => ((x.toData hsign).lowFl B).garden)
      (singleNodeToForest (ftop tops) j (c.child i)) :=
  topBranch_child _ _ _ (singleBranchToForest (ftop tops) j c) i

/-- **The `†` weight of the flower graft** is the product of the tree `†` weights. -/
theorem sibWeight_flowerGraft (c : Fin 3 → Mom d) (k : GNode (x.toData hsign).flowerGraft.garden.tree → Mom d) :
    (x.toData hsign).flowerGraft.sibWeight (fun _ => c) k =
      ∏ j, treeSibK (tops j) (hF j) c (fun a => k (topNodeEmbedding (ftop tops) x.partition
        (fun B => ((x.toData hsign).lowFl B).garden) (singleNodeToForest (ftop tops) j a))) := by
  unfold LayeredGarden.sibWeight
  rw [(x.toData hsign).prod_branch_top _ ?hlow]
  case hlow =>
    intro B b
    exact ite_eq_right ((x.toData hsign).not_isFlowerParent_lower B b)
  rw [← (forestSingleBranchEquiv (ftop tops)).symm.prod_comp, Fintype.prod_sigma]
  simp only [forestSingleBranchEquiv_symm_apply]
  refine prod_congr rfl fun j _ => ?_
  rw [Fintype.prod_eq_single ((tops j).flowerParent (hF j)) ?_]
  · refine (ite_eq_left ((isFlowerParent_top hF x hsign _).mpr rfl)).trans ?_
    unfold treeSibK
    refine prod_congr rfl fun i _ => ?_
    have hn := topChild_eq x hsign j ((tops j).flowerParent (hF j)) i
    have hfl : (x.toData hsign).flowerGraft.IsFlowerNode
        ((gardenBranchEquiv (ftop tops) x.partition (fun B => ((x.toData hsign).lowFl B).garden)
          (.inl (singleBranchToForest (ftop tops) j ((tops j).flowerParent (hF j))))).child i) ↔
        (((tops j).flowerParent (hF j)).child i).1.2 = (tops j).flowerPath := by
      rw [hn]
      exact (x.toData hsign).isFlowerNode_iff _
    have hk : k (topNodeEmbedding (ftop tops) x.partition (fun B => ((x.toData hsign).lowFl B).garden)
        (singleNodeToForest (ftop tops) j (((tops j).flowerParent (hF j)).child i))) =
        k ((gardenBranchEquiv (ftop tops) x.partition (fun B => ((x.toData hsign).lowFl B).garden)
          (.inl (singleBranchToForest (ftop tops) j ((tops j).flowerParent (hF j))))).child i) :=
      congrArg k hn.symm
    by_cases h : (((tops j).flowerParent (hF j)).child i).1.2 = (tops j).flowerPath
    · exact (ite_eq_left (hfl.mpr h)).trans (ite_eq_left h).symm
    · refine (ite_eq_right (fun h' => h (hfl.mp h'))).trans (Eq.trans ?_ (ite_eq_right h).symm)
      exact if_congr ⟨fun h1 => hk.trans h1, fun h1 => hk.symm.trans h1⟩ rfl rfl
  · intro b hb
    exact ite_eq_right fun h' => hb (Subtype.ext (Prod.ext (Subsingleton.elim _ _)
      ((isFlowerParent_top hF x hsign _).mp h')))

/-- **The gate weight of the flower graft** is the top weight, given the cutoff weights. -/
theorem gateWeight_eq (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ)
    (h1 : ∀ j₁ ∈ cut1, ∀ k : GNode (x.toData hsign).flowerGraft.garden.tree → Mom d,
      (x.toData hsign).flowerGraft.cutWeight1 p L j₁ k =
      ∏ j, treeCut1K L (tops j) j₁ (fun a => k (topNodeEmbedding (ftop tops) x.partition
        (fun B => ((x.toData hsign).lowFl B).garden) (singleNodeToForest (ftop tops) j a))))
    (h2 : ∀ j₂ ∈ cut2, ∀ k : GNode (x.toData hsign).flowerGraft.garden.tree → Mom d,
      (x.toData hsign).flowerGraft.cutWeight2 L j₂ k =
      ∏ j, treeCut2K L (tops j) (hF j) j₂ (fun a => k (topNodeEmbedding (ftop tops) x.partition
        (fun B => ((x.toData hsign).lowFl B).garden) (singleNodeToForest (ftop tops) j a))))
    (k : GNode (x.toData hsign).flowerGraft.garden.tree → Mom d) :
    (cut1.elim 1 fun j₁ => (x.toData hsign).flowerGraft.cutWeight1 p L j₁ k) *
        (cut2.elim 1 fun j₂ => (x.toData hsign).flowerGraft.cutWeight2 L j₂ k) *
        ((dagger.map fun c _ => c).elim 1 fun c => (x.toData hsign).flowerGraft.sibWeight c k) =
      wtopFl tops hF L dagger cut1 cut2
        (fun a => k (topNodeEmbedding (ftop tops) x.partition (fun B => ((x.toData hsign).lowFl B).garden) a)) := by
  unfold wtopFl treeWeightK
  rw [prod_mul_distrib, prod_mul_distrib]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_
  · cases cut1 with
    | none => simp
    | some j₁ => exact h1 j₁ rfl k
  · cases cut2 with
    | none => simp
    | some j₂ => exact h2 j₂ rfl k
  · cases dagger with
    | none => simp
    | some c => exact sibWeight_flowerGraft hF x hsign c k

end Weight

/-! ## The kernel -/

section Kernel

theorem treeFixPat_ge {F : FTree} (hF : F ≠ FTree.flower) {pat : FixPat} (hpat : pat = .plain ∨ pat = .dRoot)
    {t s c v : ℝ} (hct : c ≤ t) (hcs : c ≤ s) {b : GBranch (single F.toTree)}
    (h : treeFixPat F hF pat t s b = some v) : c ≤ v := by
  unfold treeFixPat at h
  rcases hpat with rfl | rfl
  · dsimp only at h
    split_ifs at h
    cases h
    exact hcs
  · dsimp only at h
    split_ifs at h <;> cases h <;> assumption

variable {Pm p : ℕ} {ζ : ℤˣ} {tops : Fin (2 * Pm) → FTree} (hF : ∀ j, tops j ≠ FTree.flower)
  (x : FlowerAt Pm p tops) (hsign : ∀ j, (tops j).sign = ζ)

/-- **The gate kernel of a flower graft**: the signed flower coefficients times the block kernels. -/
theorem kernelKgen_flowerGraft (F : ℕ → Mom d → ℝ)
    (hFs : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|)
    (pat : FixPat) (hpat : pat = .plain ∨ pat = .dRoot) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ)
    (wgate : (GNode (x.toData hsign).flowerGraft.garden.tree → Mom d) → ℝ)
    (hw : ∀ k, wgate k = wtopFl tops hF L dagger cut1 cut2
      (fun a => k (topNodeEmbedding (ftop tops) x.partition (fun B => ((x.toData hsign).lowFl B).garden) a)))
    {t s : ℝ} (hpt : (p : ℝ) ≤ t) (hps : (p : ℝ) ≤ s) (n n' : Fin d → ℤ) :
    kernelKgen L γ δ F (x.toData hsign).flowerGraft ((x.toData hsign).flowerGraft.fixPat (fun _ => pat) t s)
        (if dagger.isSome then univ.filter (x.toData hsign).flowerGraft.garden.IsFlowerParent else ∅)
        wgate (fun _ => t) 0 (fun _ => n) n' =
      ∑' kt : ForestDecoration (ftop tops) d (fun _ => n),
        (∏ j, zpowSign (altFlowerSig Pm j) (fkCoef L γ δ p pat dagger cut1 cut2 t s (tops j)
          (fun a => kt.1 (singleNodeToForest (ftop tops) j a)))) *
        ∏ B : x.partition.parts, kernelK L γ δ F ((x.toData hsign).lowFl B) (fun _ => p) s 0
          (fun k => kt.1 ((blockRootEquiv (ftop tops) x.partition).symm ⟨B, k⟩).toNode) n' := by
  have hwf : wgate = fun k => wtopFl tops hF L dagger cut1 cut2
      (fun a => k (topNodeEmbedding (ftop tops) x.partition (fun B => ((x.toData hsign).lowFl B).garden) a)) :=
    funext hw
  have hfixv : ∀ b v, fixFl tops hF pat t s b = some v → (p : ℝ) ≤ v :=
    fun b v h => treeFixPat_ge (hF b.1.1) hpat hpt hps h
  have hF' : ∀ q, Summable fun m : Fin d → ℤ => |F q ((0 : Mom d) + latticePoint L m)| := by
    simpa only [zero_add] using hFs
  have hk := GraftGen.kernelKgen_graft L γ δ (sig := altFlowerSig Pm) (top := ftop tops) (P := x.partition)
    (low := (x.toData hsign).lowFl) (p := p) (hsig := (x.toData hsign).lowFl_sig)
    (hbound := (x.toData hsign).lowFl_bound) F
    (x.toData hsign).lowFl_branch_layer_lt (x.toData hsign).lowFl_mark_ne_lower
    (x.toData hsign).lowFl_not_isFlowerParent
    _ (fixFl tops hF pat t s)
    (fixPat_top hF x hsign pat hpat t s) (fun z => fixPat_lower hF x hsign pat hpat t s z.1 z.2) hfixv
    _ (offFl tops hF dagger) (off_top hF x hsign dagger) (fun z => off_lower x hsign dagger z.1 z.2)
    (wtopFl tops hF L dagger cut1 cut2) (abs_wtopFl_le_one L tops hF dagger cut1 cut2) t s hpt 0 (fun _ => n) n' hF'
  rw [hwf]
  refine hk.trans ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun kt => ?_
  rw [← mul_assoc, prefactor_mul_topGenFactor_flower L γ δ p pat dagger cut1 cut2 t s tops hF (altFlowerSig Pm) kt]

end Kernel

end WaveTurbulence.X2E
