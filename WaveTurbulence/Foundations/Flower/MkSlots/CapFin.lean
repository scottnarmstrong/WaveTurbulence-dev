/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapSlotN
public import WaveTurbulence.Foundations.Flower.MkSlots.CapTriv

/-! # B3s MK-SLOTS (cap slots): the trivial case and the mass comparison

* `norm_capNodeW_le`: the capped node weight is bounded by `1`;
* `capSlot_triv`: a trivial cap couple's slot kernel is a constant of modulus at most `1`;
* `capRegBound_le`: D3's `regBound` against the B3 slot factors `(C√δ)^{size} L^{-η⁸ incoh}`;
* `maxBracketPow_zero`, `fsPhase_zero'`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.VineEstS3.FS

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

theorem norm_exp_real_I (r : ℝ) : ‖Complex.exp ((r : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I r

theorem norm_dagNodeW_le (L γ δ s : ℝ) (LG : LayeredGarden w) (J : Finset (Fin w))
    (dag : Option (Fin w → Fin 3 → Mom d)) (z : GNode LG.garden.tree) (x : Mom d) :
    ‖dagNodeW L γ δ s LG J dag z x‖ ≤ 1 := by
  cases dag with
  | none => simp [dagNodeW]
  | some cc =>
    unfold dagNodeW
    simp only [Option.elim]
    rw [norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · split_ifs
      · rw [norm_exp_real_I]
      · simp
    · split_ifs
      · rw [norm_mul, norm_exp_real_I, one_mul]; simp
      · rw [norm_mul, norm_exp_real_I, one_mul]; simp
      · rw [norm_mul, norm_exp_real_I, one_mul]; simp
      · simp

theorem norm_capNodeW_le (L γ δ : ℝ) (p : ℕ) (s : ℝ) (LG : LayeredGarden w) (J : Finset (Fin w))
    (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d)) (z : GNode LG.garden.tree) (x : Mom d) :
    ‖capNodeW L γ δ p s LG J Rf dag z x‖ ≤ 1 := by
  unfold capNodeW
  rw [norm_mul]
  refine mul_le_one₀ ?_ (norm_nonneg _) (norm_dagNodeW_le L γ δ s LG J dag z x)
  refine norm_fwNode_le LG p _ 1 le_rfl (fun j y => ?_) z x
  unfold frontierG
  rw [Complex.norm_real, Real.norm_eq_abs]
  cases Rf j with
  | none => simp
  | some r =>
    simp only [Option.elim]
    rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
    exact XChain.ProductCut.chi0_le_one _

theorem maxBracketPow_zero (θ : ℝ) : maxBracketPow θ (half (0 : Fin 2 → ℤ)) = 1 := by
  simp [maxBracketPow, half]

theorem fsPhase_zero' (ts : Fin 2 → ℝ) : fsPhase (0 : Fin 2 → ℤ) ts = 1 := by
  unfold fsPhase
  rw [show (fun i : Fin 2 => (((0 : Fin 2 → ℤ) i : ℝ) / 2)) = 0 from by funext i; simp, map_zero,
    AddChar.map_zero_eq_one]
  rfl

/-! ### The trivial cap couple -/

theorem code_eq_triv {Q : RegCpl} (hwf : Q.wf = true) (h1 : Q.trees.1 = .leaf) (h2 : Q.trees.2 = .leaf) :
    Q = .triv := by
  cases Q with
  | triv => rfl
  | type1 c Q₁ Q₂ Q₃ => simp [RegCpl.trees] at h1
  | type2 Xp Xm Qlp =>
    cases Xp with
    | pair m Qr Qg inner rest => simp [RegCpl.trees, RegChain.plug, node3] at h1
    | nil =>
      cases Xm with
      | pair m Qr Qg inner rest => simp [RegCpl.trees, RegChain.plug, node3] at h2
      | nil => simp [RegCpl.wf, RegChain.isNil] at hwf

section Triv

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w))
  (q : SourcePair S)

/-- At the two attachment addresses of a trivial cap pair the anchored profiles are indicators. -/
theorem triv_anch_le (hcap : ∀ j ∈ J, (D.garden hS).tree j = .leaf) (hq : IsCapPair S hS J q)
    (ht : (D.couple q).trees.1 = .leaf ∧ (D.couple q).trees.2 = .leaf) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (L : ℝ) (roots : Fin w → (Fin d → ℤ)) (j : Fin 2) (x : Mom d) :
    |anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots
      ((nativeCoupleForest D hS q).nodeEmbedding (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree j)).1 x| ≤ 1 := by
  have hE := capCouple_emb D hS q
  have hQ := code_eq_triv (D.couple_wf q) ht.1 ht.2
  rw [hQ] at hE
  have hleafA : (capUA D hS q).2 ∈ ((D.garden hS).tree (capUA D hS q).1).leaves := by
    simpa [addrExt] using ((node_iff_of_subtree hE.nodeA hE.treeA []).2.1).2 (by simp [RegCpl.trees, TTree.leaves])
  have hleafB : (capUB D hS q).2 ∈ ((D.garden hS).tree (capUB D hS q).1).leaves := by
    simpa [addrExt] using ((node_iff_of_subtree hE.nodeB hE.treeB []).2.1).2 (by simp [RegCpl.trees, TTree.leaves])
  let gA : GLeaf (D.garden hS).tree := ⟨capUA D hS q, by simpa [addrExt] using hleafA⟩
  let gB : GLeaf (D.garden hS).tree := ⟨capUB D hS q, by simpa [addrExt] using hleafB⟩
  have hpA : ((D.garden hS).pair gA).1 = capUB D hS q := by
    have := hE.pairs _ (List.mem_singleton_self _) gA rfl
    exact this
  have hpB : (D.garden hS).pair gB = gA := by
    have e : (D.garden hS).pair gA = gB := Subtype.ext hpA
    rw [← e, (D.garden hS).pair_pair]
  -- the anchored indicator
  have hind : ∀ g : GLeaf (D.garden hS).tree, (g.1.1 ∈ J ∨ ((D.garden hS).pair g).1.1 ∈ J) →
      |anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots g.1 x| ≤ 1 := by
    intro g hg
    have hpt : pairTrees (layeredReconstruction D hS layer hLayer).garden g.1 = (g.1.1, ((D.garden hS).pair g).1.1) :=
      pairTrees_leaf (D.garden hS) g
    unfold anchProfiles
    rw [hpt]
    dsimp only
    by_cases h1 : g.1.1 ∈ J
    · rw [if_pos h1]
      split_ifs <;> simp
    · rw [if_neg h1, if_pos (hg.resolve_left h1)]
      split_ifs <;> simp
  have hA1 : gA.1.1 = (q.firstLeaf hS).1.1 := capUA_fst D hS q
  have hB1 : gB.1.1 = (q.secondLeaf hS).1.1 := capUB_fst D hS q
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with rfl | rfl
  · have e0 : ((nativeCoupleForest D hS q).nodeEmbedding
        (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree 0)).1 = gA.1 := by
      show ((capUA D hS q).1, (capUA D hS q).2 ++ []) = capUA D hS q
      simp
    rw [e0]
    refine hind gA (hq.imp (fun h1 => by rw [hA1]; exact h1) (fun h2 => ?_))
    rw [hpA, capUB_fst]
    exact h2
  · have e1 : ((nativeCoupleForest D hS q).nodeEmbedding
        (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree 1)).1 = gB.1 := by
      show ((capUB D hS q).1, (capUB D hS q).2 ++ []) = capUB D hS q
      simp
    rw [e1]
    refine hind gB (hq.elim (fun h1 => Or.inr ?_) (fun h2 => Or.inl (by rw [hB1]; exact h2)))
    rw [hpB, hA1]
    exact h1

end Triv

end WaveTurbulence.Flower.MkSlots
