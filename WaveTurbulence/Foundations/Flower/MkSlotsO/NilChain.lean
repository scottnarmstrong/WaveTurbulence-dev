/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.SlotObl
public import WaveTurbulence.Foundations.Flower.MkSlots.CapTriv
public import WaveTurbulence.Foundations.Flower.MkSlotsB.ROne
public import WaveTurbulence.Foundations.Flower.MkSlotsO.Obstruct

/-! # B3s-HELPER8 (STOP S1): the general slot kernel of a nil-chain slot is `1`, and S1's obstruction

On a chain slot `.inr β` whose native chain garden is a single leaf (the nil chain: the lone leaf is the core node of
`β`), with no frontier scales (`Rf ≡ none`) and no dagger (`dag = none`), HELPER7's general slot kernel
`MkSlotsI.genSlotKer` is identically `1` (any pattern, `σ`, `kSel`, `Rs`, profiles, roots):

* **`genSlotKer_nilChain`**: `genSlotKer … (fun _ => none) none (.inr β) ts k = 1`;
* **`not_genSlotConclusion_nilChain`**: hence the conclusion that `MkSlotsI.GenSlotObligationAt` asks on that slot
  (ball-localized amplitudes with summable weights representing the kernel at every momentum at one point of the
  box) is unsatisfiable when `d ≥ 1` (`MkSlotsO.not_localized_of_norm_ge`).

Ingredients: B3s's `CapTriv` (`isEmpty_branch_of_leaves`, `node_root_of_leaves`, `genDecoration_subsingleton`,
`kernelNodeWF_noBranch`), β's `kernelNodeWR_one_eq`, main's `chainContextNode_lone`, `decodesTree_lone_iff`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.MkSlots (anchProfiles recLG isEmpty_branch_of_leaves node_root_of_leaves
  genDecoration_subsingleton kernelNodeWF_noBranch kerNoBranch)

namespace WaveTurbulence.Flower.MkSlotsO

variable {w d : ℕ}

/-- Without frontier scales and dagger, the chain node weight is `1`. -/
theorem chainW_none {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (L γ δ : ℝ) (p : ℕ) (s : ℝ) (J : Finset (Fin w))
    (z : GNode (D.forest hS)) (x : Mom d) :
    MkSlots.chainW D hS layer hLayer L γ δ p s J (fun _ => none) none z x = 1 := by
  have hfw : fwNode (layeredReconstruction D hS layer hLayer) p (fun j => frontierG ((fun _ => none) j)) z x = 1 := by
    unfold fwNode
    split_ifs
    · unfold Stage1W.topPsi
      split_ifs <;> simp [frontierG]
    · rfl
  unfold MkSlots.chainW
  rw [hfw, one_mul]
  split_ifs <;> rfl

/-- **The general slot kernel of a nil-chain slot is `1`** (no frontier scales, no dagger). -/
theorem genSlotKer_nilChain (L γ δ : ℝ) (p : ℕ) (a : PrescribedPrimeGarden w) (J : Finset (Fin w))
    (pat : Fin w → FixPat) (t s : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ)) (β : GBranch a.prime.skeleton.tree)
    (hT : ∀ j, (decodedTree (a.prime.data.tree β) (nodeSign a.prime.skeleton.sig β.1)).tree j = TTree.leaf)
    (ts : Fin 2 → ℝ) (k : Mom d) :
    MkSlotsI.genSlotKer L γ δ p a J pat t s σ kSel Rs h roots (fun _ => none) none (.inr β) ts k = 1 := by
  set D := a.prime.data
  set hS := a.prime.prime.1
  set LGc := nativeChainLayered D hS (sourceLayer a) (sourceLayer_isLayering a) β with hLGc
  have hT' : ∀ j, LGc.garden.tree j = TTree.leaf := hT
  have hE := isEmpty_branch_of_leaves hT'
  -- the unique native node is the lone leaf, whose context node is the core of `β`
  have hcore : ∀ z : GNode (decodedTree (D.tree β) (nodeSign a.prime.skeleton.sig β.1)).tree,
      chainContextNode D hS β z = (D.coreBranch hS β).toNode := fun z => by
    have hz : z = (chainLoneLeaf (D.tree β) (nodeSign a.prime.skeleton.sig β.1)).toNode :=
      (node_root_of_leaves hT z).trans ((congrArg (GNode.root _) (Subsingleton.elim _ _)).trans
        (node_root_of_leaves hT _).symm)
    rw [hz]
    exact chainContextNode_lone D hS β
  have hΘ : (MkSlotsI.genΘs D hS (sourceLayer a) (sourceLayer_isLayering a) J L σ kSel Rs (.inr β) k :
      NativeRelativeDecoration D hS d (.inr β) → ℂ) = fun _ => 1 := by
    funext κ
    unfold MkSlotsI.genΘs
    refine Finset.prod_eq_one fun z _ => ?_
    have hc : ∃ β' : GBranch a.prime.skeleton.tree, chainContextNode D hS β z = (D.coreBranch hS β').toNode :=
      ⟨β, hcore z⟩
    simp only [hc, ↓reduceIte]
  unfold MkSlotsI.genSlotKer
  dsimp only [MkSlotsB.slotFnGWFRL]
  rw [hΘ]
  refine ((MkSlotsB.kernelNodeWR_one_eq L γ δ LGc _ _ _ (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 _
    (fun τ _ => ?_)).trans (kernelNodeWF_noBranch L γ δ LGc hT' _ _ _ _ _ _ _ _)).trans ?_
  · simp only [MkSlotsB.kDomainR, kDomain, Set.mem_ofPred_eq, IsEmpty.forall_iff, iff_true]
    trivial
  -- the closed form
  have hord : LGc.garden.order = 0 := by
    unfold Garden.order
    exact Finset.sum_eq_zero fun j _ => by rw [hT' j]; rfl
  have hz : LGc.garden.zeta = 1 := by unfold Garden.zeta; exact Finset.prod_of_isEmpty _
  have hsub := genDecoration_subsingleton LGc.garden hT' (fun _ => (0 : Fin d → ℤ)) 0
  have κ₀ : GenDecoration LGc.garden d (fun _ => (0 : Fin d → ℤ)) 0 :=
    ⟨fun _ => 0, ⟨fun _ => by simp, fun _ => rfl⟩, fun _ => rfl, fun _ _ => rfl⟩
  have hin : inputLeaves LGc.garden = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr fun ℓ _ => ?_
    rintro ⟨-, hm⟩
    have hℓ : ℓ.1.2 = (D.tree β).lonePath := by
      have h1 := ℓ.2
      rw [hT' ℓ.1.1] at h1
      have h2 := (chainLoneLeaf (D.tree β) (nodeSign a.prime.skeleton.sig β.1)).2
      rw [show chainTreeForest (D.tree β) (nodeSign a.prime.skeleton.sig β.1)
          (chainLoneLeaf (D.tree β) (nodeSign a.prime.skeleton.sig β.1)).1.1 = TTree.leaf from
            hT (chainLoneLeaf (D.tree β) (nodeSign a.prime.skeleton.sig β.1)).1.1] at h2
      simp only [TTree.leaves, Finset.mem_singleton] at h1 h2
      rw [h1]
      exact h2.symm
    have hl := (decodesTree_lone_iff (decodedTree_decodes (D.tree β) (nodeSign a.prime.skeleton.sig β.1)) ℓ).mpr hℓ
    change LGc.garden.mark ℓ = some MarkTag.lower at hl
    rw [hl] at hm
    simp at hm
  unfold kerNoBranch
  rw [hord, hz, pow_zero, one_mul, one_mul, tsum_eq_single κ₀ (fun κ hκ => (hκ (Subsingleton.elim _ _)).elim)]
  have he : epsDec LGc.garden κ₀.1 = 1 := by unfold epsDec; exact Finset.prod_of_isEmpty _
  rw [he, hin, Finset.prod_empty, Complex.ofReal_one, one_mul, mul_one, mul_one]
  exact Finset.prod_eq_one fun z _ => chainW_none D hS _ _ L γ δ p s J _ _

/-- **S1's obstruction on a nil-chain slot.** If the slot box contains a point `ts₀` and `d ≥ 1`, there is no
ball-localized family with summable weights representing `genSlotKer … (.inr β) ts₀ k` at every momentum `k`. -/
theorem not_genSlotConclusion_nilChain (hd : 1 ≤ d) (L γ δ : ℝ) (p : ℕ) (a : PrescribedPrimeGarden w)
    (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ)) (β : GBranch a.prime.skeleton.tree)
    (hT : ∀ j, (decodedTree (a.prime.data.tree β) (nodeSign a.prime.skeleton.sig β.1)).tree j = TTree.leaf)
    (ts₀ : Fin 2 → ℝ) :
    ¬ ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (c : Λ → Fin d → ℤ)
      (amp : Λ → Mom d → ℂ),
      (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l k, ‖amp l k‖ ≤ 1) ∧
      (∀ l k, amp l k ≠ 0 → ‖k - latPt d (c l)‖ ≤ 1) ∧
      ∀ k : Mom d, HasSum (fun l => (wt l : ℂ) * amp l k * fsPhase (m l) ts₀)
        (MkSlotsI.genSlotKer L γ δ p a J pat t s σ kSel Rs h roots (fun _ => none) none (.inr β) ts₀ k) := by
  rintro ⟨Λ, _, wt, m, c, amp, hw0, hws, hamp1, hsupp, hsum⟩
  refine not_localized_of_norm_ge hd wt c amp (fun l => fsPhase (m l) ts₀)
    (fun l => (Represents.fsPhase_norm (m l) ts₀).le) hw0 hws hamp1 hsupp
    (fun k => MkSlotsI.genSlotKer L γ δ p a J pat t s σ kSel Rs h roots (fun _ => none) none (.inr β) ts₀ k)
    one_pos (fun k => ?_) hsum
  rw [genSlotKer_nilChain L γ δ p a J pat t s σ kSel Rs h roots β hT ts₀ k, norm_one]

end WaveTurbulence.Flower.MkSlotsO
