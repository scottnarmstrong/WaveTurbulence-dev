/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapT
public import WaveTurbulence.Foundations.Flower.MkSlots.IntMember1

/-! # B3s MK-SLOTS (integration, R-cap): the pinned cap slot kernels are common to the run class

For a cap pair `q` of `G_sb` and a member `y` of the run class of the representative `a`, the pinned weighted cap slot
kernel of `y` at its slot `Φ_y.iota (.inl q)` is the representative's `capSlotKer` at `Φ_a.iota (.inl q)`
(`member_capSlot`). Both are `IntCapT.capT_kernel` of their native couple (`capT_slot_eq`), and
* the native couples coincide (the native-couple chain, `memShape_nativeCouple`);
* the root tree indices are those of the `G_sb` leaves (`SpliceShape.tree_eq`);
* the last address letters agree when the flower-side leaf has a non-hinge parent in `G_sb` (it is then the same
  child of the same `G_sb` atom); when the parent is a hinge, the couple is not trivial on the flower side
  (`rep_hinge_not_attLeaf`), so no root is a capped flower and the kernel does not read the last letters
  (`capT_kernel_rl_indep`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine

namespace WaveTurbulence.Flower.MkSlots.IntCapM

open WaveTurbulence.Flower.MkSlots.IntCapT WaveTurbulence.Flower.MkSlots.IntCore
  WaveTurbulence.Flower.MkSlots.IntMember

/-- **The couple kernel does not read the last root letters when no root is a capped flower.** -/
theorem capT_kernel_rl_indep {w d : ℕ} (L γ δ : ℝ) (p : ℕ) (s : ℝ) (J : Finset (Fin w))
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ)) (Rf : Fin w → Option ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) (N : LayeredGarden 2) (ri : Fin 2 → Fin w)
    (hno : ∀ (a : GNode N.garden.tree), a.1.2 = [] → ¬ ∃ l : GLeaf N.garden.tree, capT_IsFl N ri J l ∧ l.toNode = a)
    (rl rl' : Fin 2 → Option (Fin 3)) :
    capT_kernel L γ δ p s J h roots Rf dag N ri rl = capT_kernel L γ δ p s J h roots Rf dag N ri rl' := by
  have hch : ∀ cc a (x : Mom d), capT_ch L γ δ s J cc N ri rl a x = capT_ch L γ δ s J cc N ri rl' a x := by
    intro cc a x
    unfold capT_ch
    by_cases ha : a.1.2 = []
    · rw [dif_pos ha, dif_pos ha]
      have h1 : ∀ o : Option (Fin 3), o.elim 1 (fun i =>
          if ∃ l : GLeaf N.garden.tree, capT_IsFl N ri J l ∧ l.toNode = a then
            Complex.exp (((-(capT_theta L γ δ s (if i = 1 then -N.garden.sign a else N.garden.sign a) *
              childSign i * ‖x‖ ^ 2) : ℝ) : ℂ) * Complex.I) else 1) = 1 := by
        intro o
        cases o with
        | none => rfl
        | some i => exact if_neg (hno a ha)
      rw [h1, h1]
    · rw [dif_neg ha, dif_neg ha]
  funext ts k
  unfold capT_kernel
  congr 2
  funext k'
  refine Finset.prod_congr rfl fun a _ => ?_
  unfold capT_nodeW capT_dag
  cases dag with
  | none => rfl
  | some cc => simp only [Option.elim, hch cc a]

/-! ### Through a splice shape -/

section Shape
variable {w : ℕ} {S : Garden w} {Ju : Type} [Fintype Ju] [DecidableEq Ju] {blk : Ju → CLBlock S}
  {G : Garden w} (Φ : SpliceShape blk G) (D : ReconstructionData S) (hS : S.IsPlain) (hG : G.IsPlain)

/-- The root of the native couple of the image of a `G_sb` pair, on side `c`. -/
theorem coupleRoot_iota_val (q : SourcePair G) (c : Fin 2) :
    coupleRoot D hS (pairOfLeaf S hS (Φ.leaf (q.firstLeaf hG))) c =
      inflatedPosition S D.tree (Φ.leaf (if c = 0 then q.firstLeaf hG else q.secondLeaf hG)).toNode := by
  unfold coupleRoot
  fin_cases c
  · simp only [Fin.zero_eta, Fin.isValue, if_true]
    rw [Φ.iota_first hS hG q]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false]
    rw [Φ.iota_second hS hG q]

theorem coupleRoot_iota_idx (q : SourcePair G) (c : Fin 2) :
    (coupleRoot D hS (pairOfLeaf S hS (Φ.leaf (q.firstLeaf hG))) c).1 =
      (if c = 0 then q.firstLeaf hG else q.secondLeaf hG).1.1 := by
  rw [coupleRoot_iota_val Φ D hS hG q c]
  exact (inflatedPosition_index S D.tree _).trans (leaf_fst Φ _)

/-- The last letter of the inflated position of the image of a root `G_sb` leaf. -/
theorem getLast_root (ℓ : GLeaf G.tree) (hℓ : ℓ.1.2 = []) :
    (inflatedPosition S D.tree (Φ.leaf ℓ).toNode).2.getLast? = none := by
  have h1 : (Φ.leaf ℓ).1.2 = [] := by
    have := (Φ.root_iff ℓ.toNode).mpr hℓ
    rw [← Φ.leaf_node] at this
    exact this
  have he : (Φ.leaf ℓ).toNode = GNode.root S.tree (Φ.leaf ℓ).1.1 := Subtype.ext (Prod.ext rfl h1)
  rw [he, inflatedPosition_root]
  rfl

include hS in
/-- The last letter of the inflated position of the image of a child of a non-hinge `G_sb` atom. -/
theorem getLast_child (ℓ : GLeaf G.tree) (c : GBranch G.tree) (i : Fin 3) (hℓ : ℓ.toNode = c.child i)
    (hh : ∀ j, Φ.br c ≠ (blk j).upper) :
    (inflatedPosition S D.tree (Φ.leaf ℓ).toNode).2.getLast? = some i := by
  have h1 : (Φ.leaf ℓ).toNode = (Φ.br c).child i := by rw [Φ.leaf_node, hℓ]; exact Φ.child c i hh
  have h2 : inflatedPosition S D.tree (Φ.leaf ℓ).toNode = ((D.coreBranch hS (Φ.br c)).child i).1 := by
    rw [h1]
    exact congrArg Subtype.val (attachedNode_child D hS (Φ.br c) i)
  rw [h2]
  show ((D.coreBranch hS (Φ.br c)).1.2 ++ [i]).getLast? = some i
  simp

end Shape

/-! ### The run class -/

section Class
variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R)))
  (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
  (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))

include hcapA hrepU in
/-- **The pinned cap slot kernels are common to the run class.** -/
theorem member_capSlot {d : ℕ}
    (hGeoA : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
      J p)
    (hGeoY : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p)
    (q : SourcePair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G)
    (hq : IsCapPair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G hG J q)
    (L γ δ : ℝ) (t s : ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom d)) :
    slotFnNWF y.1.data y.1.plain L γ δ
        (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) h L
          roots)
        (capNodeW L γ δ p s (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
          Rf dag) (stateLayer y.1) (stateLayer_isLayering y.1)
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
          (fun _ => FixPat.plain) t s)
        ((memShape a mk y hy).iota y.1.plain hG (.inl q)) =
      capSlotKer L γ δ p a J t s h roots Rf dag
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
          (.inl q)) := by
  set Φy := memShape a mk y hy with hΦy
  set Φa := stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) with hΦa
  have hqy : IsCapPair y.1.skeleton y.1.plain J (pairOfLeaf y.1.skeleton y.1.plain (Φy.leaf (q.firstLeaf hG))) :=
    (isCapPair_iota Φy y.1.plain hG J q).mpr hq
  have hqa : IsCapPair a.prime.skeleton a.prime.prime.1 J
      (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG))) :=
    (isCapPair_iota Φa a.prime.prime.1 hG J q).mpr hq
  funext ts k
  show slotFnNWF y.1.data y.1.plain L γ δ _ _ (stateLayer y.1) (stateLayer_isLayering y.1) _
      (.inl (pairOfLeaf y.1.skeleton y.1.plain (Φy.leaf (q.firstLeaf hG)))) ts k =
    slotFnNWF a.prime.data a.prime.prime.1 L γ δ _ _ (sourceLayer a) (sourceLayer_isLayering a) _
      (.inl (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG)))) ts k
  rw [capT_slot_eq y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J p _ hqy hGeoY L γ δ t s h roots
      Rf dag ts k,
    capT_slot_eq a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J p _ hqa hGeoA L γ δ t s
      h roots Rf dag ts k,
    memShape_nativeCouple a mk y hy hG q]
  have hidx : (fun c => (coupleRoot y.1.data y.1.plain
        (pairOfLeaf y.1.skeleton y.1.plain (Φy.leaf (q.firstLeaf hG))) c).1) =
      fun c => (coupleRoot a.prime.data a.prime.prime.1
        (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG))) c).1 := by
    funext c
    rw [coupleRoot_iota_idx Φy y.1.data y.1.plain hG q c, coupleRoot_iota_idx Φa a.prime.data a.prime.prime.1 hG q c]
  rw [hidx]
  -- the last letters: equal, or not read
  -- the flower-side leaf of `q`
  have hside : ∀ c : Fin 2, ((if c = 0 then q.firstLeaf hG else q.secondLeaf hG).1.1 ∈ J) ∨
      ((stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.pair
        (if c = 0 then q.firstLeaf hG else q.secondLeaf hG)).1.1 ∈ J := by
    have hpair : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.pair (q.firstLeaf hG) = q.secondLeaf hG :=
      VineEstS4.pair_first_eq_second hG q
    intro c
    fin_cases c
    · simp only [Fin.zero_eta, Fin.isValue, if_true]
      rw [hpair]; exact hq
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false]
      have h2 : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.pair (q.secondLeaf hG) = q.firstLeaf hG := by
        rw [← hpair, (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.pair_pair]
      rw [h2]; exact hq.symm
  by_cases hall : ∀ c : Fin 2, (coupleRoot y.1.data y.1.plain
        (pairOfLeaf y.1.skeleton y.1.plain (Φy.leaf (q.firstLeaf hG))) c).2.getLast? =
      (coupleRoot a.prime.data a.prime.prime.1
        (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG))) c).2.getLast?
  · rw [funext hall]
  · -- some root address letter differs: the corresponding leaf has a hinge parent, so the couple is nontrivial there
    push_neg at hall
    obtain ⟨c₀, hc₀⟩ := hall
    set ℓ := (if c₀ = 0 then q.firstLeaf hG else q.secondLeaf hG) with hℓdef
    rw [coupleRoot_iota_val Φy y.1.data y.1.plain hG q c₀, coupleRoot_iota_val Φa a.prime.data a.prime.prime.1 hG q
      c₀] at hc₀
    have hnr : ℓ.1.2 ≠ [] := fun h0 => hc₀ ((getLast_root Φy y.1.data ℓ h0).trans
      (getLast_root Φa a.prime.data ℓ h0).symm)
    obtain ⟨i, hpi⟩ := VineB.child_parent ℓ.toNode hnr
    set cp := ℓ.toNode.parent hnr
    have hhinge : ∃ j, Φa.br cp = (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
        j).upper := by
      by_contra hnh
      push_neg at hnh
      have hnhy : ∀ j, Φy.br cp ≠ (unitClBlock (y.2 j)).upper := fun j he =>
        (member_hinge_iff a mk y hy cp |>.mp ⟨j, he⟩).elim fun j' he' => hnh j' he'
      exact hc₀ ((getLast_child Φy y.1.data y.1.plain ℓ cp i hpi.symm hnhy).trans
        (getLast_child Φa a.prime.data a.prime.prime.1 ℓ cp i hpi.symm hnh).symm)
    -- `ℓ` is the flower-side leaf: a leaf of a cap tree has the empty path
    have hℓJ : ℓ.1.1 ∉ J := by
      intro hJ
      have h1 : (Φa.leaf ℓ).1.2 = [] :=
        skel_path_nil a.prime.data a.prime.prime.1 (hcapA _ hJ) (Φa.leaf ℓ) (leaf_fst Φa ℓ)
      have h2 := (Φa.root_iff ℓ.toNode).mp (by rw [← Φa.leaf_node]; exact h1)
      exact hnr h2
    have hpJ : ((stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.pair ℓ).1.1 ∈ J :=
      (hside c₀).resolve_left hℓJ
    have hnatt := rep_hinge_not_attLeaf a mk J hcapA hrepU cp hhinge i ℓ hpi.symm hpJ
    -- the native couple of `q` is not a leaf on the side `c₀`
    have hpq : pairOfLeaf (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G hG ℓ = q := by
      rw [hℓdef]
      split_ifs
      · exact pairOfLeaf_firstLeaf _ hG q
      · rw [← VineEstS4.pair_first_eq_second hG q, pairOfLeaf_partner, pairOfLeaf_firstLeaf]
    have hsc : (if q.firstLeaf hG = ℓ then (0 : Fin 2) else 1) = c₀ := by
      rw [hℓdef]
      fin_cases c₀
      · simp
      · have hne : q.firstLeaf hG ≠ q.secondLeaf hG := by
          rw [← VineEstS4.pair_first_eq_second hG q]
          exact fun he => (((stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.pair_eq_iff _).mp he.symm) (hG _)
        simp [hne]
    rw [attLeaf_shape_iff Φa a.prime.data a.prime.prime.1 hG ℓ, hpq, hsc] at hnatt
    -- the other side carries a cap root
    have hother : ∀ c : Fin 2, c ≠ c₀ →
        (if c = 0 then q.firstLeaf hG else q.secondLeaf hG) =
          (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.pair ℓ := by
      intro c hc
      rw [hℓdef]
      have hpair : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.pair (q.firstLeaf hG) = q.secondLeaf hG :=
        VineEstS4.pair_first_eq_second hG q
      fin_cases c₀ <;> fin_cases c
      · exact absurd rfl hc
      · simp [hpair]
      · simp only [Fin.zero_eta, Fin.isValue, if_true, Fin.mk_one, one_ne_zero, if_false]
        rw [← hpair, (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.pair_pair]
      · exact absurd rfl hc
    refine congrFun (congrFun (capT_kernel_rl_indep L γ δ p s J h roots Rf dag _ _ ?_ _ _) ts) k
    rintro x hx ⟨l, hfl, hlx⟩
    have hleaf : (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG)))).garden.tree x.1.1 = TTree.leaf := by
      have hl := l.2
      have hl1 : l.1.1 = x.1.1 := congrArg (fun z : GNode _ => z.1.1) hlx
      have hl2 : l.1.2 = x.1.2 := congrArg (fun z : GNode _ => z.1.2) hlx
      rw [hl1, hl2, hx] at hl
      cases ht : (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG)))).garden.tree x.1.1 with
      | leaf => rfl
      | node l' m' r' =>
        rw [ht] at hl
        simp [TTree.leaves, TTree.nil_notMem_pre] at hl
    by_cases hxc : x.1.1 = c₀
    · rw [hxc, nativeCoupleLayered_garden] at hleaf
      exact hnatt hleaf
    · apply hfl.1
      have hl1 : l.1.1 = x.1.1 := congrArg (fun z : GNode _ => z.1.1) hlx
      show (coupleRoot a.prime.data a.prime.prime.1 _ l.1.1).1 ∈ J
      rw [hl1, coupleRoot_iota_idx Φa a.prime.data a.prime.prime.1 hG q x.1.1, hother x.1.1 hxc]
      exact hpJ

end Class

end WaveTurbulence.Flower.MkSlots.IntCapM
