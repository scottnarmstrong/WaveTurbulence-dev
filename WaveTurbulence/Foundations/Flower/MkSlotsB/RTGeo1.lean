/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoLb
public import WaveTurbulence.Foundations.Flower.MkSlots.CapGeoQ
public import WaveTurbulence.Foundations.Flower.ProtGeo.Sel

/-! # B3s-HELPER3 B5(ii) geometry (R188), part 1: below a root-trace root there is no capped flower

* `NoFlowerBelow LG J x`: no capped flower lies at or below the node `x`;
* **`pinned_below_eq`**: below such an `x` the only branch that can be pinned (any pattern) is `x` itself, and
  `pinned_dChild`: a pinned non-root such branch is pinned by a `dChild` pattern; nodes below `x` are off the capped
  stems (`NoFlowerBelow.not_onCapStem`);
* `noFlowerBelow_child`: below a branching child `r` of a capped flower parent `F` other than its flower there is no
  capped flower (one capped flower per tree), and `fixCap_child_dChild`: under `dChild i`, child `i` is pinned at `s`;
* on a reconstruction: `noFlowerBelow_root_of_notCap` (the roots of the native couple of a non-cap pair),
  `notCap_of_root` (the leaf pair whose root is `r` is not a cap pair), `root_nonroot_of_notCap` (its roots are not
  garden roots, with `|J| = R`);
* `rootTraceSlot_geom`: the shape of a root-trace slot (chain slot of a nontrivial chain, or leaf-pair slot), from
  the data of `RootTraceSlot`;
* `RTRec`: the hypotheses of `GenSlotObligationAt` transported to the reconstruction `recLG a`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open Set
open WaveTurbulence WaveTurbulence.LGSpine TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntGeo
open WaveTurbulence.Flower.MkSlots.IntRest

namespace WaveTurbulence.Flower.MkSlotsB

/-! ## No capped flower below a node -/

section Generic
variable {w : ℕ} {LG : LayeredGarden w} {J : Finset (Fin w)}

/-- No capped flower lies at or below `x`. -/
def NoFlowerBelow (LG : LayeredGarden w) (J : Finset (Fin w)) (x : GNode LG.garden.tree) : Prop :=
  ∀ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ → ¬ x.IsDesc ℓ.toNode

theorem isDesc_trans {T : Fin w → TTree} {x y z : GNode T} (h1 : x.IsDesc y) (h2 : y.IsDesc z) : x.IsDesc z :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem isDesc_refl {T : Fin w → TTree} (x : GNode T) : x.IsDesc x := ⟨rfl, List.prefix_refl _⟩

theorem cfp_isDesc_flower {b : GBranch LG.garden.tree} (hb : IsCapFlowerParent LG J b) :
    ∃ ℓ, IsCapFlower LG J ℓ ∧ b.toNode.IsDesc ℓ.toNode := by
  obtain ⟨ℓ, hℓ, h1, i, h2⟩ := hb
  exact ⟨ℓ, hℓ, h1.symm, ⟨[i], h2.symm⟩⟩

theorem NoFlowerBelow.mono {x y : GNode LG.garden.tree} (hx : NoFlowerBelow LG J x) (h : x.IsDesc y) :
    NoFlowerBelow LG J y :=
  fun ℓ hℓ hy => hx ℓ hℓ (isDesc_trans h hy)

theorem NoFlowerBelow.not_cfp {x : GNode LG.garden.tree} (hx : NoFlowerBelow LG J x) {b : GBranch LG.garden.tree}
    (hb : x.IsDesc b.toNode) : ¬ IsCapFlowerParent LG J b := by
  intro hc
  obtain ⟨ℓ, hℓ, hd⟩ := cfp_isDesc_flower hc
  exact hx ℓ hℓ (isDesc_trans hb hd)

theorem NoFlowerBelow.not_onCapStem {x : GNode LG.garden.tree} (hx : NoFlowerBelow LG J x)
    {z : GNode LG.garden.tree} (hz : x.IsDesc z) : ¬ OnCapStem LG J z := by
  rintro ⟨ℓ, hℓ, hd⟩
  exact hx ℓ hℓ (isDesc_trans hz hd)

/-- **Below a node with no capped flower below, the only branch that can be pinned is the node itself.** -/
theorem pinned_below_eq {pat : Fin w → FixPat} {t s : ℝ} {x : GNode LG.garden.tree} (hx : NoFlowerBelow LG J x)
    {b : GBranch LG.garden.tree} (hb : x.IsDesc b.toNode) (hpin : (fixCap LG J pat t s b).isSome) :
    b.toNode = x := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hpin
  rcases fixCap_cases hv with ⟨hc, -⟩ | ⟨-, -, h0, -⟩ | ⟨-, -, ⟨C, hC, hCb⟩, -⟩ | ⟨i, -, -, ⟨C, hC, h1, h2⟩, -⟩
  · exact absurd hc (hx.not_cfp hb)
  · apply Subtype.ext
    refine Prod.ext hb.1.symm ?_
    have h3 : x.1.2 <+: b.1.2 := hb.2
    show b.1.2 = x.1.2
    rw [h0] at h3 ⊢
    exact (List.prefix_nil.mp h3).symm
  · exfalso
    obtain ⟨g1, k, g2⟩ := hCb
    refine hx.not_cfp ⟨hb.1.trans g1.symm, ?_⟩ hC
    show x.1.2 <+: C.1.2
    rw [g2]
    exact hb.2.trans (List.prefix_append _ _)
  · have h3 : x.1.2 <+: C.1.2 ++ [i] := by rw [← h2]; exact hb.2
    rcases List.prefix_concat_iff.mp h3 with h4 | h4
    · apply Subtype.ext
      exact Prod.ext hb.1.symm (h2.trans h4.symm)
    · exact absurd hC (hx.not_cfp ⟨hb.1.trans h1, h4⟩)

/-- A pinned non-root branch with no capped flower below is pinned by a `dChild` pattern. -/
theorem pinned_dChild {pat : Fin w → FixPat} {t s : ℝ} {b : GBranch LG.garden.tree}
    (hx : NoFlowerBelow LG J b.toNode) (hnr : b.1.2 ≠ []) (hpin : (fixCap LG J pat t s b).isSome) :
    ∃ i, pat b.1.1 = FixPat.dChild i := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hpin
  rcases fixCap_cases hv with ⟨hc, -⟩ | ⟨-, -, h0, -⟩ | ⟨-, -, ⟨C, hC, hCb⟩, -⟩ | ⟨i, -, hp, -, -⟩
  · exact absurd hc (hx.not_cfp (isDesc_refl _))
  · exact absurd h0 hnr
  · exfalso
    obtain ⟨g1, k, g2⟩ := hCb
    exact hx.not_cfp ⟨g1.symm, ⟨[k], g2.symm⟩⟩ hC
  · exact ⟨i, hp⟩

/-- **Below a branching child `r` of a capped flower parent there is no capped flower.** -/
theorem noFlowerBelow_child {p : ℕ} (hG : CapGeo LG J p) {F r : GBranch LG.garden.tree}
    (hF : IsCapFlowerParent LG J F) (i : Fin 3) (hr : r.toNode = F.child i) : NoFlowerBelow LG J r.toNode := by
  intro ℓ hℓ hd
  obtain ⟨f, hf, f1, i', f2⟩ := hF
  have hv := congrArg Subtype.val hr
  have r1 : r.1.1 = F.1.1 := by have h := congrArg Prod.fst hv; exact h
  have r2 : r.1.2 = F.1.2 ++ [i] := by have h := congrArg Prod.snd hv; exact h
  have hd1 : ℓ.1.1 = r.1.1 := hd.1.symm
  have hd2 : r.1.2 <+: ℓ.1.2 := hd.2
  have he : ℓ = f := hG.one_flower ℓ f hℓ hf (hd1.trans (r1.trans f1.symm))
  rw [he, r2, f2] at hd2
  have heq : F.1.2 ++ [i] = F.1.2 ++ [i'] := hd2.eq_of_length (by simp)
  have hrl : r.toNode = f.toNode :=
    Subtype.ext (Prod.ext (r1.trans f1.symm) (show r.1.2 = f.1.2 by rw [r2, f2, heq]))
  exact VineB.SpliceShape.leaf_ne_branch hrl.symm

/-- Under `dChild i`, child `i` of the capped flower parent is pinned at `s`. -/
theorem fixCap_child_dChild {p : ℕ} (hG : CapGeo LG J p) {pat : Fin w → FixPat} (t s : ℝ)
    {F r : GBranch LG.garden.tree} (hF : IsCapFlowerParent LG J F) {i : Fin 3} (hp : pat F.1.1 = FixPat.dChild i)
    (hr : r.toNode = F.child i) : fixCap LG J pat t s r = some s := by
  have hv := congrArg Subtype.val hr
  have r1 : r.1.1 = F.1.1 := by have h := congrArg Prod.fst hv; exact h
  have r2 : r.1.2 = F.1.2 ++ [i] := by have h := congrArg Prod.snd hv; exact h
  have hnc : ¬ IsCapFlowerParent LG J r := (noFlowerBelow_child hG hF i hr).not_cfp (isDesc_refl _)
  have hp' : pat r.1.1 = FixPat.dChild i := r1 ▸ hp
  have hex : ∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ r.1.1 = c.1.1 ∧ r.1.2 = c.1.2 ++ [i] :=
    ⟨F, hF, r1, r2⟩
  unfold fixCap
  simp only [hnc, ↓reduceIte, hp', hex]

end Generic

/-! ## On a reconstruction -/

section Rec
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w))

/-- The tree of a root of a native couple is that of its skeleton leaf. -/
theorem nativeRoot_fst (q : SourcePair S) (k : Fin 2) :
    ((nativeCoupleForest D hS q).root k).1.1 = (if k = 0 then (q.firstLeaf hS).1.1 else (q.secondLeaf hS).1.1) := by
  fin_cases k
  · exact inflatedPosition_index S D.tree _
  · exact inflatedPosition_index S D.tree _

theorem root_tree_not_cap {q : SourcePair S} (hnc : ¬ IsCapPair S hS J q) (k : Fin 2) :
    ((nativeCoupleForest D hS q).root k).1.1 ∉ J := by
  rw [nativeRoot_fst]
  intro h
  apply hnc
  fin_cases k
  · exact Or.inl h
  · exact Or.inr h

/-- **No capped flower below a root of the native couple of a non-cap pair** (the partner of a capped flower is a
cap root, and native couples are closed under the pairing). -/
theorem noFlowerBelow_root_of_notCap {q : SourcePair S} (hnc : ¬ IsCapPair S hS J q) (k : Fin 2) :
    NoFlowerBelow (layeredReconstruction D hS layer hLayer) J ((nativeCoupleForest D hS q).root k) := by
  intro ℓ hℓ hd
  have hmem : ℓ ∈ Comb.RootedSubforest.leafSet (G := D.garden hS) (nativeCoupleForest D hS q) :=
    (Comb.RootedSubforest.mem_leafSet_iff (G := D.garden hS) _ ℓ).mpr ⟨k, hd⟩
  have hpm := (nativeCoupleForest_closed D hS q ℓ hmem).2
  obtain ⟨k', hk'⟩ := (Comb.RootedSubforest.mem_leafSet_iff (G := D.garden hS) _ _).mp hpm
  have h1 : ((nativeCoupleForest D hS q).root k').1.1 = ((D.garden hS).pair ℓ).1.1 := hk'.1
  exact root_tree_not_cap D hS J hnc k' (h1 ▸ hℓ.2)

/-- **The leaf pair whose root (on the side of `σ`) is a branch `r` with no capped flower below is not a cap pair.** -/
theorem notCap_of_root (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf) (σ : GLeaf S.tree)
    (r : GBranch (D.forest hS)) (hr : r.toNode = attachedNode D hS σ.toNode) (hσJ : σ.1.1 ∉ J)
    (hNF : NoFlowerBelow (layeredReconstruction D hS layer hLayer) J r.toNode) :
    ¬ IsCapPair S hS J (pairOfLeaf S hS σ) := by
  intro hcp
  have hpJ : (S.pair σ).1.1 ∈ J := (isCapPair_pairOfLeaf hS J σ hcp).resolve_left hσJ
  set j1 := (S.pair σ).1.1 with hj1
  have hj : D.forest hS j1 = TTree.leaf := hcap _ hpJ
  have hpnil : (S.pair σ).1.2 = [] := IntCore.skel_path_nil D hS hj (S.pair σ) rfl
  have hroot' : attachedNode D hS (S.pair σ).toNode = GNode.root (D.forest hS) j1 := by
    have he : (S.pair σ).toNode = GNode.root S.tree j1 := Subtype.ext (Prod.ext rfl hpnil)
    rw [he]; exact attachedNode_root D hS j1
  let ℓc : GLeaf (D.garden hS).tree :=
    ⟨(j1, []), by show [] ∈ (D.forest hS j1).leaves; rw [hj]; simp [TTree.leaves]⟩
  obtain ⟨k1, hk1⟩ := exists_nativeRoot_eq D hS σ (S.pair σ) (Or.inr rfl)
  have hmem : ℓc ∈ Comb.RootedSubforest.leafSet (G := D.garden hS) (nativeCoupleForest D hS (pairOfLeaf S hS σ)) := by
    refine (Comb.RootedSubforest.mem_leafSet_iff (G := D.garden hS) _ ℓc).mpr ⟨k1, ?_⟩
    rw [hk1, hroot']
    exact ⟨rfl, List.nil_prefix⟩
  obtain ⟨hne, hpm⟩ := nativeCoupleForest_closed D hS _ ℓc hmem
  obtain ⟨k, hk⟩ := (Comb.RootedSubforest.mem_leafSet_iff (G := D.garden hS) _ _).mp hpm
  rcases nativeRoot_cases D hS σ k with he | he
  · -- the partner of the cap root is a capped flower below `r`
    rw [he, ← hr] at hk
    have hfl : IsCapFlower (layeredReconstruction D hS layer hLayer) J ((D.garden hS).pair ℓc) := by
      refine ⟨?_, ?_⟩
      · have e1 : ((D.garden hS).pair ℓc).1.1 = r.1.1 := hk.1.symm
        have e2 : r.1.1 = σ.1.1 := by
          have := congrArg (fun z : GNode (D.forest hS) => z.1.1) hr
          exact this.trans (inflatedPosition_index S D.tree σ.toNode)
        show ((D.garden hS).pair ℓc).1.1 ∉ J
        rw [e1, e2]; exact hσJ
      · show ((D.garden hS).pair ((D.garden hS).pair ℓc)).1.1 ∈ J
        rw [(D.garden hS).pair_pair]; exact hpJ
    exact hNF _ hfl hk
  · -- the partner would be in the single-leaf tree `j1`
    rw [he, hroot'] at hk
    apply hne
    apply Subtype.ext
    have h1 : ((D.garden hS).pair ℓc).1.1 = j1 := hk.1.symm
    have h2 := ((D.garden hS).pair ℓc).2
    have hj' : (D.garden hS).tree j1 = TTree.leaf := hcap _ hpJ
    rw [h1, hj'] at h2
    simp only [TTree.leaves, Finset.mem_singleton] at h2
    exact Prod.ext h1 h2

/-- The roots of the native couple of a non-cap pair are not garden roots (with every non-cap tree carrying a capped
flower). -/
theorem root_nonroot_of_notCap {q : SourcePair S} (hnc : ¬ IsCapPair S hS J q)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf (layeredReconstruction D hS layer hLayer).garden.tree,
      IsCapFlower (layeredReconstruction D hS layer hLayer) J ℓ ∧ ℓ.1.1 = j) (k : Fin 2) :
    ((nativeCoupleForest D hS q).root k).1.2 ≠ [] := by
  intro h0
  obtain ⟨ℓ, hℓ, hℓj⟩ := hroot _ (root_tree_not_cap D hS J hnc k)
  exact noFlowerBelow_root_of_notCap D hS layer hLayer J hnc k ℓ hℓ ⟨hℓj.symm, by rw [h0]; exact List.nil_prefix⟩

/-- The node of a native couple branch lies below its root. -/
theorem root_isDesc_emb (q : SourcePair S) (c : GBranch (nativeCoupleForest D hS q).shape) :
    ((nativeCoupleForest D hS q).root c.1.1).IsDesc (subforestBranchEmbedding (nativeCoupleForest D hS q) c).toNode :=
  ⟨rfl, List.prefix_append _ _⟩

/-- The node of a native couple node lies below its root. -/
theorem root_isDesc_node (q : SourcePair S) (z : GNode (nativeCoupleForest D hS q).shape) :
    ((nativeCoupleForest D hS q).root z.1.1).IsDesc ((nativeCoupleForest D hS q).nodeEmbedding z) :=
  ⟨rfl, List.prefix_append _ _⟩

end Rec

/-! ## The prescribed point: transported hypotheses and the shape of a root-trace slot -/

section Point
variable {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)

/-- The hypotheses of `GenSlotObligationAt` used here, on the reconstruction `recLG a`. -/
structure RTRec : Prop where
  can : IsCanonGC (p + 1) (recLG a)
  geo : CapGeo (recLG a) J p
  patv : CapPatValid (recLG a) J pat p
  root : ∀ j ∉ J, ∃ ℓ : GLeaf (recLG a).garden.tree, IsCapFlower (recLG a) J ℓ ∧ ℓ.1.1 = j
  cap : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf

theorem rtRec_of (hcan : IsCanonGC (p + 1) a.layered) (hJ : J.card = R) (hG : CapGeo a.layered J p)
    (hpat : CapPatValid a.layered J pat p) (hirr : a.layered.garden.Irreducible) : RTRec (p := p) a J pat := by
  have hrec : recLG a = a.layered := sourceLayer_reconstructs a
  have hpl : a.layered.garden.IsPlain := hcan.1
  have hroot := exists_capFlower_of_capGeo hG hpl hirr (by rw [hJ])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hrec]; exact hcan
  · rw [hrec]; exact hG
  · rw [hrec]; exact hpat
  · rw [hrec]; exact hroot
  · intro j hj
    have h := congrArg (fun LG : LayeredGarden (2 * R) => LG.garden.tree j) hrec
    exact h.trans (hG.cap_leaf j hj)

/-- **The shape of a root-trace slot**: the pinned branch `r` is attached at the skeleton child `β.child i` of the
core capped flower parent; it is the top of a nontrivial chain (chain slot) or a root of a native couple (leaf-pair
slot). -/
theorem rootTraceSlot_geom {sl : ReplacementSlot a.prime.skeleton} (β : GBranch a.prime.skeleton.tree) (i : Fin 3)
    (r : GBranch (a.prime.data.forest a.prime.prime.1))
    (hr : r.toNode = (a.prime.data.coreBranch a.prime.prime.1 β).child i)
    (hnc : ∀ β' : GBranch a.prime.skeleton.tree, (a.prime.data.coreBranch a.prime.prime.1 β').toNode ≠ r.toNode)
    (hs : MkSlots.slotOf a.prime.data a.prime.prime.1 r.toNode = sl) :
    r.toNode = attachedNode a.prime.data a.prime.prime.1 (β.child i) ∧
      ((∃ γ' : GBranch a.prime.skeleton.tree, γ'.toNode = β.child i ∧ (a.prime.data.tree γ').lonePath ≠ [] ∧
          r.1 = inflatedPosition a.prime.skeleton a.prime.data.tree γ'.toNode ∧ sl = .inr γ') ∨
        (∃ σ : GLeaf a.prime.skeleton.tree, σ.toNode = β.child i ∧
          sl = .inl (pairOfLeaf a.prime.skeleton a.prime.prime.1 σ))) := by
  have hr' : r.toNode = attachedNode a.prime.data a.prime.prime.1 (β.child i) := by
    rw [attachedNode_child]; exact hr
  refine ⟨hr', ?_⟩
  rcases attachedTop_of_eq a.prime.data a.prime.prime.1 _ r hr' with ⟨b', hb', -, he⟩ | ⟨b', hb', h0, h1, h2⟩ |
    ⟨σ, hσ, -, h2⟩
  · exact absurd (congrArg GBranch.toNode he).symm (hnc b')
  · exact Or.inl ⟨b', hb', h0, h1, hs.symm.trans h2⟩
  · exact Or.inr ⟨σ, hσ, hs.symm.trans h2⟩

end Point

end WaveTurbulence.Flower.MkSlotsB
