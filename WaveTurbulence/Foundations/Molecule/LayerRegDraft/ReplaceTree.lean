/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.Part2Tree
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.Replace

/-!
# TARGET Prop `layerreg1` (2): replacing a coherent regular tree

Replacing an embedded regular tree (root `a`, lone position `n`) by another one (same root, lone position
`n'`) moves the subtree at the lone position from `n` to `n'`: `shiftAddr n n'` is this move on addresses
(identity away from `n`).

* `OutAgreeT LG LG' a n n'`: outside the region of the tree, `LG'` is `LG` moved by `shiftAddr n n'` (nodes,
  leaves, layers, and partners of leaves).
* **`layerreg1_replace_tree`**: two plain layered gardens related this way, each carrying an embedded
  regular tree with the layering of part (1) (`TreePattern`), satisfy the canonicity criterion together
  (via the characterization `layerreg1_part2_tree`).
* **`layerreg1_replace_tree_canonG`**, **`layerreg1_replace_tree_canonC`**: TARGET's statement for
  `𝒢_{p+1}` and `𝒞_{p+1}`; plainness and irreducibility of `LG'` are derived.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

/-- **Move the subtree at `n` to `n'`** (other addresses are fixed). -/
def shiftAddr (n n' z : Fin w × Path) : Fin w × Path :=
  if Under n z then addrExt n' (z.2.drop n.2.length) else z

/-! ### Addresses -/

section Addr

variable {a n n' : Fin w × Path}

theorem shift_ext (s : Path) : shiftAddr n n' (addrExt n s) = addrExt n' s := by
  unfold shiftAddr
  rw [ite_pos_of (under_ext n s)]
  simp [addrExt]

theorem shift_of_not {z : Fin w × Path} (h : ¬ Under n z) : shiftAddr n n' z = z := by
  unfold shiftAddr; rw [ite_neg_of h]

theorem shift_self : shiftAddr n n' n = n' := by
  have := shift_ext (n := n) (n' := n') []
  rwa [addrExt_nil, addrExt_nil] at this

/-- Outside the region and not below `n`: not below `a`. -/
theorem not_under_root_of_out {z : Fin w × Path} (hz : ¬ InTree a n z) (h : ¬ Under n z) :
    ¬ Under a z := fun h' => hz ⟨h', h⟩

theorem out_shift {z : Fin w × Path} (hz : ¬ InTree a n z) :
    ¬ InTree a n' (shiftAddr n n' z) := by
  by_cases h : Under n z
  · obtain ⟨s, rfl⟩ := under_of_addrExt h
    rw [shift_ext]
    exact fun h' => h'.2 (under_ext _ _)
  · rw [shift_of_not h]
    exact fun h' => not_under_root_of_out hz h h'.1

theorem shift_shift (ha' : Under a n') {z : Fin w × Path} (hz : ¬ InTree a n z) :
    shiftAddr n' n (shiftAddr n n' z) = z := by
  by_cases h : Under n z
  · obtain ⟨s, rfl⟩ := under_of_addrExt h
    rw [shift_ext, shift_ext]
  · have hna := not_under_root_of_out hz h
    rw [shift_of_not h, shift_of_not (fun h' => hna (under_trans ha' h'))]

theorem shift_fst (ha : Under a n) (ha' : Under a n') (z : Fin w × Path) :
    (shiftAddr n n' z).1 = z.1 := by
  by_cases h : Under n z
  · obtain ⟨s, rfl⟩ := under_of_addrExt h
    rw [shift_ext]
    simp only [addrExt]
    exact ha'.1.symm.trans ha.1
  · rw [shift_of_not h]

/-- An address not below `a` sees a point below `a` iff it sees `a`. -/
theorem under_iff_root {a x z : Fin w × Path} (hx : ¬ Under a x) (hz : Under a z) :
    Under x z ↔ Under x a :=
  ⟨under_of_out hx hz, fun h => under_trans h hz⟩

/-- **The move preserves the order of the addresses outside the region.** -/
theorem under_shift (ha : Under a n) (ha' : Under a n') {x y : Fin w × Path} (hx : ¬ InTree a n x)
    (hy : ¬ InTree a n y) : Under x y ↔ Under (shiftAddr n n' x) (shiftAddr n n' y) := by
  by_cases hnx : Under n x <;> by_cases hny : Under n y
  · obtain ⟨s, rfl⟩ := under_of_addrExt hnx
    obtain ⟨t, rfl⟩ := under_of_addrExt hny
    rw [shift_ext, shift_ext, under_ext_iff, under_ext_iff]
  · obtain ⟨s, rfl⟩ := under_of_addrExt hnx
    have hya := not_under_root_of_out hy hny
    rw [shift_ext, shift_of_not hny]
    exact ⟨fun h => absurd (under_trans (under_trans ha (under_ext _ _)) h) hya,
      fun h => absurd (under_trans (under_trans ha' (under_ext _ _)) h) hya⟩
  · obtain ⟨t, rfl⟩ := under_of_addrExt hny
    have hxa := not_under_root_of_out hx hnx
    rw [shift_ext, shift_of_not hnx, under_iff_root hxa (under_trans ha (under_ext _ _)),
      under_iff_root hxa (under_trans ha' (under_ext _ _))]
  · rw [shift_of_not hnx, shift_of_not hny]

/-- **The move commutes with taking the parent** (outside the region, away from `n`). -/
theorem shift_parent (ha : Under a n) {z x : Fin w × Path} {k : Fin 3} (hz : ¬ InTree a n z)
    (hzn : z ≠ n) (e : z = addrExt x [k]) :
    ¬ InTree a n x ∧ shiftAddr n n' z = addrExt (shiftAddr n n' x) [k] := by
  by_cases h : Under n z
  · have hnx : Under n x := by
      refine ⟨h.1.trans (by rw [e]; rfl), ?_⟩
      have hx : x.2 <+: z.2 := by rw [e]; exact List.prefix_append _ _
      apply List.prefix_of_prefix_length_le h.2 hx
      have l1 : z.2.length = x.2.length + 1 := by rw [e]; simp [addrExt]
      by_contra hl
      have : n.2.length = z.2.length := by
        have := h.2.length_le; omega
      exact hzn (Prod.ext h.1.symm (List.IsPrefix.eq_of_length h.2 this).symm)
    obtain ⟨s, rfl⟩ := under_of_addrExt hnx
    refine ⟨fun h' => h'.2 (under_ext _ _), ?_⟩
    rw [e, addrExt_append, shift_ext, shift_ext, addrExt_append]
  · have hza := not_under_root_of_out hz h
    have hxa : ¬ Under a x := fun h' => hza (by rw [e]; exact under_trans h' (under_ext _ _))
    have hnx : ¬ Under n x := fun h' => hxa (under_trans ha h')
    refine ⟨fun h' => hxa h'.1, ?_⟩
    rw [shift_of_not h, shift_of_not hnx, e]

end Addr

/-! ### Agreement off the region -/

/-- **`LG'` is `LG` with the subtree at `n` moved to `n'`, outside the region of the trees.** -/
structure OutAgreeT (LG LG' : LayeredGarden w) (a n n' : Fin w × Path) : Prop where
  node : ∀ z : Fin w × Path, ¬ InTree a n z → (z.2 ∈ (LG.garden.tree z.1).nodes ↔
    (shiftAddr n n' z).2 ∈ (LG'.garden.tree (shiftAddr n n' z).1).nodes)
  leaf : ∀ z : Fin w × Path, ¬ InTree a n z → (z.2 ∈ (LG.garden.tree z.1).leaves ↔
    (shiftAddr n n' z).2 ∈ (LG'.garden.tree (shiftAddr n n' z).1).leaves)
  layer : ∀ z : Fin w × Path, ¬ InTree a n z → layerAt LG z = layerAt LG' (shiftAddr n n' z)
  pair : ∀ (ℓ : GLeaf LG.garden.tree) (ℓ' : GLeaf LG'.garden.tree), ¬ InTree a n ℓ.1 →
    shiftAddr n n' ℓ.1 = ℓ'.1 → shiftAddr n n' (LG.garden.pair ℓ).1 = (LG'.garden.pair ℓ').1

variable {LG LG' : LayeredGarden w} {p : ℕ} {X X' : RegChain} {ζ ζ' : ℤˣ} {a : Fin w × Path}
  {h h' : TTree}

/-- A parent-layer comparison from a parent-matching. -/
theorem parAt_eq_of {z z' : Fin w × Path} (hz : z.2 ∈ (LG.garden.tree z.1).nodes)
    (hz' : z'.2 ∈ (LG'.garden.tree z'.1).nodes) (hr : z.2 = [] ↔ z'.2 = [])
    (hpar : ∀ (x : Fin w × Path) (k : Fin 3), z = addrExt x [k] →
      ∃ x', z' = addrExt x' [k] ∧ layerAt LG x = layerAt LG' x') :
    parAt LG p z = parAt LG' p z' := by
  by_cases h0 : z.2 = []
  · have e : z = (z.1, []) := Prod.ext rfl h0
    have e' : z' = (z'.1, []) := Prod.ext rfl (hr.1 h0)
    rw [e, e', parAt_root, parAt_root]
  · obtain ⟨q, k, hqk⟩ := (List.eq_nil_or_concat z.2).resolve_left h0
    have e : z = addrExt (z.1, q) [k] := Prod.ext rfl (by simp [addrExt, hqk])
    obtain ⟨x', e', hl⟩ := hpar _ _ e
    have h1 : (addrExt (z.1, q) [k]).2 ∈ (LG.garden.tree (addrExt (z.1, q) [k]).1).nodes := by
      rw [← e]; exact hz
    have h2 : (addrExt x' [k]).2 ∈ (LG'.garden.tree (addrExt x' [k]).1).nodes := by
      rw [← e']; exact hz'
    rw [e, e', parAt_child LG p k h1, parAt_child LG' p k h2]
    exact hl

section Agree

variable (hA : OutAgreeT LG LG' a (addrExt a X.lonePath) (addrExt a X'.lonePath))
include hA

/-- Parent layers agree outside the region, away from `n`. -/
theorem OutAgreeT.parAt_eq {z : Fin w × Path} (hz : ¬ InTree a (addrExt a X.lonePath) z)
    (hzn : z ≠ addrExt a X.lonePath) (n1 : z.2 ∈ (LG.garden.tree z.1).nodes) :
    parAt LG p z = parAt LG' p (shiftAddr (addrExt a X.lonePath) (addrExt a X'.lonePath) z) := by
  have ha : Under a (addrExt a X.lonePath) := under_ext _ _
  have n2 := (hA.node z hz).1 n1
  refine parAt_eq_of n1 n2 ⟨fun h0 => ?_, fun h0 => ?_⟩ fun x k e => ?_
  · have hn : ¬ Under (addrExt a X.lonePath) z := by
      intro hu
      have h2 : (addrExt a X.lonePath).2 = [] := List.prefix_nil.1 (by rw [← h0]; exact hu.2)
      exact hzn (Prod.ext hu.1.symm (by rw [h0, h2]))
    rw [shift_of_not hn]; exact h0
  · by_contra h1
    obtain ⟨q, k, hqk⟩ := (List.eq_nil_or_concat z.2).resolve_left h1
    have e : z = addrExt (z.1, q) [k] := Prod.ext rfl (by simp [addrExt, hqk])
    have := (shift_parent (n' := addrExt a X'.lonePath) ha hz hzn e).2
    rw [this] at h0
    simp [addrExt] at h0
  · obtain ⟨hxo, e'⟩ := shift_parent (n' := addrExt a X'.lonePath) ha hz hzn e
    exact ⟨_, e', hA.layer x hxo⟩

/-- The parent layers of the root agree. -/
theorem OutAgreeT.parAt_root_eq (n1 : a.2 ∈ (LG.garden.tree a.1).nodes)
    (n2 : a.2 ∈ (LG'.garden.tree a.1).nodes) : parAt LG p a = parAt LG' p a := by
  refine parAt_eq_of n1 n2 Iff.rfl fun x k e => ⟨x, e, ?_⟩
  have hxa : ¬ Under a x := fun h' => ne_of_under_ext (q := [k]) (by simp) (e ▸ h') rfl
  have hxo : ¬ InTree a (addrExt a X.lonePath) x := fun h' => hxa h'.1
  have hnx : ¬ Under (addrExt a X.lonePath) x := fun h' => hxa (under_trans (under_ext _ _) h')
  have := hA.layer x hxo
  rwa [shift_of_not hnx] at this


end Agree

theorem OutAgreeT.symm (hA : OutAgreeT LG LG' a (addrExt a X.lonePath) (addrExt a X'.lonePath))
    (hC : ChainEmb LG.garden X ζ a h) :
    OutAgreeT LG' LG a (addrExt a X'.lonePath) (addrExt a X.lonePath) := by
  have ha : Under a (addrExt a X.lonePath) := under_ext _ _
  have ha' : Under a (addrExt a X'.lonePath) := under_ext _ _
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun ℓ' ℓ hr e => ?_⟩
  · have := hA.node _ (out_shift (n' := addrExt a X.lonePath) hz)
    rw [shift_shift ha hz] at this
    exact this.symm
  · have := hA.leaf _ (out_shift (n' := addrExt a X.lonePath) hz)
    rw [shift_shift ha hz] at this
    exact this.symm
  · have := hA.layer _ (out_shift (n' := addrExt a X.lonePath) hz)
    rw [shift_shift ha hz] at this
    exact this.symm
  · have hℓo : ¬ InTree a (addrExt a X.lonePath) ℓ.1 := by rw [← e]; exact out_shift hr
    have e2 : shiftAddr (addrExt a X.lonePath) (addrExt a X'.lonePath) ℓ.1 = ℓ'.1 := by
      rw [← e]; exact shift_shift ha hr
    rw [← hA.pair ℓ ℓ' hℓo e2]
    exact shift_shift ha' (hC.pair_out ℓ hℓo)

/-- Complete pairing of region-constant sets of leaves is the same in both gardens. -/
theorem cp_transferT (hA : OutAgreeT LG LG' a (addrExt a X.lonePath) (addrExt a X'.lonePath))
    (hplain : LG.garden.IsPlain) (hplain' : LG'.garden.IsPlain) (hC : ChainEmb LG.garden X ζ a h)
    (hC' : ChainEmb LG'.garden X' ζ' a h') (σ σ' : Fin w × Path → Prop)
    (hσ : ∀ z₁ z₂, InTree a (addrExt a X.lonePath) z₁ → InTree a (addrExt a X.lonePath) z₂ →
      (σ z₁ ↔ σ z₂))
    (hσ' : ∀ z₁ z₂, InTree a (addrExt a X'.lonePath) z₁ → InTree a (addrExt a X'.lonePath) z₂ →
      (σ' z₁ ↔ σ' z₂))
    (hσσ : ∀ z, ¬ InTree a (addrExt a X.lonePath) z →
      (σ' (shiftAddr (addrExt a X.lonePath) (addrExt a X'.lonePath) z) ↔ σ z))
    (S : Finset (GLeaf LG.garden.tree)) (S' : Finset (GLeaf LG'.garden.tree))
    (hS : ∀ ℓ, ℓ ∈ S ↔ σ ℓ.1) (hS' : ∀ ℓ, ℓ ∈ S' ↔ σ' ℓ.1) :
    LG.garden.CompletelyPaired S ↔ LG'.garden.CompletelyPaired S' := by
  have ha : Under a (addrExt a X.lonePath) := under_ext _ _
  rw [cp_iff_tree hplain hC σ hσ S hS, cp_iff_tree hplain' hC' σ' hσ' S' hS']
  constructor
  · intro H ℓ' hr hs
    have hzo : ¬ InTree a (addrExt a X.lonePath)
        (shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath) ℓ'.1) := out_shift hr
    have hzz := shift_shift (n' := addrExt a X.lonePath) ha hr
    have hl : (shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath) ℓ'.1).2 ∈
        (LG.garden.tree (shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath) ℓ'.1).1).leaves :=
      (hA.leaf _ hzo).2 (by rw [hzz]; exact ℓ'.2)
    have hp := hA.pair ⟨_, hl⟩ ℓ' hzo hzz
    have h1 := (hσσ _ hzo).1 (by rw [hzz]; exact hs)
    have h2 := H ⟨_, hl⟩ hzo h1
    rw [← hp]
    exact (hσσ _ (hC.pair_out ⟨_, hl⟩ hzo)).2 h2
  · intro H ℓ hr hs
    have hl : (shiftAddr (addrExt a X.lonePath) (addrExt a X'.lonePath) ℓ.1).2 ∈
        (LG'.garden.tree (shiftAddr (addrExt a X.lonePath) (addrExt a X'.lonePath) ℓ.1).1).leaves :=
      (hA.leaf ℓ.1 hr).1 ℓ.2
    have hp := hA.pair ℓ ⟨_, hl⟩ hr rfl
    have h2 := H ⟨_, hl⟩ (out_shift hr) ((hσσ ℓ.1 hr).2 hs)
    rw [← hp] at h2
    exact (hσσ _ (hC.pair_out ℓ hr)).1 h2

/-- An outside node pulled back along the move. -/
theorem pullback_facts (hA : OutAgreeT LG LG' a (addrExt a X.lonePath) (addrExt a X'.lonePath))
    (x' : GNode LG'.garden.tree) (hx : ¬ InTree a (addrExt a X'.lonePath) x'.1) :
    ¬ InTree a (addrExt a X.lonePath) (shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath) x'.1) ∧
    shiftAddr (addrExt a X.lonePath) (addrExt a X'.lonePath)
      (shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath) x'.1) = x'.1 ∧
    (shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath) x'.1).2 ∈
      (LG.garden.tree (shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath) x'.1).1).nodes := by
  have hzo := out_shift (n' := addrExt a X.lonePath) hx
  have hzz := shift_shift (n' := addrExt a X.lonePath) (under_ext a X.lonePath) hx
  exact ⟨hzo, hzz, (hA.node _ hzo).2 (by rw [hzz]; exact x'.2)⟩

theorem critOutT_transfer (hA : OutAgreeT LG LG' a (addrExt a X.lonePath) (addrExt a X'.lonePath))
    (hplain : LG.garden.IsPlain) (hplain' : LG'.garden.IsPlain) (hC : ChainEmb LG.garden X ζ a h)
    (hC' : ChainEmb LG'.garden X' ζ' a h') (H : CritOutT LG p a (addrExt a X.lonePath)) :
    CritOutT LG' p a (addrExt a X'.lonePath) := by
  have ha : Under a (addrExt a X.lonePath) := under_ext _ _
  have ha' : Under a (addrExt a X'.lonePath) := under_ext _ _
  intro x' y' hx hy hxn hyn hinc hcp
  obtain ⟨hxo, ex, nx⟩ := pullback_facts hA x' hx
  obtain ⟨hyo, ey, ny⟩ := pullback_facts hA y' hy
  set x := shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath) x'.1
  set y := shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath) y'.1
  have hxn' : x ≠ addrExt a X.lonePath := fun e => hxn (by rw [← ex, e, shift_self])
  have hyn' : y ≠ addrExt a X.lonePath := fun e => hyn (by rw [← ey, e, shift_self])
  have hu : ∀ {u v : Fin w × Path}, ¬ InTree a (addrExt a X.lonePath) u →
      ¬ InTree a (addrExt a X.lonePath) v → (Under u v ↔
        Under (shiftAddr (addrExt a X.lonePath) (addrExt a X'.lonePath) u)
          (shiftAddr (addrExt a X.lonePath) (addrExt a X'.lonePath) v)) :=
    fun hu hv => under_shift ha ha' hu hv
  have hinc' : GNode.Incomparable (⟨x, nx⟩ : GNode LG.garden.tree) ⟨y, ny⟩ := by
    refine ⟨fun h1 => hinc.1 ?_, fun h1 => hinc.2 ?_⟩
    · have := (hu hxo hyo).1 h1; rwa [ex, ey] at this
    · have := (hu hyo hxo).1 h1; rwa [ex, ey] at this
  have hcp' : LG.garden.CompletelyPaired (GNode.leavesBelow (⟨x, nx⟩ : GNode LG.garden.tree) ∪
      GNode.leavesBelow (⟨y, ny⟩ : GNode LG.garden.tree)) := by
    refine (cp_transferT hA hplain hplain' hC hC' (fun z => Under x z ∨ Under y z)
      (fun z => Under x'.1 z ∨ Under y'.1 z)
      (fun z₁ z₂ h₁ h₂ => or_congr (under_const_tree hxo h₁ h₂) (under_const_tree hyo h₁ h₂))
      (fun z₁ z₂ h₁ h₂ => or_congr (under_const_tree hx h₁ h₂) (under_const_tree hy h₁ h₂))
      (fun z hz => ?_) _ _ (mem_leavesBelow_union (⟨x, nx⟩ : GNode LG.garden.tree) ⟨y, ny⟩)
      (mem_leavesBelow_union x' y')).2 hcp
    show (Under x'.1 _ ∨ Under y'.1 _) ↔ (Under x z ∨ Under y z)
    rw [← ex, ← ey, ← hu hxo hz, ← hu hyo hz]
  have := H ⟨x, nx⟩ ⟨y, ny⟩ hxo hyo hxn' hyn' hinc' hcp'
  rw [← parAt_of_mem LG p nx, ← parAt_of_mem LG p ny, ← layerAt_of_mem LG nx,
    ← layerAt_of_mem LG ny, hA.parAt_eq hxo hxn' nx, hA.parAt_eq hyo hyn' ny, hA.layer _ hxo,
    hA.layer _ hyo, ex, ey] at this
  rwa [← parAt_node, ← parAt_node, ← layerAt_node, ← layerAt_node]

theorem critAttachT_transfer (hA : OutAgreeT LG LG' a (addrExt a X.lonePath) (addrExt a X'.lonePath))
    (hplain : LG.garden.IsPlain) (hplain' : LG'.garden.IsPlain) (hC : ChainEmb LG.garden X ζ a h)
    (hC' : ChainEmb LG'.garden X' ζ' a h') (H : CritAttachT LG p a (addrExt a X.lonePath)) :
    CritAttachT LG' p a (addrExt a X'.lonePath) := by
  have ha : Under a (addrExt a X.lonePath) := under_ext _ _
  have ha' : Under a (addrExt a X'.lonePath) := under_ext _ _
  intro x' y' hx hy hinc hcp
  have nn := nodeOfChainEmb hC
  have hno : ¬ InTree a (addrExt a X.lonePath) (addrExt a X.lonePath) := fun h1 => h1.2 (under_refl _)
  obtain ⟨hyo, ey, ny⟩ := pullback_facts hA y' hy
  set y := shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath) y'.1
  have hyn' : y ≠ addrExt a X.lonePath := fun e => by
    apply hinc.1
    show Under x'.1 y'.1
    rw [hx, ← ey, e, shift_self]; exact under_refl _
  have hu : ∀ {u v : Fin w × Path}, ¬ InTree a (addrExt a X.lonePath) u →
      ¬ InTree a (addrExt a X.lonePath) v → (Under u v ↔
        Under (shiftAddr (addrExt a X.lonePath) (addrExt a X'.lonePath) u)
          (shiftAddr (addrExt a X.lonePath) (addrExt a X'.lonePath) v)) :=
    fun hu hv => under_shift ha ha' hu hv
  have hinc' : GNode.Incomparable (⟨addrExt a X.lonePath, nn⟩ : GNode LG.garden.tree) ⟨y, ny⟩ := by
    refine ⟨fun h1 => hinc.1 ?_, fun h1 => hinc.2 ?_⟩
    · have := (hu hno hyo).1 h1; rw [shift_self, ey] at this
      show Under x'.1 y'.1; rw [hx]; exact this
    · have := (hu hyo hno).1 h1; rw [shift_self, ey] at this
      show Under y'.1 x'.1; rw [hx]; exact this
  have hxo' : ¬ InTree a (addrExt a X'.lonePath) x'.1 := by
    rw [hx]; exact fun h1 => h1.2 (under_refl _)
  have hcp' : LG.garden.CompletelyPaired
      (GNode.leavesBelow (⟨addrExt a X.lonePath, nn⟩ : GNode LG.garden.tree) ∪
        GNode.leavesBelow (⟨y, ny⟩ : GNode LG.garden.tree)) := by
    refine (cp_transferT hA hplain hplain' hC hC' (fun z => Under (addrExt a X.lonePath) z ∨ Under y z)
      (fun z => Under x'.1 z ∨ Under y'.1 z)
      (fun z₁ z₂ h₁ h₂ => or_congr (under_const_tree hno h₁ h₂) (under_const_tree hyo h₁ h₂))
      (fun z₁ z₂ h₁ h₂ => or_congr (under_const_tree hxo' h₁ h₂) (under_const_tree hy h₁ h₂))
      (fun z hz => ?_) _ _
      (mem_leavesBelow_union (⟨addrExt a X.lonePath, nn⟩ : GNode LG.garden.tree) ⟨y, ny⟩)
      (mem_leavesBelow_union x' y')).2 hcp
    show (Under x'.1 _ ∨ Under y'.1 _) ↔ (Under (addrExt a X.lonePath) z ∨ Under y z)
    have key := hu hno hz
    rw [shift_self] at key
    rw [hx, ← ey, ← key, ← hu hyo hz]
  have := H ⟨addrExt a X.lonePath, nn⟩ ⟨y, ny⟩ rfl hyo hinc' hcp'
  rw [← parAt_of_mem LG p ny, ← layerAt_of_mem LG nn, ← layerAt_of_mem LG ny,
    hA.parAt_root_eq hC.node hC'.node, hA.parAt_eq hyo hyn' ny, hA.layer _ hno, hA.layer _ hyo,
    shift_self, ey] at this
  rw [← parAt_node, ← layerAt_node, ← layerAt_node, hx]
  exact this

theorem crit_i_transferT (hA : OutAgreeT LG LG' a (addrExt a X.lonePath) (addrExt a X'.lonePath))
    (hC : ChainEmb LG.garden X ζ a h) (hC' : ChainEmb LG'.garden X' ζ' a h')
    (hp : ∀ x, LG.layer x ≤ p)
    (hB' : ∀ z ∈ chainNodesSet X' ζ' a, layerAt LG' z ≤ parAt LG' p a) : ∀ x, LG'.layer x ≤ p := by
  intro x'
  rw [← layerAt_node]
  by_cases hr : InTree a (addrExt a X'.lonePath) x'.1
  · calc layerAt LG' x'.1 ≤ parAt LG' p a := hB' _ (hC'.mem_chainNodesSet x'.2 hr)
      _ = parAt LG p a := (hA.parAt_root_eq hC.node hC'.node).symm
      _ ≤ p := parAt_le LG p hp a
  · obtain ⟨hzo, hzz, -⟩ := pullback_facts hA x' hr
    rw [← hzz, ← hA.layer _ hzo]
    exact layerAt_le LG p hp _

/-! ### The replacement -/

/-- **TARGET Prop `layerreg1` (2), regular trees, criterion form.** -/
theorem layerreg1_replace_tree (hA : OutAgreeT LG LG' a (addrExt a X.lonePath) (addrExt a X'.lonePath))
    (hplain : LG.garden.IsPlain) (hplain' : LG'.garden.IsPlain) (hC : ChainEmb LG.garden X ζ a h)
    (hC' : ChainEmb LG'.garden X' ζ' a h') (hP : TreePattern LG p X ζ a)
    (hP' : TreePattern LG' p X' ζ' a) : LG.CanonCriterion p ↔ LG'.CanonCriterion p := by
  have hA' := hA.symm hC
  rw [layerreg1_part2_tree hplain hC hP, layerreg1_part2_tree hplain' hC' hP']
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨crit_i_transferT hA hC hC' h1 fun z hz => (hP'.2.2 z hz).2,
      critOutT_transfer hA hplain hplain' hC hC' h2,
      critAttachT_transfer hA hplain hplain' hC hC' h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨crit_i_transferT hA' hC' hC h1 fun z hz => (hP.2.2 z hz).2,
      critOutT_transfer hA' hplain' hplain hC' hC h2,
      critAttachT_transfer hA' hplain' hplain hC' hC h3⟩

/-- The replaced garden is plain. -/
theorem plain_transferT (hA : OutAgreeT LG LG' a (addrExt a X.lonePath) (addrExt a X'.lonePath))
    (hplain : LG.garden.IsPlain) (hC : ChainEmb LG.garden X ζ a h)
    (hC' : ChainEmb LG'.garden X' ζ' a h') : LG'.garden.IsPlain := by
  have ha' : Under a (addrExt a X'.lonePath) := under_ext _ _
  intro ℓ'
  have hne : LG'.garden.pair ℓ' ≠ ℓ' := by
    intro hp'
    by_cases hr : InTree a (addrExt a X'.lonePath) ℓ'.1
    · obtain ⟨q, hq, e⟩ := hC'.partner ℓ' hr
      have hi := chain_pair_indep X' ζ' a q hq
      rw [hp'] at e
      rcases e with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact hi.1 (by rw [← e1, ← e2]; exact under_refl _)
      · exact hi.1 (by rw [← e1, ← e2]; exact under_refl _)
    · have hzo : ¬ InTree a (addrExt a X.lonePath)
          (shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath) ℓ'.1) := out_shift hr
      have hzz := shift_shift (n' := addrExt a X.lonePath) (under_ext a X.lonePath) hr
      have hl : (shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath) ℓ'.1).2 ∈
          (LG.garden.tree (shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath) ℓ'.1).1).leaves :=
        (hA.leaf _ hzo).2 (by rw [hzz]; exact ℓ'.2)
      have hp := hA.pair ⟨_, hl⟩ ℓ' hzo hzz
      have hp2 : shiftAddr (addrExt a X.lonePath) (addrExt a X'.lonePath)
          (LG.garden.pair ⟨_, hl⟩).1 = ℓ'.1 := hp.trans (by rw [hp'])
      have := congrArg (shiftAddr (addrExt a X'.lonePath) (addrExt a X.lonePath)) hp2
      rw [shift_shift ha' (hC.pair_out ⟨_, hl⟩ hzo)] at this
      exact ((LG.garden.pair_eq_iff _).1 (Subtype.ext this)) (hplain _)
  by_contra hm
  exact hne ((LG'.garden.pair_eq_iff ℓ').2 hm)

/-- The replaced garden is irreducible if the original one is. -/
theorem irreducible_transferT (hA : OutAgreeT LG LG' a (addrExt a X.lonePath) (addrExt a X'.lonePath))
    (hplain : LG.garden.IsPlain) (hplain' : LG'.garden.IsPlain) (hC : ChainEmb LG.garden X ζ a h)
    (hC' : ChainEmb LG'.garden X' ζ' a h') (hirr : LG.garden.Irreducible) :
    LG'.garden.Irreducible := by
  have ha : Under a (addrExt a X.lonePath) := under_ext _ _
  have ha' : Under a (addrExt a X'.lonePath) := under_ext _ _
  intro A h1 h2 hcp
  refine hirr A h1 h2 ((cp_transferT hA hplain hplain' hC hC' (fun z => z.1 ∈ A) (fun z => z.1 ∈ A)
    (fun z₁ z₂ h₁ h₂ => ?_) (fun z₁ z₂ h₁ h₂ => ?_) (fun z _ => ?_) _ _ (fun ℓ => ?_)
    (fun ℓ => ?_)).2 hcp)
  · show z₁.1 ∈ A ↔ z₂.1 ∈ A
    rw [← h₁.1.1, ← h₂.1.1]
  · show z₁.1 ∈ A ↔ z₂.1 ∈ A
    rw [← h₁.1.1, ← h₂.1.1]
  · show (shiftAddr (addrExt a X.lonePath) (addrExt a X'.lonePath) z).1 ∈ A ↔ z.1 ∈ A
    rw [shift_fst ha ha']
  · simp [Garden.leavesOf]
  · simp [Garden.leavesOf]

/-- **TARGET Prop `layerreg1` (2), regular trees in gardens.** If `LG ∈ 𝒢_{p+1}` contains a coherent
embedded regular tree (code `X`) at `a`, and `LG'` is `LG` with this tree replaced by a regular tree
(code `X'`) at `a` carrying the layering of part (1) (`OutAgreeT`: the rest of the garden, including the
subtree at the lone position, is moved along), then `LG' ∈ 𝒢_{p+1}`. -/
theorem layerreg1_replace_tree_canonG (hcan : IsCanonG (p + 1) LG) (hwf : X.wf = true)
    (hC : ChainEmb LG.garden X ζ a h) (hcoh : CohOn LG (X.linksAt ζ a))
    (hA : OutAgreeT LG LG' a (addrExt a X.lonePath) (addrExt a X'.lonePath))
    (hC' : ChainEmb LG'.garden X' ζ' a h') (hP' : TreePattern LG' p X' ζ' a) :
    IsCanonG (p + 1) LG' := by
  obtain ⟨hw, hplain, hirr, hcrit⟩ := hcan
  have hplain' := plain_transferT hA hplain hC hC'
  have hP := treePattern_of_canon hcrit hplain hwf hC hcoh
  exact ⟨hw, hplain', irreducible_transferT hA hplain hplain' hC hC' hirr,
    (layerreg1_replace_tree hA hplain hplain' hC hC' hP hP').1 hcrit⟩

/-- **TARGET Prop `layerreg1` (2), regular trees in couples (`𝒞_{p+1}`).** -/
theorem layerreg1_replace_tree_canonC {LG LG' : LayeredGarden 2} {a : Fin 2 × Path}
    (hcan : IsCanonC (p + 1) LG) (hwf : X.wf = true) (hC : ChainEmb LG.garden X ζ a h)
    (hcoh : CohOn LG (X.linksAt ζ a))
    (hA : OutAgreeT LG LG' a (addrExt a X.lonePath) (addrExt a X'.lonePath))
    (hsig : LG'.garden.sig = LG.garden.sig) (hC' : ChainEmb LG'.garden X' ζ' a h')
    (hP' : TreePattern LG' p X' ζ' a) : IsCanonC (p + 1) LG' := by
  obtain ⟨⟨hplain, hs⟩, hcrit⟩ := hcan
  have hplain' := plain_transferT hA hplain hC hC'
  have hP := treePattern_of_canon hcrit hplain hwf hC hcoh
  exact ⟨⟨hplain', hsig.trans hs⟩, (layerreg1_replace_tree hA hplain hplain' hC hC' hP hP').1 hcrit⟩

end WaveTurbulence.Links
