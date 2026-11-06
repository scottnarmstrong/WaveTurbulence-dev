/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeLow

/-!
# Prop 6.1, `q > q'`, trees: one block of the chain

* `TreeLowState`: a suffix `X` of the chain of a coherent tree below `(0, π)`, decoded in its own carrier `LG'`
  with the layers, signs and leaf controls transported from the whole tree;
* **`tree_block_step`**: for a suffix whose top block `B` (in layer `u`) is followed by a nonempty rest `D`, the
  kernel factors as `K_B(t, u) · K_D(r''+1, s)` (`treeLeaves_split`), the block is a single-layer tree with the
  transported slice profiles, the rest is again a lower state, and the leaf size products multiply.
-/

@[expose] public section
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

/-- A lower state of a coherent tree below `(0, π)`. -/
structure TreeLowState (LG : LayeredGarden 1) (H : LeafProfiles 1 d) (Bd : (Fin 1 × Path) → NNReal)
    (π : Path) (X : RegChain) (LG' : LayeredGarden 1) : Prop where
  dec : X.DecodesTree LG'.garden
  sig : LG'.garden.sig 0 = LG.garden.sig 0
  lay : ∀ z, layerAt LG' z = layerAt LG (botAddr π z)
  ctrl : LeafwiseControlled LG' (fun z => H (botAddr π z)) (fun z => Bd (botAddr π z))

/-- The whole tree is a lower state below its root. -/
theorem TreeLowState.root {LG : LayeredGarden 1} {H : LeafProfiles 1 d} {Bd : (Fin 1 × Path) → NNReal}
    {X : RegChain} (hX : X.DecodesTree LG.garden) (hH : LeafwiseControlled LG H Bd) :
    TreeLowState LG H Bd [] X LG := by
  have hHe : (fun z => H (botAddr [] z)) = H := funext fun z => by rw [botAddr_nil_tree]
  have hBe : (fun z => Bd (botAddr [] z)) = Bd := funext fun z => by rw [botAddr_nil_tree]
  refine ⟨hX, rfl, fun z => by rw [botAddr_nil_tree], ?_⟩
  rw [hHe, hBe]
  exact hH

/-- **One block of the chain of a tree.** -/
theorem tree_block_step {LG : LayeredGarden 1} {H : LeafProfiles 1 d} {Bd : (Fin 1 × Path) → NNReal}
    {π : Path} {X : RegChain} {LG' : LayeredGarden 1}
    (S : TreeLowState LG H Bd π X LG') (L γ δ : ℝ) (hd : 1 ≤ d) (hL : 1 ≤ L)
    (hwf : X.wf = true) {u : ℕ}
    (hDne : dropLayer LG (0, π) u X ≠ .nil)
    (hlt : layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) < u)
    (hB : ∀ z ∈ chainNodesSet (takeLayer LG (0, π) u X) (LG.garden.sig 0) (0, π), layerAt LG z = u) :
    ∃ (G₁ : LayeredGarden 1) (LG'' : LayeredGarden 1),
      (takeLayer LG (0, π) u X).DecodesTree G₁.garden ∧ G₁.garden.sig 0 = LG.garden.sig 0 ∧
      (∀ a : GNode G₁.garden.tree, G₁.layer a =
        if a.1.2 = (takeLayer LG (0, π) u X).lonePath then
          layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) else u) ∧
      LeafwiseControlled G₁ (LeafApp.sliceProfiles LG H (0, π) u X)
        (fun z => Bd (LeafApp.sliceAddress LG (0, π) u X z.2)) ∧
      TreeLowState LG H Bd (π ++ (takeLayer LG (0, π) u X).lonePath) (dropLayer LG (0, π) u X) LG'' ∧
      leafSizeProduct LG' (fun z => Bd (botAddr π z)) =
        leafSizeProduct G₁ (fun z => Bd (LeafApp.sliceAddress LG (0, π) u X z.2)) *
          leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ (takeLayer LG (0, π) u X).lonePath) z)) ∧
      ∀ (t s : ℝ) (k : Mom d), (layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) : ℝ) + 1 ≤ t →
        treeLeaves L γ δ LG' (fun z => H (botAddr π z)) t s k =
        treeLeaves L γ δ G₁ (LeafApp.sliceProfiles LG H (0, π) u X) t u k *
          treeLeaves L γ δ LG'' (fun z => H (botAddr (π ++ (takeLayer LG (0, π) u X).lonePath) z))
            ((layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) : ℝ) + 1) s k := by
  set B := takeLayer LG (0, π) u X with hBdef
  set D := dropLayer LG (0, π) u X with hDdef
  have hXe : appendChain B D = X := appendChain_take_drop LG (0, π) u X
  have hTA : TopAll LG u (0, π) B := topAll_takeLayer LG u _ X
  have hG : (appendChain B D).DecodesTree LG'.garden := by rw [hXe]; exact S.dec
  have hwf' : (appendChain B D).wf = true := by rw [hXe]; exact hwf
  rw [appendChain_wf, Bool.and_eq_true] at hwf'
  obtain ⟨G₁g, hs₁, h₁, -⟩ := RegChain.exists_decodesTree B hwf'.1 (LG'.garden.sig 0)
  obtain ⟨G₂, hs₂, h₂, -⟩ := RegChain.exists_decodesTree D hwf'.2 (LG'.garden.sig 0)
  have hlp : (appendChain B D).lonePath = B.lonePath ++ D.lonePath := appendChain_lonePath B D
  -- the block in layer `u`, in the current carrier
  have hB' : ∀ z ∈ chainNodesSet B (LG'.garden.sig 0) ((0 : Fin 1), ([] : Path)), layerAt LG' z = u := by
    intro z hz
    rw [S.lay]
    apply hB
    have hm := chainNodesSet_map B (botAddr π) (botAddr_hom π) (LG'.garden.sig 0) ((0 : Fin 1), ([] : Path))
    have h0 : botAddr π ((0 : Fin 1), ([] : Path)) = ((0 : Fin 1), π) := by simp [botAddr]
    rw [h0, S.sig] at hm
    rw [hm]
    rw [S.sig] at hz
    exact Finset.mem_image_of_mem _ hz
  have hr'' : layerAt LG' ((0 : Fin 1), B.lonePath) = layerAt LG (0, π ++ B.lonePath) := by
    rw [S.lay]
    simp [botAddr]
  have hlt' : layerAt LG' ((0 : Fin 1), B.lonePath) < u := by rw [hr'']; exact hlt
  set h := glueData_tree hG h₁ hs₁ h₂ hs₂ with hh
  have hmtop : ∀ ℓ : GLeaf LG'.garden.tree, (ℓ.1.1 = 0 ∧ ¬ B.lonePath <+: ℓ.1.2) →
      LG'.garden.mark ℓ = none := by
    intro ℓ hℓ
    rw [hG.2.1 ℓ, hlp]
    refine ite_eq_right fun he => hℓ.2 ?_
    rw [he]
    exact List.prefix_append _ _
  have hmbot : ∀ (ℓ₂ : GLeaf G₂.tree) (ℓ : GLeaf LG'.garden.tree),
      ℓ.1 = botAddr B.lonePath ℓ₂.1 → LG'.garden.mark ℓ = G₂.mark ℓ₂ := by
    intro ℓ₂ ℓ he
    rw [hG.2.1 ℓ, h₂.2.1 ℓ₂, hlp]
    have hp : ℓ.1.2 = B.lonePath ++ ℓ₂.1.2 := by
      rw [he]
      have hj : ℓ₂.1.1 = 0 := Subsingleton.elim _ _
      simp [botAddr, hj]
    rw [hp]
    simp only [List.append_cancel_left_eq]
  -- the original addresses of the block's input leaves
  have haddr : ∀ ℓ ∈ inputLeaves G₁g, LeafApp.sliceAddress LG (0, π) u X ℓ.1.2 = botAddr π (topAddr ℓ.1) := by
    intro ℓ hℓ
    rw [← hXe, sliceAddress_append_of_not_prefix LG u D B (0, π) ℓ.1.2 hTA (not_prefix_of_inputLeaf h₁ hℓ)]
    simp [botAddr, topAddr, addrExt]
  set G₁ := topLayered G₁g B h₁ u (layerAt LG' ((0 : Fin 1), B.lonePath)) hlt'.le with hG₁
  set LG'' := botLayered_tree hG h₁ hs₁ h₂ hs₂ with hLG''
  have hS'' : TreeLowState LG H Bd (π ++ B.lonePath) D LG'' := by
    refine ⟨h₂, hs₂.trans S.sig, fun z => ?_, fun ℓ₂ hℓ₂ => ?_⟩
    · rw [layerAt_botLayered_tree hG h₁ hs₁ h₂ hs₂, S.lay, botAddr_comp_tree]
    · obtain ⟨ℓ, hℓ, he⟩ := h.inputLeaf_ofBot hmbot ℓ₂ hℓ₂
      have := S.ctrl ℓ hℓ
      show SNormR _ _ (H (botAddr (π ++ B.lonePath) ℓ₂.1)) ≤
        ENNReal.ofReal (Bd (botAddr (π ++ B.lonePath) ℓ₂.1))
      simp only at this
      rw [he, botAddr_comp_tree] at this
      exact this
  refine ⟨G₁, LG'', h₁, hs₁.trans S.sig, fun a => ?_, fun ℓ hℓ => ?_, hS'', ?_, fun t s k ht => ?_⟩
  · show (if a.1.2 = B.lonePath then layerAt LG' ((0 : Fin 1), B.lonePath) else u) = _
    rw [hr'']
  · obtain ⟨ℓ', hℓ', he⟩ := h.inputLeaf_ofTop h₁.2.1 hmtop ℓ hℓ
    have := S.ctrl ℓ' hℓ'
    show SNormR _ _ (H (LeafApp.sliceAddress LG (0, π) u X ℓ.1.2)) ≤
      ENNReal.ofReal (Bd (LeafApp.sliceAddress LG (0, π) u X ℓ.1.2))
    simp only at this
    rw [haddr ℓ hℓ, ← he]
    exact this
  · unfold leafSizeProduct
    rw [h.prod_inputLeaves_glue h₁.2.1 hmtop hmbot (fun z => ((Bd (botAddr π z) : NNReal) : ℝ))]
    congr 1
    · exact Finset.prod_congr rfl fun ℓ hℓ => by
        show ((Bd (botAddr π (topAddr ℓ.1)) : NNReal) : ℝ) =
          ((Bd (LeafApp.sliceAddress LG (0, π) u X ℓ.1.2) : NNReal) : ℝ)
        rw [haddr ℓ hℓ]
    · exact Finset.prod_congr rfl fun ℓ _ => by rw [botAddr_comp_tree]
  · have hH := S.ctrl.summable_coset hd hL k
    have hsplit := treeLeaves_split L γ δ hG hDne h₁ hs₁ h₂ hs₂ hB' hlt' (fun z => H (botAddr π z)) k hH
      t s (by rw [hr'']; exact ht)
    rw [hsplit]
    congr 1
    · unfold treeLeaves
      exact kernelLeaves_congr_profiles L γ δ G₁ _ _ (fun ℓ hℓ => by
        show H (botAddr π (topAddr ℓ.1)) = H (LeafApp.sliceAddress LG (0, π) u X ℓ.1.2)
        rw [haddr ℓ hℓ]) _ _ _ _ _
    · rw [hr'']
      congr 1
      funext z
      rw [botAddr_comp_tree]

end WaveTurbulence.PL234
