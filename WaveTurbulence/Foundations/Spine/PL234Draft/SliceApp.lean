/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.ReadCongr

/-!
# Layer-indexed inputs as leaf profiles

For layer-indexed inputs `F : ℕ → Mom d → ℝ` put `H_F z := F(𝔏 z)` at every address. Then:

* `KQstar_eq_coupleLeaves`, `KTstar_eq_treeLeaves`: the source kernels are the leafwise kernels;
* `block_app_eq`, `slice_app_eq`: each slice of an embedded coherent chain reads its transported profiles only
  at leaves of its own layer `r`, so its leafwise leading term is `(𝒯_[r]).app δ r F_r`;
* `split_last_block`: a chain with all layers `≥ r` splits as `R ++ B` with no top pair of `R` and every top pair
  of `B` in layer `r`;
* **`sourceCouple_eq`**, **`sourceTree_eq`**: `SourceApp.couple`/`SourceApp.tree` (TARGET prooflayer1-1–2 with the
  layer inputs) are `LeafApp.coherentCouple`/`LeafApp.coherentTree` at the profiles `H_F`.
-/

@[expose] public section
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

/-- The leaf profiles of layer-indexed inputs. -/
def layerProfiles {w : ℕ} (LG : LayeredGarden w) (F : ℕ → Mom d → ℝ) : LeafProfiles w d :=
  fun z => F (layerAt LG z)

theorem KQstar_eq_coupleLeaves (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (t s : ℝ) (k : Mom d) :
    KQstar L γ δ F LG t s k = coupleLeaves L γ δ LG (layerProfiles LG F) t s k := by
  unfold KQstar coupleLeaves
  exact (kernelLeaves_eq_kernelK L γ δ LG F _ (fun ℓ _ => by
    show F (layerAt LG ℓ.1) = F (LG.layer ℓ.toNode)
    rw [← layerAt_node LG ℓ.toNode]
    rfl) _ _ _ _ _).symm

theorem KTstar_eq_treeLeaves (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1) (t s : ℝ) (k : Mom d) :
    KTstar L γ δ F LG t s k = treeLeaves L γ δ LG (layerProfiles LG F) t s k := by
  unfold KTstar treeLeaves
  exact (kernelLeaves_eq_kernelK L γ δ LG F _ (fun ℓ _ => by
    show F (layerAt LG ℓ.1) = F (LG.layer ℓ.toNode)
    rw [← layerAt_node LG ℓ.toNode]
    rfl) _ _ _ _ _).symm

theorem RegChain.app_nil' (δ r : ℝ) (F : Mom d → ℝ) (ζ : ℤˣ) (t s : ℝ) (k : Mom d) :
    RegChain.nil.app δ r F ζ t s k = 1 := by
  rw [← LeafApp.tree_const, LeafApp.tree_nil]

/-- The leaves among the chain nodes of a decoded tree are off its lone position. -/
theorem leaf_chainNode_not_lone {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) {z : Fin 1 × Path}
    (hz : z ∈ chainNodesSet X (G.sig 0) ((0 : Fin 1), [])) (hl : z.2 ∈ (G.tree z.1).leaves) :
    ¬ X.lonePath <+: z.2 := by
  intro hpre
  have hj : z.1 = 0 := Subsingleton.elim _ _
  have hzn : z.2 ∈ (X.plug (G.sig 0) .leaf).nodes := by
    have := TTree.leaves_subset_nodes _ hl
    rwa [hj, hX.1] at this
  have heq := plug_leaf_prefix X _ hzn hpre
  unfold chainNodesSet at hz
  rcases Finset.mem_union.mp hz with h | h
  · have hb := (tree_mem_pairEndpoints_links_iff hX z).1 (by unfold RegChain.treeLinks; exact h)
    exact not_mem_branching_of_mem_leaves _ hl hb
  · apply (chain_pairs_flat_nodup X (G.sig 0) ((0 : Fin 1), ([] : Path))).2
    have e : addrExt ((0 : Fin 1), ([] : Path)) X.lonePath = z := by
      rw [← heq]
      exact Prod.ext (by simp [addrExt, hj]) (by simp [addrExt])
    rw [e]
    exact h

/-! ### One block -/

/-- **The top block of an embedded chain** reads its transported profiles in its own layer. -/
theorem block_app_eq {w : ℕ} (LG : LayeredGarden w) (F : ℕ → Mom d → ℝ) (δ : ℝ) {X : RegChain} {ζ : ℤˣ}
    {a : Fin w × Path} {h₀ : TTree} (hwf : X.wf = true) (hC : ChainEmb LG.garden X ζ a h₀)
    (hPL : ChainPairLayers LG X ζ a) (t s : ℝ) (k : Mom d) :
    LeafApp.tree δ (layerAt LG a) (LeafApp.sliceProfiles LG (layerProfiles LG F) a (layerAt LG a) X)
        (takeLayer LG a (layerAt LG a) X) ζ t s k =
      (takeLayer LG a (layerAt LG a) X).app δ (layerAt LG a) (F (layerAt LG a)) ζ t s k := by
  set u := layerAt LG a with hu
  set B := takeLayer LG a u X with hBdef
  set D := dropLayer LG a u X with hDdef
  have hXe : appendChain B D = X := appendChain_take_drop LG a u X
  have hTA : TopAll LG u a B := topAll_takeLayer LG u _ X
  have hCBD : ChainEmb LG.garden (appendChain B D) ζ a h₀ := by rw [hXe]; exact hC
  have hPLBD : ChainPairLayers LG (appendChain B D) ζ a := by rw [hXe]; exact hPL
  have hBlay : ∀ z ∈ chainNodesSet B ζ a, layerAt LG z = u :=
    chainNodes_layer_of_topAll (chainEmb_append_left hCBD) (chainPairLayers_append_left LG B D ζ _ hPLBD) hTA
  have hwf' : (appendChain B D).wf = true := by rw [hXe]; exact hwf
  rw [appendChain_wf, Bool.and_eq_true] at hwf'
  obtain ⟨GS, hsS, hS, -⟩ := RegChain.exists_decodesTree B hwf'.1 ζ
  have hCS := ChainEmb.of_decodesTree hS
  rw [hsS] at hCS
  rw [← LeafApp.tree_const]
  refine LeafApp.tree_congr hCS δ u (fun z hz hl => ?_) t s k
  have hz' : z ∈ chainNodesSet B (GS.sig 0) ((0 : Fin 1), []) := by rw [hsS]; exact hz
  have hnp := leaf_chainNode_not_lone hS hz' hl
  show F (layerAt LG (LeafApp.sliceAddress LG a u X z.2)) = F u
  rw [← hXe, sliceAddress_append_of_not_prefix LG u D B a z.2 hTA hnp]
  congr 1
  apply hBlay
  have hm := chainNodesSet_map B (treeEmb a) (treeEmb_hom a) ζ ((0 : Fin 1), [])
  rw [treeEmb_zero] at hm
  rw [hm]
  have : addrExt a z.2 = treeEmb a z := rfl
  rw [this]
  exact Finset.mem_image_of_mem _ hz

/-- **Every slice of an embedded coherent chain** reads its transported profiles in its own layer. -/
theorem slice_app_eq {w : ℕ} (LG : LayeredGarden w) (F : ℕ → Mom d → ℝ) (δ : ℝ) (ζ : ℤˣ) :
    ∀ (n : ℕ) (X : RegChain) (a : Fin w × Path) (h₀ : TTree), X.size ≤ n → X.wf = true →
      ChainEmb LG.garden X ζ a h₀ → ChainPairLayers LG X ζ a → SpineMono LG a X →
      ∀ (r : ℕ) (t s : ℝ) (k : Mom d),
        LeafApp.tree δ r (LeafApp.sliceProfiles LG (layerProfiles LG F) a r X) (SourceApp.chainSlice LG a r X)
          ζ t s k = (SourceApp.chainSlice LG a r X).app δ r (F r) ζ t s k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X a h₀ hsz hwf hC hPL hSM r t s k
  by_cases hXn : X = .nil
  · subst hXn
    show LeafApp.tree δ r _ RegChain.nil ζ t s k = RegChain.nil.app δ r (F r) ζ t s k
    rw [LeafApp.tree_nil, RegChain.app_nil']
  set u := layerAt LG a with hu
  set B := takeLayer LG a u X with hBdef
  set D := dropLayer LG a u X with hDdef
  have hXe : appendChain B D = X := appendChain_take_drop LG a u X
  have hTA : TopAll LG u a B := topAll_takeLayer LG u _ X
  rcases lt_trichotomy r u with hr | hr | hr
  · -- a lower layer: the slice of the rest
    have hCBD : ChainEmb LG.garden (appendChain B D) ζ a h₀ := by rw [hXe]; exact hC
    have hPLBD : ChainPairLayers LG (appendChain B D) ζ a := by rw [hXe]; exact hPL
    have hSMBD : SpineMono LG a (appendChain B D) := by rw [hXe]; exact hSM
    have hwf' : (appendChain B D).wf = true := by rw [hXe]; exact hwf
    rw [appendChain_wf, Bool.and_eq_true] at hwf'
    have hB2 := two_le_size_of_ne_nil B (takeLayer_ne_nil LG X a hXn)
    have hsz' : X.size = B.size + D.size := by rw [← hXe, appendChain_size]
    have hslice := chainSlice_take_drop LG (ne_of_lt hr) a X
    have hprof : LeafApp.sliceProfiles LG (layerProfiles LG F) a r X =
        LeafApp.sliceProfiles LG (layerProfiles LG F) (addrExt a B.lonePath) r D := by
      funext z
      unfold LeafApp.sliceProfiles
      conv_lhs => rw [← hXe]
      rw [sliceAddress_append_skip LG r B D a z.2 (TopAll.topNe LG (ne_of_lt hr) _ _ hTA)]
    rw [hslice, hprof]
    exact ih D.size (by omega) D _ h₀ le_rfl hwf'.2 (chainEmb_append_right hCBD)
      (chainPairLayers_append_right LG B D ζ _ hPLBD) (spineMono_append_right LG B D _ hSMBD) r t s k
  · -- the top block
    subst hr
    rw [chainSlice_eq_take LG a X hSM fun _ => le_rfl]
    exact block_app_eq LG F δ hwf hC hPL t s k
  · -- a higher layer: the empty slice
    rw [chainSlice_eq_nil LG a X hSM fun _ => hr, LeafApp.tree_nil, RegChain.app_nil']

/-! ### The last block -/

theorem topAll_of_squeeze {w : ℕ} (LG : LayeredGarden w) (r : ℕ) :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path), SpineMono LG a X → (X ≠ .nil → layerAt LG a ≤ r) →
      (∀ z ∈ chainNodesSet X ζ a, r ≤ layerAt LG z) → TopAll LG r a X
  | .nil, _, _, _, _, _ => trivial
  | .pair m Qr Qg inner rest, ζ, a, ⟨h1, h2⟩, hle, hlow => by
    have ha : layerAt LG a = r :=
      le_antisymm (hle (fun h => RegChain.noConfusion h)) (hlow a (root_mem_chainNodesSet _ _ _ _ _ _ _))
    refine ⟨ha, topAll_of_squeeze LG r rest _ _ h2 (fun hrn => ?_) fun z hz => hlow z (mem_chainNodesSet_rest hz)⟩
    obtain ⟨m', Qr', Qg', inner', rest', hrest⟩ : ∃ m' Qr' Qg' inner' rest', rest = .pair m' Qr' Qg' inner' rest' := by
      cases hc : rest with
      | nil => exact absurd hc hrn
      | pair m' Qr' Qg' inner' rest' => exact ⟨m', Qr', Qg', inner', rest', rfl⟩
    rw [← ha]
    exact h1 m' Qr' Qg' inner' rest' hrest

/-- **The last block**: a chain with all layers `≥ r` is `R ++ B`, no top pair of `R` in layer `r`, every top pair
of `B` in layer `r`. -/
theorem split_last_block {w : ℕ} (LG : LayeredGarden w) (r : ℕ) :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path), SpineMono LG a X →
      (∀ z ∈ chainNodesSet X ζ a, r ≤ layerAt LG z) →
      ∃ R B : RegChain, X = appendChain R B ∧ TopNe LG r a R ∧ TopAll LG r (addrExt a R.lonePath) B
  | .nil, _, a, _, _ => ⟨.nil, .nil, rfl, trivial, trivial⟩
  | .pair m Qr Qg inner rest, ζ, a, hSM, hlow => by
    by_cases ha : layerAt LG a = r
    · refine ⟨.nil, .pair m Qr Qg inner rest, rfl, trivial, ?_⟩
      have e : addrExt a RegChain.nil.lonePath = a := by simp [RegChain.lonePath, addrExt]
      rw [e]
      exact topAll_of_squeeze LG r _ ζ a hSM (fun _ => ha.le) hlow
    · obtain ⟨R', B', hX', hR', hB'⟩ := split_last_block LG r rest _ _ hSM.2
        fun z hz => hlow z (mem_chainNodesSet_rest hz)
      refine ⟨.pair m Qr Qg inner R', B', by rw [hX']; rfl, ⟨ha, hR'⟩, ?_⟩
      have e : addrExt a (RegChain.pair m Qr Qg inner R').lonePath =
          addrExt (nextAddr a m inner) R'.lonePath := by
        simp [RegChain.lonePath, nextAddr, addrExt, List.append_assoc]
      rw [e]
      exact hB'

/-! ### The source approximations -/

/-- **Couples**: `SourceApp.couple` is the leafwise leading term at the layer profiles. -/
theorem sourceCouple_eq (F : ℕ → Mom d → ℝ) (δ : ℝ) {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2}
    (hqq : q' ≤ q) (hqp : q ≤ p) (hcoh : IsCoherentCoupleAt p q q' Q LG) (t s : ℝ) (k : Mom d) :
    SourceApp.couple δ F LG Q q q' t s k = LeafApp.coherentCouple δ LG (layerProfiles LG F) Q q q' t s k := by
  have hQ := hcoh.2.1
  -- a couple all of whose nodes are in one layer
  have hconst : ∀ {r : ℕ}, (∀ z : GNode LG.garden.tree, LG.layer z = r) → ∀ (r' : ℝ) (t s : ℝ),
      LeafApp.couple δ r' (layerProfiles LG F) Q t s k = Q.app δ r' (F r) t s k := by
    intro r hr r' t s
    rw [← LeafApp.couple_const]
    refine LeafApp.couple_congr hQ δ r' (fun z _ hl => ?_) t s k
    show F (layerAt LG z) = F r
    have hn : z.2 ∈ (LG.garden.tree z.1).nodes := TTree.leaves_subset_nodes _ hl
    rw [show layerAt LG z = r from (layerAt_node LG (⟨z, hn⟩ : GNode LG.garden.tree)).trans (hr _)]
  by_cases heq : q = q'
  · subst heq
    simp only [SourceApp.couple, LeafApp.coherentCouple, ↓reduceIte]
    exact (hconst (coherentCouple_layer_eq hcoh) _ _ _).symm
  have hlt : q' < q := lt_of_le_of_ne hqq (Ne.symm heq)
  cases Q with
  | triv =>
    simp only [SourceApp.couple, LeafApp.coherentCouple, heq, hlt, ↓reduceIte]
    exact (hconst (layers_type1 hqq hcoh rfl) _ _ _).symm
  | type1 c Q₁ Q₂ Q₃ =>
    simp only [SourceApp.couple, LeafApp.coherentCouple, heq, hlt, ↓reduceIte]
    exact (hconst (layers_type1 hqq hcoh rfl) _ _ _).symm
  | type2 Xp Xm Qlp =>
    have F' := cohFacts_of_coherent hqq hqp hcoh
    obtain ⟨hXwf, hmwf, hlwf, hlt2⟩ := F'.wf_suffix (R := .nil) (X := Xp) rfl
    have hsl := fun (r : ℕ) (t s : ℝ) => slice_app_eq LG F δ 1 Xp.size Xp ((0 : Fin 2), []) Qlp.trees.1 le_rfl
      hXwf F'.emb F'.pl F'.sm r t s k
    simp only [SourceApp.couple, LeafApp.coherentCouple, heq, hlt, ↓reduceIte]
    rw [Finset.prod_congr rfl fun r _ => hsl r _ _, hsl q t q]
    congr 1
    -- the bottom couple
    obtain ⟨R, B, hXRB, hR, hB⟩ := split_last_block LG q' Xp 1 ((0 : Fin 2), []) F'.sm F'.low
    have hslice : SourceApp.chainSlice LG ((0 : Fin 2), []) q' Xp = B := by
      rw [hXRB, chainSlice_append_skip LG q' R B _ hR, chainSlice_of_topAll LG q' B _ hB]
    have haddr : ∀ path, LeafApp.sliceAddress LG ((0 : Fin 2), []) q' Xp path =
        addrExt ((0 : Fin 2), R.lonePath) path := fun path => by
      rw [hXRB, sliceAddress_append_skip LG q' R B _ path hR, sliceAddress_of_topAll LG q' B _ path hB]
      rfl
    have hprof : LeafApp.lowerProfiles LG (layerProfiles LG F) q' Xp Xm 0 =
        fun z => layerProfiles LG F (botAddr R.lonePath z) := by
      funext z
      unfold LeafApp.lowerProfiles
      obtain ⟨j, path⟩ := z
      by_cases hj : j = 0
      · subst hj
        simp only [↓reduceIte]
        rw [haddr]
        simp [botAddr, addrExt]
      · simp [hj, botAddr]
    rw [hslice, hprof]
    -- every node of the bottom couple is in layer `q'`
    have hBwf : B.wf = true := by
      have h := hXwf
      rw [hXRB, appendChain_wf, Bool.and_eq_true] at h
      exact h.2
    have hwfc : (SourceApp.closeCouple B Xm Qlp).wf = true := closeCouple_wf hBwf hmwf hlwf hlt2
    obtain ⟨Gc, hGc, -⟩ := RegCpl.exists_decodes (SourceApp.closeCouple B Xm Qlp) hwfc
    rw [← LeafApp.couple_const]
    refine LeafApp.couple_congr hGc δ q' (fun z hz _ => ?_) _ _ k
    show F q' = F (layerAt LG (botAddr R.lonePath z))
    congr 1
    symm
    have hm := cplNodes_map (SourceApp.closeCouple B Xm Qlp) (botAddr R.lonePath) (botAddr_hom R.lonePath)
      ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path))
    have h0 : botAddr R.lonePath ((0 : Fin 2), ([] : Path)) = ((0 : Fin 2), R.lonePath) := by simp [botAddr]
    have h1 : botAddr R.lonePath ((1 : Fin 2), ([] : Path)) = ((1 : Fin 2), ([] : Path)) := by simp [botAddr]
    rw [h0, h1] at hm
    have hb : botAddr R.lonePath z ∈ cplNodes (SourceApp.closeCouple B Xm Qlp) ((0 : Fin 2), R.lonePath)
        ((1 : Fin 2), []) := by
      rw [hm]
      exact Finset.mem_image_of_mem _ hz
    have hlone : addrExt ((0 : Fin 2), R.lonePath) B.lonePath = ((0 : Fin 2), Xp.lonePath) := by
      rw [hXRB, appendChain_lonePath]
      rfl
    have hEmb : ChainEmb LG.garden (appendChain R B) 1 ((0 : Fin 2), []) Qlp.trees.1 := by
      rw [← hXRB]; exact F'.emb
    have hPLRB : ChainPairLayers LG (appendChain R B) 1 ((0 : Fin 2), []) := by rw [← hXRB]; exact F'.pl
    have hBlay : ∀ x ∈ chainNodesSet B 1 ((0 : Fin 2), R.lonePath), layerAt LG x = q' :=
      chainNodes_layer_of_topAll (chainEmb_append_right hEmb) (chainPairLayers_append_right LG R B 1 _ hPLRB) hB
    unfold SourceApp.closeCouple at hb
    split_ifs at hb with hnil
    · simp only [Bool.and_eq_true] at hnil
      have hBn : B = .nil := by cases B <;> simp_all [RegChain.isNil]
      have hmn : Xm = .nil := by cases Xm <;> simp_all [RegChain.isNil]
      apply F'.lp
      have e1 : ((0 : Fin 2), R.lonePath) = ((0 : Fin 2), Xp.lonePath) := by
        rw [← hlone, hBn]
        simp [RegChain.lonePath, addrExt]
      have e2 : ((1 : Fin 2), ([] : Path)) = ((1 : Fin 2), Xm.lonePath) := by rw [hmn]; rfl
      rw [← e1, ← e2]
      exact hb
    · rcases mem_cplNodes_type2.mp hb with hx | hx | hx
      · exact hBlay _ hx
      · exact F'.minus _ hx
      · apply F'.lp
        rw [hlone] at hx
        exact hx

/-- **Trees**: `SourceApp.tree` is the leafwise leading term at the layer profiles. -/
theorem sourceTree_eq (F : ℕ → Mom d → ℝ) (δ : ℝ) {p q q' : ℕ} {X : RegChain} {LG : LayeredGarden 1}
    (hqq : q' ≤ q) (hcoh : IsCoherentTreeAt p q q' X LG) (t s : ℝ) (k : Mom d) :
    SourceApp.tree δ F LG X q q' t s k = LeafApp.coherentTree δ LG (layerProfiles LG F) X q q' t s k := by
  have F' := treeCohFacts_of_coherent hcoh
  have hsl := fun (r : ℕ) (t s : ℝ) => slice_app_eq LG F δ (LG.garden.sig 0) X.size X ((0 : Fin 1), []) .leaf
    le_rfl F'.wf (ChainEmb.of_decodesTree F'.dec) F'.pl F'.sm r t s k
  by_cases heq : q = q'
  · subst heq
    simp only [SourceApp.tree, LeafApp.coherentTree, ↓reduceIte]
    have hlay := coherentTree_layer_eq hcoh
    rw [← LeafApp.tree_const]
    refine (LeafApp.tree_congr (ChainEmb.of_decodesTree F'.dec) δ q (fun z _ hl => ?_) t s k).symm
    show F (layerAt LG z) = F q
    have hn : z.2 ∈ (LG.garden.tree z.1).nodes := TTree.leaves_subset_nodes _ hl
    rw [show layerAt LG z = q from (layerAt_node LG (⟨z, hn⟩ : GNode LG.garden.tree)).trans (hlay _)]
  · simp only [SourceApp.tree, LeafApp.coherentTree, heq, ↓reduceIte]
    rw [Finset.prod_congr rfl fun r _ => hsl r _ _, hsl q t q, hsl q' _ s]

end WaveTurbulence.PL234
