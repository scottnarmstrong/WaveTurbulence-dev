/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.LowApp

/-!
# One block of the `+` chain: the garden-level step

A lower state of a coherent couple is a couple carrier `LG'` decoded by `closeCouple X Xm Qlp` whose layers are those
of the original carrier `LG` below `(0, π)`, with the transported profiles and leaf bounds (`LowState`).

**`couple_block_step`**: when the chain `X` has its top pair in layer `u` and its next layer is `r'' < u`, the
literal kernel factorizes (`coupleLeaves_split`) as the kernel of the block tree (code `B = takeLayer`, layers `u`,
lone leaf `r''`, profiles `sliceProfiles`) times the kernel of a lower state for the rest `D = dropLayer` at
`π ++ B.lonePath`; the leaf-bound products multiply.
-/

@[expose] public section
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

theorem botAddr_comp (π π' : Path) (z : Fin 2 × Path) :
    botAddr π (botAddr π' z) = botAddr (π ++ π') z := by
  obtain ⟨j, p⟩ := z
  unfold botAddr
  by_cases hj : j = 0
  · subst hj
    simp [List.append_assoc]
  · simp [hj]

theorem botAddr_nil (z : Fin 2 × Path) : botAddr [] z = z := by
  obtain ⟨j, p⟩ := z
  unfold botAddr
  by_cases hj : j = 0
  · subst hj
    simp
  · simp [hj]

/-- **The layers of the bottom couple** are those of the glued couple, at every address. -/
theorem layerAt_botLayered_couple {LG : LayeredGarden 2} {B D Xm : RegChain} {Qlp : RegCpl}
    {G₁ : Garden 1} {G₂ : Garden 2}
    (hQ : (RegCpl.type2 (appendChain B D) Xm Qlp).Decodes LG.garden) (h₁ : B.DecodesTree G₁)
    (hs₁ : G₁.sig 0 = 1) (h₂ : (SourceApp.closeCouple D Xm Qlp).Decodes G₂) (z : Fin 2 × Path) :
    layerAt (botLayered_couple hQ h₁ hs₁ h₂) z = layerAt LG (botAddr B.lonePath z) := by
  set h := glueData_couple hQ h₁ hs₁ h₂
  unfold layerAt
  by_cases hz : z.2 ∈ (G₂.tree z.1).nodes
  · have hz' := (h.bot_iff z).1.mpr hz
    have hz0 : z.2 ∈ ((botLayered_couple hQ h₁ hs₁ h₂).garden.tree z.1).nodes := hz
    simp only [hz0, hz', ↓reduceDIte]
    rfl
  · have hz' : ¬ (botAddr B.lonePath z).2 ∈ (LG.garden.tree (botAddr B.lonePath z).1).nodes :=
      fun hh => hz ((h.bot_iff z).1.mp hh)
    have hz0 : ¬ z.2 ∈ ((botLayered_couple hQ h₁ hs₁ h₂).garden.tree z.1).nodes := hz
    simp only [hz0, hz', ↓reduceDIte]

theorem topAll_of_chainNodes (LG : LayeredGarden 2) (r : ℕ) :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin 2 × Path), (∀ z ∈ chainNodesSet X ζ a, layerAt LG z = r) →
      TopAll LG r a X
  | .nil, _, _, _ => trivial
  | .pair m Qr Qg inner rest, ζ, a, h => by
    refine ⟨h a ?_, topAll_of_chainNodes LG r rest (slotSign (slotSign ζ m.c) m.lone)
      (nextAddr a m inner) fun z hz => h z ?_⟩
    · simp [chainNodesSet, pairEndpoints, RegChain.linksAt]
    · unfold chainNodesSet pairEndpoints at hz ⊢
      simp only [RegChain.linksAt, RegChain.pairsAt, List.map_cons, List.map_append, List.toFinset_cons,
        List.toFinset_append, Finset.mem_union, Finset.mem_insert] at hz ⊢
      tauto

/-- Input leaves of a decoded paired tree are off its lone path. -/
theorem not_prefix_of_inputLeaf {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {ℓ : GLeaf G.tree} (hℓ : ℓ ∈ inputLeaves G) : ¬ X.lonePath <+: ℓ.1.2 := by
  have hm : G.mark ℓ = none := (Finset.mem_filter.mp hℓ).2.2
  have hne : ℓ.1.2 ≠ X.lonePath := by
    intro he
    rw [hX.2.1 ℓ, ite_eq_left he] at hm
    exact absurd hm (by simp)
  rintro ⟨u, hu⟩
  apply hne
  have hl : ℓ.1.2 ∈ (G.tree 0).leaves := by
    have h0 : ℓ.1.1 = 0 := Subsingleton.elim _ _
    have := ℓ.2
    rwa [h0] at this
  rw [hX.1] at hl
  have hn : X.lonePath ∈ (X.plug (G.sig 0) .leaf).nodes := lonePath_mem_plug X _ _
  have hs := (mem_subtreeAt _ _ hn u).2.1.mpr (by rw [hu]; exact hl)
  rw [Links.plug_subtreeAt_lonePath] at hs
  have hu0 : u = [] := by simpa [TTree.leaves] using hs
  rw [← hu, hu0, List.append_nil]

/-- A lower state of a coherent couple below `(0, π)`. -/
structure LowState (LG : LayeredGarden 2) (H : LeafProfiles 2 d) (Bd : (Fin 2 × Path) → NNReal)
    (Xm : RegChain) (Qlp : RegCpl) (π : Path) (X : RegChain) (LG' : LayeredGarden 2) : Prop where
  dec : (SourceApp.closeCouple X Xm Qlp).Decodes LG'.garden
  lay : ∀ z, layerAt LG' z = layerAt LG (botAddr π z)
  ctrl : LeafwiseControlled LG' (fun z => H (botAddr π z)) (fun z => Bd (botAddr π z))

/-- **One block of the `+` chain.** -/
theorem couple_block_step {LG : LayeredGarden 2} {H : LeafProfiles 2 d} {Bd : (Fin 2 × Path) → NNReal}
    {Xm : RegChain} {Qlp : RegCpl} {π : Path} {X : RegChain} {LG' : LayeredGarden 2}
    (S : LowState LG H Bd Xm Qlp π X LG') (L γ δ : ℝ) (hd : 1 ≤ d) (hL : 1 ≤ L)
    (hX : X ≠ .nil) (hwf : (RegCpl.type2 X Xm Qlp).wf = true) {u : ℕ} (hu : layerAt LG (0, π) = u)
    (hlt : layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) < u)
    (hB : ∀ z ∈ chainNodesSet (takeLayer LG (0, π) u X) 1 (0, π), layerAt LG z = u) :
    ∃ (G₁ : LayeredGarden 1) (LG'' : LayeredGarden 2),
      (takeLayer LG (0, π) u X).DecodesTree G₁.garden ∧ G₁.garden.sig 0 = 1 ∧
      (∀ a : GNode G₁.garden.tree, G₁.layer a =
        if a.1.2 = (takeLayer LG (0, π) u X).lonePath then
          layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) else u) ∧
      LeafwiseControlled G₁ (LeafApp.sliceProfiles LG H (0, π) u X)
        (fun z => Bd (LeafApp.sliceAddress LG (0, π) u X z.2)) ∧
      LowState LG H Bd Xm Qlp (π ++ (takeLayer LG (0, π) u X).lonePath) (dropLayer LG (0, π) u X) LG'' ∧
      leafSizeProduct LG' (fun z => Bd (botAddr π z)) =
        leafSizeProduct G₁ (fun z => Bd (LeafApp.sliceAddress LG (0, π) u X z.2)) *
          leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ (takeLayer LG (0, π) u X).lonePath) z)) ∧
      ∀ (t s : ℝ) (k : Mom d), (layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) : ℝ) + 1 ≤ t →
        coupleLeaves L γ δ LG' (fun z => H (botAddr π z)) t s k =
        treeLeaves L γ δ G₁ (LeafApp.sliceProfiles LG H (0, π) u X) t u k *
          coupleLeaves L γ δ LG'' (fun z => H (botAddr (π ++ (takeLayer LG (0, π) u X).lonePath) z))
            ((layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) : ℝ) + 1) s k := by
  set B := takeLayer LG (0, π) u X with hBdef
  set D := dropLayer LG (0, π) u X with hDdef
  have hXe : appendChain B D = X := appendChain_take_drop LG (0, π) u X
  have hTA : TopAll LG u (0, π) B := topAll_takeLayer LG u _ X
  have hcl : SourceApp.closeCouple X Xm Qlp = RegCpl.type2 X Xm Qlp := by
    unfold SourceApp.closeCouple
    have : X.isNil = false := by cases X <;> simp_all [RegChain.isNil]
    simp [this]
  have hQ' : (RegCpl.type2 (appendChain B D) Xm Qlp).Decodes LG'.garden := by
    rw [hXe, ← hcl]
    exact S.dec
  obtain ⟨hBwf, hw₂⟩ := wf_split (hXe ▸ hwf : (RegCpl.type2 (appendChain B D) Xm Qlp).wf = true)
  obtain ⟨G₁g, hs₁, h₁, -⟩ := RegChain.exists_decodesTree B hBwf 1
  obtain ⟨G₂, h₂, -⟩ := RegCpl.exists_decodes (SourceApp.closeCouple D Xm Qlp) hw₂
  have hplain : LG'.garden.IsPlain := hQ'.1.1
  have hplain₂ : G₂.IsPlain := h₂.1.1
  -- the block in layer `u`, in the current carrier
  have hB' : ∀ z ∈ chainNodesSet B 1 ((0 : Fin 2), ([] : Path)), layerAt LG' z = u := by
    intro z hz
    rw [S.lay]
    apply hB
    have hm := chainNodesSet_map B (botAddr π) (botAddr_hom π) 1 ((0 : Fin 2), ([] : Path))
    have h0 : botAddr π ((0 : Fin 2), ([] : Path)) = ((0 : Fin 2), π) := by simp [botAddr]
    rw [h0] at hm
    rw [hm]
    exact Finset.mem_image_of_mem _ hz
  have hr'' : layerAt LG' ((0 : Fin 2), B.lonePath) = layerAt LG (0, π ++ B.lonePath) := by
    rw [S.lay]
    simp [botAddr]
  have hlt' : layerAt LG' ((0 : Fin 2), B.lonePath) < u := by rw [hr'']; exact hlt
  set h := glueData_couple hQ' h₁ hs₁ h₂ with hh
  have hmtop : ∀ ℓ : GLeaf LG'.garden.tree, (ℓ.1.1 = 0 ∧ ¬ B.lonePath <+: ℓ.1.2) →
      LG'.garden.mark ℓ = none := fun ℓ _ => hplain ℓ
  have hmbot : ∀ (ℓ₂ : GLeaf G₂.tree) (ℓ : GLeaf LG'.garden.tree),
      ℓ.1 = botAddr B.lonePath ℓ₂.1 → LG'.garden.mark ℓ = G₂.mark ℓ₂ := fun ℓ₂ ℓ _ => by
    rw [hplain ℓ, hplain₂ ℓ₂]
  -- the original addresses of the block's input leaves
  have haddr : ∀ ℓ ∈ inputLeaves G₁g, LeafApp.sliceAddress LG (0, π) u X ℓ.1.2 = botAddr π (topAddr ℓ.1) := by
    intro ℓ hℓ
    rw [← hXe, sliceAddress_append_of_not_prefix LG u D B (0, π) ℓ.1.2 hTA (not_prefix_of_inputLeaf h₁ hℓ)]
    simp [botAddr, topAddr, addrExt]
  set G₁ := topLayered G₁g B h₁ u (layerAt LG' ((0 : Fin 2), B.lonePath)) hlt'.le with hG₁
  set LG'' := botLayered_couple hQ' h₁ hs₁ h₂ with hLG''
  have hS'' : LowState LG H Bd Xm Qlp (π ++ B.lonePath) D LG'' := by
    refine ⟨h₂, fun z => ?_, fun ℓ₂ hℓ₂ => ?_⟩
    · rw [layerAt_botLayered_couple hQ' h₁ hs₁ h₂, S.lay, botAddr_comp]
    · obtain ⟨ℓ, hℓ, he⟩ := h.inputLeaf_ofBot hmbot ℓ₂ hℓ₂
      have := S.ctrl ℓ hℓ
      show SNormR _ _ (H (botAddr (π ++ B.lonePath) ℓ₂.1)) ≤
        ENNReal.ofReal (Bd (botAddr (π ++ B.lonePath) ℓ₂.1))
      simp only at this
      rw [he, botAddr_comp] at this
      exact this
  refine ⟨G₁, LG'', h₁, hs₁, fun a => ?_, fun ℓ hℓ => ?_, hS'', ?_, fun t s k ht => ?_⟩
  · show (if a.1.2 = B.lonePath then layerAt LG' ((0 : Fin 2), B.lonePath) else u) = _
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
    · exact Finset.prod_congr rfl fun ℓ _ => by rw [botAddr_comp]
  · have hH := S.ctrl.summable_coset hd hL k
    have hsplit := coupleLeaves_split L γ δ hQ' h₁ hs₁ h₂ hB' hlt' (fun z => H (botAddr π z)) k hH
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
      rw [botAddr_comp]

end WaveTurbulence.PL234
