/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiBound
public import WaveTurbulence.Foundations.Spine.PL234Draft.CoupleStep
public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeStep

/-! # FILT-COH (c5): one block of the `+` chain of a coherent couple, with the D5 multiplier

`coupleW_block_step` / `treeW_block_step`: main's `PL234.couple_block_step` / `tree_block_step` (sha256 in COPIED-SHA256SUMS; everything but the kernel
identity copied verbatim) for `kernelLeavesW … (d5Mult …)`: the glue data of the block is exposed, and every D5
multiplier of the lower carrier splits into those of the block (`starTop`, `filtTop`) and of the remaining couple
(`starBot`, `filtBot`) by `coupleW_split`. -/

public section
open WaveTurbulence.Induct
open Finset
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.PL234

variable {d : ℕ}

/-- **One block of the `+` chain, with the D5 multiplier** (main's `PL234.couple_block_step`). -/
theorem coupleW_block_step {LG : LayeredGarden 2} {H : LeafProfiles 2 d} {Bd : (Fin 2 × Path) → NNReal}
    {Xm : RegChain} {Qlp : RegCpl} {π : Path} {X : RegChain} {LG' : LayeredGarden 2}
    (S : LowState LG H Bd Xm Qlp π X LG') (L γ δ : ℝ) (hd : 1 ≤ d) (hL : 1 ≤ L)
    (hX : X ≠ .nil) (hwf : (RegCpl.type2 X Xm Qlp).wf = true) {u : ℕ} (_hu : layerAt LG (0, π) = u)
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
      ∃ hg : GlueData LG'.garden G₁.garden LG''.garden (takeLayer LG (0, π) u X),
      ∀ (t s : ℝ) (k : Mom d), (layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) : ℝ) + 1 ≤ t →
      ∀ (J : ℕ) (Sst : Finset (GNode LG'.garden.tree)) (ω : GNode LG'.garden.tree → IncTop.Star d → ℂ)
        (c : GNode LG'.garden.tree → ℝ), (∀ a ∈ Sst, IncTop.StarPresented J (ω a) (c a)) →
      ∀ (F : Finset (GBranch LG'.garden.tree)) (ann : GBranch LG'.garden.tree → Bool)
        (M : GBranch LG'.garden.tree → ℝ) (Fu : Finset (GBranch LG'.garden.tree)) (Mu : GBranch LG'.garden.tree → ℝ),
        Flower.Stage1W.kernelLeavesW L γ δ LG' (fun z => H (botAddr π z))
            (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0 (d5Mult Sst ω F ann M Fu Mu) =
          Flower.Stage1W.kernelLeavesW L γ δ G₁ (LeafApp.sliceProfiles LG H (0, π) u X) (fun _ => t) u k
              (fun _ => 0) 0
              (d5Mult (starTop hg Sst) (fun x => ω (hg.ι₁ x)) (filtTop hg F) (fun x => ann (hg.ofSum (.inl x)))
                (fun x => M (hg.ofSum (.inl x))) (filtTop hg Fu) (fun x => Mu (hg.ofSum (.inl x)))) *
            Flower.Stage1W.kernelLeavesW L γ δ LG''
              (fun z => H (botAddr (π ++ (takeLayer LG (0, π) u X).lonePath) z))
              (fun b => if b.1.1 = 0 then (layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) : ℝ) + 1 else s) 0 k
              (fun _ => 0) 0
              (d5Mult (starBot hg Sst) (fun y => ω (hg.ι₂ y)) (filtBot hg F) (fun y => ann (hg.ofSum (.inr y)))
                (fun y => M (hg.ofSum (.inr y))) (filtBot hg Fu) (fun y => Mu (hg.ofSum (.inr y)))) := by
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
  refine ⟨G₁, LG'', h₁, hs₁, fun a => ?_, fun ℓ hℓ => ?_, hS'', ?_, ?_⟩
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
  · refine ⟨h, fun t s k ht J Sst ω c hpres F ann M Fu Mu => ?_⟩
    have hH := S.ctrl.summable_coset hd hL k
    have hsplit := coupleW_split L γ δ hQ' h₁ hs₁ h₂ hB' hlt' (fun z => H (botAddr π z)) k hH
      t s (by rw [hr'']; exact ht) Sst ω F ann M Fu Mu _ _
      (norm_d5Mult_le _ _ (fun x => c (h.ι₁ x)) (fun x hx => hpres _ (mem_starTop h hx)) _ _ _ _ _)
      (norm_d5Mult_le _ _ (fun y => c (h.ι₂ y)) (fun y hy => hpres _ (mem_starBot h hy)) _ _ _ _ _)
    rw [hsplit]
    congr 1
    · exact kernelLeavesW_congr_H' L γ δ G₁ _ _ (fun ℓ hℓ => by
        show H (botAddr π (topAddr ℓ.1)) = H (LeafApp.sliceAddress LG (0, π) u X ℓ.1.2)
        rw [haddr ℓ hℓ]) _ _ _ _ _ _
    · rw [hr'']
      refine kernelLeavesW_congr_H' L γ δ LG'' _ _ (fun ℓ _ => ?_) _ _ _ _ _ _
      show H (botAddr π (botAddr B.lonePath ℓ.1)) = H (botAddr (π ++ B.lonePath) ℓ.1)
      rw [botAddr_comp]

/-- **One block of the chain of a tree.** -/
theorem treeW_block_step {LG : LayeredGarden 1} {H : LeafProfiles 1 d} {Bd : (Fin 1 × Path) → NNReal}
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
      ∃ hg : GlueData LG'.garden G₁.garden LG''.garden (takeLayer LG (0, π) u X),
      ∀ (t s : ℝ) (k : Mom d), (layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) : ℝ) + 1 ≤ t →
      ∀ (J : ℕ) (Sst : Finset (GNode LG'.garden.tree)) (ω : GNode LG'.garden.tree → IncTop.Star d → ℂ)
        (c : GNode LG'.garden.tree → ℝ), (∀ a ∈ Sst, IncTop.StarPresented J (ω a) (c a)) →
      ∀ (F : Finset (GBranch LG'.garden.tree)) (ann : GBranch LG'.garden.tree → Bool)
        (M : GBranch LG'.garden.tree → ℝ) (Fu : Finset (GBranch LG'.garden.tree)) (Mu : GBranch LG'.garden.tree → ℝ),
        Flower.Stage1W.kernelLeavesW L γ δ LG' (fun z => H (botAddr π z)) (fun _ => t) s k (fun _ => 0) 0
            (d5Mult Sst ω F ann M Fu Mu) =
          Flower.Stage1W.kernelLeavesW L γ δ G₁ (LeafApp.sliceProfiles LG H (0, π) u X) (fun _ => t) u k
              (fun _ => 0) 0
              (d5Mult (starTop hg Sst) (fun x => ω (hg.ι₁ x)) (filtTop hg F) (fun x => ann (hg.ofSum (.inl x)))
                (fun x => M (hg.ofSum (.inl x))) (filtTop hg Fu) (fun x => Mu (hg.ofSum (.inl x)))) *
            Flower.Stage1W.kernelLeavesW L γ δ LG''
              (fun z => H (botAddr (π ++ (takeLayer LG (0, π) u X).lonePath) z))
              (fun _ => (layerAt LG (0, π ++ (takeLayer LG (0, π) u X).lonePath) : ℝ) + 1) s k (fun _ => 0) 0
              (d5Mult (starBot hg Sst) (fun y => ω (hg.ι₂ y)) (filtBot hg F) (fun y => ann (hg.ofSum (.inr y)))
                (fun y => M (hg.ofSum (.inr y))) (filtBot hg Fu) (fun y => Mu (hg.ofSum (.inr y)))) := by
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
  refine ⟨G₁, LG'', h₁, hs₁.trans S.sig, fun a => ?_, fun ℓ hℓ => ?_, hS'', ?_, ?_⟩
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
  · refine ⟨h, fun t s k ht J Sst ω c hpres F ann M Fu Mu => ?_⟩
    have hH := S.ctrl.summable_coset hd hL k
    have hsplit := treeW_split L γ δ hG hDne h₁ hs₁ h₂ hs₂ hB' hlt' (fun z => H (botAddr π z)) k hH
      t s (by rw [hr'']; exact ht) Sst ω F ann M Fu Mu _ _
      (norm_d5Mult_le _ _ (fun x => c (h.ι₁ x)) (fun x hx => hpres _ (mem_starTop h hx)) _ _ _ _ _)
      (norm_d5Mult_le _ _ (fun y => c (h.ι₂ y)) (fun y hy => hpres _ (mem_starBot h hy)) _ _ _ _ _)
    rw [hsplit]
    congr 1
    · exact kernelLeavesW_congr_H' L γ δ G₁ _ _ (fun ℓ hℓ => by
        show H (botAddr π (topAddr ℓ.1)) = H (LeafApp.sliceAddress LG (0, π) u X ℓ.1.2)
        rw [haddr ℓ hℓ]) _ _ _ _ _ _
    · rw [hr'']
      refine kernelLeavesW_congr_H' L γ δ LG'' _ _ (fun ℓ _ => ?_) _ _ _ _ _ _
      show H (botAddr π (botAddr B.lonePath ℓ.1)) = H (botAddr (π ++ B.lonePath) ℓ.1)
      rw [botAddr_comp_tree]

end WaveTurbulence.Flower.FiltCoh
