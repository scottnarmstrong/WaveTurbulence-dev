/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiGlue
public import WaveTurbulence.Foundations.Spine.PL234Draft.SplitCouple
public import WaveTurbulence.Foundations.Spine.PL234Draft.SplitTree

/-! # FILT-COH (c5): splitting off the top block of a coherent couple, with the D5 multiplier

`coupleW_split`: main's `PL234.coupleLeaves_split` (sha256 in COPIED-SHA256SUMS; the domain splitting `hD` is copied
verbatim) for the multiplied kernel `kernelLeavesW … (d5Mult …)`: the multiplier factors through main's glue data
(`d5Mult_glue`) and `kernelLeavesW_glue` gives the product. `summable_mult_leavesSummand`: a bounded multiplier
keeps main's leafwise summability. -/

public section
open WaveTurbulence.Induct
open MeasureTheory Finset
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine WaveTurbulence.PL234
open scoped ENNReal

theorem summable_mult_leavesSummand {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (Mb : ℝ) (hm : ∀ κ, ‖m κ‖ ≤ Mb)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|) :
    Summable fun κ : GenDecoration LG.garden d (fun _ => 0) 0 =>
      ‖m (cosetDecoration LG.garden L k₀ κ.1) * leavesSummand L γ δ LG H up s k₀ κ‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun κ => ?_)
    ((summable_norm_leavesSummand L γ δ LG H up s k₀ (fun _ => 0) 0 hlone hH).mul_left Mb)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hm _) (norm_nonneg _)

section Couple

variable {LG : LayeredGarden 2} {B D Xm : RegChain} {Qlp : RegCpl}

/-- **Splitting off the top block of a couple, with the D5 multiplier** (main's `PL234.coupleLeaves_split`). -/
theorem coupleW_split (L γ δ : ℝ) {d : ℕ}
    (hQ : (RegCpl.type2 (appendChain B D) Xm Qlp).Decodes LG.garden)
    {G₁ : Garden 1} (h₁ : B.DecodesTree G₁) (hs₁ : G₁.sig 0 = 1)
    {G₂ : Garden 2} (h₂ : (SourceApp.closeCouple D Xm Qlp).Decodes G₂) {r : ℕ}
    (hB : ∀ z ∈ chainNodesSet B 1 ((0 : Fin 2), ([] : Path)), layerAt LG z = r)
    (hlt : layerAt LG ((0 : Fin 2), B.lonePath) < r)
    (H : LeafProfiles 2 d) (k : Mom d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|)
    (t s : ℝ) (ht : (layerAt LG ((0 : Fin 2), B.lonePath) : ℝ) + 1 ≤ t)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (Mb₁ Mb₂ : ℝ)
    (hb₁ : ∀ κ, ‖d5Mult ((starTop (glueData_couple hQ h₁ hs₁ h₂)) S)
      (fun x => ω ((glueData_couple hQ h₁ hs₁ h₂).ι₁ x)) ((filtTop (glueData_couple hQ h₁ hs₁ h₂)) F)
      (fun x => ann ((glueData_couple hQ h₁ hs₁ h₂).ofSum (.inl x)))
      (fun x => M ((glueData_couple hQ h₁ hs₁ h₂).ofSum (.inl x))) ((filtTop (glueData_couple hQ h₁ hs₁ h₂)) Fu)
      (fun x => Mu ((glueData_couple hQ h₁ hs₁ h₂).ofSum (.inl x))) κ‖ ≤ Mb₁)
    (hb₂ : ∀ κ, ‖d5Mult ((starBot (glueData_couple hQ h₁ hs₁ h₂)) S)
      (fun y => ω ((glueData_couple hQ h₁ hs₁ h₂).ι₂ y)) ((filtBot (glueData_couple hQ h₁ hs₁ h₂)) F)
      (fun y => ann ((glueData_couple hQ h₁ hs₁ h₂).ofSum (.inr y)))
      (fun y => M ((glueData_couple hQ h₁ hs₁ h₂).ofSum (.inr y))) ((filtBot (glueData_couple hQ h₁ hs₁ h₂)) Fu)
      (fun y => Mu ((glueData_couple hQ h₁ hs₁ h₂).ofSum (.inr y))) κ‖ ≤ Mb₂) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0
        (d5Mult S ω F ann M Fu Mu) =
      Flower.Stage1W.kernelLeavesW L γ δ (topLayered G₁ B h₁ r (layerAt LG ((0 : Fin 2), B.lonePath)) hlt.le)
          (fun z => H (topAddr z)) (fun _ => t) r k (fun _ => 0) 0
          (d5Mult ((starTop (glueData_couple hQ h₁ hs₁ h₂)) S)
            (fun x => ω ((glueData_couple hQ h₁ hs₁ h₂).ι₁ x)) ((filtTop (glueData_couple hQ h₁ hs₁ h₂)) F)
            (fun x => ann ((glueData_couple hQ h₁ hs₁ h₂).ofSum (.inl x)))
            (fun x => M ((glueData_couple hQ h₁ hs₁ h₂).ofSum (.inl x))) ((filtTop (glueData_couple hQ h₁ hs₁ h₂)) Fu)
            (fun x => Mu ((glueData_couple hQ h₁ hs₁ h₂).ofSum (.inl x)))) *
        Flower.Stage1W.kernelLeavesW L γ δ (botLayered_couple hQ h₁ hs₁ h₂) (fun z => H (botAddr B.lonePath z))
          (fun b => if b.1.1 = 0 then (layerAt LG ((0 : Fin 2), B.lonePath) : ℝ) + 1 else s) 0 k (fun _ => 0) 0
          (d5Mult ((starBot (glueData_couple hQ h₁ hs₁ h₂)) S)
            (fun y => ω ((glueData_couple hQ h₁ hs₁ h₂).ι₂ y)) ((filtBot (glueData_couple hQ h₁ hs₁ h₂)) F)
            (fun y => ann ((glueData_couple hQ h₁ hs₁ h₂).ofSum (.inr y)))
            (fun y => M ((glueData_couple hQ h₁ hs₁ h₂).ofSum (.inr y))) ((filtBot (glueData_couple hQ h₁ hs₁ h₂)) Fu)
            (fun y => Mu ((glueData_couple hQ h₁ hs₁ h₂).ofSum (.inr y)))) := by
  set r'' := layerAt LG ((0 : Fin 2), B.lonePath) with hr''
  set h := glueData_couple hQ h₁ hs₁ h₂ with hh
  have hplain : LG.garden.IsPlain := hQ.1.1
  have hplain₂ : G₂.IsPlain := h₂.1.1
  have hmtop : ∀ ℓ : GLeaf LG.garden.tree, (ℓ.1.1 = 0 ∧ ¬ B.lonePath <+: ℓ.1.2) →
      LG.garden.mark ℓ = none := fun ℓ _ => hplain ℓ
  have hmbot : ∀ (ℓ₂ : GLeaf G₂.tree) (ℓ : GLeaf LG.garden.tree),
      ℓ.1 = botAddr B.lonePath ℓ₂.1 → LG.garden.mark ℓ = G₂.mark ℓ₂ := fun ℓ₂ ℓ _ => by
    rw [hplain ℓ, hplain₂ ℓ₂]
  -- the lone position and the bottom tree `0`
  have nLone : ((0 : Fin 2), B.lonePath).2 ∈ (LG.garden.tree ((0 : Fin 2), B.lonePath).1).nodes := by
    show B.lonePath ∈ (LG.garden.tree 0).nodes
    rw [h.tree0]
    exact lonePath_mem_plug B _ _
  have hbot0 : ∀ y : GNode G₂.tree, y.1.1 = 0 → LG.layer (h.ι₂ y) ≤ r'' := by
    intro y hy
    rw [← layerAt_node LG (h.ι₂ y)]
    have e : (h.ι₂ y).1 = addrExt ((0 : Fin 2), B.lonePath) y.1.2 := by
      show botAddr B.lonePath y.1 = _
      obtain ⟨⟨j, p⟩, _⟩ := y
      simp only at hy
      subst hy
      simp [botAddr, addrExt]
    have hu : Under ((0 : Fin 2), B.lonePath) (h.ι₂ y).1 := by rw [e]; exact under_ext _ _
    exact layerAt_le_of_under LG nLone (h.ι₂ y).2 hu
  have hD : ∀ τ, τ ∈ kDomain LG (fun b => if b.1.1 = 0 then t else s) 0 ↔
      (fun x => τ (h.ofSum (.inl x))) ∈
        kDomain (topLayered G₁ B h₁ r r'' hlt.le) (fun _ => t) r ∧
      (fun y => τ (h.ofSum (.inr y))) ∈ kDomain (botLayered_couple hQ h₁ hs₁ h₂)
        (fun b => if b.1.1 = 0 then (r'' : ℝ) + 1 else s) 0 := by
    intro τ
    have hlay₁ : ∀ x : GBranch G₁.tree, topLayer G₁ B r r'' x.toNode = r := by
      intro x
      unfold topLayer
      refine ite_eq_right fun he => ?_
      have he' : x.1.2 = B.lonePath := he
      have hl : x.1.2 ∈ (G₁.tree x.1.1).leaves := by
        rw [Subsingleton.elim x.1.1 0, h₁.1, hs₁, he']
        exact lonePath_mem_leaves B _
      exact TTree.not_mem_branching_of_mem_leaves _ hl x.2
    refine kDomain_glue (LG₁ := topLayered G₁ B h₁ r r'' hlt.le)
      (LG₂ := botLayered_couple hQ h₁ hs₁ h₂) h _ 0 _ r _ 0 ?_ (fun _ => rfl) ?_ ?_ ?_ ?_ rfl ?_ τ
    · intro x
      refine (hlay₁ x).trans ?_
      rw [← layerAt_node]
      refine (hB _ ?_).symm
      have hm : x.1.2 ∈ (B.plug 1 .leaf).branching := by
        have hx := x.2
        have e : (topLayered G₁ B h₁ r r'' hlt.le).garden.tree x.1.1 = B.plug 1 .leaf := by
          show G₁.tree x.1.1 = _
          rw [Subsingleton.elim x.1.1 0, h₁.1, hs₁]
        rw [e] at hx
        exact hx
      exact mem_chainNodes_of_branch hm
    · intro x
      rfl
    · intro y
      by_cases hy : y.1.1 = 0
      · right
        have hle := hbot0 y.toNode hy
        have hle' : (LG.layer (h.ι₂ y.toNode) : ℝ) ≤ r'' := by exact_mod_cast hle
        show (LG.layer (h.ι₂ y.toNode) : ℝ) + 1 ≤ (if (h.ofSum (.inr y)).1.1 = 0 then t else s) ∧
          (LG.layer (h.ι₂ y.toNode) : ℝ) + 1 ≤ (if y.1.1 = 0 then (r'' : ℝ) + 1 else s)
        have e : (h.ofSum (.inr y)).1.1 = 0 := by
          show (botAddr B.lonePath y.1).1 = 0
          obtain ⟨⟨j, p⟩, _⟩ := y
          simp only at hy
          subst hy
          simp [botAddr]
        rw [ite_eq_left e, ite_eq_left hy]
        exact ⟨by linarith, by linarith⟩
      · left
        have e : ¬ (h.ofSum (.inr y)).1.1 = 0 := by
          show ¬ (botAddr B.lonePath y.1).1 = 0
          obtain ⟨⟨j, p⟩, _⟩ := y
          simp only at hy
          simp [botAddr, hy]
        show (if (h.ofSum (.inr y)).1.1 = 0 then t else s) = if y.1.1 = 0 then (r'' : ℝ) + 1 else s
        rw [ite_eq_right e, ite_eq_right hy]
    · intro x y hc
      have hy : y.1.1 = 0 := by
        obtain ⟨h1, -⟩ := hc
        change (botAddr B.lonePath y.1).1 = (0 : Fin 2) at h1
        obtain ⟨⟨j, p⟩, _⟩ := y
        by_contra hj
        simp only at hj
        simp [botAddr, hj] at h1
      have hle := hbot0 y.toNode hy
      have e : ((topLayered G₁ B h₁ r r'' hlt.le).layer x.toNode : ℝ) = r := by
        exact_mod_cast hlay₁ x
      have : (LG.layer (h.ι₂ y.toNode) : ℝ) ≤ r'' := by exact_mod_cast hle
      have hlt' : (r'' : ℝ) + 1 ≤ r := by exact_mod_cast hlt
      show (LG.layer (h.ι₂ y.toNode) : ℝ) + 1 ≤ ((topLayered G₁ B h₁ r r'' hlt.le).layer x.toNode : ℝ)
      rw [e]
      linarith
    · intro b
      exact iff_of_false (not_loneParent_of_plain hplain b)
        (fun ⟨y, _, hy⟩ => not_loneParent_of_plain hplain₂ y hy)
    · intro x _
      have e : ((topLayered G₁ B h₁ r r'' hlt.le).layer x.toNode : ℝ) = r := by
        exact_mod_cast hlay₁ x
      rw [e]
  have hH₁ : ∀ ℓ ∈ inputLeaves G₁,
      Summable fun n : Fin d → ℤ => |H (topAddr ℓ.1) (k + latticePoint L n)| := by
    intro ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := h.inputLeaf_ofTop h₁.2.1 hmtop ℓ hℓ
    rw [← he]
    exact hH ℓ' hℓ'
  have hH₂ : ∀ ℓ ∈ inputLeaves G₂,
      Summable fun n : Fin d → ℤ => |H (botAddr B.lonePath ℓ.1) (k + latticePoint L n)| := by
    intro ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := h.inputLeaf_ofBot hmbot ℓ hℓ
    rw [← he]
    exact hH ℓ' hℓ'
  exact kernelLeavesW_glue L γ δ (LG₁ := topLayered G₁ B h₁ r r'' hlt.le)
    (LG₂ := botLayered_couple hQ h₁ hs₁ h₂) h (decSplit_couple hQ h₁ hs₁ h₂)
    (decGlue_couple hQ h₁ hs₁ h₂) (not_flower_of_plain hplain) (not_flower_of_decodesTree h₁)
    (not_flower_of_plain hplain₂) h₁.2.1 hmtop hmbot H _ 0 _ r _ 0 hD k _ _ _ ((d5Mult_glue h) S ω F ann M Fu Mu)
    (summable_mult_leavesSummand L γ δ _ _ _ _ k _ Mb₁ hb₁ (card_lone_le_of_decodesTree h₁) hH₁)
    (summable_mult_leavesSummand L γ δ _ _ _ _ k _ Mb₂ hb₂ (card_lone_le_of_plain hplain₂) hH₂)

end Couple

section Tree

variable {LG : LayeredGarden 1} {B D : RegChain}

/-- **Splitting off the top block of a regular tree, with the D5 multiplier** (main's `PL234.treeLeaves_split`). -/
theorem treeW_split (L γ δ : ℝ) {d : ℕ}
    (hG : (appendChain B D).DecodesTree LG.garden) (hDne : D ≠ .nil)
    {G₁ : Garden 1} (h₁ : B.DecodesTree G₁) (hs₁ : G₁.sig 0 = LG.garden.sig 0)
    {G₂ : Garden 1} (h₂ : D.DecodesTree G₂) (hs₂ : G₂.sig 0 = LG.garden.sig 0) {r : ℕ}
    (hB : ∀ z ∈ chainNodesSet B (LG.garden.sig 0) ((0 : Fin 1), ([] : Path)), layerAt LG z = r)
    (hlt : layerAt LG ((0 : Fin 1), B.lonePath) < r)
    (H : LeafProfiles 1 d) (k : Mom d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|)
    (t s : ℝ) (ht : (layerAt LG ((0 : Fin 1), B.lonePath) : ℝ) + 1 ≤ t)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (Mb₁ Mb₂ : ℝ) (hb₁ : ∀ κ, ‖(d5Mult ((starTop (glueData_tree hG h₁ hs₁ h₂ hs₂)) S) (fun x => ω ((glueData_tree hG h₁ hs₁ h₂ hs₂).ι₁ x)) ((filtTop (glueData_tree hG h₁ hs₁ h₂ hs₂)) F)
            (fun x => ann ((glueData_tree hG h₁ hs₁ h₂ hs₂).ofSum (.inl x))) (fun x => M ((glueData_tree hG h₁ hs₁ h₂ hs₂).ofSum (.inl x))) ((filtTop (glueData_tree hG h₁ hs₁ h₂ hs₂)) Fu)
            (fun x => Mu ((glueData_tree hG h₁ hs₁ h₂ hs₂).ofSum (.inl x)))) κ‖ ≤ Mb₁) (hb₂ : ∀ κ, ‖(d5Mult ((starBot (glueData_tree hG h₁ hs₁ h₂ hs₂)) S) (fun y => ω ((glueData_tree hG h₁ hs₁ h₂ hs₂).ι₂ y)) ((filtBot (glueData_tree hG h₁ hs₁ h₂ hs₂)) F)
            (fun y => ann ((glueData_tree hG h₁ hs₁ h₂ hs₂).ofSum (.inr y))) (fun y => M ((glueData_tree hG h₁ hs₁ h₂ hs₂).ofSum (.inr y))) ((filtBot (glueData_tree hG h₁ hs₁ h₂ hs₂)) Fu)
            (fun y => Mu ((glueData_tree hG h₁ hs₁ h₂ hs₂).ofSum (.inr y)))) κ‖ ≤ Mb₂) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0 (d5Mult S ω F ann M Fu Mu) =
      Flower.Stage1W.kernelLeavesW L γ δ (topLayered G₁ B h₁ r (layerAt LG ((0 : Fin 1), B.lonePath)) hlt.le)
          (fun z => H (topAddr z)) (fun _ => t) r k (fun _ => 0) 0
          (d5Mult ((starTop (glueData_tree hG h₁ hs₁ h₂ hs₂)) S) (fun x => ω ((glueData_tree hG h₁ hs₁ h₂ hs₂).ι₁ x)) ((filtTop (glueData_tree hG h₁ hs₁ h₂ hs₂)) F)
            (fun x => ann ((glueData_tree hG h₁ hs₁ h₂ hs₂).ofSum (.inl x))) (fun x => M ((glueData_tree hG h₁ hs₁ h₂ hs₂).ofSum (.inl x))) ((filtTop (glueData_tree hG h₁ hs₁ h₂ hs₂)) Fu)
            (fun x => Mu ((glueData_tree hG h₁ hs₁ h₂ hs₂).ofSum (.inl x)))) *
        Flower.Stage1W.kernelLeavesW L γ δ (botLayered_tree hG h₁ hs₁ h₂ hs₂) (fun z => H (botAddr B.lonePath z))
          (fun _ => (layerAt LG ((0 : Fin 1), B.lonePath) : ℝ) + 1) s k (fun _ => 0) 0
          (d5Mult ((starBot (glueData_tree hG h₁ hs₁ h₂ hs₂)) S) (fun y => ω ((glueData_tree hG h₁ hs₁ h₂ hs₂).ι₂ y)) ((filtBot (glueData_tree hG h₁ hs₁ h₂ hs₂)) F)
            (fun y => ann ((glueData_tree hG h₁ hs₁ h₂ hs₂).ofSum (.inr y))) (fun y => M ((glueData_tree hG h₁ hs₁ h₂ hs₂).ofSum (.inr y))) ((filtBot (glueData_tree hG h₁ hs₁ h₂ hs₂)) Fu)
            (fun y => Mu ((glueData_tree hG h₁ hs₁ h₂ hs₂).ofSum (.inr y)))) := by
  set r'' := layerAt LG ((0 : Fin 1), B.lonePath) with hr''
  set h := glueData_tree hG h₁ hs₁ h₂ hs₂ with hh
  have hlp : (appendChain B D).lonePath = B.lonePath ++ D.lonePath := appendChain_lonePath B D
  have hDlp := lonePath_ne_nil_of_ne_nil hDne
  have hmtop : ∀ ℓ : GLeaf LG.garden.tree, (ℓ.1.1 = 0 ∧ ¬ B.lonePath <+: ℓ.1.2) →
      LG.garden.mark ℓ = none := by
    intro ℓ hℓ
    rw [hG.2.1 ℓ, hlp]
    refine ite_eq_right fun he => hℓ.2 ?_
    rw [he]
    exact List.prefix_append _ _
  have hmbot : ∀ (ℓ₂ : GLeaf G₂.tree) (ℓ : GLeaf LG.garden.tree),
      ℓ.1 = botAddr B.lonePath ℓ₂.1 → LG.garden.mark ℓ = G₂.mark ℓ₂ := by
    intro ℓ₂ ℓ he
    rw [hG.2.1 ℓ, h₂.2.1 ℓ₂, hlp]
    have hp : ℓ.1.2 = B.lonePath ++ ℓ₂.1.2 := by
      rw [he]
      have hj : ℓ₂.1.1 = 0 := Subsingleton.elim _ _
      simp [botAddr, hj]
    rw [hp]
    simp only [List.append_cancel_left_eq]
  have nLone : ((0 : Fin 1), B.lonePath).2 ∈ (LG.garden.tree ((0 : Fin 1), B.lonePath).1).nodes := by
    show B.lonePath ∈ (LG.garden.tree 0).nodes
    rw [h.tree0]
    exact lonePath_mem_plug B _ _
  have hbot0 : ∀ y : GNode G₂.tree, LG.layer (h.ι₂ y) ≤ r'' := by
    intro y
    rw [← layerAt_node LG (h.ι₂ y)]
    have e : (h.ι₂ y).1 = addrExt ((0 : Fin 1), B.lonePath) y.1.2 := by
      show botAddr B.lonePath y.1 = _
      obtain ⟨⟨j, p⟩, _⟩ := y
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp [botAddr, addrExt]
    have hu : Under ((0 : Fin 1), B.lonePath) (h.ι₂ y).1 := by rw [e]; exact under_ext _ _
    exact layerAt_le_of_under LG nLone (h.ι₂ y).2 hu
  have hlay₁ : ∀ x : GBranch G₁.tree, topLayer G₁ B r r'' x.toNode = r := by
    intro x
    unfold topLayer
    refine ite_eq_right fun he => ?_
    have he' : x.1.2 = B.lonePath := he
    have hl : x.1.2 ∈ (G₁.tree x.1.1).leaves := by
      rw [Subsingleton.elim x.1.1 0, h₁.1, he']
      exact lonePath_mem_leaves B _
    exact TTree.not_mem_branching_of_mem_leaves _ hl x.2
  -- the lone parents of the glued tree are those of the bottom tree
  have hloneG : ∀ b : GBranch LG.garden.tree, LG.garden.IsLoneParent b ↔
      ∃ i : Fin 3, b.1.2 ++ [i] = B.lonePath ++ D.lonePath := by
    intro b
    constructor
    · rintro ⟨ℓ, hℓ, -, i, hi⟩
      have hpath : ℓ.1.2 = B.lonePath ++ D.lonePath := by
        by_contra hne
        unfold Garden.IsLone at hℓ
        rw [hG.2.1 ℓ, hlp, ite_eq_right hne] at hℓ
        exact absurd hℓ (by simp)
      exact ⟨i, hi.symm.trans hpath⟩
    · rintro ⟨i, hi⟩
      have hmem : (B.lonePath ++ D.lonePath) ∈ (LG.garden.tree b.1.1).leaves := by
        rw [Subsingleton.elim b.1.1 0, hG.1, ← hlp]
        exact lonePath_mem_leaves _ _
      refine ⟨⟨(b.1.1, B.lonePath ++ D.lonePath), hmem⟩, ?_, rfl, i, hi.symm⟩
      unfold Garden.IsLone
      exact (hG.2.1 _).trans (by simp [hlp])
  have hloneG₂ : ∀ y : GBranch G₂.tree, G₂.IsLoneParent y ↔ ∃ i : Fin 3, y.1.2 ++ [i] = D.lonePath := by
    intro y
    constructor
    · rintro ⟨ℓ, hℓ, -, i, hi⟩
      have hpath : ℓ.1.2 = D.lonePath := by
        by_contra hne
        unfold Garden.IsLone at hℓ
        rw [h₂.2.1 ℓ, ite_eq_right hne] at hℓ
        exact absurd hℓ (by simp)
      exact ⟨i, hi.symm.trans hpath⟩
    · rintro ⟨i, hi⟩
      have hmem : D.lonePath ∈ (G₂.tree y.1.1).leaves := by
        rw [Subsingleton.elim y.1.1 0, h₂.1]
        exact lonePath_mem_leaves _ _
      refine ⟨⟨(y.1.1, D.lonePath), hmem⟩, ?_, rfl, i, hi.symm⟩
      unfold Garden.IsLone
      exact (h₂.2.1 _).trans (by simp)
  have hlone : ∀ b, LG.garden.IsLoneParent b ↔ ∃ y, b = h.ofSum (.inr y) ∧ G₂.IsLoneParent y := by
    intro b
    rw [← h.ofSum_toSum b]
    rcases h.toSum b with x | y
    · refine iff_of_false ?_ ?_
      · rw [hloneG]
        rintro ⟨i, hi⟩
        have hx : ¬ B.lonePath <+: x.1.2 := by
          have hm := x.2
          rw [Subsingleton.elim x.1.1 0] at hm
          exact ((h.top_branch_iff _).mp hm).2
        apply hx
        obtain ⟨D', iD, hD'⟩ := (List.eq_nil_or_concat D.lonePath).resolve_left hDlp
        have hi' : x.1.2 ++ [i] = (B.lonePath ++ D') ++ [iD] := by
          have hi2 : x.1.2 ++ [i] = B.lonePath ++ D.lonePath := hi
          rw [hi2, hD', List.concat_eq_append, List.append_assoc]
        rw [(List.append_inj' hi' rfl).1]
        exact List.prefix_append _ _
      · rintro ⟨y, hy, -⟩
        exact absurd (h.ofSum_injective hy) (by simp)
    · rw [hloneG]
      constructor
      · rintro ⟨i, hi⟩
        refine ⟨y, rfl, (hloneG₂ y).mpr ⟨i, ?_⟩⟩
        have e : (h.ofSum (.inr y)).1.2 = B.lonePath ++ y.1.2 := by
          show (botAddr B.lonePath y.1).2 = _
          have hj : y.1.1 = 0 := Subsingleton.elim _ _
          obtain ⟨⟨j, p⟩, _⟩ := y
          simp only at hj
          subst hj
          simp [botAddr]
        rw [e, List.append_assoc] at hi
        exact List.append_cancel_left hi
      · rintro ⟨y', hy', hl⟩
        have : y = y' := by simpa using h.ofSum_injective hy'
        subst this
        obtain ⟨i, hi⟩ := (hloneG₂ y).mp hl
        refine ⟨i, ?_⟩
        have e : (h.ofSum (.inr y)).1.2 = B.lonePath ++ y.1.2 := by
          show (botAddr B.lonePath y.1).2 = _
          have hj : y.1.1 = 0 := Subsingleton.elim _ _
          obtain ⟨⟨j, p⟩, _⟩ := y
          simp only at hj
          subst hj
          simp [botAddr]
        rw [e, List.append_assoc, hi]
  have hD : ∀ τ, τ ∈ kDomain LG (fun _ => t) s ↔
      (fun x => τ (h.ofSum (.inl x))) ∈ kDomain (topLayered G₁ B h₁ r r'' hlt.le) (fun _ => t) r ∧
      (fun y => τ (h.ofSum (.inr y))) ∈ kDomain (botLayered_tree hG h₁ hs₁ h₂ hs₂)
        (fun _ => (r'' : ℝ) + 1) s := by
    intro τ
    refine kDomain_glue (LG₁ := topLayered G₁ B h₁ r r'' hlt.le)
      (LG₂ := botLayered_tree hG h₁ hs₁ h₂ hs₂) h _ s _ r _ s ?_ (fun _ => rfl) (fun _ => rfl) ?_ ?_
      hlone rfl ?_ τ
    · intro x
      refine (hlay₁ x).trans ?_
      rw [← layerAt_node]
      refine (hB _ ?_).symm
      have hm : x.1.2 ∈ (B.plug (LG.garden.sig 0) .leaf).branching := by
        have hx := x.2
        have e : (topLayered G₁ B h₁ r r'' hlt.le).garden.tree x.1.1 = B.plug (LG.garden.sig 0) .leaf := by
          show G₁.tree x.1.1 = _
          rw [Subsingleton.elim x.1.1 0, h₁.1, hs₁]
        rw [e] at hx
        exact hx
      exact mem_chainNodes_of_branch hm
    · intro y
      right
      have hle : (LG.layer (h.ι₂ y.toNode) : ℝ) ≤ r'' := by exact_mod_cast hbot0 y.toNode
      show (LG.layer (h.ι₂ y.toNode) : ℝ) + 1 ≤ t ∧ (LG.layer (h.ι₂ y.toNode) : ℝ) + 1 ≤ (r'' : ℝ) + 1
      exact ⟨by linarith, by linarith⟩
    · intro x y _
      have e : ((topLayered G₁ B h₁ r r'' hlt.le).layer x.toNode : ℝ) = r := by
        exact_mod_cast hlay₁ x
      have hle : (LG.layer (h.ι₂ y.toNode) : ℝ) ≤ r'' := by exact_mod_cast hbot0 y.toNode
      have hlt' : (r'' : ℝ) + 1 ≤ r := by exact_mod_cast hlt
      show (LG.layer (h.ι₂ y.toNode) : ℝ) + 1 ≤ ((topLayered G₁ B h₁ r r'' hlt.le).layer x.toNode : ℝ)
      rw [e]
      linarith
    · intro x _
      have e : ((topLayered G₁ B h₁ r r'' hlt.le).layer x.toNode : ℝ) = r := by
        exact_mod_cast hlay₁ x
      rw [e]
  have hH₁ : ∀ ℓ ∈ inputLeaves G₁,
      Summable fun n : Fin d → ℤ => |H (topAddr ℓ.1) (k + latticePoint L n)| := by
    intro ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := h.inputLeaf_ofTop h₁.2.1 hmtop ℓ hℓ
    rw [← he]
    exact hH ℓ' hℓ'
  have hH₂ : ∀ ℓ ∈ inputLeaves G₂,
      Summable fun n : Fin d → ℤ => |H (botAddr B.lonePath ℓ.1) (k + latticePoint L n)| := by
    intro ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := h.inputLeaf_ofBot hmbot ℓ hℓ
    rw [← he]
    exact hH ℓ' hℓ'
  exact kernelLeavesW_glue L γ δ (LG₁ := topLayered G₁ B h₁ r r'' hlt.le)
    (LG₂ := botLayered_tree hG h₁ hs₁ h₂ hs₂) h (decSplit_tree hG h₁ hs₁ h₂ hs₂)
    (decGlue_tree hG h₁ hs₁ h₂ hs₂) (not_flower_of_decodesTree hG) (not_flower_of_decodesTree h₁)
    (not_flower_of_decodesTree h₂) h₁.2.1 hmtop hmbot H _ s _ r _ s hD k _ _ _ ((d5Mult_glue h) S ω F ann M Fu Mu)
    (summable_mult_leavesSummand L γ δ _ _ _ _ k _ Mb₁ hb₁ (card_lone_le_of_decodesTree h₁) hH₁)
    (summable_mult_leavesSummand L γ δ _ _ _ _ k _ Mb₂ hb₂ (card_lone_le_of_decodesTree h₂) hH₂)

end Tree

end WaveTurbulence.Flower.FiltCoh
