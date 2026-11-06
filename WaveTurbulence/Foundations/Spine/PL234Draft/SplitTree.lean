/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SplitCouple

/-!
# Splitting off the top block of a coherent regular tree (TARGET (prooflayer1-2), one step)

For a paired-tree carrier decoded by `appendChain B D` with `D` nonempty, whose top block `B` lies in
layer `r` and whose lone position of `B` is in a lower layer `r'' < r`, the leafwise kernel splits
(`treeLeaves_split`): `K*_𝒯(t, s, k) = K*_{𝒯₁}(t, r, k) · K*_{𝒯₂}(r'' + 1, s, k)` for `t ≥ r'' + 1`.
The lone leaf, and hence the lower time `s`, belong to the bottom tree.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

variable {LG : LayeredGarden 1} {B D : RegChain}

theorem lonePath_ne_nil_of_ne_nil {X : RegChain} (hX : X ≠ .nil) : X.lonePath ≠ [] := by
  cases X with
  | nil => exact absurd rfl hX
  | pair m _ _ inner rest => simp [RegChain.lonePath]

/-- **Splitting off the top block of a regular tree.** -/
theorem treeLeaves_split (L γ δ : ℝ) {d : ℕ}
    (hG : (appendChain B D).DecodesTree LG.garden) (hDne : D ≠ .nil)
    {G₁ : Garden 1} (h₁ : B.DecodesTree G₁) (hs₁ : G₁.sig 0 = LG.garden.sig 0)
    {G₂ : Garden 1} (h₂ : D.DecodesTree G₂) (hs₂ : G₂.sig 0 = LG.garden.sig 0) {r : ℕ}
    (hB : ∀ z ∈ chainNodesSet B (LG.garden.sig 0) ((0 : Fin 1), ([] : Path)), layerAt LG z = r)
    (hlt : layerAt LG ((0 : Fin 1), B.lonePath) < r)
    (H : LeafProfiles 1 d) (k : Mom d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|)
    (t s : ℝ) (ht : (layerAt LG ((0 : Fin 1), B.lonePath) : ℝ) + 1 ≤ t) :
    treeLeaves L γ δ LG H t s k =
      treeLeaves L γ δ (topLayered G₁ B h₁ r (layerAt LG ((0 : Fin 1), B.lonePath)) hlt.le)
          (fun z => H (topAddr z)) t r k *
        treeLeaves L γ δ (botLayered_tree hG h₁ hs₁ h₂ hs₂) (fun z => H (botAddr B.lonePath z))
          ((layerAt LG ((0 : Fin 1), B.lonePath) : ℝ) + 1) s k := by
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
  unfold treeLeaves
  exact kernelLeaves_glue L γ δ (LG₁ := topLayered G₁ B h₁ r r'' hlt.le)
    (LG₂ := botLayered_tree hG h₁ hs₁ h₂ hs₂) h (decSplit_tree hG h₁ hs₁ h₂ hs₂)
    (decGlue_tree hG h₁ hs₁ h₂ hs₂) (not_flower_of_decodesTree hG) (not_flower_of_decodesTree h₁)
    (not_flower_of_decodesTree h₂) h₁.2.1 hmtop hmbot H _ s _ r _ s hD k
    (summable_norm_leavesSummand L γ δ _ _ _ _ k _ _ (card_lone_le_of_decodesTree h₁) hH₁)
    (summable_norm_leavesSummand L γ δ _ _ _ _ k _ _ (card_lone_le_of_decodesTree h₂) hH₂)

end WaveTurbulence.PL234
