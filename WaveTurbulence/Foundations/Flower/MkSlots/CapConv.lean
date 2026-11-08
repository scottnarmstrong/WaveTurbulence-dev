/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PRedNode
public import WaveTurbulence.Foundations.Flower.ProtWhole.RegWeight

/-! # B3s MK-SLOTS (cap slots): the pinned native kernel is the protected kernel of a paired tree

1. `kernelNodeWF_eq_kernelProt`: the pinned weighted kernel `kernelNodeWF` (the UNPINNED domain `kDomain`
   integrated against `fixMeasure fix`) is D2a's protected kernel `kernelProt` (the frozen `kDomainFix` and the
   lone-port constraint, integrated over the free times) when every pinned value lies in its layer window and below
   the upper time of a FREE parent (`CapPins`): on the pinned slice the two domains agree (the constraint
   `τ_b < up b` of a pinned `b` follows from `τ_b < τ_parent < up parent ≤ up b`), for every upper time.
2. `kernelProt_capG_T1`: on a width-2 cap couple (D6b's `CapG`), `kernelProt` is the protected kernel of the paired
   tree `T1` (D2b's `objTree`), the cap pair's leaf factors moving into the multiplier (`capPairFactor`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
  WaveTurbulence.Flower.ProtWhole

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

theorem capExtendFix_eq (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) : G.extendFix fix τ = extendFixI fix τ := by
  funext b
  unfold Garden.extendFix extendFixI
  rfl

/-- Pins with a free parent: every pinned value is in its layer window, positive, and its branch has a free parent
whose upper time is at most its own; no parent–child pair is pinned; no lone leaves. -/
structure CapPins (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (fix : GBranch LG.garden.tree → Option ℝ) :
    Prop where
  val : ∀ b v, fix b = some v → (LG.layer b.toNode : ℝ) < v ∧ v < LG.layer b.toNode + 1 ∧ 0 < v
  par : ∀ b v, fix b = some v → ∃ b' : GBranch LG.garden.tree, b.IsChildOf b' ∧ fix b' = none ∧ up b' ≤ up b
  adj : ∀ b b' : GBranch LG.garden.tree, b'.IsChildOf b → fix b = none ∨ fix b' = none
  nolone : ∀ b, ¬ LG.garden.IsLoneParent b

theorem mem_kDomain_iff_protDom {LG : LayeredGarden w} {up : GBranch LG.garden.tree → ℝ}
    {fix : GBranch LG.garden.tree → Option ℝ} (hP : CapPins LG up fix) (τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ) :
    LG.garden.extendFix fix τ ∈ kDomain LG up 0 ↔ LG.garden.extendFix fix τ ∈ protDom LG up 0 fix := by
  set T := LG.garden.extendFix fix τ with hT
  have hTv : ∀ b v, fix b = some v → T b = v := fun b v hb => by
    rw [hT, capExtendFix_eq]; exact extendFixI_some fix τ hb
  constructor
  · intro h
    refine ⟨fun b => ⟨fun _ => ?_, fun b' hb' _ => (h b).2.2.2.2.1 b' hb'⟩, fun b hb => absurd hb (hP.nolone b)⟩
    obtain ⟨h1, h2, h3, h4, -, -⟩ := h b
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h, -⟩ b
    have hord : ∀ b', b'.IsChildOf b → T b' < T b := fun b' hb' => by
      refine (h b).2 b' hb' ?_
      rcases hP.adj b b' hb' with h0 | h0
      · exact Or.inr h0
      · exact Or.inl h0
    have hown : (LG.layer b.toNode : ℝ) < T b ∧ T b < LG.layer b.toNode + 1 ∧ 0 < T b ∧ T b < up b := by
      cases hfb : fix b with
      | none => exact (h b).1 hfb
      | some v =>
        obtain ⟨v1, v2, v3⟩ := hP.val b v hfb
        obtain ⟨b', hbb', hfb', hup⟩ := hP.par b v hfb
        have hlt : T b < T b' := (h b').2 b hbb' (Or.inr hfb')
        have hup' : T b' < up b' := ((h b').1 hfb').2.2.2
        rw [hTv b v hfb] at hlt ⊢
        exact ⟨v1, v2, v3, by linarith⟩
    exact ⟨hown.1, hown.2.1, hown.2.2.1, hown.2.2.2, hord, fun hb => absurd hb (hP.nolone b)⟩

/-- The leaf profiles of a node function (`0` off the nodes). -/
def capProfiles (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ) : LeafProfiles w d :=
  fun z => if h : z.2 ∈ (LG.garden.tree z.1).nodes then A ⟨z, h⟩ else 0

theorem capProfiles_leaf (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ) (ℓ : GLeaf LG.garden.tree) :
    capProfiles LG A ℓ.1 = A ℓ.toNode := by
  unfold capProfiles
  rw [dif_pos (show ℓ.1.2 ∈ (LG.garden.tree ℓ.1.1).nodes from ℓ.toNode.2)]
  rfl

/-- **The pinned native kernel is the protected kernel** (pins with a free parent, lower time `0`). -/
theorem kernelNodeWF_eq_kernelProt (L γ δ : ℝ) (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (fix : GBranch LG.garden.tree → Option ℝ)
    (hP : CapPins LG up fix) :
    kernelNodeWF L γ δ LG A m up 0 k₀ nroot nfl fix =
      kernelProt L γ δ LG (capProfiles LG A) m up 0 fix k₀ nroot nfl := by
  rw [kernelProt_eq_tsum]
  unfold kernelNodeWF
  congr 1
  refine tsum_congr fun κ => ?_
  unfold protSummand protTime
  congr 2
  · congr 1
    rw [integral_fixMeasure]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only [Set.indicator]
    rw [← capExtendFix_eq]
    by_cases h : LG.garden.extendFix fix τ ∈ kDomain LG up 0
    · rw [if_pos h, if_pos ((mem_kDomain_iff_protDom hP τ).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((mem_kDomain_iff_protDom hP τ).2 h'))]
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [capProfiles_leaf]

/-! ### The cap couple and its paired tree -/

namespace CapG

variable {LG : LayeredGarden 2} {j0 c : Fin 2} {X : RegChain} {ζ : ℤˣ}

/-- The cap pair of a cap couple. -/
abbrev IsCapPairLeaf (c : Fin 2) (ℓ : GLeaf LG.garden.tree) : Prop :=
  ℓ.1.1 ∈ ({c} : Finset (Fin 2)) ∨ (LG.garden.pair ℓ).1.1 ∈ ({c} : Finset (Fin 2))

/-- The leaf factors of the cap pair, read on the paired tree. -/
def capPairFactor (D : CapG LG j0 c X ζ) (H : LeafProfiles 2 d) (K : GNode D.T1.garden.tree → Mom d) : ℂ :=
  ∏ ℓ ∈ (inputLeaves LG.garden).filter (IsCapPairLeaf c), (H ℓ.1 (K (D.ρ ℓ.toNode)) : ℂ)

/-- The leaf profiles of the paired tree. -/
def capH1 (j0 : Fin 2) (H : LeafProfiles 2 d) : LeafProfiles 1 d := fun z => H (j0, z.2)

/-- **A cap couple's protected kernel is that of its paired tree.** -/
theorem kernelProt_capG_T1 (D : CapG LG j0 c X ζ) (L γ δ : ℝ) (H : LeafProfiles 2 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) :
    kernelProt L γ δ LG H m up 0 fix k₀ (fun _ => 0) 0 =
      kernelProt L γ δ D.T1 (capH1 j0 H) (fun K => m (fun a => K (D.ρ a)) * capPairFactor D H K)
        (fun b => up (D.βc b)) 0 (fun b => fix (D.βc b)) k₀ (fun _ => 0) 0 := by
  rw [kernelProt_eq_tsum, kernelProt_eq_tsum, D.order_eq, D.zeta_eq]
  congr 1
  rw [← (D.decEquiv d).tsum_eq]
  refine tsum_congr fun κ => ?_
  have he : D.decEquiv d κ = D.decFwd κ := rfl
  rw [he]
  unfold protSummand
  rw [D.protTime_capG L γ δ up 0 fix, D.epsDec_eq κ, D.coset_ρ L k₀ κ]
  have hι : (fun a => cosetDecoration D.T1.garden L k₀ (D.decFwd κ).1 (D.ρ (D.ι a))) =
      cosetDecoration D.T1.garden L k₀ (D.decFwd κ).1 := by
    funext a; rw [D.ρ_ι]
  rw [hι]
  rw [← Finset.prod_filter_not_mul_prod_filter (inputLeaves LG.garden) (IsCapPairLeaf c)]
  have hsplit : (inputLeaves LG.garden).filter (fun ℓ => ¬ IsCapPairLeaf c ℓ) =
      (inputLeaves D.T1.garden).map ⟨D.ιL, D.ιL_injective⟩ := by
    convert D.inputLeaves_filter using 1
  rw [hsplit, Finset.prod_map]
  have hT : ∀ ℓ : GLeaf D.T1.garden.tree,
      (H (D.ιL ℓ).1 (cosetDecoration D.T1.garden L k₀ (D.decFwd κ).1 (D.ρ (D.ιL ℓ).toNode)) : ℂ) =
        (capH1 j0 H ℓ.1 (cosetDecoration D.T1.garden L k₀ (D.decFwd κ).1 ℓ.toNode) : ℂ) := fun ℓ => by
    rw [D.ιL_toNode, D.ρ_ι]
    rfl
  simp only [Function.Embedding.coeFn_mk, hT]
  unfold capPairFactor
  ring

end CapG

end WaveTurbulence.Flower.MkSlots
