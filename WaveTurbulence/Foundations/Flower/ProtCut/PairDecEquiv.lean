/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.PairDec

/-! # D2c PROT-CUT: the decoration bijection of a closing pair

`PairData.decEquiv`: decorations of a closing pair with root value `0` ≃ exceptional data `PairE` × decorations
with root values `0` of the interior, the red and the green couple. The forward map reads `x`, `yr`, `yg` at the
interior root and at the two couple roots and shifts each piece by its root value; the backward map is the
region-wise glue `pairGlue`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The address map of the interior piece. -/
def pφi (m : MiniTreeCode) (x : Fin 1 × Path) : Fin 1 × Path := ((0 : Fin 1), m.c :: x.2)

/-- The address map of the red couple. -/
def pφr (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (x : Fin 2 × Path) : Fin 1 × Path :=
  ((0 : Fin 1), rBase m inner ζ x.1 ++ x.2)

/-- The address map of the green couple. -/
def pφg (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (x : Fin 2 × Path) : Fin 1 × Path :=
  ((0 : Fin 1), gBase m inner ζ x.1 ++ x.2)

theorem pφi_hom (m : MiniTreeCode) : ∀ x q, pφi m (addrExt x q) = addrExt (pφi m x) q := by
  intro x q; simp [pφi, addrExt]

theorem pφr_hom (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) :
    ∀ x q, pφr m inner ζ (addrExt x q) = addrExt (pφr m inner ζ x) q := by
  intro x q; simp [pφr, addrExt]

theorem pφg_hom (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) :
    ∀ x q, pφg m inner ζ (addrExt x q) = addrExt (pφg m inner ζ x) q := by
  intro x q; simp [pφg, addrExt]

namespace PairData

variable {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} {G Gi : Garden 1} {Gr Gg : Garden 2}
variable (h : PairData m Qr Qg inner G Gi Gr Gg)
include h

theorem ιi_val (z : GNode Gi.tree) : (h.ιi z).1 = pφi m z.1 := rfl
theorem ιr_val (z : GNode Gr.tree) : (h.ιr z).1 = pφr m inner (G.sig 0) z.1 := rfl
theorem ιg_val (z : GNode Gg.tree) : (h.ιg z).1 = pφg m inner (G.sig 0) z.1 := rfl

omit h in
theorem extend_val {w : ℕ} {T : Fin w → TTree} {V : Type*} [AddCommGroup V] (F : Fin w × Path → V)
    (a : Fin w × Path) (ha : a.2 ∈ (T a.1).nodes) : extend (fun z : GNode T => F z.1) a = F a := by
  unfold extend; rw [dif_pos ha]

theorem node_iff (p : Path) : p ∈ (G.tree 0).nodes ↔ p ∈ (pairTree m Qr Qg inner (G.sig 0)).nodes := by
  rw [h.tree0]

section Forward

variable {V : Type*} [AddCommGroup V] {κ : GNode G.tree → V} (hκ : IsDecoration G κ)
include hκ

theorem chainDec_G :
    ChainDec (extend κ) (RegChain.pair m Qr Qg inner .nil) (G.sig 0) ((0 : Fin 1), []) :=
  chainDec_of_decoration h.decZ hκ

theorem chainDec_inner : ChainDec (extend κ) inner (slotSign (G.sig 0) m.c) ((0 : Fin 1), [m.c]) := by
  have := (h.chainDec_G hκ).2.2.2.2.1
  simpa [addrExt] using this

theorem cplDec_red : CplDec (extend κ) Qr (0, rBase m inner (G.sig 0) 0) (0, rBase m inner (G.sig 0) 1) :=
  (oriented_rBase m inner (G.sig 0) _ Qr).mp (h.chainDec_G hκ).2.2.1

theorem cplDec_green :
    CplDec (extend κ) Qg (0, gBase m inner (G.sig 0) 0) (0, gBase m inner (G.sig 0) 1) :=
  (oriented_gBase m inner (G.sig 0) _ Qg).mp (h.chainDec_G hκ).2.2.2.1

theorem extend_bPath : extend κ ((0 : Fin 1), bPath m inner) = extend κ ((0 : Fin 1), [m.c]) := by
  have := chainDec_lone_eq _ inner _ _ (h.chainDec_inner hκ)
  rw [this]; simp [addrExt, bPath]

theorem extend_lonePos : extend κ ((0 : Fin 1), lonePos m inner) = extend κ ((0 : Fin 1), []) := by
  have := chainDec_lone_eq _ _ _ _ (h.chainDec_G hκ)
  rw [this]; simp [addrExt, lonePos, bPath, RegChain.lonePath]

theorem extend_rBase (j : Fin 2) :
    extend κ ((0 : Fin 1), rBase m inner (G.sig 0) j) = extend κ ((0 : Fin 1), rBase m inner (G.sig 0) 0) := by
  fin_cases j
  · rfl
  · exact (cplDec_root_eq _ _ _ _ (h.cplDec_red hκ)).symm

theorem extend_gBase (j : Fin 2) :
    extend κ ((0 : Fin 1), gBase m inner (G.sig 0) j) = extend κ ((0 : Fin 1), gBase m inner (G.sig 0) 0) := by
  fin_cases j
  · rfl
  · exact (cplDec_root_eq _ _ _ _ (h.cplDec_green hκ)).symm

/-- The values at the children of `𝔫_a`. -/
theorem extend_slot (i : Fin 3) :
    extend κ ((0 : Fin 1), [i]) = pairA m (extend κ ((0 : Fin 1), [m.c]))
      (extend κ ((0 : Fin 1), rBase m inner (G.sig 0) 0)) (extend κ ((0 : Fin 1), gBase m inner (G.sig 0) 0)) i := by
  unfold pairA
  rcases slot_cases m i with rfl | rfl | rfl
  · simp
  · obtain ⟨j, hj⟩ := exists_rBase_top m inner (G.sig 0)
    rw [if_neg (red_ne_c m), if_pos rfl, ← h.extend_rBase hκ j, hj]
  · obtain ⟨j, hj⟩ := exists_gBase_top m inner (G.sig 0)
    rw [if_neg (green_ne_c m), if_neg (fun e => red_ne_green m e.symm), ← h.extend_gBase hκ j, hj]

/-- The values at the children of `𝔫_b`. -/
theorem extend_bslot (h0 : extend κ ((0 : Fin 1), []) = 0) (k : Fin 3) :
    extend κ ((0 : Fin 1), bPath m inner ++ [k]) = pairB m
      (extend κ ((0 : Fin 1), rBase m inner (G.sig 0) 0)) (extend κ ((0 : Fin 1), gBase m inner (G.sig 0) 0)) k := by
  unfold pairB
  rcases slot2_cases m k with rfl | rfl | rfl
  · rw [if_pos rfl, ← h0, ← h.extend_lonePos hκ]; rfl
  · obtain ⟨j, hj⟩ := exists_rBase_bot m inner (G.sig 0)
    rw [if_neg (red2_ne_lone m), if_pos rfl, ← h.extend_rBase hκ j, hj]
  · obtain ⟨j, hj⟩ := exists_gBase_bot m inner (G.sig 0)
    rw [if_neg (green2_ne_lone m), if_neg (fun e => red2_ne_green2 m e.symm), ← h.extend_gBase hκ j, hj]

theorem pairRel_of (h0 : extend κ ((0 : Fin 1), []) = 0) :
    PairRel m (extend κ ((0 : Fin 1), [m.c])) (extend κ ((0 : Fin 1), rBase m inner (G.sig 0) 0))
      (extend κ ((0 : Fin 1), gBase m inner (G.sig 0) 0)) := by
  obtain ⟨ha, hb, -⟩ := h.chainDec_G hκ
  constructor
  · unfold NodeRel at ha
    simp only [addrExt, List.nil_append] at ha
    rw [h.extend_slot hκ 0, h.extend_slot hκ 1, h.extend_slot hκ 2, h0] at ha
    exact ha
  · unfold NodeRel at hb
    simp only [addrExt, List.nil_append] at hb
    have e : [m.c] ++ inner.lonePath = bPath m inner := rfl
    rw [e, h.extend_bslot hκ h0 0, h.extend_bslot hκ h0 1, h.extend_bslot hκ h0 2,
      h.extend_bPath hκ] at hb
    exact hb

theorem isDec_I : IsDecoration Gi (fun z => κ (h.ιi z) - extend κ ((0 : Fin 1), [m.c])) := by
  have h1 : ChainDec (extend κ ∘ pφi m) inner (slotSign (G.sig 0) m.c) ((0 : Fin 1), []) :=
    (chainDec_comp (pφi_hom m) (extend κ) inner _ _).mpr (by simpa [pφi] using h.chainDec_inner hκ)
  have h2 := (chainDec_add_const (extend κ ∘ pφi m) (-extend κ ((0 : Fin 1), [m.c])) inner _ _).mpr h1
  rw [← h.sigI] at h2
  have h3 := PL234.isDecoration_of_chainDec h.decI h2
  convert h3 using 1
  funext z
  simp only [Function.comp_apply, sub_eq_add_neg]
  rw [← h.ιi_val, extend_node]

theorem isDec_R : IsDecoration Gr (fun z => κ (h.ιr z) - extend κ ((0 : Fin 1), rBase m inner (G.sig 0) 0)) := by
  have h1 : CplDec (extend κ ∘ pφr m inner (G.sig 0)) Qr (0, []) (1, []) :=
    (cplDec_comp (pφr_hom m inner (G.sig 0)) (extend κ) Qr _ _).mpr (by simpa [pφr] using h.cplDec_red hκ)
  have h2 := (cplDec_add_const (extend κ ∘ pφr m inner (G.sig 0)) (-extend κ ((0 : Fin 1), rBase m inner (G.sig 0) 0)) Qr _ _).mpr h1
  have h3 := isDecoration_of_cplDec h.decR h2
  convert h3 using 1
  funext z
  simp only [Function.comp_apply, sub_eq_add_neg]
  rw [← h.ιr_val, extend_node]

theorem isDec_G' : IsDecoration Gg (fun z => κ (h.ιg z) - extend κ ((0 : Fin 1), gBase m inner (G.sig 0) 0)) := by
  have h1 : CplDec (extend κ ∘ pφg m inner (G.sig 0)) Qg (0, []) (1, []) :=
    (cplDec_comp (pφg_hom m inner (G.sig 0)) (extend κ) Qg _ _).mpr (by simpa [pφg] using h.cplDec_green hκ)
  have h2 := (cplDec_add_const (extend κ ∘ pφg m inner (G.sig 0)) (-extend κ ((0 : Fin 1), gBase m inner (G.sig 0) 0)) Qg _ _).mpr h1
  have h3 := isDecoration_of_cplDec h.decG h2
  convert h3 using 1
  funext z
  simp only [Function.comp_apply, sub_eq_add_neg]
  rw [← h.ιg_val, extend_node]

end Forward

section Backward

variable {V : Type*} [AddCommGroup V] (x yr yg : V) {κi : GNode Gi.tree → V} {κr : GNode Gr.tree → V}
  {κg : GNode Gg.tree → V}

theorem gF_slot (hi0 : κi (GNode.root Gi.tree 0) = 0) (hr0 : ∀ j, κr (GNode.root Gr.tree j) = 0)
    (hg0 : ∀ j, κg (GNode.root Gg.tree j) = 0) (i : Fin 3) :
    pairGlue m inner (G.sig 0) x yr yg (extend κi) (extend κr) (extend κg) ((0 : Fin 1), [i]) =
      pairA m x yr yg i := by
  unfold pairA
  rcases slot_cases m i with rfl | rfl | rfl
  · rw [if_pos rfl]
    by_cases hl : inner.lonePath = []
    · have e : [m.c] = bPath m inner := by rw [bPath_eq, hl]
      rw [e, pairGlue_bPath]
    · have hq : ¬ inner.lonePath <+: ([] : Path) := fun hp => hl (List.prefix_nil.mp hp)
      rw [pairGlue_inner m inner _ _ _ _ _ _ _ [] hq]
      rw [show ((0 : Fin 1), ([] : Path)) = (GNode.root Gi.tree 0).1 from rfl, extend_node, hi0, zero_add]
  · obtain ⟨j, hj⟩ := exists_rBase_top m inner (G.sig 0)
    rw [if_neg (red_ne_c m), if_pos rfl, show [m.red.1] = rBase m inner (G.sig 0) j ++ [] by rw [hj, List.append_nil],
      pairGlue_rBase, show (j, ([] : Path)) = (GNode.root Gr.tree j).1 from rfl, extend_node, hr0, zero_add]
  · obtain ⟨j, hj⟩ := exists_gBase_top m inner (G.sig 0)
    rw [if_neg (green_ne_c m), if_neg (fun e => red_ne_green m e.symm),
      show [m.green.1] = gBase m inner (G.sig 0) j ++ [] by rw [hj, List.append_nil],
      pairGlue_gBase, show (j, ([] : Path)) = (GNode.root Gg.tree j).1 from rfl, extend_node, hg0, zero_add]

theorem gF_bslot (hr0 : ∀ j, κr (GNode.root Gr.tree j) = 0)
    (hg0 : ∀ j, κg (GNode.root Gg.tree j) = 0) (k : Fin 3) :
    pairGlue m inner (G.sig 0) x yr yg (extend κi) (extend κr) (extend κg) ((0 : Fin 1), bPath m inner ++ [k]) =
      pairB m yr yg k := by
  unfold pairB
  rcases slot2_cases m k with rfl | rfl | rfl
  · rw [if_pos rfl]; exact pairGlue_lonePos m inner _ _ _ _ _ _ _
  · obtain ⟨j, hj⟩ := exists_rBase_bot m inner (G.sig 0)
    rw [if_neg (red2_ne_lone m), if_pos rfl, show bPath m inner ++ [m.red.2] = rBase m inner (G.sig 0) j ++ [] by
      rw [hj, List.append_nil], pairGlue_rBase, show (j, ([] : Path)) = (GNode.root Gr.tree j).1 from rfl, extend_node, hr0,
      zero_add]
  · obtain ⟨j, hj⟩ := exists_gBase_bot m inner (G.sig 0)
    rw [if_neg (green2_ne_lone m), if_neg (fun e => red2_ne_green2 m e.symm),
      show bPath m inner ++ [m.green.2] = gBase m inner (G.sig 0) j ++ [] by rw [hj, List.append_nil], pairGlue_gBase,
      show (j, ([] : Path)) = (GNode.root Gg.tree j).1 from rfl, extend_node, hg0, zero_add]

theorem extend_lone_I (hκi : IsDecoration Gi κi) (hi0 : κi (GNode.root Gi.tree 0) = 0) :
    extend κi ((0 : Fin 1), inner.lonePath) = 0 := by
  have := chainDec_lone_eq _ _ _ _ (chainDec_of_decoration h.decI hκi)
  simp only [addrExt, List.nil_append] at this
  rw [← this, show ((0 : Fin 1), ([] : Path)) = (GNode.root Gi.tree 0).1 from rfl, extend_node, hi0]

/-- **The glued decoration.** -/
theorem glue_isDec (hrel : PairRel m x yr yg) (hκi : IsDecoration Gi κi) (hκr : IsDecoration Gr κr)
    (hκg : IsDecoration Gg κg) (hi0 : κi (GNode.root Gi.tree 0) = 0)
    (hr0 : ∀ j, κr (GNode.root Gr.tree j) = 0) (hg0 : ∀ j, κg (GNode.root Gg.tree j) = 0) :
    IsDecoration G (fun z => pairGlue m inner (G.sig 0) x yr yg (extend κi) (extend κr) (extend κg) z.1) := by
  set F := pairGlue m inner (G.sig 0) x yr yg (extend κi) (extend κr) (extend κg) with hF
  refine PL234.isDecoration_of_chainDec h.decZ ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
  · unfold NodeRel
    simp only [addrExt, List.nil_append]
    rw [hF, pairGlue_nil, h.gF_slot x yr yg hi0 hr0 hg0, h.gF_slot x yr yg hi0 hr0 hg0,
      h.gF_slot x yr yg hi0 hr0 hg0]
    exact hrel.1
  · unfold NodeRel
    simp only [addrExt, List.nil_append]
    have e : [m.c] ++ inner.lonePath = bPath m inner := rfl
    rw [e, hF, pairGlue_bPath, h.gF_bslot x yr yg hr0 hg0, h.gF_bslot x yr yg hr0 hg0,
      h.gF_bslot x yr yg hr0 hg0]
    exact hrel.2
  · refine (oriented_rBase m inner (G.sig 0) F Qr).mpr ?_
    have h1 := (cplDec_add_const (extend κr) yr Qr (0, []) (1, [])).mpr (cplDec_of_decoration h.decR hκr)
    have h2 : CplDec (F ∘ pφr m inner (G.sig 0)) Qr (0, []) (1, []) := by
      convert h1 using 1
      funext z
      simp only [Function.comp_apply, pφr, hF, pairGlue_rBase]
    have h3 := (cplDec_comp (pφr_hom m inner (G.sig 0)) F Qr (0, []) (1, [])).mp h2
    simpa [pφr] using h3
  · refine (oriented_gBase m inner (G.sig 0) F Qg).mpr ?_
    have h1 := (cplDec_add_const (extend κg) yg Qg (0, []) (1, [])).mpr (cplDec_of_decoration h.decG hκg)
    have h2 : CplDec (F ∘ pφg m inner (G.sig 0)) Qg (0, []) (1, []) := by
      convert h1 using 1
      funext z
      simp only [Function.comp_apply, pφg, hF, pairGlue_gBase]
    have h3 := (cplDec_comp (pφg_hom m inner (G.sig 0)) F Qg (0, []) (1, [])).mp h2
    simpa [pφg] using h3
  · have h1 := (chainDec_add_const (extend κi) x inner _ ((0 : Fin 1), [])).mpr
      (chainDec_of_decoration h.decI hκi)
    rw [h.sigI] at h1
    have h2 : ChainDec (F ∘ pφi m) inner (slotSign (G.sig 0) m.c) ((0 : Fin 1), []) := by
      refine (chainDec_congr inner _ _ fun q hq => ?_).mpr h1
      simp only [Function.comp_apply, pφi, addrExt, List.nil_append]
      by_cases hp : inner.lonePath <+: q
      · have := plug_leaf_prefix inner _ hq hp
        subst this
        rw [hF, show m.c :: inner.lonePath = bPath m inner from rfl, pairGlue_bPath,
          h.extend_lone_I hκi hi0, zero_add]
      · rw [hF, pairGlue_inner m inner _ _ _ _ _ _ _ q hp]
    have h3 := (chainDec_comp (pφi_hom m) F inner _ ((0 : Fin 1), [])).mp h2
    simpa [pφi, addrExt] using h3

end Backward

/-! ### The bijection -/

variable (d : ℕ)

omit h in
theorem genDec_root {w : ℕ} {G' : Garden w} (κ : GenDecoration G' d (fun _ => 0) 0) (j : Fin w) :
    κ.1 (GNode.root G'.tree j) = 0 := κ.2.2.1 j

/-- **Decorations of a closing pair ≃ exceptional data × decorations of the pieces.** -/
def decEquiv : GenDecoration G d (fun _ => 0) 0 ≃
    PairE m d × (GenDecoration Gi d (fun _ => 0) 0 ×
      (GenDecoration Gr d (fun _ => 0) 0 × GenDecoration Gg d (fun _ => 0) 0)) where
  toFun κ :=
    have h0 : extend κ.1 ((0 : Fin 1), []) = 0 := by
      rw [show ((0 : Fin 1), ([] : Path)) = (GNode.root G.tree 0).1 from rfl, extend_node]; exact κ.2.2.1 0
    (⟨(extend κ.1 ((0 : Fin 1), [m.c]), extend κ.1 ((0 : Fin 1), rBase m inner (G.sig 0) 0),
        extend κ.1 ((0 : Fin 1), gBase m inner (G.sig 0) 0)), h.pairRel_of κ.2.1 h0⟩,
      ⟨fun z => κ.1 (h.ιi z) - extend κ.1 ((0 : Fin 1), [m.c]), h.isDec_I κ.2.1, fun j => by
          show κ.1 (h.ιi (GNode.root Gi.tree j)) - extend κ.1 ((0 : Fin 1), [m.c]) = 0
          rw [Subsingleton.elim j 0, ← extend_node κ.1 (h.ιi _)]; exact sub_self _,
        fun ℓ hℓ => absurd hℓ (not_flower_of_decodesTree h.decI ℓ)⟩,
      ⟨fun z => κ.1 (h.ιr z) - extend κ.1 ((0 : Fin 1), rBase m inner (G.sig 0) 0), h.isDec_R κ.2.1, fun j => by
          show κ.1 (h.ιr (GNode.root Gr.tree j)) - extend κ.1 ((0 : Fin 1), rBase m inner (G.sig 0) 0) = 0
          rw [← extend_node κ.1 (h.ιr _)]
          show extend κ.1 ((0 : Fin 1), rBase m inner (G.sig 0) j ++ []) - _ = 0
          rw [List.append_nil, h.extend_rBase κ.2.1 j]; exact sub_self _,
        fun ℓ hℓ => absurd hℓ (not_flower_of_plain h.decR.1.1 ℓ)⟩,
      ⟨fun z => κ.1 (h.ιg z) - extend κ.1 ((0 : Fin 1), gBase m inner (G.sig 0) 0), h.isDec_G' κ.2.1, fun j => by
          show κ.1 (h.ιg (GNode.root Gg.tree j)) - extend κ.1 ((0 : Fin 1), gBase m inner (G.sig 0) 0) = 0
          rw [← extend_node κ.1 (h.ιg _)]
          show extend κ.1 ((0 : Fin 1), gBase m inner (G.sig 0) j ++ []) - _ = 0
          rw [List.append_nil, h.extend_gBase κ.2.1 j]; exact sub_self _,
        fun ℓ hℓ => absurd hℓ (not_flower_of_plain h.decG.1.1 ℓ)⟩)
  invFun p :=
    ⟨fun z => pairGlue m inner (G.sig 0) p.1.1.1 p.1.1.2.1 p.1.1.2.2 (extend p.2.1.1) (extend p.2.2.1.1)
        (extend p.2.2.2.1) z.1,
      h.glue_isDec _ _ _ p.1.2 p.2.1.2.1 p.2.2.1.2.1 p.2.2.2.2.1 (genDec_root d p.2.1 0)
        (genDec_root d p.2.2.1) (genDec_root d p.2.2.2),
      fun j => by rw [Subsingleton.elim j 0]; exact pairGlue_nil m inner _ _ _ _ _ _ _,
      fun ℓ hℓ => absurd hℓ (not_flower_of_decodesTree h.decZ ℓ)⟩
  left_inv κ := by
    have h0 : extend κ.1 ((0 : Fin 1), []) = 0 := by
      rw [show ((0 : Fin 1), ([] : Path)) = (GNode.root G.tree 0).1 from rfl, extend_node]; exact κ.2.2.1 0
    apply Subtype.ext
    funext z
    obtain ⟨⟨j0, p⟩, hz⟩ := z
    have hj0 : j0 = 0 := Subsingleton.elim _ _
    subst hj0
    have hz' : p ∈ (pairTree m Qr Qg inner (G.sig 0)).nodes := (h.node_iff p).mp hz
    have hκz : κ.1 ⟨((0 : Fin 1), p), hz⟩ = extend κ.1 ((0 : Fin 1), p) := (extend_node κ.1 ⟨_, hz⟩).symm
    simp only
    rw [hκz]
    rcases pairTree_cases m inner (G.sig 0) Qr Qg p hz' with
      rfl | rfl | rfl | ⟨q, rfl, hq, hqn⟩ | ⟨j, q, rfl, hqn⟩ | ⟨j, q, rfl, hqn⟩
    · rw [pairGlue_nil, h0]
    · rw [pairGlue_bPath, h.extend_bPath κ.2.1]
    · rw [pairGlue_lonePos, h.extend_lonePos κ.2.1, h0]
    · have hn : q ∈ (Gi.tree ((0 : Fin 1), q).1).nodes := by rw [h.treeI]; exact hqn
      have e1 : extend (fun z : GNode Gi.tree => κ.1 (h.ιi z) - extend κ.1 ((0 : Fin 1), [m.c]))
          ((0 : Fin 1), q) = κ.1 (h.ιi ⟨((0 : Fin 1), q), hn⟩) - extend κ.1 ((0 : Fin 1), [m.c]) :=
        extend_node _ ⟨_, hn⟩
      have e2 : κ.1 (h.ιi ⟨((0 : Fin 1), q), hn⟩) = extend κ.1 ((0 : Fin 1), m.c :: q) :=
        (extend_node κ.1 _).symm
      rw [pairGlue_inner m inner _ _ _ _ _ _ _ q hq, e1, e2, sub_add_cancel]
    · have hn : q ∈ (Gr.tree (j, q).1).nodes := by rw [h.treeR]; exact hqn
      have e1 : extend (fun z : GNode Gr.tree => κ.1 (h.ιr z) -
          extend κ.1 ((0 : Fin 1), rBase m inner (G.sig 0) 0)) (j, q) =
          κ.1 (h.ιr ⟨(j, q), hn⟩) - extend κ.1 ((0 : Fin 1), rBase m inner (G.sig 0) 0) :=
        extend_node _ ⟨_, hn⟩
      have e2 : κ.1 (h.ιr ⟨(j, q), hn⟩) = extend κ.1 ((0 : Fin 1), rBase m inner (G.sig 0) j ++ q) :=
        (extend_node κ.1 _).symm
      rw [pairGlue_rBase, e1, e2, sub_add_cancel]
    · have hn : q ∈ (Gg.tree (j, q).1).nodes := by rw [h.treeG]; exact hqn
      have e1 : extend (fun z : GNode Gg.tree => κ.1 (h.ιg z) -
          extend κ.1 ((0 : Fin 1), gBase m inner (G.sig 0) 0)) (j, q) =
          κ.1 (h.ιg ⟨(j, q), hn⟩) - extend κ.1 ((0 : Fin 1), gBase m inner (G.sig 0) 0) :=
        extend_node _ ⟨_, hn⟩
      have e2 : κ.1 (h.ιg ⟨(j, q), hn⟩) = extend κ.1 ((0 : Fin 1), gBase m inner (G.sig 0) j ++ q) :=
        (extend_node κ.1 _).symm
      rw [pairGlue_gBase, e1, e2, sub_add_cancel]
  right_inv p := by
    obtain ⟨⟨⟨x, yr, yg⟩, he⟩, κi, κr, κg⟩ := p
    have hi0 := genDec_root d κi 0
    have hr0 := genDec_root d κr
    have hg0 := genDec_root d κg
    set F := pairGlue m inner (G.sig 0) x yr yg (extend κi.1) (extend κr.1) (extend κg.1) with hF
    have hc : extend (fun z : GNode G.tree => F z.1) ((0 : Fin 1), [m.c]) = x := by
      rw [extend_val F ((0 : Fin 1), [m.c]) (h.ιi (GNode.root Gi.tree 0)).2]
      exact h.gF_slot x yr yg hi0 hr0 hg0 m.c |>.trans (by simp [pairA])
    have hyr : extend (fun z : GNode G.tree => F z.1) ((0 : Fin 1), rBase m inner (G.sig 0) 0) = yr := by
      have hn := (h.ιr (GNode.root Gr.tree 0)).2
      rw [show ((0 : Fin 1), rBase m inner (G.sig 0) 0) = (h.ιr (GNode.root Gr.tree 0)).1 by
        simp [ιr, GNode.root], extend_val F _ hn]
      show F ((0 : Fin 1), rBase m inner (G.sig 0) 0 ++ []) = yr
      rw [hF, pairGlue_rBase, show ((0 : Fin 2), ([] : Path)) = (GNode.root Gr.tree 0).1 from rfl, extend_node,
        hr0, zero_add]
    have hyg : extend (fun z : GNode G.tree => F z.1) ((0 : Fin 1), gBase m inner (G.sig 0) 0) = yg := by
      have hn := (h.ιg (GNode.root Gg.tree 0)).2
      rw [show ((0 : Fin 1), gBase m inner (G.sig 0) 0) = (h.ιg (GNode.root Gg.tree 0)).1 by
        simp [ιg, GNode.root], extend_val F _ hn]
      show F ((0 : Fin 1), gBase m inner (G.sig 0) 0 ++ []) = yg
      rw [hF, pairGlue_gBase, show ((0 : Fin 2), ([] : Path)) = (GNode.root Gg.tree 0).1 from rfl, extend_node,
        hg0, zero_add]
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)))
    · show (extend (fun z : GNode G.tree => F z.1) ((0 : Fin 1), [m.c]),
        extend (fun z : GNode G.tree => F z.1) ((0 : Fin 1), rBase m inner (G.sig 0) 0),
        extend (fun z : GNode G.tree => F z.1) ((0 : Fin 1), gBase m inner (G.sig 0) 0)) = (x, yr, yg)
      rw [hc, hyr, hyg]
    · funext z
      show F (h.ιi z).1 - extend (fun z : GNode G.tree => F z.1) ((0 : Fin 1), [m.c]) = κi.1 z
      rw [hc]
      obtain ⟨⟨j0, q⟩, hz⟩ := z
      have hj0 : j0 = 0 := Subsingleton.elim _ _
      subst hj0
      show F ((0 : Fin 1), m.c :: q) - x = _
      have hz' : q ∈ (inner.plug (slotSign (G.sig 0) m.c) .leaf).nodes := by rw [← h.treeI]; exact hz
      by_cases hp : inner.lonePath <+: q
      · have := plug_leaf_prefix inner _ hz' hp
        subst this
        rw [hF, show m.c :: inner.lonePath = bPath m inner from rfl, pairGlue_bPath, sub_self,
          ← extend_node κi.1 ⟨_, hz⟩, h.extend_lone_I κi.2.1 hi0]
      · rw [hF, pairGlue_inner m inner _ _ _ _ _ _ _ q hp, add_sub_cancel_right, ← extend_node κi.1 ⟨_, hz⟩]
    · funext z
      show F (h.ιr z).1 - extend (fun z : GNode G.tree => F z.1) ((0 : Fin 1), rBase m inner (G.sig 0) 0) = κr.1 z
      rw [hyr]
      show F ((0 : Fin 1), rBase m inner (G.sig 0) z.1.1 ++ z.1.2) - yr = _
      rw [hF, pairGlue_rBase, add_sub_cancel_right, ← extend_node κr.1 z]
    · funext z
      show F (h.ιg z).1 - extend (fun z : GNode G.tree => F z.1) ((0 : Fin 1), gBase m inner (G.sig 0) 0) = κg.1 z
      rw [hyg]
      show F ((0 : Fin 1), gBase m inner (G.sig 0) z.1.1 ++ z.1.2) - yg = _
      rw [hF, pairGlue_gBase, add_sub_cancel_right, ← extend_node κg.1 z]

end PairData

end WaveTurbulence.Flower.ProtCut
