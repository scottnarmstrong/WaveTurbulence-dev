/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.PairDecEquiv

/-! # D2c PROT-CUT: the input leaves of a closing pair

`PairData.prod_inputLeaves_pair`: the input leaves (sign `+`, unmarked) of a closing pair are those of the
interior, of the red couple and of the green couple, placed by `pφi`, `pφr`, `pφg`; the lone leaf is marked. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem mem_inputLeaves {w : ℕ} {G : Garden w} (ℓ : GLeaf G.tree) :
    ℓ ∈ inputLeaves G ↔ G.sign ℓ.toNode = 1 ∧ G.mark ℓ = none := by
  simp [inputLeaves]

theorem cpair_lonePath' (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) :
    (RegChain.pair m Qr Qg inner .nil).lonePath = lonePos m inner := by
  simp [RegChain.lonePath, lonePos, bPath]

namespace PairData

variable {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} {G Gi : Garden 1} {Gr Gg : Garden 2}
variable (h : PairData m Qr Qg inner G Gi Gr Gg)
include h

theorem pφi_injective : Function.Injective (pφi m) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ he
  have hi : i = j := Subsingleton.elim _ _
  simp only [pφi, Prod.mk.injEq, List.cons.injEq, true_and] at he
  rw [hi, he]

theorem pφr_injective : Function.Injective (pφr m inner (G.sig 0)) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ he
  simp only [pφr, Prod.mk.injEq, true_and] at he
  have hr := regionOf_rBase m inner (G.sig 0) i p
  rw [he, regionOf_rBase] at hr
  have hij : j = i := by simpa using hr
  subst hij
  rw [List.append_cancel_left he]

theorem pφg_injective : Function.Injective (pφg m inner (G.sig 0)) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ he
  simp only [pφg, Prod.mk.injEq, true_and] at he
  have hr := regionOf_gBase m inner (G.sig 0) i p
  rw [he, regionOf_gBase] at hr
  have hij : j = i := by simpa using hr
  subst hij
  rw [List.append_cancel_left he]

theorem mark_G (ℓ : GLeaf G.tree) : G.mark ℓ = if ℓ.1.2 = lonePos m inner then some .lower else none := by
  rw [h.decZ.2.1 ℓ, cpair_lonePath']

theorem leaves_iff (p : Path) : p ∈ (G.tree 0).leaves ↔ p ∈ (pairTree m Qr Qg inner (G.sig 0)).leaves := by
  rw [h.tree0]

/-- The input-leaf addresses of a closing pair. -/
theorem inputLeaves_addr_pair :
    (inputLeaves G).map (leafEmb G.tree) =
      ((inputLeaves Gi).map (leafEmb Gi.tree)).image (pφi m) ∪
        (((inputLeaves Gr).map (leafEmb Gr.tree)).image (pφr m inner (G.sig 0)) ∪
          ((inputLeaves Gg).map (leafEmb Gg.tree)).image (pφg m inner (G.sig 0))) := by
  ext z
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_map, leafEmb_apply]
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    obtain ⟨hs, hm⟩ := (mem_inputLeaves ℓ).mp hℓ
    obtain ⟨⟨j0, p⟩, hl⟩ := ℓ
    have hj0 : j0 = 0 := Subsingleton.elim _ _
    subst hj0
    have hl' : p ∈ (pairTree m Qr Qg inner (G.sig 0)).leaves := (h.leaves_iff p).mp hl
    have hmark := h.mark_G ⟨((0 : Fin 1), p), hl⟩
    rw [hm] at hmark
    rcases pairTree_cases m inner (G.sig 0) Qr Qg p (TTree.leaves_subset_nodes _ hl') with
      rfl | rfl | rfl | ⟨q, rfl, hq, -⟩ | ⟨j, q, rfl, -⟩ | ⟨j, q, rfl, -⟩
    · exact absurd (nil_mem_pairTree_branching m Qr Qg inner _)
        (TTree.not_mem_branching_of_mem_leaves _ hl')
    · exact absurd (bPath_mem_branching m Qr Qg inner _) (TTree.not_mem_branching_of_mem_leaves _ hl')
    · simp at hmark
    · left
      have hq' : q ∈ (Gi.tree ((0 : Fin 1), q).1).leaves := by
        rw [h.treeI]; exact (mem_pairTree_inner m Qr Qg inner _ q hq).2.1.mp hl'
      refine ⟨((0 : Fin 1), q), ⟨⟨_, hq'⟩, (mem_inputLeaves _).mpr ⟨?_, ?_⟩, rfl⟩, rfl⟩
      · rw [← h.sign_ιi]; exact hs
      · have : q ≠ inner.lonePath := fun he => hq (he ▸ List.prefix_refl _)
        exact (h.decI.2.1 _).trans (by simp [this])
    · right; left
      have hq' : q ∈ (Gr.tree (j, q).1).leaves := by
        rw [h.treeR]; exact (memT_rBase m Qr Qg inner _ j q).2.1.mp hl'
      refine ⟨(j, q), ⟨⟨_, hq'⟩, (mem_inputLeaves _).mpr ⟨?_, h.decR.1.1 _⟩, rfl⟩, rfl⟩
      rw [← h.sign_ιr]; exact hs
    · right; right
      have hq' : q ∈ (Gg.tree (j, q).1).leaves := by
        rw [h.treeG]; exact (memT_gBase m Qr Qg inner _ j q).2.1.mp hl'
      refine ⟨(j, q), ⟨⟨_, hq'⟩, (mem_inputLeaves _).mpr ⟨?_, h.decG.1.1 _⟩, rfl⟩, rfl⟩
      rw [← h.sign_ιg]; exact hs
  · rintro (⟨x, ⟨ℓ, hℓ, rfl⟩, rfl⟩ | ⟨y, ⟨ℓ, hℓ, rfl⟩, rfl⟩ | ⟨y, ⟨ℓ, hℓ, rfl⟩, rfl⟩) <;>
      obtain ⟨hs, hm⟩ := (mem_inputLeaves ℓ).mp hℓ
    · have hne : ℓ.1.2 ≠ inner.lonePath := by
        intro he
        rw [h.decI.2.1 ℓ, if_pos he] at hm
        exact absurd hm (by simp)
      have hnp : ¬ inner.lonePath <+: ℓ.1.2 := by
        intro hpre
        have hmem := ℓ.2
        rw [show ℓ.1.1 = 0 from Subsingleton.elim _ _, h.decI.1] at hmem
        exact hne (plug_leaf_prefix inner _ (TTree.leaves_subset_nodes _ hmem) hpre)
      have hmem : (pφi m ℓ.1).2 ∈ (G.tree (pφi m ℓ.1).1).leaves := by
        show m.c :: ℓ.1.2 ∈ (G.tree 0).leaves
        rw [h.tree0]
        have hl := ℓ.2
        rw [show ℓ.1.1 = 0 from Subsingleton.elim _ _, h.treeI] at hl
        exact (mem_pairTree_inner m Qr Qg inner _ _ hnp).2.1.mpr hl
      refine ⟨⟨pφi m ℓ.1, hmem⟩, (mem_inputLeaves _).mpr ⟨?_, ?_⟩, rfl⟩
      · have e : h.ιi ℓ.toNode = GLeaf.toNode ⟨pφi m ℓ.1, hmem⟩ := rfl
        rw [← e, h.sign_ιi]; exact hs
      · have : (pφi m ℓ.1).2 ≠ lonePos m inner := by
          intro he
          apply hnp
          have he' : m.c :: ℓ.1.2 = m.c :: (inner.lonePath ++ [m.lone]) := by
            rw [← lonePos_eq]; exact he
          rw [List.cons.injEq] at he'
          rw [he'.2]
          exact List.prefix_append _ _
        exact (h.mark_G _).trans (by simp [this])
    · have hmem : (pφr m inner (G.sig 0) ℓ.1).2 ∈ (G.tree (pφr m inner (G.sig 0) ℓ.1).1).leaves := by
        show _ ∈ (G.tree 0).leaves
        rw [h.tree0]
        have hl := ℓ.2
        rw [h.treeR] at hl
        exact (memT_rBase m Qr Qg inner _ ℓ.1.1 ℓ.1.2).2.1.mpr hl
      refine ⟨⟨pφr m inner (G.sig 0) ℓ.1, hmem⟩, (mem_inputLeaves _).mpr ⟨?_, ?_⟩, rfl⟩
      · have e : h.ιr ℓ.toNode = GLeaf.toNode ⟨pφr m inner (G.sig 0) ℓ.1, hmem⟩ := rfl
        rw [← e, h.sign_ιr]; exact hs
      · have : (pφr m inner (G.sig 0) ℓ.1).2 ≠ lonePos m inner := by
          intro he
          have h1 := regionOf_rBase m inner (G.sig 0) ℓ.1.1 ℓ.1.2
          have h2 := regionOf_lonePos m inner (G.sig 0)
          rw [← he] at h2
          simp only [pφr] at h2
          rw [h1] at h2
          exact absurd h2 (by simp)
        exact (h.mark_G _).trans (by simp [this])
    · have hmem : (pφg m inner (G.sig 0) ℓ.1).2 ∈ (G.tree (pφg m inner (G.sig 0) ℓ.1).1).leaves := by
        show _ ∈ (G.tree 0).leaves
        rw [h.tree0]
        have hl := ℓ.2
        rw [h.treeG] at hl
        exact (memT_gBase m Qr Qg inner _ ℓ.1.1 ℓ.1.2).2.1.mpr hl
      refine ⟨⟨pφg m inner (G.sig 0) ℓ.1, hmem⟩, (mem_inputLeaves _).mpr ⟨?_, ?_⟩, rfl⟩
      · have e : h.ιg ℓ.toNode = GLeaf.toNode ⟨pφg m inner (G.sig 0) ℓ.1, hmem⟩ := rfl
        rw [← e, h.sign_ιg]; exact hs
      · have : (pφg m inner (G.sig 0) ℓ.1).2 ≠ lonePos m inner := by
          intro he
          have h1 := regionOf_gBase m inner (G.sig 0) ℓ.1.1 ℓ.1.2
          have h2 := regionOf_lonePos m inner (G.sig 0)
          rw [← he] at h2
          simp only [pφg] at h2
          rw [h1] at h2
          exact absurd h2 (by simp)
        exact (h.mark_G _).trans (by simp [this])

/-- **The input leaves of a closing pair.** -/
theorem prod_inputLeaves_pair {M : Type*} [CommMonoid M] (f : Fin 1 × Path → M) :
    ∏ ℓ ∈ inputLeaves G, f ℓ.1 =
      (∏ ℓ ∈ inputLeaves Gi, f (pφi m ℓ.1)) *
        ((∏ ℓ ∈ inputLeaves Gr, f (pφr m inner (G.sig 0) ℓ.1)) *
          ∏ ℓ ∈ inputLeaves Gg, f (pφg m inner (G.sig 0) ℓ.1)) := by
  classical
  set A := (inputLeaves G).map (leafEmb G.tree)
  set Ai := (inputLeaves Gi).map (leafEmb Gi.tree)
  set Ar := (inputLeaves Gr).map (leafEmb Gr.tree)
  set Ag := (inputLeaves Gg).map (leafEmb Gg.tree)
  have e0 : ∏ ℓ ∈ inputLeaves G, f ℓ.1 = ∏ z ∈ A, f z := by rw [prod_map]; rfl
  have e1 : ∏ ℓ ∈ inputLeaves Gi, f (pφi m ℓ.1) = ∏ z ∈ Ai, f (pφi m z) := by rw [prod_map]; rfl
  have e2 : ∏ ℓ ∈ inputLeaves Gr, f (pφr m inner (G.sig 0) ℓ.1) = ∏ z ∈ Ar, f (pφr m inner (G.sig 0) z) := by
    rw [prod_map]; rfl
  have e3 : ∏ ℓ ∈ inputLeaves Gg, f (pφg m inner (G.sig 0) ℓ.1) = ∏ z ∈ Ag, f (pφg m inner (G.sig 0) z) := by
    rw [prod_map]; rfl
  rw [e0, e1, e2, e3]
  -- regions of the three images
  have regI : ∀ z ∈ Ai, regionOf m inner (G.sig 0) (pφi m z).2 = .inner := by
    intro z hz
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_map.mp hz
    simp only [inputLeaves, mem_filter, mem_univ, true_and] at hℓ
    have hne : ℓ.1.2 ≠ inner.lonePath := by
      intro he
      have hm := hℓ.2
      rw [h.decI.2.1 ℓ, if_pos he] at hm
      exact absurd hm (by simp)
    have hnp : ¬ inner.lonePath <+: ℓ.1.2 := by
      intro hpre
      have hmem := ℓ.2
      rw [show ℓ.1.1 = 0 from Subsingleton.elim _ _, h.decI.1] at hmem
      exact hne (plug_leaf_prefix inner _ (TTree.leaves_subset_nodes _ hmem) hpre)
    exact regionOf_inner m inner _ _ hnp
  have regR : ∀ z ∈ Ar, ∃ j, regionOf m inner (G.sig 0) (pφr m inner (G.sig 0) z).2 = .red j :=
    fun z _ => ⟨z.1, regionOf_rBase m inner _ _ _⟩
  have regG : ∀ z ∈ Ag, ∃ j, regionOf m inner (G.sig 0) (pφg m inner (G.sig 0) z).2 = .green j :=
    fun z _ => ⟨z.1, regionOf_gBase m inner _ _ _⟩
  have hdisj1 : Disjoint (Ai.image (pφi m)) (Ar.image (pφr m inner (G.sig 0)) ∪ Ag.image (pφg m inner (G.sig 0))) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have h1 := regI x hx
    rcases Finset.mem_union.mp hz' with hz' | hz'
    · obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hz'
      obtain ⟨j, hj⟩ := regR y hy
      rw [hxy, h1] at hj; exact absurd hj (by simp)
    · obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hz'
      obtain ⟨j, hj⟩ := regG y hy
      rw [hxy, h1] at hj; exact absurd hj (by simp)
  have hdisj2 : Disjoint (Ar.image (pφr m inner (G.sig 0))) (Ag.image (pφg m inner (G.sig 0))) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hz'
    obtain ⟨j, hj⟩ := regR x hx
    obtain ⟨j', hj'⟩ := regG y hy
    rw [hxy, hj] at hj'; exact absurd hj' (by simp)
  have hA : A = Ai.image (pφi m) ∪ (Ar.image (pφr m inner (G.sig 0)) ∪ Ag.image (pφg m inner (G.sig 0))) :=
    h.inputLeaves_addr_pair
  rw [hA, prod_union hdisj1, prod_union hdisj2, prod_image (fun x _ y _ hxy => h.pφi_injective hxy),
    prod_image (fun x _ y _ hxy => h.pφr_injective hxy), prod_image (fun x _ y _ hxy => h.pφg_injective hxy)]

theorem inputLeaf_ofI (ℓ : GLeaf Gi.tree) (hℓ : ℓ ∈ inputLeaves Gi) :
    ∃ ℓ' ∈ inputLeaves G, ℓ'.1 = pφi m ℓ.1 := by
  have : pφi m ℓ.1 ∈ (inputLeaves G).map (leafEmb G.tree) := by
    rw [h.inputLeaves_addr_pair]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ℓ.1, Finset.mem_map.mpr ⟨ℓ, hℓ, rfl⟩, rfl⟩)
  obtain ⟨ℓ', h1, h2⟩ := Finset.mem_map.mp this
  exact ⟨ℓ', h1, h2⟩

theorem inputLeaf_ofR (ℓ : GLeaf Gr.tree) (hℓ : ℓ ∈ inputLeaves Gr) :
    ∃ ℓ' ∈ inputLeaves G, ℓ'.1 = pφr m inner (G.sig 0) ℓ.1 := by
  have : pφr m inner (G.sig 0) ℓ.1 ∈ (inputLeaves G).map (leafEmb G.tree) := by
    rw [h.inputLeaves_addr_pair]
    exact Finset.mem_union_right _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨ℓ.1, Finset.mem_map.mpr ⟨ℓ, hℓ, rfl⟩, rfl⟩))
  obtain ⟨ℓ', h1, h2⟩ := Finset.mem_map.mp this
  exact ⟨ℓ', h1, h2⟩

theorem inputLeaf_ofG (ℓ : GLeaf Gg.tree) (hℓ : ℓ ∈ inputLeaves Gg) :
    ∃ ℓ' ∈ inputLeaves G, ℓ'.1 = pφg m inner (G.sig 0) ℓ.1 := by
  have : pφg m inner (G.sig 0) ℓ.1 ∈ (inputLeaves G).map (leafEmb G.tree) := by
    rw [h.inputLeaves_addr_pair]
    exact Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨ℓ.1, Finset.mem_map.mpr ⟨ℓ, hℓ, rfl⟩, rfl⟩))
  obtain ⟨ℓ', h1, h2⟩ := Finset.mem_map.mp this
  exact ⟨ℓ', h1, h2⟩

end PairData

end WaveTurbulence.Flower.ProtCut
