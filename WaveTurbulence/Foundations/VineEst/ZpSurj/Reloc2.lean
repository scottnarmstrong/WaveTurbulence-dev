/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Reloc1
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.ReplaceTree

/-! # ZP-SURJ: relocation of the layerreg1 layer patterns

`LayerPatternN`/`TreePatternN`: the patterns of TARGET `layerreg1` (1) with the parent layers of the roots given as
numbers. `layerPatternN_reloc`/`treePatternN_reloc`: they only depend on the layers of the region and `(pa, pb)`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree WaveTurbulence.Reg WaveTurbulence.Links

variable {w w' : ℕ}

/-- `LayerPattern` with the parent layers of the two roots given as numbers. -/
@[expose] def LayerPatternN (LG : LayeredGarden w) (pa pb : ℕ) (Q : RegCpl) (a b : Fin w × Path) : Prop :=
  CohOn LG (Q.linksAt a b) ∧
  match Q with
  | .type2 Xp Xm Qlp =>
    (∀ z ∈ cplNodes Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath), layerAt LG z = min pa pb) ∧
    ChainPairLayers LG Xp 1 a ∧ ChainPairLayers LG Xm (-1) b ∧
    (∀ z ∈ chainNodesSet Xp 1 a, min pa pb ≤ layerAt LG z ∧ layerAt LG z ≤ pa) ∧
    (∀ z ∈ chainNodesSet Xm (-1) b, min pa pb ≤ layerAt LG z ∧ layerAt LG z ≤ pb)
  | Q => ∀ z ∈ cplNodes Q a b, layerAt LG z = min pa pb

theorem layerPattern_eq_N {LG : LayeredGarden w} {p : ℕ} {Q : RegCpl} {a b : Fin w × Path} :
    LayerPattern LG p Q a b ↔ LayerPatternN LG (parAt LG p a) (parAt LG p b) Q a b := Iff.rfl

/-- `TreePattern` with the parent layer of the root given as a number. -/
@[expose] def TreePatternN (LG : LayeredGarden w) (pa : ℕ) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) : Prop :=
  CohOn LG (X.linksAt ζ a) ∧ ChainPairLayers LG X ζ a ∧
  ∀ z ∈ chainNodesSet X ζ a, layerAt LG (addrExt a X.lonePath) ≤ layerAt LG z ∧ layerAt LG z ≤ pa

theorem treePattern_eq_N {LG : LayeredGarden w} {p : ℕ} {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} :
    TreePattern LG p X ζ a ↔ TreePatternN LG (parAt LG p a) X ζ a := Iff.rfl

theorem mem_pairEndpoints_fst {L : List ((Fin w × Path) × (Fin w × Path))} {l : (Fin w × Path) × (Fin w × Path)}
    (hl : l ∈ L) : l.1 ∈ pairEndpoints L :=
  Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_map.2 ⟨l, hl, rfl⟩))

theorem mem_pairEndpoints_snd {L : List ((Fin w × Path) × (Fin w × Path))} {l : (Fin w × Path) × (Fin w × Path)}
    (hl : l ∈ L) : l.2 ∈ pairEndpoints L :=
  Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map.2 ⟨l, hl, rfl⟩))

section Reloc
variable (P : Fin w × Path → Prop) (ρ : Fin w × Path → Fin w' × Path)
  (hP : ∀ x q, P x → P (addrExt x q)) (hρ : ∀ x q, P x → ρ (addrExt x q) = addrExt (ρ x) q)

theorem mem_pairEndpoints_map {f : Fin w × Path → Fin w' × Path} {L : List ((Fin w × Path) × (Fin w × Path))}
    {z : Fin w' × Path} :
    z ∈ pairEndpoints (L.map (fun l => (f l.1, f l.2))) ↔ ∃ y ∈ pairEndpoints L, f y = z := by
  simp only [pairEndpoints, Finset.mem_union, List.mem_toFinset, List.map_map, List.mem_map, Function.comp_def]
  constructor
  · rintro (⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact ⟨l.1, Or.inl ⟨l, hl, rfl⟩, rfl⟩
    · exact ⟨l.2, Or.inr ⟨l, hl, rfl⟩, rfl⟩
  · rintro ⟨y, (⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩), rfl⟩
    · exact Or.inl ⟨l, hl, rfl⟩
    · exact Or.inr ⟨l, hl, rfl⟩

include hP hρ

theorem mem_cplNodes_map (Q : RegCpl) (a b : Fin w × Path) (ha : P a) (hb : P b) (z : Fin w' × Path) :
    z ∈ cplNodes Q (ρ a) (ρ b) ↔ ∃ y ∈ cplNodes Q a b, ρ y = z := by
  unfold cplNodes
  rw [cpl_links_map P ρ hP hρ Q a b ha hb, cpl_pairs_map P ρ hP hρ Q a b ha hb, Finset.mem_union,
    mem_pairEndpoints_map, mem_pairEndpoints_map]
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, Finset.mem_union_left _ hy, rfl⟩
    · exact ⟨y, Finset.mem_union_right _ hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rcases Finset.mem_union.1 hy with hy | hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨y, hy, rfl⟩

theorem mem_chainNodesSet_map (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (ha : P a) (z : Fin w' × Path) :
    z ∈ chainNodesSet X ζ (ρ a) ↔ ∃ y ∈ chainNodesSet X ζ a, ρ y = z := by
  unfold chainNodesSet
  rw [chain_links_map P ρ hP hρ X ζ a ha, chain_pairs_map P ρ hP hρ X ζ a ha, Finset.mem_union,
    mem_pairEndpoints_map, mem_pairEndpoints_map]
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, Finset.mem_union_left _ hy, rfl⟩
    · exact ⟨y, Finset.mem_union_right _ hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rcases Finset.mem_union.1 hy with hy | hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨y, hy, rfl⟩

omit hP hρ in
theorem ball_map {α β : Type*} (f : α → β) (M1 : Finset α) (M2 : Finset β)
    (hM : ∀ z, z ∈ M2 ↔ ∃ u ∈ M1, f u = z) (F1 : α → Prop) (F2 : β → Prop)
    (hF : ∀ u ∈ M1, F2 (f u) ↔ F1 u) : (∀ z ∈ M2, F2 z) ↔ ∀ u ∈ M1, F1 u := by
  constructor
  · intro h u hu; exact (hF u hu).1 (h _ ((hM _).2 ⟨u, hu, rfl⟩))
  · intro h z hz
    obtain ⟨u, hu, rfl⟩ := (hM z).1 hz
    exact (hF u hu).2 (h u hu)

theorem mem_oriented_map (Pr : Prop) [Decidable Pr] (Q : RegCpl) (x y : Fin w × Path) (hx : P x) (hy : P y)
    (z : Fin w' × Path) :
    z ∈ orientedNodes Pr Q (ρ x) (ρ y) ↔ ∃ u ∈ orientedNodes Pr Q x y, ρ u = z := by
  unfold orientedNodes
  split_ifs
  · exact mem_cplNodes_map P ρ hP hρ Q x y hx hy z
  · exact mem_cplNodes_map P ρ hP hρ Q y x hy hx z

omit hρ in
theorem P_of_under {a z : Fin w × Path} (ha : P a) (h : Under a z) : P z := by
  obtain ⟨q, rfl⟩ := under_of_addrExt h
  exact hP a q ha

omit hρ in
theorem oriented_P (Pr : Prop) [Decidable Pr] (Q : RegCpl) (x y : Fin w × Path) (hx : P x) (hy : P y)
    {u : Fin w × Path} (hu : u ∈ orientedNodes Pr Q x y) : P u := by
  rcases oriented_under hu with h | h
  · exact P_of_under P hP hx h
  · exact P_of_under P hP hy h

variable {H1 : LayeredGarden w} {H2 : LayeredGarden w'}
  (hlay : ∀ z, P z → layerAt H2 (ρ z) = layerAt H1 z)

include hlay

theorem layerAt_ext_map {a : Fin w × Path} (ha : P a) (q : Path) :
    layerAt H2 (addrExt (ρ a) q) = layerAt H1 (addrExt a q) := by
  rw [← hρ a q ha]; exact hlay _ (hP a q ha)

theorem oriented_layers_map (Pr : Prop) [Decidable Pr] (Q : RegCpl) (x y : Fin w × Path) (a : Fin w × Path)
    (hx : P x) (hy : P y) (ha : P a) :
    (∀ z ∈ orientedNodes Pr Q (ρ x) (ρ y), layerAt H2 z = layerAt H2 (ρ a)) ↔
    (∀ z ∈ orientedNodes Pr Q x y, layerAt H1 z = layerAt H1 a) := by
  refine ball_map ρ _ _ (fun z => mem_oriented_map P ρ hP hρ Pr Q x y hx hy z) _ _ ?_
  intro u hu
  rw [hlay u (oriented_P P hP Pr Q x y hx hy hu), hlay a ha]

theorem chainPairLayers_map (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (ha : P a) :
    ChainPairLayers H2 X ζ (ρ a) ↔ ChainPairLayers H1 X ζ a := by
  cases X with
  | nil => simp [ChainPairLayers]
  | pair m Qr Qg inner rest =>
    have hl := layerAt_ext_map P ρ hP hρ hlay ha
    have e0 : layerAt H2 (ρ a) = layerAt H1 a := hlay a ha
    have hi := chainPairLayers_map inner (slotSign ζ m.c) (addrExt a [m.c]) (hP _ _ ha)
    have hr := chainPairLayers_map rest (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) (hP _ _ ha)
    have hor := oriented_layers_map P ρ hP hρ hlay (slotSign ζ m.red.1 = 1) Qr (addrExt a [m.red.1])
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) a (hP _ _ ha) (hP _ _ ha) ha
    have hog := oriented_layers_map P ρ hP hρ hlay (slotSign ζ m.green.1 = 1) Qg (addrExt a [m.green.1])
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) a (hP _ _ ha) (hP _ _ ha) ha
    simp only [hρ a _ ha] at hi hr hor hog
    rw [e0] at hor hog
    simp only [ChainPairLayers, hi, hr, hl, e0, hor, hog]
termination_by structural X

omit hρ hlay in
theorem cplNodes_P (Q : RegCpl) {a b : Fin w × Path} (ha : P a) (hb : P b) {z : Fin w × Path}
    (hz : z ∈ cplNodes Q a b) : P z := by
  rcases cpl_endpoints_under Q a b z hz with h | h
  · exact P_of_under P hP ha h
  · exact P_of_under P hP hb h

omit hρ hlay in
theorem chainNodes_P (X : RegChain) (ζ : ℤˣ) {a : Fin w × Path} (ha : P a) {z : Fin w × Path}
    (hz : z ∈ chainNodesSet X ζ a) : P z :=
  P_of_under P hP ha (chain_endpoints_region X ζ a z hz).1

theorem cohOn_cpl_map (Q : RegCpl) (a b : Fin w × Path) (ha : P a) (hb : P b) :
    CohOn H2 (Q.linksAt (ρ a) (ρ b)) ↔ CohOn H1 (Q.linksAt a b) := by
  rw [cpl_links_map P ρ hP hρ Q a b ha hb]
  unfold CohOn
  simp only [List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h l hl
    have h1 : P l.1 := cplNodes_P P hP Q ha hb (Finset.mem_union_left _ (mem_pairEndpoints_fst hl))
    have h2 : P l.2 := cplNodes_P P hP Q ha hb (Finset.mem_union_left _ (mem_pairEndpoints_snd hl))
    have := h _ l hl rfl
    rwa [hlay _ h1, hlay _ h2] at this
  · intro h l' l hl e
    subst e
    have h1 : P l.1 := cplNodes_P P hP Q ha hb (Finset.mem_union_left _ (mem_pairEndpoints_fst hl))
    have h2 : P l.2 := cplNodes_P P hP Q ha hb (Finset.mem_union_left _ (mem_pairEndpoints_snd hl))
    simp only
    rw [hlay _ h1, hlay _ h2]
    exact h l hl

theorem cohOn_chain_map (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (ha : P a) :
    CohOn H2 (X.linksAt ζ (ρ a)) ↔ CohOn H1 (X.linksAt ζ a) := by
  rw [chain_links_map P ρ hP hρ X ζ a ha]
  unfold CohOn
  simp only [List.mem_map, forall_exists_index, and_imp]
  have hP' : ∀ l ∈ X.linksAt ζ a, P l.1 ∧ P l.2 := fun l hl =>
    ⟨chainNodes_P P hP X ζ ha (Finset.mem_union_left _ (mem_pairEndpoints_fst hl)),
     chainNodes_P P hP X ζ ha (Finset.mem_union_left _ (mem_pairEndpoints_snd hl))⟩
  constructor
  · intro h l hl
    have := h _ l hl rfl
    rwa [hlay _ (hP' l hl).1, hlay _ (hP' l hl).2] at this
  · intro h l' l hl e
    subst e
    simp only
    rw [hlay _ (hP' l hl).1, hlay _ (hP' l hl).2]
    exact h l hl

theorem layerPatternN_map (pa pb : ℕ) (Q : RegCpl) (a b : Fin w × Path) (ha : P a) (hb : P b) :
    LayerPatternN H2 pa pb Q (ρ a) (ρ b) ↔ LayerPatternN H1 pa pb Q a b := by
  have hn : ∀ (Q' : RegCpl) (x y : Fin w × Path), P x → P y →
      ((∀ z ∈ cplNodes Q' (ρ x) (ρ y), layerAt H2 z = min pa pb) ↔
        ∀ z ∈ cplNodes Q' x y, layerAt H1 z = min pa pb) := by
    intro Q' x y hx hy
    refine ball_map ρ _ _ (fun z => mem_cplNodes_map P ρ hP hρ Q' x y hx hy z) _ _ ?_
    intro u hu
    rw [hlay u (cplNodes_P P hP Q' hx hy hu)]
  unfold LayerPatternN
  refine and_congr (cohOn_cpl_map P ρ hP hρ hlay Q a b ha hb) ?_
  cases Q with
  | triv => exact hn _ a b ha hb
  | type1 c Q₁ Q₂ Q₃ => exact hn _ a b ha hb
  | type2 Xp Xm Qlp =>
    have hc1 := hn Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) (hP _ _ ha) (hP _ _ hb)
    simp only [hρ a _ ha, hρ b _ hb] at hc1
    have hxp := fun (u : Fin w' × Path) => mem_chainNodesSet_map P ρ hP hρ Xp 1 a ha u
    have hxm := fun (u : Fin w' × Path) => mem_chainNodesSet_map P ρ hP hρ Xm (-1) b hb u
    have h4 : (∀ z ∈ chainNodesSet Xp 1 (ρ a), min pa pb ≤ layerAt H2 z ∧ layerAt H2 z ≤ pa) ↔
        ∀ z ∈ chainNodesSet Xp 1 a, min pa pb ≤ layerAt H1 z ∧ layerAt H1 z ≤ pa := by
      refine ball_map ρ _ _ hxp _ _ ?_
      intro u hu; rw [hlay u (chainNodes_P P hP Xp 1 ha hu)]
    have h5 : (∀ z ∈ chainNodesSet Xm (-1) (ρ b), min pa pb ≤ layerAt H2 z ∧ layerAt H2 z ≤ pb) ↔
        ∀ z ∈ chainNodesSet Xm (-1) b, min pa pb ≤ layerAt H1 z ∧ layerAt H1 z ≤ pb := by
      refine ball_map ρ _ _ hxm _ _ ?_
      intro u hu; rw [hlay u (chainNodes_P P hP Xm (-1) hb hu)]
    dsimp only
    rw [hc1, chainPairLayers_map P ρ hP hρ hlay Xp 1 a ha, chainPairLayers_map P ρ hP hρ hlay Xm (-1) b hb, h4, h5]

theorem treePatternN_map (pa : ℕ) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (ha : P a) :
    TreePatternN H2 pa X ζ (ρ a) ↔ TreePatternN H1 pa X ζ a := by
  unfold TreePatternN
  have hxp := fun (u : Fin w' × Path) => mem_chainNodesSet_map P ρ hP hρ X ζ a ha u
  have hl : layerAt H2 (addrExt (ρ a) X.lonePath) = layerAt H1 (addrExt a X.lonePath) :=
    layerAt_ext_map P ρ hP hρ hlay ha _
  have h4 : (∀ z ∈ chainNodesSet X ζ (ρ a), layerAt H2 (addrExt (ρ a) X.lonePath) ≤ layerAt H2 z ∧
      layerAt H2 z ≤ pa) ↔
      ∀ z ∈ chainNodesSet X ζ a, layerAt H1 (addrExt a X.lonePath) ≤ layerAt H1 z ∧ layerAt H1 z ≤ pa := by
    rw [hl]
    refine ball_map ρ _ _ hxp _ _ ?_
    intro u hu; rw [hlay u (chainNodes_P P hP X ζ ha hu)]
  rw [cohOn_chain_map P ρ hP hρ hlay X ζ a ha, chainPairLayers_map P ρ hP hρ hlay X ζ a ha, h4]

end Reloc
end WaveTurbulence.ZpSurj
