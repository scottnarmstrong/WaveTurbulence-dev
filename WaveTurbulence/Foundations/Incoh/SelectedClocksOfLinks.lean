/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RootCoordinatesOfEmbedding
public import WaveTurbulence.Foundations.Incoh.SelectedLinkClocks

/-! # Constructing complete selected clock pairs from actual distinct links -/

public section
noncomputable section
open scoped Classical

namespace WaveTurbulence.Incoh

/-- Enumerate both endpoints of every selected link, in the selected link order. -/
@[expose] def selectedVerticesOfLinks {n h : ℕ} (v : Fin h ↪ Fin n) : Fin (h * 2) ↪ (Fin n × Fin 2) where
  toFun k := (v (finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)
  inj' := by
    intro i j he
    have h1 := v.injective (congrArg Prod.fst he)
    have h2 := congrArg Prod.snd he
    exact finProdFinEquiv.symm.injective (Prod.ext h1 h2)

/-- The root-link set is exactly the range of the selected source links. -/
theorem rootLinks_selectedVertices {n h : ℕ} (v : Fin h ↪ Fin n) :
    (rootCoordinatesOfEmbedding (selectedVerticesOfLinks v)).rootLinks = Finset.univ.image v := by
  ext i
  simp only [RootCoordinates.rootLinks, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    rw [rootCoordinatesOfEmbedding_rootVertex] at hk
    exact ⟨(finProdFinEquiv.symm k).1, hk⟩
  · rintro ⟨j, rfl⟩
    refine ⟨finProdFinEquiv (j, 0), ?_⟩
    rw [rootCoordinatesOfEmbedding_rootVertex]
    change v (finProdFinEquiv.symm (finProdFinEquiv (j, 0))).1 = v j
    rw [Equiv.symm_apply_apply]

/-- The actual endpoint pairing induced by the selected link embedding. -/
@[expose] def selectedLinkPairMap {n h : ℕ} (v : Fin h ↪ Fin n) (k : Fin (h * 2)) :
    {i : Fin n // i ∈ (rootCoordinatesOfEmbedding (selectedVerticesOfLinks v)).rootLinks} × Fin 2 :=
  (⟨v (finProdFinEquiv.symm k).1, by
    rw [rootLinks_selectedVertices]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩, (finProdFinEquiv.symm k).2)

/-- No selected endpoint is repeated or omitted. -/
theorem selectedLinkPairMap_bijective {n h : ℕ} (v : Fin h ↪ Fin n) :
    Function.Bijective (selectedLinkPairMap v) := by
  constructor
  · intro i j he
    have h1 := v.injective (congrArg (fun p => p.1.val) he)
    have h2 := congrArg Prod.snd he
    exact finProdFinEquiv.symm.injective (Prod.ext h1 h2)
  · rintro ⟨⟨i, hi⟩, b⟩
    rw [rootLinks_selectedVertices] at hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    refine ⟨finProdFinEquiv (j, b), ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change v (finProdFinEquiv.symm (finProdFinEquiv (j, b))).1 = v j
      rw [Equiv.symm_apply_apply]
    · change (finProdFinEquiv.symm (finProdFinEquiv (j, b))).2 = b
      rw [Equiv.symm_apply_apply]

/-- The full analytic selected-clock carrier follows from actual distinct selected links. -/
@[expose] def selectedClocksOfLinks {n h : ℕ} (v : Fin h ↪ Fin n) : SelectedLinkClocks n (h * 2) where
  coordinates := rootCoordinatesOfEmbedding (selectedVerticesOfLinks v)
  pairing := Equiv.ofBijective (selectedLinkPairMap v) (selectedLinkPairMap_bijective v)
  vertex_eq := by
    intro k
    exact rootCoordinatesOfEmbedding_rootVertex (selectedVerticesOfLinks v) k

end WaveTurbulence.Incoh
