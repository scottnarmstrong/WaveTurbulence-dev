/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Spec
public import WaveTurbulence.Foundations.Spine.coarse_spliced.Count
/-! # Counting facts for a ladder (S3c) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine Finset
open scoped Classical

variable {w : ℕ} {G : Garden w}

/-- A ladder has at least `4m + 2` bonds inside its atomic group (rungs and rails; chords between
end atoms may add more). -/
theorem card_bonds_inGroup_ge {m : ℕ} {u v : Fin (m + 1) → GBranch G.tree}
    (h : G.molecule.IsLadder u v) :
    4 * m + 2 ≤ (G.molecule.bonds.filter (G.molecule.InGroup (Molecule.ladderAtoms u v))).card := by
  obtain ⟨-, hinj, hmem, hbb, hrail⟩ := h
  obtain ⟨hu, hv, hcross⟩ := Sum.elim_injective.mp hinj
  let e : (Fin (m + 1) ⊕ (Fin m ⊕ Fin m)) → Sym2 (GBranch G.tree) := fun i =>
    match i with
    | .inl j => s(u j, v j)
    | .inr (.inl j) => s(u j.castSucc, u j.succ)
    | .inr (.inr j) => s(v j.castSucc, v j.succ)
  have hcr : ∀ a b, u a ≠ v b := fun a b => hcross a b
  have he : Function.Injective e := by
    intro i k hik
    rcases i with j | j | j <;> rcases k with k | k | k <;> simp only [e, Sym2.eq_iff] at hik
    · rcases hik with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact congrArg Sum.inl (hu h1)
      · exact absurd h2.symm (hcr _ _)
    · rcases hik with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (exact absurd h2.symm (hcr _ _))
    · rcases hik with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (exact absurd h1 (hcr _ _))
    · rcases hik with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (first | exact absurd h1 (hcr _ _) | exact absurd h2 (hcr _ _))
    · rcases hik with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hu h1
        exact congrArg (fun x => Sum.inr (Sum.inl x)) (Fin.castSucc_injective _ this)
      · have e1 := hu h1
        have e2 := hu h2
        have a1 := congrArg Fin.val e1
        have a2 := congrArg Fin.val e2
        simp at a1 a2
        omega
    · rcases hik with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (exact absurd h1 (hcr _ _))
    · rcases hik with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (first | exact absurd h1.symm (hcr _ _) | exact absurd h2.symm (hcr _ _))
    · rcases hik with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (exact absurd h1.symm (hcr _ _))
    · rcases hik with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hv h1
        exact congrArg (fun x => Sum.inr (Sum.inr x)) (Fin.castSucc_injective _ this)
      · have e1 := hv h1
        have e2 := hv h2
        have a1 := congrArg Fin.val e1
        have a2 := congrArg Fin.val e2
        simp at a1 a2
        omega
  let B : (Fin (m + 1) ⊕ (Fin m ⊕ Fin m)) → Finset (GardenDart G) := fun i =>
    G.molecule.bonds.filter (fun x => G.molecule.ends x = e i)
  have hdisj : ∀ i k, i ≠ k → Disjoint (B i) (B k) := by
    intro i k hik
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [B, mem_filter] at hx hx'
    exact hik (he (hx.2.symm.trans hx'.2))
  have hsub : (univ.biUnion B) ⊆
      G.molecule.bonds.filter (G.molecule.InGroup (Molecule.ladderAtoms u v)) := by
    intro x hx
    obtain ⟨i, -, hi⟩ := mem_biUnion.mp hx
    simp only [B, mem_filter] at hi
    refine mem_filter.mpr ⟨hi.1, ?_⟩
    have hends := hi.2
    have hin : ∀ a b, a ∈ Molecule.ladderAtoms u v → b ∈ Molecule.ladderAtoms u v →
        G.molecule.ends x = s(a, b) → G.molecule.InGroup (Molecule.ladderAtoms u v) x := by
      intro a b ha hb hab
      simp only [Molecule.ends, Sym2.eq_iff] at hab
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by rw [h1]; exact ha, by rw [h2]; exact hb⟩
      · exact ⟨by rw [h1]; exact hb, by rw [h2]; exact ha⟩
    have memu : ∀ k, u k ∈ Molecule.ladderAtoms u v := fun k =>
      mem_union_left _ (mem_image_of_mem _ (mem_univ k))
    have memv : ∀ k, v k ∈ Molecule.ladderAtoms u v := fun k =>
      mem_union_right _ (mem_image_of_mem _ (mem_univ k))
    rcases i with j | j | j
    · exact hin _ _ (memu j) (memv j) hends
    · exact hin _ _ (memu _) (memu _) hends
    · exact hin _ _ (memv _) (memv _) hends
  have hcard : (univ.biUnion B).card = 4 * m + 2 := by
    rw [Finset.card_biUnion (fun i _ k _ hik => hdisj i k hik), Fintype.sum_sum_type, Fintype.sum_sum_type]
    have h1 : ∀ j : Fin (m + 1), (B (.inl j)).card = 2 := fun j => hbb j
    have h2 : ∀ j : Fin m, (B (.inr (.inl j))).card = 1 := fun j => (hrail j).1
    have h3 : ∀ j : Fin m, (B (.inr (.inr j))).card = 1 := fun j => (hrail j).2.1
    simp only [h1, h2, h3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  calc 4 * m + 2 = (univ.biUnion B).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

theorem card_ladderAtoms_ladder {m : ℕ} {u v : Fin (m + 1) → GBranch G.tree}
    (h : G.molecule.IsLadder u v) : (Molecule.ladderAtoms u v).card = 2 * m + 2 := by
  have := ladderAtoms_card_of_injective h.2.1
  omega

theorem ladderAtoms_subset_atoms {m : ℕ} {u v : Fin (m + 1) → GBranch G.tree}
    (h : G.molecule.IsLadder u v) : Molecule.ladderAtoms u v ⊆ G.molecule.atoms := by
  intro x hx
  unfold Molecule.ladderAtoms at hx
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨j, -, rfl⟩ := mem_image.mp hx
    exact (h.2.2.1 j).1
  · obtain ⟨j, -, rfl⟩ := mem_image.mp hx
    exact (h.2.2.1 j).2

end WaveTurbulence.CoarseSpliced
