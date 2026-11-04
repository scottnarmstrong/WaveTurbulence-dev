/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalizationTree

/-!
# Finite tree momentum localization

TARGET treelemma (2), reused from C2's statement-independent bottom-up
cover argument. There are at most C^order simultaneous vertex centers.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh.LocalizationTree

/-- **DH23 Lemma A.4 (1)** (`explem`, L2116–L2127) and **TARGET Lemma `treelemma` (2)**
(L2422–L2430): decorations with leaves in unit balls around `k⁰` split into at most `C^n`
sub-collections on which every `k_𝔫` lies in a fixed unit ball. -/
theorem exists_finite_localization (d : ℕ) : ∃ C : ℕ, ∀ (t : LocalizationTree) (k0 : Path → Mom d),
    ∃ S : Finset (Path → Mom d), S.card ≤ C ^ t.order ∧
      ∀ k : Path → Mom d, IsDecoration t k → (∀ p ∈ t.leaves, ‖k p - k0 p‖ ≤ 1) →
        ∃ c ∈ S, ∀ p ∈ t.nodes, ‖k p - c p‖ ≤ 1 := by
  obtain ⟨F, hF⟩ := Links.exists_unit_cover_at (E := Mom d) 3
  refine ⟨F.card, fun t => ?_⟩
  induction t with
  | leaf =>
    intro k0
    refine ⟨{k0}, by simp [LocalizationTree.order], fun k _ hl => ⟨k0, Finset.mem_singleton_self _, ?_⟩⟩
    intro p hp
    simp only [LocalizationTree.nodes, Finset.mem_singleton] at hp
    subst hp
    exact hl [] (by simp [LocalizationTree.leaves])
  | node l m r ihl ihm ihr =>
    classical
    intro k0
    obtain ⟨S₀, hS₀, H₀⟩ := ihl (fun p => k0 (0 :: p))
    obtain ⟨S₁, hS₁, H₁⟩ := ihm (fun p => k0 (1 :: p))
    obtain ⟨S₂, hS₂, H₂⟩ := ihr (fun p => k0 (2 :: p))
    let mk : (Path → Mom d) × (Path → Mom d) × (Path → Mom d) × Mom d → (Path → Mom d) :=
      fun x => combine (x.1 [] - x.2.1 [] + x.2.2.1 [] + x.2.2.2) ![x.1, x.2.1, x.2.2.1]
    refine ⟨(S₀ ×ˢ S₁ ×ˢ S₂ ×ˢ F).image mk, ?_, ?_⟩
    · refine Finset.card_image_le.trans ?_
      simp only [Finset.card_product, LocalizationTree.order]
      calc S₀.card * (S₁.card * (S₂.card * F.card))
          ≤ F.card ^ l.order * (F.card ^ m.order * (F.card ^ r.order * F.card)) := by gcongr
        _ = F.card ^ (l.order + m.order + r.order + 1) := by ring
    · intro k hk hl
      obtain ⟨h0, d₀, d₁, d₂⟩ := treeDec_child hk
      obtain ⟨c₀, hc₀, e₀⟩ := H₀ _ d₀ (leaves_child hl 0)
      obtain ⟨c₁, hc₁, e₁⟩ := H₁ _ d₁ (leaves_child hl 1)
      obtain ⟨c₂, hc₂, e₂⟩ := H₂ _ d₂ (leaves_child hl 2)
      have r₀ := e₀ [] (by cases l <;> simp [LocalizationTree.nodes])
      have r₁ := e₁ [] (by cases m <;> simp [LocalizationTree.nodes])
      have r₂ := e₂ [] (by cases r <;> simp [LocalizationTree.nodes])
      have hroot : ‖k [] - (c₀ [] - c₁ [] + c₂ [])‖ ≤ 3 := by
        rw [h0]
        calc ‖k [0] - k [1] + k [2] - (c₀ [] - c₁ [] + c₂ [])‖
            = ‖(k [0] - c₀ []) - (k [1] - c₁ []) + (k [2] - c₂ [])‖ := by congr 1; abel
          _ ≤ ‖k [0] - c₀ []‖ + ‖k [1] - c₁ []‖ + ‖k [2] - c₂ []‖ :=
            (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
          _ ≤ 1 + 1 + 1 := by gcongr
          _ = 3 := by norm_num
      obtain ⟨q, hq, hkq⟩ := hF _ _ hroot
      refine ⟨mk (c₀, c₁, c₂, q), Finset.mem_image_of_mem _ (Finset.mem_product.2 ⟨hc₀,
        Finset.mem_product.2 ⟨hc₁, Finset.mem_product.2 ⟨hc₂, hq⟩⟩⟩), ?_⟩
      intro p hp
      rcases mem_nodes_node hp with rfl | ⟨i, q', rfl, hq'⟩
      · simpa [mk, combine, add_assoc] using hkq
      · fin_cases i
        · exact e₀ q' hq'
        · exact e₁ q' hq'
        · exact e₂ q' hq'


end WaveTurbulence.Incoh.LocalizationTree
