/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Top.StarDecay

/-! # INC-TOP: star-weighted Proposition 5.1 for every decoded incoherent regular couple

The weighted copy of main's `IncohLeafwise.exists_KQstar_decayL` (Spine/IncohLeafwise/AllCoupleDecay.lean): the
root-shape dispatch (two branching roots; exactly one branching root; no branching root is impossible at incoherency
`≥ 1`) over C2-B-TOP's ported star decays `exists_KQstarStar_twoRoot_decay` / `exists_KQstarStar_oneRoot_decay`.

Source: supplement Lemma 4.1 (couple half; T981–1017, the Sobolev step T999 is the one in the ported rate). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.IncohInst WaveTurbulence.Incoh WaveTurbulence.Links
open WaveTurbulence.LGSpine WaveTurbulence.IncohLeafwise

/-- **Star-weighted couple decay** (weighted `exists_KQstar_decayL`). -/
theorem exists_KQstarStar_decay (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ,
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ p : ℕ, p ≤ D →
        ∀ Q : RegCpl, ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
        LG.layer (GNode.root LG.garden.tree 0) ≤ q →
        LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
        1 ≤ LG.incoherency Q.links → ∀ H : LeafProfiles 2 d,
        (∀ ℓ ∈ inputLeaves LG.garden,
          Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H ℓ.1 k : ℂ)) ≤ ENNReal.ofReal B) →
        ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
          (c : GNode LG.garden.tree → ℝ), (∀ a ∈ S, StarPresented (30 * d) (ω a) (c a)) →
        Fourier.mixedRestrictionNorm η (30 * d) (30 * d) (timeBox q q') univ
          (fun (ts : timeBox q q') (k : (univ : Set (Mom d))) =>
            coupleLeavesStar L γ δ LG S ω H (ts.1 0) (ts.1 1) k.1) ≤
            ENNReal.ofReal (rootJetConstant (30 * d)) * (∏ a ∈ S, ENNReal.ofReal (c a)) *
            ENNReal.ofReal ((C * δ) ^ Q.links.length *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links)) := by
  obtain ⟨Ctwo, hCtwo, htwo⟩ := exists_KQstarStar_twoRoot_decay d hd B hB
  obtain ⟨Cone, hCone, hone⟩ := exists_KQstarStar_oneRoot_decay d hd B hB
  refine ⟨max Ctwo Cone, hCtwo.trans_le (le_max_left _ _), ?_⟩
  intro η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  obtain ⟨Lt, hLt, htwo⟩ := htwo η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  obtain ⟨Lo, hLo, hone⟩ := hone η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  refine ⟨max Lt Lo, hLt.trans (le_max_left _ _), ?_⟩
  intro L hL p hpD Q LG hQ hlayers q q' hq hq' hrootq hrootq' hg H hH S ω c hω
  have hLone : 1 ≤ L := hLt.trans ((le_max_left Lt Lo).trans hL)
  have hpos : 0 ≤ L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links) :=
    Real.rpow_nonneg (zero_le_one.trans hLone) _
  have ht (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching) :=
    (htwo L ((le_max_left Lt Lo).trans hL) p hpD Q LG hQ hb hlayers q q' hq hq'
      hrootq hrootq' hg H hH S ω c hω).trans
      (mul_le_mul_right (sourceRate_mono_constant hCtwo.le (le_max_left Ctwo Cone) hδ.le hpos
        Q.links.length) _)
  have ho (a : Fin 2) (hb : ([] : TTree.Path) ∈ (LG.garden.tree a).branching)
      (hw : ∀ b : GBranch LG.garden.tree, b.1.1 = a) :=
    (hone L ((le_max_right Lt Lo).trans hL) p hpD Q LG hQ a hb hw hlayers q q' hq hq'
      hrootq hrootq' hg H hH S ω c hω).trans
      (mul_le_mul_right (sourceRate_mono_constant hCone.le (le_max_right Ctwo Cone) hδ.le hpos
        Q.links.length) _)
  by_cases h0 : ([] : TTree.Path) ∈ (LG.garden.tree 0).branching
  · by_cases h1 : ([] : TTree.Path) ∈ (LG.garden.tree 1).branching
    · exact ht (fun i => by fin_cases i <;> assumption)
    · apply ho 0 h0
      apply branch_index_eq_of_other_leaf
      intro i hi
      have he : i = 1 := by omega
      subst i
      exact tree_eq_leaf_of_root_not_branching h1
  · by_cases h1 : ([] : TTree.Path) ∈ (LG.garden.tree 1).branching
    · apply ho 1 h1
      apply branch_index_eq_of_other_leaf
      intro i hi
      have he : i = 0 := by omega
      subst i
      exact tree_eq_leaf_of_root_not_branching h0
    · have hn := one_le_linkCount_of_incoherent (coupleLayerLinks (d := d) LG hQ)
        ((coupleLayerLinks_incoherenceCount d hQ).symm ▸ hg)
      let b := chosenBranch hQ (⟨0, by omega⟩ : Fin Q.links.length)
      have hr := root_mem_branching_of_mem b.2
      by_cases hb : b.1.1 = 0
      · rw [hb] at hr
        exact False.elim (h0 hr)
      · have hb1 : b.1.1 = 1 := by omega
        rw [hb1] at hr
        exact False.elim (h1 hr)

end WaveTurbulence.Flower.IncTop
