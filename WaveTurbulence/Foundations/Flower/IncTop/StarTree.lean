/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Top.StarDecay

/-! # INC-TOP: star-weighted Proposition 5.1 for decoded incoherent regular trees

The weighted copy of main's `IncohLeafwise.exists_KTstar_decayL` (Spine/IncohLeafwise/TreeDecay.lean): the
star-weighted leafwise tree kernel is C2-B-REG's weighted raw tree operator with the root-modulated internal measure
of the star weights (`treeLeavesW_eq_weightedRaw_of_summable`, `tree_starWeight_eq_value`), bounded by
`exists_rootRawTreeKernel_rate`.  The presentation cost is `rootJetConstant (30d) * ∏_{a ∈ S} c a`.

Source: supplement Lemma 4.1 (tree half, with the referee's fix: T1062–T1092's uniform-in-`k` argument; the inserted
factors enter as `k`-dependent modulation parameters and a unimodular root character, which is exactly the
`RootMeasure` form consumed by `exists_rootRawTreeKernel_rate`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.IncohInst WaveTurbulence.Incoh WaveTurbulence.Links
open WaveTurbulence.LGSpine WaveTurbulence.IncohLeafwise

/-- **Star-weighted tree decay** (weighted `exists_KTstar_decayL`). -/
theorem exists_KTstarStar_decay (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ,
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ p : ℕ, p ≤ D →
        ∀ X : RegChain, ∀ LG : LayeredGarden 1, X.DecodesTree LG.garden →
        (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
        1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) → ∀ H : LeafProfiles 1 d,
        (∀ ℓ ∈ inputLeaves LG.garden,
          Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H ℓ.1 k : ℂ)) ≤ ENNReal.ofReal B) →
        ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
          (c : GNode LG.garden.tree → ℝ), (∀ a ∈ S, StarPresented (30 * d) (ω a) (c a)) →
        Fourier.mixedRestrictionNorm η (30 * d) 0 (timeBoxGt q q') univ
          (fun (ts : timeBoxGt q q') (k : (univ : Set (Mom d))) =>
            treeLeavesStar L γ δ LG S ω H (ts.1 0) (ts.1 1) k.1) ≤
            ENNReal.ofReal (rootJetConstant (30 * d)) * (∏ a ∈ S, ENNReal.ofReal (c a)) *
            ENNReal.ofReal ((C * δ) ^ (X.treeLinks (LG.garden.sig 0)).length *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) *
                LG.incoherency (X.treeLinks (LG.garden.sig 0)))) := by
  obtain ⟨C, hC, hb⟩ := exists_rootRawTreeKernel_rate d hd B hB
  refine ⟨C, hC, ?_⟩
  intro η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  choose L₀ hL₀ hb using fun l : Fin 3 => hb l (by omega) η hη hη₁ hsmall
    (finiteLayerCutoff D) (contDiff_finiteLayerCutoff D) (hasCompactSupport_finiteLayerCutoff D)
    γ hγ hηγ δ hδ hδ₁ ((D : ℝ) + 1) (by positivity)
  let Lstar := max (L₀ 0) (max (L₀ 1) (L₀ 2))
  have hmax (l : Fin 3) : L₀ l ≤ Lstar := by
    fin_cases l
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Lstar, (hL₀ 0).trans (hmax 0), ?_⟩
  intro L hL p hpD X LG hX hlayers q q' hq hq' hg H hH S ω c hω
  have hcount := treeLayerLinks_incoherenceCount d hX
  have hg' : 1 ≤ incoherenceCount (treeLayerLinks (d := d) LG hX) := hcount ▸ hg
  have hn := one_le_linkCount_of_incoherent (treeLayerLinks (d := d) LG hX) hg'
  have hnontriv : X ≠ .nil := by
    intro he
    subst X
    simp [RegChain.treeLinks, RegChain.linksAt] at hn
  let Csel := actualTreeSelection hX hnontriv
  have hmsel : Csel.m ≤ 2 := by rcases Csel.m_cases with h | h <;> omega
  let l : Fin 3 := ⟨Csel.m, by omega⟩
  have hLa := (hmax l).trans hL
  have hLone := (hL₀ l).trans hLa
  have hm : Fintype.card (TPlus LG.garden) + 1 ≤ 3 * (X.treeLinks (LG.garden.sig 0)).length := by
    rw [tree_input_count hX]
    omega
  have hspan (j) : |(((treeLayerLinks (d := d) LG hX j).leftLayer : ℝ)) -
      (treeLayerLinks (d := d) LG hX j).rightLayer| + 1 ≤ (D : ℝ) + 1 :=
    (treeLayerLinks_span d hX hlayers j).trans (by exact_mod_cast Nat.add_le_add_right hpD 1)
  let G := starRootMeasure (30 * d) S ω c hω (treeRow hX)
  have hraw := hb l L hLa (X.treeLinks (LG.garden.sig 0)).length (Fintype.card (TPlus LG.garden)) 1 hm
    (treeCarrier hX) (treeLayerLinks LG hX) hspan hg' Csel.rootCoordinates
    (actualTreeFibers LG hX Csel) Csel.rootCoordinates_first Csel.rootCoordinates_last
    (finiteLayerCutoff_one_on_tree_clocks D LG hX (fun a => (hlayers a).trans hpD) Csel.rootCoordinates)
    (finiteLayerCutoff_one_on_tree_clocks D LG hX (fun a => (hlayers a).trans hpD)
      Csel.selection.coordinates)
    (treeInputFunctionsL LG H) (fun a => treeInputFunctions_spatialNorm_leL hX H hH a)
    (timeBoxGt q q') (fun _ ht => ht.2.le)
    (finiteLayerCutoff_one_on_timeBoxGt D q q' (hq.trans hpD) (hq'.trans hpD))
    (gardenCircle LG.garden) univ G
  rw [hcount] at hraw
  have heq : (fun (ts : timeBoxGt q q') (k : (univ : Set (Mom d))) =>
      treeLeavesStar L γ δ LG S ω H (ts.1 0) (ts.1 1) k.1) =
      fun ts k => MomentumTreeData.weightedSourceTreeKernel (treeCarrier hX) (G.at k.1)
        (gardenCircle LG.garden) Csel.rootCoordinates L γ δ (treeLayerLinks LG hX)
        (actualTreeFibers (d := d) LG hX Csel).timeDomain (treeInputFunctionsL LG H) ts.1 k.1 := by
    funext ts k
    exact treeLeavesW_eq_weightedRaw_of_summable hX Csel L γ δ H k.1 ts.1 (starWeight S ω) (G.at k.1)
      (tree_starWeight_eq_value hX (30 * d) S ω c hω L k.1)
      ((treeCarrier hX).summable_norm_treeSourceLeafWeight_lattice (by omega)
        (treeInputFunctionsL LG H) hLone (by omega) (by omega)
        (fun a => treeInputFunctions_spatialNorm_leL hX H hH a) k.1)
  rw [heq]
  refine hraw.trans ?_
  gcongr
  exact starRootMeasure_momentMass_le (30 * d) S ω c hω (treeRow hX)

end WaveTurbulence.Flower.IncTop
