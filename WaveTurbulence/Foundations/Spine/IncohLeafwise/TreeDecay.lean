/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.IncohLeafwise.TreeExternalBox
public import WaveTurbulence.Foundations.IncohInst.NormBridge
public import WaveTurbulence.Foundations.Incoh.TreeUpperPropositionRate

/-! # B2.2 for every actual decoded incoherent regular tree -/

public section
noncomputable section
open scoped ENNReal Classical
open MeasureTheory Set
namespace WaveTurbulence.IncohLeafwise
open WaveTurbulence.IncohInst Incoh Links
open WaveTurbulence.LGSpine

/-- All actual tree carriers, clock fibers and kernel identities are discharged here. -/
theorem exists_KTstar_decayL (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ,
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ p : ℕ, p ≤ D →
        ∀ X : RegChain, ∀ LG : LayeredGarden 1, X.DecodesTree LG.garden →
        (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
        1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) → ∀ H : LeafProfiles 1 d,
        (∀ ℓ ∈ inputLeaves LG.garden, Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H ℓ.1 k : ℂ)) ≤ ENNReal.ofReal B) →
        Fourier.mixedRestrictionNorm η (30 * d) 0 (timeBoxGt q q') univ
          (fun (ts : timeBoxGt q q') (k : (univ : Set (Mom d))) =>
            treeLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1) ≤
            ENNReal.ofReal ((C * δ) ^ (X.treeLinks (LG.garden.sig 0)).length *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) *
                LG.incoherency (X.treeLinks (LG.garden.sig 0)))) := by
  obtain ⟨C, hC, hb⟩ := exists_rawTreeKernel_upperPropositionRate d hd B hB
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
  intro L hL p hpD X LG hX hlayers q q' hq hq' hg H hH
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
  have hraw := hb l L hLa (X.treeLinks (LG.garden.sig 0)).length (Fintype.card (TPlus LG.garden)) 1 hm
    (treeCarrier hX) (treeLayerLinks LG hX) hspan hg' Csel.rootCoordinates
    (actualTreeFibers LG hX Csel) Csel.rootCoordinates_first Csel.rootCoordinates_last
    (finiteLayerCutoff_one_on_tree_clocks D LG hX (fun a => (hlayers a).trans hpD) Csel.rootCoordinates)
    (finiteLayerCutoff_one_on_tree_clocks D LG hX (fun a => (hlayers a).trans hpD) Csel.selection.coordinates) (treeInputFunctionsL LG H)
    (fun a => treeInputFunctions_spatialNorm_leL hX H hH a)
    (timeBoxGt q q') (fun _ ht => ht.2.le)
    (finiteLayerCutoff_one_on_timeBoxGt D q q' (hq.trans hpD) (hq'.trans hpD))
    (gardenCircle LG.garden) univ
  rw [hcount] at hraw
  convert hraw using 1
  congr 1
  funext ts k
  exact treeLeaves_eq_rawL hX Csel (by omega) L γ δ hLone H hlayers hH k.1 ts.1

end WaveTurbulence.IncohLeafwise
