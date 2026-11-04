/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleLinkCoordinates

/-! # Exact source layer counts and bounds for the actual couple link family -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links

variable {LG : LayeredGarden 2} {Q : RegCpl}

/-- The analytic incoherence count is precisely B2's decoded source incoherence count. -/
theorem coupleLayerLinks_incoherenceCount (d : ℕ) (hQ : Q.Decodes LG.garden) :
    incoherenceCount (coupleLayerLinks (d := d) LG hQ) = LG.incoherency Q.links := by
  unfold incoherenceCount LayeredGarden.incoherency
  apply Finset.card_bij (fun j _ => (coupleLinkBranch hQ j 0, coupleLinkBranch hQ j 1))
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    refine ⟨?_, ?_⟩
    · exact List.get_mem Q.links j
    · change (LG.layer (coupleLinkBranch hQ j 0).toNode : ℤ) ≠
        LG.layer (coupleLinkBranch hQ j 1).toNode at hj
      exact_mod_cast hj
  · intro i _ j _ he
    have he' := congrArg (fun p => (p.1.1, p.2.1)) he
    exact (nodup_of_flat_nodup (couple_links_flat_nodup Q)).get_inj_iff.mp he'
  · intro bb hbb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbb
    obtain ⟨j, hj⟩ := List.get_of_mem hbb.1
    have he : (coupleLinkBranch hQ j 0, coupleLinkBranch hQ j 1) = bb := by
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst hj)
      · exact Subtype.ext (congrArg Prod.snd hj)
    refine ⟨j, ?_, he⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (LG.layer (coupleLinkBranch hQ j 0).toNode : ℤ) ≠ LG.layer (coupleLinkBranch hQ j 1).toNode
    rw [show coupleLinkBranch hQ j 0 = bb.1 from congrArg Prod.fst he,
      show coupleLinkBranch hQ j 1 = bb.2 from congrArg Prod.snd he]
    exact_mod_cast hbb.2

/-- The total source layer bound supplies the analytic layer-span bound. -/
theorem coupleLayerLinks_span (d : ℕ) (hQ : Q.Decodes LG.garden) {p : ℕ}
    (hp : ∀ a, LG.layer a ≤ p) (j : Fin Q.links.length) :
    |(((coupleLayerLinks (d := d) LG hQ j).leftLayer : ℝ)) -
      (coupleLayerLinks (d := d) LG hQ j).rightLayer| + 1 ≤ (p : ℝ) + 1 := by
  have h0 := hp (coupleLinkBranch hQ j 0).toNode
  have h1 := hp (coupleLinkBranch hQ j 1).toNode
  change |((LG.layer (coupleLinkBranch hQ j 0).toNode : ℤ) : ℝ) -
    ((LG.layer (coupleLinkBranch hQ j 1).toNode : ℤ) : ℝ)| + 1 ≤ _
  push_cast
  have ha : (0 : ℝ) ≤ LG.layer (coupleLinkBranch hQ j 0).toNode := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ LG.layer (coupleLinkBranch hQ j 1).toNode := Nat.cast_nonneg _
  have h0' : (LG.layer (coupleLinkBranch hQ j 0).toNode : ℝ) ≤ p := by exact_mod_cast h0
  have h1' : (LG.layer (coupleLinkBranch hQ j 1).toNode : ℝ) ≤ p := by exact_mod_cast h1
  have hab : |(LG.layer (coupleLinkBranch hQ j 0).toNode : ℝ) -
      LG.layer (coupleLinkBranch hQ j 1).toNode| ≤ p := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith only [hab]

end WaveTurbulence.IncohInst
