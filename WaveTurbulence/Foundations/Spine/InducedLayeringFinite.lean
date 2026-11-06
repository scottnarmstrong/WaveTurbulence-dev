/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.LayerReg2
/-! Finiteness of the exact induced-layering carrier, extracted from C4's proved injection. -/
public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Links WaveTurbulence.Reg
open TTree

theorem finite_inducedLayerings {w : ℕ} (Q : RegCpl) (hwf : Q.wf = true)
    (a b : Fin w × Path) (p q q' g : ℕ) : (inducedLayerings p Q a b q q' g).Finite := by
  set B := pairEndpoints (Q.linksAt a b)
  set T := ldist q q' + 9 * p * g
  have hmap : ∀ f ∈ inducedLayerings p Q a b q q' g, dropF B a b q q' f ∈ boundedVecs B T := by
    rintro f ⟨LG, hcan, hplain, hE, ha, hb, hg, hfz⟩
    obtain ⟨W1, W2⟩ := witness_facts hE ha hb hfz
    refine ⟨fun z hz => by unfold dropF; rw [ite_neg_of hz], ?_⟩
    have hbud := cpl_budget hcan hplain Q a b hwf hE
    rw [ha, hb, hg] at hbud
    calc ∑ z ∈ B, dropF B a b q q' f z = budget LG p B :=
          Finset.sum_congr rfl fun z hz => by
            unfold dropF dropAt
            rw [ite_pos_of hz, W2 z (links_sub_nodes hz), W1 z (links_sub_nodes hz)]
      _ ≤ T := hbud
  have hinj : Set.InjOn (dropF B a b q q' ·) (inducedLayerings p Q a b q q' g) :=
    fun f hf f' hf' hd => layering_determined hf hf' hd
  exact Set.Finite.of_injOn hmap hinj (boundedVecs_spec B T).1

end WaveTurbulence.LGSpine
