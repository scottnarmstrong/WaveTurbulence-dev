/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtWhole.CapRed
public import WaveTurbulence.Foundations.Flower.ProtGeo.Couple
public import WaveTurbulence.Foundations.Molecule.GardenMoleculeDefs
public import WaveTurbulence.Foundations.RegStruct.SourceRegularDecoding

/-! # D6b: a wholly regular capped component of width 2 is a cap couple (`CapG`)

From the carrier of `RegularComponentBoundAtI` (cap tree `c` a leaf, `IsRegularCouple`, order `≥ 1`): D2b's
`embeds_stem_cap` applied to the whole couple (main's `isRegularCouple_exists_wf_decodes`, `Embeds.of_decodes`) gives
the big tree `j0 ≠ c`, its chain `X`, its root sign `ζ = sig j0`, the cap chain (`CapChain`), hence `CapG`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset

namespace WaveTurbulence.Flower.ProtWhole

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.MkDefs

theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

theorem eq_leaf_of_nil_mem_leaves {t : TTree} (h : ([] : Path) ∈ t.leaves) : t = .leaf := by
  cases t with
  | leaf => rfl
  | node l m r => simp [TTree.leaves, TTree.pre, Finset.mem_image] at h

/-- **Extraction.** A width-2 regular couple of order `≥ 1` with a leaf cap tree `c` is a cap couple. -/
theorem exists_capChain {LG : LayeredGarden 2} {c : Fin 2} (hcap : LG.garden.tree c = .leaf)
    (hreg : IsRegularCouple LG.garden) (hord : 1 ≤ LG.garden.order) :
    ∃ (j0 : Fin 2) (X : RegChain) (ζ : ℤˣ), j0 ≠ c ∧ CapChain LG {c} X ζ (j0, []) c ∧
      LG.garden.sig j0 = ζ ∧ LG.garden.IsPlain ∧
      ∃ Q : RegCpl, Q.wf = true ∧ Q.Decodes LG.garden ∧ Q.links = X.linksAt ζ (j0, []) ∧ Q.size = X.size := by
  obtain ⟨Q, hwf, hQ⟩ := isRegularCouple_exists_wf_decodes _ hreg
  have hE : Embeds LG.garden Q (0, []) (1, []) := Embeds.of_decodes hQ
  have hcapJ : ∀ j ∈ ({c} : Finset (Fin 2)), LG.garden.tree j = TTree.leaf := by
    intro j hj
    rw [Finset.mem_singleton.1 hj]
    exact hcap
  have hplain : LG.garden.IsPlain := hQ.1.1
  have hsig : LG.garden.sig = ![1, -1] := hQ.1.2
  let ℓc : GLeaf LG.garden.tree := ⟨(c, []), by rw [hcap]; simp [TTree.leaves]⟩
  let f : GLeaf LG.garden.tree := LG.garden.pair ℓc
  have hfne : f ≠ ℓc := fun h => ((LG.garden.pair_eq_iff ℓc).1 h) (hplain ℓc)
  have hf1 : f.1.1 ≠ c := by
    intro h
    apply hfne
    have h2 : f.1.2 ∈ (LG.garden.tree f.1.1).leaves := f.2
    rw [h, hcap] at h2
    simp [TTree.leaves] at h2
    exact Subtype.ext (Prod.ext h h2)
  have hff : IsCapFlower LG {c} f := by
    refine ⟨by simpa using hf1, ?_⟩
    show (LG.garden.pair (LG.garden.pair ℓc)).1.1 ∈ ({c} : Finset (Fin 2))
    rw [LG.garden.pair_pair]
    simp [ℓc]
  have hfnil : f.1.2 ≠ [] := by
    intro h
    have h2 : f.1.2 ∈ (LG.garden.tree f.1.1).leaves := f.2
    rw [h] at h2
    have hl := eq_leaf_of_nil_mem_leaves h2
    have ho : LG.garden.order = 0 := by
      unfold Garden.order
      rw [fin2_sum _ f.1.1 c hf1, hl, hcap]
      rfl
    omega
  have hq : f.1.2.dropLast ∈ (LG.garden.tree f.1.1).branching :=
    TTree.dropLast_mem_branching (TTree.leaves_subset_nodes _ f.2) hfnil
  let v : GBranch LG.garden.tree := ⟨(f.1.1, f.1.2.dropLast), hq⟩
  have hvs : OnCapStem LG {c} v.toNode := ⟨f, hff, rfl, List.dropLast_prefix _⟩
  have hm : MeetsStem LG {c} (branchAddresses Q.trees.1 (0, []) ∪ branchAddresses Q.trees.2 (1, [])) := by
    refine ⟨v, ?_, hvs⟩
    rw [Finset.mem_union, mem_branchAddresses', mem_branchAddresses']
    rcases fin2_cases f.1.1 with h0 | h0
    · left
      refine ⟨f.1.2.dropLast, ?_, ?_⟩
      · rw [← hQ.2.1, ← h0]; exact hq
      · show (f.1.1, f.1.2.dropLast) = ((0 : Fin 2), [] ++ f.1.2.dropLast)
        rw [h0, List.nil_append]
    · right
      refine ⟨f.1.2.dropLast, ?_, ?_⟩
      · rw [← hQ.2.2.1, ← h0]; exact hq
      · show (f.1.1, f.1.2.dropLast) = ((1 : Fin 2), [] ++ f.1.2.dropLast)
        rw [h0, List.nil_append]
  obtain ⟨X, c', hcase | hcase⟩ := embeds_stem_cap hcapJ hwf hE hm
  · obtain ⟨hQX, hb, hC⟩ := hcase
    have hc' : c' = 1 := (congrArg Prod.fst hb).symm
    have hcc : c = c' := (Finset.mem_singleton.1 hC.cap).symm
    refine ⟨0, X, 1, ?_, ?_, ?_, hplain, Q, hwf, hQ, ?_, ?_⟩
    · rw [hcc, hc']; decide
    · exact hcc ▸ hC
    · rw [hsig]; rfl
    · rw [hQX]; simp [RegCpl.links, RegCpl.linksAt, RegChain.linksAt]
    · rw [hQX]; simp [RegCpl.size, RegChain.size]
  · obtain ⟨hQX, ha, hC⟩ := hcase
    have hc' : c' = 0 := (congrArg Prod.fst ha).symm
    have hcc : c = c' := (Finset.mem_singleton.1 hC.cap).symm
    refine ⟨1, X, -1, ?_, ?_, ?_, hplain, Q, hwf, hQ, ?_, ?_⟩
    · rw [hcc, hc']; decide
    · exact hcc ▸ hC
    · rw [hsig]; rfl
    · rw [hQX]; simp [RegCpl.links, RegCpl.linksAt, RegChain.linksAt]
    · rw [hQX]; simp [RegCpl.size, RegChain.size]

/-- The general cap data of an extracted cap chain. -/
theorem capG_of_capChain {LG : LayeredGarden 2} {c j0 : Fin 2} {X : RegChain} {ζ : ℤˣ} (hne : j0 ≠ c)
    (hcap : LG.garden.tree c = .leaf) (hC : CapChain LG {c} X ζ (j0, []) c) (hsig : LG.garden.sig j0 = ζ)
    (hplain : LG.garden.IsPlain) : CapG LG j0 c X ζ :=
  ⟨hne, hC.stem.emb, hcap, hsig, fun ℓ h => hC.pair ℓ (by rw [h]; simp [addrExt]), hplain⟩

end WaveTurbulence.Flower.ProtWhole
