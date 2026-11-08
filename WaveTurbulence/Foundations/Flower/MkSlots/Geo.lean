/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.Data
public import WaveTurbulence.Foundations.Flower.ProtGeo.Vine

/-! # B3s MK-SLOTS: pins never sit in a spliced unit

A pinned branch is a seed of the protected set `Π`, so its closed neighbourhood is protected. Hence a vine of `𝒱`
one of whose atoms carries a pinned vertex is marked (`marked_of_fix_atom`: a non-upper atom through its own region,
the upper joint through its child toward the vine, D2b's `upper_internal_child`). The units of the piece of a
prescribed point `a` are made of vines of `𝒱₀(σ)` outside `classMk mkF a`; with `markI ⊆ mkF` (`FineMarking.sub`) no
unit atom carries a pin (`fixCap_coreBranch_unit`). This holds for every pattern and every selection. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg.Skeleton WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.ProtGeo
open WaveTurbulence.Flower.Stage1MKGate WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice (Prescription stSt vinesV0 unitBlocks)

namespace WaveTurbulence.Flower.MkSlots

variable {w : ℕ} {LG : LayeredGarden w} {J : Finset (Fin w)}

theorem fixChild_mem_protI (pat : Fin w → FixPat) (t s : ℝ) {kSel : Fin w → Option ℕ}
    {v : GBranch LG.garden.tree} (hv : (fixCap LG J pat t s v).isSome) (i : Fin 3) :
    v.child i ∈ protI LG J pat t s kSel := by
  unfold protI protectedSet
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.toNode, ⟨rfl, Or.inr (Or.inr ⟨by simp [GBranch.child], ?_⟩)⟩,
    Or.inr ⟨v, rfl, Or.inl hv⟩⟩
  simp [GBranch.child, GBranch.toNode]

/-- **A vine of `𝒱` with a pinned atom is marked.** -/
theorem marked_of_fix_atom (A : VineA.PrimeData LG) (pat : Fin w → FixPat) (t s : ℝ)
    (kSel : Fin w → Option ℕ) (c : Stage1.CLVine A.skeleton) (hc : c ∈ Stage1.vinesV A.skeleton)
    (y : GBranch A.skeleton.tree) (hy : y ∈ c.atoms) {v : GBranch LG.garden.tree}
    (hv : (fixCap LG J pat t s v).isSome) (hvy : v.1 = skelAddr A.skeleton A.data.tree y) :
    c ∈ markI J pat t s kSel A := by
  by_cases hup : y = c.upper
  · subst hup
    obtain ⟨i, b, hb, hbne, hbi⟩ := upper_internal_child c
    have hpos : (v.child i).1 = inflatedPosition A.skeleton A.data.tree (c.upper.child i) := by
      rw [inflatedPosition_child]
      show (v.1.1, v.1.2 ++ [i]) = _
      rw [hvy]; simp [skelAddr, addrExt, List.append_assoc]
    refine ⟨hc, b, hb, hbne, v.child i, fixChild_mem_protI pat t s hv i, ?_⟩
    rw [hpos]
    rcases hbi with hbi | ⟨ℓ, hℓ, hbp⟩
    · apply mem_nearRegion_own
      rw [hbi]; exact inflatedPosition_mem_ownRegion _ _ _
    · apply mem_nearRegion_partner hbp
      rw [A.skeleton.pair_pair, hℓ]
      exact inflatedPosition_mem_ownRegion _ _ _
  · refine ⟨hc, y, hy, hup, v.toNode, mem_protI_of_fixCap hv, mem_nearRegion_own ?_⟩
    show v.1 ∈ _
    rw [hvy]
    exact skelAddr_mem_ownRegion _ _ y

/-- **No atom of a unit of the piece carries a pin.** `a` is a prescribed point, `mkF` a fine marking containing
`markI`; the units are those of `unitBlocks` at the marked set `classMk mkF a`. -/
theorem fixCap_coreBranch_unit (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (mkF : Stage1Mk.MarkFn w) (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden w) {u : RedSplice.CLBlock a.prime.skeleton}
    (hu : u ∈ unitBlocks a.prime.skeleton a.totalSigma (classMk mkF a)) {y : GBranch a.prime.skeleton.tree}
    (hy : y ∈ u.atoms) :
    fixCap a.layered J pat t s (a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes y) = none := by
  obtain ⟨c, hc, hyc, -⟩ := RedSplice.unitBlocks_soundMk hu y hy
  rw [RedSplice.mem_vinesV0] at hc
  obtain ⟨hc0, hcMk⟩ := hc
  by_contra hpin
  have hpin' := Option.ne_none_iff_isSome.1 hpin
  have hm : c ∈ markI J pat t s kSel a.prime :=
    marked_of_fix_atom a.prime pat t s kSel c (RedSplice.vinesV0_subset _ _ hc0) y hyc hpin' rfl
  exact hcMk ⟨hsub a.prime hm, hc0⟩

end WaveTurbulence.Flower.MkSlots
