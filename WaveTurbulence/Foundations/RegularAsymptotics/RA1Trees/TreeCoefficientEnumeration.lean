/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeTimeExpansion
public import WaveTurbulence.Foundations.IncohInst.Links.Coherence
public import WaveTurbulence.Foundations.RegAsymp.TreeMarkedEnumeration

/-! # Actual tree link indices enumerate the source coefficient variables -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links ClassJR MainCoef Reg

/-- The chosen endpoint of the actual source tree link, placed in ClassJR's sign root. -/
def treeChosenAddress (X : RegChain) (ζ : ℤˣ) (j : Fin (X.treeLinks ζ).length) : ClassJR.Addr :=
  ((rootT ζ).1, ((X.treeLinks ζ).get j).1.2)

/-- No chosen source address is repeated; this follows from C2's endpoint partition. -/
theorem treeChosenAddress_injective (X : RegChain) (ζ : ℤˣ) :
    Function.Injective (treeChosenAddress X ζ) := by
  intro i j he
  have hp : ((X.treeLinks ζ).get i).1 = ((X.treeLinks ζ).get j).1 :=
    Prod.ext (Subsingleton.elim _ _) (congrArg (fun v : ClassJR.Addr => v.2) he)
  have hpair := eq_of_flat_nodup (tree_links_flat_nodup X ζ)
    (List.get_mem (X.treeLinks ζ) i) (List.get_mem (X.treeLinks ζ) j)
    (Or.inl rfl) (Or.inl hp)
  exact (nodup_of_flat_nodup (tree_links_flat_nodup X ζ)).get_inj_iff.mp hpair

/-- The independent tree links enumerate exactly the chosen ClassJR address set. -/
theorem range_treeChosenAddress (X : RegChain) (ζ : ℤˣ) :
    Set.range (treeChosenAddress X ζ) =
      (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)) : Set ClassJR.Addr) := by
  rw [linksAt_rootT]
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨_, List.mem_map.mpr ⟨(X.treeLinks ζ).get j, List.get_mem _ _, rfl⟩, rfl⟩
  · intro hv
    obtain ⟨l, hl, hv⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
    obtain ⟨j, rfl⟩ := List.get_of_mem hl'
    exact ⟨j, hv⟩

/-- The exact actual tree coefficient has the original SRep budget on unmarked link indices. -/
theorem tree_sourceCoefficient_on_unmarkedLinks {X : RegChain} {ζ : ℤˣ}
    {Z : Finset ClassJR.Addr} {θ a b A N : ℝ}
    {F : (ClassJR.Addr → ℝ) → ℝ → ℝ → ℂ}
    (hF : MCRep θ a b A N
      (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)) \ Z : Finset ClassJR.Addr) F) :
    ∃ C : ({j : Fin (X.treeLinks ζ).length // j ∉ treeMarkedIndices (treeChosenAddress X ζ) Z} → ℝ) →
        ℝ × ℝ → ℂ,
      SRep θ a b A N C ∧
      ∀ α t s, t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
        F α t s = ∫ lam, C (fun j => α (treeChosenAddress X ζ j)) lam * e2 lam t s :=
  treeCoefficient_on_unmarked hF _ (treeChosenAddress_injective X ζ) (range_treeChosenAddress X ζ)

end WaveTurbulence.RegAsymp
