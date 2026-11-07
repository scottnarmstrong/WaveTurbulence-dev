/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitTransport
/-! Coverage by disjoint units respects the overlapping ingredients of a
spine. A skipped ingredient cannot itself belong to the selected carrier. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- An ingredient spine covered by pairwise disjoint units lies in a single unit. -/
theorem spine_cover_one_unit {D : Type*} [Fintype D] [DecidableEq D]
    {N : Molecule (GBranch G.tree) D} {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (us : List (CLBlock G)) (hd : us.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    (hs : Spine N L S a b)
    (hc : ∀ t ∈ L, ∃ u ∈ us, t.1 ⊆ u.atoms) : ∃ u ∈ us, S ⊆ u.atoms := by
  induction hs with
  | @one T a b hv => exact hc (T, a, b) (List.mem_singleton_self _)
  | @snoc L U T a b c hs hv hi hne ih =>
    obtain ⟨u, hu, hU⟩ := ih (fun t ht => hc t (List.mem_append_left _ ht))
    obtain ⟨v, hvm, hT⟩ := hc (T, b, c) (List.mem_append_right _ (List.mem_singleton_self _))
    have he : u = v := units_eq_of_mem_inter us hd hu hvm
      (hU hs.ends.2.1) (hT (isSomeVine_ends hv).1)
    subst v
    exact ⟨u, hu, union_subset hU hT⟩

/-- Cover and the singleton run intersections exclude the skipped vine from V. -/
theorem skipped_not_vinesV {S : Finset (GBranch G.tree)}
    (U : GroupUnits G S) (hS : S ∈ maximalGroups G.molecule)
    (sk : SkipData G S) (hsk : U.skip = some sk)
    {c : CLVine G} (hc : c ∈ vinesV G) : c.atoms ≠ sk.A := by
  intro hat
  have hi : IsIngredient G.molecule S c.atoms := hat.symm ▸ sk.ingredient
  obtain ⟨u, hu, hsub⟩ := U.cover (Mole.garden_isMolecule G) hS c hc hi
  have hxy := isSomeVine_ends sk.vine
  have hx : sk.x ∈ u.atoms := hsub (hat.symm ▸ hxy.1)
  have hy : sk.y ∈ u.atoms := hsub (hat.symm ▸ hxy.2.1)
  rcases (U.skip_units sk hsk).1 u hu with ⟨ha, _⟩ | ⟨ha, _⟩
  · rw [ha] at hx hy
    rcases sk.left with ⟨he, _⟩ | ⟨_, _, _, he⟩
    · rw [he] at hx; exact Finset.notMem_empty sk.x hx
    · have hz := mem_inter.mpr ⟨hy, hxy.2.1⟩
      rw [he, mem_singleton] at hz
      exact hxy.2.2 hz.symm
  · rw [ha] at hx hy
    rcases sk.right with ⟨he, _⟩ | ⟨_, _, _, he⟩
    · rw [he] at hy; exact Finset.notMem_empty sk.y hy
    · have hz := mem_inter.mpr ⟨hx, hxy.1⟩
      rw [he, mem_singleton] at hz
      exact hxy.2.2 hz

end WaveTurbulence.VineA
