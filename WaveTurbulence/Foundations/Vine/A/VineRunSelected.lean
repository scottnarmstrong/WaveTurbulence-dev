/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSkipSelected
/-! Declared skipped runs have spines consisting entirely of selected V
ingredients in the original garden molecule. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Vine
variable {w : ℕ} {G : Garden w}

/-- A spine is determined by its ingredient vines and the source concatenations. -/
theorem spine_replace_molecule {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] {M : Molecule V D} {N : Molecule V E}
    {L : List (Finset V × V × V)} {S : Finset V} {a b : V} (hs : Spine M L S a b)
    (hv : ∀ T p q, (T, p, q) ∈ L → LGSpine.SourceVine.IsSomeVine N T p q) :
    Spine N L S a b := by
  induction hs with
  | one _ => exact .one (hv _ _ _ (List.mem_singleton_self _))
  | snoc hs ht hi hne ih =>
    exact .snoc (ih (fun T p q hm => hv T p q (List.mem_append_left _ hm)))
      (hv _ _ _ (List.mem_append_right _ (List.mem_singleton_self _))) hi hne

/-- An atom set with distinct joints cannot fit into a singleton intersection. -/
theorem atoms_ne_skipped {D : Type*} [Fintype D] [DecidableEq D]
    {N : Molecule (GBranch G.tree) D} {S : Finset (GBranch G.tree)} (sk : SkipData G S)
    {LL : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {R : Finset (GBranch G.tree)} {a b j : GBranch G.tree}
    (hs : Spine N LL R a b) (hi : R ∩ sk.A = {j})
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ LL) : t.1 ≠ sk.A := by
  intro he
  have hsub : sk.A ⊆ R := he ▸ (hs.mem_vine ht).2
  have hj := isSomeVine_ends sk.vine
  have hx := mem_inter.mpr ⟨hsub hj.1, hj.1⟩
  have hy := mem_inter.mpr ⟨hsub hj.2.1, hj.2.1⟩
  rw [hi, mem_singleton] at hx hy
  exact hj.2.2 (hx.trans hy.symm)

/-- A declared skipped run has only V ingredients, in the original molecule. -/
theorem skipped_run_spines {S : Finset (GBranch G.tree)} (U : GroupUnits G S)
    (hS : S ∈ maximalGroups G.molecule) (sk : SkipData G S) (hsk : U.skip = some sk)
    {D : Type*} [Fintype D] [DecidableEq D] {N : Molecule (GBranch G.tree) D}
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    (H : SkelDecomp N S sk.A sk.L0 sk.R0 sk.a sk.b sk.x sk.y)
    (hs : Spine N L S sk.a sk.b) (hA : (sk.A, sk.x, sk.y) ∈ L)
    (hv : ∀ T p q, (T, p, q) ∈ L → LGSpine.SourceVine.IsSomeVine G.molecule T p q)
    (hi : ∀ T p q, (T, p, q) ∈ L → IsIngredient G.molecule S T) :
    (sk.L0 = ∅ ∨ ∃ LL, Spine G.molecule LL sk.L0 sk.a sk.x ∧
      ∀ t ∈ LL, ∃ c ∈ vinesV G, c.atoms = t.1 ∧ IsIngredient G.molecule S t.1) ∧
    (sk.R0 = ∅ ∨ ∃ RR, Spine G.molecule RR sk.R0 sk.y sk.b ∧
      ∀ t ∈ RR, ∃ c ∈ vinesV G, c.atoms = t.1 ∧ IsIngredient G.molecule S t.1) := by
  obtain ⟨LL, RR, L0, R0, hL, hScut, hl, hr, hd⟩ := hs.split_around H.mol H.hSB hA
  have K : SkelDecomp N S sk.A L0 R0 sk.a sk.b sk.x sk.y := {
    mol := H.mol, hS := hScut, hSB := H.hSB, hA := H.hA,
    hL := hl.imp (fun h => ⟨h.2.1, h.2.2⟩) (fun h => ⟨h.1, h.2.1, h.2.2.2⟩),
    hR := hr.imp (fun h => ⟨h.2.1, h.2.2⟩) (fun h => ⟨h.1, h.2.1, h.2.2.2⟩), hd := hd }
  obtain ⟨heL, heR⟩ := run_unique H K
  rw [← heL] at hl
  rw [← heR] at hr
  have hLL : ∀ t ∈ LL, t ∈ L := by intro t ht; rw [hL]; exact List.mem_append_left _ ht
  have hRR : ∀ t ∈ RR, t ∈ L := by
    intro t ht; rw [hL]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ht)
  have hsel := skip_spine_selected U hS sk hsk hs hA hv hi
  constructor
  · rcases hl with ⟨_, he, _⟩ | ⟨_, _, hsL, hiL⟩
    · exact Or.inl he
    · refine Or.inr ⟨LL, spine_replace_molecule hsL (fun T p q ht => hv T p q (hLL _ ht)), ?_⟩
      intro t ht
      exact hsel t (hLL t ht) (atoms_ne_skipped sk hsL hiL ht)
  · rcases hr with ⟨_, he, _⟩ | ⟨_, _, hsR, hiR⟩
    · exact Or.inl he
    · refine Or.inr ⟨RR, spine_replace_molecule hsR (fun T p q ht => hv T p q (hRR _ ht)), ?_⟩
      intro t ht
      exact hsel t (hRR t ht) (atoms_ne_skipped sk hsR hiR ht)

end WaveTurbulence.VineA
