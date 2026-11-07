/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineWholeUnit
/-! Every non-skipped ingredient of a declared group spine is in V.
The weaker top-case record is completed using its cover property. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole
open WaveTurbulence.Vine
variable {w : ℕ} {G : Garden w}

/-- The two source chain presentations have identical constructors. -/
theorem chain_toSource {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ} (h : Chain M S a b n) :
    LGSpine.SourceVine.Chain M S a b n := by
  induction h with
  | single h => exact .single h
  | append _ h hi hne ih => exact .append ih h hi hne

/-- A skipped group is an actual VC or HVC, with the declared outer joints. -/
theorem skip_group_kind {S : Finset (GBranch G.tree)} (sk : SkipData G S) :
    LGSpine.SourceVine.IsVC G.molecule S sk.a sk.b ∨ LGSpine.SourceVine.IsHVC G.molecule S sk.a sk.b := by
  cases hb : sk.bond with
  | none =>
    obtain ⟨n, hi⟩ := sk.chainM hb
    exact Or.inl ⟨sk.blockM hb, n, chain_toSource (chainIngredient_spec hi).1⟩
  | some e =>
    obtain ⟨n, hn, hi⟩ := sk.chainN e hb
    have he := sk.blockN e hb
    exact Or.inr ⟨e, he.1, he.2, n, hn, chain_toSource (chainIngredient_spec hi).1⟩

/-- With a CN ingredient, every CL ingredient of a VC/HVC belongs to V. -/
theorem cl_mem_vinesV_of_CN {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule)
    (hvl : ∃ a b, LGSpine.SourceVine.IsVC G.molecule S a b ∨ LGSpine.SourceVine.IsHVC G.molecule S a b)
    (hcn : ∃ T, IsIngredient G.molecule S T ∧ IsCNVine G T)
    (c : CLVine G) (hi : IsIngredient G.molecule S c.atoms) : c ∈ vinesV G := by
  refine ⟨S, hS, hi, ?_⟩
  obtain ⟨a, b, hvc | hhvc⟩ := hvl
  · by_cases hr : IsRootVC G S
    · exact Or.inr ⟨Or.inr hr, Or.inl hcn⟩
    · exact Or.inl ⟨a, b, hvc, hr⟩
  · exact Or.inr ⟨Or.inl ⟨a, b, hhvc⟩, Or.inl hcn⟩

/-- All source ingredients of the declared spine except the skipped one are selected. -/
theorem skip_spine_selected {S : Finset (GBranch G.tree)} (U : GroupUnits G S)
    (hS : S ∈ maximalGroups G.molecule) (sk : SkipData G S) (hsk : U.skip = some sk)
    {D : Type*} [Fintype D] [DecidableEq D] {N : Molecule (GBranch G.tree) D}
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    (hs : Spine N L S sk.a sk.b) (hA : (sk.A, sk.x, sk.y) ∈ L)
    (hv : ∀ T p q, (T, p, q) ∈ L → LGSpine.SourceVine.IsSomeVine G.molecule T p q)
    (hi : ∀ T p q, (T, p, q) ∈ L → IsIngredient G.molecule S T) :
    ∀ t ∈ L, t.1 ≠ sk.A → ∃ c ∈ vinesV G, c.atoms = t.1 ∧ IsIngredient G.molecule S t.1 := by
  have hvl : ∃ a b, LGSpine.SourceVine.IsVC G.molecule S a b ∨ LGSpine.SourceVine.IsHVC G.molecule S a b :=
    ⟨sk.a, sk.b, skip_group_kind sk⟩
  have hblk : ∀ T p q, (T, p, q) ∈ L → G.molecule.IsBlock T p q :=
    fun T p q ht => (hv T p q ht).choose_spec.1
  rcases sk.kind with hcn | ⟨hroot, c0, hat, htop⟩
  · have hCN : ∃ T, IsIngredient G.molecule S T ∧ IsCNVine G T :=
      ⟨sk.A, sk.ingredient, sk.x, sk.y, sk.vine, hcn⟩
    intro ⟨T, p, q⟩ ht hne
    have hn : ¬ CNMem G (T, p, q) := fun hc =>
      hne (congrArg Prod.fst (hs.cn_unique hblk ht hA hc hcn))
    obtain ⟨c, hc, _⟩ := exists_clVine (hv T p q ht) hn
    have hci : IsIngredient G.molecule S c.atoms := hc.symm ▸ hi T p q ht
    exact ⟨c, cl_mem_vinesV_of_CN hS hvl hCN c hci, hc, hi T p q ht⟩
  · have hbase : (∃ a b, LGSpine.SourceVine.IsHVC G.molecule S a b) ∨ IsRootVC G S := by
      cases hb : sk.bond with
      | none => exact Or.inr (hroot hb)
      | some e =>
        rcases skip_group_kind sk with hvc | hvc
        · exact (vc_not_hyper hvc.1 ⟨e, (sk.blockN e hb).1, (sk.blockN e hb).2⟩).elim
        · exact Or.inl ⟨sk.a, sk.b, hvc⟩
    have hn : ∀ t ∈ L, ¬ CNMem G t := by
      intro ⟨T, p, q⟩ ht hcn
      have hCN : ∃ T, IsIngredient G.molecule S T ∧ IsCNVine G T :=
        ⟨T, hi T p q ht, p, q, hv T p q ht, hcn⟩
      have hci : IsIngredient G.molecule S c0.atoms := hat.symm ▸ sk.ingredient
      have hc0 := cl_mem_vinesV_of_CN hS hvl hCN c0 hci
      exact skipped_not_vinesV U hS sk hsk hc0 hat
    intro ⟨T, p, q⟩ ht hne
    obtain ⟨c, hc, _⟩ := exists_clVine (hv T p q ht) (hn _ ht)
    have hci : IsIngredient G.molecule S c.atoms := hc.symm ▸ hi T p q ht
    have hnt : ¬ IsTopIngredient S c := fun h => top_unique h htop hci
      (hat.symm ▸ sk.ingredient) (by rw [hc, hat]; exact hne)
    exact ⟨c, ⟨S, hS, hci, Or.inr ⟨hbase, Or.inr hnt⟩⟩, hc, hi T p q ht⟩

end WaveTurbulence.VineA
