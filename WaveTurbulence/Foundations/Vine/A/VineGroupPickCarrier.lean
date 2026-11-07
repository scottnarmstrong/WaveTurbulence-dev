/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceDiagrams
public import WaveTurbulence.Foundations.FinalCount.RedSpliceDesig
/-! R83 single-HV and pure-DV candidate carriers and their literal survival. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole
open WaveTurbulence.LGSpine.SourceVine
variable {w : ℕ} {G : Garden w}

/-- The maximal single-HV case, before any prescription is supplied. -/
def SingleHVGroup (G : Garden w) (S : Finset (GBranch G.tree)) : Prop :=
  S ∈ maximalGroups G.molecule ∧ (∃ a b, IsHV G.molecule S a b) ∧
    ¬ ∃ a b, IsHVC G.molecule S a b

/-- The maximal pure-DV case, excluding all HV/VC/HVC presentations. -/
def PureDVGroup (G : Garden w) (S : Finset (GBranch G.tree)) : Prop :=
  S ∈ maximalGroups G.molecule ∧ (∃ a b, IsDV G.molecule S a b) ∧
    ¬ ∃ a b, IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b

/-- All valid deleted-bond triples, including both joint orders and dart orientations. -/
def HVCandidate (G : Garden w) (S : Finset (GBranch G.tree))
    (t : GBranch G.tree × GBranch G.tree × GardenDart G) : Prop :=
  G.molecule.ends t.2.2 = s(t.1, t.2.1) ∧
    Vine.IsSomeVine (eraseBond G.molecule t.2.2) S t.1 t.2.1

/-- All valid ordered constituent triples of a double vine. -/
def DVCandidate (G : Garden w) (S : Finset (GBranch G.tree))
    (t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) : Prop :=
  ∃ B, G.molecule.IsVine .V t.1 t.2.1 t.2.2 ∧
    G.molecule.IsVine .V B t.2.1 t.2.2 ∧ t.1 ∩ B = {t.2.1, t.2.2} ∧ S = t.1 ∪ B

/-- Every single-HV case has a candidate. -/
theorem SingleHVGroup.candidate {S : Finset (GBranch G.tree)} (h : SingleHVGroup G S) :
    Nonempty {t // HVCandidate G S t} := by
  obtain ⟨a, b, e, he, hv⟩ := h.2.1
  exact ⟨⟨(a, b, e), he, hv⟩⟩

/-- Every pure-DV case has a candidate. -/
theorem PureDVGroup.candidate {S : Finset (GBranch G.tree)} (h : PureDVGroup G S) :
    Nonempty {t // DVCandidate G S t} := by
  obtain ⟨a, b, A, B, hA, hB, hI, hS⟩ := h.2.1
  exact ⟨⟨(A, a, b), B, hA, hB, hI, hS⟩⟩

/-- Ingredients certify a VC or HVC presentation of their group. -/
theorem ingredient_vc_or_hvc {S A : Finset (GBranch G.tree)} (h : IsIngredient G.molecule S A) :
    ∃ a b, IsVC G.molecule S a b ∨ IsHVC G.molecule S a b := by
  rcases h with ⟨a, b, n, x, y, hB, hI⟩ | ⟨a, b, e, n, x, y, he, hn, hB, hI⟩
  · exact ⟨a, b, Or.inl ⟨hB, n, chain_ofVine (Vine.chainIngredient_spec hI).1⟩⟩
  · exact ⟨a, b, Or.inr ⟨e, he, hB, n, hn, chain_ofVine (Vine.chainIngredient_spec hI).1⟩⟩

/-- No actual unit belongs to a pure-DV group. -/
theorem PureDVGroup.units_empty {S : Finset (GBranch G.tree)} (h : PureDVGroup G S) :
    (groupUnitsOf G S).units = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro u hu
  obtain ⟨cs, hcs, hiff⟩ := (groupUnitsOf G S).sound u hu
  obtain ⟨c, hc, _⟩ := (hiff u.upper).mp u.isBlock.2.1
  obtain ⟨c', _, _, hi⟩ := hcs c hc
  obtain ⟨a, b, hkind⟩ := ingredient_vc_or_hvc hi
  exact h.2.2 ⟨a, b, Or.inr hkind⟩

/-- Pure-DV atoms are untouched by any prescription's actual unit list. -/
theorem PureDVGroup.no_unit {S : Finset (GBranch G.tree)} (h : PureDVGroup G S)
    (σ : Prescription G) {v : GBranch G.tree} (hv : v ∈ S) : ∀ u ∈ unitBlocks G σ, v ∉ u.atoms := by
  intro u hu hvu
  obtain ⟨T, hT, _, hu⟩ := mem_unitBlocks.mp hu
  by_cases he : T = S
  · subst T
    rw [h.units_empty] at hu
    exact List.not_mem_nil hu
  · exact Finset.disjoint_left.mp (groups_disjoint (garden_isMolecule G) hT h.1 he)
      ((groupUnitsOf G T).sub u hu hvu) hv

/-- All single-HV atoms survive the sigma-independent normalization literally. -/
theorem SingleHVGroup.cls_none {S : Finset (GBranch G.tree)} (h : SingleHVGroup G S)
    {v : GBranch G.tree} (hv : v ∈ S) : (coarseSplice G).cls v = none :=
  stSt_cls_none (garden_isMolecule G) (fun _ => .SG)
    (no_unit_hv (garden_isMolecule G) (fun _ => .SG) h.1 h.2.1 h.2.2 hv)

/-- All pure-DV atoms survive the sigma-independent normalization literally. -/
theorem PureDVGroup.cls_none {S : Finset (GBranch G.tree)} (h : PureDVGroup G S)
    {v : GBranch G.tree} (hv : v ∈ S) : (coarseSplice G).cls v = none :=
  stSt_cls_none (garden_isMolecule G) (fun _ => .SG) (h.no_unit (fun _ => .SG) hv)

end WaveTurbulence.VineA
