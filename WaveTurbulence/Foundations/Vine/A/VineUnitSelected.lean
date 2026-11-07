/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineRunSelected
/-! Every actual unit has a spine of V ingredients. For an SG group these
are exactly selected ingredients, so disjoint-unit coverage can be transported. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Vine
variable {w : ℕ} {G : Garden w}

/-- The declared skipped runs have selected spines without a choice of adjoint. -/
theorem skip_runs_selected {S : Finset (GBranch G.tree)} (U : GroupUnits G S)
    (hS : S ∈ maximalGroups G.molecule) (sk : SkipData G S) (hsk : U.skip = some sk) :
    (sk.L0 = ∅ ∨ ∃ LL, Spine G.molecule LL sk.L0 sk.a sk.x ∧
      ∀ t ∈ LL, ∃ c ∈ vinesV G, c.atoms = t.1 ∧ IsIngredient G.molecule S t.1) ∧
    (sk.R0 = ∅ ∨ ∃ RR, Spine G.molecule RR sk.R0 sk.y sk.b ∧
      ∀ t ∈ RR, ∃ c ∈ vinesV G, c.atoms = t.1 ∧ IsIngredient G.molecule S t.1) := by
  cases hb : sk.bond with
  | none =>
    obtain ⟨n, hi⟩ := sk.chainM hb
    obtain ⟨L, hs, hA⟩ := Spine.mem_of_ingredient hi
    exact skipped_run_spines U hS sk hsk (sk.skelM hb) hs hA
      (fun T p q ht => (hs.mem_vine ht).1)
      (fun T p q ht => Or.inl ⟨sk.a, sk.b, L.length, p, q, sk.blockM hb, hs.ingredient_of_mem ht⟩)
  | some e =>
    obtain ⟨n, hn, hi⟩ := sk.chainN e hb
    have H := sk.skelN e hb
    obtain ⟨L, hs, hlen⟩ := Spine.of_chain_len (chainIngredient_spec hi).1
    have hlen2 : 2 ≤ L.length := hlen ▸ hn
    have hA := hs.ingredient_mem H.mol H.hSB hi
    have he := (sk.blockN e hb).1
    exact skipped_run_spines U hS sk hsk H hs hA
      (fun T p q ht => (vine_transfer G.molecule he (hs.not_both hlen2 ht) p q).mp (hs.mem_vine ht).1)
      (fun T p q ht => Or.inr ⟨sk.a, sk.b, e, L.length, p, q, he, hlen2, H.hSB, hs.ingredient_of_mem ht⟩)

/-- A spine and its V-membership assertions can be read in the opposite direction. -/
theorem selected_spine_reverse {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hs : Spine G.molecule L S a b)
    (hc : ∀ t ∈ L, ∃ c ∈ vinesV G, c.atoms = t.1) :
    ∃ R, Spine G.molecule R S b a ∧ ∀ t ∈ R, ∃ c ∈ vinesV G, c.atoms = t.1 := by
  refine ⟨_, hs.reverse, ?_⟩
  intro ⟨T, p, q⟩ ht
  exact hc (T, q, p) (mem_revSwap.mp ht)

/-- Every chosen group unit is an actual spine of selected source ingredients. -/
theorem groupUnit_selected_spine {S : Finset (GBranch G.tree)} (U : GroupUnits G S)
    (hS : S ∈ maximalGroups G.molecule) {u : CLBlock G} (hu : u ∈ U.units) :
    ∃ L, Spine G.molecule L u.atoms u.upper u.lower ∧
      ∀ t ∈ L, ∃ c ∈ vinesV G, c.atoms = t.1 := by
  cases hsk : U.skip with
  | none =>
    obtain ⟨n, hn⟩ := groupUnit_chain U hu
    obtain ⟨L, hs⟩ := Spine.of_chain hn
    have hat := U.noskip_units hsk u hu
    have hBu : G.molecule.IsBlock S u.upper u.lower := hat ▸ u.isBlock
    have hnroot := whole_unit_nonroot U hS hsk hu
    obtain ⟨a, b, hvc⟩ := U.whole_vc hsk (fun he => by rw [he] at hu; exact List.not_mem_nil hu)
    refine ⟨L, hs, ?_⟩
    intro ⟨T, p, q⟩ ht
    have hncn := spine_noCN hs u.isBlock (Or.inl u.cl) (T, p, q) ht
    obtain ⟨c, hc, he, _⟩ := member_mem_vinesV hS ⟨a, b, hvc⟩ hBu
      (hat ▸ hs.ingredient_of_mem ht) hncn (Or.inl hnroot)
    exact ⟨c, hc, he⟩
  | some sk =>
    have hr := skip_runs_selected U hS sk hsk
    have take_run {R : Finset (GBranch G.tree)} {a b : GBranch G.tree}
        (hat : u.atoms = R)
        (hc : R = ∅ ∨ ∃ LL, Spine G.molecule LL R a b ∧
          ∀ t ∈ LL, ∃ c ∈ vinesV G, c.atoms = t.1 ∧ IsIngredient G.molecule S t.1)
        (hj : u.upper = a ∧ u.lower = b ∨ u.upper = b ∧ u.lower = a) :
        ∃ L, Spine G.molecule L u.atoms u.upper u.lower ∧
          ∀ t ∈ L, ∃ c ∈ vinesV G, c.atoms = t.1 := by
      have hne : R ≠ ∅ := fun he => by
        have hm := hat ▸ u.isBlock.2.1
        rw [he] at hm; exact Finset.notMem_empty u.upper hm
      obtain ⟨LL, hs, hsel⟩ := hc.resolve_left hne
      have hmem : ∀ t ∈ LL, ∃ c ∈ vinesV G, c.atoms = t.1 := by
        intro t ht; obtain ⟨c, hc, he, _⟩ := hsel t ht; exact ⟨c, hc, he⟩
      rcases hj with ⟨hup, hlo⟩ | ⟨hup, hlo⟩
      · exact ⟨LL, by rw [hat, hup, hlo]; exact hs, hmem⟩
      · obtain ⟨RR, hsR, hmemR⟩ := selected_spine_reverse hs hmem
        exact ⟨RR, by rw [hat, hup, hlo]; exact hsR, hmemR⟩
    rcases (U.skip_units sk hsk).1 u hu with ⟨hat, hj⟩ | ⟨hat, hj⟩
    · exact take_run hat hr.1 hj
    · exact take_run hat hr.2 hj

/-- The actual unit spine consists entirely of V0(sigma) vines. -/
theorem unitBlocks_selected_spine {σ : Prescription G} {u : CLBlock G} (hu : u ∈ unitBlocks G σ) :
    ∃ L, Spine G.molecule L u.atoms u.upper u.lower ∧
      ∀ t ∈ L, ∃ c ∈ vinesV0 G σ, c.atoms = t.1 := by
  obtain ⟨S, hS, hσ, hum⟩ := mem_unitBlocks.mp hu
  obtain ⟨L, hs, hsel⟩ := groupUnit_selected_spine (groupUnitsOf G S) hS hum
  refine ⟨L, hs, ?_⟩
  intro t ht
  obtain ⟨c, hc, he⟩ := hsel t ht
  have hci : IsIngredient G.molecule S c.atoms := by
    obtain ⟨S', hS', hi', _⟩ := hc
    have hin : c.atoms ⊆ S := he ▸ (hs.mem_vine ht).2.trans ((groupUnitsOf G S).sub u hum)
    have heS : S' = S := by
      by_contra hne
      exact (disjoint_left.mp (groups_disjoint' (Mole.garden_isMolecule G) hS' hS hne)
        (ingredient_sub hi' c.upper_mem)) (hin c.upper_mem)
    exact heS ▸ hi'
  exact ⟨c, ⟨hc, S, hS, hci, hσ, fun h => h⟩, he⟩

end WaveTurbulence.VineA
