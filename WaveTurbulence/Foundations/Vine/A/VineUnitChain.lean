/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineRunChain
/-! Actual splice units are vine chains, with their declared CL orientation.
This includes runs of HVC adjoints, transported back to the original molecule. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Vine
variable {w : ℕ} {G : Garden w}

/-- The two declared skipped runs are chains of the original garden molecule. -/
theorem skip_runs_chain {S : Finset (GBranch G.tree)} (sk : SkipData G S) :
    (sk.L0 = ∅ ∨ ∃ n, Chain G.molecule sk.L0 sk.a sk.x n) ∧
    (sk.R0 = ∅ ∨ ∃ n, Chain G.molecule sk.R0 sk.y sk.b n) := by
  cases hb : sk.bond with
  | none =>
    obtain ⟨n, hi⟩ := sk.chainM hb
    exact cut_runs_chain (sk.skelM hb) hi
  | some e =>
    obtain ⟨n, _, hi⟩ := sk.chainN e hb
    have H := sk.skelN e hb
    have hc := cut_runs_chain H hi
    have he := (sk.blockN e hb).1
    constructor
    · rcases hc.1 with h | ⟨m, hm⟩
      · exact Or.inl h
      · right
        have hmiss : ¬ (sk.a ∈ sk.L0 ∧ sk.b ∈ sk.L0) :=
          fun h => cut_left_misses_end H h.2
        exact ⟨m, (eraseBond_local_embedding G.molecule e sk.L0
          (not_inGroup_of_ends G.molecule he hmiss)).chain_to hm (subset_refl _)⟩
    · rcases hc.2 with h | ⟨m, hm⟩
      · exact Or.inl h
      · right
        have hmiss : ¬ (sk.a ∈ sk.R0 ∧ sk.b ∈ sk.R0) :=
          fun h => cut_right_misses_start H h.1
        exact ⟨m, (eraseBond_local_embedding G.molecule e sk.R0
          (not_inGroup_of_ends G.molecule he hmiss)).chain_to hm (subset_refl _)⟩

/-- Chain existence respects the uniquely determined unordered block joints. -/
theorem chain_rejoint_exists {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} {S : Finset V} {a b x y : V}
    (hB : M.IsBlock S a b) (hC : ∃ n, Chain M S a b n) (hB' : M.IsBlock S x y) :
    ∃ n, Chain M S x y n := by
  have hj := block_joints_unique M hB hB'
  rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hC
  · obtain ⟨n, hn⟩ := hC
    obtain ⟨L, hL⟩ := Spine.of_chain hn
    exact ⟨_, hL.reverse.chain⟩

/-- Every actual group unit has an actual chain in the CL joint order. -/
theorem groupUnit_chain {S : Finset (GBranch G.tree)} (U : GroupUnits G S)
    {u : CLBlock G} (hu : u ∈ U.units) :
    ∃ n, Chain G.molecule u.atoms u.upper u.lower n := by
  cases hs : U.skip with
  | none =>
    have hnon : U.units ≠ [] := fun he => by
      rw [he] at hu
      exact List.not_mem_nil hu
    obtain ⟨a, b, hB, n, hn⟩ := U.whole_vc hs hnon
    have hat := U.noskip_units hs u hu
    apply chain_rejoint_exists (hat ▸ hB) ⟨n, hat ▸ hn.toVine⟩ u.isBlock
  | some sk =>
    have hc := skip_runs_chain sk
    rcases (U.skip_units sk hs).1 u hu with ⟨hat, hj⟩ | ⟨hat, hj⟩
    · have hne : sk.L0 ≠ ∅ := fun he => by
        have hm := hat ▸ u.isBlock.2.1
        rw [he] at hm
        exact Finset.notMem_empty u.upper hm
      obtain ⟨n, hn⟩ := hc.1.resolve_left hne
      rcases hj with ⟨hup, hlo⟩ | ⟨hup, hlo⟩
      · exact ⟨n, by rw [hat, hup, hlo]; exact hn⟩
      · obtain ⟨L, hL⟩ := Spine.of_chain hn
        exact ⟨_, by rw [hat, hup, hlo]; exact hL.reverse.chain⟩
    · have hne : sk.R0 ≠ ∅ := fun he => by
        have hm := hat ▸ u.isBlock.2.1
        rw [he] at hm
        exact Finset.notMem_empty u.upper hm
      obtain ⟨n, hn⟩ := hc.2.resolve_left hne
      rcases hj with ⟨hup, hlo⟩ | ⟨hup, hlo⟩
      · exact ⟨n, by rw [hat, hup, hlo]; exact hn⟩
      · obtain ⟨L, hL⟩ := Spine.of_chain hn
        exact ⟨_, by rw [hat, hup, hlo]; exact hL.reverse.chain⟩

/-- B1a: every unit of a group (main's units of an unmarked group, the runs of a marked one) is a chain. -/
theorem groupUnitsMk_chain {Mk : Set (Stage1.CLVine G)} {S : Finset (GBranch G.tree)} {u : CLBlock G}
    (hu : u ∈ groupUnitsMk G Mk S) : ∃ n, Chain G.molecule u.atoms u.upper u.lower n := by
  classical
  unfold groupUnitsMk at hu
  split_ifs at hu with h1 h2
  · exact (Classical.choice h2).chain u hu
  · simp at hu
  · exact groupUnit_chain (groupUnitsOf G S) hu

/-- B1a: canonical unit-chain existence for every marked vine set. -/
theorem unitBlocks_chainMk {σ : Prescription G} {Mk : Set (Stage1.CLVine G)} {u : CLBlock G}
    (hu : u ∈ unitBlocks G σ Mk) : ∃ n, Chain G.molecule u.atoms u.upper u.lower n := by
  obtain ⟨S, _, _, hm⟩ := mem_unitBlocksMk.mp hu
  exact groupUnitsMk_chain hm

end WaveTurbulence.VineA
