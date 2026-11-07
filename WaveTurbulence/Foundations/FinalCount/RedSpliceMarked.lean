/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceUnits
public import WaveTurbulence.Foundations.FinalCount.RedSpliceV0
import Mathlib.Tactic

/-!
# B1a THREAD-ROOTS (ruling F-1): the marked vocabulary of Stage 1′ in main's REDSPLICE layer

Copied by source from `scope/B0-STAGE1MK/probe/Stage1MKProbe.lean` (sha256 `dab37b30…6c6b`, lines 130–164), with the
deviations recorded in the B1a handoff:
* `vinesV0Mk G σ Mk = {c | c ∈ vinesV0 G σ ∧ c ∉ Mk}` (o75 `𝒱₀♮`); main's `vinesV0` itself carries the trailing
  marked set (`vinesV0 G σ Mk`, default `∅`), and `vinesV0Mk_eq` identifies the two;
* `markedGroup G Mk S`: the group `S` of `𝒞` has a marked `𝒱`-ingredient (`m_𝕎 ≥ 1`, o75 §2.5);
* `MarkedGroupUnits G S Mk`: runs and survivors of a marked group (o75 §2.5 and Lemma 3).  One field is added to the
  probe's twelve: `chain` (every run is a vine chain from its upper to its lower joint, as main's units are,
  `VineA.groupUnit_chain`), which the threaded unit assemblies (R13) need.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1

variable {w : ℕ}

/-- The unmarked selected collection `𝒱₀♮ = 𝒱₀ \ Mk`. -/
def vinesV0Mk (G : Garden w) (σ : Prescription G) (Mk : Set (Stage1.CLVine G)) : Set (Stage1.CLVine G) :=
  {c | c ∈ vinesV0 G σ ∧ c ∉ Mk}

theorem vinesV0Mk_empty (G : Garden w) (σ : Prescription G) : vinesV0Mk G σ ∅ = vinesV0 G σ := by
  ext c; simp [vinesV0Mk]

/-- B1a bridge: the probe's `𝒱₀♮` is main's threaded `vinesV0` at the same marked set. -/
theorem vinesV0Mk_eq (G : Garden w) (σ : Prescription G) (Mk : Set (Stage1.CLVine G)) :
    vinesV0Mk G σ Mk = vinesV0 G σ Mk := by
  ext c; exact mem_vinesV0.symm

/-- A group of `𝒞` with a marked `𝒱`-ingredient (`m_𝕎 ≥ 1`, o75 §2.5). -/
def markedGroup (G : Garden w) (Mk : Set (Stage1.CLVine G)) (S : Finset (GBranch G.tree)) : Prop :=
  ∃ c ∈ Mk, c ∈ Stage1.vinesV G ∧ Stage1.IsIngredient G.molecule S c.atoms

/-- B1a bridge: no group is marked by the empty marked set. -/
theorem not_markedGroup_empty (G : Garden w) (S : Finset (GBranch G.tree)) : ¬ markedGroup G ∅ S :=
  fun ⟨_, h, _⟩ => h

/-- An unmarked group has no marked `𝒱`-ingredient. -/
theorem not_mem_of_not_markedGroup {G : Garden w} {Mk : Set (Stage1.CLVine G)} {S : Finset (GBranch G.tree)}
    (h : ¬ markedGroup G Mk S) {c : Stage1.CLVine G} (hV : c ∈ Stage1.vinesV G)
    (hI : Stage1.IsIngredient G.molecule S c.atoms) : c ∉ Mk :=
  fun hc => h ⟨c, hc, hV, hI⟩

/-- **Runs and survivors of a marked group** (o75 §2.5 and Lemma 3): the runs are the maximal concatenations of
consecutive unmarked `𝒱`-ingredients (CL blocks); the survivors are the marked ingredients and the ingredient
skipped by T1934 (main's `SkipData.A`), each with its joints. -/
structure MarkedGroupUnits (G : Garden w) (S : Finset (GBranch G.tree)) (Mk : Set (Stage1.CLVine G)) where
  runs : List (CLBlock G)
  surv : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)
  sub : ∀ u ∈ runs, u.atoms ⊆ S
  disj : runs.Pairwise (fun u u' => Disjoint u.atoms u'.atoms)
  sound : ∀ u ∈ runs, ∃ cs : List (Stage1.CLVine G),
    (∀ c ∈ cs, c ∈ Stage1.vinesV G ∧ c ∉ Mk ∧ Stage1.IsIngredient G.molecule S c.atoms) ∧
    ∀ v, v ∈ u.atoms ↔ ∃ c ∈ cs, v ∈ c.atoms
  cover : ∀ c : Stage1.CLVine G, c ∈ Stage1.vinesV G → c ∉ Mk → Stage1.IsIngredient G.molecule S c.atoms →
    ∃ u ∈ runs, c.atoms ⊆ u.atoms
  maximal : ∀ u ∈ runs, ∀ c : Stage1.CLVine G, c ∈ Stage1.vinesV G → c ∉ Mk →
    Stage1.IsIngredient G.molecule S c.atoms → ¬ Disjoint c.atoms u.atoms → c.atoms ⊆ u.atoms
  surv_spec : ∀ t ∈ surv, IsSomeVine G.molecule t.1 t.2.1 t.2.2 ∧ Stage1.IsIngredient G.molecule S t.1 ∧
    ((∃ c ∈ Mk, c ∈ Stage1.vinesV G ∧ c.atoms = t.1) ∨ ∀ c ∈ Stage1.vinesV G, c.atoms ≠ t.1)
  surv_cover : ∀ c ∈ Mk, c ∈ Stage1.vinesV G → Stage1.IsIngredient G.molecule S c.atoms → ∃ t ∈ surv, t.1 = c.atoms
  partition : ∀ v ∈ S, (∃ u ∈ runs, v ∈ u.atoms) ∨ ∃ t ∈ surv, v ∈ t.1
  surv_meet : surv.Pairwise (fun t t' => (t.1 ∩ t'.1).card ≤ 1)
  ext : ∀ u ∈ runs, ∃ j, (j = u.upper ∨ j = u.lower) ∧ HasExtPair G.molecule u.atoms j
  /-- B1a: every run is a vine chain from its upper to its lower joint (as main's units, `groupUnit_chain`). -/
  chain : ∀ u ∈ runs, ∃ n, Vine.Chain G.molecule u.atoms u.upper u.lower n

end WaveTurbulence.RedSplice
