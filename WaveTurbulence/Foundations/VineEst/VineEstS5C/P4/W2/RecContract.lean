/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSpec
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecProd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecEng

/-! # P4-W2 (session 18, step 2): the contraction clause `hcontract` of `freeDict_rec` from `SuppConcl`

`ae_ne_pi`: two distinct coordinates of `τ : ι → ℝ` differ almost everywhere.
`records_ne_zero_of_prod`: if the full product of the term (exceptional weights times native rows) is nonzero then every record factor is nonzero.
`hcontract_of_records`: with `SuppConcl` for every record, `add = recAdd` and distinct clock variables a.e., a nonzero product forces every order atom of `add` strictly and every record branch below the top clock or
below an interior clock; this is exactly the contradiction required.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4

theorem ae_ne_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) (hij : i ≠ j) :
    ∀ᵐ τ : ι → ℝ, τ i ≠ τ j := by
  have hker : (volume : Measure (ι → ℝ)) {τ | τ i = τ j} = 0 := by
    let f : (ι → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) -
      LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j
    have hne : LinearMap.ker f ≠ ⊤ := by
      intro h
      have : (Pi.single i 1 : ι → ℝ) ∈ LinearMap.ker f := by rw [h]; trivial
      simp [f, Pi.single_apply, hij.symm] at this
    have := Measure.addHaar_submodule (volume : Measure (ι → ℝ)) _ hne
    convert this using 2
    ext τ
    simp [f, sub_eq_zero]
  rw [ae_iff]
  simpa using hker

theorem ae_pairs_distinct {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset (ι × ι)) :
    ∀ᵐ τ : ι → ℝ, ∀ c ∈ S, c.1 ≠ c.2 → τ c.1 ≠ τ c.2 := by
  rw [Filter.eventually_all_finset]
  intro c hc
  by_cases h : c.1 = c.2
  · exact Filter.Eventually.of_forall fun τ hh => absurd h hh
  · filter_upwards [ae_ne_pi c.1 c.2 h] with τ hτ _ using hτ

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {hG : G.IsPlain}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem records_ne_zero_of_prod (recs : List (ExcRec G d)) (hnp : (recs.map ExcRec.p0).Nodup)
    (hreg : ∀ r ∈ recs, r.p0 ∈ clRegionalPairs hG U) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ)
    (ξ : GNode G.tree → (Fin d → ℤ)) (Q : SourcePair G → ℂ)
    (h : ∏ p ∈ clRegionalPairs hG U, (if p ∈ pexOf recs then xqOf recs p t u ξ else Q p) ≠ 0) :
    ∀ r ∈ recs, r.X ξ u ≠ 0 := by
  classical
  intro r hr hX0
  have hall := Finset.prod_ne_zero_iff.mp h
  have hsub : pexOf recs ⊆ clRegionalPairs hG U := fun p hp => by
    obtain ⟨r', hr', rfl⟩ := mem_pexOf.mp hp
    exact hreg r' hr'
  have h1 : ∏ p ∈ pexOf recs, xqOf recs p t u ξ ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have := hall p (hsub hp)
    rwa [if_pos hp] at this
  rw [prod_pexOf_xqOf recs hnp t u ξ] at h1
  exact h1 (List.prod_eq_zero (List.mem_map.mpr ⟨r, hr, hX0⟩))

variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n)

/-- **`hcontract` from `SuppConcl`.**  Almost every clock vector either makes the product vanish or has all order atoms of `recAdd` strict and every record branch
below the top clock or below an interior clock. -/
theorem hcontract_of_records (recs : List (ExcRec G d)) (hnp : (recs.map ExcRec.p0).Nodup)
    (hreg : ∀ r ∈ recs, r.p0 ∈ clRegionalPairs hG U) (zc : ExcRec G d → Prop)
    (addr : ExcRec G d → Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar))
    (hss : ∀ r ∈ recs, SuppConcl B hM9 r.X r.bj (zc r) (addr r)) (tt : Fin 3 → ℝ)
    (ξ : GNode G.tree → (Fin d → ℤ)) (Qf : ((assemblyShape hM9 B).TVar → ℝ) → SourcePair G → ℂ)
    (Tf : ((assemblyShape hM9 B).TVar → ℝ) → GBranch G.tree → ℂ) :
    ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ,
      ¬ ((∀ c ∈ recAdd B hM9 recs zc addr, τ c.1 < τ c.2) ∧
        ∀ v ∈ bexOf recs, clLocalClock R tt (assemblyClockEquiv hM9 B τ) v < tt 0 ∨ ∃ y ∈ U, y ≠ a ∧
          clLocalClock R tt (assemblyClockEquiv hM9 B τ) v < clLocalClock R tt (assemblyClockEquiv hM9 B τ) y) →
      (∏ p ∈ clRegionalPairs hG U, (if p ∈ pexOf recs then xqOf recs p tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) ξ
          else Qf τ p)) *
        (∏ v ∈ U.erase a, (if v ∈ bexOf recs then 1 else Tf τ v)) = 0 := by
  classical
  filter_upwards [ae_pairs_distinct (recAdd B hM9 recs zc addr)] with τ hτ hnot
  by_contra hne
  have hne1 : ∏ p ∈ clRegionalPairs hG U, (if p ∈ pexOf recs then xqOf recs p tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) ξ
          else Qf τ p) ≠ 0 := left_ne_zero_of_mul hne
  have hX := records_ne_zero_of_prod recs hnp hreg tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) ξ (Qf τ) hne1
  have hup : clLocalClock R tt (assemblyClockEquiv hM9 B τ) a = tt 0 := clLocalClock_upper R tt _
  refine hnot ⟨fun c hc => ?_, fun v hv => ?_⟩
  · obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
    have hr' : r ∈ recs := List.mem_toFinset.mp hr
    have hz : ¬ zc r := by
      intro hzr; rw [if_pos hzr] at hcr; exact absurd hcr (Finset.notMem_empty _)
    rw [if_neg hz] at hcr
    obtain ⟨hpair, -⟩ := hss r hr' _ _ (hX r hr')
    obtain ⟨hle, hdis⟩ := hpair hz c hcr
    rw [clLocalClock_slot, clLocalClock_slot] at hle hdis
    rcases hdis with hne' | hlt
    · exact lt_of_le_of_ne hle (hτ c hc hne')
    · exact hlt
  · obtain ⟨r, hr, rfl⟩ := mem_bexOf.mp hv
    obtain ⟨-, hlt⟩ := hss r hr _ _ (hX r hr)
    rw [← hup]
    exact hlt

end WaveTurbulence.VineEstS5C.P4.W2
