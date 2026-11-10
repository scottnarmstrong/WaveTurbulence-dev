/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Class
public import WaveTurbulence.Foundations.VineEst.VineEstS4.PrimeState
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Region

/-! # The canonical representatives of the twist class (V5 Step 4b, R31(1))

For a start state with a prime skeleton (TARGET `propstructure2`: the skeleton `G_sk` is prime), the set `CanonReps` of
(state, region) pairs reached by once-per-member batches has exactly one element over each garden of the class
(`canonReps_unique`, from `eq_of_prime_layered` and `Reach.region_unique`), is finite, and is the unique `ClassSection`
(`classSection_eq`).  `canonFinset` is that finite set; the statement over canonical representatives (TARGET's literal
form) sums over it, with no choice of section.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*} [Fintype ι] {kind : Bool}

/-- The (state, region) pairs reached from `(A, c)` by a once-per-member LF batch over all core members. -/
@[expose] def CanonRepsK (p : ℕ) (kind : Bool) (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) :
    Set (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family) :=
  {x | ∃ M : List ι, M.Perm Finset.univ.toList ∧ Reach p kind M A c x.1 x.2}

theorem perm_univ_nodup {M : List ι} (h : M.Perm Finset.univ.toList) : M.Nodup :=
  h.nodup_iff.mpr (Finset.nodup_toList _)

/-- Exactly one canonical representative over each (layered) garden of the class. -/
theorem canonReps_unique {p : ℕ} {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    {c : ChainAt A.skeleton A.family} {x y : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family}
    (hx : x ∈ CanonRepsK p kind A c) (hy : y ∈ CanonRepsK p kind A c) (h : x.1.layered = y.1.layered) : x = y := by
  classical
  obtain ⟨M, hM, hx⟩ := hx
  obtain ⟨M', hM', hy⟩ := hy
  have e := eq_of_prime_layered hA (perm_univ_nodup hM) (perm_univ_nodup hM') hx.batch hy.batch h
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  dsimp only at e hx hy
  subst e
  rw [Reach.region_unique (perm_univ_nodup hM) (perm_univ_nodup hM') hx hy]

theorem mem_allCoreOutputs_of_canonReps {p : ℕ} {A : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family}
    {x : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family} (hx : x ∈ CanonRepsK p kind A c) :
    x.1.layered ∈ A.allCoreOutputs (p := p) (kind := kind) := by
  obtain ⟨M, hM, hx⟩ := hx
  exact ⟨M, x.1, hM, hx.batch, rfl⟩

/-- Every class section is exactly the set of canonical representatives. -/
theorem classSection_eq_canonReps {p : ℕ} {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    {c : ChainAt A.skeleton A.family}
    {Z : Finset (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family)} (hZ : ClassSectionK p kind A c Z) :
    (Z : Set (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family)) = CanonRepsK p kind A c := by
  ext x
  constructor
  · intro hx
    obtain ⟨M, hM, hr⟩ := hZ.1 x hx
    exact ⟨M, hM, hr⟩
  · intro hx
    have hmem := mem_allCoreOutputs_of_canonReps hx
    rw [← hZ.2.2] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hyc : y ∈ CanonRepsK p kind A c := by
      obtain ⟨M, hM, hr⟩ := hZ.1 y hy
      exact ⟨M, hM, hr⟩
    have := canonReps_unique hA hyc hx hyx
    exact this ▸ hy

theorem canonReps_finite (p : ℕ) (kind : Bool) {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    (c : ChainAt A.skeleton A.family) : (CanonRepsK p kind A c).Finite := by
  obtain ⟨Z, hZ⟩ := exists_classSection p kind A c
  rw [← classSection_eq_canonReps hA hZ]
  exact Z.finite_toSet

/-- The finite set of canonical representatives (empty if it were infinite, which never happens for a prime start). -/
@[expose] noncomputable def canonFinsetK (p : ℕ) (kind : Bool) (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) :
    Finset (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family) := by
  classical
  exact if h : (CanonRepsK p kind A c).Finite then h.toFinset else ∅

theorem mem_canonFinset {p : ℕ} {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    {c : ChainAt A.skeleton A.family} {x : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family} :
    x ∈ canonFinsetK p kind A c ↔ x ∈ CanonRepsK p kind A c := by
  classical
  unfold canonFinsetK
  split_ifs with h
  · exact Set.Finite.mem_toFinset _
  · exact absurd (canonReps_finite p kind hA c) h

theorem classSection_eq {p : ℕ} {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    {c : ChainAt A.skeleton A.family}
    {Z : Finset (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family)} (hZ : ClassSectionK p kind A c Z) :
    Z = canonFinsetK p kind A c := by
  ext x
  rw [mem_canonFinset hA, ← classSection_eq_canonReps hA hZ]
  exact Finset.mem_coe.symm

/-- The `kind = true` (garden) canonical finset: the V5 uni object. -/
@[expose] noncomputable def canonFinset (p : ℕ) (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) :
    Finset (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family) := canonFinsetK p true A c

theorem canonFinsetK_true (p : ℕ) (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) :
    canonFinsetK p true A c = canonFinset p A c := rfl

end WaveTurbulence.VineEstS4
