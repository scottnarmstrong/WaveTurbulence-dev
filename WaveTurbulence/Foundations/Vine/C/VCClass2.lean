/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.C.VCClass1

/-! # VINE-C: the class product `τ ≅ Π_j canonFinsetK p kind (unit start) (unit region)` and the sum identity

* `classU A us`: the τ-class as a finite set of (state, unit regions) pairs; one pair over each garden of the class
  (`classU_layered_injOn`, `classU_layered_image`: the layered gardens are exactly `A.allCoreOutputs`).
* `classProd`: the unit coordinates; `classProd_bijOn`: a bijection of `classU A us` onto the product
  `Fintype.piFinset fun j => canonFinsetK p kind (Us.st A j) (Us.reg us j)` (twists at disjoint chains commute: S1
  `OpsCommute`; uniqueness from the signatures, V5's `zp_eq_of_sigStar`).  `classProdEquiv` is the bijection.
* `unitKernelW_classProd`: the unit-`j` kernel of a class member is the kernel of its `j`-th coordinate (TARGET L1948,
  observation 1).
* `sum_classU_prod`: `Σ_{y ∈ τ} Π_j f_j(y) = Π_j Σ_{x ∈ class_j} g_j(x)` whenever `f_j(y) = g_j(classProd y j)`;
  `sum_classU_prod_kernelW` / `sum_classU_prod_recenteredW` are the kernel instances, with an arbitrary weight `W j` of the
  lower-joint clock of each unit (R58: `W j = modW (λ j)`) and arbitrary per-unit arguments.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineC
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Represents WaveTurbulence.RegRed TTree

variable {w : ℕ}

section CanonK
variable {κ : Type*} [Fintype κ] [DecidableEq κ] {p : ℕ} {kind : Bool}

/-- V5's kind-generic class of a prime start is finite. -/
theorem canonRepsK_finite {A : FamilyReconstruction w κ} (hA : IsPrimeGarden A.skeleton) (c : ChainAt A.skeleton A.family) :
    (CanonRepsK p kind A c).Finite := by
  refine Set.Finite.of_injOn (f := fun x => x.1.layered) (t := A.allCoreOutputs (p := p) (kind := kind)) ?_ ?_
    (allCoreOutputs_finite A)
  · rintro x ⟨M, hM, hR⟩
    exact ⟨M, x.1, hM, hR.batch, rfl⟩
  · rintro ⟨X, cx⟩ ⟨M, hM, hR⟩ ⟨X', cx'⟩ ⟨M', hM', hR'⟩ hl
    dsimp only at hR hR' hl
    have e := eq_of_prime_layered hA (perm_univ_nodup hM) (perm_univ_nodup hM') hR.batch hR'.batch hl
    subst e
    rw [Reach.region_unique (perm_univ_nodup hM) (perm_univ_nodup hM') hR hR']

theorem mem_canonFinsetK {A : FamilyReconstruction w κ} (hA : IsPrimeGarden A.skeleton) {c : ChainAt A.skeleton A.family}
    {x : Σ Bs : FamilyReconstruction w κ, ChainAt Bs.skeleton Bs.family} :
    x ∈ canonFinsetK p kind A c ↔ x ∈ CanonRepsK p kind A c := by
  classical
  unfold canonFinsetK
  rw [dite_eq_left (canonRepsK_finite hA c)]
  exact Set.Finite.mem_toFinset _

end CanonK

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J] {κ : J → Type*}
  [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] {Us : UnitSplit ι J κ} {p : ℕ} {kind : Bool}

section Finite

omit [Fintype J] [DecidableEq J] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] in
/-- One class member over each garden. -/
theorem classU_layered_injOn {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) :
    Set.InjOn (fun y : UState w Us => y.1.layered) (ClassUSet Us p kind A us) := by
  rintro ⟨B, usB⟩ ⟨M, hM, hR⟩ ⟨B', usB'⟩ ⟨M', hM', hR'⟩ hl
  dsimp only at hR hR' hl
  have e := eq_of_prime_layered hA (perm_univ_nodup hM) (perm_univ_nodup hM') hR.batch hR'.batch hl
  subst e
  rw [ReachU.unique (perm_univ_nodup hM) (perm_univ_nodup hM') hR hR']

omit [DecidableEq ι] [Fintype J] [DecidableEq J] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] in
/-- The layered gardens of the class members are exactly the class `A.allCoreOutputs` (M7 `outputs`, S1
`congruent_layered_iff`). -/
theorem classU_layered_image {A : FamilyReconstruction w ι} (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) :
    (fun y : UState w Us => y.1.layered) '' (ClassUSet Us p kind A us) = A.allCoreOutputs (p := p) (kind := kind) := by
  ext LH
  constructor
  · rintro ⟨y, ⟨M, hM, hR⟩, rfl⟩
    exact ⟨M, y.1, hM, hR.batch, rfl⟩
  · rintro ⟨M, B, hM, hB, rfl⟩
    obtain ⟨usB, hR⟩ := batch_reachU (Qm := Us.Q) hB us
    exact ⟨⟨B, usB⟩, ⟨M, hM, hR⟩, rfl⟩

omit [Fintype J] [DecidableEq J] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] in
theorem classUSet_finite {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) : (ClassUSet Us p kind A us).Finite :=
  Set.Finite.of_injOn (fun _ hy => (classU_layered_image (p := p) (kind := kind) us) ▸ Set.mem_image_of_mem _ hy)
    (classU_layered_injOn hA us) (allCoreOutputs_finite A)

variable (Us p kind) in
/-- **The τ-class** as a finite set of (state, unit regions) pairs. -/
@[expose] noncomputable def classU (A : FamilyReconstruction w ι) (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) :
    Finset (UState w Us) := by
  classical
  exact if h : (ClassUSet Us p kind A us).Finite then h.toFinset else ∅

omit [Fintype J] [DecidableEq J] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] in
theorem mem_classU {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    {us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)} {y : UState w Us} :
    y ∈ classU Us p kind A us ↔ y ∈ ClassUSet Us p kind A us := by
  classical
  unfold classU
  rw [dite_eq_left (classUSet_finite hA us)]
  exact Set.Finite.mem_toFinset _

end Finite

section Coord

variable (Us p kind) in
/-- **The unit coordinates of a class member** (the class-product map). -/
@[expose] noncomputable def classProd (A : FamilyReconstruction w ι) (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j))
    (y : UState w Us) (j : J) : Σ X : FamilyReconstruction w (κ j), ChainAt X.skeleton X.family := by
  classical
  exact if h : ∃ x, IsCoord Us p kind A us y j x then Classical.choose h else ⟨Us.st A j, Us.reg us j⟩

omit [Fintype J] in
theorem classProd_isCoord {A : FamilyReconstruction w ι} {us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)}
    {y : UState w Us} (hy : y ∈ ClassUSet Us p kind A us) (j : J) : IsCoord Us p kind A us y j (classProd Us p kind A us y j) := by
  classical
  have h : ∃ x, IsCoord Us p kind A us y j x := (coord_exists hy j).imp fun x hx => hx.1
  unfold classProd
  rw [dite_eq_left h]
  exact Classical.choose_spec h

omit [Fintype J] in
/-- **TARGET L1948, observation 1: the unit kernel of a class member is the kernel of its unit coordinate.** -/
theorem unitKernelW_classProd {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    {us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)} {y : UState w Us} (hy : y ∈ ClassUSet Us p kind A us) (j : J)
    {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    unitKernelW y.1 (y.2 j) L γ δ F base W t0 t1 t2 e f g h =
      twistedLocalKernelW (classProd Us p kind A us y j).1 (classProd Us p kind A us y j).2 L γ δ F base W t0 t1 t2
        e f g h := by
  obtain ⟨x, hx, hk⟩ := coord_exists hy j
  rw [coord_unique hA (classProd_isCoord hy j) hx]
  exact (hk L γ δ F base W t0 t1 t2 e f g h).symm

theorem classProd_mem {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    {us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)} {y : UState w Us} (hy : y ∈ classU Us p kind A us) :
    classProd Us p kind A us y ∈ Fintype.piFinset fun j => canonFinsetK p kind (Us.st A j) (Us.reg us j) := by
  rw [Fintype.mem_piFinset]
  intro j
  exact (mem_canonFinsetK (A := Us.st A j) hA).mpr (classProd_isCoord ((mem_classU hA).mp hy) j).1

/-- **The class-product bijection** `τ ≅ Π_j canonFinsetK p kind (Us.st A j) (Us.reg us j)`. -/
theorem classProd_bijOn {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) :
    Set.BijOn (classProd Us p kind A us) (classU Us p kind A us)
      (Fintype.piFinset fun j => canonFinsetK p kind (Us.st A j) (Us.reg us j)) := by
  refine ⟨fun y hy => classProd_mem hA hy, ?_, ?_⟩
  · intro y hy y' hy' he
    have hy1 := (mem_classU hA).mp hy
    have hy1' := (mem_classU hA).mp hy'
    refine classU_eq_of_sig hA hy1 hy1' fun i => ?_
    obtain ⟨k, hk⟩ := Us.surj i
    rw [← hk]
    have h1 := (classProd_isCoord hy1 (Us.unitOf i)).2 k
    have h2 := (classProd_isCoord hy1' (Us.unitOf i)).2 k
    rw [← h1, ← h2, he]
  · intro x hx
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hx
    have hx' : ∀ j, x j ∈ CanonRepsK p kind (Us.st A j) (Us.reg us j) := fun j => (mem_canonFinsetK (A := Us.st A j) hA).mp (hx j)
    obtain ⟨y, hy, hs⟩ := lift_exists us x hx'
    refine ⟨y, (mem_classU hA).mpr hy, funext fun j => ?_⟩
    exact coord_unique hA (classProd_isCoord hy j) ⟨hx' j, fun k => (hs j k).symm⟩

/-- The class-product bijection as an equivalence of the finite sets. -/
@[expose] noncomputable def classProdEquiv {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) :
    ↥(classU Us p kind A us) ≃ ↥(Fintype.piFinset fun j => canonFinsetK p kind (Us.st A j) (Us.reg us j)) :=
  (classProd_bijOn hA us).equiv _ |>.trans (Equiv.refl _)

end Coord

section Sum

/-- **The class sum of a product of unit factors is the product of the unit class sums**, whenever each unit factor of a
class member is a function of its unit coordinate. -/
theorem sum_classU_prod {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) {M : Type*} [CommSemiring M] (f : J → UState w Us → M)
    (g : ∀ j, (Σ X : FamilyReconstruction w (κ j), ChainAt X.skeleton X.family) → M)
    (hfg : ∀ y ∈ classU Us p kind A us, ∀ j, f j y = g j (classProd Us p kind A us y j)) :
    ∑ y ∈ classU Us p kind A us, ∏ j, f j y = ∏ j, ∑ x ∈ canonFinsetK p kind (Us.st A j) (Us.reg us j), g j x := by
  rw [Finset.prod_univ_sum]
  have hb := classProd_bijOn (p := p) (kind := kind) hA us
  refine Finset.sum_bij (fun y _ => classProd Us p kind A us y) (fun y hy => hb.1 hy)
    (fun y hy y' hy' he => hb.2.1 hy hy' he) (fun x hx => ?_) (fun y hy => ?_)
  · obtain ⟨y, hy, rfl⟩ := hb.2.2 hx
    exact ⟨y, hy, rfl⟩
  · exact Finset.prod_congr rfl fun j _ => hfg y hy j

/-- **The class product for the weighted unit kernels** (R58 modulation: `W j = modW (λ j)`; `λ = 0` is `clLocalKernel`). -/
theorem sum_classU_prod_kernelW {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) {d : ℕ} (L γ δ : ℝ) (F : J → ℕ → Mom d → ℝ) (base : Mom d)
    (W : J → ℝ → ℂ) (t0 t1 t2 : J → ℝ) (e f g h : J → Mom d) :
    ∑ y ∈ classU Us p kind A us, ∏ j, unitKernelW y.1 (y.2 j) L γ δ (F j) base (W j) (t0 j) (t1 j) (t2 j)
        (e j) (f j) (g j) (h j) =
      ∏ j, ∑ x ∈ canonFinsetK p kind (Us.st A j) (Us.reg us j),
        twistedLocalKernelW x.1 x.2 L γ δ (F j) base (W j) (t0 j) (t1 j) (t2 j) (e j) (f j) (g j) (h j) :=
  sum_classU_prod hA us _ _ fun _ hy j =>
    unitKernelW_classProd hA ((mem_classU hA).mp hy) j L γ δ (F j) base (W j) (t0 j) (t1 j) (t2 j) (e j) (f j) (g j) (h j)

end Sum

end WaveTurbulence.VineC
