/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.C.VCComb
public import WaveTurbulence.Foundations.Stage1.Represents.RepVineEst

/-! # VINE-C: the τ-class and its unit coordinates

`UnitSplit ι J κ`: the members `ι` of the core family of a τ-class state are split into the units `j : J` (TARGET L1946:
the VCs `U_1, …, U_q` of `V₀`), the members of the unit `j` being `emb j : κ j → ι`.  `Us.st A j` is the state restricted to
the unit `j` and `Us.reg us j` the unit's chain region: these are the start state and the start region of V5's class of the
unit (S2 identifies them with `startState`/`chainStart` of the unit's chain assembly).

* `ClassUSet A us`: the (state, unit regions) pairs reached from `A` by once-per-member batches over all members (the
  τ-class, TARGET L1944, with the regions of the units carried along).
* `coord_exists`: every class member `y` has, for each unit `j`, a coordinate in V5's class of the unit, with the same
  signatures at the unit's members, and with the SAME unit kernel (`twistedLocalKernelW` of the coordinate equals the unit
  kernel `unitKernelW` of `y`; TARGET L1948, observation 1).  `coord_unique`: the coordinate is unique.
* `classU_eq_of_sig`: a class member is determined by its signatures.  `lift_exists`: every tuple of unit coordinates comes
  from a class member (twists at disjoint chains commute).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineC
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Represents TTree

variable {w : ℕ}

/-- A splitting of the members `ι` of a core family into units `j : J`; the members of the unit `j` are `emb j k`,
`k : κ j`. -/
structure UnitSplit (ι J : Type*) (κ : J → Type*) where
  unitOf : ι → J
  emb : ∀ j, κ j → ι
  inj : ∀ j, Function.Injective (emb j)
  unitOf_emb : ∀ j k, unitOf (emb j k) = j
  surj : ∀ i, ∃ k, emb (unitOf i) k = i

namespace UnitSplit
variable {ι J : Type*} {κ : J → Type*} (Us : UnitSplit ι J κ)

/-- Membership in the unit `j`. -/
@[expose] def Q (j : J) (i : ι) : Prop := Us.unitOf i = j

theorem q_emb (j : J) (k : κ j) : Us.Q j (Us.emb j k) := Us.unitOf_emb j k

/-- The state restricted to the members of the unit `j`. -/
@[expose] def st (A : FamilyReconstruction w ι) (j : J) : FamilyReconstruction w (κ j) := stComap A (Us.emb j) (Us.inj j)

/-- The chain region of the unit `j`, as a V5 region of the restricted state. -/
@[expose] def reg {A : FamilyReconstruction w ι} (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) (j : J) :
    ChainAt (Us.st A j).skeleton (Us.st A j).family :=
  (us j).toChainAt (Us.emb j) (Us.inj j) (Us.q_emb j)

theorem exists_map_eq (j : J) : ∀ L : List ι, (∀ i ∈ L, Us.unitOf i = j) → ∃ N : List (κ j), N.map (Us.emb j) = L := by
  intro L
  induction L with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons i L ih =>
    intro hL
    obtain ⟨N, hN⟩ := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    obtain ⟨k, hk⟩ : ∃ k : κ j, Us.emb j k = i := by
      have hi := hL i List.mem_cons_self
      subst hi
      exact Us.surj i
    exact ⟨k :: N, by simp [hk, hN]⟩

theorem mem_map_emb (j : J) {N : List (κ j)} (hN : ∀ k, k ∈ N) (i : ι) : i ∈ N.map (Us.emb j) ↔ Us.unitOf i = j := by
  constructor
  · intro hi
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hi
    exact Us.unitOf_emb j k
  · intro hi
    obtain ⟨k, hk⟩ : ∃ k : κ j, Us.emb j k = i := by
      subst hi
      exact Us.surj i
    exact List.mem_map.mpr ⟨k, hN k, hk⟩

theorem filter_eq_map [Fintype ι] [DecidableEq J] (j : J) [Fintype (κ j)] [DecidableEq (κ j)] {M : List ι} (hM : M.Perm Finset.univ.toList) :
    ∃ N : List (κ j), N.Perm Finset.univ.toList ∧ N.map (Us.emb j) = M.filter (fun i => decide (Us.unitOf i = j)) := by
  obtain ⟨N, hN⟩ := Us.exists_map_eq j (M.filter (fun i => decide (Us.unitOf i = j)))
    (fun i hi => by simpa using (List.mem_filter.mp hi).2)
  have hMn := perm_univ_nodup hM
  have hNn : N.Nodup := by
    have := hMn.filter (fun i => decide (Us.unitOf i = j))
    rw [← hN] at this
    exact List.Nodup.of_map _ this
  refine ⟨N, List.perm_of_nodup_nodup_toFinset_eq hNn (Finset.nodup_toList _) ?_, hN⟩
  ext k
  simp only [List.mem_toFinset, Finset.mem_toList, Finset.mem_univ, iff_true]
  have : Us.emb j k ∈ M.filter (fun i => decide (Us.unitOf i = j)) :=
    List.mem_filter.mpr ⟨hM.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ _)), by simp [Us.unitOf_emb]⟩
  rw [← hN] at this
  exact (List.mem_map_of_injective (Us.inj j)).mp this

end UnitSplit

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J] {κ : J → Type*}
  [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] (Us : UnitSplit ι J κ) (p : ℕ) (kind : Bool)

/-- A state with the regions of all units. -/
abbrev UState (w : ℕ) (Us : UnitSplit ι J κ) := Σ B : FamilyReconstruction w ι, ∀ j, UnitAt B.skeleton B.family (Us.Q j)

/-- **The τ-class**: the (state, unit regions) pairs reached from `A` by once-per-member LF batches over all members. -/
@[expose] def ClassUSet (A : FamilyReconstruction w ι) (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) :
    Set (UState w Us) :=
  {y | ∃ M : List ι, M.Perm Finset.univ.toList ∧ ReachU p kind Us.Q M A us y.1 y.2}

/-- `x` is the unit-`j` coordinate of the class member `y`: an element of V5's class of the unit with the signatures of `y`
at the unit's members. -/
@[expose] def IsCoord (A : FamilyReconstruction w ι) (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)) (y : UState w Us)
    (j : J) (x : Σ X : FamilyReconstruction w (κ j), ChainAt X.skeleton X.family) : Prop :=
  x ∈ CanonRepsK p kind (Us.st A j) (Us.reg us j) ∧ ∀ k, sigStar x.1 k = sigStar y.1 (Us.emb j k)

variable {Us p kind}

omit [Fintype J] in
/-- **Existence of the unit coordinates, with the unit kernel read at the coordinate** (TARGET L1948, observation 1). -/
theorem coord_exists {A : FamilyReconstruction w ι} {us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)} {y : UState w Us}
    (hy : y ∈ ClassUSet Us p kind A us) (j : J) :
    ∃ x, IsCoord Us p kind A us y j x ∧
      ∀ {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g h : Mom d),
        twistedLocalKernelW x.1 x.2 L γ δ F base W t0 t1 t2 e f g h =
          unitKernelW y.1 (y.2 j) L γ δ F base W t0 t1 t2 e f g h := by
  obtain ⟨B, usB⟩ := y
  obtain ⟨M, hM, hR⟩ := hy
  dsimp only at hR ⊢
  have hMn : M.Nodup := perm_univ_nodup hM
  obtain ⟨Y, h1, h2⟩ := batch_partition (fun i => decide (Us.unitOf i = j)) M hMn hR.batch
  obtain ⟨usY, hRY⟩ := batch_reachU (Qm := Us.Q) h1 us
  obtain ⟨us'', hR2⟩ := batch_reachU (Qm := Us.Q) h2 usY
  have hn2 : (M.filter (fun i => decide (Us.unitOf i = j)) ++
      M.filter (fun i => !decide (Us.unitOf i = j))).Nodup :=
    (List.filter_append_perm (fun i => decide (Us.unitOf i = j)) M).nodup_iff.mpr hMn
  have hus : us'' = usB := ReachU.unique hn2 hMn (hRY.append hR2) hR
  subst hus
  obtain ⟨N, hN, hNe⟩ := Us.filter_eq_map j hM
  have hRY' : ReachU p kind Us.Q (N.map (Us.emb j)) A us Y usY := by rw [hNe]; exact hRY
  have hproj := ReachU.proj (Us.emb j) (Us.inj j) j (Us.q_emb j) N hRY'
  have hnot : ∀ i ∈ M.filter (fun i => !decide (Us.unitOf i = j)), ¬ Us.Q j i := by
    intro i hi hq
    have := (List.mem_filter.mp hi).2
    simp only [UnitSplit.Q] at hq
    simp [hq] at this
  refine ⟨⟨stComap Y (Us.emb j) (Us.inj j), (usY j).toChainAt (Us.emb j) (Us.inj j) (Us.q_emb j)⟩,
    ⟨⟨N, hN, hproj⟩, fun k => ?_⟩, fun L γ δ F base W t0 t1 t2 e f g h => ?_⟩
  · show sigStar Y (Us.emb j k) = sigStar B (Us.emb j k)
    exact (sigStar_batch h2 (fun hm => hnot _ hm (Us.q_emb j k))).symm
  · exact (unitKernelW_eq_twisted (Us.emb j) (Us.inj j) (Us.q_emb j) Y (usY j) L γ δ F base W t0 t1 t2 e f g h).symm.trans
      (ReachU.kernel_eq hR2 j hnot L γ δ F base W t0 t1 t2 e f g h).symm

omit [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J] in
/-- Two elements of V5's class of a unit with the same signatures coincide (prime start). -/
theorem unit_eq_of_sig {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    {us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)} (j : J)
    {x x' : Σ X : FamilyReconstruction w (κ j), ChainAt X.skeleton X.family}
    (hx : x ∈ CanonRepsK p kind (Us.st A j) (Us.reg us j)) (hx' : x' ∈ CanonRepsK p kind (Us.st A j) (Us.reg us j))
    (hs : ∀ k, sigStar x.1 k = sigStar x'.1 k) : x = x' := by
  obtain ⟨N, hN, hRx⟩ := hx
  obtain ⟨N', hN', hRx'⟩ := hx'
  have e1 : x.1 = x'.1 := eq_of_sigStar_batch (Finset.univ.toList) (Finset.nodup_toList _) (A := Us.st A j) hA hN hN'
    hRx.batch hRx'.batch (fun k _ => hs k)
  obtain ⟨X, c⟩ := x
  obtain ⟨X', c'⟩ := x'
  dsimp only at e1 hRx hRx'
  subst e1
  rw [Reach.region_unique (perm_univ_nodup hN) (perm_univ_nodup hN') hRx hRx']

omit [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J] in
theorem coord_unique {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    {us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)} {y : UState w Us} {j : J}
    {x x' : Σ X : FamilyReconstruction w (κ j), ChainAt X.skeleton X.family}
    (hx : IsCoord Us p kind A us y j x) (hx' : IsCoord Us p kind A us y j x') : x = x' :=
  unit_eq_of_sig hA j hx.1 hx'.1 (fun k => (hx.2 k).trans (hx'.2 k).symm)

omit [Fintype J] [DecidableEq J] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] in
/-- A class member is determined by its signatures (prime start). -/
theorem classU_eq_of_sig {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    {us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)} {y y' : UState w Us}
    (hy : y ∈ ClassUSet Us p kind A us) (hy' : y' ∈ ClassUSet Us p kind A us)
    (hs : ∀ i, sigStar y.1 i = sigStar y'.1 i) : y = y' := by
  obtain ⟨M, hM, hR⟩ := hy
  obtain ⟨M', hM', hR'⟩ := hy'
  have e1 : y.1 = y'.1 := eq_of_sigStar_batch (Finset.univ.toList) (Finset.nodup_toList _) hA hM hM'
    hR.batch hR'.batch (fun i _ => hs i)
  obtain ⟨B, usB⟩ := y
  obtain ⟨B', usB'⟩ := y'
  dsimp only at e1 hR hR'
  subst e1
  rw [ReachU.unique (perm_univ_nodup hM) (perm_univ_nodup hM') hR hR']

omit [DecidableEq J] [∀ j, DecidableEq (κ j)] in
/-- **Every tuple of unit coordinates comes from a class member** (twists at disjoint chains commute). -/
theorem lift_exists {A : FamilyReconstruction w ι} (us : ∀ j, UnitAt A.skeleton A.family (Us.Q j))
    (x : ∀ j, Σ X : FamilyReconstruction w (κ j), ChainAt X.skeleton X.family)
    (hx : ∀ j, x j ∈ CanonRepsK p kind (Us.st A j) (Us.reg us j)) :
    ∃ y ∈ ClassUSet Us p kind A us, ∀ j k, sigStar y.1 (Us.emb j k) = sigStar (x j).1 k := by
  choose N hN hR using hx
  have hZ : ∀ j, ∃ Z, FamilyBatch p kind ((N j).map (Us.emb j)) A Z ∧ stComap Z (Us.emb j) (Us.inj j) = (x j).1 :=
    fun j => batch_lift (Us.emb j) (Us.inj j) (hR j).batch rfl
  choose Z hZb hZe using hZ
  have hall : ∀ j k, k ∈ N j := fun j k => (hN j).mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ k))
  have key : ∀ Js : List J, Js.Nodup → ∃ B L, L.Nodup ∧ (∀ i, i ∈ L ↔ Us.unitOf i ∈ Js) ∧
      FamilyBatch p kind L A B ∧ ∀ j ∈ Js, ∀ k, sigStar B (Us.emb j k) = sigStar (Z j) (Us.emb j k) := by
    intro Js
    induction Js with
    | nil =>
      intro _
      exact ⟨A, [], List.nodup_nil, by simp, .nil A, by simp⟩
    | cons j Js ih =>
      intro hn
      obtain ⟨hj, hn'⟩ := List.nodup_cons.mp hn
      obtain ⟨B', L', hL'n, hL'm, hL'b, hs'⟩ := ih hn'
      have hmem := Us.mem_map_emb j (hall j)
      have hd : ∀ i ∈ (N j).map (Us.emb j), i ∉ L' := by
        intro i hi hiL
        have h1 := (hL'm i).mp hiL
        rw [(hmem i).mp hi] at h1
        exact hj h1
      obtain ⟨B, h1, h2⟩ := batch_diamond ((N j).map (Us.emb j)) hL'b (hZb j) hd
      refine ⟨B, L' ++ (N j).map (Us.emb j), ?_, ?_, Stage1.familyBatch_append hL'b h1, ?_⟩
      · refine List.nodup_append.mpr ⟨hL'n, ((hN j).nodup_iff.mpr (Finset.nodup_toList _)).map (Us.inj j), ?_⟩
        intro a ha b hb hab
        subst hab
        exact hd a hb ha
      · intro i
        rw [List.mem_append, hL'm i, hmem i, List.mem_cons]
        exact or_comm
      · intro j' hj' k
        rcases List.mem_cons.mp hj' with rfl | hj'
        · exact sigStar_batch h2 (fun hm => hd _ ((hmem _).mpr (Us.unitOf_emb j' k)) hm)
        · have hne : Us.unitOf (Us.emb j' k) ≠ j := by
            rw [Us.unitOf_emb]
            exact fun h => hj (h ▸ hj')
          exact (sigStar_batch h1 (fun hm => hne ((hmem _).mp hm))).trans (hs' j' hj' k)
  obtain ⟨B, L, hLn, hLm, hLb, hsig⟩ := key Finset.univ.toList (Finset.nodup_toList _)
  have hLp : L.Perm Finset.univ.toList := by
    refine List.perm_of_nodup_nodup_toFinset_eq hLn (Finset.nodup_toList _) ?_
    ext i
    simp only [List.mem_toFinset, hLm, Finset.mem_toList, Finset.mem_univ]
  obtain ⟨usB, hRB⟩ := batch_reachU (Qm := Us.Q) hLb us
  refine ⟨⟨B, usB⟩, ⟨L, hLp, hRB⟩, fun j k => ?_⟩
  rw [hsig j (Finset.mem_toList.mpr (Finset.mem_univ j)) k, ← hZe j]
  rfl

end WaveTurbulence.VineC
