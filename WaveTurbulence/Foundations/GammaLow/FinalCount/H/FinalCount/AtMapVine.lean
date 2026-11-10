/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AtMapVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.Invariance
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AtMapVine`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # ATOM-TRANSPORT, part 2: vines, chains, VC/HV/HVC/DV, hyper realizations

For `ι : V ↪ W`: `IsVine` (all eight types, with the F72 template for (II)), `IsSomeVine`, `Chain`, `IsVC`, `IsHV`,
`IsHVC`, `IsDV` and `HyperLikeRealization` correspond along `S ↦ S.map ι` in both directions
(`*_mapAtoms` iff lemmas, and `exists_*_of_mapAtoms` for an arbitrary object of `mapAtoms M ι`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.AtomTransport
open WaveTurbulence WaveTurbulence.MoleProp WaveTurbulence.LGSpine.SourceVine

variable {V W D : Type*} [DecidableEq V] [DecidableEq W] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) (ι : V ↪ W)

/-! ### Vines -/

/-- T-vines correspond along `mapAtoms` (L6-HASM: low family; H-TV's `isTVine_map`, forward along `ι`, backward
along a left inverse of `ι`; bond counts and blocks by main's `mapAtoms_bondsBetween`, `mapAtoms_isBlock`). -/
theorem mapAtoms_isTVine (S : Finset V) (a b : V) :
    (mapAtoms M ι).IsTVine (S.map ι) (ι a) (ι b) ↔ M.IsTVine S a b := by
  constructor
  · intro h
    have : Nonempty V := ⟨a⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : W → V, ∀ x, φ (ι x) = x :=
      ⟨Function.invFun ι, Function.leftInverse_invFun ι.injective⟩
    have hinj : Set.InjOn φ ↑(S.map ι) := by
      intro u hu v hv huv
      obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hu)
      obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hv)
      rw [hφ, hφ] at huv; rw [huv]
    have hS : S = (S.map ι).image φ := by
      ext x
      simp only [Finset.mem_image, Finset.mem_map]
      constructor
      · intro hx; exact ⟨ι x, ⟨x, hx, rfl⟩, hφ x⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; rwa [hφ]
    have hbb : ∀ u ∈ S.map ι, ∀ v ∈ S.map ι, M.bondsBetween (φ u) (φ v) = (mapAtoms M ι).bondsBetween u v := by
      intro u hu v hv
      obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hv
      rw [hφ, hφ, mapAtoms_bondsBetween]
    have hB : M.IsBlock S (φ (ι a)) (φ (ι b)) := by rw [hφ, hφ]; exact (mapAtoms_isBlock M ι S a b).mp h.1
    have h' := TV.isTVine_map hinj hS hbb hB h
    rwa [hφ, hφ] at h'
  · intro h
    exact TV.isTVine_map (fun x _ y _ e => ι.injective e) (Finset.map_eq_image ι S)
      (fun u _ v _ => mapAtoms_bondsBetween M ι u v) ((mapAtoms_isBlock M ι S a b).mpr h.1) h

theorem mapAtoms_isVineEnl (S : Finset V) (a b : V) :
    (mapAtoms M ι).IsVineEnl (S.map ι) (ι a) (ι b) ↔ M.IsVineEnl S a b := by
  unfold Molecule.IsVineEnl
  rw [mapAtoms_isVine, mapAtoms_isVine, mapAtoms_isTVine]

theorem mapAtoms_isVineGamma (γ : ℝ) (S : Finset V) (a b : V) :
    (mapAtoms M ι).IsVineGamma γ (S.map ι) (ι a) (ι b) ↔ M.IsVineGamma γ S a b := by
  unfold Molecule.IsVineGamma
  rw [mapAtoms_isVineEnl]
  exact or_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun X => mapAtoms_isVine M ι X S a b))

theorem exists_isVineGamma_of_mapAtoms {γ : ℝ} {S' : Finset W} {a' b' : W}
    (h : (mapAtoms M ι).IsVineGamma γ S' a' b') :
    ∃ S a b, S' = S.map ι ∧ a' = ι a ∧ b' = ι b ∧ M.IsVineGamma γ S a b := by
  obtain ⟨S, a, b, rfl, rfl, rfl, -⟩ :=
    exists_isBlock_of_mapAtoms M ι (Src.IsSomeVine.block (γ := γ) (M := mapAtoms M ι) h)
  exact ⟨S, a, b, rfl, rfl, rfl, (mapAtoms_isVineGamma M ι γ S a b).mp h⟩

theorem mapAtoms_isSomeVine (S : Finset V) (a b : V) :
    Src.IsSomeVine Src.γL (mapAtoms M ι) (S.map ι) (ι a) (ι b) ↔ Src.IsSomeVine Src.γL M S a b :=
  mapAtoms_isVineGamma M ι Src.γL S a b

theorem exists_isSomeVine_of_mapAtoms {S' : Finset W} {a' b' : W} (h : Src.IsSomeVine Src.γL (mapAtoms M ι) S' a' b') :
    ∃ S a b, S' = S.map ι ∧ a' = ι a ∧ b' = ι b ∧ Src.IsSomeVine Src.γL M S a b :=
  exists_isVineGamma_of_mapAtoms M ι h

/-! ### Chains, VC, DV -/

theorem chain_map {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain Src.γL M S a b n) :
    Src.Chain Src.γL (mapAtoms M ι) (S.map ι) (ι a) (ι b) n := by
  induction h with
  | single hv => exact Src.Chain.single ((mapAtoms_isSomeVine M ι _ _ _).mpr hv)
  | append _ hv hint hne ih =>
    rw [Finset.map_union]
    refine Src.Chain.append ih ((mapAtoms_isSomeVine M ι _ _ _).mpr hv) ?_ (fun e => hne (ι.injective e))
    rw [← Finset.map_inter, hint]; rfl

theorem exists_chain_of_mapAtoms {S' : Finset W} {a' b' : W} {n : ℕ} (h : Src.Chain Src.γL (mapAtoms M ι) S' a' b' n) :
    ∃ S a b, S' = S.map ι ∧ a' = ι a ∧ b' = ι b ∧ Src.Chain Src.γL M S a b n := by
  induction h with
  | single hv =>
    obtain ⟨S, a, b, h1, h2, h3, h4⟩ := exists_isSomeVine_of_mapAtoms M ι hv
    exact ⟨S, a, b, h1, h2, h3, Src.Chain.single h4⟩
  | @append S' T' a' b' c' n _ hv hint hne ih =>
    obtain ⟨S, a, b, rfl, rfl, rfl, hc⟩ := ih
    obtain ⟨T, b2, c, rfl, hb2, rfl, hT⟩ := exists_isSomeVine_of_mapAtoms M ι hv
    have hb : b = b2 := ι.injective hb2
    subst hb
    refine ⟨S ∪ T, a, c, by rw [Finset.map_union], rfl, rfl, Src.Chain.append hc hT ?_ (fun e => hne (e ▸ rfl))⟩
    rw [← Finset.map_inter] at hint
    exact Finset.map_injective ι (by rw [hint]; rfl)

theorem mapAtoms_chain (S : Finset V) (a b : V) (n : ℕ) :
    Src.Chain Src.γL (mapAtoms M ι) (S.map ι) (ι a) (ι b) n ↔ Src.Chain Src.γL M S a b n := by
  refine ⟨fun h => ?_, chain_map M ι⟩
  obtain ⟨S₂, a₂, b₂, h1, h2, h3, h4⟩ := exists_chain_of_mapAtoms M ι h
  rw [Finset.map_inj] at h1
  rw [ι.injective.eq_iff] at h2 h3
  subst h1 h2 h3; exact h4

theorem mapAtoms_isVC (S : Finset V) (a b : V) :
    Src.IsVC Src.γL (mapAtoms M ι) (S.map ι) (ι a) (ι b) ↔ Src.IsVC Src.γL M S a b := by
  unfold Src.IsVC
  rw [mapAtoms_isBlock]
  simp only [mapAtoms_chain]

theorem exists_isVC_of_mapAtoms {S' : Finset W} {a' b' : W} (h : Src.IsVC Src.γL (mapAtoms M ι) S' a' b') :
    ∃ S a b, S' = S.map ι ∧ a' = ι a ∧ b' = ι b ∧ Src.IsVC Src.γL M S a b := by
  obtain ⟨S, a, b, rfl, rfl, rfl, -⟩ := exists_isBlock_of_mapAtoms M ι h.1
  exact ⟨S, a, b, rfl, rfl, rfl, (mapAtoms_isVC M ι S a b).mp h⟩

theorem mapAtoms_isDV (S : Finset V) (a b : V) :
    Src.IsDV Src.γL (mapAtoms M ι) (S.map ι) (ι a) (ι b) ↔ Src.IsDV Src.γL M S a b := by
  unfold Src.IsDV Molecule.IsDVPrime
  rw [show (mapAtoms M ι).sigma (ι a) (ι b) = M.sigma a b from mapAtoms_bondsBetween M ι a b]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨A', B', hA, hB, hint, hS⟩
    obtain ⟨A, a1, b1, rfl, h1, h2, hA⟩ := exists_isVineGamma_of_mapAtoms M ι hA
    obtain ⟨B, a2, b2, rfl, h3, h4, hB⟩ := exists_isVineGamma_of_mapAtoms M ι hB
    rw [ι.injective.eq_iff] at h1 h2 h3 h4
    subst h1 h2 h3 h4
    refine ⟨A, B, hA, hB, ?_, ?_⟩
    · rw [← Finset.map_inter] at hint
      exact Finset.map_injective ι (by rw [hint]; simp [Finset.map_insert])
    · rw [← Finset.map_union] at hS
      exact Finset.map_injective ι hS
  · rintro ⟨A, B, hA, hB, hint, rfl⟩
    refine ⟨A.map ι, B.map ι, (mapAtoms_isVineGamma M ι _ A a b).mpr hA, (mapAtoms_isVineGamma M ι _ B a b).mpr hB,
      ?_, Finset.map_union _ _⟩
    rw [← Finset.map_inter, hint]; simp [Finset.map_insert]

theorem exists_isDV_of_mapAtoms {S' : Finset W} {a' b' : W} (h : Src.IsDV Src.γL (mapAtoms M ι) S' a' b') :
    ∃ S a b, S' = S.map ι ∧ a' = ι a ∧ b' = ι b ∧ Src.IsDV Src.γL M S a b := by
  obtain ⟨hσ, A', B', hA, hB, hint, rfl⟩ := h
  obtain ⟨A, a1, b1, rfl, rfl, rfl, hA2⟩ := exists_isVineGamma_of_mapAtoms M ι hA
  obtain ⟨B, a2, b2, rfl, h3, h4, hB2⟩ := exists_isVineGamma_of_mapAtoms M ι hB
  rw [ι.injective.eq_iff] at h3 h4
  subst h3 h4
  refine ⟨A ∪ B, a1, b1, by rw [Finset.map_union], rfl, rfl, ?_, A, B, hA2, hB2, ?_, rfl⟩
  · rw [← show (mapAtoms M ι).sigma (ι a1) (ι b1) = M.sigma a1 b1 from mapAtoms_bondsBetween M ι a1 b1]; exact hσ
  · rw [← Finset.map_inter] at hint
    exact Finset.map_injective ι (by rw [hint]; simp [Finset.map_insert])

end WaveTurbulence.GammaLow.FinalCount.H
