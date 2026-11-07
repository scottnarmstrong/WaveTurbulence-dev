/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AtMapBasic
import Mathlib.Tactic

/-! # ATOM-TRANSPORT, part 2: vines, chains, VC/HV/HVC/DV, hyper realizations

For `ι : V ↪ W`: `IsVine` (all eight types, with the F72 template for (II)), `IsSomeVine`, `Chain`, `IsVC`, `IsHV`,
`IsHVC`, `IsDV` and `HyperLikeRealization` correspond along `S ↦ S.map ι` in both directions
(`*_mapAtoms` iff lemmas, and `exists_*_of_mapAtoms` for an arbitrary object of `mapAtoms M ι`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.AtomTransport
open WaveTurbulence WaveTurbulence.MoleProp WaveTurbulence.LGSpine.SourceVine

variable {V W D : Type*} [DecidableEq V] [DecidableEq W] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) (ι : V ↪ W)

/-! ### Vines -/

/-- The vine data on `S.map ι` for `f'` is the vine data on `S` for `f' ∘ ι`. -/
theorem vineData_iff (X : VineType) (k : List ℕ) (S : Finset V) (j₁ j₂ : V) (f' : W → ℕ) :
    (Set.InjOn f' ↑(S.map ι) ∧ (S.map ι).image f' = Finset.range (X.expand k).n ∧
      ({f' (ι j₁), f' (ι j₂)} : Finset ℕ) = {0, 1} ∧
      ((mapAtoms M ι).groupBonds (S.map ι)).map (Sym2.map f') =
        ((X.expand k).bonds.map fun p => s(p.1, p.2) : Multiset _)) ↔
    (Set.InjOn (f' ∘ ι) ↑S ∧ S.image (f' ∘ ι) = Finset.range (X.expand k).n ∧
      ({(f' ∘ ι) j₁, (f' ∘ ι) j₂} : Finset ℕ) = {0, 1} ∧
      (M.groupBonds S).map (Sym2.map (f' ∘ ι)) =
        ((X.expand k).bonds.map fun p => s(p.1, p.2) : Multiset _)) := by
  have h1 : Set.InjOn f' ↑(S.map ι) ↔ Set.InjOn (f' ∘ ι) ↑S := by
    constructor
    · intro h x hx y hy hxy
      exact ι.injective (@h (ι x) (by simpa using hx) (ι y) (by simpa using hy) hxy)
    · intro h x hx y hy hxy
      obtain ⟨x, hx2, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
      obtain ⟨y, hy2, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
      rw [h (Finset.mem_coe.mpr hx2) (Finset.mem_coe.mpr hy2) hxy]
  have h2 : (S.map ι).image f' = S.image (f' ∘ ι) := by
    rw [Finset.map_eq_image, Finset.image_image]
  have h3 : ((mapAtoms M ι).groupBonds (S.map ι)).map (Sym2.map f') =
      (M.groupBonds S).map (Sym2.map (f' ∘ ι)) := by
    rw [mapAtoms_groupBonds, Multiset.map_map]
    congr 1
    funext z
    simp [Sym2.map_map]
  rw [h1, h2, h3]
  rfl

theorem mapAtoms_isVine (X : VineType) (S : Finset V) (j₁ j₂ : V) :
    (mapAtoms M ι).IsVine X (S.map ι) (ι j₁) (ι j₂) ↔ M.IsVine X S j₁ j₂ := by
  unfold Molecule.IsVine
  rw [mapAtoms_isBlock]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨k, hk, f', hf⟩
    exact ⟨k, hk, f' ∘ ι, (vineData_iff M ι X k S j₁ j₂ f').mp hf⟩
  · rintro ⟨k, hk, f, hf⟩
    refine ⟨k, hk, Function.extend ι f (fun _ => 0), ?_⟩
    rw [vineData_iff]
    have : (Function.extend ι f (fun _ => 0)) ∘ ι = f := funext fun a => ι.injective.extend_apply f _ a
    rw [this]; exact hf

theorem exists_isVine_of_mapAtoms {X : VineType} {S' : Finset W} {a' b' : W}
    (h : (mapAtoms M ι).IsVine X S' a' b') :
    ∃ S a b, S' = S.map ι ∧ a' = ι a ∧ b' = ι b ∧ M.IsVine X S a b := by
  obtain ⟨S, a, b, rfl, rfl, rfl, -⟩ := exists_isBlock_of_mapAtoms M ι h.1
  exact ⟨S, a, b, rfl, rfl, rfl, (mapAtoms_isVine M ι X S a b).mp h⟩

theorem mapAtoms_isSomeVine (S : Finset V) (a b : V) :
    IsSomeVine (mapAtoms M ι) (S.map ι) (ι a) (ι b) ↔ IsSomeVine M S a b := by
  unfold IsSomeVine
  exact exists_congr fun X => mapAtoms_isVine M ι X S a b

theorem exists_isSomeVine_of_mapAtoms {S' : Finset W} {a' b' : W} (h : IsSomeVine (mapAtoms M ι) S' a' b') :
    ∃ S a b, S' = S.map ι ∧ a' = ι a ∧ b' = ι b ∧ IsSomeVine M S a b := by
  obtain ⟨X, hX⟩ := h
  obtain ⟨S, a, b, h1, h2, h3, h4⟩ := exists_isVine_of_mapAtoms M ι hX
  exact ⟨S, a, b, h1, h2, h3, X, h4⟩

/-! ### Chains, VC, DV -/

theorem chain_map {S : Finset V} {a b : V} {n : ℕ} (h : Chain M S a b n) :
    Chain (mapAtoms M ι) (S.map ι) (ι a) (ι b) n := by
  induction h with
  | single hv => exact Chain.single ((mapAtoms_isSomeVine M ι _ _ _).mpr hv)
  | append _ hv hint hne ih =>
    rw [Finset.map_union]
    refine Chain.append ih ((mapAtoms_isSomeVine M ι _ _ _).mpr hv) ?_ (fun e => hne (ι.injective e))
    rw [← Finset.map_inter, hint]; rfl

theorem exists_chain_of_mapAtoms {S' : Finset W} {a' b' : W} {n : ℕ} (h : Chain (mapAtoms M ι) S' a' b' n) :
    ∃ S a b, S' = S.map ι ∧ a' = ι a ∧ b' = ι b ∧ Chain M S a b n := by
  induction h with
  | single hv =>
    obtain ⟨S, a, b, h1, h2, h3, h4⟩ := exists_isSomeVine_of_mapAtoms M ι hv
    exact ⟨S, a, b, h1, h2, h3, Chain.single h4⟩
  | @append S' T' a' b' c' n _ hv hint hne ih =>
    obtain ⟨S, a, b, rfl, rfl, rfl, hc⟩ := ih
    obtain ⟨T, b2, c, rfl, hb2, rfl, hT⟩ := exists_isSomeVine_of_mapAtoms M ι hv
    have hb : b = b2 := ι.injective hb2
    subst hb
    refine ⟨S ∪ T, a, c, by rw [Finset.map_union], rfl, rfl, Chain.append hc hT ?_ (fun e => hne (e ▸ rfl))⟩
    rw [← Finset.map_inter] at hint
    exact Finset.map_injective ι (by rw [hint]; rfl)

theorem mapAtoms_chain (S : Finset V) (a b : V) (n : ℕ) :
    Chain (mapAtoms M ι) (S.map ι) (ι a) (ι b) n ↔ Chain M S a b n := by
  refine ⟨fun h => ?_, chain_map M ι⟩
  obtain ⟨S₂, a₂, b₂, h1, h2, h3, h4⟩ := exists_chain_of_mapAtoms M ι h
  rw [Finset.map_inj] at h1
  rw [ι.injective.eq_iff] at h2 h3
  subst h1 h2 h3; exact h4

theorem mapAtoms_isVC (S : Finset V) (a b : V) :
    IsVC (mapAtoms M ι) (S.map ι) (ι a) (ι b) ↔ IsVC M S a b := by
  unfold IsVC
  rw [mapAtoms_isBlock]
  simp only [mapAtoms_chain]

theorem exists_isVC_of_mapAtoms {S' : Finset W} {a' b' : W} (h : IsVC (mapAtoms M ι) S' a' b') :
    ∃ S a b, S' = S.map ι ∧ a' = ι a ∧ b' = ι b ∧ IsVC M S a b := by
  obtain ⟨S, a, b, rfl, rfl, rfl, -⟩ := exists_isBlock_of_mapAtoms M ι h.1
  exact ⟨S, a, b, rfl, rfl, rfl, (mapAtoms_isVC M ι S a b).mp h⟩

theorem mapAtoms_isDV (S : Finset V) (a b : V) :
    IsDV (mapAtoms M ι) (S.map ι) (ι a) (ι b) ↔ IsDV M S a b := by
  unfold IsDV
  constructor
  · rintro ⟨A', B', hA, hB, hint, hS⟩
    obtain ⟨A, a1, b1, rfl, h1, h2, hA⟩ := exists_isVine_of_mapAtoms M ι hA
    obtain ⟨B, a2, b2, rfl, h3, h4, hB⟩ := exists_isVine_of_mapAtoms M ι hB
    rw [ι.injective.eq_iff] at h1 h2 h3 h4
    subst h1 h2 h3 h4
    refine ⟨A, B, hA, hB, ?_, ?_⟩
    · rw [← Finset.map_inter] at hint
      exact Finset.map_injective ι (by rw [hint]; simp [Finset.map_insert])
    · rw [← Finset.map_union] at hS
      exact Finset.map_injective ι hS
  · rintro ⟨A, B, hA, hB, hint, rfl⟩
    refine ⟨A.map ι, B.map ι, (mapAtoms_isVine M ι _ A a b).mpr hA, (mapAtoms_isVine M ι _ B a b).mpr hB,
      ?_, Finset.map_union _ _⟩
    rw [← Finset.map_inter, hint]; simp [Finset.map_insert]

theorem exists_isDV_of_mapAtoms {S' : Finset W} {a' b' : W} (h : IsDV (mapAtoms M ι) S' a' b') :
    ∃ S a b, S' = S.map ι ∧ a' = ι a ∧ b' = ι b ∧ IsDV M S a b := by
  obtain ⟨A', B', hA, hB, hint, rfl⟩ := h
  obtain ⟨A, a1, b1, rfl, rfl, rfl, hA2⟩ := exists_isVine_of_mapAtoms M ι hA
  obtain ⟨B, a2, b2, rfl, h3, h4, hB2⟩ := exists_isVine_of_mapAtoms M ι hB
  rw [ι.injective.eq_iff] at h3 h4
  subst h3 h4
  refine ⟨A ∪ B, a1, b1, by rw [Finset.map_union], rfl, rfl, A, B, hA2, hB2, ?_, rfl⟩
  rw [← Finset.map_inter] at hint
  exact Finset.map_injective ι (by rw [hint]; simp [Finset.map_insert])

end WaveTurbulence.AtomTransport
