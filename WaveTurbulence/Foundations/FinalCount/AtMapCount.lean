/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AtMapBasic
import Mathlib.Tactic

/-! # ATOM-TRANSPORT, part 4: decorations, ladders, `rho`, `countE`, `countA`

`mapAtoms M ι` has the same darts as `M`, so a decoration `κ : D → (Fin d → ℤ)` and an admissibility predicate
`Adm` on decorations are literally shared.  We prove, for `ι : V ↪ W`:
* `IsDecoration`, `Gamma`, `IsRestricted` correspond (with `c' ∘ ι`, `β' ∘ ι`);
* ladders and maximal ladders correspond (`maximalLadders (mapAtoms M ι) = (maximalLadders M).image (map ι)`);
* `numLadders`, `numFree`, `rho` and `circuitRank` are invariant;
* `countE` is invariant, and `countA (mapAtoms M ι) … Adm P' = countA M … Adm (P' ∘ map ι)`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.AtomTransport
open WaveTurbulence WaveTurbulence.MoleProp

variable {V W D : Type*} [DecidableEq V] [DecidableEq W] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) (ι : V ↪ W)

/-! ### Decorations -/

theorem mapAtoms_gamma (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (a : V) :
    (mapAtoms M ι).Gamma L w κ (ι a) = M.Gamma L w κ a := by
  unfold Molecule.Gamma
  rw [mapAtoms_dartsAt]; rfl

theorem mapAtoms_isDecoration (L : ℝ) (w : Mom d) (c' : W → Mom d) (κ : D → (Fin d → ℤ)) :
    (mapAtoms M ι).IsDecoration L w c' κ ↔ M.IsDecoration L w (c' ∘ ι) κ := by
  unfold Molecule.IsDecoration
  refine and_congr Iff.rfl ⟨fun h v hv => ?_, fun h v' hv' => ?_⟩
  · have := h (ι v) ((Finset.mem_map' ι).mpr hv)
    rwa [mapAtoms_dartsAt] at this
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hv'
    rw [mapAtoms_dartsAt]
    exact h v hv

theorem mapAtoms_isRestricted (L γ δ : ℝ) (w : Mom d) (β' : W → ℝ) (k0 : D → Mom d)
    (κ : D → (Fin d → ℤ)) :
    (mapAtoms M ι).IsRestricted L γ δ w β' k0 κ ↔ M.IsRestricted L γ δ w (β' ∘ ι) k0 κ := by
  unfold Molecule.IsRestricted
  refine and_congr ⟨fun h v hv => ?_, fun h v' hv' => ?_⟩ Iff.rfl
  · have := h (ι v) ((Finset.mem_map' ι).mpr hv)
    rwa [mapAtoms_gamma] at this
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hv'
    rw [mapAtoms_gamma]
    exact h v hv

/-! ### `countE` -/

theorem mapAtoms_countE (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    (mapAtoms M ι).countE L γ δ w Adm = M.countE L γ δ w Adm := by
  apply le_antisymm
  · unfold Molecule.countE
    refine iSup_le fun c' => iSup_le fun hc' => iSup_le fun β' => iSup_le fun k0 => iSup_le fun hk0 => ?_
    refine le_trans (Set.encard_mono (b := {κ | M.IsDecoration L w (c' ∘ ι) κ ∧
      M.IsRestricted L γ δ w (β' ∘ ι) k0 κ ∧ Adm κ}) ?_) ?_
    · rintro κ ⟨h1, h2, h3⟩
      exact ⟨(mapAtoms_isDecoration M ι L w c' κ).mp h1, (mapAtoms_isRestricted M ι L γ δ w β' k0 κ).mp h2, h3⟩
    · refine le_iSup_of_le (c' ∘ ι) (le_iSup_of_le ?_ (le_iSup_of_le (β' ∘ ι) (le_iSup_of_le k0
        (le_iSup_of_le hk0 le_rfl))))
      intro v hv h4
      exact hc' (ι v) ((Finset.mem_map' ι).mpr hv) (by rw [mapAtoms_deg]; exact h4)
  · unfold Molecule.countE
    refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
    obtain ⟨c', e1⟩ : ∃ c' : W → Mom d, c' ∘ ι = c :=
      ⟨Function.extend ι c (fun _ => 0), funext fun a => ι.injective.extend_apply c _ a⟩
    obtain ⟨β', e2⟩ : ∃ β' : W → ℝ, β' ∘ ι = β :=
      ⟨Function.extend ι β (fun _ => 0), funext fun a => ι.injective.extend_apply β _ a⟩
    refine le_trans (Set.encard_mono (b := {κ | (mapAtoms M ι).IsDecoration L w c' κ ∧
      (mapAtoms M ι).IsRestricted L γ δ w β' k0 κ ∧ Adm κ}) ?_) ?_
    · rintro κ ⟨h1, h2, h3⟩
      exact ⟨(mapAtoms_isDecoration M ι L w c' κ).mpr (by rwa [e1]),
        (mapAtoms_isRestricted M ι L γ δ w β' k0 κ).mpr (by rwa [e2]), h3⟩
    · refine le_iSup_of_le c' (le_iSup_of_le ?_ (le_iSup_of_le β' (le_iSup_of_le k0
        (le_iSup_of_le hk0 le_rfl))))
      intro v' hv' h4
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hv'
      rw [mapAtoms_deg] at h4
      have := hc v hv h4
      rwa [← e1] at this

/-! ### Ladders -/

theorem mapAtoms_ladderAtoms {m : ℕ} (u v : Fin (m + 1) → V) :
    Molecule.ladderAtoms (fun j => ι (u j)) (fun j => ι (v j)) = (Molecule.ladderAtoms u v).map ι := by
  unfold Molecule.ladderAtoms
  rw [Finset.map_union, Finset.map_eq_image, Finset.map_eq_image, Finset.image_image, Finset.image_image]
  rfl

theorem mapAtoms_isLadder {m : ℕ} (u v : Fin (m + 1) → V) :
    (mapAtoms M ι).IsLadder (fun j => ι (u j)) (fun j => ι (v j)) ↔ M.IsLadder u v := by
  unfold Molecule.IsLadder
  have hinj : Function.Injective (Sum.elim (fun j => ι (u j)) (fun j => ι (v j))) ↔
      Function.Injective (Sum.elim u v) := by
    have : Sum.elim (fun j => ι (u j)) (fun j => ι (v j)) = ι ∘ Sum.elim u v := by
      funext s; cases s <;> rfl
    rw [this]
    exact ⟨fun h => Function.Injective.of_comp h, fun h => ι.injective.comp h⟩
  have hmem : ∀ a, ι a ∈ (mapAtoms M ι).atoms ↔ a ∈ M.atoms := fun a => Finset.mem_map' ι
  simp only [hinj, hmem, mapAtoms_bondsBetween, mapAtoms_directed]

theorem mapAtoms_isLadderSet (S : Finset V) :
    (mapAtoms M ι).IsLadderSet (S.map ι) ↔ M.IsLadderSet S := by
  unfold Molecule.IsLadderSet
  constructor
  · rintro ⟨m, u', v', hl, hS⟩
    have hu : ∀ j, ∃ a, ι a = u' j := fun j => by
      obtain ⟨a, -, ha⟩ := Finset.mem_map.mp (hl.2.2.1 j).1
      exact ⟨a, ha⟩
    have hv : ∀ j, ∃ a, ι a = v' j := fun j => by
      obtain ⟨a, -, ha⟩ := Finset.mem_map.mp (hl.2.2.1 j).2
      exact ⟨a, ha⟩
    choose a ha using hu
    choose b hb using hv
    have hu' : u' = fun j => ι (a j) := funext fun j => (ha j).symm
    have hv' : v' = fun j => ι (b j) := funext fun j => (hb j).symm
    subst hu' hv'
    refine ⟨m, a, b, (mapAtoms_isLadder M ι a b).mp hl, ?_⟩
    rw [mapAtoms_ladderAtoms] at hS
    exact Finset.map_injective ι hS
  · rintro ⟨m, u, v, hl, hS⟩
    exact ⟨m, _, _, (mapAtoms_isLadder M ι u v).mpr hl, by rw [mapAtoms_ladderAtoms, hS]⟩

theorem exists_isLadderSet_of_mapAtoms {S' : Finset W} (h : (mapAtoms M ι).IsLadderSet S') :
    ∃ S, S' = S.map ι ∧ M.IsLadderSet S := by
  obtain ⟨m, u', v', hl, hS⟩ := h
  have hu : ∀ j, ∃ a, ι a = u' j := fun j => by
    obtain ⟨a, -, ha⟩ := Finset.mem_map.mp (hl.2.2.1 j).1
    exact ⟨a, ha⟩
  have hv : ∀ j, ∃ a, ι a = v' j := fun j => by
    obtain ⟨a, -, ha⟩ := Finset.mem_map.mp (hl.2.2.1 j).2
    exact ⟨a, ha⟩
  choose a ha using hu
  choose b hb using hv
  have hu' : u' = fun j => ι (a j) := funext fun j => (ha j).symm
  have hv' : v' = fun j => ι (b j) := funext fun j => (hb j).symm
  subst hu' hv'
  refine ⟨Molecule.ladderAtoms a b, by rw [← hS, mapAtoms_ladderAtoms], m, a, b,
    (mapAtoms_isLadder M ι a b).mp hl, rfl⟩

theorem exists_ladder_of_mapAtoms {m : ℕ} (u' v' : Fin (m + 1) → W) (hl : (mapAtoms M ι).IsLadder u' v') :
    ∃ u v : Fin (m + 1) → V, u' = (fun j => ι (u j)) ∧ v' = (fun j => ι (v j)) ∧ M.IsLadder u v := by
  have hu : ∀ j, ∃ a, ι a = u' j := fun j => by
    obtain ⟨a, -, ha⟩ := Finset.mem_map.mp (hl.2.2.1 j).1
    exact ⟨a, ha⟩
  have hv : ∀ j, ∃ a, ι a = v' j := fun j => by
    obtain ⟨a, -, ha⟩ := Finset.mem_map.mp (hl.2.2.1 j).2
    exact ⟨a, ha⟩
  choose a ha using hu
  choose b hb using hv
  have hu' : u' = fun j => ι (a j) := funext fun j => (ha j).symm
  have hv' : v' = fun j => ι (b j) := funext fun j => (hb j).symm
  subst hu' hv'
  exact ⟨a, b, rfl, rfl, (mapAtoms_isLadder M ι a b).mp hl⟩

theorem mapAtoms_isLadderGap {m : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (u v : Fin (m + 1) → V)
    (hm : 1 ≤ m) (r : Mom d) :
    (mapAtoms M ι).IsLadderGap L w κ (fun j => ι (u j)) (fun j => ι (v j)) hm r ↔
      M.IsLadderGap L w κ u v hm r := by
  unfold Molecule.IsLadderGap
  refine exists_congr fun x => exists_congr fun y => ?_
  rw [mapAtoms_ends_iff M ι x (u 0) (u ⟨1, by omega⟩), mapAtoms_ends_iff M ι y (v 0) (v ⟨1, by omega⟩)]
  simp only [mapAtoms_atom, ι.injective.eq_iff]

theorem mapAtoms_maximalLadders :
    (mapAtoms M ι).maximalLadders = M.maximalLadders.image (fun S => S.map ι) := by
  classical
  ext S'
  unfold Molecule.maximalLadders
  simp only [mem_filter, mem_powerset, mem_image]
  constructor
  · rintro ⟨hsub, hl, hmax⟩
    obtain ⟨S, rfl, hS⟩ := exists_isLadderSet_of_mapAtoms M ι hl
    refine ⟨S, ⟨?_, hS, fun T hT hST => ?_⟩, rfl⟩
    · exact Finset.map_subset_map.mp hsub
    · have := hmax (T.map ι) ((mapAtoms_isLadderSet M ι T).mpr hT) (Finset.map_subset_map.mpr hST)
      exact (Finset.map_injective ι this)
  · rintro ⟨S, ⟨hsub, hS, hmax⟩, rfl⟩
    refine ⟨Finset.map_subset_map.mpr hsub, (mapAtoms_isLadderSet M ι S).mpr hS, fun T' hT' hST' => ?_⟩
    obtain ⟨T, rfl, hT⟩ := exists_isLadderSet_of_mapAtoms M ι hT'
    rw [hmax T hT (Finset.map_subset_map.mp hST')]

theorem mapAtoms_numLadders : (mapAtoms M ι).numLadders = M.numLadders := by
  unfold Molecule.numLadders
  rw [mapAtoms_maximalLadders, Finset.card_image_of_injective _ (Finset.map_injective ι)]

theorem mapAtoms_numFree : (mapAtoms M ι).numFree = M.numFree := by
  classical
  unfold Molecule.numFree
  rw [← Finset.card_map ι]
  congr 1
  ext v'
  rw [Finset.mem_filter, Finset.mem_map]
  constructor
  · rintro ⟨hv', h⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hv'
    refine ⟨v, Finset.mem_filter.mpr ⟨hv, fun S hS hvS => h (S.map ι) ?_ ((Finset.mem_map' ι).mpr hvS)⟩, rfl⟩
    rw [mapAtoms_maximalLadders]; exact Finset.mem_image_of_mem _ hS
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hv, h⟩ := Finset.mem_filter.mp hv
    refine ⟨(Finset.mem_map' ι).mpr hv, fun S' hS' hvS' => ?_⟩
    rw [mapAtoms_maximalLadders] at hS'
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hS'
    exact h S hS ((Finset.mem_map' ι).mp hvS')

theorem mapAtoms_rho : (mapAtoms M ι).rho = M.rho := by
  unfold Molecule.rho
  rw [mapAtoms_numLadders, mapAtoms_numFree]

theorem mapAtoms_ladderLength (S : Finset V) : Molecule.ladderLength (S.map ι) = Molecule.ladderLength S := by
  unfold Molecule.ladderLength
  rw [Finset.card_map]

/-! ### `countA` -/

/-- **`countA` is invariant under an injective atom renaming**, with the same decorations `κ : D → …` and the
same admissibility predicate `Adm`; the ladder scale `P'` of `mapAtoms M ι` is read on the images of the atom
sets of the ladders of `M`. -/
theorem mapAtoms_countA (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P' : Finset W → ℝ) :
    (mapAtoms M ι).countA L γ δ C₁ w Adm P' = M.countA L γ δ C₁ w Adm (fun S => P' (S.map ι)) := by
  unfold Molecule.countA
  rw [mapAtoms_countE, mapAtoms_circuitRank, mapAtoms_maximalLadders,
    Finset.prod_image (fun a _ b _ h => Finset.map_injective ι h)]
  simp only [mapAtoms_ladderLength]

end WaveTurbulence.AtomTransport
