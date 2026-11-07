/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.SmallGapCase
import Mathlib.Tactic

/-! # The label count for a double pair with a small gap (DH23 L1975)

`𝔈(M) ≤ ⌈8 (2L+1)^d (2L λ+1)^d C δ⁻¹ L^{2(d−γ)}⌉ · 𝔈(M ∖ {v₁,v₂})`, `λ = L^{−γ+η}`: the six removed labels are
counted by fixing the close pair `(k_a, k_b)` and the triple `(p₁, p₂, a')` (`sixTuple_card_le`); there are eight cases
(which extra dart at each atom, and the sign).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.CountLemmas
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem cover44 (M : Molecule V D) {v₁ v₂ : V} {x y ex ex' ey ey' : D}
    (hA : M.dartsAt v₁ = {x, y, ex, ex'}) (hB : M.dartsAt v₂ = {M.mate x, M.mate y, ey, ey'}) :
    ∀ z : DeletedDart M {v₁, v₂}, ∃ i : Fin 6,
      z.val = (![x, y, ex, ex', ey, ey'] : Fin 6 → D) i ∨ z.val = M.mate ((![x, y, ex, ex', ey, ey'] : Fin 6 → D) i) := by
  apply deleted_cover_of_incident_cover
  intro z hz
  rcases mem_insert.mp hz with hz | hz
  · have hmem : z ∈ M.dartsAt v₁ := (Mole.mem_dartsAt M v₁ z).mpr hz
    rw [hA] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact ⟨0, Or.inl rfl⟩
    · exact ⟨1, Or.inl rfl⟩
    · exact ⟨2, Or.inl rfl⟩
    · exact ⟨3, Or.inl rfl⟩
  · have hmem : z ∈ M.dartsAt v₂ := (Mole.mem_dartsAt M v₂ z).mpr (mem_singleton.mp hz)
    rw [hB] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact ⟨0, Or.inr rfl⟩
    · exact ⟨1, Or.inr rfl⟩
    · exact ⟨4, Or.inl rfl⟩
    · exact ⟨5, Or.inl rfl⟩

theorem smallgap_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) {v₁ v₂ : V} (hv₁ : v₁ ∈ M.atoms) (hv₂ : v₂ ∈ M.atoms)
      (hne : v₁ ≠ v₂) (h1 : M.deg v₁ = 4) (h2 : M.deg v₂ = 4) (hbb : M.bondsBetween v₁ v₂ = 2)
      (Adm : (D → (Fin d → ℤ)) → Prop), (∀ κ, Adm κ → SmallPairGap M v₁ v₂ L γ η κ) →
      MoleProp.countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈8 * ((2 * L + 1) ^ d * (2 * (L * L ^ (-γ + η)) + 1) ^ d * (C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))))⌉₊ : ℕ∞) *
          MoleProp.countEFree (Degen.eraseAtoms M {v₁, v₂}) L γ δ (0 : Mom d)
            (MoleProp.erasedFreeAdmissibility M {v₁, v₂} Adm) := by
  classical
  obtain ⟨C, L₀, hC, h⟩ := smallgap_case_bound d hd γ hγ
  refine ⟨C, max L₀ 1, hC, fun L hL δ hδ V D _ _ _ M hcap v₁ v₂ hv₁ hv₂ hne h1 h2 hbb Adm hAdm => ?_⟩
  have hLL : L ≥ L₀ := (le_max_left _ _).trans hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hL)
  have hlam : 0 ≤ L ^ (-γ + η) := Real.rpow_nonneg hLp.le _
  obtain ⟨x, y, r₁, r₂, s₁, s₂, hxy, hxr1, hxr2, hyr1, hyr2, hrr, hmxy, hms1x, hms2x, hms1y, hms2y, hss,
    hxa, hxb, hya, hyb, hA, hB, _⟩ := stars44 M hne h1 h2 hbb
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let A := {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}
  have hf : A.Finite := (Mole.finite_restricted M hLp γ δ (0 : Mom d) β k0).subset (fun _ h => h.2.1)
  let F := hf.toFinset
  have hmem (κ) : κ ∈ F ↔ κ ∈ A := hf.mem_toFinset
  set Bd : ℝ := (2 * L + 1) ^ d * (2 * (L * L ^ (-γ + η)) + 1) ^ d * (C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) with hBd
  -- one case
  have case : ∀ (ex ex' ey ey' : D) (σ : ℤ), (σ = 1 ∨ σ = -1) →
      x ≠ ex → x ≠ ex' → y ≠ ex → y ≠ ex' → ex ≠ ex' → M.mate x ≠ ey → M.mate x ≠ ey' → M.mate y ≠ ey →
      M.mate y ≠ ey' → ey ≠ ey' → M.dartsAt v₁ = {x, y, ex, ex'} → M.dartsAt v₂ = {M.mate x, M.mate y, ey, ey'} →
      (((F.filter fun κ => ‖latticePoint L (κ ex) - (σ : ℝ) • latticePoint L (κ ey)‖ ≤ L ^ (-γ + η)).image
        (deletedLabels M {v₁, v₂})).card : ℝ) ≤ Bd := by
    intro ex ex' ey ey' σ hσ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hA' hB'
    set G := F.filter fun κ => ‖latticePoint L (κ ex) - (σ : ℝ) • latticePoint L (κ ey)‖ ≤ L ^ (-γ + η)
    have hlocal := card_deletedLabels_image_le_localLabels_image M {v₁, v₂} ![x, y, ex, ex', ey, ey']
      (cover44 M hA' hB') G (fun κ hκ => ((hmem κ).mp (mem_filter.mp hκ).1).1.1)
    have := h L hLL δ hδ (L ^ (-γ + η)) hlam M hcap hv₁ hv₂ hxy a1 a2 a3 a4 a5 hmxy a6 a7 a8 a9 a10 hA' hB' σ hσ c β k0 G
      (fun κ hκ => by
        obtain ⟨hF, hg⟩ := mem_filter.mp hκ
        have hκA := (hmem κ).mp hF
        exact ⟨hκA.1, hκA.2.1, hg⟩)
    exact (by exact_mod_cast hlocal : (_ : ℝ) ≤ _).trans this
  have hBd0 : 0 ≤ Bd := by have := hδ.1; positivity
  -- the eight cases
  let P : Finset ((D × D) × (D × D) × ℤ) :=
    ({(r₁, r₂), (r₂, r₁)} : Finset (D × D)) ×ˢ (({(s₁, s₂), (s₂, s₁)} : Finset (D × D)) ×ˢ ({1, -1} : Finset ℤ))
  let G : (D × D) × (D × D) × ℤ → Finset (D → Fin d → ℤ) := fun p =>
    F.filter fun κ => ‖latticePoint L (κ p.1.1) - ((p.2.2 : ℤ) : ℝ) • latticePoint L (κ p.2.1.1)‖ ≤ L ^ (-γ + η)
  have hr12 : M.dartsAt v₁ = {x, y, r₂, r₁} := by rw [hA]; ext z; simp only [mem_insert, mem_singleton]; tauto
  have hs12 : M.dartsAt v₂ = {M.mate x, M.mate y, s₂, s₁} := by rw [hB]; ext z; simp only [mem_insert, mem_singleton]; tauto
  have key : ∀ (p : (D × D) × (D × D) × ℤ) (ex ex' ey ey' : D) (σ : ℤ), p.1 = (ex, ex') → p.2.1 = (ey, ey') →
      p.2.2 = σ → (σ = 1 ∨ σ = -1) → x ≠ ex → x ≠ ex' → y ≠ ex → y ≠ ex' → ex ≠ ex' → M.mate x ≠ ey →
      M.mate x ≠ ey' → M.mate y ≠ ey → M.mate y ≠ ey' → ey ≠ ey' → M.dartsAt v₁ = {x, y, ex, ex'} →
      M.dartsAt v₂ = {M.mate x, M.mate y, ey, ey'} →
      (((G p).image (deletedLabels M {v₁, v₂})).card : ℝ) ≤ Bd := by
    intro p ex ex' ey ey' σ h1 h2 h3 hσ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hA' hB'
    have := case ex ex' ey ey' σ hσ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hA' hB'
    simpa only [G, h1, h2, h3] using this
  have hPcard : ∀ p ∈ P, (((G p).image (deletedLabels M {v₁, v₂})).card : ℝ) ≤ Bd := by
    intro p hp
    simp only [P, mem_product, mem_insert, mem_singleton] at hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2 <;> rcases hp3 with h3 | h3
    · exact key p r₁ r₂ s₁ s₂ 1 h1 h2 h3 (Or.inl rfl) hxr1 hxr2 hyr1 hyr2 hrr hms1x hms2x hms1y hms2y hss hA hB
    · exact key p r₁ r₂ s₁ s₂ (-1) h1 h2 h3 (Or.inr rfl) hxr1 hxr2 hyr1 hyr2 hrr hms1x hms2x hms1y hms2y hss hA hB
    · exact key p r₁ r₂ s₂ s₁ 1 h1 h2 h3 (Or.inl rfl) hxr1 hxr2 hyr1 hyr2 hrr hms2x hms1x hms2y hms1y hss.symm hA hs12
    · exact key p r₁ r₂ s₂ s₁ (-1) h1 h2 h3 (Or.inr rfl) hxr1 hxr2 hyr1 hyr2 hrr hms2x hms1x hms2y hms1y hss.symm hA hs12
    · exact key p r₂ r₁ s₁ s₂ 1 h1 h2 h3 (Or.inl rfl) hxr2 hxr1 hyr2 hyr1 hrr.symm hms1x hms2x hms1y hms2y hss hr12 hB
    · exact key p r₂ r₁ s₁ s₂ (-1) h1 h2 h3 (Or.inr rfl) hxr2 hxr1 hyr2 hyr1 hrr.symm hms1x hms2x hms1y hms2y hss hr12 hB
    · exact key p r₂ r₁ s₂ s₁ 1 h1 h2 h3 (Or.inl rfl) hxr2 hxr1 hyr2 hyr1 hrr.symm hms2x hms1x hms2y hms1y hss.symm hr12 hs12
    · exact key p r₂ r₁ s₂ s₁ (-1) h1 h2 h3 (Or.inr rfl) hxr2 hxr1 hyr2 hyr1 hrr.symm hms2x hms1x hms2y hms1y hss.symm hr12 hs12
  have hcov : ∀ κ ∈ F, ∃ p ∈ P, κ ∈ G p := by
    intro κ hκ
    have hκA := (hmem κ).mp hκ
    obtain ⟨ex0, ey0, hex0, hnex, hey0, hney, hgap⟩ := hAdm κ hκA.2.2
    have hex0A : ex0 ∈ M.dartsAt v₁ := (Mole.mem_dartsAt M v₁ ex0).mpr hex0
    have hey0B : ey0 ∈ M.dartsAt v₂ := (Mole.mem_dartsAt M v₂ ey0).mpr hey0
    rw [hA] at hex0A
    rw [hB] at hey0B
    simp only [mem_insert, mem_singleton] at hex0A hey0B
    have hex : ex0 = r₁ ∨ ex0 = r₂ := by
      rcases hex0A with rfl | rfl | h | h
      · exact absurd hxb hnex
      · exact absurd hyb hnex
      · exact Or.inl h
      · exact Or.inr h
    have hey : ey0 = s₁ ∨ ey0 = s₂ := by
      rcases hey0B with rfl | rfl | h | h
      · exact absurd (by rw [M.mate_mate]; exact hxa) hney
      · exact absurd (by rw [M.mate_mate]; exact hya) hney
      · exact Or.inl h
      · exact Or.inr h
    have hlp : ∀ z, Molecule.kvec L (0 : Mom d) κ z = latticePoint L (κ z) := fun z => by
      simp [Molecule.kvec]
    rcases hex with rfl | rfl <;> rcases hey with rfl | rfl <;> rcases hgap with hg | hg
    · exact ⟨((ex0, r₂), (ey0, s₂), 1), by simp [P], mem_filter.mpr ⟨hκ, by simpa [hlp] using hg⟩⟩
    · exact ⟨((ex0, r₂), (ey0, s₂), -1), by simp [P], mem_filter.mpr ⟨hκ, by simpa [hlp, sub_neg_eq_add] using hg⟩⟩
    · exact ⟨((ex0, r₂), (ey0, s₁), 1), by simp [P], mem_filter.mpr ⟨hκ, by simpa [hlp] using hg⟩⟩
    · exact ⟨((ex0, r₂), (ey0, s₁), -1), by simp [P], mem_filter.mpr ⟨hκ, by simpa [hlp, sub_neg_eq_add] using hg⟩⟩
    · exact ⟨((ex0, r₁), (ey0, s₂), 1), by simp [P], mem_filter.mpr ⟨hκ, by simpa [hlp] using hg⟩⟩
    · exact ⟨((ex0, r₁), (ey0, s₂), -1), by simp [P], mem_filter.mpr ⟨hκ, by simpa [hlp, sub_neg_eq_add] using hg⟩⟩
    · exact ⟨((ex0, r₁), (ey0, s₁), 1), by simp [P], mem_filter.mpr ⟨hκ, by simpa [hlp] using hg⟩⟩
    · exact ⟨((ex0, r₁), (ey0, s₁), -1), by simp [P], mem_filter.mpr ⟨hκ, by simpa [hlp, sub_neg_eq_add] using hg⟩⟩
  have hcard8 : (F.image (deletedLabels M {v₁, v₂})).card ≤ ∑ p ∈ P, ((G p).image (deletedLabels M {v₁, v₂})).card := by
    refine (card_le_card ?_).trans card_biUnion_le
    intro q hq
    obtain ⟨κ, hκ, rfl⟩ := mem_image.mp hq
    obtain ⟨p, hp, hκp⟩ := hcov κ hκ
    exact mem_biUnion.mpr ⟨p, hp, mem_image_of_mem _ hκp⟩
  have hPle : (P.card : ℝ) ≤ 8 := by
    have h2 : ∀ a b : D × D, ({a, b} : Finset (D × D)).card ≤ 2 := fun a b => card_le_two
    have h2' : ∀ a b : ℤ, ({a, b} : Finset ℤ).card ≤ 2 := fun a b => card_le_two
    have : P.card ≤ 8 := by
      simp only [P, card_product]
      have := Nat.mul_le_mul (h2 (r₁, r₂) (r₂, r₁)) (Nat.mul_le_mul (h2 (s₁, s₂) (s₂, s₁)) (h2' 1 (-1)))
      omega
    exact_mod_cast this
  have hnat : ((F.image (deletedLabels M {v₁, v₂})).card : ℝ) ≤ 8 * Bd := by
    calc ((F.image (deletedLabels M {v₁, v₂})).card : ℝ)
        ≤ ((∑ p ∈ P, ((G p).image (deletedLabels M {v₁, v₂})).card : ℕ) : ℝ) := by exact_mod_cast hcard8
      _ = ∑ p ∈ P, (((G p).image (deletedLabels M {v₁, v₂})).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _p ∈ P, Bd := sum_le_sum hPcard
      _ = (P.card : ℝ) * Bd := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 8 * Bd := mul_le_mul_of_nonneg_right hPle hBd0
  have hImage : (deletedLabels M {v₁, v₂} '' A).ncard = (F.image (deletedLabels M {v₁, v₂})).card := by
    have he : deletedLabels M {v₁, v₂} '' A = (F.image (deletedLabels M {v₁, v₂}) : Set _) := by
      rw [Finset.coe_image, hf.coe_toFinset]
    rw [he, Set.ncard_coe_finset]
  have hceil : (deletedLabels M {v₁, v₂} '' A).ncard ≤ ⌈8 * Bd⌉₊ := by
    rw [hImage]; exact_mod_cast hnat.trans (Nat.le_ceil _)
  have hEN : ((deletedLabels M {v₁, v₂} '' A).ncard : ℕ∞) ≤ (⌈8 * Bd⌉₊ : ℕ∞) := by exact_mod_cast hceil
  exact (encard_le_deletedImage_mul_post M {v₁, v₂} hLp γ δ (0 : Mom d) Adm c β k0 hk0).trans
    (mul_le_mul_of_nonneg_right hEN bot_le)

end WaveTurbulence.FinalCountG8
