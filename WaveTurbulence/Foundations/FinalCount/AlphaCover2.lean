/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AlphaCover
/-! The `α`-cut (FINALCOUNT-G2 step 4), part 3: the cover. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

/-- The centre of the energy window for the gap `latticePoint L n`. -/
noncomputable def alphaCenter (L τ : ℝ) (s₀ : Mom d) (n : Fin d → ℤ) : ℝ :=
  -(inner ℝ (latticePoint L n) s₀) / τ

/-- The window indices for the gap `n`. -/
noncomputable def alphaJ (L τ R : ℝ) (s₀ : Mom d) (n : Fin d → ℤ) : Finset ℤ :=
  Finset.Icc ⌊alphaCenter L τ s₀ n - (1 / 2 + 4 * R / τ)⌋ ⌈alphaCenter L τ s₀ n + (1 / 2 + 4 * R / τ)⌉

/-- The gaps `n` with `‖latticePoint L n - r₀‖ ≤ ρ` lie in this box. -/
noncomputable def alphaN (d : ℕ) (L : ℝ) (r₀ : Mom d) (ρ : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc ⌈L * r₀ i - ρ * L⌉ ⌊L * r₀ i + ρ * L⌋

/-- The index set of the post classes. -/
noncomputable def alphaIndex (d : ℕ) (L τ R : ℝ) (s₀ r₀ : Mom d) (ρ : ℝ) : Finset ((Fin d → ℤ) × ℤ × ℤ) :=
  (alphaN d L r₀ ρ).biUnion fun n => ((alphaJ L τ R s₀ n) ×ˢ ({-1, 1} : Finset ℤ)).image (fun p => (n, p.1, p.2))

theorem mem_alphaIndex {L τ R : ℝ} {s₀ r₀ : Mom d} {ρ : ℝ} {n : Fin d → ℤ} {j e : ℤ} :
    (n, j, e) ∈ alphaIndex d L τ R s₀ r₀ ρ ↔ n ∈ alphaN d L r₀ ρ ∧ j ∈ alphaJ L τ R s₀ n ∧ e ∈ ({-1, 1} : Finset ℤ) := by
  unfold alphaIndex
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product, Prod.mk.injEq]
  constructor
  · rintro ⟨n', hn', ⟨j', e'⟩, ⟨hj, he⟩, rfl, rfl, rfl⟩
    exact ⟨hn', hj, he⟩
  · rintro ⟨hn, hj, he⟩
    exact ⟨n, hn, (j, e), ⟨hj, he⟩, rfl, rfl, rfl⟩

theorem alpha_cover (hcd : M.IsCutData v v₂ x₁ x₂) (L γ δ : ℝ) (hδ : 0 < δ) (hL : 0 < L) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (R : ℝ) (hgap : ∀ κ, Adm κ → ‖Molecule.gapAt L w κ x₁ x₂‖ ≤ 2 * R)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (r₀ : Mom d) (ρ : ℝ)
    (hball : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ x₁ x₂ - r₀‖ ≤ ρ) :
    decSet M L γ δ w Adm c β k0 ⊆
      ⋃ i ∈ alphaIndex d L (δ⁻¹ * L ^ (-2 * γ)) R (k0 x₁ + k0 x₂) r₀ ρ, decSet (M.cut v v₂ x₁ x₂) L γ δ w Adm
        (alphaParams v v₂ L (δ⁻¹ * L ^ (-2 * γ)) c β k0 i.1 i.2.1 i.2.2).1
        (alphaParams v v₂ L (δ⁻¹ * L ^ (-2 * γ)) c β k0 i.1 i.2.1 i.2.2).2.1
        (alphaParams v v₂ L (δ⁻¹ * L ^ (-2 * γ)) c β k0 i.1 i.2.1 i.2.2).2.2 := by
  classical
  intro κ ⟨hdec, hres, hadm⟩
  set τ := δ⁻¹ * L ^ (-2 * γ) with hτ
  have hτpos : 0 < τ := by positivity
  have hvmem : v ∈ M.atoms := hcd.1
  have hv₂ : v₂ ≠ v := fun e => hcd.2.1 (e ▸ hcd.1)
  have hvne : v ≠ v₂ := hv₂.symm
  set k₁ := Molecule.kvec L w κ x₁ with hk₁
  set k₂ := Molecule.kvec L w κ x₂ with hk₂
  set n : Fin d → ℤ := κ x₁ - κ x₂ with hn
  have hr : k₁ - k₂ = latticePoint L n := by
    rw [hn, latticePoint_sub]; simp only [hk₁, hk₂, Molecule.kvec]; abel
  have hrR : ‖latticePoint L n‖ ≤ 2 * R := by
    rw [← hr]; exact hgap κ hadm
  -- the box
  have hbox : n ∈ alphaN d L r₀ ρ := by
    unfold alphaN
    rw [Fintype.mem_piFinset]
    intro i
    have hb := hball κ ⟨hdec, hres, hadm⟩
    have hr' : Molecule.gapAt L w κ x₁ x₂ = latticePoint L n := hr
    rw [hr'] at hb
    have h1 : ‖(latticePoint L n - r₀) i‖ ≤ ‖latticePoint L n - r₀‖ := PiLp.norm_apply_le _ i
    have h2 : (latticePoint L n - r₀) i = (n i : ℝ) / L - r₀ i := rfl
    rw [h2, Real.norm_eq_abs] at h1
    have h3 := abs_le.mp (h1.trans hb)
    rw [Finset.mem_Icc]
    have e1 : (n i : ℝ) = L * ((n i : ℝ) / L) := by field_simp
    constructor
    · exact Int.ceil_le.mpr (by nlinarith [h3.1])
    · exact Int.le_floor.mpr (by nlinarith [h3.2])
  -- the energy
  set g := (M.cut v v₂ x₁ x₂).Gamma L w κ v with hg
  have hgv : g = -(inner ℝ (k₁ - k₂) (k₁ + k₂)) := by
    rw [hg, cut_gamma_v M hcd, ← norm_sq_sub_norm_sq]; ring
  set s₀ : Mom d := k0 x₁ + k0 x₂ with hs₀
  have hs : ‖(k₁ + k₂) - s₀‖ ≤ 2 := by
    have e : (k₁ + k₂) - s₀ = (k₁ - k0 x₁) + (k₂ - k0 x₂) := by rw [hs₀]; abel
    rw [e]
    calc _ ≤ ‖k₁ - k0 x₁‖ + ‖k₂ - k0 x₂‖ := norm_add_le _ _
      _ ≤ 1 + 1 := add_le_add (hres.2 x₁) (hres.2 x₂)
      _ = 2 := by norm_num
  have hgs : |g + inner ℝ (latticePoint L n) s₀| ≤ 4 * R := by
    have e : g + inner ℝ (latticePoint L n) s₀ = -(inner ℝ (k₁ - k₂) ((k₁ + k₂) - s₀)) := by
      rw [hgv, ← hr, inner_sub_right]; ring
    rw [e, abs_neg]
    calc _ ≤ ‖k₁ - k₂‖ * ‖(k₁ + k₂) - s₀‖ := abs_real_inner_le_norm _ _
      _ ≤ (2 * R) * 2 := by
          rw [hr]; exact mul_le_mul hrR hs (norm_nonneg _) (by linarith [norm_nonneg (latticePoint L n)])
      _ = 4 * R := by ring
  set j : ℤ := round (g / τ) with hj
  have hj1 : |g / τ - j| ≤ 1 / 2 := abs_sub_round _
  have hgq : |g / τ - alphaCenter L τ s₀ n| ≤ 4 * R / τ := by
    have e : g / τ - alphaCenter L τ s₀ n = (g + inner ℝ (latticePoint L n) s₀) / τ := by
      unfold alphaCenter; ring
    rw [e, abs_div, abs_of_pos hτpos]
    exact div_le_div_of_nonneg_right hgs hτpos.le
  have hjq : |(j : ℝ) - alphaCenter L τ s₀ n| ≤ 1 / 2 + 4 * R / τ := by
    calc |(j : ℝ) - alphaCenter L τ s₀ n| = |-(g / τ - j) + (g / τ - alphaCenter L τ s₀ n)| := by ring_nf
      _ ≤ |-(g / τ - j)| + |g / τ - alphaCenter L τ s₀ n| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg]; linarith
  have hgj : |g - j * τ| ≤ τ / 2 := by
    have : g - j * τ = (g / τ - j) * τ := by field_simp
    rw [this, abs_mul, abs_of_pos hτpos]
    nlinarith
  set G := M.Gamma L w κ v with hG
  have hΓv := hres.1 v hvmem
  set u : ℝ := (G - β v) - (g - j * τ) with hu
  have hu_bound : |u| ≤ τ + τ / 2 := by
    calc |u| ≤ |G - β v| + |g - j * τ| := abs_sub _ _
      _ ≤ τ + τ / 2 := add_le_add hΓv hgj
  set e : ℤ := if 0 ≤ u then 1 else -1 with he
  have he_mem : e ∈ ({-1, 1} : Finset ℤ) := by
    simp only [he]; split_ifs <;> simp
  have hue : |u - e * τ| ≤ τ := by
    simp only [he]
    split_ifs with hu0
    · rw [abs_le] at hu_bound ⊢; constructor <;> push_cast <;> linarith [hu_bound.1, hu_bound.2]
    · rw [abs_le] at hu_bound ⊢; push Not at hu0; constructor <;> push_cast <;> linarith [hu_bound.1, hu_bound.2]
  rw [Set.mem_iUnion₂]
  refine ⟨(n, j, e), ?_, ?_⟩
  · rw [mem_alphaIndex]
    refine ⟨hbox, ?_, he_mem⟩
    unfold alphaJ
    rw [Finset.mem_Icc]
    have := abs_le.mp hjq
    constructor
    · have h5 : (⌊alphaCenter L τ s₀ n - (1 / 2 + 4 * R / τ)⌋ : ℝ) ≤ j :=
        (Int.floor_le _).trans (by linarith [this.1])
      exact_mod_cast h5
    · have : (j : ℝ) ≤ (⌈alphaCenter L τ s₀ n + (1 / 2 + 4 * R / τ)⌉ : ℝ) :=
        (by linarith [this.2, Int.le_ceil (alphaCenter L τ s₀ n + (1 / 2 + 4 * R / τ))])
      exact_mod_cast this
  · refine ⟨⟨hdec.1, fun a ha => ?_⟩, ⟨fun a ha => ?_, hres.2⟩, hadm⟩
    · by_cases h2 : a = v₂
      · simp only [alphaParams, h2, ite_true]
        have hs' := cut_sum_split M hcd (fun x => M.dartSign x • Molecule.kvec L w κ x)
        have e1 := hdec.2 v hvmem
        have e3 := cut_c_v M hcd L w κ
        rw [e1] at hs'
        have e4 : ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v₂, (M.cut v v₂ x₁ x₂).dartSign x • Molecule.kvec L w κ x =
            ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v₂, M.dartSign x • Molecule.kvec L w κ x := rfl
        rw [e4]
        have e5 : ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v, M.dartSign x • Molecule.kvec L w κ x =
            -(k₁ - k₂) := e3
        rw [e5, hr] at hs'
        have : ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v₂, M.dartSign x • Molecule.kvec L w κ x =
            c v + latticePoint L n := by
          rw [← hr] at hs' ⊢; rw [hs']; abel
        exact this
      by_cases h1 : a = v
      · simp only [alphaParams, h1, hvne, ite_true, ite_false]
        rw [cut_c_v M hcd L w κ, hr]
      · simp only [alphaParams, h1, h2, ite_false]
        have haM : a ∈ M.atoms := (Finset.mem_insert.mp ha).resolve_left h2
        rw [show (M.cut v v₂ x₁ x₂).dartsAt a = M.dartsAt a from cut_dartsAt_other M hcd h1 h2]
        exact hdec.2 a haM
    · by_cases h2 : a = v₂
      · simp only [alphaParams, h2, ite_true]
        have hsp := cut_gamma_split M hcd L w κ
        have : (M.cut v v₂ x₁ x₂).Gamma L w κ v₂ - (β v - j * τ + e * τ) = u - e * τ := by
          have : (M.cut v v₂ x₁ x₂).Gamma L w κ v₂ = G - g := by rw [hG, hg]; linarith
          rw [this, hu]; ring
        rw [this]; exact hue
      by_cases h1 : a = v
      · simp only [alphaParams, h1, hvne, ite_true, ite_false]
        rw [← hg]; exact hgj.trans (by linarith)
      · simp only [alphaParams, h1, h2, ite_false]
        have haM : a ∈ M.atoms := (Finset.mem_insert.mp ha).resolve_left h2
        rw [cut_gamma_other M hcd L w κ h1 h2]
        exact hres.1 a haM

end WaveTurbulence.FinalCount
