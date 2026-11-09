/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCNew11
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew10
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCNew11`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 33 (session 4): the new-component label count for a VC formed by two double bonds `a = x = b`.

The count is two slab counts (the fixed gap `r = n₀` forces `κ_{y₁}` into a slab by the lower-joint energy and
`κ_{x₁} - κ_{y₁}` into a slab by the middle atom's window), i.e. `≲ (ν δ⁻¹ L^{d-γ+γ₀})²`. NOTE: this is a factor `L^{γ₀}` more
than a single vine; excessprop1 (2) does not claim this case (TARGET L2167: the objects of `Cs_2` do not create new components). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.CountLemmas

variable {d : ℕ}

/-- **The new-component label count of two double bonds** `a = x = b`. -/
theorem double_count_new (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ ν : ℝ, 1 ≤ ν →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {K : VineCut g M}
        (S : DoubleShape K) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
        NewCompFixed M K L γ δ ν w Adm →
        ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
          (K.labelSet L γ δ w Adm c β k0).encard ≤
            ENNReal.ofReal (Cd * ν ^ 2 * (δ⁻¹) ^ 2 * (L ^ ((d : ℝ) - γ + min γ (1 - γ))) ^ 2) := by
  obtain ⟨Cs, L₀, hCs0, hL₀1, hslab⟩ := slab_count hd hγ
  refine ⟨((coverNum d : ℝ) * Cs) ^ 2, by positivity, L₀, hL₀1, ?_⟩
  intro L hL δ hδ ν hν V D _ _ _ M K S w Adm hfix c β k0 hP
  have hL1 : 1 ≤ L := hL₀1.trans hL
  have hL0 : 0 < L := by linarith
  obtain ⟨n₀, hn₀, e₀, hne⟩ := hfix c β k0 hP
  set r : Mom d := latticePoint L n₀ with hr
  let βy : ℝ := e₀ - 2 * inner ℝ r w - ‖r‖ ^ 2
  let βu : ℝ := 2 * ‖r‖ ^ 2 + β S.x
  obtain ⟨hAfin, hAcard⟩ := hslab L hL δ hδ ν hν n₀ hn₀ (k0 K.y₁ - w) βy
  obtain ⟨hBfin, hBcard⟩ := hslab L hL δ hδ ν hν n₀ hn₀ (k0 K.x₁ - k0 K.y₁) βu
  set A := slabSet L (k0 K.y₁ - w) n₀ βy (ν * δ⁻¹ * L ^ (-2 * γ)) with hA
  set B := slabSet L (k0 K.x₁ - k0 K.y₁) n₀ βu (ν * δ⁻¹ * L ^ (-2 * γ)) with hB
  let Φ : (D → (Fin d → ℤ)) → (Fin d → ℤ) × (Fin d → ℤ) := fun ℓ => (ℓ K.y₁, ℓ K.x₁ - ℓ K.y₁)
  have hinj : Set.InjOn Φ (K.labelSet L γ δ w Adm c β k0) := by
    rintro _ ⟨κ, hκ, rfl⟩ _ ⟨κ', hκ', rfl⟩ h
    simp only [Φ, K.restrS_x₁, K.restrS_y₁, Prod.mk.injEq] at h
    obtain ⟨h3, h1'⟩ := h
    have h1 : κ K.x₁ = κ' K.x₁ := by
      have : κ K.x₁ - κ K.y₁ = κ' K.x₁ - κ' K.y₁ := h1'
      rw [h3] at this
      exact sub_left_inj.mp this
    have e1 := (hne κ hκ).1
    have e2 := (hne κ' hκ').1
    have h2 : κ K.x₂ = κ' K.x₂ := by
      have : κ K.x₁ - κ K.x₂ = κ' K.x₁ - κ' K.x₂ := e1.trans e2.symm
      rw [h1] at this
      exact (sub_right_inj.mp this)
    show K.restrS κ = K.restrS κ'
    exact S.restrS_eq hP hL0 hκ hκ' h1 h2 h3
  have hsub : Φ '' (K.labelSet L γ δ w Adm c β k0) ⊆ A ×ˢ B := by
    rintro _ ⟨_, ⟨κ, hκ, rfl⟩, rfl⟩
    simp only [Φ, K.restrS_x₁, K.restrS_y₁]
    obtain ⟨hdec, hres, hadm⟩ := hκ
    have hκ' : κ ∈ decSet M L γ δ w Adm c β k0 := ⟨hdec, hres, hadm⟩
    obtain ⟨hrint, hG⟩ := hne κ hκ'
    have hlat := S.lat_cons hP hL0 hκ'
    have hy2 : κ K.y₂ = κ K.y₁ + n₀ := by
      rw [hlat, add_sub_assoc, hrint]
    have hkv2 : Molecule.kvec L w κ K.y₂ = Molecule.kvec L w κ K.y₁ + r := by
      unfold Molecule.kvec; rw [hy2, latticePoint_add]; abel
    have hgap : Molecule.gapAt L w κ K.x₁ K.x₂ = r := by
      rw [gapAt_eq_lattice]; unfold rint; rw [hrint]
    have hk1 : ‖Molecule.kvec L w κ K.x₁ - k0 K.x₁‖ ≤ 1 := hres.2 K.x₁
    have hk3 : ‖Molecule.kvec L w κ K.y₁ - k0 K.y₁‖ ≤ 1 := hres.2 K.y₁
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · -- Near4 for y₁
      show ‖latticePoint L (κ K.y₁) - (k0 K.y₁ - w)‖ ≤ 4
      have : latticePoint L (κ K.y₁) - (k0 K.y₁ - w) = Molecule.kvec L w κ K.y₁ - k0 K.y₁ := by
        unfold Molecule.kvec; abel
      rw [this]; linarith
    · -- energy slab for y₁
      have e : 2 * inner ℝ r (latticePoint L (κ K.y₁)) - βy = lowerG K L w κ - e₀ := by
        unfold lowerG
        rw [hkv2]
        have hk : Molecule.kvec L w κ K.y₁ = w + latticePoint L (κ K.y₁) := rfl
        rw [norm_add_sq_real, hk, norm_add_sq_real, inner_add_left]
        simp only [βy]
        have c1 := real_inner_comm r w
        have c2 := real_inner_comm r (latticePoint L (κ K.y₁))
        linarith
      show |2 * inner ℝ (latticePoint L n₀) (latticePoint L (κ K.y₁)) - βy| ≤ ν * δ⁻¹ * L ^ (-2 * γ)
      rw [← hr, e]; exact hG
    · -- Near4 for u
      show ‖latticePoint L (κ K.x₁ - κ K.y₁) - (k0 K.x₁ - k0 K.y₁)‖ ≤ 4
      rw [latticePoint_sub]
      have : latticePoint L (κ K.x₁) - latticePoint L (κ K.y₁) - (k0 K.x₁ - k0 K.y₁) =
          (Molecule.kvec L w κ K.x₁ - k0 K.x₁) - (Molecule.kvec L w κ K.y₁ - k0 K.y₁) := by
        unfold Molecule.kvec; abel
      rw [this]
      calc _ ≤ ‖Molecule.kvec L w κ K.x₁ - k0 K.x₁‖ + ‖Molecule.kvec L w κ K.y₁ - k0 K.y₁‖ := norm_sub_le _ _
        _ ≤ 4 := by linarith
    · -- middle-atom slab for u
      have hGx := S.gamma_x hP hκ'
      have hb := hres.1 S.x S.x_mem
      rw [hgap] at hGx
      have hu : Molecule.kvec L w κ K.x₁ - Molecule.kvec L w κ K.y₁ = latticePoint L (κ K.x₁ - κ K.y₁) := by
        unfold Molecule.kvec; rw [latticePoint_sub]; abel
      rw [hu, inner_sub_right, real_inner_self_eq_norm_sq] at hGx
      show |2 * inner ℝ (latticePoint L n₀) (latticePoint L (κ K.x₁ - κ K.y₁)) - βu| ≤ ν * δ⁻¹ * L ^ (-2 * γ)
      rw [← hr]
      have hτν : δ⁻¹ * L ^ (-2 * γ) ≤ ν * δ⁻¹ * L ^ (-2 * γ) := by
        have : 0 ≤ δ⁻¹ * L ^ (-2 * γ) := by have := hδ.1; positivity
        nlinarith
      rw [hGx] at hb
      have e : 2 * inner ℝ r (latticePoint L (κ K.x₁ - κ K.y₁)) - βu =
          2 * (inner ℝ r (latticePoint L (κ K.x₁ - κ K.y₁)) - ‖r‖ ^ 2) - β S.x - ‖r‖ ^ 2 * 0 := by
        simp only [βu]; ring
      rw [abs_le] at hb ⊢
      constructor <;> nlinarith [hb.1, hb.2]
  have hfin : (A ×ˢ B).Finite := hAfin.prod hBfin
  have hlab : (K.labelSet L γ δ w Adm c β k0).encard ≤ ((A ×ˢ B).ncard : ℕ∞) := by
    calc _ = (Φ '' (K.labelSet L γ δ w Adm c β k0)).encard := (hinj.encard_image).symm
      _ ≤ (A ×ˢ B).encard := Set.encard_le_encard hsub
      _ = _ := by rw [← hfin.cast_ncard_eq]
  have hfinite : (A ×ˢ B).ncard = A.ncard * B.ncard := Set.ncard_prod
  rw [hfinite] at hlab
  refine (ENat.toENNReal_le.2 hlab).trans ?_
  have hAB : ((A.ncard * B.ncard : ℕ) : ℝ) ≤ ((coverNum d : ℝ) * Cs * ν * δ⁻¹ * L ^ ((d : ℝ) - γ + min γ (1 - γ))) *
      ((coverNum d : ℝ) * Cs * ν * δ⁻¹ * L ^ ((d : ℝ) - γ + min γ (1 - γ))) := by
    push_cast
    exact mul_le_mul hAcard hBcard (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) hAcard)
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal (hAB.trans (le_of_eq ?_))
  ring

end WaveTurbulence.GammaLow.FinalCount.Step1
