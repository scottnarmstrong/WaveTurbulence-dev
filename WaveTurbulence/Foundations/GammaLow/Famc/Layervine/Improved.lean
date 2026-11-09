/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Layervine.Range
public import WaveTurbulence.Foundations.LayerCnt.Improved
/-! # layervine′, improved bound: `LayervineTVineImproved` (packet L5c)

TARGET L1517, L1523–L1531 for (CL) T-vines, by main's route (`LayerCnt.layervine_improved_of_range`,
`layervine_improved`): for coherent pre-layerings satisfying `canonequiv` on the vine region every layer lies in
`[q', q]` (`tvine_layer_range`); clamping to `[0, q − q']` changes neither the bond exponents nor the injectivity, and
the first bound (`layervineTVineFirst`) with `𝔇 = q − q'`, `g = 0` and `C_2 = C_0^{𝔇+1}` gives `C_0^{m + (q−q') + 1}`,
which is at most `(C_0²)^{m + (q − q')}` unless `m = 0` and `q = q'`; in that case every member is constant `= q`
on the vine, so the family has at most one member and each product is `1`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc
open Finset WaveTurbulence.LayerCnt WaveTurbulence.Vine

/-- **TARGET `layervine`, improved bound, for (CL) T-vines** (from N3 Thm 6 (i)–(iv) and N2 Prop 1.17(b)). -/
theorem layervineTVineImproved (hLad : LaddersInput) (hPS : PieceShapeInput) (hLV : LayervineInput) :
    LayervineTVineImproved := by
  intro B hB
  obtain ⟨C₀, hC₀, hfirst⟩ := layervineTVineFirst hLad hPS B hB
  refine ⟨C₀ ^ 2, one_le_pow₀ hC₀, ?_⟩
  intro w G S a b hT hCL m hm p q q' 𝓕 hpre hcoh hjoint hC hinj
  classical
  set P : (GBranch G.tree → ℕ) → ℝ := fun f => ∏ x ∈ bondsIn G.molecule S,
    B ^ dst (f (G.molecule.atom x)) (f (G.molecule.atom (G.molecule.mate x))) with hPdef
  show ∑ f ∈ 𝓕, P f ≤ (C₀ ^ 2) ^ (m + (q - q'))
  by_cases hne : 𝓕 = ∅
  · subst hne
    simp only [Finset.sum_empty]
    positivity
  obtain ⟨f0, hf0⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hrange : ∀ f ∈ 𝓕, ∀ x ∈ S, q' ≤ f x ∧ f x ≤ q := by
    intro f hf x hx
    have h := tvine_layer_range hLV G hT hCL (hpre f hf) (hcoh f hf) (hC f hf) x hx
    have hj := hjoint f hf
    rw [hj.1, hj.2] at h
    exact ⟨h.1, h.2⟩
  have haS : a ∈ S := hT.1.2.1
  have hqq : q' ≤ q := (hrange f0 hf0 a haS).1.trans (hrange f0 hf0 a haS).2
  -- the degenerate case `m = 0`, `q = q'`
  by_cases h0 : m + (q - q') = 0
  · have hqe : q = q' := by omega
    have hconst : ∀ f ∈ 𝓕, ∀ x ∈ S, f x = q := by
      intro f hf x hx
      have := hrange f hf x hx
      omega
    have hP1 : ∀ f ∈ 𝓕, P f = 1 := by
      intro f hf
      simp only [hPdef]
      apply Finset.prod_eq_one
      intro x hx
      simp only [bondsIn, mem_filter] at hx
      rw [hconst f hf _ hx.2.1, hconst f hf _ hx.2.2]
      simp [dst]
    have hcard : 𝓕.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro f hf g hg
      exact hinj f hf g hg (fun x hx => by rw [hconst f hf x hx, hconst g hg x hx])
    rw [h0, pow_zero, Finset.sum_congr rfl hP1]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast hcard
  -- clamping
  set cl : (GBranch G.tree → ℕ) → (GBranch G.tree → ℕ) := fun f x => clampL q q' (f x) with hcl
  have hclinj : ∀ f ∈ 𝓕, ∀ f' ∈ 𝓕, (∀ x ∈ S, cl f x = cl f' x) → f = f' := by
    intro f hf f' hf' h
    apply hinj f hf f' hf'
    intro x hx
    have := h x hx
    simp only [hcl] at this
    rw [clampL_of_mem (hrange f hf x hx).1 (hrange f hf x hx).2,
      clampL_of_mem (hrange f' hf' x hx).1 (hrange f' hf' x hx).2] at this
    have := (hrange f hf x hx).1; have := (hrange f' hf' x hx).1
    omega
  have hPcl : ∀ f ∈ 𝓕, P (cl f) = P f := by
    intro f hf
    simp only [hPdef]
    apply Finset.prod_congr rfl
    intro x hx
    simp only [bondsIn, mem_filter] at hx
    have h1 := hrange f hf _ hx.2.1
    have h2 := hrange f hf _ hx.2.2
    simp only [hcl]
    rw [clampL_of_mem h1.1 h1.2, clampL_of_mem h2.1 h2.2]
    congr 1
    unfold dst; omega
  have hsum : ∑ f ∈ 𝓕, P f = ∑ h ∈ 𝓕.image cl, P h := by
    rw [Finset.sum_image (fun f hf f' hf' h => hclinj f hf f' hf' (fun x _ => congrFun h x))]
    exact Finset.sum_congr rfl (fun f hf => (hPcl f hf).symm)
  rw [hsum]
  have hflt : (𝓕.image cl).filter (fun h => tvineIncoherency G.molecule S a b h = 0) = 𝓕.image cl := by
    apply Finset.filter_true_of_mem
    intro h hh
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hh
    have hcf := coherent_of_tvineIncoherency_zero (hcoh f hf)
    unfold tvineIncoherency
    simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_not]
    intro Q hQ x hx y hy
    exact congrArg (clampL q q') (hcf Q hQ x hx y hy)
  have hcore := hfirst G S a b hT m hm (q - q') (C₀ ^ (q - q' + 1)) le_rfl 0 (by omega) (𝓕.image cl)
    (by
      intro h hh
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hh
      refine ⟨?_, fun x => clampL_le q q' _⟩
      intro b' c i hc
      exact clampL_mono q q' (hpre f hf b' c i hc))
    (by
      intro h hh h' hh' hagree
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hh
      obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hh'
      have := hclinj f hf f' hf' hagree
      rw [this])
  rw [hflt] at hcore
  refine hcore.trans ?_
  have hC0 : (0 : ℝ) ≤ C₀ := by linarith
  calc C₀ ^ m * (C₀ ^ (q - q' + 1)) ^ (0 + 1) = C₀ ^ (m + (q - q') + 1) := by
        rw [zero_add, pow_one, ← pow_add]; ring_nf
    _ ≤ C₀ ^ (2 * (m + (q - q'))) := pow_le_pow_right₀ hC₀ (by omega)
    _ = (C₀ ^ 2) ^ (m + (q - q')) := by rw [← pow_mul]

end WaveTurbulence.GammaLow.Famc
