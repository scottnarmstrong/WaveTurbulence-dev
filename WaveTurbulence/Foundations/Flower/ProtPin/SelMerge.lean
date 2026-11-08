/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.SelFinal

/-! # D3 PROT-PIN (R181): the selected filter merged into two layers

`ProtBoundSelAt`'s multiplier carries the selected factor `chiDN(|Ω_v|/M₂)` on top of the two `χ₀` layers `F`, `Fu`.
When `v ∉ F ∩ Fu` it rearranges exactly into D3's two-layer form with a first-layer flag, times `chiDNorm⁻¹`
(`sel_mult_merge`): if `v ∉ F` the first layer becomes `insert v F` (flag `· = v`, scale `M₂` at `v`); if `v ∈ F \ Fu`
the `χ₀` factor of `F` at `v` moves to the second layer (`insert v Fu`, scale `M v`) and `v` carries `chiD` in the
first. (`chiDN = chiD / chiDNorm`; `MkDefs.chiD` and `FlShell.chiD` are the same function.) -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open scoped Classical

namespace WaveTurbulence.Flower.ProtPin.Sel

open WaveTurbulence.Flower.ProtDefs

theorem chiD_mk_eq (u : ℝ) : Flower.MkDefs.chiD u = FlShell.chiD u := rfl

theorem chiDN_eq (u : ℝ) :
    ((Flower.MkDefs.chiDN u : ℝ) : ℂ) = ((Flower.MkDefs.chiDNorm⁻¹ : ℝ) : ℂ) * ((FlShell.chiD u : ℝ) : ℂ) := by
  unfold Flower.MkDefs.chiDN
  rw [chiD_mk_eq, div_eq_mul_inv]
  push_cast
  ring

theorem norm_chiDNorm_inv_le : ‖((Flower.MkDefs.chiDNorm⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr Flower.MkDefs.chiDNorm_pos)]
  exact inv_le_one_of_one_le₀ Flower.MkDefs.one_le_chiDNorm

/-- **The selected filter merged into two layers** (`v ∉ F ∩ Fu`). -/
theorem sel_mult_merge {w d : ℕ} {G : Garden w} (L : ℝ) (v : GBranch G.tree) (S : Finset (GNode G.tree))
    (ω : GNode G.tree → Flower.IncTop.Star d → ℂ) (F : Finset (GBranch G.tree)) (M : GBranch G.tree → ℝ)
    (hM : ∀ b ∈ F, L ≤ M b) (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (hMu : ∀ b ∈ Fu, L ≤ Mu b)
    (M₂ : ℝ) (hM₂ : L ≤ M₂) (ind : (GNode G.tree → Mom d) → ℝ) (hv : v ∉ F ∨ v ∉ Fu) :
    ∃ (F₁ : Finset (GBranch G.tree)) (ann₁ : GBranch G.tree → Bool) (M₁ : GBranch G.tree → ℝ)
      (F₂ : Finset (GBranch G.tree)) (M₂' : GBranch G.tree → ℝ),
      (∀ b ∈ F₁, L ≤ M₁ b) ∧ (∀ b ∈ F₂, L ≤ M₂' b) ∧
      ∀ κ : GNode G.tree → Mom d,
        Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ * filtWeight Fu (fun _ => false) Mu κ *
            ((Flower.MkDefs.chiDN (|omegaNode G κ v| / M₂) : ℝ) : ℂ) * (ind κ : ℂ) =
          ((Flower.MkDefs.chiDNorm⁻¹ : ℝ) : ℂ) * (Flower.IncTop.starWeight S ω κ * filtWeight F₁ ann₁ M₁ κ *
            filtWeight F₂ (fun _ => false) M₂' κ * (ind κ : ℂ)) := by
  by_cases hvF : v ∈ F
  · have hvFu : v ∉ Fu := hv.resolve_left (not_not.mpr hvF)
    refine ⟨F, fun b => decide (b = v), Function.update M v M₂, insert v Fu, Function.update Mu v (M v),
      fun b hb => ?_, fun b hb => ?_, fun κ => ?_⟩
    · by_cases h : b = v
      · subst h; simpa using hM₂
      · rw [Function.update_of_ne h]; exact hM b hb
    · rcases Finset.mem_insert.mp hb with h | hb'
      · subst h; simpa using hM _ hvF
      · have h : b ≠ v := fun h => hvFu (h ▸ hb')
        rw [Function.update_of_ne h]; exact hMu b hb'
    · unfold filtWeight
      rw [← Finset.mul_prod_erase F _ hvF, ← Finset.mul_prod_erase F _ hvF, Finset.prod_insert hvFu, chiDN_eq]
      have hrest : ∏ b ∈ F.erase v, (((if decide (b = v) then FlShell.chiD else chi0)
            (|omegaNode G κ b| / Function.update M v M₂ b) : ℝ) : ℂ) =
          ∏ b ∈ F.erase v, (((if (fun _ : GBranch G.tree => false) b then FlShell.chiD else chi0)
            (|omegaNode G κ b| / M b) : ℝ) : ℂ) := by
        refine Finset.prod_congr rfl fun b hb => ?_
        have h : b ≠ v := Finset.ne_of_mem_erase hb
        simp [h, Function.update_of_ne h]
      have hrest2 : ∏ b ∈ Fu, (((if (fun _ : GBranch G.tree => false) b then FlShell.chiD else chi0)
            (|omegaNode G κ b| / Function.update Mu v (M v) b) : ℝ) : ℂ) =
          ∏ b ∈ Fu, (((if (fun _ : GBranch G.tree => false) b then FlShell.chiD else chi0)
            (|omegaNode G κ b| / Mu b) : ℝ) : ℂ) := by
        refine Finset.prod_congr rfl fun b hb => ?_
        have h : b ≠ v := fun h => hvFu (h ▸ hb)
        simp [Function.update_of_ne h]
      rw [hrest, hrest2]
      simp only [decide_true, ↓reduceIte, Function.update_self, Bool.false_eq_true]
      ring
  · refine ⟨insert v F, fun b => decide (b = v), Function.update M v M₂, Fu, Mu,
      fun b hb => ?_, hMu, fun κ => ?_⟩
    · rcases Finset.mem_insert.mp hb with h | hb'
      · subst h; simpa using hM₂
      · have h : b ≠ v := fun h => hvF (h ▸ hb')
        rw [Function.update_of_ne h]; exact hM b hb'
    · unfold filtWeight
      rw [Finset.prod_insert hvF, chiDN_eq]
      have hrest : ∏ b ∈ F, (((if decide (b = v) then FlShell.chiD else chi0)
            (|omegaNode G κ b| / Function.update M v M₂ b) : ℝ) : ℂ) =
          ∏ b ∈ F, (((if (fun _ : GBranch G.tree => false) b then FlShell.chiD else chi0)
            (|omegaNode G κ b| / M b) : ℝ) : ℂ) := by
        refine Finset.prod_congr rfl fun b hb => ?_
        have h : b ≠ v := fun h => hvF (h ▸ hb)
        simp [h, Function.update_of_ne h]
      rw [hrest]
      simp only [decide_true, ↓reduceIte, Function.update_self]
      ring

end WaveTurbulence.Flower.ProtPin.Sel
