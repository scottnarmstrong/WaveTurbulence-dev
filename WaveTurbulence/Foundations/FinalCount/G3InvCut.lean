/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3CutDeg
/-! **FINALCOUNT-G3**: the invariant `Inv` of the algorithm and its preservation by a classified cut. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*}

/-- The invariants of a state (`R` = half the number of missing darts of `M_sub`, i.e. the number of roots / `2`). -/
structure Inv (R : ℕ) (s : St.{u} V D₀) : Prop where
  bounds : ∀ a ∈ s.M.atoms, s.M.outdeg a ≤ 2 ∧ s.M.indeg a ≤ 2
  eps : ∀ a ∈ s.M.atoms, s.cls a = .eps → 1 ≤ s.M.deg a
  ab : ∀ a ∈ s.M.atoms, s.cls a ≠ .eps → s.M.deg a ≤ 2 ∧ (s.cls a = .ghost → s.M.deg a = 0) ∧
    (s.cls a ≠ .ghost → 1 ≤ s.M.deg a)
  phi : ∑ a ∈ s.M.atoms, (s.cls a).base = (Fintype.card s.D : ℤ) + 2 * R
  noloop : ∀ x, s.M.atom x ≠ s.M.atom (s.M.mate x)

theorem sum_replace {β : Type*} [AddCommMonoid β] {s : Finset V} {f g : V → β} {v : V} (hv : v ∈ s) (h : ∀ a ∈ s, a ≠ v → g a = f a) :
    ∑ a ∈ s, g a + f v = ∑ a ∈ s, f a + g v := by
  rw [← Finset.add_sum_erase s g hv, ← Finset.add_sum_erase s f hv]
  have : ∑ a ∈ s.erase v, g a = ∑ a ∈ s.erase v, f a :=
    Finset.sum_congr rfl fun a ha => h a (Finset.mem_of_mem_erase ha) (Finset.ne_of_mem_erase ha)
  rw [this]; abel

section cut
variable {s : St.{u} V D₀} {R : ℕ} {v v₂ : V} {x₁ x₂ : s.D}

theorem Inv.cutSt (hI : Inv R s) (hcd : s.M.IsCutData v v₂ x₁ x₂) (c₁ c₂ : Cls)
    (hc : c₁.base + c₂.base = (s.cls v).base) (h₁ : c₁ ≠ .eps) (h₂ : c₂ ≠ .eps) (h₁g : c₁ ≠ .ghost)
    (hg : c₂ = .ghost → s.M.deg v = 2) (hp : c₂ ≠ .ghost → 3 ≤ s.M.deg v) :
    Inv R (s.cutSt v v₂ x₁ x₂ c₁ c₂) := by
  have hv : v ∈ s.M.atoms := hcd.1
  have hv₂ : v₂ ∉ s.M.atoms := hcd.2.1
  have hne : v₂ ≠ v := fun e => hv₂ (e ▸ hv)
  have hb := hI.bounds v hv
  have hdeg₂ := cut_deg_v₂ hcd
  have hout₂ := cut_outdeg_v₂ hcd
  have hin₂ := cut_indeg_v₂ hcd
  have hdv : s.M.deg v ≤ 4 := deg_le_four _ hb
  have hdvv : s.M.deg v = s.M.outdeg v + s.M.indeg v := deg_eq _ _
  have hcv : (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls = Function.update (Function.update s.cls v c₁) v₂ c₂ := rfl
  have hMd : (s.cutSt v v₂ x₁ x₂ c₁ c₂).M = s.M.cut v v₂ x₁ x₂ := rfl
  have hat : (s.cutSt v v₂ x₁ x₂ c₁ c₂).M.atoms = insert v₂ s.M.atoms := rfl
  have hD : (s.cutSt v v₂ x₁ x₂ c₁ c₂).D = s.D := rfl
  have hcl : ∀ a, (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls a =
      if a = v₂ then c₂ else if a = v then c₁ else s.cls a := by
    intro a
    show Function.update (Function.update s.cls v c₁) v₂ c₂ a = _
    by_cases h1 : a = v₂
    · rw [if_pos h1, h1]; simp
    · by_cases h2 : a = v
      · rw [if_neg h1, if_pos h2, h2, Function.update_of_ne hne.symm, Function.update_self]
      · rw [if_neg h1, if_neg h2, Function.update_of_ne h1, Function.update_of_ne h2]
  have hdN : ∀ a, (s.cutSt v v₂ x₁ x₂ c₁ c₂).M.deg a =
      if a = v₂ then s.M.deg v - 2 else if a = v then 2 else s.M.deg a := by
    intro a
    show (s.M.cut v v₂ x₁ x₂).deg a = _
    by_cases h1 : a = v₂
    · rw [if_pos h1, h1]; omega
    · by_cases h2 : a = v
      · rw [if_neg h1, if_pos h2, h2]; exact cut_deg_v s.M hcd
      · rw [if_neg h1, if_neg h2]; exact cut_deg_other hcd h2 h1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hat, Finset.mem_insert] at ha
    show (s.M.cut v v₂ x₁ x₂).outdeg a ≤ 2 ∧ (s.M.cut v v₂ x₁ x₂).indeg a ≤ 2
    by_cases h1 : a = v₂
    · rw [h1]; omega
    · by_cases h2 : a = v
      · rw [h2, cut_outdeg_v hcd, cut_indeg_v hcd]; omega
      · have hm : a ∈ s.M.atoms := ha.resolve_left h1
        rw [cut_outdeg_other hcd h2 h1, cut_indeg_other hcd h2 h1]
        exact hI.bounds a hm
  · intro a ha hce
    rw [hat, Finset.mem_insert] at ha
    rw [hcl] at hce
    rw [hdN]
    by_cases h1 : a = v₂
    · rw [if_pos h1] at hce; exact absurd hce h₂
    · by_cases h2 : a = v
      · rw [if_neg h1, if_pos h2] at hce; exact absurd hce h₁
      · simp only [if_neg h1, if_neg h2] at hce ⊢
        exact hI.eps a (ha.resolve_left h1) hce
  · intro a ha hce
    rw [hat, Finset.mem_insert] at ha
    rw [hcl] at hce ⊢
    rw [hdN]
    by_cases h1 : a = v₂
    · simp only [if_pos h1] at hce ⊢
      refine ⟨by omega, fun hgh => ?_, fun hgh => ?_⟩
      · have := hg hgh; omega
      · have := hp hgh; omega
    · by_cases h2 : a = v
      · simp only [if_neg h1, if_pos h2] at hce ⊢
        exact ⟨le_refl _, fun hgh => absurd hgh h₁g, fun _ => by omega⟩
      · simp only [if_neg h1, if_neg h2] at hce ⊢
        exact hI.ab a (ha.resolve_left h1) hce
  · show ∑ a ∈ insert v₂ s.M.atoms, ((s.cutSt v v₂ x₁ x₂ c₁ c₂).cls a).base = _
    rw [Finset.sum_insert hv₂]
    have hrep := sum_replace (s := s.M.atoms)
      (f := fun a => (s.cls a).base) (g := fun a => ((s.cutSt v v₂ x₁ x₂ c₁ c₂).cls a).base) hv
      (fun a _ ha' => by
        rw [hcl]
        have : a ≠ v₂ := fun e => hv₂ (e ▸ ‹a ∈ s.M.atoms›)
        simp [this, ha'])
    have h2 : ((s.cutSt v v₂ x₁ x₂ c₁ c₂).cls v₂).base = c₂.base := by rw [hcl]; simp
    have h1 : ((s.cutSt v v₂ x₁ x₂ c₁ c₂).cls v).base = c₁.base := by
      rw [hcl]; simp [hne.symm]
    simp only [h1] at hrep
    have := hI.phi
    show _ = (Fintype.card s.D : ℤ) + 2 * R
    rw [h2]
    linarith
  · intro x
    show (s.M.cut v v₂ x₁ x₂).atom x ≠ (s.M.cut v v₂ x₁ x₂).atom (s.M.mate x)
    have hl := hI.noloop x
    have hm1 := s.M.atom_mem x
    have hm2 := s.M.atom_mem (s.M.mate x)
    intro heq
    rw [cut_atom s.M v v₂ x₁ x₂ x, cut_atom s.M v v₂ x₁ x₂ (s.M.mate x)] at heq
    split_ifs at heq with h1 h2 h2
    · exact hl (h1.1.trans h2.1.symm)
    · exact hv₂ (by rw [heq]; exact hm2)
    · exact hv₂ (by rw [← heq]; exact hm1)
    · exact hl heq

end cut
end WaveTurbulence.FinalCountG3
