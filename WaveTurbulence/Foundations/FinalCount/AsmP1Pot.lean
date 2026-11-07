/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmP1Basic
/-! **FINALCOUNT-ASSEMBLY, phase 1 (b): potential bookkeeping of a vine removal.**  `apProd`, `vBeta`, `ApPos` of `vineSt`, and the translation of the
`excessprop1` right sides (`α`-case, new-component case) into `stepRHS`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The product over the atoms of the post state splits off the two new atoms. -/
theorem prod_vineSt {α : Type*} [CommMonoid α] (s : St.{u} V D₀) (K : VineCut s.M) (c : Cls) (f : Cls → α)
    (hrem : ∀ a ∈ K.C.atoms, f (s.cls a) = 1) :
    ∏ a ∈ (vineSt s K c).M.atoms, f ((vineSt s K c).cls a) = f c * f c * ∏ a ∈ s.M.atoms, f (s.cls a) := by
  have hfa : K.fa ∉ s.M.atoms.filter (fun a => a ∉ K.C.atoms) := fun h => K.fa_fresh (Finset.mem_filter.1 h).1
  have hfb : K.fb ∉ insert K.fa (s.M.atoms.filter (fun a => a ∉ K.C.atoms)) := by
    intro h
    rcases Finset.mem_insert.1 h with e | h
    · exact K.fa_ne_fb e.symm
    · exact K.fb_fresh (Finset.mem_filter.1 h).1
  have hat : (vineSt s K c).M.atoms = insert K.fb (insert K.fa (s.M.atoms.filter (fun a => a ∉ K.C.atoms))) := by
    rw [vineSt_atoms]
    ext a
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨h | h | h, hn⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h, hn⟩)
    · rintro (h | h | ⟨h, hn⟩)
      · exact ⟨Or.inl h, by rw [h]; exact fun hh => K.fb_fresh (objectAtoms_sub K.C hh)⟩
      · exact ⟨Or.inr (Or.inl h), by rw [h]; exact fun hh => K.fa_fresh (objectAtoms_sub K.C hh)⟩
      · exact ⟨Or.inr (Or.inr h), hn⟩
  rw [hat, Finset.prod_insert hfb, Finset.prod_insert hfa, vineSt_cls_fb, vineSt_cls_fa]
  have e1 : ∏ a ∈ s.M.atoms.filter (fun a => a ∉ K.C.atoms), f ((vineSt s K c).cls a) =
      ∏ a ∈ s.M.atoms.filter (fun a => a ∉ K.C.atoms), f (s.cls a) :=
    Finset.prod_congr rfl fun a ha => by
      have := Finset.mem_filter.1 ha
      rw [vineSt_cls_old s K c this.1 this.2]
  have e2 : ∏ a ∈ s.M.atoms, f (s.cls a) = ∏ a ∈ s.M.atoms.filter (fun a => a ∉ K.C.atoms), f (s.cls a) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun a ha => ?_
    by_cases haC : a ∈ K.C.atoms
    · simp [haC, hrem a haC]
    · simp [haC]
  rw [e1, e2, mul_assoc]

theorem apProd_vineSt (L γ η : ℝ) (s : St.{u} V D₀) (K : VineCut s.M) (c : Cls)
    (hrem : ∀ a ∈ K.C.atoms, s.cls a = .eps) :
    apProd L γ η (vineSt s K c) = apFactor L γ η c * apFactor L γ η c * apProd L γ η s := by
  unfold apProd
  exact prod_vineSt s K c (apFactor L γ η) (fun a ha => by rw [hrem a ha]; rfl)

theorem vBeta_vineSt (s : St.{u} V D₀) (K : VineCut s.M) (c : Cls) (hrem : ∀ a ∈ K.C.atoms, s.cls a = .eps) :
    vBeta (vineSt s K c) = vBeta s + (if c = .beta then 2 else 0) := by
  have key := prod_vineSt (α := Multiplicative ℕ) s K c (fun x => Multiplicative.ofAdd (if x = Cls.beta then 1 else 0))
    (fun a ha => by rw [hrem a ha]; simp)
  have hv : ∀ t : St.{u} V D₀, vBeta t = ∑ a ∈ t.M.atoms, (if t.cls a = Cls.beta then 1 else 0) := by
    intro t; unfold vBeta; rw [Finset.card_filter]
  rw [hv, hv]
  have := congrArg Multiplicative.toAdd key
  simp only [toAdd_prod, toAdd_mul, toAdd_ofAdd] at this
  rw [this]
  by_cases hc : c = .beta <;> simp [hc]; ring

theorem apPos_vineSt {s : St.{u} V D₀} (hap : ApPos s) (K : VineCut s.M) (c : Cls)
    (hc : ∀ R' kp', c = .alpha R' kp' → 0 < R') : ApPos (vineSt s K c) := by
  intro a ha R' kp' hcl
  rw [vineSt_atoms, Finset.mem_filter] at ha
  obtain ⟨ha1, haC⟩ := ha
  by_cases h1 : a = K.fb
  · rw [h1, vineSt_cls_fb] at hcl; exact hc _ _ hcl
  by_cases h2 : a = K.fa
  · rw [h2, vineSt_cls_fa] at hcl; exact hc _ _ hcl
  have haM : a ∈ s.M.atoms := by
    rcases Finset.mem_insert.1 ha1 with h | h
    · exact absurd h h1
    · rcases Finset.mem_insert.1 h with h | h
      · exact absurd h h2
      · exact h
  rw [vineSt_cls_old s K c haM haC] at hcl
  exact hap a haM R' kp' hcl

end WaveTurbulence.FinalCountAsm
