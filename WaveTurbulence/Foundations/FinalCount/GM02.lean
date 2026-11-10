/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GM01
/-! **FINALCOUNT-G3: `FinalShape` for a component** (second part: parity, `β`-atoms, cycles, chains). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop} {hf : HSt V D₀}

/-- `odd`: the component contains an atom of odd degree. -/
def CompOddL (hf : HSt V D₀) (a₀ : V) : Prop := ∃ b ∈ (compMol hf.s.M a₀).atoms, ¬ Even ((compMol hf.s.M a₀).deg b)

/-- The number of odd-degree atoms is even (handshake). -/
theorem card_odd_even {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) :
    Even (M.atoms.filter fun a => ¬ Even (M.deg a)).card := by
  have h1 : Even (∑ a ∈ M.atoms, M.deg a) := by
    rw [sum_deg_eq M, card_darts_eq_two_bonds M]; exact even_two_mul _
  have h2 : (∑ a ∈ M.atoms, M.deg a) % 2 = (∑ a ∈ M.atoms, M.deg a % 2) % 2 := Finset.sum_nat_mod _ _ _
  have h3 : ∑ a ∈ M.atoms, M.deg a % 2 = (M.atoms.filter fun a => ¬ Even (M.deg a)).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases he : Even (M.deg a)
    · rw [if_neg (not_not.2 he)]; exact Nat.even_iff.1 he
    · rw [if_pos he]; exact Nat.odd_iff.1 (Nat.not_even_iff_odd.1 he)
  rw [Nat.even_iff] at h1 ⊢
  omega

section shape2
variable (hC : Prop95ConclAtL L γ η w κ R hf Tm) {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms)
include hC ha₀

theorem shape_evenDegL : ¬ CompOddL hf a₀ → ∀ a ∈ (compMol hf.s.M a₀).atoms,
    (compMol hf.s.M a₀).deg a = 2 ∨ (compMol hf.s.M a₀).deg a = 4 := by
  intro hn a ha
  have h := (mem_compMol _ _).1 ha
  have hev : Even ((compMol hf.s.M a₀).deg a) := by
    by_contra hc; exact hn ⟨a, ha, hc⟩
  rw [compMol_deg _ _ h.2] at hev ⊢
  have hr := hC.struct.deg_range a h.1
  obtain ⟨k, hk⟩ := hev
  omega

theorem shape_evenBetaL (hE : LowFree hf a₀) : ¬ CompOddL hf a₀ → ∃ a ∈ (compMol hf.s.M a₀).atoms, (toCls (hf.s.cls a)).IsBeta := by
  intro hn
  have hper : ∀ b ∈ hf.s.M.atoms, hf.s.M.SameComponent a₀ b → contrib hf.s b = 0 := by
    intro b hb hsc
    have hm : b ∈ (compMol hf.s.M a₀).atoms := (mem_compMol _ _).2 ⟨hb, hsc⟩
    have hev : Even (hf.s.M.deg b) := by
      by_contra hc
      exact hn ⟨b, hm, by rwa [compMol_deg _ _ hsc]⟩
    have hr := hC.struct.deg_range b hb
    obtain ⟨k, hk⟩ := hev
    unfold contrib
    by_cases he : hf.s.cls b = .eps
    · have h3 := hE b (Finset.mem_filter.2 ⟨hb, hsc⟩) he
      rw [he]; simp only [Cls.base]; omega
    · have h2 := hC.struct.ab_deg b hb he
      rcases hC.struct.ab_cls b hb he with ⟨ρ, kp, e⟩ | e <;> rw [e] <;> simp only [Cls.base] <;> omega
  obtain ⟨b, hb, hsc, hcb⟩ := hC.struct.perfect_beta a₀ ha₀ (fun b hb hsc => hper b hb hsc)
  exact ⟨b, (mem_compMol _ _).2 ⟨hb, hsc⟩, by rw [toCls_isBeta]; exact Or.inl hcb⟩

end shape2

end WaveTurbulence.FinalCountG3
