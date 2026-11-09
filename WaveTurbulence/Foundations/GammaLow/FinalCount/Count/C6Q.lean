/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6Theta
public import WaveTurbulence.Foundations.FinalCount.ChainOrient
import Mathlib.Tactic

/-! # Case (6): the charges of a genuine decoration (packet L6-COUNT, Case6TopLow; M2 §4.10, REF-M2 N2)

For a decoration with charge `0` at the degree-four atoms, the charges `c₁, c₂, c_β` of the three non-`ε` atoms
`v₁, v₂, β` of case (6) sum to zero (`charge_sum_zero`), and each has norm `≥ ρ = L^{−γ−100η}/2`: at the `α`-atoms
by `alphaGap` (labels `> L^{−γ−50η}`), at `β` by the `ι/κ` property N2 (`FinalDec.iota`, `r_β = −r₁ − r₂`)
(`c6_charges`). Consequences for operation (e): the gap of a chain `C ⊆ {v₂, β}` (`c6_chain_gap`) and the total
charge of a generalized theta chain (`c6_starSum_double`, `c6_starSum_single`). -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The charge of a degree-two atom, with its two darts. -/
theorem charge_at_deg2 {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd) {d : ℕ}
    {L : ℝ} {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L 0 c κ) {v : V} (hv : v ∈ M.atoms)
    (h2 : M.deg v = 2) :
    ∃ xo xi, M.atom xo = v ∧ M.atom xi = v ∧ xo ≠ xi ∧ c v = Molecule.gapAt L 0 κ xo xi := by
  obtain ⟨xo, xi, ho, hi, hoo, hio, hstar⟩ := deg2_darts (hS.dir2 v hv h2)
  have hne : xo ≠ xi := fun e => by rw [e, hio] at hoo; exact Bool.false_ne_true hoo
  exact ⟨xo, xi, ho, hi, hne, charge_deg2 hκ hv hoo hio hne hstar⟩

/-- **The three charges of case (6)** (see the module docstring). -/
theorem c6_charges {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd) {d : ℕ}
    {L γ η : ℝ} {Adm : (D → (Fin d → ℤ)) → Prop} (hF : FinalDec M cls L γ η Adm) (hL1 : 1 ≤ L) (hη : 0 ≤ η)
    {v₁ v₂ b : V} (h1 : v₁ ∈ M.atoms) (h2 : v₂ ∈ M.atoms) (h3 : b ∈ M.atoms) (hα1 : (cls v₁).IsAlpha)
    (hα2 : (cls v₂).IsAlpha) (hβ : (cls b).IsBeta) (h12 : v₁ ≠ v₂) (h1b : v₁ ≠ b) (h2b : v₂ ≠ b)
    (d1 : M.deg v₁ = 2) (d2 : M.deg v₂ = 2) (d3 : M.deg b = 2)
    (h4 : ∀ v ∈ M.atoms, v ≠ v₁ → v ≠ v₂ → v ≠ b → M.deg v = 4)
    (hk1 : (cls v₁).kap = 0) (hk2 : (cls v₂).kap = 0)
    (hl1 : L ^ (-γ - 50 * η) < (cls v₁).lab) (hl2 : L ^ (-γ - 50 * η) < (cls v₂).lab)
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0)
    (hκ : M.IsDecoration L 0 c κ) (hA : Adm κ) :
    c v₁ + c v₂ + c b = 0 ∧ L ^ (-γ - 100 * η) / 2 ≤ ‖c v₁‖ ∧ L ^ (-γ - 100 * η) / 2 ≤ ‖c v₂‖ ∧
      L ^ (-γ - 100 * η) / 2 ≤ ‖c b‖ := by
  have hL0 : 0 < L := by linarith
  -- total charge
  have hsum : c v₁ + c v₂ + c b = 0 := by
    have hz := charge_sum_zero hκ
    have hsub : ({v₁, v₂, b} : Finset V) ⊆ M.atoms := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl | rfl <;> assumption
    rw [← sum_subset hsub (fun x hx hxn => by
      simp only [mem_insert, mem_singleton, not_or] at hxn
      exact hc x hx (h4 x hx hxn.1 hxn.2.1 hxn.2.2))] at hz
    rw [sum_insert (by simp [h12, h1b]), sum_pair h2b] at hz
    rw [← hz]; abel
  obtain ⟨o1, i1, ho1, hi1, hne1, hc1⟩ := charge_at_deg2 hS hκ h1 d1
  obtain ⟨o2, i2, ho2, hi2, hne2, hc2⟩ := charge_at_deg2 hS hκ h2 d2
  obtain ⟨o3, i3, ho3, hi3, hne3, hc3⟩ := charge_at_deg2 hS hκ h3 d3
  have hg1 := (hF.alphaGap κ hA v₁ h1 hα1 o1 i1 ho1 hi1 hne1).1
  have hg2 := (hF.alphaGap κ hA v₂ h2 hα2 o2 i2 ho2 hi2 hne2).1
  have hlow : ∀ R : ℝ, L ^ (-γ - 50 * η) < R → L ^ (-γ - 100 * η) / 2 ≤ R / 2 := by
    intro R hR
    have : L ^ (-γ - 100 * η) ≤ L ^ (-γ - 50 * η) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    linarith
  have hb1 : L ^ (-γ - 100 * η) / 2 ≤ ‖c v₁‖ := by rw [hc1]; exact (hlow _ hl1).trans hg1
  have hb2 : L ^ (-γ - 100 * η) / 2 ≤ ‖c v₂‖ := by rw [hc2]; exact (hlow _ hl2).trans hg2
  refine ⟨hsum, hb1, hb2, ?_⟩
  -- the `β`-charge by N2
  have hpos : ∀ R : ℝ, L ^ (-γ - 50 * η) < R → 0 < R / 2 := fun R hR => by
    have : 0 < L ^ (-γ - 50 * η) := Real.rpow_pos_of_pos hL0 _
    linarith
  have hr1 : Molecule.gapAt L 0 κ o1 i1 ≠ 0 := fun h => by
    rw [h, norm_zero] at hg1; linarith [hpos _ hl1]
  have hr2 : Molecule.gapAt L 0 κ o2 i2 ≠ 0 := fun h => by
    rw [h, norm_zero] at hg2; linarith [hpos _ hl2]
  have hr3 := hF.betaGap κ hA b h3 hβ o3 i3 ho3 hi3 hne3
  have hiota := hF.iota κ hA v₁ h1 v₂ h2 b h3 h12 hα1 hα2 hβ (by rw [hk1, hk2]) o1 i1 o2 i2 o3 i3 ho1 hi1 hne1
    ho2 hi2 hne2 ho3 hi3 hne3 hr1 hr2 hr3 ⟨-1, -1, Or.inr rfl, Or.inr rfl, by
      rw [← hc1, ← hc2, ← hc3, neg_smul, neg_smul, one_smul, one_smul]
      rw [← sub_eq_zero, ← hsum]; abel⟩
  rw [hc3]
  refine le_trans ?_ hiota
  have hmin : L ^ (-γ - 50 * η) ≤ min (cls v₁).lab (cls v₂).lab := le_min hl1.le hl2.le
  have e : L ^ (-γ - 100 * η) = L ^ (-50 * η) * L ^ (-γ - 50 * η) := by
    rw [← Real.rpow_add hL0]; congr 1; ring
  rw [e]
  have h0 : 0 ≤ L ^ (-50 * η) := (Real.rpow_pos_of_pos hL0 _).le
  have := mul_le_mul_of_nonneg_left hmin h0
  linarith

/-- The norm of `±x` (`dartSign`). -/
theorem norm_dartSign_smul (M : Molecule V D) {d : ℕ} (z : D) (x : Mom d) : ‖M.dartSign z • x‖ = ‖x‖ := by
  unfold Molecule.dartSign
  split_ifs
  · rw [one_smul]
  · rw [neg_smul, one_smul, norm_neg]

/-- The star sum over a set of atoms is its total charge. -/
theorem starSum_eq {M : Molecule V D} {d : ℕ} {L : ℝ} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hκ : M.IsDecoration L 0 c κ) {S : Finset V} (hS : S ⊆ M.atoms) :
    ∑ w ∈ S, ∑ z ∈ M.dartsAt w, M.dartSign z • Molecule.kvec L 0 κ z = ∑ w ∈ S, c w :=
  sum_congr rfl fun w hw => hκ.2 w (hS hw)

/-- The total charge of a chain `C ⊆ {v₂, β}`, `C ≠ ∅`, has norm `≥ ρ`. -/
theorem c6_chain_charge {d : ℕ} {c : V → Mom d} {v₁ v₂ b : V} {ρ : ℝ} (h2b : v₂ ≠ b)
    (hsum : c v₁ + c v₂ + c b = 0) (hb1 : ρ ≤ ‖c v₁‖) (hb2 : ρ ≤ ‖c v₂‖) (hb3 : ρ ≤ ‖c b‖) {C : Finset V}
    (hC : ∀ x ∈ C, x = v₂ ∨ x = b) (hne : C.Nonempty) : ρ ≤ ‖∑ x ∈ C, c x‖ := by
  by_cases h2 : v₂ ∈ C <;> by_cases h3 : b ∈ C
  · have hCe : C = {v₂, b} := by
      ext x; constructor
      · intro hx; rcases hC x hx with rfl | rfl <;> simp
      · intro hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
    rw [hCe, sum_pair h2b]
    have : c v₂ + c b = -c v₁ := by rw [← sub_eq_zero, ← hsum]; abel
    rw [this, norm_neg]; exact hb1
  · have hCe : C = {v₂} := by
      ext x; constructor
      · intro hx; rcases hC x hx with rfl | rfl
        · simp
        · exact absurd hx h3
      · intro hx; rw [mem_singleton.mp hx]; exact h2
    rw [hCe, sum_singleton]; exact hb2
  · have hCe : C = {b} := by
      ext x; constructor
      · intro hx; rcases hC x hx with rfl | rfl
        · exact absurd hx h2
        · simp
      · intro hx; rw [mem_singleton.mp hx]; exact h3
    rw [hCe, sum_singleton]; exact hb3
  · exfalso
    obtain ⟨x, hx⟩ := hne
    rcases hC x hx with rfl | rfl
    · exact h2 hx
    · exact h3 hx

/-- **The gap of a chain** `‖k_{mate y₁} − k_{mate y₂}‖ = ‖∑_C c‖`. -/
theorem chain_gap_norm {M : Molecule V D} {d : ℕ} {L : ℝ} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hκ : M.IsDecoration L 0 c κ) {C : Finset V} (hC : C ⊆ M.atoms) {y₁ y₂ : D} (hne : y₁ ≠ y₂)
    (hcross : crossDarts M C = {y₁, y₂}) (hdir : M.out y₁ ≠ M.out y₂) :
    ‖Molecule.kvec L 0 κ (M.mate y₁) - Molecule.kvec L 0 κ (M.mate y₂)‖ = ‖∑ v ∈ C, c v‖ := by
  rw [← chain_charge hκ hC hne hcross hdir, norm_dartSign_smul]

/-- The total charge of `insert p (insert q C)` with `c p = c q = 0`. -/
theorem sum_insert_two_zero {d : ℕ} {c : V → Mom d} {p q : V} {C : Finset V} (hpC : p ∉ C) (hqC : q ∉ C)
    (hpq : p ≠ q) (hp : c p = 0) (hq : c q = 0) : ∑ w ∈ insert p (insert q C), c w = ∑ w ∈ C, c w := by
  rw [sum_insert (by simp [hpq, hpC]), sum_insert hqC, hp, hq, zero_add, zero_add]

end

end WaveTurbulence.GammaLow.FinalCount.Count
