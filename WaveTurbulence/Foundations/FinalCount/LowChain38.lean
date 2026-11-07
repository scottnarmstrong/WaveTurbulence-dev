/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain37
public import WaveTurbulence.Foundations.FinalCount.LowChain8
/-! **FINALCOUNT LOW-CHAIN, session 6 (12): the `r = 1` LowFree lemma and `hZ_ofL`** (R79 NOTES §4, referee F1).
At `r = 1` with no tame atom, a degree-`2` `ε`-atom would have all other contributions `0`, hence balanced darts, hence an opposite pair
`(x, y)` with LG (nonzero) gap, which is a D3 pair (`D3Data`) that `NoD3` and `Desig` (a degree-2 hinge has its unique pair designated)
exclude; a degree-`1` `ε`-atom has contribution `3 > 2`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem lowFree_r1 {M₀ : Molecule V D₀} {C : CollData M₀} {hf : HSt V D₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    (hL : 0 < L) (hg : Good 1 hf.s) (hbal : BalS hf.s)
    (hND : ∀ (v : V) (x₁ x₂ : hf.s.D), D3Data hf v x₁ x₂ →
      pgap L w κ (hf.s.pr x₁ x₂) = 0 ∨ ¬ Desig C (hf.anc v) (hf.s.pr x₁ x₂))
    (hLG : ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a →
      hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .LG)
    (hDes : ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → hf.s.M.deg a = 2 → ∀ x y : hf.s.D, hf.s.M.atom x = a →
      hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
      Desig C (hf.anc a) (hf.s.pr x y)) :
    ∀ e ∈ hf.s.M.atoms, hf.s.cls e = .eps → 3 ≤ hf.s.M.deg e := by
  intro e he hε
  by_contra hlt
  push Not at hlt
  have hsum := hg.sum_contrib
  have hnn := fun a (ha : a ∈ hf.s.M.atoms) => Good.contrib_nonneg hg ha
  have hce : contrib hf.s e = 4 - hf.s.M.deg e := by unfold contrib; rw [hε]; simp [Cls.base]
  have hd1 := hg.1.eps e he hε
  have hsplit := Finset.add_sum_erase hf.s.M.atoms (contrib hf.s) he
  have hrest : 0 ≤ ∑ a ∈ hf.s.M.atoms.erase e, contrib hf.s a :=
    Finset.sum_nonneg fun a ha => hnn a (Finset.mem_of_mem_erase ha)
  have hd2 : hf.s.M.deg e = 2 := by
    by_contra hne
    have : hf.s.M.deg e = 1 := by omega
    omega
  have hrest0 : ∑ a ∈ hf.s.M.atoms.erase e, contrib hf.s a = 0 := by omega
  have hz : ∀ a ∈ hf.s.M.atoms.erase e, contrib hf.s a = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun a ha => hnn a (Finset.mem_of_mem_erase ha)).1 hrest0
  have hbd : ∀ a ∈ hf.s.M.atoms.erase e, hf.s.M.outdeg a = hf.s.M.indeg a := by
    intro a ha
    have haM := Finset.mem_of_mem_erase ha
    have h0 := hz a ha
    have hb := hg.1.bounds a haM
    have hdeq := deg_eq hf.s.M a
    unfold contrib at h0
    by_cases hεa : hf.s.cls a = .eps
    · rw [hεa] at h0; simp only [Cls.base] at h0; omega
    · have hab := hg.1.ab a haM hεa
      have hba := hbal.2 a haM hεa
      by_cases hgh : hf.s.cls a = .ghost
      · have := hab.2.1 hgh; omega
      · have hbase : (hf.s.cls a).base = 2 := by
          rcases hc : hf.s.cls a with _ | ⟨ρ, kp⟩ | _ | _
          · exact absurd hc hεa
          · simp [Cls.base]
          · simp [Cls.base]
          · exact absurd hc hgh
        have h2 : hf.s.M.deg a = 2 := by omega
        have := hba h2
        omega
  have hs := sum_outdeg_eq_sum_indeg hf.s.M
  have hsE : ∑ a ∈ hf.s.M.atoms.erase e, hf.s.M.outdeg a = ∑ a ∈ hf.s.M.atoms.erase e, hf.s.M.indeg a :=
    Finset.sum_congr rfl hbd
  have hs1 := Finset.add_sum_erase hf.s.M.atoms (fun a => hf.s.M.outdeg a) he
  have hs2 := Finset.add_sum_erase hf.s.M.atoms (fun a => hf.s.M.indeg a) he
  beta_reduce at hs1 hs2
  have hoi : hf.s.M.outdeg e = hf.s.M.indeg e := by omega
  have hdeq := deg_eq hf.s.M e
  have ho1 : hf.s.M.outdeg e = 1 := by omega
  have hi1 : hf.s.M.indeg e = 1 := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.1 (by unfold Molecule.indeg at hi1; omega : 0 < ((hf.s.M.dartsAt e).filter fun x => hf.s.M.out x = false).card)
  obtain ⟨y, hy⟩ := Finset.card_pos.1 (by unfold Molecule.outdeg at ho1; omega : 0 < ((hf.s.M.dartsAt e).filter fun x => hf.s.M.out x = true).card)
  obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
  obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
  have hxa : hf.s.M.atom x = e := by simpa [Molecule.dartsAt] using hx1
  have hya : hf.s.M.atom y = e := by simpa [Molecule.dartsAt] using hy1
  have hxo : hf.s.M.out x = false := hx2
  have hne : y ≠ hf.s.M.mate x := by
    intro h
    exact hg.1.noloop x (by rw [← h, hxa, hya])
  have hD : D3Data hf e x y := ⟨he, hε, hd2, hxa, hya, hne, hxo, hy2⟩
  have hlg := hLG e he hε x y hxa hya hxo hy2 hne
  have hdes := hDes e he hε hd2 x y hxa hya hxo hy2 hne
  rcases hND e x y hD with h0 | h0
  · have hn := lt_norm_of_LG hlg
    have hp : 0 < L ^ (-γ + η) := Real.rpow_pos_of_pos hL _
    have : Molecule.gapAt L w (κ ∘ hf.s.down) x y = 0 := h0
    rw [this, norm_zero] at hn
    linarith
  · exact h0 hdes

/-- **`hZ` of `term_exponentL`.** -/
theorem hZ_ofL {hf : HSt V D₀} {Tm : V → Prop} {R' r k : ℕ} {B : Finset V} (hg : Good R' hf.s) (hRk : r + k = R')
    (hBT : ∀ b ∈ B, b ∈ tameSet hf Tm) (hBdeg : ∀ b ∈ B, hf.s.M.deg b ≤ 2) (hBcard : B.card = k)
    {𝒦 : Finset (Finset V)} (h1 : 𝒦.biUnion id = tameSet hf Tm) {Rs : Finset V} (hR : CompRep (hf.op5 Tm).s.M Rs)
    (hLF1 : r = 1 → tameSet hf Tm = ∅ → ∀ e ∈ hf.s.M.atoms, hf.s.cls e = .eps → 3 ≤ hf.s.M.deg e) :
    ∑ a ∈ Rs.filter (fun a => ¬ UntCL hf Tm r a),
        (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) ≤
      (eDart hf.s.M (tameSet hf Tm) : ℝ) + 4 * (((r - 1 : ℕ) : ℝ)) + 3 * (𝒦.card : ℝ) := by
  have h2 := eps_defect_le_L hg hRk hBT hBdeg hBcard hR
  have h3 : ∑ a ∈ Rs.filter (fun a => ¬ UntCL hf Tm r a),
      (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) ≤
      ∑ a ∈ Rs, (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
  have h4 : ∑ a ∈ Rs, (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) ≤
      (eDart hf.s.M (tameSet hf Tm) : ℝ) + 2 * r := by
    rw [← Nat.cast_sum]; exact_mod_cast h2
  have hq0 : (0 : ℝ) ≤ 𝒦.card := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ eDart hf.s.M (tameSet hf Tm) := Nat.cast_nonneg _
  rcases Nat.lt_or_ge 1 r with hr2 | hr2
  · have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    have hc : (((r - 1 : ℕ) : ℝ)) = (r : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hc]; linarith
  · by_cases hr0 : r = 0
    · subst hr0; simp at h4 ⊢; linarith
    · have hr1 : r = 1 := by omega
      subst hr1
      by_cases hK : 𝒦 = ∅
      · have hT : tameSet hf Tm = ∅ := by rw [← h1, hK]; simp
        have hall : Rs.filter (fun a => ¬ UntCL hf Tm 1 a) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro a _
          refine not_not.2 ⟨fun e he _ hε hTm => ?_, fun e he hε => ?_, fun _ => rfl⟩
          · have : e ∈ tameSet hf Tm := tameSet_mem.2 ⟨he, hε, hTm⟩
            rw [hT] at this; simp at this
          · have he' : e ∈ hf.s.M.atoms ∧ hf.s.M.SameComponent a e := by
              unfold compAtoms at he; exact Finset.mem_filter.1 he
            exact hLF1 rfl hT e he'.1 hε
        rw [hall]
        simp only [Finset.sum_empty]
        positivity
      · have : 1 ≤ 𝒦.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hK)
        have : (1 : ℝ) ≤ 𝒦.card := by exact_mod_cast this
        simp at h4 ⊢
        linarith

end WaveTurbulence.FinalCountAsm
