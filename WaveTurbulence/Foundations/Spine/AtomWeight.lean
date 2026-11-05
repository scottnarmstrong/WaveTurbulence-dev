/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IndGood
public import WaveTurbulence.Foundations.Spine.SourceLocalLadder
/-! # The weight of one interior atom (S3b LADDER-DECAY)

For an interior atom with relative slot labels `-τ_s(p) - cs_s`, the epsilon factor and the gap
indicator are good sums of indicators of slot-difference forms. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset WaveTurbulence WaveTurbulence.WeylSums WaveTurbulence.LGSpine

variable {d n : ℕ}

lemma tvecHom_form (j j' : Fin 4) (h : j ≠ j') :
    AxisX (tvecHom j - tvecHom j' : Pt d →+ (Fin d → ℤ)) ∨ AxisY (tvecHom j - tvecHom j' : Pt d →+ (Fin d → ℤ)) ∨
      DiagF (tvecHom j - tvecHom j' : Pt d →+ (Fin d → ℤ)) := by
  have hj : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  rcases hj j with rfl | rfl | rfl | rfl <;> rcases hj j' with rfl | rfl | rfl | rfl <;>
    try (first | exact (h rfl).elim | (simp at h; done))
  all_goals first
    | (refine Or.inl (Or.inl ?_); intro p; simp [tvecHom, tvec, sub_eq_add_neg]; first | done | (abel_nf; done))
    | (refine Or.inl (Or.inr ?_); intro p; simp [tvecHom, tvec, sub_eq_add_neg]; first | done | (abel_nf; done))
    | (refine Or.inr (Or.inl (Or.inl ?_)); intro p; simp [tvecHom, tvec, sub_eq_add_neg]; first | done | (abel_nf; done))
    | (refine Or.inr (Or.inl (Or.inr ?_)); intro p; simp [tvecHom, tvec, sub_eq_add_neg]; first | done | (abel_nf; done))
    | (refine Or.inr (Or.inr ⟨1, 1, Or.inl rfl, Or.inl rfl, ?_⟩); intro p; simp [tvecHom, tvec, sub_eq_add_neg]; first | done | (abel_nf; done))
    | (refine Or.inr (Or.inr ⟨1, -1, Or.inl rfl, Or.inr rfl, ?_⟩); intro p; simp [tvecHom, tvec, sub_eq_add_neg]; first | done | (abel_nf; done))
    | (refine Or.inr (Or.inr ⟨-1, 1, Or.inr rfl, Or.inl rfl, ?_⟩); intro p; simp [tvecHom, tvec, sub_eq_add_neg]; first | done | (abel_nf; done))
    | (refine Or.inr (Or.inr ⟨-1, -1, Or.inr rfl, Or.inr rfl, ?_⟩); intro p; simp [tvecHom, tvec, sub_eq_add_neg]; first | done | abel_nf)

lemma tvecHom_axis (j j' : Fin 4) (h : (j.1 < 2) ≠ (j'.1 < 2)) :
    AxisX (tvecHom j - tvecHom j' : Pt d →+ (Fin d → ℤ)) ∨ AxisY (tvecHom j - tvecHom j' : Pt d →+ (Fin d → ℤ)) := by
  have hj : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  rcases hj j with rfl | rfl | rfl | rfl <;> rcases hj j' with rfl | rfl | rfl | rfl <;>
    try (first | exact (h rfl).elim | (simp at h; done))
  all_goals first
    | (refine Or.inl (Or.inl ?_); intro p; simp [tvecHom, tvec, sub_eq_add_neg]; first | done | (abel_nf; done))
    | (refine Or.inl (Or.inr ?_); intro p; simp [tvecHom, tvec, sub_eq_add_neg]; first | done | (abel_nf; done))
    | (refine Or.inr (Or.inl ?_); intro p; simp [tvecHom, tvec, sub_eq_add_neg]; first | done | (abel_nf; done))
    | (refine Or.inr (Or.inr ?_); intro p; simp [tvecHom, tvec, sub_eq_add_neg])

/-- Relative label of slot `s` of an atom of the chart (anchor dropped). -/
def relLab (S : ChainSigns n) (i : Fin n) (cs : Fin 4 → (Fin d → ℤ)) (s : Fin 4) (p : Pt d) :
    Fin d → ℤ := -(tauHom S i s p) - cs s

lemma relLab_sub (S : ChainSigns n) (i : Fin n) (cs : Fin 4 → (Fin d → ℤ)) (s s' : Fin 4) (p : Pt d) :
    relLab S i cs s' p - relLab S i cs s p =
      ((tvecHom ((S.σ i).symm s) - tvecHom ((S.σ i).symm s') : Pt d →+ (Fin d → ℤ)) p) +
        (cs s - cs s') := by
  unfold relLab tauHom
  simp only [AddMonoidHom.sub_apply]
  abel

lemma eqInd_good {L R : ℝ} {a b : Fin d → ℝ} {m : Pt d →+ (Fin d → ℤ)} (hL : 0 < L) (hR : 0 ≤ R)
    (hm : AxisX m ∨ AxisY m ∨ DiagF m) (c : Fin d → ℤ) : GoodTerm L R a b (eqInd m c) := by
  rcases hm with hm | hm | hm
  · exact eqInd_goodX hm c hR
  · exact eqInd_goodY hm c hR
  · exact eqInd_goodDiag hm c hL

lemma eps_goodSum {L R : ℝ} {a b : Fin d → ℝ} (hL : 0 < L) (hR : 0 ≤ R) (S : ChainSigns n) (i : Fin n)
    (cs : Fin 4 → (Fin d → ℤ)) {k1 k2 k3 : Fin 4} (h12 : k1 ≠ k2) (h23 : k2 ≠ k3) :
    GoodSum L R a b (Fin 3) (fun p => epsCoef (relLab S i cs k1 p) (relLab S i cs k2 p)
      (relLab S i cs k3 p)) := by
  set m1 : Pt d →+ (Fin d → ℤ) := tvecHom ((S.σ i).symm k1) - tvecHom ((S.σ i).symm k2) with hm1
  set m2 : Pt d →+ (Fin d → ℤ) := tvecHom ((S.σ i).symm k2) - tvecHom ((S.σ i).symm k3) with hm2
  have f1 := tvecHom_form (d := d) ((S.σ i).symm k1) ((S.σ i).symm k2)
    (fun h => h12 ((S.σ i).symm.injective h))
  have f2 := tvecHom_form (d := d) ((S.σ i).symm k2) ((S.σ i).symm k3)
    (fun h => h23 ((S.σ i).symm.injective h))
  refine ⟨![1, -1, -1], ![fun _ => 1, eqInd m1 (cs k1 - cs k2), eqInd m2 (cs k2 - cs k3)], ?_, ?_, ?_⟩
  · intro j; fin_cases j <;> simp
  · intro j; fin_cases j
    · exact goodTerm_one L R a b
    · exact eqInd_good hL hR f1 _
    · exact eqInd_good hL hR f2 _
  · intro p
    dsimp only
    rw [epsCoef_eq_sub, Fin.sum_univ_three]
    have e1 : relLab S i cs k2 p = relLab S i cs k1 p ↔ m1 p + (cs k1 - cs k2) = 0 := by
      rw [← relLab_sub S i cs k1 k2 p, sub_eq_zero]
    have e2 : relLab S i cs k2 p = relLab S i cs k3 p ↔ m2 p + (cs k2 - cs k3) = 0 := by
      rw [← relLab_sub S i cs k2 k3 p, sub_eq_zero]; exact eq_comm
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, eqInd, e1, e2]
    ring

/-- The gap indicator of an atom with relative labels. -/
noncomputable def gapW (L γ η : ℝ) (S : ChainSigns n) (i : Fin n) (cs : Fin 4 → (Fin d → ℤ))
    (gap : Option (Fin 4 × Fin 4 × Molecule.GapKind)) (p : Pt d) : ℝ :=
  match gap with
  | none => 1
  | some g => if Molecule.gapKind L γ η (latticePoint L (relLab S i cs g.1 p - relLab S i cs g.2.1 p))
      = g.2.2 then 1 else 0

lemma latticePoint_eq_zero_iff {L : ℝ} (hL : L ≠ 0) (v : Fin d → ℤ) :
    latticePoint L v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply latticePoint_injective (d := d) hL
    rw [h]; ext j; simp [latticePoint]
  · rintro rfl; ext j; simp [latticePoint]

lemma gapKind_cases (L γ η : ℝ) (r : Mom d) :
    (Molecule.gapKind L γ η r = Molecule.GapKind.ZG ∧ r = 0) ∨
    (Molecule.gapKind L γ η r = Molecule.GapKind.SG ∧ r ≠ 0 ∧ ‖r‖ ≤ L ^ (-γ + η)) ∨
    (Molecule.gapKind L γ η r = Molecule.GapKind.LG ∧ r ≠ 0 ∧ ¬ ‖r‖ ≤ L ^ (-γ + η)) := by
  unfold Molecule.gapKind
  by_cases h0 : r = 0
  · left; simp [h0]
  · by_cases h1 : ‖r‖ ≤ L ^ (-γ + η)
    · right; left; simp [h0, h1]
    · right; right; simp [h0, h1]

lemma gapKind_iff {L : ℝ} (hL : 0 < L) (γ η : ℝ) (hρ : 0 ≤ L ^ (-γ + η)) (v : Fin d → ℤ) :
    (Molecule.gapKind L γ η (latticePoint L v) = Molecule.GapKind.ZG ↔ v = 0) ∧
    (Molecule.gapKind L γ η (latticePoint L v) = Molecule.GapKind.SG ↔
      (v ≠ 0 ∧ ‖latticePoint L v‖ ≤ L ^ (-γ + η))) ∧
    (Molecule.gapKind L γ η (latticePoint L v) = Molecule.GapKind.LG ↔
      ¬ ‖latticePoint L v‖ ≤ L ^ (-γ + η)) := by
  have hz := latticePoint_eq_zero_iff (d := d) hL.ne' v
  rcases gapKind_cases L γ η (latticePoint L v) with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hv : v = 0 := hz.mp h2
    subst hv
    have : ‖latticePoint L (0 : Fin d → ℤ)‖ = 0 := by
      rw [show latticePoint L (0 : Fin d → ℤ) = 0 from hz.mpr rfl]; simp
    simp [h1, this, hρ]
  · have hv : v ≠ 0 := fun h => h2 (hz.mpr h)
    simp [h1, hv, h3]
  · have hv : v ≠ 0 := fun h => h2 (hz.mpr h)
    simp [h1, hv, h3]

lemma gap_goodSum {L R : ℝ} {a b : Fin d → ℝ} (γ η : ℝ) (hL : 0 < L) (hρ : 0 ≤ L ^ (-γ + η))
    (hR : L * L ^ (-γ + η) ≤ R) (S : ChainSigns n) (i : Fin n) (cs : Fin 4 → (Fin d → ℤ))
    (gap : Option (Fin 4 × Fin 4 × Molecule.GapKind))
    (hgap : ∀ g, gap = some g → S.sg i g.1 ≠ S.sg i g.2.1) :
    GoodSum L R a b (Fin 2) (gapW L γ η S i cs gap) := by
  have hR0 : 0 ≤ R := le_trans (mul_nonneg hL.le hρ) hR
  rcases gap with _ | ⟨kf, ks, kd⟩
  · refine ⟨![1, 0], ![fun _ => 1, fun _ => 1], ?_, ?_, ?_⟩
    · intro j; fin_cases j <;> simp
    · intro j; fin_cases j <;> exact goodTerm_one L R a b
    · intro p; simp [gapW, Fin.sum_univ_two]
  · have hne := hgap (kf, ks, kd) rfl
    simp only at hne
    set m : Pt d →+ (Fin d → ℤ) := tvecHom ((S.σ i).symm ks) - tvecHom ((S.σ i).symm kf) with hm
    have hax : AxisX m ∨ AxisY m := by
      apply tvecHom_axis
      intro h
      apply hne
      have e1 := sg_sigma S i ((S.σ i).symm kf)
      have e2 := sg_sigma S i ((S.σ i).symm ks)
      rw [Equiv.apply_symm_apply] at e1 e2
      rw [e1, e2]
      have hh : ((↑((S.σ i).symm ks) : ℕ) < 2) ↔ ((↑((S.σ i).symm kf) : ℕ) < 2) := Iff.of_eq h
      by_cases hA : ((↑((S.σ i).symm kf) : ℕ) < 2) <;> simp [hA, hh]
    set c : Fin d → ℤ := cs ks - cs kf with hc
    have hv : ∀ p, gapW L γ η S i cs (some (kf, ks, kd)) p =
        if Molecule.gapKind L γ η (latticePoint L (m p + c)) = kd then 1 else 0 := by
      intro p
      simp only [gapW]
      rw [relLab_sub S i cs ks kf p]
    have gE : GoodTerm L R a b (eqInd m c) := eqInd_good hL hR0 (by tauto) c
    have gB : GoodTerm L R a b (ballInd L (L ^ (-γ + η)) m c) := by
      rcases hax with hax | hax
      · exact ballInd_goodX hax c hL hR
      · exact ballInd_goodY hax c hL hR
    refine ?_
    cases kd
    · refine ⟨![1, 0], ![eqInd m c, fun _ => 1], ?_, ?_, ?_⟩
      · intro j; fin_cases j <;> simp
      · intro j; fin_cases j
        · exact gE
        · exact goodTerm_one L R a b
      · intro p
        rw [hv p]
        have key := (gapKind_iff hL γ η hρ (m p + c)).1
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, eqInd]
        generalize m p + c = v at key ⊢
        by_cases h : v = 0
        · subst h; simp [key]
        · simp [h, key]
    · refine ⟨![1, -1], ![ballInd L (L ^ (-γ + η)) m c, eqInd m c], ?_, ?_, ?_⟩
      · intro j; fin_cases j <;> simp
      · intro j; fin_cases j
        · exact gB
        · exact gE
      · intro p
        rw [hv p]
        have key := (gapKind_iff hL γ η hρ (m p + c)).2.1
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, eqInd, ballInd]
        generalize m p + c = v at key ⊢
        have h0 : ‖latticePoint L (0 : Fin d → ℤ)‖ ≤ L ^ (-γ + η) := by
          rw [show latticePoint L (0 : Fin d → ℤ) = 0 by ext j; simp [latticePoint]]
          simpa using hρ
        by_cases h : v = 0
        · subst h; simp [key, h0]
        · by_cases h2 : ‖latticePoint L v‖ ≤ L ^ (-γ + η) <;> simp [h, h2, key]
    · refine ⟨![1, -1], ![fun _ => 1, ballInd L (L ^ (-γ + η)) m c], ?_, ?_, ?_⟩
      · intro j; fin_cases j <;> simp
      · intro j; fin_cases j
        · exact goodTerm_one L R a b
        · exact gB
      · intro p
        rw [hv p]
        have key := (gapKind_iff hL γ η hρ (m p + c)).2.2
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ballInd]
        generalize m p + c = v at key ⊢
        by_cases h2 : ‖latticePoint L v‖ ≤ L ^ (-γ + η) <;> simp [h2, key]

/-- **The weight of one atom is a good sum of 6 terms.** -/
theorem atom_goodSum {L R : ℝ} {a b : Fin d → ℝ} (γ η : ℝ) (hL : 0 < L) (hρ : 0 ≤ L ^ (-γ + η))
    (hR : L * L ^ (-γ + η) ≤ R) (S : ChainSigns n) (i : Fin n) (cs : Fin 4 → (Fin d → ℤ))
    {k1 k2 k3 : Fin 4} (h12 : k1 ≠ k2) (h23 : k2 ≠ k3)
    (gap : Option (Fin 4 × Fin 4 × Molecule.GapKind))
    (hgap : ∀ g, gap = some g → S.sg i g.1 ≠ S.sg i g.2.1) :
    GoodSum L R a b (Fin 3 × Fin 2) (fun p => epsCoef (relLab S i cs k1 p) (relLab S i cs k2 p)
      (relLab S i cs k3 p) * gapW L γ η S i cs gap p) :=
  GoodSum.mul hL.le (le_trans (mul_nonneg hL.le hρ) hR) (eps_goodSum hL (le_trans (mul_nonneg hL.le hρ) hR) S i cs h12 h23)
    (gap_goodSum γ η hL hρ hR S i cs gap hgap)

end WaveTurbulence.LadderDecay
