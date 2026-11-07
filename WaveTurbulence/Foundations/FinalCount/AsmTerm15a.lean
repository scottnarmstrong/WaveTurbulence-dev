/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm14c
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 15a: the `ε`-defect `Z₅ ≤ e + 4(R-1) + 3q`.** -/
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

/-- The atoms outside `E` having a bond into `E` number at most `eDart M E`. -/
theorem touched_card_le {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (E : Finset V) :
    (M.atoms.filter fun v => v ∉ E ∧ 1 ≤ multS M E v).card ≤ eDart M E := by
  have h1 : (Finset.univ.filter fun x : D => M.atom (M.mate x) ∈ E ∧ M.atom x ∉ E).card = eDart M E := by
    unfold eDart
    refine Finset.card_bij (fun x _ => M.mate x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [M.mate_mate]; exact ⟨hx.1, hx.2⟩
    · intro x _ y _ e; simpa [M.mate_mate] using congrArg M.mate e
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨M.mate y, ?_, M.mate_mate y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [M.mate_mate]; exact ⟨hy.1, hy.2⟩
  rw [← h1]
  refine le_trans (Finset.card_le_card (t := (Finset.univ.filter fun x : D => M.atom (M.mate x) ∈ E ∧ M.atom x ∉ E).image M.atom) ?_)
    Finset.card_image_le
  intro v hv
  obtain ⟨hvM, hvE, hm⟩ := Finset.mem_filter.1 hv
  unfold multS at hm
  obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega : 0 < ((M.dartsAt v).filter fun x => M.atom (M.mate x) ∈ E).card)
  obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
  have hxa : M.atom x = v := by simpa [Molecule.dartsAt] using hx1
  exact Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx2, by rw [hxa]; exact hvE⟩, hxa⟩

/-- **`Z₅ ≤ e + 2R`:** the surviving `ε`-atoms of degree `≠ 4` are touched by the erased set or are among the `2R` odd atoms. -/
theorem eps_defect_le {hf : HSt V D₀} {Tm : V → Prop} {R : ℕ} (hst : FinalStructE R 0 hf.s)
    {Rs : Finset V} (hR : CompRep (hf.op5 Tm).s.M Rs) :
    ∑ a ∈ Rs, WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) ≤
      eDart hf.s.M (tameSet hf Tm) + 2 * R := by
  set M5 := (hf.op5 Tm).s.M with hM5
  have hsum : ∑ a ∈ Rs, WaveTurbulence.FinalCountG8.epsDefect (compMol M5 a) (cl8 hf) =
      (M5.atoms.filter fun v => hf.s.cls v = .eps ∧ M5.deg v ≠ 4).card := by
    unfold WaveTurbulence.FinalCountG8.epsDefect
    simp only [Finset.card_filter, compMol_atoms_eq]
    rw [hR.sum_atoms (fun v => if hf.s.cls v = .eps ∧ M5.deg v ≠ 4 then 1 else 0)]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun v hv => ?_
    have hsc := (Finset.mem_filter.1 hv).2
    rw [compMol_deg _ _ hsc]
    simp only [cl8, g8Cls_isEps, toCls_isEps]
  rw [hsum]
  set T := tameSet hf Tm with hT
  have hodd := hst.odd_card rfl
  have hsub : (M5.atoms.filter fun v => hf.s.cls v = .eps ∧ M5.deg v ≠ 4) ⊆
      (M5.atoms.filter fun v => v ∉ T ∧ 1 ≤ multS hf.s.M T v) ∪
        (hf.s.M.atoms.filter fun a => ¬ Even (hf.s.M.deg a)) := by
    intro v hv
    obtain ⟨hv5, hε, hd⟩ := Finset.mem_filter.1 hv
    obtain ⟨hvM, hvT⟩ := Op5.atoms_sub hv5
    have hk : keepS hf.s T v := (Finset.mem_filter.1 hv5).2
    have hd5 : M5.deg v = (eraseSet hf.s.M T).deg v := eraseSetSt_deg hk
    have hdc := eraseSet_deg_card hf.s.M T hvT
    by_cases hm : 1 ≤ multS hf.s.M T v
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hv5, hvT, hm⟩)
    · apply Finset.mem_union_right
      refine Finset.mem_filter.2 ⟨hvM, ?_⟩
      have h3 := hst.eps_deg rfl v hvM hε
      have h4 := (hst.deg_range v hvM).2
      have hm0 : multS hf.s.M T v = 0 := by omega
      have : hf.s.M.deg v = 3 := by omega
      rw [this]; decide
  calc _ ≤ ((M5.atoms.filter fun v => v ∉ T ∧ 1 ≤ multS hf.s.M T v) ∪
        (hf.s.M.atoms.filter fun a => ¬ Even (hf.s.M.deg a))).card := Finset.card_le_card hsub
    _ ≤ (M5.atoms.filter fun v => v ∉ T ∧ 1 ≤ multS hf.s.M T v).card +
        (hf.s.M.atoms.filter fun a => ¬ Even (hf.s.M.deg a)).card := Finset.card_union_le _ _
    _ ≤ eDart hf.s.M T + 2 * R := by
        rw [hodd]
        refine Nat.add_le_add_right (le_trans (Finset.card_le_card ?_) (touched_card_le hf.s.M T)) _
        intro v hv
        obtain ⟨hv5, hh⟩ := Finset.mem_filter.1 hv
        exact Finset.mem_filter.2 ⟨(Op5.atoms_sub hv5).1, hh⟩


/-- **`hZ` of `term_exponent`.** -/
theorem hZ_of {hf : HSt V D₀} {Tm : V → Prop} {R : ℕ} (hst : FinalStructE R 0 hf.s) (hR1 : 1 ≤ R)
    {𝒦 : Finset (Finset V)} (h1 : 𝒦.biUnion id = tameSet hf Tm) {Rs : Finset V} (hR : CompRep (hf.op5 Tm).s.M Rs) :
    ∑ a ∈ Rs.filter (fun a => ¬ UntC hf Tm R a),
        (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) ≤
      (eDart hf.s.M (tameSet hf Tm) : ℝ) + 4 * ((R : ℝ) - 1) + 3 * (𝒦.card : ℝ) := by
  have h2 := eps_defect_le hst hR
  have h3 : ∑ a ∈ Rs.filter (fun a => ¬ UntC hf Tm R a),
      (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) ≤
      ∑ a ∈ Rs, (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
  have h4 : ∑ a ∈ Rs, (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) ≤
      (eDart hf.s.M (tameSet hf Tm) : ℝ) + 2 * R := by
    rw [← Nat.cast_sum]; exact_mod_cast h2
  have hq0 : (0 : ℝ) ≤ 𝒦.card := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ eDart hf.s.M (tameSet hf Tm) := Nat.cast_nonneg _
  rcases Nat.lt_or_ge 1 R with hR2 | hR2
  · have : (2 : ℝ) ≤ R := by exact_mod_cast hR2
    linarith
  · have hR1' : R = 1 := by omega
    by_cases hD : (Rs.filter (fun a => ¬ UntC hf Tm R a)) = ∅
    · rw [hD]; simp only [Finset.sum_empty]; subst hR1'; push_cast; linarith
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hD
      obtain ⟨haR, hna⟩ := Finset.mem_filter.1 ha
      have hnt : ¬ TameFree hf Tm a := fun h => hna ⟨h, fun _ => hR1'⟩
      unfold TameFree at hnt
      push_neg at hnt
      obtain ⟨e, he, -, hε, hTe⟩ := hnt
      have heT : e ∈ 𝒦.biUnion id := by rw [h1]; exact tameSet_mem.2 ⟨he, hε, hTe⟩
      obtain ⟨K, hK, -⟩ := Finset.mem_biUnion.1 heT
      have : 1 ≤ 𝒦.card := Finset.card_pos.2 ⟨K, hK⟩
      have : (1 : ℝ) ≤ 𝒦.card := by exact_mod_cast this
      subst hR1'; push_cast at h4 ⊢; linarith

end WaveTurbulence.FinalCountAsm
