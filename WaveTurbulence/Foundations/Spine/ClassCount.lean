/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.KernelCore
/-! # Counting the classes of decorations (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Finset

variable {w d : ℕ} {G : Garden w}

/-- The centre attached to a dart: that of the outgoing dart of its bond. -/
noncomputable def dartCtr (D : SplicedKernelData G d) (x : GardenDart G) : Mom d :=
  if G.molecule.out x = true then D.center x else D.center (G.molecule.mate x)

/-- A decoration of nonzero weight has all group labels within one of the centre. -/
lemma label_in_ball (hP : G.IsPlain) {L : ℝ} (hL : 0 < L) (base : Mom d) (D : SplicedKernelData G d)
    (hD : SplicedAmplitudeBounds G D) (S : Finset (GBranch G.tree)) (γ η : ℝ)
    (roots : Fin w → (Fin d → ℤ)) (boundary : GardenDart G → (Fin d → ℤ))
    (z : ↥(localLadderDecorations G S roots boundary))
    (hzw : ladderWeight D S L γ η base z.1.1 ≠ 0) (x : GardenDart G) (hg : G.molecule.InGroup S x) :
    ‖(base - dartCtr D x) + latticePoint L (bondIndex G z.1.1 x)‖ ≤ 1 := by
  have hamp : ∀ y ∈ G.molecule.bonds.filter (G.molecule.InGroup S),
      ‖base + latticePoint L (bondIndex G z.1.1 y) - D.center y‖ ≤ 1 := by
    intro y hy
    have hne : D.edgeAmplitude y (base + latticePoint L (bondIndex G z.1.1 y)) ≠ 0 := by
      intro h0
      apply hzw
      unfold ladderWeight
      have : (∏ x ∈ G.molecule.bonds.filter (G.molecule.InGroup S),
          D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1.1 x))) = 0 :=
        Finset.prod_eq_zero hy h0
      rw [this, mul_zero]
    by_contra hcon
    push_neg at hcon
    exact hne ((hD.2.1 y (Finset.mem_filter.mp hy).1).2 _ hcon)
  have hmate : bondIndex G z.1.1 (G.molecule.mate x) = bondIndex G z.1.1 x := by
    rw [bondIndex_eq_restrict]
    exact Mole.restrictLabels_mate G z.1.1 z.1.2.1.2 x
  unfold dartCtr
  by_cases ho : G.molecule.out x = true
  · rw [if_pos ho]
    have := hamp x (Finset.mem_filter.mpr ⟨by simp [Molecule.bonds, ho], hg⟩)
    have e : (base - D.center x) + latticePoint L (bondIndex G z.1.1 x) =
        base + latticePoint L (bondIndex G z.1.1 x) - D.center x := by abel
    rw [e]; exact this
  · rw [if_neg ho]
    have hom : G.molecule.out (G.molecule.mate x) = true := by
      rw [G.molecule.out_mate]; simpa using ho
    have hgm : G.molecule.InGroup S (G.molecule.mate x) := by
      refine ⟨hg.2, ?_⟩; rw [G.molecule.mate_mate]; exact hg.1
    have := hamp _ (Finset.mem_filter.mpr ⟨by simp [Molecule.bonds, hom], hgm⟩)
    rw [hmate] at this
    have e : (base - D.center (G.molecule.mate x)) + latticePoint L (bondIndex G z.1.1 x) =
        base + latticePoint L (bondIndex G z.1.1 x) - D.center (G.molecule.mate x) := by abel
    rw [e]; exact this

/-- The integer points near a centre. -/
noncomputable def ballBox (L : ℝ) (base c : Mom d) : Finset (Fin d → ℤ) :=
  Counting.latticeBox (fun j => L * (c j - base j)) L

lemma mem_ballBox {L : ℝ} (hL : 0 < L) {base c : Mom d} {n : Fin d → ℤ}
    (h : ‖(base - c) + latticePoint L n‖ ≤ 1) : n ∈ ballBox L base c := by
  unfold ballBox
  rw [Counting.mem_latticeBox]
  intro j
  have h1 := PiLp.norm_apply_le ((base - c) + latticePoint L n) j
  rw [Real.norm_eq_abs] at h1
  have h2 : |((base - c) + latticePoint L n) j| ≤ 1 := h1.trans h
  have e : ((base - c) + latticePoint L n) j = base j - c j + (n j : ℝ) / L := by
    simp [latticePoint]
  rw [e] at h2
  have h3 : |(n j : ℝ) - L * (c j - base j)| = L * |base j - c j + (n j : ℝ) / L| := by
    have : (n j : ℝ) - L * (c j - base j) = L * (base j - c j + (n j : ℝ) / L) := by field_simp; ring
    rw [this, abs_mul, abs_of_pos hL]
  rw [h3]
  nlinarith

lemma card_ballBox_le {L : ℝ} (hL : 0 < L) (base c : Mom d) :
    ((ballBox L base c).card : ℝ) ≤ (2 * L + 1) ^ d :=
  Counting.card_latticeBox_le _ hL.le

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDarts.Ctx G.molecule u v)

include C in
lemma card_end_atoms : ((Molecule.ladderAtoms u v) \ intAtoms u v).card ≤ 4 := by
  classical
  have hsub : (Molecule.ladderAtoms u v) \ intAtoms u v ⊆
      ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1))).image u ∪
        ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1))).image v := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_sdiff.mp ha
    unfold Molecule.ladderAtoms at ha1
    rcases Finset.mem_union.mp ha1 with h | h
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h
      apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
      by_contra hj
      apply ha2
      refine (C.u_mem_intAtoms j).mpr ⟨?_, ?_⟩ <;> intro h' <;> apply hj <;> simp [h']
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
      by_contra hj
      apply ha2
      refine (C.v_mem_intAtoms j).mpr ⟨?_, ?_⟩ <;> intro h' <;> apply hj <;> simp [h']
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have h2 : ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1))).card ≤ 2 := Finset.card_le_two
  have h3 := Finset.card_image_le (s := ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1)))) (f := u)
  have h4 := Finset.card_image_le (s := ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1)))) (f := v)
  omega


open scoped Classical in
include C in
/-- **The number of classes.** -/
theorem class_count (hP : G.IsPlain) {L : ℝ} (hL : 0 < L) (base : Mom d) (D : SplicedKernelData G d)
    (hD : SplicedAmplitudeBounds G D) (γ η : ℝ) (roots : Fin w → (Fin d → ℤ))
    (boundary : GardenDart G → (Fin d → ℤ))
    (T : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary))
    (hT : ∀ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 ≠ 0) :
    ((T.image (fun z => clsOf (u := u) (v := v) z.1)).card : ℝ) ≤ ((2 * L + 1) ^ d) ^ 16 := by
  set F' : GardenDart G → Finset (Fin d → ℤ) := fun x =>
    if G.molecule.atom x ∈ intAtoms u v then {0}
    else if G.molecule.InGroup (Molecule.ladderAtoms u v) x then ballBox L base (dartCtr D x) else {boundary x} with hF'
  have hsub : T.image (fun z => clsOf (u := u) (v := v) z.1) ⊆ Fintype.piFinset F' := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    rw [Fintype.mem_piFinset]
    intro x
    simp only [hF', clsOf]
    by_cases hi : G.molecule.atom x ∈ intAtoms u v
    · simp [hi]
    · by_cases hg : G.molecule.InGroup (Molecule.ladderAtoms u v) x
      · simp only [hi, hg, if_false, if_true]
        exact mem_ballBox hL (label_in_ball hP hL base D hD (Molecule.ladderAtoms u v) γ η roots boundary z (hT z hz) x hg)
      · simp only [hi, hg, if_false]
        simp [z.2 x hg]
  have hcard := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at hcard
  set K : ℝ := (2 * L + 1) ^ d with hK
  have hK1 : 1 ≤ K := one_le_pow₀ (by linarith)
  set Dnt : Finset (GardenDart G) := Finset.univ.filter
    (fun x => G.molecule.atom x ∉ intAtoms u v ∧ G.molecule.InGroup (Molecule.ladderAtoms u v) x) with hDnt
  have hDntcard : Dnt.card ≤ 16 := by
    have hsub2 : Dnt ⊆ (Molecule.ladderAtoms u v \ intAtoms u v).biUnion (fun a => G.molecule.dartsAt a) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := (Finset.mem_filter.mp hx).2
      refine Finset.mem_biUnion.mpr ⟨G.molecule.atom x, Finset.mem_sdiff.mpr ⟨hx2.1, hx1⟩, ?_⟩
      rw [Molecule.dartsAt, Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩
    refine (Finset.card_le_card hsub2).trans ((Finset.card_biUnion_le).trans ?_)
    have : ∀ a ∈ Molecule.ladderAtoms u v \ intAtoms u v, (G.molecule.dartsAt a).card ≤ 4 := fun a _ => C.hdeg a
    calc ∑ a ∈ Molecule.ladderAtoms u v \ intAtoms u v, (G.molecule.dartsAt a).card ≤ ∑ _a ∈ Molecule.ladderAtoms u v \ intAtoms u v, 4 :=
          Finset.sum_le_sum this
      _ = (Molecule.ladderAtoms u v \ intAtoms u v).card * 4 := by simp
      _ ≤ 4 * 4 := Nat.mul_le_mul_right 4 C.card_end_atoms
  have hprod : ((∏ x : GardenDart G, (F' x).card : ℕ) : ℝ) ≤ K ^ 16 := by
    push_cast
    have h1 : ∀ x : GardenDart G, ((F' x).card : ℝ) ≤ if x ∈ Dnt then K else 1 := by
      intro x
      by_cases hx : x ∈ Dnt
      · rw [if_pos hx]
        obtain ⟨hx1, hx2⟩ := (Finset.mem_filter.mp hx).2
        simp only [hF', hx1, hx2, if_false, if_true]
        exact card_ballBox_le hL _ _
      · rw [if_neg hx]
        have : ¬ (G.molecule.atom x ∉ intAtoms u v ∧ G.molecule.InGroup (Molecule.ladderAtoms u v) x) := fun h =>
          hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        simp only [hF']
        by_cases hi : G.molecule.atom x ∈ intAtoms u v
        · simp [hi]
        · have hng : ¬ G.molecule.InGroup (Molecule.ladderAtoms u v) x := fun hg => this ⟨hi, hg⟩
          simp [hi, hng]
    calc ∏ x : GardenDart G, ((F' x).card : ℝ) ≤ ∏ x : GardenDart G, (if x ∈ Dnt then K else 1) :=
          Finset.prod_le_prod₀ (s := Finset.univ) (f := fun x => ((F' x).card : ℝ)) (g := fun x => if x ∈ Dnt then K else 1) (fun _ _ => Nat.cast_nonneg _) (fun x _ => h1 x)
      _ = K ^ Dnt.card := by
          rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
          congr 2
          ext x; simp
      _ ≤ K ^ 16 := pow_le_pow_right₀ hK1 hDntcard
  exact_mod_cast (Nat.cast_le.mpr hcard).trans hprod

end LadderDarts.Ctx
end WaveTurbulence.LadderDecay
