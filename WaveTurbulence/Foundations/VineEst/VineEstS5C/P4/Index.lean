/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Expand

/-! # P4: the index type `Ch` of the bundle summands and their sum (V5 Step 4d part C)

`PIdx S bs = Σ b ∈ bs, Fin (mQ b) × Fin (mT b)`; `RIdx S bs = Σ b ∈ bs, (Fin (mQ b) ⊕ Fin (mT b) ⊕ Unit)`.
`Ch S bs₁ bs₂ rA rB` is the sum of three copies of `PIdx bs₁` (clause (a) II-a, (b), (c) couple), three copies of `PIdx bs₂` (clause (a) II-b,
(b), (c) tree), `RIdx rA` and `RIdx rB`.  `ptTerm`: the summand at a point.  `card_ch`: `|Ch| = ∑_{bs₁} 3 mQ mT + ∑_{bs₂} 3 mQ mT + ∑_{rA} (mQ+mT+1) + ∑_{rB} (mQ+mT+1)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P4
open WaveTurbulence WaveTurbulence.VineEstS4c Finset
open scoped ComplexConjugate

variable {β : Type*} {d : ℕ} [DecidableEq β] (S : SepTerms β d)

/-- The `(b, i, j)` index of a piece. -/
abbrev PIdx (bs : Finset β) : Type _ := Σ b : bs, Fin (S.mQ b.1) × Fin (S.mT b.1)

/-- The index of the remainder terms. -/
abbrev RIdx (bs : Finset β) : Type _ := Σ b : bs, (Fin (S.mQ b.1) ⊕ Fin (S.mT b.1) ⊕ Unit)

/-- The index of all summands of a bundle. -/
abbrev PCh (bs₁ bs₂ : Finset β) : Type _ :=
  PIdx S bs₁ ⊕ PIdx S bs₁ ⊕ PIdx S bs₁ ⊕ PIdx S bs₂ ⊕ PIdx S bs₂ ⊕ PIdx S bs₂

/-- The index of the remainder summands. -/
abbrev RCh (rA rB : Finset β) : Type _ := RIdx S rA ⊕ RIdx S rB

/-- The index of all summands of a bundle. -/
abbrev Ch (bs₁ bs₂ rA rB : Finset β) : Type _ := PCh S bs₁ bs₂ ⊕ RCh S rA rB

theorem sum_sigma_coe {bs : Finset β} {F : β → Type} [∀ b, Fintype (F b)] (f : ∀ b, F b → ℂ) :
    ∑ c : (Σ b : bs, F b.1), f c.1.1 c.2 = ∑ b ∈ bs, ∑ y : F b, f b y := by
  rw [Fintype.sum_sigma]
  exact Finset.sum_coe_sort bs (fun b => ∑ y : F b, f b y)

theorem sum_pidx (bs : Finset β) (f : ∀ b, Fin (S.mQ b) → Fin (S.mT b) → ℂ) :
    ∑ c : PIdx S bs, f c.1.1 c.2.1 c.2.2 = ∑ b ∈ bs, ∑ i, ∑ j, f b i j := by
  rw [show (∑ c : PIdx S bs, f c.1.1 c.2.1 c.2.2) = ∑ c : (Σ b : bs, Fin (S.mQ b.1) × Fin (S.mT b.1)), (fun b (z : Fin (S.mQ b) × Fin (S.mT b)) => f b z.1 z.2) c.1.1 c.2 from rfl,
    sum_sigma_coe (F := fun b => Fin (S.mQ b) × Fin (S.mT b)) (fun b z => f b z.1 z.2)]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Fintype.sum_prod_type _

theorem sum_ridx (bs : Finset β) (f : ∀ b, Fin (S.mQ b) → ℂ) (g : ∀ b, Fin (S.mT b) → ℂ) (h : β → ℂ) :
    ∑ c : RIdx S bs, Sum.elim (f c.1.1) (Sum.elim (g c.1.1) (fun _ => h c.1.1)) c.2 =
      ∑ b ∈ bs, ((∑ i, f b i) + (∑ j, g b j) + h b) := by
  rw [show (∑ c : RIdx S bs, Sum.elim (f c.1.1) (Sum.elim (g c.1.1) (fun _ => h c.1.1)) c.2) =
      ∑ c : (Σ b : bs, Fin (S.mQ b.1) ⊕ Fin (S.mT b.1) ⊕ Unit),
        (fun b (z : Fin (S.mQ b) ⊕ Fin (S.mT b) ⊕ Unit) => Sum.elim (f b) (Sum.elim (g b) (fun _ => h b)) z) c.1.1 c.2 from rfl,
    sum_sigma_coe (F := fun b => Fin (S.mQ b) ⊕ Fin (S.mT b) ⊕ Unit)
      (fun b z => Sum.elim (f b) (Sum.elim (g b) (fun _ => h b)) z)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [add_assoc]

theorem card_ch (bs₁ bs₂ rA rB : Finset β) :
    Fintype.card (Ch S bs₁ bs₂ rA rB) =
      3 * (∑ b ∈ bs₁, S.mQ b * S.mT b) + 3 * (∑ b ∈ bs₂, S.mQ b * S.mT b) +
        (∑ b ∈ rA, (S.mQ b + S.mT b + 1)) + ∑ b ∈ rB, (S.mQ b + S.mT b + 1) := by
  have hP : ∀ bs : Finset β, Fintype.card (PIdx S bs) = ∑ b ∈ bs, S.mQ b * S.mT b := fun bs => by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact Finset.sum_coe_sort bs (fun b => S.mQ b * S.mT b)
  have hR : ∀ bs : Finset β, Fintype.card (RIdx S bs) = ∑ b ∈ bs, (S.mQ b + S.mT b + 1) := fun bs => by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    rw [Finset.sum_coe_sort bs (fun b => S.mQ b + (S.mT b + 1))]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp only [Fintype.card_sum, hP, hR]
  ring

section Pt
variable (RQ RT : β → ℝ → ℝ → Mom d → ℂ) (bs₁ bs₂ rA rB : Finset β) (t0 s1 t1 : ℝ) (x y : Mom d)

/-- The piece summands at a point. -/
noncomputable def ptP : PCh S bs₁ bs₂ → ℂ :=
  Sum.elim (fun c : PIdx S bs₁ => tA1 S t0 s1 t1 x y c.1.1 c.2.1 c.2.2)
  (Sum.elim (fun c : PIdx S bs₁ => tKQ S t0 s1 t1 x y c.1.1 c.2.1 c.2.2)
  (Sum.elim (fun c : PIdx S bs₁ => tTQ S t0 s1 t1 x c.1.1 c.2.1 c.2.2)
  (Sum.elim (fun c : PIdx S bs₂ => -tA2 S t0 s1 t1 x y c.1.1 c.2.1 c.2.2)
  (Sum.elim (fun c : PIdx S bs₂ => tKT S t0 s1 t1 x y c.1.1 c.2.1 c.2.2)
  (fun c : PIdx S bs₂ => tTT S t0 s1 t1 x c.1.1 c.2.1 c.2.2)))))

/-- The remainder summands at a point. -/
noncomputable def ptR : RCh S rA rB → ℂ :=
  Sum.elim (fun c : RIdx S rA => Sum.elim (rA1 S t0 s1 t1 x y RT c.1.1)
      (Sum.elim (rA2 S t0 s1 t1 x y RQ c.1.1) (fun _ => rA3 t0 s1 t1 x y RQ RT c.1.1)) c.2)
    (fun c : RIdx S rB => -Sum.elim (rB1 S t0 s1 t1 x y RT c.1.1)
      (Sum.elim (rB2 S t0 s1 t1 x y RQ c.1.1) (fun _ => rB3 t0 s1 t1 x y RQ RT c.1.1)) c.2)

theorem sum_ptP :
    ∑ c, ptP S bs₁ bs₂ t0 s1 t1 x y c =
      ((∑ b ∈ bs₁, ∑ i, ∑ j, tA1 S t0 s1 t1 x y b i j) + (∑ b ∈ bs₁, ∑ i, ∑ j, tKQ S t0 s1 t1 x y b i j) +
        (∑ b ∈ bs₁, ∑ i, ∑ j, tTQ S t0 s1 t1 x b i j)) +
      (-(∑ b ∈ bs₂, ∑ i, ∑ j, tA2 S t0 s1 t1 x y b i j) + (∑ b ∈ bs₂, ∑ i, ∑ j, tKT S t0 s1 t1 x y b i j) +
        (∑ b ∈ bs₂, ∑ i, ∑ j, tTT S t0 s1 t1 x b i j)) := by
  unfold ptP
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [sum_pidx S bs₁ (fun b i j => tA1 S t0 s1 t1 x y b i j), sum_pidx S bs₁ (fun b i j => tKQ S t0 s1 t1 x y b i j),
    sum_pidx S bs₁ (fun b i j => tTQ S t0 s1 t1 x b i j), sum_pidx S bs₂ (fun b i j => -tA2 S t0 s1 t1 x y b i j),
    sum_pidx S bs₂ (fun b i j => tKT S t0 s1 t1 x y b i j), sum_pidx S bs₂ (fun b i j => tTT S t0 s1 t1 x b i j)]
  simp only [Finset.sum_neg_distrib]
  ring

theorem sum_ptR :
    ∑ c, ptR S RQ RT rA rB t0 s1 t1 x y c =
      ((∑ b ∈ rA, ((∑ i, rA1 S t0 s1 t1 x y RT b i) + (∑ j, rA2 S t0 s1 t1 x y RQ b j) + rA3 t0 s1 t1 x y RQ RT b)) -
        ∑ b ∈ rB, ((∑ i, rB1 S t0 s1 t1 x y RT b i) + (∑ j, rB2 S t0 s1 t1 x y RQ b j) + rB3 t0 s1 t1 x y RQ RT b)) := by
  unfold ptR
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [sum_ridx S rA (rA1 S t0 s1 t1 x y RT ·) (rA2 S t0 s1 t1 x y RQ ·) (rA3 t0 s1 t1 x y RQ RT)]
  have hB := sum_ridx S rB (rB1 S t0 s1 t1 x y RT ·) (rB2 S t0 s1 t1 x y RQ ·) (rB3 t0 s1 t1 x y RQ RT)
  simp only [Finset.sum_neg_distrib] at hB ⊢
  rw [hB]
  ring

end Pt

section Main
variable (Q T RQ RT : β → ℝ → ℝ → Mom d → ℂ) (bs₁ bs₂ rA rB : Finset β) (t0 s1 t1 : ℝ) (x y : Mom d)

/-- **The piece summands sum to the pieces (a)-(c)** (case A form of `zpPieces`). -/
theorem sum_ptP_eq
    (hQ : ∀ b, (b ∈ bs₁ ∨ b ∈ bs₂) →
      (∀ k, Q b s1 t0 k = ∑ i, S.sQ b i s1 t0 k) ∧ ∀ k, Q b t1 t0 k = ∑ i, S.sQ b i t1 t0 k)
    (hT : ∀ b, (b ∈ bs₁ ∨ b ∈ bs₂) →
      (∀ k, T b s1 t0 k = ∑ j, S.sT b j s1 t0 k) ∧ ∀ k, T b t1 t0 k = ∑ j, S.sT b j t1 t0 k) :
    ∑ c, ptP S bs₁ bs₂ t0 s1 t1 x y c =
      (pieceA1 bs₁ T (cswap Q) t0 s1 t1 x y - pieceA2 bs₂ Q (cconj T) t0 s1 t1 x y +
        (if t0 < t1 ∧ t0 < s1 then pieceKQ bs₁ Q T t0 s1 t1 x y + pieceTQ bs₁ Q T t0 s1 t1 x +
          pieceKT bs₂ Q T t0 s1 t1 x y + pieceTT bs₂ Q T t0 s1 t1 x else 0)) := by
  classical
  rw [sum_ptP]
  have h1 : ∀ b ∈ bs₁, _ ∧ _ := fun b hb => ⟨hQ b (Or.inl hb), hT b (Or.inl hb)⟩
  have h2 : ∀ b ∈ bs₂, _ ∧ _ := fun b hb => ⟨hQ b (Or.inr hb), hT b (Or.inr hb)⟩
  rw [← pieceA1_expand S t0 s1 t1 x y Q T bs₁ (fun b hb => (h1 b hb).1) (fun b hb => (h1 b hb).2),
    ← pieceA2_expand S t0 s1 t1 x y Q T bs₂ (fun b hb => (h2 b hb).1) (fun b hb => (h2 b hb).2)]
  by_cases hc : t0 < t1 ∧ t0 < s1
  · rw [if_pos hc,
      pieceKQ_expand S t0 s1 t1 x y Q T bs₁ (fun b hb => (h1 b hb).1) (fun b hb => (h1 b hb).2) hc,
      pieceTQ_expand S t0 s1 t1 x Q T bs₁ (fun b hb => (h1 b hb).1) (fun b hb => (h1 b hb).2) hc,
      pieceKT_expand S t0 s1 t1 x y Q T bs₂ (fun b hb => (h2 b hb).1) (fun b hb => (h2 b hb).2) hc,
      pieceTT_expand S t0 s1 t1 x Q T bs₂ (fun b hb => (h2 b hb).1) (fun b hb => (h2 b hb).2) hc]
    ring
  · rw [if_neg hc]
    simp [tKQ, tTQ, tKT, tTT, hc]
    ring

/-- **The remainder summands sum to the remainder rows.** -/
theorem sum_ptR_eq
    (hQ : ∀ b, (b ∈ rA ∨ b ∈ rB) →
      (∀ k, Q b s1 t0 k = ∑ i, S.sQ b i s1 t0 k) ∧ ∀ k, Q b t1 t0 k = ∑ i, S.sQ b i t1 t0 k)
    (hT : ∀ b, (b ∈ rA ∨ b ∈ rB) →
      (∀ k, T b s1 t0 k = ∑ j, S.sT b j s1 t0 k) ∧ ∀ k, T b t1 t0 k = ∑ j, S.sT b j t1 t0 k) :
    ∑ c, ptR S RQ RT rA rB t0 s1 t1 x y c =
      (∑ b ∈ rA, remA Q T RQ RT b t0 s1 t1 x y - ∑ b ∈ rB, remB Q T RQ RT b t0 s1 t1 x y) := by
  classical
  rw [sum_ptR]
  have hA : ∀ b ∈ rA, remA Q T RQ RT b t0 s1 t1 x y =
      (∑ i, rA1 S t0 s1 t1 x y RT b i) + (∑ j, rA2 S t0 s1 t1 x y RQ b j) + rA3 t0 s1 t1 x y RQ RT b := fun b hb =>
    remA_expand S t0 s1 t1 x y RQ RT Q T b (hQ b (Or.inl hb)) (hT b (Or.inl hb))
  have hB : ∀ b ∈ rB, remB Q T RQ RT b t0 s1 t1 x y =
      (∑ i, rB1 S t0 s1 t1 x y RT b i) + (∑ j, rB2 S t0 s1 t1 x y RQ b j) + rB3 t0 s1 t1 x y RQ RT b := fun b hb =>
    remB_expand S t0 s1 t1 x y RQ RT Q T b (hQ b (Or.inr hb)) (hT b (Or.inr hb))
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB]

end Main

end WaveTurbulence.VineEstS5C.P4
