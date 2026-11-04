/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCChainTerm
public import WaveTurbulence.Foundations.ClassJR.MCSum

/-!
# A chain with a bottom coefficient, for fixed masks

DH21 Proposition 5.1, Case 2, for fixed masks of the pair coefficients (L1121–L1150). Let `c` be a
chain of pairs `j < m` with variables `σ j`, signs `ε j`, and coefficients `R_j` with
`MCRep` on `S_j`, and let `G` be a bottom coefficient with `MCRep` on `S_b`. Then
`(t, s) ↦ chainT c R α t (G α · s)` is `Σ_{Y ⊆ adj} Σ_{Y' ⊆ Y} ∏_{j ∈ Y'} Φ(ζ_{σ j} α_{σ j})
(T_{Y,Y',J} + T_{Y,Y',R})`, each `T` an `MCRep` on `⋃_j S_j ∪ S_b ∪ σ(\[0,m) ∖ Y')`
(`MCRep.chainOne`).

This file first does the bookkeeping of the variables (`range_fT_chainP`, `injective_fT_chainP`,
`fTerm_spec`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Vars

variable {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ} {P : ℕ → PSym V}
  {S : ℕ → Set V} {c : LegalCode}

/-- The variables of the pair symbols with the differences. -/
theorem range_fT_chainP (hS : ∀ j ∈ Set.Ico 0 c.size, Set.range (P j).f = S j)
    {D : Finset ℕ} (hD : D ⊆ Finset.Ico 0 (0 + c.size)) :
    Set.range (fT (chainP P σ ε D) c 0) = (⋃ j ∈ Set.Ico 0 c.size, S j) ∪ σ '' ↑D := by
  rw [range_fT]
  ext v
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_image, Finset.mem_coe, exists_prop,
    range_chainP_f]
  constructor
  · rintro ⟨j, hj, hv⟩
    have hj' : j ∈ Set.Ico 0 c.size := by simpa using hj
    rcases hv with hv | hv
    · exact Or.inl ⟨j, hj', hS j hj' ▸ hv⟩
    · by_cases hjD : j ∈ D
      · simp only [hjD, ↓reduceIte, Set.mem_singleton_iff] at hv
        exact Or.inr ⟨j, hjD, hv.symm⟩
      · simp [hjD] at hv
  · rintro (⟨j, hj, hv⟩ | ⟨j, hjD, rfl⟩)
    · exact ⟨j, by simpa using hj, Or.inl ((hS j hj).symm ▸ hv)⟩
    · have hj := hD hjD
      refine ⟨j, by simpa [Finset.mem_Ico] using hj, Or.inr ?_⟩
      simp [hjD]

/-- The pair symbols with the differences have distinct variables. -/
theorem injective_fT_chainP (hf : ∀ j ∈ Set.Ico 0 c.size, Function.Injective (P j).f)
    (hS : ∀ j ∈ Set.Ico 0 c.size, Set.range (P j).f = S j)
    (hSS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, j ≠ k → Disjoint (S j) (S k))
    (hσS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, σ k ∉ S j)
    (hinj : Set.InjOn σ (Set.Ico 0 c.size)) (D : Finset ℕ) :
    Function.Injective (fT (chainP P σ ε D) c 0) := by
  have hr : ∀ j, j ∈ Set.Ico 0 (0 + c.size) → j ∈ Set.Ico 0 c.size := fun j hj => by
    simpa using hj
  refine injective_fT _ c 0 (fun j hj => injective_chainP_f (hf j (hr j hj))
    (by rw [hS j (hr j hj)]; exact hσS j (hr j hj) j (hr j hj))) fun j hj k hk hjk => ?_
  have hj' := hr j hj
  have hk' := hr k hk
  rw [range_chainP_f, range_chainP_f, hS j hj', hS k hk']
  refine Set.disjoint_union_left.2 ⟨Set.disjoint_union_right.2 ⟨hSS j hj' k hk' hjk, ?_⟩,
    Set.disjoint_union_right.2 ⟨?_, ?_⟩⟩
  · split_ifs
    · exact Set.disjoint_singleton_right.2 (hσS j hj' k hk')
    · exact Set.disjoint_empty _
  · split_ifs
    · exact Set.disjoint_singleton_left.2 (hσS k hk' j hj')
    · exact Set.empty_disjoint _
  · split_ifs
    · exact Set.disjoint_singleton.2 fun h => hjk (hinj hj' hk' h)
    · exact Set.disjoint_empty _
    · exact Set.empty_disjoint _
    · exact Set.empty_disjoint _

/-- **The variables of a chain term.** -/
theorem fTerm_spec (hf : ∀ j ∈ Set.Ico 0 c.size, Function.Injective (P j).f)
    (hS : ∀ j ∈ Set.Ico 0 c.size, Set.range (P j).f = S j)
    (hSS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, j ≠ k → Disjoint (S j) (S k))
    {Sb : Set V} (hSb : ∀ j ∈ Set.Ico 0 c.size, Disjoint (S j) Sb)
    (hσS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, σ k ∉ S j)
    (hσb : ∀ k ∈ Set.Ico 0 c.size, σ k ∉ Sb) (hinj : Set.InjOn σ (Set.Ico 0 c.size))
    {Y Y' : Finset ℕ} (hY' : Y' ⊆ Y) (hY : Y ⊆ Finset.Ico 0 (0 + c.size))
    {ιb ιH : Type} {fb : ιb → V} (hfb : Function.Injective fb) (hrb : Set.range fb = Sb)
    {fH : ιH → V} (hfH : Function.Injective fH)
    (hrH : Set.range fH = σ '' (Set.Ico 0 c.size \ ↑Y)) :
    Function.Injective (fTerm (σ := σ) (ε := ε) P c (Y \ Y') fb fH) ∧
      Set.range (fTerm (σ := σ) (ε := ε) P c (Y \ Y') fb fH) =
        (⋃ j ∈ Set.Ico 0 c.size, S j) ∪ Sb ∪ σ '' (Set.Ico 0 c.size \ ↑Y') := by
  have hD : Y \ Y' ⊆ Finset.Ico 0 (0 + c.size) := Finset.sdiff_subset.trans hY
  have hYI : ∀ j ∈ Y, j ∈ Set.Ico 0 c.size := fun j hj => by
    have := hY hj; simpa [Finset.mem_Ico] using this
  have hr1 := range_fT_chainP (σ := σ) (ε := ε) hS hD
  have hi1 := injective_fT_chainP (ε := ε) hf hS hSS hσS hinj (Y \ Y')
  -- the disjointness of the three groups
  have hd12 : Disjoint (Set.range (fT (chainP P σ ε (Y \ Y')) c 0)) (Set.range fb) := by
    rw [hr1, hrb]
    refine Set.disjoint_union_left.2 ⟨?_, ?_⟩
    · simp only [Set.disjoint_iUnion_left]
      exact fun j hj => hSb j hj
    · rw [Set.disjoint_left]
      rintro v ⟨j, hj, rfl⟩
      exact hσb j (hYI j (Finset.mem_sdiff.1 hj).1)
  have hd3 : Disjoint (Set.range (Sum.elim (fT (chainP P σ ε (Y \ Y')) c 0) fb))
      (Set.range fH) := by
    rw [Set.Sum.elim_range, hr1, hrb, hrH]
    refine Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩
    · simp only [Set.disjoint_iUnion_left]
      intro j hj
      rw [Set.disjoint_right]
      rintro v ⟨k, hk, rfl⟩
      exact hσS j hj k hk.1
    · rw [Set.disjoint_left]
      rintro v ⟨j, hj, rfl⟩ ⟨k, hk, hkj⟩
      have hjY := (Finset.mem_sdiff.1 hj).1
      exact hk.2 (hinj hk.1 (hYI j hjY) hkj ▸ (Finset.mem_coe.2 hjY))
    · rw [Set.disjoint_right]
      rintro v ⟨k, hk, rfl⟩
      exact hσb k hk.1
  refine ⟨?_, ?_⟩
  · refine (hi1.sumElim hfb fun x y h => ?_).sumElim hfH fun x y h => ?_
    · exact Set.disjoint_left.1 hd12 ⟨x, rfl⟩ ⟨y, h.symm⟩
    · exact Set.disjoint_left.1 hd3 ⟨x, rfl⟩ ⟨y, h.symm⟩
  · change Set.range (Sum.elim (Sum.elim (fT (chainP P σ ε (Y \ Y')) c 0) fb) fH) = _
    rw [Set.Sum.elim_range, Set.Sum.elim_range, hr1, hrb, hrH]
    ext v
    simp only [Set.mem_union, Set.mem_image, Finset.mem_coe, Finset.mem_sdiff, Set.mem_sdiff]
    constructor
    · rintro (((h | ⟨j, ⟨hjY, hjY'⟩, rfl⟩) | h) | ⟨j, ⟨hj, hjY⟩, rfl⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨j, ⟨hYI j hjY, hjY'⟩, rfl⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨j, ⟨hj, fun h => hjY (hY' h)⟩, rfl⟩
    · rintro ((h | h) | ⟨j, ⟨hj, hjY'⟩, rfl⟩)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inr h)
      · by_cases hjY : j ∈ Y
        · exact Or.inl (Or.inl (Or.inr ⟨j, ⟨hjY, hjY'⟩, rfl⟩))
        · exact Or.inr ⟨j, ⟨hj, hjY⟩, rfl⟩

end Vars

section Piece

variable {V : Type} [DecidableEq V] {σ : ℕ → V} {ε : ℕ → ℤ} {P : ℕ → PSym V}
  {S : ℕ → Set V} {c : LegalCode}

/-- The constant of the Lemma G pieces. -/
@[expose] noncomputable def KH (θ a b : ℝ) : ℝ := max (12 * CE * Ir 2) (KRs θ a b)

theorem KH_nonneg (θ a b : ℝ) : 0 ≤ KH θ a b := by
  have := CE_nonneg; have := Ir2_nonneg
  exact le_max_of_le_left (by positivity)

/-- **The constant of a term of a chain** with bottom coefficient. -/
@[expose] noncomputable def Nchain (θ a b : ℝ) (c : LegalCode) (N : ℕ → ℝ) (Nb : ℝ) : ℝ :=
  4 * (4 * NT (fun j => (1 + KPD a b) * N j) c 0 * Nb) * (KH θ a b * C510 θ ^ c.size)

/-- **A term of a chain with bottom coefficient, from a Lemma G piece** (DH21 L1137–L1150). -/
theorem chainOne_piece {θ a b A : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (ha : 0 < a) (hb : 0 ≤ b)
    (hab : a + b ≤ θ) (hA : A1 ≤ A) (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hinj : Set.InjOn σ (Set.Ico 0 c.size)) {N : ℕ → ℝ}
    (hP : ∀ j ∈ Set.Ico 0 c.size, Function.Injective (P j).f ∧ Set.range (P j).f = S j ∧
      SRep θ a b A (N j) (P j).C)
    (hSS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, j ≠ k → Disjoint (S j) (S k))
    {Sb : Set V} (hSb : ∀ j ∈ Set.Ico 0 c.size, Disjoint (S j) Sb)
    (hσS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, σ k ∉ S j)
    (hσb : ∀ k ∈ Set.Ico 0 c.size, σ k ∉ Sb)
    {ιb : Type} [Fintype ιb] {fb : ιb → V} {Cb : (ιb → ℝ) → ℝ × ℝ → ℂ} {Nb : ℝ}
    (hfb : Function.Injective fb) (hrb : Set.range fb = Sb) (hCb : SRep θ a b A Nb Cb)
    {Y Y' : Finset ℕ} (hY : Y ⊆ adjSet c 0) (hY' : Y' ⊆ Y)
    {Gp : ZT c → ℝ → (V → ℝ) → ℝ → ℂ} {NH : ℝ} (hNH : NH ≤ KH θ a b * C510 θ ^ c.size)
    (hL : LGPiece θ a b A NH (σ '' (Set.Ico 0 (0 + c.size) \ (↑Y ∩ ↑(adjSet c 0)))) Gp) :
    MCRep θ a b A (Nchain θ a b c N Nb)
        ((⋃ j ∈ Set.Ico 0 c.size, S j) ∪ Sb ∪ σ '' (Set.Ico 0 c.size \ ↑Y'))
        (fun α t s => ∫ w, gTerm σ ε P fb Cb c Gp Y Y' α t s w) ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → Integrable (gTerm σ ε P fb Cb c Gp Y Y' α t s) := by
  classical
  have hA0 : 0 ≤ A := A1_nonneg.trans hA
  have haθ : a ≤ θ := by linarith
  have hAchi : Achi ≤ A := Achi_le_A1.trans hA
  have hYI : Y ⊆ Finset.Ico 0 (0 + c.size) := fun j hj => by
    have := mem_adjSet c 0 j (hY hj)
    simp only [Finset.mem_Ico]; omega
  have hD : Y \ Y' ⊆ Finset.Ico 0 (0 + c.size) := Finset.sdiff_subset.trans hYI
  have hT := tbound_MzS (chainP P σ ε (Y \ Y')) hA0 (NP := fun j => (1 + KPD a b) * N j) c 0
    fun j hj => PBound.chainP (hP j (by simpa using hj)).2.2 ha hb hab hθ1 hAchi (hε j)
  obtain ⟨ιH, hιH, fH, Ξ, hΞ, hΞs, bfr, H, hfH, hrH, hbfr, hHF, hHm, hGp⟩ := hL
  have hvar : σ '' (Set.Ico 0 (0 + c.size) \ (↑Y ∩ ↑(adjSet c 0))) =
      σ '' (Set.Ico 0 c.size \ ↑Y) := by
    rw [zero_add, Set.inter_eq_left.2 (Finset.coe_subset.2 hY)]
  rw [hvar] at hrH
  have hjH : ∀ i, ∃ j, j ∈ Set.Ico 0 c.size ∧ fH i = σ j := fun i => by
    have : fH i ∈ Set.range fH := ⟨i, rfl⟩
    rw [hrH] at this
    obtain ⟨j, hj, hji⟩ := this
    exact ⟨j, hj.1, hji.symm⟩
  choose jH hjH using hjH
  have hK := KH_nonneg θ a b
  have hC5 : 0 ≤ C510 θ ^ c.size := by
    unfold C510; positivity
  obtain ⟨hS, hid⟩ := chainTerm hθ0 ha.le haθ hb hA0 hε hinj hD hT hCb hbfr
    (NH := KH θ a b * C510 θ ^ c.size) (mul_nonneg hK hC5)
    (fun p L0 => (hHF p L0).mono hNH hA0) hHm hjH hGp
  obtain ⟨hfi, hfr⟩ := fTerm_spec (ε := ε) (fun j hj => (hP j hj).1) (fun j hj => (hP j hj).2.1)
    hSS hSb hσS hσb hinj hY' hYI hfb hrb hfH hrH
  refine ⟨⟨_, inferInstance, fTerm (σ := σ) (ε := ε) P c (Y \ Y') fb fH, _, hfi, hfr, hS.nonneg,
    hS.reg, hS.norm, hS.wnorm, fun α t s ht _ => (hid α t ht s).2⟩,
    fun α t s ht => (hid α t ht s).1⟩

/-- A term with a vanishing piece vanishes. -/
theorem gTerm_eq_zero {P : ℕ → PSym V} {ιb : Type} {fb : ιb → V} {Cb : (ιb → ℝ) → ℝ × ℝ → ℂ}
    {Gp : ZT c → ℝ → (V → ℝ) → ℝ → ℂ}
    (hz : ∀ p L0 α, ∀ t ∈ Icc (0 : ℝ) 1, Gp p L0 α t = 0) (Y Y' : Finset ℕ) (α : V → ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (s : ℝ) :
    gTerm σ ε P fb Cb c Gp Y Y' α t s = fun _ => 0 := by
  funext w
  simp only [gTerm, hz _ _ _ t ht, mul_zero]

end Piece

section Main

variable {V : Type} [DecidableEq V]

/-- **A chain with a bottom coefficient, for fixed masks** (DH21 Proposition 5.1, Case 2,
L1121–L1150). The `PhiZ` factors come from the adjacent pairs `Y' ⊆ Y ⊆ adj` (Lemma 5.10 with
`Φ(ε_jα̃_j) = Φ(ε_jα_j) + D_j`); every term is a coefficient representation in the remaining
variables, with a constant `Nchain` of the form `K^m ∏ N_j N_b` (DH23 weights). -/
theorem MCRep.chainOne {θ a b A : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b)
    (hab1 : a + b < 1) (hab : a + b ≤ θ) (hA : A1 ≤ A)
    {σ : ℕ → V} {ε : ℕ → ℤ} (hε : ∀ j, ε j = 1 ∨ ε j = -1) {ζ : V → ℤ} {c : LegalCode}
    (hζ : ∀ j ∈ Set.Ico 0 c.size, ζ (σ j) = ε j) (hc : c ≠ .nil)
    (hinj : Set.InjOn σ (Set.Ico 0 c.size))
    {S : ℕ → Set V} {N : ℕ → ℝ} {R : ℕ → (V → ℝ) → ℝ → ℝ → ℂ}
    (hR : ∀ j ∈ Set.Ico 0 c.size, MCRep θ a b A (N j) (S j) (R j))
    {Sb : Set V} {Nb : ℝ} {G : (V → ℝ) → ℝ → ℝ → ℂ} (hG : MCRep θ a b A Nb Sb G)
    (hSS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, j ≠ k → Disjoint (S j) (S k))
    (hSb : ∀ j ∈ Set.Ico 0 c.size, Disjoint (S j) Sb)
    (hσS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, σ k ∉ S j)
    (hσb : ∀ k ∈ Set.Ico 0 c.size, σ k ∉ Sb) :
    ∃ T : Finset ℕ → Finset ℕ → Bool → (V → ℝ) → ℝ → ℝ → ℂ,
      (∀ Y ⊆ adjSet c 0, ∀ Y' ⊆ Y, ∀ pc, MCRep θ a b A (Nchain θ a b c N Nb)
        ((⋃ j ∈ Set.Ico 0 c.size, S j) ∪ Sb ∪ σ '' (Set.Ico 0 c.size \ ↑Y')) (T Y Y' pc)) ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
        chainT σ ε c 0 R α t (fun t' => G α t' s) =
          ∑ Y ∈ (adjSet c 0).powerset, ∑ Y' ∈ Y.powerset,
            (∏ j ∈ Y', PhiZ ζ (σ j) (α (σ j))) * (T Y Y' true α t s + T Y Y' false α t s) := by
  classical
  have hinj0 : Set.InjOn σ (Set.Ico 0 (0 + c.size)) := by rwa [zero_add]
  -- the pair symbols
  have hPex : ∀ j, ∃ Pj : PSym V, SymReg Pj.C ∧ (j ∈ Set.Ico 0 c.size →
      (Function.Injective Pj.f ∧ Set.range Pj.f = S j ∧ SRep θ a b A (N j) Pj.C) ∧
        ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
          R j α t s = ∫ lam, Pj.C (α ∘ Pj.f) lam * e2 lam t s) := by
    intro j
    by_cases hj : j ∈ Set.Ico 0 c.size
    · obtain ⟨ι, hι, f, C, hf, hr, hS, he⟩ := (hR j hj).exists_srep
      exact ⟨⟨ι, f, C⟩, hS.reg, fun _ => ⟨⟨hf, hr, hS⟩, he⟩⟩
    · exact ⟨⟨Empty, fun e => Empty.elim e, fun _ _ => 0⟩, symReg_zero, fun h => absurd h hj⟩
  choose P hPreg hP using hPex
  -- the bottom symbol
  obtain ⟨ιb, hιb, fb, Cb, hfb, hrb, hCb, heb⟩ := hG.exists_srep
  -- Lemma 5.10 and Lemma G
  have hJR : ∀ Y : Finset ℕ, ∃ (GJ GR : ZT c → ℝ → (V → ℝ) → ℝ → ℂ) (NJ NR : ℝ),
      0 ≤ NJ ∧ 0 ≤ NR ∧ NJ + NR ≤ C510 θ ^ c.size ∧
      LGPiece θ a b A (12 * CE * Ir 2 * NJ)
        (σ '' (Set.Ico 0 (0 + c.size) \ (↑Y ∩ ↑(adjSet c 0)))) GJ ∧
      (LGPiece θ a b A (KRs θ a b * NR)
          (σ '' (Set.Ico 0 (0 + c.size) \ (↑Y ∩ ↑(adjSet c 0)))) GR ∨
        ∀ (p : ZT c) (L0 : ℝ) (α : V → ℝ), ∀ t ∈ Icc (0 : ℝ) 1, GR p L0 α t = 0) ∧
      ∀ (p : ZT c) (L0 : ℝ) (α : V → ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
        volterra (tildeP σ ε (μZ c) Y c 0 p α) (fun s => cexp (π * I * (L0 * s))) t =
          GJ p L0 α t + GR p L0 α t := by
    intro Y
    have hM := (lemma510 hθ0 hθ1 (A0_le_A1.trans hA) hε (measurable_μZ c) hc hinj0).2.2 Y
    exact hM.lgpieces hθ0 hθ1 ha.le hb hab1 hab hA
  choose GJ GR NJ NR hNJ hNR hNJR hLJ hLR hGJR using hJR
  have hK := KH_nonneg θ a b
  have hJb : ∀ Y, 12 * CE * Ir 2 * NJ Y ≤ KH θ a b * C510 θ ^ c.size := fun Y =>
    mul_le_mul (le_max_left _ _) (by linarith [hNR Y, hNJR Y]) (hNJ Y) hK
  have hRb : ∀ Y, KRs θ a b * NR Y ≤ KH θ a b * C510 θ ^ c.size := fun Y =>
    mul_le_mul (le_max_right _ _) (by linarith [hNJ Y, hNJR Y]) (hNR Y) hK
  -- the pieces
  have hpJ := fun Y (hY : Y ⊆ adjSet c 0) Y' (hY' : Y' ⊆ Y) =>
    chainOne_piece (ε := ε) (N := N) hθ0 hθ1.le ha hb hab hA hε hinj (fun j hj => (hP j hj).1)
      hSS hSb hσS hσb hfb hrb hCb hY hY' (hJb Y) (hLJ Y)
  have hpR : ∀ Y, Y ⊆ adjSet c 0 → ∀ Y', Y' ⊆ Y →
      MCRep θ a b A (Nchain θ a b c N Nb)
        ((⋃ j ∈ Set.Ico 0 c.size, S j) ∪ Sb ∪ σ '' (Set.Ico 0 c.size \ ↑Y'))
        (fun α t s => ∫ w, gTerm σ ε P fb Cb c (GR Y) Y Y' α t s w) ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → Integrable (gTerm σ ε P fb Cb c (GR Y) Y Y' α t s) := by
    intro Y hY Y' hY'
    rcases hLR Y with hL | hz
    · exact chainOne_piece (ε := ε) (N := N) hθ0 hθ1.le ha hb hab hA hε hinj
        (fun j hj => (hP j hj).1) hSS hSb hσS hσb hfb hrb hCb hY hY' (hRb Y) hL
    · obtain ⟨ι, hι, f, C, hf, hr, hN0, -⟩ := (hpJ Y hY Y' hY').1
      refine ⟨(MCRep.zero_of_range hf hr hN0).congr fun α t s ht _ => ?_, fun α t s ht => ?_⟩
      · simp only [gTerm_eq_zero (hz) Y Y' α ht s, integral_zero]
      · rw [gTerm_eq_zero hz Y Y' α ht s]
        exact integrable_zero _ _ _
  refine ⟨fun Y Y' pc α t s =>
      ∫ w, gTerm σ ε P fb Cb c (if pc then GJ Y else GR Y) Y Y' α t s w, ?_, ?_⟩
  · intro Y hY Y' hY' pc
    cases pc
    · simpa using (hpR Y hY Y' hY').1
    · simpa using (hpJ Y hY Y' hY').1
  · intro α t s ht hs
    rw [chainT_bottom_expand hε hζ hc hinj hPreg (fun j hj => (hP j hj).2) hCb.reg heb
      (GJ := GJ) (GR := GR) (fun Y _ => hGJR Y) α ht hs fun Y hY Y' hY' =>
        ⟨(hpJ Y (Finset.mem_powerset.1 hY) Y' (Finset.mem_powerset.1 hY')).2 α t s ht,
          (hpR Y (Finset.mem_powerset.1 hY) Y' (Finset.mem_powerset.1 hY')).2 α t s ht⟩]
    simp

end Main

end WaveTurbulence.ClassJR
