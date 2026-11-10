/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Gate
public import WaveTurbulence.Foundations.Stage1.Represents.RepS10e
public import WaveTurbulence.Foundations.Spine.Stage1GateMonotone

/-! # B4 STAGE1MK-GATE: the parameter prefix

* Large-constant monotonicity (`C₁`, `C₂` enlarged) of the representation statements and of the two inputs
  `MarkedClassRepresentsMK` (B3 + B3s) and `ZeroVanish` (FL-SEP zero classes).
* **`stage1ReductionAtMKFull_of`**: `∃ C₀ ≥ 2, WTPrefix (Stage1ReductionAtMKFull C₀ cP cθ)` from
  `WTPrefix (MarkedClassRepresentsMK cP cθ)` (B3s, R179), B2e's `B2eIX` and `WTPrefix ZeroVanish`.
* **`stage1ReductionAtMK_of`**: the frozen form `WTPrefix (Stage1ReductionAtMK C₀ (cP + 343))` from the same inputs. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents

namespace WaveTurbulence.Flower.Stage1MKGate

/-- The common mass factor is monotone in `C₁`. -/
theorem massFactor_mono {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (n : ℕ) (c₁ : ℝ) (hc : P.C₁ ≤ c₁)
    (h0 : 0 ≤ P.C₁) (X : ℝ) (hX : 0 ≤ X) :
    (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) * X ≤
      (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * c₁ ^ (π.Gsb.order + 2 * R) * X := by
  have hsq : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hpow : (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) ≤ (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) :=
    pow_le_pow_left₀ (mul_nonneg h0 hsq) (mul_le_mul_of_nonneg_right hc hsq) _
  have hpow2 : P.C₁ ^ (π.Gsb.order + 2 * R) ≤ c₁ ^ (π.Gsb.order + 2 * R) := pow_le_pow_left₀ h0 hc _
  have hB : 0 ≤ (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) := pow_nonneg (mul_nonneg (h0.trans hc) hsq) _
  have hC : 0 ≤ P.C₁ ^ (π.Gsb.order + 2 * R) := pow_nonneg h0 _
  exact mul_le_mul_of_nonneg_right (mul_le_mul hpow hpow2 hC hB) hX

theorem representsIntMKSel_largeConstants {P : WTParams} {R : ℕ} (c₁ c₂ : ℝ) (hc : P.C₁ ≤ c₁) (h0 : 0 ≤ P.C₁)
    (hL : 0 ≤ P.L) (π : Stage1PieceMK P.d R) (sel : Finset (GBranch π.Gsb.tree)) (n : ℕ) (cP : ℝ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : 0 ≤ s) (val : ℂ)
    (h : RepresentsIntMKSel π sel n cP tt base roots s val) :
    RepresentsIntMKSel (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π sel n cP tt base roots s val := by
  obtain ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwb, hD⟩ := h
  refine ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwb.trans ?_, hD⟩
  have hX : 0 ≤ P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
      P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s := by
    have h1 := Real.rpow_nonneg hL (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
      P.η ^ 7 * (π.Cs.hinges.card : ℝ))
    have h2 := Real.rpow_nonneg hL (cP * P.d * (π.nProt : ℝ))
    have h3 := Real.rpow_nonneg hL (7 * (47 * P.d + 2) * (sel.card : ℝ))
    positivity
  have := massFactor_mono π n c₁ hc h0 _ hX
  simp only [mul_assoc] at this ⊢
  exact this

theorem representsIntMK_largeConstants {P : WTParams} {R : ℕ} (c₁ c₂ : ℝ) (hc : P.C₁ ≤ c₁) (h0 : 0 ≤ P.C₁)
    (hL : 0 ≤ P.L) (π : Stage1PieceMK P.d R) (n : ℕ) (cP : ℝ) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : 0 ≤ s) (val : ℂ)
    (h : π.RepresentsIntMK n cP tt base roots s val) :
    Stage1PieceMK.RepresentsIntMK (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π n cP tt base roots s val := by
  rw [← representsIntMKSel_empty] at h ⊢
  exact representsIntMKSel_largeConstants c₁ c₂ hc h0 hL π ∅ n cP tt base roots s hs val h

/-- The gate carrier is unchanged by the large constants. -/
theorem carrier_largeConstants {P : WTParams} (c₁ c₂ : ℝ) {p N R : ℕ} {J : Finset (Fin (2 * R))}
    {pat : Fin (2 * R) → FixPat} {LG : LayeredGarden (2 * R)}
    (h : MkCarries ({P with C₁ := c₁, C₂ := c₂} : WTParams) p N LG ∧
      (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) :
    MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h
  refine ⟨⟨h1, ?_, h3, h4⟩, h5⟩
  simpa only [N_largeConstants] using h2

/-- `PieceRestB3s` does not read the large constants (field-by-field: the structure's parameter record changes). -/
theorem pieceRestB3s_largeConstants {P : WTParams} {R : ℕ} (c₁ c₂ : ℝ) (π : Stage1PieceMK P.d R) (cθ : ℝ)
    (h : PieceRestB3s π cθ) : PieceRestB3s (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π cθ :=
  ⟨h.prot_card, h.fix_prot, h.fix_layer, h.filt_ok, h.ind_ok, h.ind_local, h.lb_free, h.lb_prot, h.lb_layer⟩

/-- **The B3 + B3s hypothesis is large-constant monotone.** -/
theorem markedClassRepresentsMK_mono (cP cθ : ℝ) : LargeConstantMonotone (MarkedClassRepresentsMK cP cθ) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp R hR hRmax N hN1 hNb J hJ pat kSel t ht s hs A hA hpl hTC roots hh b Rf σ Rs dag hb hhb hRf hRs hhigh
    mkF hF π hnz
  rw [R_largeConstants] at hRmax
  rw [N_largeConstants] at hNb
  obtain ⟨prot, fix, filt, ind, lb, selR, hok⟩ := h p hp R hR hRmax N hN1 hNb J hJ pat kSel t ht s hs A
    (fun LG hLG => carrier_largeConstants c₁ c₂ (hA LG hLG)) hpl hTC roots hh b Rf σ Rs dag hb hhb hRf hRs hhigh
    mkF hF π hnz
  have hL0 : 0 ≤ P.L := by linarith
  have hRs0 : ∀ j, 0 ≤ Rs j := fun j => hL0.trans (hRs j)
  refine ⟨prot, fix, filt, ind, lb, selR, ?_⟩
  have h1 := representsIntMKSel_largeConstants (P := P) c₁ c₂ h₁ (by linarith) hL0
    (classPiece P mkF (repPt π) prot (protI (repPt π).layered J pat t s kSel).card fix filt ind lb) selR N cP
    (fun _ => t) 0 roots _ (selMassMK_nonneg N (zero_le_one.trans hb) hRs0 kSel _) _ hok.rep
  have h2 := pieceRestB3s_largeConstants (P := P) c₁ c₂
    (classPiece P mkF (repPt π) prot (protI (repPt π).layered J pat t s kSel).card fix filt ind lb) cθ hok.rest
  have h3 := representsIntMK_largeConstants (P := P) c₁ c₂ h₁ (by linarith) hL0
    (classPiece P mkF (repPt π) prot (protI (repPt π).layered J pat t s kSel).card fix filt ind lb) N (cP + 343)
    (fun _ => t) 0 roots _ (pow_nonneg (zero_le_one.trans hb) N) _ hok.repMK
  exact ⟨h1, h2, hok.sel_spec, hok.sel_inj, hok.sel_card, h3, hok.sel_lb⟩

/-- **The zero-class statement is large-constant monotone.** -/
theorem zeroVanish_mono : LargeConstantMonotone ZeroVanish := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp R hR hRmax N hN1 hNb J pat kSel t ht s hs A hA roots hh b Rf σ Rs dag hRf hhigh π hS hun
  rw [R_largeConstants] at hRmax
  rw [N_largeConstants] at hNb
  exact h p hp R hR hRmax N hN1 hNb J pat kSel t ht s hs A (fun LG hLG => carrier_largeConstants c₁ c₂ (hA LG hLG))
    roots hh b Rf σ Rs dag hRf hhigh π hS hun

/-- The prefix gives `1 ≤ C₁`. -/
theorem prefix_C1 : WTPrefix (fun P => 1 ≤ P.C₁) := by
  intro d hd γ hγ
  exact ⟨1, one_pos, fun η hη φin hφin τ hτ φ hφ => ⟨1, le_rfl, 1, one_pos, fun ν hν => ⟨1, one_pos,
    fun δ hδ D hD hτD => ⟨1, le_rfl, 2, le_rfl, fun L hL => le_rfl⟩⟩⟩⟩

theorem prefix_C1_mono : LargeConstantMonotone (fun P => 1 ≤ P.C₁) :=
  fun _ _ _ _ _ _ _ h₁ _ h => h.trans h₁

/-- **The marked Stage-1′ gate, Full form (ruling R177)**, from the B3 + B3s hypothesis, B2e's fine transport and
the zero-class statement. -/
theorem stage1ReductionAtMKFull_of (cP cθ : ℝ) (hB : WTPrefix (MarkedClassRepresentsMK cP cθ)) (hIX : B2eIX)
    (hZ : WTPrefix ZeroVanish) : ∃ C₀ : ℕ, 2 ≤ C₀ ∧ WTPrefix (Stage1ReductionAtMKFull C₀ cP cθ) := by
  obtain ⟨C₀, K, hC₀, hcnt⟩ := exists_pieceCountAt
  refine ⟨C₀, hC₀, ?_⟩
  have hm := (markedClassRepresentsMK_mono cP cθ).and zeroVanish_mono
  have hQ := prefix_and (prefix_and hB hZ (markedClassRepresentsMK_mono cP cθ) zeroVanish_mono) prefix_C1 hm
    prefix_C1_mono
  have hQ2 := prefix_with_C2_ge hQ (hm.and prefix_C1_mono) (K : ℝ)
  exact prefix_map (fun P hP => fullAt hcnt hP.2.1 (zero_le_one.trans hP.1.2) (by linarith [hP.2.2]) hP.1.1.1 hIX
    hP.1.1.2) hQ2

end WaveTurbulence.Flower.Stage1MKGate
