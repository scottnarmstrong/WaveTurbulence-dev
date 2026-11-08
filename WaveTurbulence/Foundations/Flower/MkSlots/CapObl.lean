/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapMain

/-! # B3s MK-SLOTS (cap slots): **`capSlotObligation : CapSlotObligation`**

* `capSlot_triv_obl`: the trivial cap couple (one centred mode);
* `capSlotObligationAt_of`: one parameter record (D3's `ProtBoundNTAt`, `η` small against `γ₁`);
* **`capSlotObligation`**: the prefix, from D3's `ProtPin.protBoundNTGate`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.VineEstS3.FS WaveTurbulence.VineA
  WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign WaveTurbulence.Represents

namespace WaveTurbulence.Flower.MkSlots

section Slot

variable {P : WTParams} (hL : 2 ≤ P.L) (hd : 3 ≤ P.d) (hη : 0 < P.η)
  (C : ℝ) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (t s : ℝ)
  (hGeo : CapGeo (recLG a) J p)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
  (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (q : SourcePair a.prime.skeleton)

include hL hd hη hGeo hb1 in
/-- **A trivial cap slot.** -/
theorem capSlot_triv_obl (hq : IsCapPair a.prime.skeleton a.prime.prime.1 J q)
    (ht : (a.prime.data.couple q).trees.1 = .leaf ∧ (a.prime.data.couple q).trees.2 = .leaf) :
    ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (c : Λ → Fin P.d → ℤ)
      (amp : Λ → Mom P.d → ℂ),
      (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l k, ‖amp l k‖ ≤ 1) ∧ (∀ l, SNorm (30 * P.d) 0 (amp l) ≤ 1) ∧
      (∀ l k, amp l k ≠ 0 → ‖k - RepAnalytic.latPt P.d (c l)‖ ≤ 1) ∧
      (∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
          a.prime.prime.1 (.inl q),
        HasSum (fun l => (wt l : ℂ) * amp l (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) *
            fsPhase (m l) ts)
          (capSlotKer P.L P.γ P.δ p a J t s h roots Rf dag (.inl q) ts
            (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))))) ∧
      ∑' l, maxBracketPow P.η (half (m l)) * ENNReal.ofReal (wt l) ≤
        ENNReal.ofReal (capKc P.d P.η * (C * Real.sqrt P.δ) ^ Represents.slotSize a.prime.data (.inl q) *
          P.L ^ (-(P.η ^ 8) * (Represents.slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a) (.inl q) : ℝ)) *
          (frontierConst P.d ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 (.inl q) *
            (b⁻¹ * Represents.slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
              (fun _ => b.toNNReal) (.inl q))) *
          P.L ^ (31 * (P.d : ℝ) + 6)) := by
  set k₀ := latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)) with hk₀
  have hT := triv_trees a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q ht
  -- the constant value
  set V := kerNoBranch P.L P.γ P.δ (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) q)
    (fun z => anchProfiles J (recLG a) h P.L roots ((nativeCoupleForest a.prime.data a.prime.prime.1 q).nodeEmbedding z).1)
    (fun k' => ∏ z, capNodeW P.L P.γ P.δ p s (recLG a) J Rf dag
      ((nativeCoupleForest a.prime.data a.prime.prime.1 q).nodeEmbedding z) (k' z)) k₀ (fun _ => 0) 0 with hV
  have hval : ∀ ts, capSlotKer P.L P.γ P.δ p a J t s h roots Rf dag (.inl q) ts k₀ = V := fun ts => by
    show kernelNodeWF P.L P.γ P.δ (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) q)
      (fun z => anchProfiles J (recLG a) h P.L roots ((nativeCoupleForest a.prime.data a.prime.prime.1 q).nodeEmbedding z).1)
      (fun k' => ∏ z, capNodeW P.L P.γ P.δ p s (recLG a) J Rf dag
        ((nativeCoupleForest a.prime.data a.prime.prime.1 q).nodeEmbedding z) (k' z))
      (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k₀ (fun _ => 0) 0
      (fixNative a.prime.data a.prime.prime.1 (fixCap (recLG a) J (fun _ => FixPat.plain) t s) (.inl q)) = V
    exact kernelNodeWF_noBranch _ _ _ _ hT _ _ _ _ _ _ _ _
  have hVn : ‖V‖ ≤ 1 := by
    refine norm_kerNoBranch_le _ _ _ _ hT _ _ _ _ _ (fun k' => ?_) (fun ℓ _ x => ?_)
    · rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun z _ => norm_capNodeW_le _ _ _ _ _ _ _ _ _ _ _
    · rw [node_root_of_leaves hT ℓ.toNode]
      exact triv_anch_le a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J q hGeo.cap_leaf hq
        ht h P.L roots _ x
  set u : ℂ := if V = 0 then 0 else V / (‖V‖ : ℂ) with hu
  have hu1 : ‖u‖ ≤ 1 := by
    rw [hu]
    split_ifs with hV0
    · simp
    · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hV0)]
  have hwu : (‖V‖ : ℂ) * u = V := by
    rw [hu]
    split_ifs with hV0
    · rw [hV0]; simp
    · have : (‖V‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hV0)
      field_simp
  obtain ⟨c, amp, hw0', hws', hamp1, hampS, hampc, hsum', hmass'⟩ :=
    (Classical.choose_spec (cap_centre P.d)).2 P.η
      (slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1 (.inl q))
      (fun ts => capSlotKer P.L P.γ P.δ p a J t s h roots Rf dag (.inl q) ts k₀) k₀ (fun _ : Unit => ‖V‖)
      (fun _ => 0) (fun _ => u) (fun _ => norm_nonneg _) Summable.of_finite
      (fun _ => hu1) (fun ts _ => by
        have hs := hasSum_single (f := fun l : Unit => ((‖V‖ : ℝ) : ℂ) * u * fsPhase 0 ts) ()
          (fun b' hb' => absurd (Subsingleton.elim b' ()) hb')
        have hv : ((‖V‖ : ℝ) : ℂ) * u * fsPhase 0 ts =
            capSlotKer P.L P.γ P.δ p a J t s h roots Rf dag (.inl q) ts k₀ := by
          rw [fsPhase_zero', mul_one, hwu, hval ts]
        rw [← hv]
        exact hs)
  refine ⟨Unit, inferInstance, fun l => capKcen P.d * ‖V‖, fun _ => 0, c, amp, hw0', hws', hamp1, hampS, hampc,
    hsum', ?_⟩
  refine le_trans (le_of_eq hmass') ?_
  rw [tsum_eq_single () (fun b' hb' => absurd (Subsingleton.elim b' ()) hb'), maxBracketPow_zero, one_mul]
  change ENNReal.ofReal (capKcen P.d) * ENNReal.ofReal ‖V‖ ≤ _
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one (one_le_capKcen P.d))]
  refine ENNReal.ofReal_le_ofReal ?_
  change capKcen P.d * ‖V‖ ≤ _
  rw [triv_size a.prime.data q ht, triv_incoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q ht]
  simp only [pow_zero, mul_one, Nat.cast_zero, mul_zero, Real.rpow_zero]
  have hK := one_le_capKcen P.d
  have hKc : capKcen P.d ≤ capKc P.d P.η := le_mul_of_one_le_right (by linarith) (le_max_left _ _)
  have hcF : 1 ≤ frontierConst P.d ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 (.inl q) :=
    one_le_pow₀ (one_le_frontierConst P.d)
  have hLSb := triv_leaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q ht b hb1
  have hLc : 1 ≤ P.L ^ (31 * (P.d : ℝ) + 6) := Real.one_le_rpow (by linarith) (by positivity)
  have h1 : 1 ≤ frontierConst P.d ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 (.inl q) *
      (b⁻¹ * Represents.slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        (fun _ => b.toNNReal) (.inl q)) := one_le_mul_of_one_le_of_one_le hcF hLSb
  calc capKcen P.d * ‖V‖ ≤ capKcen P.d * 1 := mul_le_mul_of_nonneg_left hVn (by linarith)
    _ ≤ capKc P.d P.η * 1 * 1 := by linarith
    _ ≤ capKc P.d P.η * (frontierConst P.d ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 (.inl q) *
        (b⁻¹ * Represents.slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (fun _ => b.toNNReal) (.inl q))) * P.L ^ (31 * (P.d : ℝ) + 6) := by
        have hKc0 : 0 ≤ capKc P.d P.η := by linarith
        gcongr

end Slot

/-! ### One parameter record -/

/-- **The cap-slot obligation at one parameter record**, from D3. -/
theorem capSlotObligationAt_of {P : WTParams} (hD3 : ProtPin.ProtBoundNTAt P) (hd : 3 ≤ P.d) (hη : 0 < P.η)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) :
    CapSlotObligationAt capKc P := by
  intro C hC R p a J t s hp hcan hsz hGeo _ ht hs roots h b hb1 hb Rf hRf dag q hq
  have hrec : recLG a = a.layered := sourceLayer_reconstructs a
  rw [← hrec] at hcan hGeo
  have hcap : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = .leaf := hGeo.cap_leaf
  have hRf1 : ∀ j r, Rf j = some r → 1 ≤ r := fun j r hr => by have := hRf j r hr; linarith
  rcases capSlot_cases a.prime.data a.prime.prime.1 J hcap q hq with htriv | ⟨X, hX, hne, hQ, h2, h1⟩ |
      ⟨X, hX, hne, hQ, h1, h2⟩
  · exact capSlot_triv_obl hL hd hη C a J t s hGeo roots h b hb1 Rf dag q hq htriv
  · exact capSlot_nontriv_obl hD3 hd hη hηγ hL hC1 hδ C hC a J t s hp hcan hsz hGeo hs.1 hs.2 ht.2 roots h b hb1 hb
      Rf hRf1 dag q (capSideLeft a.prime.data a.prime.prime.1 J q X hX hne hQ h2 h1)
  · exact capSlot_nontriv_obl hD3 hd hη hηγ hL hC1 hδ C hC a J t s hp hcan hsz hGeo hs.1 hs.2 ht.2 roots h b hb1 hb
      Rf hRf1 dag q (capSideRight a.prime.data a.prime.prime.1 J hcap q X hX hne hQ h1 h2)

/-! ### The prefix -/

theorem sqrt_add_pow8_le {g η : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hη : 0 < η) (hηg : η ≤ (g / 2) ^ 2) :
    η ^ 8 ≤ g - Real.sqrt η := by
  have h1 : Real.sqrt η ≤ g / 2 := by
    calc Real.sqrt η ≤ Real.sqrt ((g / 2) ^ 2) := Real.sqrt_le_sqrt hηg
      _ = g / 2 := Real.sqrt_sq (by linarith)
  have hη1 : η ≤ 1 := hηg.trans (by nlinarith)
  have h2 : η ^ 8 ≤ η := pow_le_of_le_one hη.le hη1 (by norm_num)
  have h3 : (g / 2) ^ 2 ≤ g / 2 := by nlinarith
  linarith

/-- **`CapSlotObligation`** (B3s, milestone α): proved from D3's `ProtPin.protBoundNTGate`. -/
theorem capSlotObligation : CapSlotObligation := by
  refine ⟨capKc, fun d η => one_le_capKc d η, ?_⟩
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := ProtPin.protBoundNTGate d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1def
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg1 : 0 < g1 := by
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    have : 0 < (d : ℝ) - 1 := by linarith
    positivity
  have hg1' : g1 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨min η₀ ((g1 / 2) ^ 2), lt_min hη₀ (by positivity), fun η hη φin hφin τs hτs φ hW => ?_⟩
  have hη1 : η ∈ Ioc 0 η₀ := ⟨hη.1, hη.2.trans (min_le_left _ _)⟩
  have hη2 : η ≤ (g1 / 2) ^ 2 := hη.2.trans (min_le_right _ _)
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H η hη1 φin hφin τs hτs φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD hτD
  refine ⟨C₂, hC₂, L₀, hL₀, fun L hL => ?_⟩
  exact capSlotObligationAt_of (H4 L hL) hd hη.1 (sqrt_add_pow8_le hg1 hg1' hη.1 hη2) (le_trans hL₀ hL) hC₁
    hδ.1.le

end WaveTurbulence.Flower.MkSlots
