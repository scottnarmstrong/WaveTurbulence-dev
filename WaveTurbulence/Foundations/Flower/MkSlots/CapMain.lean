/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapFin
public import WaveTurbulence.Foundations.Flower.ProtPin.NTGate

/-! # B3s MK-SLOTS (cap slots): **`capSlotObligation : CapSlotObligation`**

The isolated cap-slot hypothesis of the integration (`IntCapHyp.lean`), proved:
* a trivial cap couple (two leaf trees) has a constant slot kernel of modulus `≤ 1` (`CapTriv`, `CapFin`), one
  centred mode;
* a nontrivial cap couple is D2b's paired tree `objTree` of the reconstruction with the `term` pin; its slot
  kernel is a unimodular constant times D3's admissible protected kernel (`CapNat`, `CapKerQ`, `CapMul*`), bounded
  by D3's proved `ProtPin.protBoundNTGate` (`CapD3`), turned into a superposition on the slot box (`CapSup`) and
  centred at the cap momentum (`CapCen`); the mass is compared with the B3 slot mass (`capMass_le`).

The constant: `capKc d η = capKcen d · max 1 (2 · capCsup d η)` (centring constant and main's Fourier
superposition constant at `θ = η`, `Λ = 30 d`). The prefix: D3's prefix with `η` also below `(γ₁/2)²` (so that
`√η + η⁸ ≤ γ₁`, comparing D3's incoherency gain `L^{-(γ₁-√η)g}` with `L^{-η⁸ g}`). -/

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

/-! ### The constants -/

/-- The centring constant (`cap_centre`). -/
def capKcen (d : ℕ) : ℝ := Classical.choose (cap_centre d)

theorem one_le_capKcen (d : ℕ) : 1 ≤ capKcen d := (Classical.choose_spec (cap_centre d)).1

/-- The Fourier superposition constant at `θ = η`, `Λ = 30 d` (`0` for `η < 0`). -/
def capCsup (d : ℕ) (η : ℝ) : ℝ≥0∞ :=
  if h : 0 ≤ η then Classical.choose (exists_capSupProp d h) else 0

theorem capCsup_ne_top (d : ℕ) (η : ℝ) : capCsup d η ≠ ⊤ := by
  unfold capCsup
  split_ifs with h
  · exact (Classical.choose_spec (exists_capSupProp d h)).1
  · exact ENNReal.zero_ne_top

theorem capCsup_spec (d : ℕ) {η : ℝ} (h : 0 ≤ η) : CapSupProp d η (capCsup d η) := by
  unfold capCsup
  rw [dif_pos h]
  exact (Classical.choose_spec (exists_capSupProp d h)).2

/-- **The cap-slot constant.** -/
def capKc (d : ℕ) (η : ℝ) : ℝ := capKcen d * max 1 (2 * (capCsup d η).toReal)

theorem one_le_capKc (d : ℕ) (η : ℝ) : 1 ≤ capKc d η :=
  one_le_mul_of_one_le_of_one_le (one_le_capKcen d) (le_max_left _ _)

/-! ### The mass comparison -/

theorem capRegBound_le (P : WTParams) (C : ℝ) (hC : P.C₁ ≤ C) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (n g : ℕ) (hn : 1 ≤ n) :
    P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) ≤
      (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) := by
  have hC0 : 0 ≤ P.C₁ := le_trans zero_le_one hC1
  have hCC : 1 ≤ C := hC1.trans hC
  have h1 : (C * Real.sqrt P.δ) ^ (2 * n) = (C ^ 2) ^ n * P.δ ^ n := by
    rw [pow_mul, mul_pow, Real.sq_sqrt hδ, mul_pow]
  have h2 : P.C₁ * (P.C₁ * P.δ) ^ n = P.C₁ ^ (n + 1) * P.δ ^ n := by
    rw [mul_pow, pow_succ]; ring
  have h3 : P.C₁ ^ (n + 1) ≤ (C ^ 2) ^ n := by
    calc P.C₁ ^ (n + 1) ≤ C ^ (n + 1) := pow_le_pow_left₀ hC0 hC _
      _ ≤ C ^ (2 * n) := pow_le_pow_right₀ hCC (by omega)
      _ = (C ^ 2) ^ n := pow_mul C 2 n
  have h4 : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) ≤ P.L ^ (-(P.η ^ 8) * (g : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le hL ?_
    have hg : (0 : ℝ) ≤ g := Nat.cast_nonneg g
    nlinarith
  rw [h1, h2]
  have hδn : 0 ≤ P.δ ^ n := pow_nonneg hδ n
  have hLp : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := Real.rpow_nonneg (by linarith) _
  calc P.C₁ ^ (n + 1) * P.δ ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ))
      ≤ (C ^ 2) ^ n * P.δ ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := by gcongr
    _ ≤ (C ^ 2) ^ n * P.δ ^ n * P.L ^ (-(P.η ^ 8) * (g : ℝ)) := by gcongr

theorem capMass_le (P : WTParams) (C : ℝ) (hC : P.C₁ ≤ C) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (Kcen Cs Kc : ℝ) (hKcen : 0 ≤ Kcen) (hCs : 0 ≤ Cs)
    (hKc : Kcen * (2 * Cs) ≤ Kc) (ns nr : ℕ) (hns : ns ≤ nr) (n g : ℕ) (hn : 1 ≤ n) (LSb : ℝ) (hLSb : 0 ≤ LSb) :
    ENNReal.ofReal Kcen * (ENNReal.ofReal Cs * (2 * (ENNReal.ofReal (frontierConst P.d ^ ns) *
        ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) * regBound P n g * ENNReal.ofReal LSb))) ≤
      ENNReal.ofReal (Kc * (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) *
        (frontierConst P.d ^ nr * LSb) * P.L ^ (31 * (P.d : ℝ) + 6)) := by
  have hcF := one_le_frontierConst P.d
  have hcF0 : 0 ≤ frontierConst P.d := le_trans zero_le_one hcF
  set Lc := P.L ^ (31 * (P.d : ℝ) + 6)
  have hLc : 0 ≤ Lc := Real.rpow_nonneg (by linarith) _
  set R := P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ))
  have hR : 0 ≤ R := by
    have : 0 ≤ P.C₁ := le_trans zero_le_one hC1
    positivity
  have hreg : regBound P n g = ENNReal.ofReal R := rfl
  rw [hreg, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  rw [← ENNReal.ofReal_mul (pow_nonneg hcF0 _), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul hCs, ← ENNReal.ofReal_mul hKcen]
  refine ENNReal.ofReal_le_ofReal ?_
  have hR' := capRegBound_le P C hC hC1 hδ hL hηγ n g hn
  have hpow : frontierConst P.d ^ ns ≤ frontierConst P.d ^ nr := pow_le_pow_right₀ hcF hns
  have hAB : 0 ≤ (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) := by
    have : 0 ≤ C * Real.sqrt P.δ := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    positivity
  have hK0 : 0 ≤ Kc := le_trans (by positivity) hKc
  calc Kcen * (Cs * (2 * (frontierConst P.d ^ ns * Lc * R * LSb)))
      = (Kcen * (2 * Cs)) * frontierConst P.d ^ ns * R * LSb * Lc := by ring
    _ ≤ Kc * frontierConst P.d ^ nr * ((C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ))) * LSb * Lc := by
        gcongr
    _ = Kc * (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) * (frontierConst P.d ^ nr * LSb) * Lc := by
        ring

/-! ### One cap pair -/

section Slot

variable {P : WTParams} (hD3 : ProtPin.ProtBoundNTAt P) (hd : 3 ≤ P.d) (hη : 0 < P.η)
  (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
  (C : ℝ) (hC : P.C₁ ≤ C) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (t s : ℝ)
  (hp : p < P.D) (hcan : IsCanonGC (p + 1) (recLG a)) (hsz : a.prime.data.size ≤ P.N (p + 1) ^ 4)
  (hGeo : CapGeo (recLG a) J p) (hps : (p : ℝ) < s) (hst : s < t) (htp : t < p + 1)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
  (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
  (Rf : Fin (2 * R) → Option ℝ) (hRf1 : ∀ j r, Rf j = some r → 1 ≤ r)
  (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (q : SourcePair a.prime.skeleton)

include hD3 hd hη hηγ hL hC1 hδ hC hp hcan hsz hGeo hps hst htp hb1 hb hRf1 in
/-- **A nontrivial cap slot.** -/
theorem capSlot_nontriv_obl (K : CapSide a.prime.data a.prime.prime.1 J q) :
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
  have hL1 : 1 ≤ P.L := by linarith
  obtain ⟨wt, u, hw0, hws, hu, hsum, hmass⟩ := K.capSlot_sup (sourceLayer a) (sourceLayer_isLayering a) hGeo hD3
    (capCsup_spec P.d hη.le) hη.le (by omega) hL1 hcan hp hsz hps hst htp h b hb1 hb Rf hRf1 dag roots
  set k₀ := latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)) with hk₀
  have hk₀' : k₀ = latticePoint P.L (roots K.cleaf.1.1) := by rw [hk₀, K.capTree]
  obtain ⟨c, amp, hw0', hws', hamp1, hampS, hampc, hsum', hmass'⟩ :=
    (Classical.choose_spec (cap_centre P.d)).2 P.η
      (slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1 (.inl q))
      (fun ts => capSlotKer P.L P.γ P.δ p a J t s h roots Rf dag (.inl q) ts k₀) k₀ wt (fun m => capMode K.j0 m) u
      hw0 hws hu (fun ts hts => by rw [hk₀']; exact hsum ts hts)
  refine ⟨Fin 2 → ℤ, inferInstance, fun l => capKcen P.d * wt l, fun l => capMode K.j0 l, c, amp, hw0', hws',
    hamp1, hampS, hampc, hsum', ?_⟩
  -- the mass
  have hCs := capCsup_ne_top P.d P.η
  set Cs := (capCsup P.d P.η).toReal
  have hCs0 : 0 ≤ Cs := ENNReal.toReal_nonneg
  have hcF0 : 0 ≤ frontierConst P.d := le_trans zero_le_one (one_le_frontierConst P.d)
  have hLSb : 0 ≤ b⁻¹ * Represents.slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (fun _ => b.toNNReal) (.inl q) := by
    refine mul_nonneg (inv_nonneg.2 (by linarith)) ?_
    unfold Represents.slotLeaf leafSizeProduct
    exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hn : 1 ≤ K.X.size / 2 := by have := K.two_le_size; omega
  have hsize : Represents.slotSize a.prime.data (.inl q) = 2 * (K.X.size / 2) := by
    rw [K.slotSize_eq]
    obtain ⟨r, hr⟩ := chain_size_even K.X
    omega
  rw [hsize]
  calc ∑' l, maxBracketPow P.η (half (capMode K.j0 l)) * ENNReal.ofReal (capKcen P.d * wt l)
      = ENNReal.ofReal (capKcen P.d) * ∑' l, maxBracketPow P.η (half (capMode K.j0 l)) * ENNReal.ofReal (wt l) :=
        hmass'
    _ ≤ ENNReal.ofReal (capKcen P.d) * (ENNReal.ofReal Cs * (2 * (ENNReal.ofReal (frontierConst P.d ^
          (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p).card) *
          ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
          regBound P (K.X.size / 2) (Represents.slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a) (.inl q)) *
          ENNReal.ofReal (b⁻¹ * Represents.slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a) (fun _ => b.toNNReal) (.inl q))))) := by
        refine mul_le_mul' le_rfl (hmass.trans (le_of_eq ?_))
        rw [ENNReal.ofReal_toReal hCs, Finset.prod_const, ENNReal.ofReal_pow hcF0]
    _ ≤ _ := capMass_le P C hC hC1 hδ hL1 hηγ (capKcen P.d) Cs (capKc P.d P.η)
          (le_trans zero_le_one (one_le_capKcen P.d)) hCs0
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (le_trans zero_le_one (one_le_capKcen P.d))) _ _
          (K.frontS_card_le (sourceLayer a) (sourceLayer_isLayering a)) _ _ hn _ hLSb

end Slot

end WaveTurbulence.Flower.MkSlots
