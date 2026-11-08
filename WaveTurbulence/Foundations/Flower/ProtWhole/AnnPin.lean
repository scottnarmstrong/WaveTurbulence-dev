/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtWhole.AnnBound
public import WaveTurbulence.Foundations.Flower.ProtWhole.FoldBox
public import WaveTurbulence.Foundations.Flower.ProtOps.LocalExt
public import WaveTurbulence.Foundations.Flower.FiltCoh.TreeStarLayer
public import WaveTurbulence.Foundations.Flower.V5WB.W2.RowsS
public import WaveTurbulence.Foundations.Flower.MkDefs.ChiDNorm

/-! # D6b: a pinned protected object with a selected vertex (o82 Thm 18.2)

`annPin_of`: `ProtAnnPinSelAt` from D3's `ProtBoundSelAt` (the `X^{1/4}` input, ruling R181), D6a's `ProtPtwAt`
(the pointwise input, `L^6 M₂^{-1}`), the fold on the boxes (`fold_box`, D1b-F) and the local output extension
(D1b `localOutputExtension`):
`X^η ≤ C L^{31d} · (L^6 M₂^{-1})^τ (chiDNorm · L^{47d+2})^{1-τ}`, `τ = (1-8η)/9 ≥ 1/18` for `η ≤ 1/16`,
which is at most `L^{(47d+5)·2} M₂^{-1/18}` once `L` dominates the constants. The pinned object does not see its port
time (`kernelProt_port`), so its kernel is a continuous function of the upper clock (`continuous_kernelProt_up`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtWhole

open WaveTurbulence.Flower.ProtDefs

/-! ### The numerics -/

theorem annPin_real {L M₂ Cloc Cf cN τ : ℝ} {d : ℕ} (hL : 1 ≤ L) (hM : 1 ≤ M₂) (hτ1 : 1 / 18 ≤ τ) (hτ2 : τ ≤ 1)
    (hCloc : 0 ≤ Cloc) (hCf : 0 ≤ Cf) (hcN : 1 ≤ cN) (hC : Cloc * Cf * cN ≤ L) :
    Cloc * L ^ (31 * d) * Cf * (L ^ 6 * M₂⁻¹) ^ τ * cN ^ (1 - τ) * (L ^ (47 * d + 2)) ^ (1 - τ) ≤
      L ^ ((47 * d + 5) * 2) * M₂ ^ (-(1 / 18 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < M₂ := by linarith
  have h1 : (L ^ 6 * M₂⁻¹) ^ τ ≤ L ^ 6 * M₂ ^ (-(1 / 18 : ℝ)) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · calc (L ^ 6) ^ τ ≤ (L ^ 6) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hL) hτ2
        _ = L ^ 6 := Real.rpow_one _
    · rw [← Real.rpow_neg_one, ← Real.rpow_mul hM0.le]
      exact Real.rpow_le_rpow_of_exponent_le hM (by linarith)
  have h2 : cN ^ (1 - τ) ≤ cN := by
    calc cN ^ (1 - τ) ≤ cN ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hcN (by linarith)
      _ = cN := Real.rpow_one _
  have h3 : (L ^ (47 * d + 2)) ^ (1 - τ) ≤ L ^ (47 * d + 2) := by
    calc (L ^ (47 * d + 2)) ^ (1 - τ) ≤ (L ^ (47 * d + 2)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hL) (by linarith)
      _ = L ^ (47 * d + 2) := Real.rpow_one _
  have hMp : 0 ≤ M₂ ^ (-(1 / 18 : ℝ)) := Real.rpow_nonneg hM0.le _
  calc Cloc * L ^ (31 * d) * Cf * (L ^ 6 * M₂⁻¹) ^ τ * cN ^ (1 - τ) * (L ^ (47 * d + 2)) ^ (1 - τ)
      ≤ Cloc * L ^ (31 * d) * Cf * (L ^ 6 * M₂ ^ (-(1 / 18 : ℝ))) * cN * L ^ (47 * d + 2) := by
        gcongr
    _ = (Cloc * Cf * cN) * (L ^ (31 * d) * L ^ 6 * L ^ (47 * d + 2)) * M₂ ^ (-(1 / 18 : ℝ)) := by ring
    _ ≤ L * (L ^ (31 * d) * L ^ 6 * L ^ (47 * d + 2)) * M₂ ^ (-(1 / 18 : ℝ)) := by gcongr
    _ = L ^ (78 * d + 9) * M₂ ^ (-(1 / 18 : ℝ)) := by ring
    _ ≤ L ^ ((47 * d + 5) * 2) * M₂ ^ (-(1 / 18 : ℝ)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by omega)) hMp

theorem annPin_alg {Y : ℝ≥0∞} {L M₂ Cloc Cf cN τ : ℝ} {d : ℕ} (hL : 1 ≤ L) (hM : 1 ≤ M₂) (hτ1 : 1 / 18 ≤ τ)
    (hτ2 : τ ≤ 1) (hCloc : 0 ≤ Cloc) (hCf : 0 ≤ Cf) (hcN : 1 ≤ cN) (hC : Cloc * Cf * cN ≤ L) :
    ENNReal.ofReal (Cloc * L ^ (31 * d)) * (ENNReal.ofReal Cf * (Y * ENNReal.ofReal (L ^ 6 * M₂⁻¹)) ^ τ *
      (ENNReal.ofReal cN * Y * ENNReal.ofReal (L ^ (47 * d + 2))) ^ (1 - τ)) ≤
      Y * ENNReal.ofReal (L ^ ((47 * d + 5) * 2) * M₂ ^ (-(1 / 18 : ℝ))) := by
  have ht0 : 0 ≤ τ := by linarith
  have ht1 : 0 ≤ 1 - τ := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hM0 : 0 ≤ M₂ := by linarith
  rw [ENNReal.mul_rpow_of_nonneg _ _ ht0, ENNReal.mul_rpow_of_nonneg _ _ ht1,
    ENNReal.mul_rpow_of_nonneg _ _ ht1]
  have hY : Y ^ τ * Y ^ (1 - τ) = Y := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ ht0 ht1, show τ + (1 - τ) = 1 by ring, ENNReal.rpow_one]
  calc ENNReal.ofReal (Cloc * L ^ (31 * d)) * (ENNReal.ofReal Cf * (Y ^ τ * ENNReal.ofReal (L ^ 6 * M₂⁻¹) ^ τ) *
        (ENNReal.ofReal cN ^ (1 - τ) * Y ^ (1 - τ) * ENNReal.ofReal (L ^ (47 * d + 2)) ^ (1 - τ)))
      = (Y ^ τ * Y ^ (1 - τ)) * (ENNReal.ofReal (Cloc * L ^ (31 * d)) * ENNReal.ofReal Cf *
          ENNReal.ofReal (L ^ 6 * M₂⁻¹) ^ τ * ENNReal.ofReal cN ^ (1 - τ) *
          ENNReal.ofReal (L ^ (47 * d + 2)) ^ (1 - τ)) := by ring
    _ = Y * ENNReal.ofReal (Cloc * L ^ (31 * d) * Cf * (L ^ 6 * M₂⁻¹) ^ τ * cN ^ (1 - τ) *
          (L ^ (47 * d + 2)) ^ (1 - τ)) := by
        rw [hY, ENNReal.ofReal_rpow_of_nonneg (by positivity) ht0,
          ENNReal.ofReal_rpow_of_nonneg (by linarith) ht1, ENNReal.ofReal_rpow_of_nonneg (by positivity) ht1,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ Y * ENNReal.ofReal (L ^ ((47 * d + 5) * 2) * M₂ ^ (-(1 / 18 : ℝ))) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (annPin_real hL hM hτ1 hτ2 hCloc hCf hcN hC)) zero_le

/-! ### Facts about protected objects -/

theorem protShape_lone {p : ℕ} {X : RegChain} {w : ℕ} {LG : LayeredGarden w} (hsh : ProtShape p X LG) (s up : ℝ) :
    (∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1) ∧
      ∀ b, LG.garden.IsLoneParent b → ProtCfg.term.fix X s s up b ≠ none := by
  rcases w with _ | _ | _ | w
  · exact hsh.elim
  · -- paired trees
    obtain ⟨-, hdec, -, -⟩ := hsh
    refine ⟨PL234.card_lone_le_of_decodesTree hdec, ?_⟩
    rintro b ⟨ℓ, hl, ⟨-, i, hi⟩⟩
    have hlone : ℓ.1.2 = X.lonePath := by
      by_contra hne
      have hm := hdec.2.1 ℓ
      unfold Garden.IsLone at hl
      rw [hm, if_neg hne] at hl
      exact absurd hl (by simp)
    have hb : b.1.2 = X.lonePath.dropLast := by rw [← hlone, hi, List.dropLast_concat]
    unfold ProtCfg.fix
    rw [if_pos (Fin.val_eq_zero b.1.1), hb]
    simp [ProtCfg.pins]
  · -- cap couples: plain, no lone leaves
    obtain ⟨-, hdec, -⟩ := hsh
    have hplain : LG.garden.IsPlain := hdec.1.1
    have hnl : ∀ ℓ, ¬ LG.garden.IsLone ℓ := fun ℓ hl => by
      unfold Garden.IsLone at hl; rw [hplain ℓ] at hl; exact absurd hl (by simp)
    refine ⟨fun j => ?_, fun b ⟨ℓ, hl, _⟩ => absurd hl (hnl ℓ)⟩
    rw [Finset.card_le_one]
    intro a ha
    exact absurd (Finset.mem_filter.1 ha).2.2 (hnl a)
  · exact hsh.elim

theorem norm_filtWeight_le {w d : ℕ} {G : Garden w} (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool)
    (M : GBranch G.tree → ℝ) (k : GNode G.tree → Mom d) :
    ‖filtWeight F ann M k‖ ≤ (max 1 MkDefs.chiDConst) ^ F.card := by
  unfold filtWeight
  rw [norm_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun b _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs
  · exact (MkDefs.abs_chiD_le _).trans (le_max_right _ _)
  · rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
    exact (XChain.ProductCut.chi0_le_one _).trans (le_max_left _ _)

/-! ### The pinned selected case -/

/-- **`ProtAnnPinSelAt`** from `ProtBoundSelAt` and `ProtPtwAt`, for `L` beyond a constant of `d, η`. -/
theorem annPin_of (d : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 16) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : WTParams, P.d = d → P.η = η → 1 ≤ P.d → C ≤ P.L →
      ProtBoundSelAt P → ProtPtw.ProtPtwAt P → ProtAnnPinSelAt P := by
  obtain ⟨Cloc, hCloc0, hloc⟩ := ProtOps.localOutputExtension d η hη0
  obtain ⟨Cf, hCf0, hfold⟩ := fold_box d hη0 (by linarith : η < 1 / 8)
  set cN : ℝ := MkDefs.chiDNorm with hcN
  have hcN1 : 1 ≤ cN := MkDefs.one_le_chiDNorm
  refine ⟨max 1 (Cloc * Cf * cN), le_max_left _ _, ?_⟩
  intro P hdP hηP hd1 hCL hsel hptw p hp n hn w LG X hsh hsz pin Sel hpX hSel hr hcard hamb hcase M₂ hM₂ s hs1 hs2
    q' hq' _hlay S ω cω hω F M hM Fu Mu hMu ind hind hind1 H B hHB b₀ c₀
  subst hdP hηP
  obtain ⟨hpin, hne⟩ := hcase
  subst hpin
  obtain ⟨v, rfl⟩ : ∃ v, Sel = {v} := Finset.card_eq_one.1 (le_antisymm hcard (Finset.card_pos.2 hne))
  obtain ⟨hv0, hvp, hvne, hvd⟩ := hSel v (Finset.mem_singleton_self v)
  have hL1 : 1 ≤ P.L := (le_max_left _ _).trans hCL
  have hM₂1 : 1 ≤ M₂ := hL1.trans hM₂
  set τ : ℝ := (1 - 8 * P.η) / 9 with hτ
  -- the multipliers
  set mA : (GNode LG.garden.tree → Mom P.d) → ℂ := fun κ => Flower.IncTop.starWeight S ω κ *
    filtWeight (F ∪ {v}) (fun b => decide (b ∈ ({v} : Finset (GBranch LG.garden.tree))))
      (fun b => if b ∈ ({v} : Finset (GBranch LG.garden.tree)) then M₂ else M b) κ *
    filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ) with hmA
  set mS : (GNode LG.garden.tree → Mom P.d) → ℂ := fun κ => Flower.IncTop.starWeight S ω κ *
    filtWeight (F.erase v) (fun _ => false) M κ * filtWeight Fu (fun _ => false) Mu κ *
    ((MkDefs.chiDN (|omegaNode LG.garden κ v| / M₂) : ℝ) : ℂ) * (ind κ : ℂ) with hmS
  have hmAS : mA = fun κ => (cN : ℂ) * mS κ := by
    funext κ
    have hfw : filtWeight (F ∪ {v}) (fun b => decide (b ∈ ({v} : Finset (GBranch LG.garden.tree))))
        (fun b => if b ∈ ({v} : Finset (GBranch LG.garden.tree)) then M₂ else M b) κ =
        ((FlShell.chiD (|omegaNode LG.garden κ v| / M₂) : ℝ) : ℂ) * filtWeight (F.erase v) (fun _ => false) M κ := by
      unfold filtWeight
      rw [← Finset.mul_prod_erase (F ∪ {v}) _ (Finset.mem_union_right _ (Finset.mem_singleton_self v))]
      rw [show (F ∪ {v}).erase v = F.erase v by ext b; simp [and_comm, or_comm]]
      congr 1
      · simp
      · refine Finset.prod_congr rfl fun b hb => ?_
        have hbv : b ≠ v := (Finset.mem_erase.1 hb).1
        simp [hbv]
    have hchi : ((FlShell.chiD (|omegaNode LG.garden κ v| / M₂) : ℝ) : ℂ) =
        (cN : ℂ) * ((MkDefs.chiDN (|omegaNode LG.garden κ v| / M₂) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      unfold MkDefs.chiDN
      rw [hcN, mul_div_cancel₀ _ (ne_of_gt MkDefs.chiDNorm_pos)]
      rfl
    simp only [hmA, hmS, hfw, hchi]
    ring
  -- the bounded multiplier
  have hmA_bd : ∀ K, ‖mA K‖ ≤ (∏ a ∈ S, max (cω a) 0) * (max 1 MkDefs.chiDConst) ^ (F ∪ {v}).card *
      (max 1 MkDefs.chiDConst) ^ Fu.card * 1 := by
    intro K
    simp only [hmA]
    rw [norm_mul, norm_mul, norm_mul]
    refine mul_le_mul (mul_le_mul (mul_le_mul ?_ (norm_filtWeight_le _ _ _ _) (norm_nonneg _) (by positivity))
      (norm_filtWeight_le _ _ _ _) (norm_nonneg _) (by positivity)) ?_ (norm_nonneg _) (by positivity)
    · unfold Flower.IncTop.starWeight
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun a ha => FiltCoh.norm_star_le (hω a ha) _
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hind.1 K).1]
      exact (hind.1 K).2
  obtain ⟨hlone, hlp⟩ := protShape_lone hsh s 0
  -- the kernel, as a function of the upper clock
  set FA : (Fin 2 → ℝ) → Mom P.d → ℂ := fun ts k => kernelProt P.L P.γ P.δ LG H mA (fun _ => ts 0) (ts 1)
    ((if true = true then ProtCfg.term else ProtCfg.none).fix X s s (ts 0)) k (fun _ => 0) 0 with hFA
  have hfixT : ∀ up : ℝ, ((if true = true then ProtCfg.term else ProtCfg.none).fix X s s up :
      GBranch LG.garden.tree → Option ℝ) = ProtCfg.term.fix X s s 0 := fun up =>
    fix_up_indep ProtCfg.term (by decide) X s s up 0
  have hGfun : ∀ (k : Mom P.d) (ts : Fin 2 → ℝ), FA ts k =
      (fun T => kernelProt P.L P.γ P.δ LG H mA (fun _ => T) 0 (ProtCfg.term.fix X s s 0) k (fun _ => 0) 0) (ts 0) := by
    intro k ts
    simp only [hFA, hfixT]
    exact kernelProt_port _ _ _ _ _ _ _ _ _ _ _ _ _ (fun b hb => hlp b hb)
  have hGc : ∀ k : Mom P.d, Continuous fun T =>
      kernelProt P.L P.γ P.δ LG H mA (fun _ => T) 0 (ProtCfg.term.fix X s s 0) k (fun _ => 0) 0 := by
    intro k
    rcases Nat.eq_zero_or_pos P.d with h0 | hdpos
    · omega
    exact continuous_kernelProt_up P.L P.γ P.δ LG H mA _ hmA_bd 0 _ k hlone
      (hHB.summable_coset (Nat.succ_le_of_lt hdpos) hL1 k)
  set Y : ℝ≥0∞ := (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n (protIncoh X LG) *
    ENNReal.ofReal (leafSizeProduct LG B) with hY
  -- the pointwise input (D6a)
  have hsup : ∀ k : Mom P.d, (⨆ (T : ℝ) (_ : T ∈ Icc (p : ℝ) (p + 1)),
      ‖kernelProt P.L P.γ P.δ LG H mA (fun _ => T) 0 (ProtCfg.term.fix X s s 0) k (fun _ => 0) 0‖ₑ) ≤
      Y * ENNReal.ofReal (P.L ^ 6 * M₂⁻¹) := by
    intro k
    refine iSup₂_le fun T _ => ?_
    have key := hptw p hp n hn w LG X hsh hsz true {v} hpX hSel hcard M₂ hM₂ s S ω cω hω F M hM Fu Mu hMu ind
      hind hind1 H B hHB T 0 k
    rw [hfixT T] at key
    refine key.trans (le_of_eq ?_)
    simp only [Finset.card_singleton, if_true, Nat.cast_one, Real.rpow_neg_one, hY]
    ring
  -- the X^{1/4} input (D3, R181), at q' = p
  have hquart : ∀ k ∈ latticeBall P.L b₀ c₀, XNorm00Restr (1 / 4) (timeBoxGt p p) {k} FA ≤
      ENNReal.ofReal cN * Y * ENNReal.ofReal (P.L ^ (47 * P.d + 2)) := by
    intro k hk
    have hsel' := hsel p hp n hn w LG X hsh hsz (hpX rfl) hamb v hv0 hvp hvne (hvd rfl) M₂ hM₂ s hs1 hs2 p le_rfl
      S ω cω hω (F.erase v) M (fun b hb => hM b (Finset.mem_of_mem_erase hb)) (Finset.notMem_erase v F) Fu Mu hMu
      ind hind H B hHB b₀ c₀
    have hFA' : FA = fun ts k => (cN : ℂ) * kernelProt P.L P.γ P.δ LG H mS (fun _ => ts 0) (ts 1)
        (ProtCfg.term.fix X s s (ts 0)) k (fun _ => 0) 0 := by
      funext ts k
      simp only [hFA, hmAS]
      exact kernelProt_smul_m _ _ _ _ _ _ _ _ _ _ _ _ _
    have hle1 : XNorm00Restr (1 / 4) (timeBoxGt p p) {k} FA ≤ XNormRestr (1 / 4) (30 * P.d) 0 (timeBoxGt p p)
        (latticeBall P.L b₀ c₀) FA := by
      unfold XNormRestr
      refine le_iInf₂ fun G hG => ?_
      refine (iInf₂_le_of_le G (fun t ht v' hv' => by
        rw [Set.mem_singleton_iff] at hv'; subst hv'; exact hG t ht v' hk) le_rfl).trans ?_
      exact VineEstS3.XNorm00_le_XNorm _ _ _ G
    refine hle1.trans ?_
    rw [hFA']
    refine (V5WB.XNormRestr_const_mul_le (by exact_mod_cast (ne_of_gt MkDefs.chiDNorm_pos)) _ _ _ _ _ _).trans ?_
    rw [show ‖(cN : ℂ)‖ₑ = ENNReal.ofReal cN by
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]]
    calc ENNReal.ofReal cN * XNormRestr (1 / 4) (30 * P.d) 0 (timeBoxGt p p) (latticeBall P.L b₀ c₀)
          (fun ts k => kernelProt P.L P.γ P.δ LG H mS (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s s (ts 0)) k
            (fun _ => 0) 0)
        ≤ ENNReal.ofReal cN * ((∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (47 * P.d + 2)) *
            regBound P n (protIncoh X LG) * ENNReal.ofReal (leafSizeProduct LG B)) :=
          mul_le_mul_of_nonneg_left hsel' zero_le
      _ = ENNReal.ofReal cN * Y * ENNReal.ofReal (P.L ^ (47 * P.d + 2)) := by rw [hY]; ring
  -- per output: the fold
  have hk : ∀ k ∈ latticeBall P.L b₀ c₀, XNorm00Restr P.η (timeBoxGt p q') {k} FA ≤
      ENNReal.ofReal Cf * (Y * ENNReal.ofReal (P.L ^ 6 * M₂⁻¹)) ^ τ *
        (ENNReal.ofReal cN * Y * ENNReal.ofReal (P.L ^ (47 * P.d + 2))) ^ (1 - τ) := by
    intro k hk
    refine (hfold p q' hq' FA k _ (hGc k) (hGfun k)).trans ?_
    have ht0 : 0 ≤ τ := by rw [hτ]; linarith
    have ht1 : 0 ≤ 1 - τ := by rw [hτ]; linarith
    gcongr
    · exact hsup k
    · exact hquart k hk
  have hext := hloc P.L hL1 (timeBoxGt p q') b₀ c₀ FA _ hk
  refine hext.trans ?_
  have hτ1 : 1 / 18 ≤ τ := by rw [hτ]; linarith
  have hτ2 : τ ≤ 1 := by rw [hτ]; linarith
  have hfinal := annPin_alg (Y := Y) (d := P.d) hL1 hM₂1 hτ1 hτ2 hCloc0 hCf0 hcN1 ((le_max_right _ _).trans hCL)
  refine hfinal.trans (le_of_eq ?_)
  simp only [hY, Finset.card_singleton, if_true, Nat.cast_one]
  ring_nf

/-! ### The gate -/

theorem protBoundSelAt_mono : LargeConstantMonotone ProtBoundSelAt := by
  intro P c₁ c₂ hC _hC₂ hδ hL hCC _hCC₂ h p hp n hn w LG X a1 a2 a3 a4 v a5 a6 a7 a8 M₂ a9 s a10 a11 q' a12 S ω cω
    a13 F M a14 a14' Fu Mu a15 ind a16 H B a17 b₀ c₀
  rw [N_largeConstants] at hn
  exact (h p hp n hn w LG X a1 a2 a3 a4 v a5 a6 a7 a8 M₂ a9 s a10 a11 q' a12 S ω cω a13 F M a14 a14' Fu Mu a15 ind
    a16 H B a17 b₀ c₀).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (regBound_largeConstants_mono P (by linarith) hCC hδ.le (by linarith) n _) zero_le) zero_le)

/-- **`ProtAnnBoundGate`** from D3's two gates (`ProtBoundGate`, R181's `ProtBoundSelGate`) and the unpinned
selected case (F-D6b-4); D6a's gate is `ProtPtw.protPtwGate`. -/
theorem protAnnBoundGate_of_sel (hD3 : ProtBoundGate) (hSel : ProtBoundSelGate)
    (hfree : WTPrefix ProtAnnFreeSelAt) : ProtAnnBoundGate := by
  have h1 : WTPrefix (fun P => ProtBoundAt P ∧ ProtAnnFreeSelAt P) :=
    prefix_and hD3 hfree protBoundAt_mono (protAnnCaseAt_mono _)
  have h2 : WTPrefix (fun P => (ProtBoundAt P ∧ ProtAnnFreeSelAt P) ∧ ProtBoundSelAt P) :=
    prefix_and h1 hSel (protBoundAt_mono.and (protAnnCaseAt_mono _)) protBoundSelAt_mono
  have hall : WTPrefix (fun P => ((ProtBoundAt P ∧ ProtAnnFreeSelAt P) ∧ ProtBoundSelAt P) ∧ ProtPtw.ProtPtwAt P) :=
    prefix_and h2 ProtPtw.protPtwGate ((protBoundAt_mono.and (protAnnCaseAt_mono _)).and protBoundSelAt_mono)
      protPtwAt_mono
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := hall d hd γ hγ
  refine ⟨min η₀ (1 / 16), lt_min hη₀ (by norm_num), fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨Cp, hCp1, hCp⟩ := annPin_of d hη.1.le (hη.2.trans (min_le_right _ _))
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩ φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD htime
  refine ⟨C₂, hC₂, max L₀ Cp, le_max_of_le_left hL₀, fun L hL => ?_⟩
  obtain ⟨⟨⟨hb, hf⟩, hs⟩, hp⟩ := H4 L ((le_max_left _ _).trans hL)
  have hL1 : (1 : ℝ) ≤ L := by linarith [le_max_left L₀ Cp]
  exact protAnnBoundAt_of_cases _ hb hL1 (show 1 ≤ d by omega) hf
    (hCp _ rfl rfl (show 1 ≤ d by omega) ((le_max_right _ _).trans hL) hs hp)

end WaveTurbulence.Flower.ProtWhole
