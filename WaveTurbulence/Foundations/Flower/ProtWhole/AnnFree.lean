/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtWhole.AnnQuarter
public import WaveTurbulence.Foundations.Flower.ProtWhole.AnnSel
public import WaveTurbulence.Foundations.Flower.ProtWhole.ContJ
public import WaveTurbulence.Foundations.Flower.ProtWhole.FoldFree
public import WaveTurbulence.Foundations.Flower.ProtPin.RootPack

/-! # D6b: an unpinned protected object with a selected vertex (o82 Thm 18.2), and the whole gate

`annFree_of`: `ProtAnnFreeSelAt` from the `X^{1/4}` bound `NoneAnnAt` (D5 FILT-GATE and D3's flat gate,
`AnnQuarter.lean`), D6a's `ProtPtwAt` (the pointwise input, `L^3 M₂^{-1}`), the fold on the boxes for kernels that
read the port time (`fold_free`, D1b-F) and the local output extension (D1b `localOutputExtension`):
`X^η ≤ C L^{31d} · (L^3 M₂^{-1})^τ (L^{4d})^{1-τ}`, `τ = (1-8η)/9 ≥ 1/18` for `η ≤ 1/16`, which is at most
`L^{47d+5} M₂^{-1/18}` once `L` dominates the constants. The unpinned kernel is jointly continuous in the upper
clock and the port time (`continuous_kernelProt_joint`); below the layer `p` of the free lone parents it does not
read the port time (D3's `kernelProt_port_low`), which is what `fold_free` needs on the boxes with `q' < p`.

`annFreeGate : WTPrefix ProtAnnFreeSelAt` (no hypothesis), and
**`protAnnBoundGate_of_D3 : ProtBoundGate → ProtAnnBoundGate`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtWhole

open WaveTurbulence.Flower.ProtDefs

/-! ### The numerics -/

theorem annFree_real {L M₂ Cloc Cf τ : ℝ} {d : ℕ} (hL : 1 ≤ L) (hM : 1 ≤ M₂) (hτ1 : 1 / 18 ≤ τ) (hτ2 : τ ≤ 1)
    (hCloc : 0 ≤ Cloc) (hCf : 0 ≤ Cf) (hC : Cloc * Cf ≤ L) :
    Cloc * L ^ (31 * d) * Cf * (L ^ 3 * M₂⁻¹) ^ τ * (L ^ (4 * (d : ℝ))) ^ (1 - τ) ≤
      L ^ (47 * d + 5) * M₂ ^ (-(1 / 18 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < M₂ := by linarith
  have h1 : (L ^ 3 * M₂⁻¹) ^ τ ≤ L ^ 3 * M₂ ^ (-(1 / 18 : ℝ)) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · calc (L ^ 3) ^ τ ≤ (L ^ 3) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hL) hτ2
        _ = L ^ 3 := Real.rpow_one _
    · rw [← Real.rpow_neg_one, ← Real.rpow_mul hM0.le]
      exact Real.rpow_le_rpow_of_exponent_le hM (by linarith)
  have e4 : L ^ (4 * (d : ℝ)) = L ^ (4 * d) := by
    rw [show (4 * (d : ℝ)) = ((4 * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have h3 : (L ^ (4 * (d : ℝ))) ^ (1 - τ) ≤ L ^ (4 * d) := by
    rw [e4]
    calc (L ^ (4 * d)) ^ (1 - τ) ≤ (L ^ (4 * d)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hL) (by linarith)
      _ = L ^ (4 * d) := Real.rpow_one _
  have hMp : 0 ≤ M₂ ^ (-(1 / 18 : ℝ)) := Real.rpow_nonneg hM0.le _
  calc Cloc * L ^ (31 * d) * Cf * (L ^ 3 * M₂⁻¹) ^ τ * (L ^ (4 * (d : ℝ))) ^ (1 - τ)
      ≤ Cloc * L ^ (31 * d) * Cf * (L ^ 3 * M₂ ^ (-(1 / 18 : ℝ))) * L ^ (4 * d) := by
        gcongr
    _ = (Cloc * Cf) * (L ^ (31 * d) * L ^ 3 * L ^ (4 * d)) * M₂ ^ (-(1 / 18 : ℝ)) := by ring
    _ ≤ L * (L ^ (31 * d) * L ^ 3 * L ^ (4 * d)) * M₂ ^ (-(1 / 18 : ℝ)) := by gcongr
    _ = L ^ (35 * d + 4) * M₂ ^ (-(1 / 18 : ℝ)) := by ring
    _ ≤ L ^ (47 * d + 5) * M₂ ^ (-(1 / 18 : ℝ)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by omega)) hMp

theorem annFree_alg {Y : ℝ≥0∞} {L M₂ Cloc Cf τ : ℝ} {d : ℕ} (hL : 1 ≤ L) (hM : 1 ≤ M₂) (hτ1 : 1 / 18 ≤ τ)
    (hτ2 : τ ≤ 1) (hCloc : 0 ≤ Cloc) (hCf : 0 ≤ Cf) (hC : Cloc * Cf ≤ L) :
    ENNReal.ofReal (Cloc * L ^ (31 * d)) * (ENNReal.ofReal Cf * (Y * ENNReal.ofReal (L ^ 3 * M₂⁻¹)) ^ τ *
      (Y * ENNReal.ofReal (L ^ (4 * (d : ℝ)))) ^ (1 - τ)) ≤
      Y * ENNReal.ofReal (L ^ (47 * d + 5) * M₂ ^ (-(1 / 18 : ℝ))) := by
  have ht0 : 0 ≤ τ := by linarith
  have ht1 : 0 ≤ 1 - τ := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hM0 : 0 ≤ M₂ := by linarith
  rw [ENNReal.mul_rpow_of_nonneg _ _ ht0, ENNReal.mul_rpow_of_nonneg _ _ ht1]
  have hY : Y ^ τ * Y ^ (1 - τ) = Y := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ ht0 ht1, show τ + (1 - τ) = 1 by ring, ENNReal.rpow_one]
  calc ENNReal.ofReal (Cloc * L ^ (31 * d)) * (ENNReal.ofReal Cf * (Y ^ τ * ENNReal.ofReal (L ^ 3 * M₂⁻¹) ^ τ) *
        (Y ^ (1 - τ) * ENNReal.ofReal (L ^ (4 * (d : ℝ))) ^ (1 - τ)))
      = (Y ^ τ * Y ^ (1 - τ)) * (ENNReal.ofReal (Cloc * L ^ (31 * d)) * ENNReal.ofReal Cf *
          ENNReal.ofReal (L ^ 3 * M₂⁻¹) ^ τ * ENNReal.ofReal (L ^ (4 * (d : ℝ))) ^ (1 - τ)) := by ring
    _ = Y * ENNReal.ofReal (Cloc * L ^ (31 * d) * Cf * (L ^ 3 * M₂⁻¹) ^ τ * (L ^ (4 * (d : ℝ))) ^ (1 - τ)) := by
        rw [hY, ENNReal.ofReal_rpow_of_nonneg (by positivity) ht0,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) ht1,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ Y * ENNReal.ofReal (L ^ (47 * d + 5) * M₂ ^ (-(1 / 18 : ℝ))) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (annFree_real hL hM hτ1 hτ2 hCloc hCf hC)) zero_le

/-! ### Facts about protected objects -/

/-- The free lone parents of a protected object are in layer `p` (cap couples have none). -/
theorem protShape_loneParent_layer {p : ℕ} {X : RegChain} {w : ℕ} {LG : LayeredGarden w}
    (hsh : ProtShape p X LG) (b : GBranch LG.garden.tree) (hb : LG.garden.IsLoneParent b) :
    LG.layer b.toNode = p := by
  rcases w with _ | _ | _ | w
  · exact hsh.elim
  · exact ProtPin.loneParent_layer hsh b hb
  · exfalso
    obtain ⟨-, hdec, -⟩ := hsh
    exact ProtPin.not_loneParent_of_isPlain hdec.1.1 b hb
  · exact hsh.elim

/-- One output of a box restriction is bounded by the local norm on any output set containing it. -/
theorem xnorm00_le_restr {r d : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) (B : Set (Fin r → ℝ)) {K : Set (Mom d)} {k : Mom d}
    (hk : k ∈ K) (F : (Fin r → ℝ) → Mom d → ℂ) : XNorm00Restr θ B {k} F ≤ XNormRestr θ Λ₁ Λ₂ B K F := by
  unfold XNormRestr
  refine le_iInf₂ fun G hG => ?_
  refine (iInf₂_le_of_le G (fun t ht v' hv' => by
    rw [Set.mem_singleton_iff] at hv'; subst hv'; exact hG t ht v' hk) le_rfl).trans ?_
  exact VineEstS3.XNorm00_le_XNorm _ _ _ G

/-! ### The unpinned selected case -/

/-- **`ProtAnnFreeSelAt`** from `NoneAnnAt` and `ProtPtwAt`, for `L` beyond a constant of `d, η`. -/
theorem annFree_of (d : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 16) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : WTParams, P.d = d → P.η = η → 1 ≤ P.d → C ≤ P.L →
      NoneAnnAt P → ProtPtw.ProtPtwAt P → ProtAnnFreeSelAt P := by
  obtain ⟨Cloc, hCloc0, hloc⟩ := ProtOps.localOutputExtension d η hη0
  obtain ⟨Cf, hCf0, hfold⟩ := fold_free d hη0 (by linarith : η < 1 / 8)
  refine ⟨max 1 (Cloc * Cf), le_max_left _ _, ?_⟩
  intro P hdP hηP hd1 hCL hquar hptw p hp n hn w LG X hsh hsz pin Sel hpX hSel hr hcard hamb hcase M₂ hM₂ s _hs1
    _hs2 q' hq' _hlay S ω cω hω F M hM Fu Mu hMu ind hind hind1 H B hHB b₀ c₀
  subst hdP hηP hcase
  have hc1 : 1 ≤ Sel.card := by simpa using hr
  obtain ⟨v, rfl⟩ : ∃ v, Sel = {v} := Finset.card_eq_one.1 (le_antisymm hcard hc1)
  have hL1 : 1 ≤ P.L := (le_max_left _ _).trans hCL
  have hM₂1 : 1 ≤ M₂ := hL1.trans hM₂
  set τ : ℝ := (1 - 8 * P.η) / 9 with hτ
  -- the multipliers: with the dagger (`= 1`) and without
  set mA : (GNode LG.garden.tree → Mom P.d) → ℂ := fun κ => Flower.IncTop.starWeight S ω κ *
    filtWeight (F ∪ {v}) (fun b => decide (b ∈ ({v} : Finset (GBranch LG.garden.tree))))
      (fun b => if b ∈ ({v} : Finset (GBranch LG.garden.tree)) then M₂ else M b) κ *
    filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ) with hmA
  set mB : (GNode LG.garden.tree → Mom P.d) → ℂ := fun κ => Flower.IncTop.starWeight S ω κ *
    filtWeight (F ∪ {v}) (fun b => decide (b ∈ ({v} : Finset (GBranch LG.garden.tree))))
      (fun b => if b ∈ ({v} : Finset (GBranch LG.garden.tree)) then M₂ else M b) κ *
    filtWeight Fu (fun _ => false) Mu κ with hmB
  have hmAB : mA = mB := by
    funext κ
    simp only [hmA, hmB, hind1 rfl κ, Complex.ofReal_one, mul_one]
  have hmB_bd : ∀ K, ‖mB K‖ ≤ (∏ a ∈ S, max (cω a) 0) * (max 1 MkDefs.chiDConst) ^ (F ∪ {v}).card *
      (max 1 MkDefs.chiDConst) ^ Fu.card := by
    intro K
    simp only [hmB]
    rw [norm_mul, norm_mul]
    refine mul_le_mul (mul_le_mul ?_ (norm_filtWeight_le _ _ _ _) (norm_nonneg _) (by positivity))
      (norm_filtWeight_le _ _ _ _) (norm_nonneg _) (by positivity)
    unfold Flower.IncTop.starWeight
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun a ha => FiltCoh.norm_star_le (hω a ha) _
  have hM' : ∀ b ∈ F ∪ {v}, P.L ≤ (fun b => if b ∈ ({v} : Finset (GBranch LG.garden.tree)) then M₂ else M b) b := by
    intro b hb
    by_cases hbv : b ∈ ({v} : Finset (GBranch LG.garden.tree))
    · simp only [if_pos hbv]; exact hM₂
    · simp only [if_neg hbv]
      exact hM b ((Finset.mem_union.1 hb).resolve_right hbv)
  -- the unpinned kernel
  have hfixN : ∀ up : ℝ, ((if false = true then ProtCfg.term else ProtCfg.none).fix X s s up :
      GBranch LG.garden.tree → Option ℝ) = fun _ => none := fun up => funext fun b => by
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact protCfg_none_fix X s s up b
  set FA : (Fin 2 → ℝ) → Mom P.d → ℂ := fun ts k => kernelProt P.L P.γ P.δ LG H mB (fun _ => ts 0) (ts 1)
    (fun _ => none) k (fun _ => 0) 0 with hFA
  have hfun : ∀ (ts : Fin 2 → ℝ) (k : Mom P.d), kernelProt P.L P.γ P.δ LG H mA (fun _ => ts 0) (ts 1)
      ((if false = true then ProtCfg.term else ProtCfg.none).fix X s s (ts 0)) k (fun _ => 0) 0 = FA ts k := by
    intro ts k
    rw [hfixN, hmAB]
  rw [ProtPin.XNormRestr_congr (fun ts _ k _ => hfun ts k)]
  obtain ⟨hlone, -⟩ := protShape_lone hsh s 0
  have hcont : ∀ k : Mom P.d, Continuous fun ts => FA ts k := fun k =>
    continuous_kernelProt_joint P.L P.γ P.δ LG H mB _ hmB_bd (fun _ => none) k hlone
      (hHB.summable_coset hd1 hL1 k)
  have hport : ∀ k : Mom P.d, q' < p → ∀ ts ∈ timeBoxGt (p : ℝ) q', FA ts k = FA ![ts 0, (p : ℝ)] k := by
    intro k hlt ts hts
    obtain ⟨⟨-, ⟨-, h4⟩⟩, -⟩ := hts
    have hpq : (q' : ℝ) + 1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt hlt
    have e0 : (![ts 0, (p : ℝ)] : Fin 2 → ℝ) 0 = ts 0 := rfl
    have e1 : (![ts 0, (p : ℝ)] : Fin 2 → ℝ) 1 = p := rfl
    simp only [hFA, e0, e1]
    exact ProtPin.kernelProt_port_low P.L P.γ P.δ LG H mB (fun _ => ts 0) (fun _ => none) k (fun _ => 0) 0
      (q := p) (fun b hb _ => by rw [protShape_loneParent_layer hsh b hb]) (by linarith) le_rfl
  set Y : ℝ≥0∞ := (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n (protIncoh X LG) *
    ENNReal.ofReal (leafSizeProduct LG B) with hY
  -- the pointwise input (D6a)
  have hsup : ∀ k : Mom P.d, (⨆ ts : Fin 2 → ℝ, ‖FA ts k‖ₑ) ≤ Y * ENNReal.ofReal (P.L ^ 3 * M₂⁻¹) := by
    intro k
    refine iSup_le fun ts => ?_
    have key := hptw p hp n hn w LG X hsh hsz false {v} hpX hSel hcard M₂ hM₂ s S ω cω hω F M hM Fu Mu hMu ind
      hind hind1 H B hHB (ts 0) (ts 1) k
    rw [hfun ts k] at key
    refine key.trans (le_of_eq ?_)
    simp only [Finset.card_singleton, Bool.false_eq_true, ↓reduceIte, zero_add, mul_one, Nat.cast_one,
      Real.rpow_neg_one, hY]
    ring
  -- the X^{1/4} input (D5 + D3's flat gate)
  have hquart : ∀ k : Mom P.d, XNorm00Restr (1 / 4) (timeBoxGt p q') {k} FA ≤
      Y * ENNReal.ofReal (P.L ^ (4 * (P.d : ℝ))) := by
    intro k
    refine (xnorm00_le_restr (1 / 4) (30 * P.d) 0 (timeBoxGt p q') (Set.mem_univ k) FA).trans ?_
    refine (hquar p hp n hn w LG X hsh hsz hamb q' hq' S ω cω hω (F ∪ {v})
      (fun b => decide (b ∈ ({v} : Finset (GBranch LG.garden.tree))))
      (fun b => if b ∈ ({v} : Finset (GBranch LG.garden.tree)) then M₂ else M b) hM' Fu Mu hMu H B hHB).trans
      (le_of_eq ?_)
    rw [hY]
    ring
  -- per output: the fold
  have hk : ∀ k ∈ latticeBall P.L b₀ c₀, XNorm00Restr P.η (timeBoxGt p q') {k} FA ≤
      ENNReal.ofReal Cf * (Y * ENNReal.ofReal (P.L ^ 3 * M₂⁻¹)) ^ τ *
        (Y * ENNReal.ofReal (P.L ^ (4 * (P.d : ℝ)))) ^ (1 - τ) := by
    intro k _
    refine (hfold p q' hq' FA k (hcont k) (hport k)).trans ?_
    have ht0 : 0 ≤ τ := by rw [hτ]; linarith
    have ht1 : 0 ≤ 1 - τ := by rw [hτ]; linarith
    gcongr
    · exact hsup k
    · exact hquart k
  have hext := hloc P.L hL1 (timeBoxGt p q') b₀ c₀ FA _ hk
  refine hext.trans ?_
  have hτ1 : 1 / 18 ≤ τ := by rw [hτ]; linarith
  have hτ2 : τ ≤ 1 := by rw [hτ]; linarith
  have hfinal := annFree_alg (Y := Y) (d := P.d) hL1 hM₂1 hτ1 hτ2 hCloc0 hCf0 ((le_max_right _ _).trans hCL)
  refine hfinal.trans (le_of_eq ?_)
  simp only [hY, Finset.card_singleton, Bool.false_eq_true, ↓reduceIte, zero_add, mul_one, Nat.cast_one]
  ring_nf

/-! ### The gates -/

/-- **The unpinned selected case**, unconditionally (FILT-GATE, D3's flat gate, D6a's `protPtwGate`). -/
theorem annFreeGate : WTPrefix ProtAnnFreeSelAt := by
  have hall : WTPrefix (fun P => NoneAnnAt P ∧ ProtPtw.ProtPtwAt P) :=
    prefix_and noneAnnGate ProtPtw.protPtwGate noneAnnAt_mono protPtwAt_mono
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := hall d hd γ hγ
  refine ⟨min η₀ (1 / 16), lt_min hη₀ (by norm_num), fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨Cp, -, hCp⟩ := annFree_of d hη.1.le (hη.2.trans (min_le_right _ _))
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩ φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD htime
  refine ⟨C₂, hC₂, max L₀ Cp, le_max_of_le_left hL₀, fun L hL => ?_⟩
  obtain ⟨hq, hp⟩ := H4 L ((le_max_left _ _).trans hL)
  exact hCp _ rfl rfl (show 1 ≤ d by omega) ((le_max_right _ _).trans hL) hq hp

/-- **`ProtAnnBoundGate` from D3's `ProtBoundGate` alone** (ruling R183). -/
theorem protAnnBoundGate_of_D3 (hD3 : ProtBoundGate) : ProtAnnBoundGate :=
  protAnnBoundGate_of_free hD3 annFreeGate

end WaveTurbulence.Flower.ProtWhole
