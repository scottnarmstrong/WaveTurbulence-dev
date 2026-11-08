/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.RT2T1
public import WaveTurbulence.Foundations.Flower.ProtRT.RT2Aux
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildFix

/-! # RT-GATE (ii), both roots pinned: a type-1 couple, pointwise

Both mini-couple roots (layer `p`) pinned at `s`: by `rt2_kernelProt_t1`, `c² Σ'_{e ∈ T1E} Mc ε_e Q₁ Q₂ Q₃` at the clocks
`s`. The sub-couples are bounded pointwise by the gates (`tc_couple_pt`, coherence in the ambient `tc_t1_coh`), the
exceptional sum by `tcWt`, and the root link is coherent (both roots in layer `p`): `c² C₁² rb(n−1, g)`. Model: D3's
`tc_t1_fix` (ProtPin/TChildFix.lean; copy recorded in RT2-COPIED.md) without the partner integral. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **A type-1 couple with both roots pinned at `s`**, pointwise. -/
theorem rt2_t1_both {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b)
      (_hFC : TcFC P) (_hθc : PieceLoss P θ 0) {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LGr LG₁ LG₂ LG₃ : LayeredGarden 2}
      (h : T1Data c Q₁ Q₂ Q₃ LGr.garden LG₁.garden LG₂.garden LG₃.garden)
      (_hlA : ∀ z, LG₁.layer z = LGr.layer (h.ιA z)) (_hlB : ∀ z, LG₂.layer z = LGr.layer (h.ιB z))
      (_hlC : ∀ z, LG₃.layer z = LGr.layer (h.ιC z))
      (_hwf : (RegCpl.type1 c Q₁ Q₂ Q₃).wf = true) (_hsz : (RegCpl.type1 c Q₁ Q₂ Q₃).size = 2 * n)
      (_hle : ∀ a, LGr.layer a ≤ p) (_hA : TcCplAmbS p (RegCpl.type1 c Q₁ Q₂ Q₃) LGr)
      (_hj : ∀ t : Fin 2, layerAt LGr (t, []) = p)
      {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
      (Hr : LeafProfiles 2 P.d) (Br : (Fin 2 × TTree.Path) → NNReal) (_hHr : LeafwiseControlled LGr Hr Br)
      (S : Finset (GNode LGr.garden.tree)) (ω : GNode LGr.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LGr.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LGr.garden.tree)) (M : GBranch LGr.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LGr.garden.tree)) (Mu : GBranch LGr.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (k : Mom P.d),
      ‖kernelProt P.L P.γ P.δ LGr Hr (gateM S ω F M Fu Mu) (fun _ => s) 0 (MkSlotsO.rootPins (fun _ => True) s) k
          (fun _ => 0) 0‖ₑ ≤
        ENNReal.ofReal (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 2 * rb P (n - 1) (LGr.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links)) *
            leafSizeProduct LGr Br * starCost S cω) * tcWt P.L k := by
  intro P C₁a C₂a C₁b C₂b K hFC hθc p hp n hn c Q₁ Q₂ Q₃ LGr LG₁ LG₂ LG₃ h hlA hlB hlC hwf hsz hle hA hj
    s hps hsp Hr Br hHr S ω cω hpres F M hM Fu Mu hMu k
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hrb : ∀ j g, 0 ≤ rb P j g := fun j g => rb_nonneg hC1 K.hδ hL0 j g
  obtain ⟨hw₁, hw₂, hw₃⟩ := tc_t1_wf hwf
  obtain ⟨n₁, n₂, n₃, hn₁, hn₂, hn₃, hnsum⟩ := tc_t1_sizes hsz
  obtain ⟨hH₁, hH₂, hH₃⟩ := tc_t1_leafwise h hHr
  obtain ⟨hc₁, hc₂, hc₃⟩ := tc_t1_coh h hlA hlB hlC hwf hA
  have hle₁ : ∀ a, LG₁.layer a ≤ p := fun a => by rw [hlA]; exact hle _
  have hle₂ : ∀ a, LG₂.layer a ≤ p := fun a => by rw [hlB]; exact hle _
  have hle₃ : ∀ a, LG₃.layer a ≤ p := fun a => by rw [hlC]; exact hle _
  have hle_n : ∀ i, i ≤ n → i ≤ P.N (p + 1) ^ 4 := fun i hi => hi.trans hn
  have hq : ∀ t : Fin 2, layerAt LGr (t, []) ≤ p := fun t => (hj t).le
  have hrA : ∀ t : Fin 2, LG₁.layer (GNode.root LG₁.garden.tree t) ≤ layerAt LGr (t, []) := fun t => by
    rw [hlA]; exact tc_child_le LGr hle _ t (slotA c t) rfl
  have hrB : ∀ t : Fin 2, LG₂.layer (GNode.root LG₂.garden.tree t) ≤ layerAt LGr (t1sw t, []) := fun t => by
    rw [hlB]; exact tc_child_le LGr hle _ (t1sw t) 1 rfl
  have hrC : ∀ t : Fin 2, LG₃.layer (GNode.root LG₃.garden.tree t) ≤ layerAt LGr (t, []) := fun t => by
    rw [hlC]; exact tc_child_le LGr hle _ t (slotC c t) rfl
  -- the multiplier
  have hMf := tc_t1_mult h S ω F M Fu Mu
  set m₁ := pullMult h.ιA h.βA S ω F M Fu Mu with hm₁
  set m₂ := pullMult h.ιB h.βB S ω F M Fu Mu with hm₂
  set m₃ := pullMult h.ιC h.βC S ω F M Fu Mu with hm₃
  have hG₁ := pull_pres (J := 30 * P.d) h.ιA hpres
  have hG₂ := pull_pres (J := 30 * P.d) h.ιB hpres
  have hG₃ := pull_pres (J := 30 * P.d) h.ιC hpres
  have hm₁B := FiltCoh.norm_d5Mult_le (pullS h.ιA S) (fun z => ω (h.ιA z)) (fun z => cω (h.ιA z)) hG₁
    (pullF h.βA F) (fun _ => false) (fun y => M (h.βA y)) (pullF h.βA Fu) (fun y => Mu (h.βA y))
  have hm₂B := FiltCoh.norm_d5Mult_le (pullS h.ιB S) (fun z => ω (h.ιB z)) (fun z => cω (h.ιB z)) hG₂
    (pullF h.βB F) (fun _ => false) (fun y => M (h.βB y)) (pullF h.βB Fu) (fun y => Mu (h.βB y))
  have hm₃B := FiltCoh.norm_d5Mult_le (pullS h.ιC S) (fun z => ω (h.ιC z)) (fun z => cω (h.ιC z)) hG₃
    (pullF h.βC F) (fun _ => false) (fun y => M (h.βC y)) (pullF h.βC Fu) (fun y => Mu (h.βC y))
  set Ca : ℝ := costB S cω (h.rt 0) * costB S cω (h.rt 1) with hCa
  have hCa0 : 0 ≤ Ca := mul_nonneg (costB_nonneg _ _ _) (costB_nonneg _ _ _)
  have hMc : ∀ A B : Fin 4 → Mom P.d, ‖fD3' S ω F (fun _ => false) M Fu Mu (h.rt 0) A *
      fD3' S ω F (fun _ => false) M Fu Mu (h.rt 1) B‖ ≤ Ca := fun A B => by
    rw [norm_mul]
    exact mul_le_mul (norm_fD3'_le S ω cω hpres F M Fu Mu _ _) (norm_fD3'_le S ω cω hpres F M Fu Mu _ _)
      (norm_nonneg _) (costB_nonneg _ _ _)
  set B₁ : ℝ := (∏ a ∈ pullS h.ιA S, max (cω (h.ιA a)) 0) * FiltCoh.chiDSup ^ (pullF h.βA F).card *
    FiltCoh.chiDSup ^ (pullF h.βA Fu).card with hB₁
  set B₂ : ℝ := (∏ a ∈ pullS h.ιB S, max (cω (h.ιB a)) 0) * FiltCoh.chiDSup ^ (pullF h.βB F).card *
    FiltCoh.chiDSup ^ (pullF h.βB Fu).card with hB₂
  set B₃ : ℝ := (∏ a ∈ pullS h.ιC S, max (cω (h.ιC a)) 0) * FiltCoh.chiDSup ^ (pullF h.βC F).card *
    FiltCoh.chiDSup ^ (pullF h.βC Fu).card with hB₃
  set CM : ℝ := max Ca (max B₁ (max B₂ B₃)) with hCM
  have hHs : ∀ ℓ ∈ inputLeaves LGr.garden, ∀ k' : Mom P.d,
      Summable fun i : Fin P.d → ℤ => |Hr ℓ.1 (k' + latticePoint P.L i)| :=
    fun ℓ hℓ k' => summable_coset_piece hHr hL1 k' ℓ hℓ
  -- the identity
  have hid := T1B.rt2_kernelProt_t1 h P.L P.γ P.δ Hr hHs (gateM S ω F M Fu Mu) _ m₁ m₂ m₃ hMf CM
    (fun A B => (hMc A B).trans (le_max_left _ _))
    (fun κ => (hm₁B κ).trans ((le_max_left _ _).trans (le_max_right _ _)))
    (fun κ => (hm₂B κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    (fun κ => (hm₃B κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    0 s hlA hlB hlC k
  rw [hid]
  -- the pointwise bounds of the sub-couples at the clocks `s`
  set b₁ : ℝ := P.L ^ (0 : ℝ) * rb P n₁ (LG₁.incoherency Q₁.links) * leafSizeProduct LG₁ (tcBA c Br) *
    starCost (pullS h.ιA S) (fun z => cω (h.ιA z)) with hb₁
  set b₂ : ℝ := P.L ^ (0 : ℝ) * rb P n₂ (LG₂.incoherency Q₂.links) * leafSizeProduct LG₂ (tcBB Br) *
    starCost (pullS h.ιB S) (fun z => cω (h.ιB z)) with hb₂
  set b₃ : ℝ := P.L ^ (0 : ℝ) * rb P n₃ (LG₃.incoherency Q₃.links) * leafSizeProduct LG₃ (tcBC c Br) *
    starCost (pullS h.ιC S) (fun z => cω (h.ιC z)) with hb₃
  set J : Mom P.d → ℝ := fun x => (jbr x ^ (30 * P.d))⁻¹ with hJ
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hsI : s ∈ Icc (p : ℝ) (p + 1) := ⟨hps.le, hsp.le⟩
  have hclk : ∀ t : Fin 2, (fun _ : Fin 2 => s) t ∈ Icc (layerAt LGr (t, []) : ℝ) (layerAt LGr (t, []) + 1) :=
    fun t => by rw [hj t]; exact hsI
  have e1 : ∀ {LGx : LayeredGarden 2}, (fun _ : GBranch LGx.garden.tree => s) = fun y => (fun _ : Fin 2 => s) y.1.1 :=
    fun {_} => rfl
  have hKA : ∀ e : T1E P.d,
      ‖kernelProt P.L P.γ P.δ LG₁ (t1HA c Hr) m₁ (fun _ => s) 0 (fun _ => none)
        (k + latticePoint P.L e.1.1) (fun _ => 0) 0‖ₑ ≤
        ENNReal.ofReal b₁ * ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) := fun e => by
    rw [e1, cut_kernel_couple_m P.L P.γ P.δ LG₁ h.dec₁ (t1HA c Hr) m₁ (fun _ => s)]
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₁, ← piece_conv hL0 hrb _ _ 0 n₁ _ _]
    exact tc_couple_pt K hFC hp (hle_n n₁ (by omega)) hθc Q₁ LG₁ hw₁ hn₁ h.dec₁ hle₁ (hq 0) (hq 1)
      (hrA 0) (hrA 1) hc₁ _ _ _ hG₁ _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hH₁ _
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₁ (t1HA c Hr) h.dec₁.1.1 m₁ B₁ hm₁B _
        (summable_coset_piece hH₁ hL1 _)) (x := fun _ => s) ⟨hclk 0, hclk 1⟩
  have e0 : t1sw (0 : Fin 2) = 1 := by decide
  have e1' : t1sw (1 : Fin 2) = 0 := by decide
  have hrB0 : LG₂.layer (GNode.root LG₂.garden.tree 0) ≤ layerAt LGr ((1 : Fin 2), []) := by
    have := hrB 0; rwa [e0] at this
  have hrB1 : LG₂.layer (GNode.root LG₂.garden.tree 1) ≤ layerAt LGr ((0 : Fin 2), []) := by
    have := hrB 1; rwa [e1'] at this
  have hKB : ∀ e : T1E P.d,
      ‖kernelProt P.L P.γ P.δ LG₂ (t1HB Hr) m₂ (fun _ => s) 0 (fun _ => none)
        (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0‖ₑ ≤
        ENNReal.ofReal b₂ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) := fun e => by
    rw [e1, cut_kernel_couple_m P.L P.γ P.δ LG₂ h.dec₂ (t1HB Hr) m₂ (fun _ => s)]
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₂, ← piece_conv hL0 hrb _ _ 0 n₂ _ _]
    exact tc_couple_pt K hFC hp (hle_n n₂ (by omega)) hθc Q₂ LG₂ hw₂ hn₂ h.dec₂ hle₂ (hq 1) (hq 0)
      hrB0 hrB1 hc₂ _ _ _ hG₂ _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hH₂ _
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₂ (t1HB Hr) h.dec₂.1.1 m₂ B₂ hm₂B _
        (summable_coset_piece hH₂ hL1 _)) (x := fun _ => s) ⟨hclk 1, hclk 0⟩
  have hKC : ∀ e : T1E P.d,
      ‖kernelProt P.L P.γ P.δ LG₃ (t1HC c Hr) m₃ (fun _ => s) 0 (fun _ => none)
        (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0‖ₑ ≤
        ENNReal.ofReal b₃ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2)) := fun e => by
    rw [e1, cut_kernel_couple_m P.L P.γ P.δ LG₃ h.dec₃ (t1HC c Hr) m₃ (fun _ => s)]
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₃, ← piece_conv hL0 hrb _ _ 0 n₃ _ _]
    exact tc_couple_pt K hFC hp (hle_n n₃ (by omega)) hθc Q₃ LG₃ hw₃ hn₃ h.dec₃ hle₃ (hq 0) (hq 1)
      (hrC 0) (hrC 1) hc₃ _ _ _ hG₃ _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hH₃ _
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₃ (t1HC c Hr) h.dec₃.1.1 m₃ B₃ hm₃B _
        (summable_coset_piece hH₃ hL1 _)) (x := fun _ => s) ⟨hclk 0, hclk 1⟩
  -- the modulus
  set c2 : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hc2
  have hc20 : 0 ≤ c2 := sq_nonneg _
  set Wb : ℝ≥0∞ := ENNReal.ofReal b₁ * ENNReal.ofReal b₂ * ENNReal.ofReal b₃ with hWb
  have hterm : ∀ e : T1E P.d,
      ‖(fD3' S ω F (fun _ => false) M Fu Mu (h.rt 0) (t1Star c P.L k e 0) *
          fD3' S ω F (fun _ => false) M Fu Mu (h.rt 1) (t1Star c P.L k e 1)) * (t1Eps c e : ℂ) *
        (kernelProt P.L P.γ P.δ LG₁ (t1HA c Hr) m₁ (fun _ => s) 0 (fun _ => none)
            (k + latticePoint P.L e.1.1) (fun _ => 0) 0 *
          (kernelProt P.L P.γ P.δ LG₂ (t1HB Hr) m₂ (fun _ => s) 0 (fun _ => none)
              (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 *
            kernelProt P.L P.γ P.δ LG₃ (t1HC c Hr) m₃ (fun _ => s) 0 (fun _ => none)
              (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0))‖ₑ ≤
        ENNReal.ofReal Ca * (Wb * (ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) *
          ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2)))) := by
    intro e
    rw [enorm_mul, enorm_mul]
    have hMe : ‖fD3' S ω F (fun _ => false) M Fu Mu (h.rt 0) (t1Star c P.L k e 0) *
        fD3' S ω F (fun _ => false) M Fu Mu (h.rt 1) (t1Star c P.L k e 1)‖ₑ ≤ ENNReal.ofReal Ca := by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hMc _ _)
    have hεe : ‖(t1Eps c e : ℂ)‖ₑ ≤ 1 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (tc_abs_t1Eps_le c e)
    have hpr : ‖kernelProt P.L P.γ P.δ LG₁ (t1HA c Hr) m₁ (fun _ => s) 0 (fun _ => none)
            (k + latticePoint P.L e.1.1) (fun _ => 0) 0 *
          (kernelProt P.L P.γ P.δ LG₂ (t1HB Hr) m₂ (fun _ => s) 0 (fun _ => none)
              (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 *
            kernelProt P.L P.γ P.δ LG₃ (t1HC c Hr) m₃ (fun _ => s) 0 (fun _ => none)
              (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0)‖ₑ ≤
        Wb * (ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) *
          ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2))) := by
      rw [enorm_mul, enorm_mul]
      calc _ ≤ (ENNReal.ofReal b₁ * ENNReal.ofReal (J (k + latticePoint P.L e.1.1))) *
            ((ENNReal.ofReal b₂ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1))) *
              (ENNReal.ofReal b₃ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2)))) :=
            mul_le_mul' (hKA e) (mul_le_mul' (hKB e) (hKC e))
        _ = _ := by rw [hWb]; ring
    calc _ ≤ ENNReal.ofReal Ca * 1 * _ := mul_le_mul' (mul_le_mul' hMe hεe) hpr
      _ = _ := by rw [mul_one]
  have hmod : ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' e : T1E P.d,
        (fD3' S ω F (fun _ => false) M Fu Mu (h.rt 0) (t1Star c P.L k e 0) *
          fD3' S ω F (fun _ => false) M Fu Mu (h.rt 1) (t1Star c P.L k e 1)) * (t1Eps c e : ℂ) *
        (kernelProt P.L P.γ P.δ LG₁ (t1HA c Hr) m₁ (fun _ => s) 0 (fun _ => none)
            (k + latticePoint P.L e.1.1) (fun _ => 0) 0 *
          (kernelProt P.L P.γ P.δ LG₂ (t1HB Hr) m₂ (fun _ => s) 0 (fun _ => none)
              (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 *
            kernelProt P.L P.γ P.δ LG₃ (t1HC c Hr) m₃ (fun _ => s) 0 (fun _ => none)
              (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0))‖ₑ ≤
      ENNReal.ofReal (c2 * Ca) * Wb * tcWt P.L k := by
    rw [enorm_mul]
    have hcc : ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ 2‖ₑ = ENNReal.ofReal c2 := by
      rw [← ofReal_norm, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hcc]
    refine (mul_le_mul' le_rfl (enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum hterm))).trans ?_
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.ofReal_mul hc20]
    calc ENNReal.ofReal c2 * (ENNReal.ofReal Ca * (Wb * ∑' e : T1E P.d,
          ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) *
            ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2))))
        ≤ ENNReal.ofReal c2 * (ENNReal.ofReal Ca * (Wb * tcWt P.L k)) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl le_self_add))
      _ = _ := by ring
  refine hmod.trans (le_of_eq ?_)
  -- the algebra (the root link is coherent)
  have hg : LGr.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links =
      LG₁.incoherency Q₁.links + LG₂.incoherency Q₂.links + LG₃.incoherency Q₃.links := by
    rw [tc_t1_incoh h hlA hlB hlC, if_pos ((hj 0).trans (hj 1).symm), add_zero]
  have hn1 : n₁ + n₂ + n₃ = n - 1 := by omega
  have hleaf := tc_t1_leafSize h Br
  have hcost := tc_t1_cost h S cω
  have hb0 : ∀ {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal),
      0 ≤ leafSizeProduct LGx Bx := fun LGx Bx => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hb10 : 0 ≤ b₁ := by
    rw [hb₁, Real.rpow_zero, one_mul]
    exact mul_nonneg (mul_nonneg (hrb _ _) (hb0 _ _)) (starCost_nonneg' _ _)
  have hb20 : 0 ≤ b₂ := by
    rw [hb₂, Real.rpow_zero, one_mul]
    exact mul_nonneg (mul_nonneg (hrb _ _) (hb0 _ _)) (starCost_nonneg' _ _)
  have hb30 : 0 ≤ b₃ := by
    rw [hb₃, Real.rpow_zero, one_mul]
    exact mul_nonneg (mul_nonneg (hrb _ _) (hb0 _ _)) (starCost_nonneg' _ _)
  have hval : c2 * Ca * (b₁ * b₂ * b₃) =
      coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) (LGr.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links)) *
        leafSizeProduct LGr Br * starCost S cω := by
    rw [hb₁, hb₂, hb₃, Real.rpow_zero, hg, ← hn1, hleaf, hcost, hc2]
    have h3 := rb_three (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := n₁) (n₂ := n₂) (n₃ := n₃)
      (g₁ := LG₁.incoherency Q₁.links) (g₂ := LG₂.incoherency Q₂.links) (g₃ := LG₃.incoherency Q₃.links)
    rw [← h3, hCa]
    ring
  rw [hWb, ← ENNReal.ofReal_mul hb10, ← ENNReal.ofReal_mul (mul_nonneg hb10 hb20),
    ← ENNReal.ofReal_mul (mul_nonneg hc20 hCa0), hval]

end WaveTurbulence.Flower.ProtRT
