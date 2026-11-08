/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.RT1TF

/-! # RT-GATE (ii), fork C: type 1, partner root in the layer of its window

D3's `tc_t1_move` (ProtPin/TChildB.lean; copy recorded in RT1T-COPIED.md) with the partner window `q' ≤ p` (the partner
root in layer `q'`): the partner root time `u ∈ (q', y)`, the kink at the window start (`tc_kink0` at `q'`), the
sub-couples at `(s, u)` on their mixed boxes (`tc_couple_mixed`, coherence `tc_t1_cohR`; traces `rt1t_piece_trace`),
any piece loss `c'`, and the root link (lost when `q' < p`) paid by `L` (`rt1t_rb_lost`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem rt_ite_le' (P : Prop) [Decidable P] : (if P then 0 else 1 : ℕ) ≤ 1 := by
  split <;> omega

/-- **The root trace of a type-1 side couple, both roots in layer `p`, one output.** -/
theorem rt1t_t1_move {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b)
      (_hFC : TcFC P) {c' : ℝ} (_hc' : 0 ≤ c') (_hC11 : 1 ≤ P.C₁) (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LGr LG₁ LG₂ LG₃ : LayeredGarden 2}
      (h : T1Data c Q₁ Q₂ Q₃ LGr.garden LG₁.garden LG₂.garden LG₃.garden)
      (_hlA : ∀ z, LG₁.layer z = LGr.layer (h.ιA z)) (_hlB : ∀ z, LG₂.layer z = LGr.layer (h.ιB z))
      (_hlC : ∀ z, LG₃.layer z = LGr.layer (h.ιC z))
      (_hwf : (RegCpl.type1 c Q₁ Q₂ Q₃).wf = true) (_hsz : (RegCpl.type1 c Q₁ Q₂ Q₃).size = 2 * n)
      (_hle : ∀ a, LGr.layer a ≤ p) {w' : ℕ} {Hm : LayeredGarden w'} {a b : Fin w' × TTree.Path}
      (_hcan : IsCanonGC (p + 1) Hm) (_hE : Embeds Hm.garden (RegCpl.type1 c Q₁ Q₂ Q₃) a b)
      (_hsa : nodeSign Hm.garden.sig a = 1) (_hsb : nodeSign Hm.garden.sig b = -1)
      (_hlay : ∀ z : GNode LGr.garden.tree, LGr.layer z = layerAt Hm (addrExt (if z.1.1 = 0 then a else b) z.1.2))
      (j : Fin 2) (_hj : layerAt LGr (j, []) = p) {q' : ℕ} (_hq'p : q' ≤ p)
      (_hpart : layerAt LGr (t1sw j, []) = q') {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
      (Hr : LeafProfiles 2 P.d) (Br : (Fin 2 × TTree.Path) → NNReal) (_hHr : LeafwiseControlled LGr Hr Br)
      (S : Finset (GNode LGr.garden.tree)) (ω : GNode LGr.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LGr.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LGr.garden.tree)) (M : GBranch LGr.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LGr.garden.tree)) (Mu : GBranch LGr.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (k : Mom P.d),
      rn θ (win (q' : ℝ)) (fun y => kernelProt P.L P.γ P.δ LGr Hr
          (gateM S ω F M Fu Mu) (fun b => if b.1.1 = j then s else y 0) 0 (trFix j s) k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 3 * rb P (n - 1) (LGr.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links)) *
            leafSizeProduct LGr Br * starCost S cω))) * tcWt P.L k := by
  obtain ⟨C₀, hC₀, hkink⟩ := tc_kink0 hθ0 (by linarith)
  set Tr := Regref.traceConst (r := 2) θ VineEstS3.chiUnit with hTr
  have hTrf : Tr < ⊤ := traceConst_lt_top θ
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨ENNReal.ofReal C₀ * (T4 * (Tr * (Tr * Tr))), ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top hT4f (ENNReal.mul_lt_top hTrf (ENNReal.mul_lt_top hTrf hTrf))), ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC c' hc' hC11 hθc p hp n hn c Q₁ Q₂ Q₃ LGr LG₁ LG₂ LG₃ h hlA hlB hlC hwf hsz hle w'
    Hm a b hcan hE hsa hsb hlay j hj q' hq'p hpart s hps hsp Hr Br hHr S ω cω hpres F M hM Fu Mu hMu k
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hrb : ∀ j g, 0 ≤ rb P j g := fun j g => rb_nonneg hC1 K.hδ hL0 j g
  obtain ⟨hw₁, hw₂, hw₃⟩ := tc_t1_wf hwf
  obtain ⟨n₁, n₂, n₃, hn₁, hn₂, hn₃, hnsum⟩ := tc_t1_sizes hsz
  obtain ⟨hH₁, hH₂, hH₃⟩ := tc_t1_leafwise h hHr
  have hle₁ : ∀ a, LG₁.layer a ≤ p := fun a => by rw [hlA]; exact hle _
  have hle₂ : ∀ a, LG₂.layer a ≤ p := fun a => by rw [hlB]; exact hle _
  have hle₃ : ∀ a, LG₃.layer a ≤ p := fun a => by rw [hlC]; exact hle _
  have hle_n : ∀ i, i ≤ n → i ≤ P.N (p + 1) ^ 4 := fun i hi => hi.trans hn
  obtain ⟨hc₁, hc₂, hc₃⟩ := tc_t1_cohR h hlA hlB hlC hwf hcan hE hsa hsb hlay
  have hq : ∀ t : Fin 2, layerAt LGr (t, []) ≤ p := fun t => by
    have hm : ([] : TTree.Path) ∈ (LGr.garden.tree t).nodes := TTree.nil_mem_nodes _
    rw [layerAt_node LGr (⟨(t, []), hm⟩ : GNode LGr.garden.tree)]
    exact hle _
  have hrA : ∀ t : Fin 2, LG₁.layer (GNode.root LG₁.garden.tree t) ≤ layerAt LGr (t, []) := fun t => by
    rw [hlA]; exact tc_child_le LGr hle _ t (slotA c t) rfl
  have hrB : ∀ t : Fin 2, LG₂.layer (GNode.root LG₂.garden.tree t) ≤ layerAt LGr (t1sw t, []) := fun t => by
    rw [hlB]; exact tc_child_le LGr hle _ (t1sw t) 1 rfl
  have hrC : ∀ t : Fin 2, LG₃.layer (GNode.root LG₃.garden.tree t) ≤ layerAt LGr (t, []) := fun t => by
    rw [hlC]; exact tc_child_le LGr hle _ t (slotC c t) rfl
  have e0 : t1sw (0 : Fin 2) = 1 := by decide
  have e1 : t1sw (1 : Fin 2) = 0 := by decide
  have hrB0 : LG₂.layer (GNode.root LG₂.garden.tree 0) ≤ layerAt LGr ((1 : Fin 2), []) := by
    have := hrB 0; rwa [e0] at this
  have hrB1 : LG₂.layer (GNode.root LG₂.garden.tree 1) ≤ layerAt LGr ((0 : Fin 2), []) := by
    have := hrB 1; rwa [e1] at this
  have hlay' : ∀ t : Fin 2, ((layerAt LGr (t, []) : ℕ) : ℝ) = t1Clock j (p : ℝ) (q' : ℝ) t := fun t => by
    by_cases ht : t = j
    · subst ht; simp [t1Clock, hj]
    · have ht' : t = t1sw j := by fin_cases t <;> fin_cases j <;> simp_all [t1sw]
      rw [show t1Clock j (p : ℝ) (q' : ℝ) t = q' by simp [t1Clock, ht], ht', hpart]
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
  -- the pieces
  set ζ : ℤˣ := LGr.garden.sig j with hζ
  set Bf : T1E P.d → ℝ := fun e => ((ζ : ℤ) : ℝ) * t1Freq P.L P.γ P.δ k e with hBf
  set f₁ : T1E P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG₁ (t1HA c Hr)
    (fun z => if z.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.1) (fun _ => 0) 0 m₁ with hf₁d
  set f₂ : T1E P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG₂ (t1HB Hr)
    (fun z => if z.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 m₂ with hf₂d
  set f₃ : T1E P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG₃ (t1HC c Hr)
    (fun z => if z.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0 m₃ with hf₃d
  have hf₁c : ∀ e, Continuous (fun x : Fin 2 → ℝ => f₁ e (x 0) (x 1)) := fun e =>
    FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₁ (t1HA c Hr) h.dec₁.1.1 m₁ B₁ hm₁B _
      (summable_coset_piece hH₁ hL1 _)
  have hf₂c : ∀ e, Continuous (fun x : Fin 2 → ℝ => f₂ e (x 0) (x 1)) := fun e =>
    FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₂ (t1HB Hr) h.dec₂.1.1 m₂ B₂ hm₂B _
      (summable_coset_piece hH₂ hL1 _)
  have hf₃c : ∀ e, Continuous (fun x : Fin 2 → ℝ => f₃ e (x 0) (x 1)) := fun e =>
    FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₃ (t1HC c Hr) h.dec₃.1.1 m₃ B₃ hm₃B _
      (summable_coset_piece hH₃ hL1 _)
  set g₁ : T1E P.d → (Fin 2 → ℝ) → ℂ := fun e x => f₁ e (tcOr j s (x 1) 0) (tcOr j s (x 1) 1) with hg₁
  set g₂ : T1E P.d → (Fin 2 → ℝ) → ℂ := fun e x => f₂ e (tcOrB j s (x 1) 0) (tcOrB j s (x 1) 1) with hg₂
  set g₃ : T1E P.d → (Fin 2 → ℝ) → ℂ := fun e x => f₃ e (tcOr j s (x 1) 0) (tcOr j s (x 1) 1) with hg₃
  set hh : T1E P.d → (Fin 2 → ℝ) → ℂ := fun e x => g₁ e x * (g₂ e x * g₃ e x) with hhh
  have hgc : ∀ (f : ℝ → ℝ → ℂ) (o : ℝ → ℝ → Fin 2 → ℝ),
      ((∀ u v, o u v 0 = u ∧ o u v 1 = v) ∨ (∀ u v, o u v 0 = v ∧ o u v 1 = u)) →
      Continuous (fun x : Fin 2 → ℝ => f (x 0) (x 1)) →
      Continuous (fun x : Fin 2 → ℝ => f (o s (x 1) 0) (o s (x 1) 1)) := by
    intro f o ho hf
    have := tc_oriented_cont o ho hf
    exact this.comp (show Continuous fun x : Fin 2 → ℝ => ![s, x 1] by fun_prop)
  have hg₁c : ∀ e, Continuous (g₁ e) := fun e => hgc _ _ (tcOr_cases j) (hf₁c e)
  have hg₂c : ∀ e, Continuous (g₂ e) := fun e => hgc _ _ (tcOrB_cases j) (hf₂c e)
  have hg₃c : ∀ e, Continuous (g₃ e) := fun e => hgc _ _ (tcOr_cases j) (hf₃c e)
  have hhc : ∀ e, Continuous (hh e) := fun e => (hg₁c e).mul ((hg₂c e).mul (hg₃c e))
  -- the gate bounds of the pieces
  set b₁ : ℝ := P.L ^ c' * rb P n₁ (LG₁.incoherency Q₁.links) * leafSizeProduct LG₁ (tcBA c Br) *
    starCost (pullS h.ιA S) (fun z => cω (h.ιA z)) with hb₁
  set b₂ : ℝ := P.L ^ c' * rb P n₂ (LG₂.incoherency Q₂.links) * leafSizeProduct LG₂ (tcBB Br) *
    starCost (pullS h.ιB S) (fun z => cω (h.ιB z)) with hb₂
  set b₃ : ℝ := P.L ^ c' * rb P n₃ (LG₃.incoherency Q₃.links) * leafSizeProduct LG₃ (tcBC c Br) *
    starCost (pullS h.ιC S) (fun z => cω (h.ιC z)) with hb₃
  set J : Mom P.d → ℝ := fun x => (jbr x ^ (30 * P.d))⁻¹ with hJ
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hp1 : ∀ e, rn θ (timeBox ((layerAt LGr ((0 : Fin 2), []) : ℕ) : ℝ) (layerAt LGr ((1 : Fin 2), []) : ℕ))
      (fun x => f₁ e (x 0) (x 1)) ≤
      ENNReal.ofReal b₁ * ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) := fun e => by
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₁, ← piece_conv hL0 hrb _ _ c' n₁ _ _]
    exact tc_couple_mixed K hFC hp (hle_n n₁ (by omega)) hθc Q₁ LG₁ hw₁ hn₁ h.dec₁ hle₁ (hq 0) (hq 1)
      (hrA 0) (hrA 1) hc₁ _ _ _ hG₁ _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hH₁ _
  have hp2 : ∀ e, rn θ (timeBox ((layerAt LGr ((1 : Fin 2), []) : ℕ) : ℝ) (layerAt LGr ((0 : Fin 2), []) : ℕ))
      (fun x => f₂ e (x 0) (x 1)) ≤
      ENNReal.ofReal b₂ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) := fun e => by
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₂, ← piece_conv hL0 hrb _ _ c' n₂ _ _]
    exact tc_couple_mixed K hFC hp (hle_n n₂ (by omega)) hθc Q₂ LG₂ hw₂ hn₂ h.dec₂ hle₂ (hq 1) (hq 0)
      hrB0 hrB1 hc₂ _ _ _ hG₂ _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hH₂ _
  have hp3 : ∀ e, rn θ (timeBox ((layerAt LGr ((0 : Fin 2), []) : ℕ) : ℝ) (layerAt LGr ((1 : Fin 2), []) : ℕ))
      (fun x => f₃ e (x 0) (x 1)) ≤
      ENNReal.ofReal b₃ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2)) := fun e => by
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₃, ← piece_conv hL0 hrb _ _ c' n₃ _ _]
    exact tc_couple_mixed K hFC hp (hle_n n₃ (by omega)) hθc Q₃ LG₃ hw₃ hn₃ h.dec₃ hle₃ (hq 0) (hq 1)
      (hrC 0) (hrC 1) hc₃ _ _ _ hG₃ _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hH₃ _
  have hps' : (p : ℝ) ≤ s := hps.le
  have hsp' : s ≤ (p : ℝ) + 1 := hsp.le
  have ht1 : ∀ e, rn θ (triS (q' : ℝ) q') (g₁ e) ≤ Tr * (ENNReal.ofReal b₁ * ENNReal.ofReal (J (k + latticePoint P.L e.1.1))) :=
    fun e => (rt1t_piece_trace hθ0 (q := (q' : ℝ)) hps' hsp' (f₁ e) (tcOr j) (tcOr_cases j) (hf₁c e)).trans
      (mul_le_mul' le_rfl (by rw [show tcOr j (p : ℝ) (q' : ℝ) 0 = _ from (hlay' 0).symm,
        show tcOr j (p : ℝ) (q' : ℝ) 1 = _ from (hlay' 1).symm]; exact hp1 e))
  have ht2 : ∀ e, rn θ (triS (q' : ℝ) q') (g₂ e) ≤ Tr * (ENNReal.ofReal b₂ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1))) :=
    fun e => (rt1t_piece_trace hθ0 (q := (q' : ℝ)) hps' hsp' (f₂ e) (tcOrB j) (tcOrB_cases j) (hf₂c e)).trans
      (mul_le_mul' le_rfl (by rw [show tcOrB j (p : ℝ) (q' : ℝ) 0 = _ from (e0 ▸ (hlay' 1)).symm,
        show tcOrB j (p : ℝ) (q' : ℝ) 1 = _ from (e1 ▸ (hlay' 0)).symm]; exact hp2 e))
  have ht3 : ∀ e, rn θ (triS (q' : ℝ) q') (g₃ e) ≤ Tr * (ENNReal.ofReal b₃ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2))) :=
    fun e => (rt1t_piece_trace hθ0 (q := (q' : ℝ)) hps' hsp' (f₃ e) (tcOr j) (tcOr_cases j) (hf₃c e)).trans
      (mul_le_mul' le_rfl (by rw [show tcOr j (p : ℝ) (q' : ℝ) 0 = _ from (hlay' 0).symm,
        show tcOr j (p : ℝ) (q' : ℝ) 1 = _ from (hlay' 1).symm]; exact hp3 e))
  have hfin : ∀ x : ℝ≥0∞, ∀ a b : ℝ, x * (ENNReal.ofReal a * ENNReal.ofReal b) < ⊤ → True := fun _ _ _ _ => trivial
  have hf1 : ∀ e, rn θ (triS (q' : ℝ) q') (g₁ e) < ⊤ := fun e => (ht1 e).trans_lt
    (ENNReal.mul_lt_top hTrf (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))
  have hf2 : ∀ e, rn θ (triS (q' : ℝ) q') (g₂ e) < ⊤ := fun e => (ht2 e).trans_lt
    (ENNReal.mul_lt_top hTrf (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))
  have hf3 : ∀ e, rn θ (triS (q' : ℝ) q') (g₃ e) < ⊤ := fun e => (ht3 e).trans_lt
    (ENNReal.mul_lt_top hTrf (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))
  have h23 : ∀ e, rn θ (triS (q' : ℝ) q') (fun x => g₂ e x * g₃ e x) ≤
      ENNReal.ofReal (2 ^ θ) * rn θ (triS (q' : ℝ) q') (g₂ e) * rn θ (triS (q' : ℝ) q') (g₃ e) := fun e =>
    rn_mul_le hθ0 (triS_closure q' q') (g₂ e) (g₃ e) (hg₃c e) (hf2 e) (hf3 e)
  have hf23 : ∀ e, rn θ (triS (q' : ℝ) q') (fun x => g₂ e x * g₃ e x) < ⊤ := fun e =>
    (h23 e).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hf2 e)) (hf3 e))
  have hhb : ∀ e, rn θ (triS (q' : ℝ) q') (hh e) ≤ T4 * (Tr * (Tr * Tr)) *
      (ENNReal.ofReal b₁ * ENNReal.ofReal b₂ * ENNReal.ofReal b₃) *
        (ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) *
          ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2))) := fun e => by
    refine (rn_mul_le hθ0 (triS_closure q' q') (g₁ e) (fun x => g₂ e x * g₃ e x) ((hg₂c e).mul (hg₃c e))
      (hf1 e) (hf23 e)).trans ?_
    calc ENNReal.ofReal (2 ^ θ) * rn θ (triS (q' : ℝ) q') (g₁ e) * rn θ (triS (q' : ℝ) q') (fun x => g₂ e x * g₃ e x)
        ≤ ENNReal.ofReal (2 ^ θ) * (Tr * (ENNReal.ofReal b₁ * ENNReal.ofReal (J (k + latticePoint P.L e.1.1)))) *
          (ENNReal.ofReal (2 ^ θ) * (Tr * (ENNReal.ofReal b₂ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)))) *
            (Tr * (ENNReal.ofReal b₃ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2))))) :=
          mul_le_mul' (mul_le_mul' le_rfl (ht1 e)) ((h23 e).trans (mul_le_mul' (mul_le_mul' le_rfl (ht2 e)) (ht3 e)))
      _ = _ := by rw [hT4]; ring
  have hhfin : ∀ e, rn θ (triS (q' : ℝ) q') (hh e) < ⊤ := fun e => (hhb e).trans_lt (by
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top hT4f (ENNReal.mul_lt_top hTrf
      (ENNReal.mul_lt_top hTrf hTrf))) ?_) ?_ <;>
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top)
  -- the coefficients and the identity on the window
  set cc : ℂ := (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 with hcc
  set a : T1E P.d → ℂ := fun e => cc * ((fD3' S ω F (fun _ => false) M Fu Mu (h.rt 0) (t1Star c P.L k e 0) *
    fD3' S ω F (fun _ => false) M Fu Mu (h.rt 1) (t1Star c P.L k e 1)) * (t1Eps c e : ℂ) *
      Complex.exp (((Real.pi * Bf e * (s - q') : ℝ) : ℂ) * Complex.I)) with ha
  have hwin : ∀ y ∈ win (q' : ℝ), kernelProt P.L P.γ P.δ LGr Hr (gateM S ω F M Fu Mu)
      (fun b => if b.1.1 = j then s else y 0) 0 (trFix j s) k (fun _ => 0) 0 =
      ∑' e, a e * ∫ u in Ioo (q' : ℝ) (y 0), cutMod (-Bf e) q' u * hh e ![y 0, u] := by
    intro y hy
    set U : Fin 2 → ℝ := fun t => if t = j then s else y 0 with hU
    have hUj : U j = s := by simp [hU]
    have hUo : U (t1sw j) = y 0 := by simp [hU, t1sw_ne j]
    have hid := h.kernelProt_t1Trace P.L P.γ P.δ Hr hHs (gateM S ω F M Fu Mu) _ m₁ m₂ m₃ hMf CM
      (fun A B => (hMc A B).trans (le_max_left _ _))
      (fun κ => (hm₁B κ).trans ((le_max_left _ _).trans (le_max_right _ _)))
      (fun κ => (hm₂B κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
      (fun κ => (hm₃B κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
      U 0 j s hUj.symm.le hlA hlB hlC k
    have hl : layerAt LGr (t1sw j, []) = q' := hpart
    rw [hUo, tc_t1U_eq hl hy.2] at hid
    refine hid.trans ?_
    rw [← tsum_mul_left]
    refine tsum_congr fun e => ?_
    simp_rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_Ioo (a := (q' : ℝ)) (b := y 0)) fun u _ => ?_
    rw [tc_t1Ph_split ζ P.L P.γ P.δ k e s q' u]
    rw [cut_kernel_couple_m P.L P.γ P.δ LG₁ h.dec₁ (t1HA c Hr) m₁ (fun t => t1Clock j s u t),
      cut_kernel_couple_m P.L P.γ P.δ LG₂ h.dec₂ (t1HB Hr) m₂ (fun t => t1Clock j s u (t1sw t)),
      cut_kernel_couple_m P.L P.γ P.δ LG₃ h.dec₃ (t1HC c Hr) m₃ (fun t => t1Clock j s u t)]
    simp only [ha, hcc, hhh, hg₁, hg₂, hg₃, hf₁d, hf₂d, hf₃d, tcOr, tcOrB, hBf, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    ring
  rw [rn_congr θ hwin]
  refine (hkink (T1E P.d) q' q' le_rfl (by linarith) (fun e => -Bf e) a hh hhc hhfin).trans ?_
  -- the exceptional sum
  set c2 : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hc2
  have hc20 : 0 ≤ c2 := sq_nonneg _
  have hae : ∀ e, ‖a e‖ₑ ≤ ENNReal.ofReal (c2 * Ca) := fun e => by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [ha]
    simp only
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, hcc, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_left ((mul_le_mul (hMc _ _) (tc_abs_t1Eps_le c e) (abs_nonneg _) hCa0).trans
      (by rw [mul_one])) hc20
  set Z : ℝ≥0∞ := ENNReal.ofReal (c2 * Ca) * (T4 * (Tr * (Tr * Tr)) *
    (ENNReal.ofReal b₁ * ENNReal.ofReal b₂ * ENNReal.ofReal b₃)) with hZ
  have hterm : ∀ e, ‖a e‖ₑ * rn θ (triS (q' : ℝ) q') (hh e) ≤ Z * (ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) *
      ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2))) :=
    fun e => (mul_le_mul' (hae e) (hhb e)).trans (le_of_eq (by rw [hZ]; ring))
  have hsum : ∑' e, ‖a e‖ₑ * rn θ (triS (q' : ℝ) q') (hh e) ≤ Z * tcWt P.L k := by
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul' le_rfl le_self_add
  calc ENNReal.ofReal C₀ * ∑' e, ‖a e‖ₑ * rn θ (triS (q' : ℝ) q') (hh e)
      ≤ ENNReal.ofReal C₀ * (Z * tcWt P.L k) := mul_le_mul' le_rfl hsum
    _ ≤ _ := by
        -- the algebra
        set g₀ := LG₁.incoherency Q₁.links + LG₂.incoherency Q₂.links + LG₃.incoherency Q₃.links with hg₀
        have hgI := tc_t1_incoh h hlA hlB hlC
        have hgle : g₀ ≤ LGr.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links := by rw [hgI]; omega
        have hgle' : LGr.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links ≤ g₀ + 1 := by
          rw [hgI]; have := rt_ite_le' (layerAt LGr ((0 : Fin 2), []) = layerAt LGr ((1 : Fin 2), [])); omega
        have hlost := rt1t_rb_lost hL1 hC1 K.hδ K.hη0 (n - 1) hgle hgle'
        have hn1 : n₁ + n₂ + n₃ = n - 1 := by omega
        have hleaf := tc_t1_leafSize h Br
        have hcost := tc_t1_cost h S cω
        have hb0 : ∀ {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal),
            0 ≤ leafSizeProduct LGx Bx := fun LGx Bx => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
        have hb10 : 0 ≤ b₁ :=
          mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hL0 _) (hrb _ _)) (hb0 _ _)) (starCost_nonneg' _ _)
        have hb20 : 0 ≤ b₂ :=
          mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hL0 _) (hrb _ _)) (hb0 _ _)) (starCost_nonneg' _ _)
        have hb30 : 0 ≤ b₃ :=
          mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hL0 _) (hrb _ _)) (hb0 _ _)) (starCost_nonneg' _ _)
        have hval : c2 * Ca * (b₁ * b₂ * b₃) = P.L ^ (3 * c') * (coupling P.d P.L P.γ P.δ ^ 2 *
            (P.C₁ ^ 2 * rb P (n - 1) g₀) * leafSizeProduct LGr Br * starCost S cω) := by
          rw [hb₁, hb₂, hb₃, ← hn1, hleaf, hcost, hc2, ← rt1t_rpow3 (by linarith : (0 : ℝ) < P.L) c']
          have h3 := rb_three (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := n₁) (n₂ := n₂) (n₃ := n₃)
            (g₁ := LG₁.incoherency Q₁.links) (g₂ := LG₂.incoherency Q₂.links) (g₃ := LG₃.incoherency Q₃.links)
          rw [← h3, hCa]
          ring
        have hY : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 * P.C₁ ^ 2 * leafSizeProduct LGr Br * starCost S cω := by
          have := starCost_nonneg' S cω
          have := hb0 LGr Br
          positivity
        have hfin : P.L ^ (3 * c') * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) g₀) *
            leafSizeProduct LGr Br * starCost S cω) ≤ P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
              (P.C₁ ^ 3 * rb P (n - 1) (LGr.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links)) *
                leafSizeProduct LGr Br * starCost S cω)) := by
          refine le_trans ?_ (rt1t_rhs hL1 hC11 K.hδ hc' (a := 2) (by norm_num) (n - 1) _ (hb0 LGr Br)
            (starCost_nonneg' S cω))
          have h3 : 0 ≤ P.L ^ (3 * c') := Real.rpow_nonneg hL0 _
          calc P.L ^ (3 * c') * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) g₀) *
                leafSizeProduct LGr Br * starCost S cω)
              = P.L ^ (3 * c') * ((coupling P.d P.L P.γ P.δ ^ 2 * P.C₁ ^ 2 * leafSizeProduct LGr Br *
                  starCost S cω) * rb P (n - 1) g₀) := by ring
            _ ≤ P.L ^ (3 * c') * ((coupling P.d P.L P.γ P.δ ^ 2 * P.C₁ ^ 2 * leafSizeProduct LGr Br *
                  starCost S cω) * (P.L * rb P (n - 1) (LGr.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlost hY) h3
            _ = _ := by ring
        rw [hZ, ← ENNReal.ofReal_mul hb10, ← ENNReal.ofReal_mul (mul_nonneg hb10 hb20)]
        calc ENNReal.ofReal C₀ * (ENNReal.ofReal (c2 * Ca) * (T4 * (Tr * (Tr * Tr)) * ENNReal.ofReal (b₁ * b₂ * b₃)) *
              tcWt P.L k)
            = ENNReal.ofReal C₀ * (T4 * (Tr * (Tr * Tr))) * ENNReal.ofReal (c2 * Ca * (b₁ * b₂ * b₃)) *
                tcWt P.L k := by
              rw [ENNReal.ofReal_mul (mul_nonneg hc20 hCa0)]; ring
          _ ≤ _ := by
              rw [hval]
              exact mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hfin)) le_rfl

end WaveTurbulence.Flower.ProtRT
