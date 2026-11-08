/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermTree
public import WaveTurbulence.Foundations.Flower.ProtPin.CutFlat

/-! # D3 PROT-PIN: `term`, one output: assembly of the cut, the core estimate and the gates -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem abs_epsCoef_le {d : ℕ} (a b c : Fin d → ℤ) : |epsCoef a b c| ≤ 1 := by
  unfold epsCoef; split_ifs <;> norm_num

theorem abs_cutEps_le {d : ℕ} (m : MiniTreeCode) (e : PairE m d) : |cutEps m e| ≤ 1 := by
  unfold cutEps
  rw [abs_mul]
  exact mul_le_one₀ (abs_epsCoef_le _ _ _) (abs_nonneg _) (abs_epsCoef_le _ _ _)

theorem norm_I_mul_unit (u : ℤˣ) : ‖Complex.I * (((u : ℤ) : ℂ))‖ = 1 := by
  rw [norm_mul, Complex.norm_I, one_mul]
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

theorem coupling_nonneg {d : ℕ} {L γ δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) : 0 ≤ coupling d L γ δ := by
  unfold coupling
  have := Real.rpow_nonneg hL ((d : ℝ) - γ)
  positivity

/-- The modulus of the prefactor of (cut-term). -/
theorem norm_cutPrefactor {d : ℕ} {L γ δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (u v : ℤˣ) :
    ‖(coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((u : ℤ) : ℂ)) * (Complex.I * ((v : ℤ) : ℂ))‖ =
      coupling d L γ δ ^ 2 := by
  rw [norm_mul, norm_mul, norm_I_mul_unit, norm_I_mul_unit, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (coupling_nonneg hL hδ)]
  ring

instance instCountablePairE {d : ℕ} (m : MiniTreeCode) : Countable (PairE m d) := by
  unfold PairE; infer_instance

/-- **`term` at one output.** The pieces of the multiplier are `1` and the cut factor has modulus `≤ 1`. -/
theorem term_perk {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
      {Qr Qg : RegCpl} {inner : RegChain} (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
      (_hsh : ProtShape p (appendChain Xp (cpair m Qr Qg inner)) LG)
      (_hsz : (appendChain Xp (cpair m Qr Qg inner)).size = 2 * n)
      (_hamb : TreeAmb p (appendChain Xp (cpair m Qr Qg inner)) LG) {s : ℝ} (_hps : (p : ℝ) < s)
      (_hsp : s < p + 1) (t q' : ℝ) (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal)
      (_hH : LeafwiseControlled LG H B)
      (M : (GNode LG.garden.tree → Mom P.d) → ℂ) (Mc : (Fin 4 → Mom P.d) → (Fin 4 → Mom P.d) → ℂ)
      (Mp : (GNode LGp.garden.tree → Mom P.d) → ℂ) (Mi : (GNode LGi.garden.tree → Mom P.d) → ℂ)
      (Mr : (GNode LGr.garden.tree → Mom P.d) → ℂ) (Mg : (GNode LGg.garden.tree → Mom P.d) → ℂ)
      (_hM : D.MultFactors M Mc Mp Mi Mr Mg) (_hMp : ∀ K, Mp K = 1) (_hMi : ∀ K, Mi K = 1)
      (_hMr : ∀ K, Mr K = 1) (_hMg : ∀ K, Mg K = 1) (_hMc : ∀ A B, ‖Mc A B‖ ≤ 1) (k : Mom P.d),
      rn θ (timeBoxGt p q') (fun ts => kernelProt P.L P.γ P.δ LG H M (fun _ => ts 0) (ts 1)
          (ProtCfg.term.fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
          (P.C₁ ^ 3 * rb P (n - 1) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
            leafSizeProduct LG B) := by
  obtain ⟨Cc, hCc, hcore⟩ := term_core hθ0 (by linarith)
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  refine ⟨Cc * T4, ENNReal.mul_lt_top hCc (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top), ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LGp LGi LGr LGg Xp m Qr Qg inner D hsh hsz hamb s hps hsp t q' H B
    hH M Mc Mp Mi Mr Mg hM hMp hMi hMr hMg hMc k
  have hsh' := hsh
  obtain ⟨hwf, hdec, hle, hch⟩ := hsh'
  obtain ⟨hwfp, hwfi, hwfr, hwfg⟩ := cut_wf D hwf
  obtain ⟨np, ni, nr, ng, hnp, hni, hnr, hng, hnsum⟩ := cut_sizes hsz
  obtain ⟨hlp, hlonep, hli, hlonei, hlr, hlg⟩ := cut_layers D hsh
  obtain ⟨hHp, hHi, hHr, hHg⟩ := cut_leafwise D hH
  obtain ⟨fP, fI, fR, fG⟩ := cut_flat D hsh hamb
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  set ζ := LG.garden.sig 0 with hζ
  have hle_n : ∀ j, j ≤ n → j ≤ P.N (p + 1) ^ 4 := fun j hj => hj.trans hn
  -- the pieces as time functions
  set Kp : (Fin 2 → ℝ) → ℂ := fun x => treeLeaves P.L P.γ P.δ LGp (cutHp H) (x 0) (x 1) k with hKp
  set Ki : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    treeLeaves P.L P.γ P.δ LGi (cutHi Xp m H) (x 0) (x 1) (k + latticePoint P.L e.1.1) with hKi
  set Kr : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    coupleLeaves P.L P.γ P.δ LGr (cutHr Xp m inner ζ H) (cupR m inner ζ (x 0) (x 1) 0)
      (cupR m inner ζ (x 0) (x 1) 1) (k + latticePoint P.L e.1.2.1) with hKr
  set Kg : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    coupleLeaves P.L P.γ P.δ LGg (cutHg Xp m inner ζ H) (cupG m inner ζ (x 0) (x 1) 0)
      (cupG m inner ζ (x 0) (x 1) 1) (k + latticePoint P.L e.1.2.2) with hKg
  set W : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x => Ki e x * (Kr e x * Kg e x) with hW
  -- continuity
  have hKpc : Continuous Kp := cut_cont_tree _ _ _ hL1 LGp D.decP (cutHp H) (cutBp B) hHp k
  have hKic : ∀ e, Continuous (Ki e) := fun e =>
    cut_cont_tree _ _ _ hL1 LGi D.decI (cutHi Xp m H) (cutBi Xp m B) hHi _
  have hor : ∀ {f : ℝ → ℝ → ℂ} (c : ℝ → ℝ → Fin 2 → ℝ),
      ((∀ u v, c u v 0 = u ∧ c u v 1 = v) ∨ (∀ u v, c u v 0 = v ∧ c u v 1 = u)) →
      Continuous (fun x : Fin 2 → ℝ => f (x 0) (x 1)) →
      Continuous (fun x : Fin 2 → ℝ => f (c (x 0) (x 1) 0) (c (x 0) (x 1) 1)) := by
    intro f c hc hf
    rcases hc with hc | hc
    · simpa only [(hc _ _).1, (hc _ _).2] using hf
    · simp only [(hc _ _).1, (hc _ _).2]
      exact hf.comp (show Continuous fun x : Fin 2 → ℝ => ![x 1, x 0] by fun_prop)
  have hKrc : ∀ e, Continuous (Kr e) := fun e =>
    hor (f := fun a b => coupleLeaves P.L P.γ P.δ LGr (cutHr Xp m inner ζ H) a b (k + latticePoint P.L e.1.2.1))
      (cupR m inner ζ) (cupR_cases m inner ζ)
      (cut_cont_couple _ _ _ hL1 LGr D.decR (cutHr Xp m inner ζ H) (cutBr Xp m inner ζ B) hHr _)
  have hKgc : ∀ e, Continuous (Kg e) := fun e =>
    hor (f := fun a b => coupleLeaves P.L P.γ P.δ LGg (cutHg Xp m inner ζ H) a b (k + latticePoint P.L e.1.2.2))
      (cupG m inner ζ) (cupG_cases m inner ζ)
      (cut_cont_couple _ _ _ hL1 LGg D.decG (cutHg Xp m inner ζ H) (cutBg Xp m inner ζ B) hHg _)
  have hWc : ∀ e, Continuous (W e) := fun e => (hKic e).mul ((hKrc e).mul (hKgc e))
  -- the gates on the pieces
  set bp : ℝ := P.L ^ c' * rb P np (LGp.incoherency (Xp.treeLinks (LGp.garden.sig 0))) *
    leafSizeProduct LGp (cutBp B) with hbp
  set bi : ℝ := P.L ^ c' * rb P ni (LGi.incoherency (inner.treeLinks (LGi.garden.sig 0))) *
    leafSizeProduct LGi (cutBi Xp m B) with hbi
  set br : ℝ := P.L ^ c' * rb P nr (LGr.incoherency Qr.links) * leafSizeProduct LGr (cutBr Xp m inner ζ B) with hbr
  set bg : ℝ := P.L ^ c' * rb P ng (LGg.incoherency Qg.links) * leafSizeProduct LGg (cutBg Xp m inner ζ B) with hbg
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hrb : ∀ j g, 0 ≤ rb P j g := fun j g => rb_nonneg hC1 K.hδ hL0 j g
  have hLc : 0 ≤ P.L ^ c' := Real.rpow_nonneg hL0 _
  have hls : ∀ {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal), 0 ≤ leafSizeProduct LGx Bx :=
    fun LGx Bx => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hconv : ∀ (j g : ℕ) {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal),
      ENNReal.ofReal (P.L ^ c') * regBound P j g * ENNReal.ofReal (leafSizeProduct LGx Bx) =
        ENNReal.ofReal (P.L ^ c' * rb P j g * leafSizeProduct LGx Bx) := by
    intro j g w LGx Bx
    rw [regBound_eq_rb, ← ENNReal.ofReal_mul hLc, ← ENNReal.ofReal_mul (mul_nonneg hLc (hrb j g))]
  have hKpb : rn θ (timeBoxGt p p) Kp ≤ ENNReal.ofReal bp := by
    rw [hbp, ← hconv]
    exact tree_piece_rn K hp (hle_n np (by omega)) hθc Xp LGp hwfp hnp D.decP hlp hlonep fP (cutHp H) (cutBp B) hHp k
  have hKib : ∀ e, rn θ (timeBoxGt p p) (Ki e) ≤ ENNReal.ofReal bi := fun e => by
    rw [hbi, ← hconv]
    exact tree_piece_rn K hp (hle_n ni (by omega)) hθc inner LGi hwfi hni D.decI hli hlonei fI (cutHi Xp m H)
      (cutBi Xp m B) hHi _
  set Jr : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.1) ^ (30 * P.d))⁻¹ with hJr
  set Jg : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.2) ^ (30 * P.d))⁻¹ with hJg
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hKrb : ∀ e, rn θ (timeBoxGt p p) (Kr e) ≤ ENNReal.ofReal br * ENNReal.ofReal (Jr e) := fun e => by
    refine (rn_couple_oriented (fun a b => coupleLeaves P.L P.γ P.δ LGr (cutHr Xp m inner ζ H) a b
      (k + latticePoint P.L e.1.2.1)) (cupR m inner ζ) (cupR_cases m inner ζ)).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbr, ← hconv]
    exact couple_piece_rn K hp (hle_n nr (by omega)) hθc Qr LGr hwfr hnr D.decR hlr fR _ _ hHr _
  have hKgb : ∀ e, rn θ (timeBoxGt p p) (Kg e) ≤ ENNReal.ofReal bg * ENNReal.ofReal (Jg e) := fun e => by
    refine (rn_couple_oriented (fun a b => coupleLeaves P.L P.γ P.δ LGg (cutHg Xp m inner ζ H) a b
      (k + latticePoint P.L e.1.2.2)) (cupG m inner ζ) (cupG_cases m inner ζ)).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbg, ← hconv]
    exact couple_piece_rn K hp (hle_n ng (by omega)) hθc Qg LGg hwfg hng D.decG hlg fG _ _ hHg _
  have hfinr : ∀ e, rn θ (timeBoxGt p p) (Kr e) < ⊤ := fun e =>
    (hKrb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hfing : ∀ e, rn θ (timeBoxGt p p) (Kg e) < ⊤ := fun e =>
    (hKgb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hfini : ∀ e, rn θ (timeBoxGt p p) (Ki e) < ⊤ := fun e => (hKib e).trans_lt ENNReal.ofReal_lt_top
  have hRG : ∀ e, rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x) ≤
      ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Kr e) * rn θ (timeBoxGt p p) (Kg e) := fun e =>
    rn_mul_le hθ0 (timeBoxGt_cl p) (Kr e) (Kg e) (hKgc e) (hfinr e) (hfing e)
  have hfinRG : ∀ e, rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x) < ⊤ := fun e =>
    (hRG e).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfinr e)) (hfing e))
  have hWb : ∀ e, rn θ (timeBoxGt p p) (W e) ≤
      T4 * (ENNReal.ofReal bi * ((ENNReal.ofReal br * ENNReal.ofReal (Jr e)) *
        (ENNReal.ofReal bg * ENNReal.ofReal (Jg e)))) := fun e => by
    refine (rn_mul_le hθ0 (timeBoxGt_cl p) (Ki e) (fun x => Kr e x * Kg e x) ((hKrc e).mul (hKgc e))
      (hfini e) (hfinRG e)).trans ?_
    calc ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Ki e) * rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x)
        ≤ ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal bi *
            (ENNReal.ofReal (2 ^ θ) * (ENNReal.ofReal br * ENNReal.ofReal (Jr e)) *
              (ENNReal.ofReal bg * ENNReal.ofReal (Jg e))) :=
          mul_le_mul' (mul_le_mul' le_rfl (hKib e)) ((hRG e).trans (mul_le_mul' (mul_le_mul' le_rfl (hKrb e))
            (hKgb e)))
      _ = _ := by rw [hT4]; ring
  have hWfin : ∀ e, rn θ (timeBoxGt p p) (W e) < ⊤ := fun e =>
    (hWb e).trans_lt (by
      refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ?_ ?_)) <;>
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hKpfin : rn θ (timeBoxGt p p) Kp < ⊤ := hKpb.trans_lt ENNReal.ofReal_lt_top
  -- the cut identity on the box
  have hHs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom P.d,
      Summable fun j : Fin P.d → ℤ => |H ℓ.1 (k' + latticePoint P.L j)| :=
    fun ℓ hℓ k' => summable_coset_piece hH hL1 k' ℓ hℓ
  have hMp' : Mp = fun _ => 1 := funext hMp
  have hMi' : Mi = fun _ => 1 := funext hMi
  have hMr' : Mr = fun _ => 1 := funext hMr
  have hMg' : Mg = fun _ => 1 := funext hMg
  subst hMp' hMi' hMr' hMg'
  set c₀ : ℂ := (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
    (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) with hc₀
  set A : PairE m P.d → ℝ := fun e => cutFreq m ζ P.L P.γ P.δ k e with hA
  set c : PairE m P.d → ℂ := fun e => c₀ * (Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ)) with hc
  have hcut : ∀ ts ∈ timeBoxGt (p : ℝ) q',
      kernelProt P.L P.γ P.δ LG H M (fun _ => ts 0) (ts 1)
          (ProtCfg.term.fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k (fun _ => 0) 0 =
        ∑' e, c e * ∫ u in Ioo s (ts 0), cutMod (A e) s u * (Kp ![ts 0, u] * W e ![u, s]) := by
    intro ts hts
    rw [kernelProt_term_cut D P.L P.γ P.δ H hHs M Mc _ _ _ _ hM 1 hMc (fun _ => by simp) (fun _ => by simp)
      (fun _ => by simp) (fun _ => by simp) s t (ts 0) (ts 1) k, cutU_eq D hch hps hts.1.1.2, ← tsum_mul_left]
    refine tsum_congr fun e => ?_
    rw [show c e = c₀ * (Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ)) from rfl, mul_assoc c₀]
    congr 1
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    simp only [cut_kernel_tree _ _ _ _ D.decP, cut_kernel_tree _ _ _ _ D.decI, cut_kernel_couple _ _ _ _ D.decR,
      cut_kernel_couple _ _ _ _ D.decG]
    rfl
  rw [rn_congr θ hcut]
  refine (hcore (PairE m P.d) p s q' hps hsp A c Kp W hKpc hWc hKpfin hWfin).trans ?_
  -- the exceptional sum
  set cc : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hcc
  have hcc0 : 0 ≤ cc := sq_nonneg _
  have hc0n : ‖c₀‖ = cc := norm_cutPrefactor hL0 K.hδ _ _
  have hce : ∀ e, ‖c e‖ₑ ≤ ENNReal.ofReal cc := fun e => by
    rw [← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal ?_
    have hMe : ‖Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (hMc _ _) (abs_cutEps_le m e) (abs_nonneg _) zero_le_one).trans (by norm_num)
    calc ‖c e‖ = ‖c₀‖ * ‖Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ)‖ := norm_mul _ _
      _ ≤ cc * 1 := by rw [hc0n]; exact mul_le_mul_of_nonneg_left hMe hcc0
      _ = cc := mul_one _
  set f : (Fin P.d → ℤ) → ℝ≥0∞ := fun y => ENNReal.ofReal (jbr (k + latticePoint P.L y) ^ (30 * P.d))⁻¹ with hf
  set Z : ℝ≥0∞ := ENNReal.ofReal cc * ENNReal.ofReal bp * T4 *
    (ENNReal.ofReal bi * ENNReal.ofReal br * ENNReal.ofReal bg) with hZ
  have hterm : ∀ e, ‖c e‖ₑ * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W e)) ≤
      Z * (f e.1.2.1 * f e.1.2.2) := fun e => by
    calc ‖c e‖ₑ * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W e))
        ≤ ENNReal.ofReal cc * (ENNReal.ofReal bp * (T4 * (ENNReal.ofReal bi * ((ENNReal.ofReal br *
            ENNReal.ofReal (Jr e)) * (ENNReal.ofReal bg * ENNReal.ofReal (Jg e)))))) :=
          mul_le_mul' (hce e) (mul_le_mul' hKpb (hWb e))
      _ = Z * (f e.1.2.1 * f e.1.2.2) := by rw [hZ, hf]; ring
  have hsum : ∑' e, ‖c e‖ₑ * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W e)) ≤
      Z * (ENNReal.ofReal (latC P.d * P.L ^ P.d) * ENNReal.ofReal (latC P.d * P.L ^ P.d)) := by
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    rw [ENNReal.tsum_mul_left]
    refine mul_le_mul' le_rfl ((tsum_pairE_le m f).trans (mul_le_mul' ?_ ?_)) <;>
      exact tsum_decay_le hd1 hL1 k
  refine (mul_le_mul' le_rfl hsum).trans (le_of_eq ?_)
  -- the algebra
  have hlat0 : 0 ≤ latC P.d * P.L ^ P.d := mul_nonneg (latC_nonneg _) (pow_nonneg hL0 _)
  have hn1 : np + ni + nr + ng = n - 1 := by omega
  have hg : LGp.incoherency (Xp.treeLinks (LGp.garden.sig 0)) + LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) +
      LGr.incoherency Qr.links + LGg.incoherency Qg.links = protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG :=
    (D.incoherency_cutTerm_of_chainIn hch).symm
  have hprod : bp * bi * br * bg = P.L ^ (4 * c') *
      (P.C₁ ^ 3 * rb P (n - 1) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) * leafSizeProduct LG B := by
    rw [hbp, hbi, hbr, hbg, cut_leafSize D B, ← hn1, ← hg]
    have h4 : P.L ^ (4 * c') = P.L ^ c' * P.L ^ c' * P.L ^ c' * P.L ^ c' := by
      rw [show 4 * c' = c' + c' + c' + c' by ring, Real.rpow_add (by linarith), Real.rpow_add (by linarith),
        Real.rpow_add (by linarith)]
    have h4r := rb_four (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := np) (n₂ := ni) (n₃ := nr) (n₄ := ng)
      (g₁ := LGp.incoherency (Xp.treeLinks (LGp.garden.sig 0))) (g₂ := LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)))
      (g₃ := LGr.incoherency Qr.links) (g₄ := LGg.incoherency Qg.links)
    rw [h4, show P.C₁ ^ 3 * rb P (np + ni + nr + ng) (LGp.incoherency (Xp.treeLinks (LGp.garden.sig 0)) +
        LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) + LGr.incoherency Qr.links + LGg.incoherency Qg.links) =
        rb P np _ * rb P ni _ * rb P nr _ * rb P ng _ from by rw [h4r]; unfold rb; ring]
    ring
  have hb0 : 0 ≤ bp := mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)
  have hi0 : 0 ≤ bi := mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)
  have hr0 : 0 ≤ br := mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)
  have hg0 : 0 ≤ bg := mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)
  rw [hZ, ← ENNReal.ofReal_mul hcc0, ← ENNReal.ofReal_mul hi0, ← ENNReal.ofReal_mul (mul_nonneg hi0 hr0),
    ← ENNReal.ofReal_mul hlat0]
  calc Cc * (ENNReal.ofReal (cc * bp) * T4 * ENNReal.ofReal (bi * br * bg) *
        ENNReal.ofReal ((latC P.d * P.L ^ P.d) * (latC P.d * P.L ^ P.d)))
      = Cc * T4 * (ENNReal.ofReal (cc * bp) * ENNReal.ofReal (bi * br * bg) *
          ENNReal.ofReal ((latC P.d * P.L ^ P.d) * (latC P.d * P.L ^ P.d))) := by ring
    _ = Cc * T4 * ENNReal.ofReal (cc * bp * (bi * br * bg) * ((latC P.d * P.L ^ P.d) * (latC P.d * P.L ^ P.d))) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hcc0 hb0), ← ENNReal.ofReal_mul
          (mul_nonneg (mul_nonneg hcc0 hb0) (mul_nonneg (mul_nonneg hi0 hr0) hg0))]
    _ = _ := by
        congr 2
        linear_combination (cc * (latC P.d * P.L ^ P.d) ^ 2) * hprod

end WaveTurbulence.Flower.ProtPin
