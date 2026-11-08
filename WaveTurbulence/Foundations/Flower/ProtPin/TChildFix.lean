/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildB
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildMix
public import WaveTurbulence.Foundations.Flower.ProtPin.RootTerm
public import WaveTurbulence.Foundations.Flower.ProtPin.FinalTwo

/-! # D3 PROT-PIN (P7): the root trace of a type-1 side couple whose partner root lies below `p`

o104 Prop 7.4 (b), the fixed case: the traced root (tree `j`) is in layer `p`, pinned at `s`, the partner root in a
layer `𝔏 < p`. For a partner clock `y ∈ [p, p + 1]` the partner root's time range is the whole cell `(𝔏, 𝔏 + 1)`, so
the traced kernel is CONSTANT on the window (`rn_const_le`). Its modulus is bounded by the sub-couple kernels at the
mixed clocks `(s, u) ∈ [p, p+1] × [𝔏, 𝔏+1]`, pointwise (`tc_couple_pt`: FILT-GATE or FILT-COH in either orientation),
the exceptional sum by `tcWt`, and the incoherent root link (lost by the cut) by the factor `L` (`rb_pred_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- A child of a root lies in a layer at most that of the root. -/
theorem tc_child_le {w : ℕ} (LG : LayeredGarden w) {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) (z : GNode LG.garden.tree)
    (t : Fin w) (i : Fin 3) (hz : z.1 = (t, [i])) : LG.layer z ≤ layerAt LG (t, []) := by
  have hm : (addrExt (t, ([] : TTree.Path)) [i]).2 ∈ (LG.garden.tree (addrExt (t, ([] : TTree.Path)) [i]).1).nodes := by
    have h2 := z.2
    rw [hz] at h2
    simpa [addrExt] using h2
  rw [← layerAt_node LG z, hz]
  have e : ((t, [i]) : Fin w × TTree.Path) = addrExt (t, []) [i] := by simp [addrExt]
  rw [e]
  exact (layerAt_le_parAt LG p hle hm).trans (parAt_child LG p i hm).le

theorem tc_t1U_fix {LG : LayeredGarden 2} {t : Fin 2} {q : ℕ} (hl : layerAt LG (t, []) = q) {T : ℝ}
    (hT : (q : ℝ) + 1 ≤ T) : t1U LG t T = Ioo (q : ℝ) (q + 1) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  ext u
  simp only [t1U, hl, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2, -, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2, by linarith, by linarith⟩

theorem tc_clock_mem {LG : LayeredGarden 2} (j : Fin 2) {p q : ℕ} (hj : layerAt LG (j, []) = p)
    (ho : layerAt LG (t1sw j, []) = q) {s u : ℝ} (hs : s ∈ Icc (p : ℝ) (p + 1)) (hu : u ∈ Icc (q : ℝ) (q + 1))
    (t : Fin 2) : t1Clock j s u t ∈ Icc (layerAt LG (t, []) : ℝ) (layerAt LG (t, []) + 1) := by
  by_cases ht : t = j
  · subst ht
    simp only [t1Clock, ite_true, hj]
    exact hs
  · have ht' : t = t1sw j := by
      fin_cases t <;> fin_cases j <;> simp_all [t1sw]
    rw [show t1Clock j s u t = u by simp [t1Clock, ht], ht', ho]
    exact hu

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LGr LG₁ LG₂ LG₃ : LayeredGarden 2}

/-- **The root trace of a type-1 side couple, the partner root below `p`** (o104 Prop 7.4 (b), fixed case). -/
theorem tc_t1_fix {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b)
      (_hFC : TcFC P) (_hθc : PieceLoss P θ 0) {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LGr LG₁ LG₂ LG₃ : LayeredGarden 2}
      (h : T1Data c Q₁ Q₂ Q₃ LGr.garden LG₁.garden LG₂.garden LG₃.garden)
      (_hlA : ∀ z, LG₁.layer z = LGr.layer (h.ιA z)) (_hlB : ∀ z, LG₂.layer z = LGr.layer (h.ιB z))
      (_hlC : ∀ z, LG₃.layer z = LGr.layer (h.ιC z))
      (_hwf : (RegCpl.type1 c Q₁ Q₂ Q₃).wf = true) (_hsz : (RegCpl.type1 c Q₁ Q₂ Q₃).size = 2 * n)
      (_hle : ∀ a, LGr.layer a ≤ p) (_hA : TcCplAmbS p (RegCpl.type1 c Q₁ Q₂ Q₃) LGr)
      (j : Fin 2) (_hj : layerAt LGr (j, []) = p) (_hpart : layerAt LGr (t1sw j, []) < p)
      {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
      (Hr : LeafProfiles 2 P.d) (Br : (Fin 2 × TTree.Path) → NNReal) (_hHr : LeafwiseControlled LGr Hr Br)
      (S : Finset (GNode LGr.garden.tree)) (ω : GNode LGr.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LGr.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LGr.garden.tree)) (M : GBranch LGr.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LGr.garden.tree)) (Mu : GBranch LGr.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (k : Mom P.d),
      rn θ (win p) (fun y => kernelProt P.L P.γ P.δ LGr Hr
          (gateM S ω F M Fu Mu) (fun b => if b.1.1 = j then s else y 0) 0 (trFix j s) k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 2 * rb P (n - 1) (LGr.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links)) *
            leafSizeProduct LGr Br * starCost S cω)) * tcWt P.L k := by
  refine ⟨cutNormR θ 1, cutNormR_lt_top θ 1, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC hθc p hp n hn c Q₁ Q₂ Q₃ LGr LG₁ LG₂ LG₃ h hlA hlB hlC hwf hsz hle hA j hj hpart
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
  have hq : ∀ t : Fin 2, layerAt LGr (t, []) ≤ p := fun t => by
    have hm : ([] : TTree.Path) ∈ (LGr.garden.tree t).nodes := TTree.nil_mem_nodes _
    rw [layerAt_node LGr (⟨(t, []), hm⟩ : GNode LGr.garden.tree)]
    exact hle _
  -- root layers of the sub-couples
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
  -- the identity, constant on the window
  set 𝔏 : ℕ := layerAt LGr (t1sw j, []) with h𝔏
  have h𝔏p : (𝔏 : ℝ) + 1 ≤ p := by exact_mod_cast hpart
  set ζ : ℤˣ := LGr.garden.sig j with hζ
  have hid : ∀ T : ℝ, (𝔏 : ℝ) + 1 ≤ T → kernelProt P.L P.γ P.δ LGr Hr (gateM S ω F M Fu Mu)
      (fun b => if b.1.1 = j then s else T) 0 (trFix j s) k (fun _ => 0) 0 =
      (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' e : T1E P.d,
        (fD3' S ω F (fun _ => false) M Fu Mu (h.rt 0) (t1Star c P.L k e 0) *
          fD3' S ω F (fun _ => false) M Fu Mu (h.rt 1) (t1Star c P.L k e 1)) * (t1Eps c e : ℂ) *
        ∫ u in Ioo (𝔏 : ℝ) (𝔏 + 1), t1Ph ζ P.L P.γ P.δ k e s u *
          (kernelProt P.L P.γ P.δ LG₁ (t1HA c Hr) m₁ (fun x => t1Clock j s u x.1.1) 0 (fun _ => none)
              (k + latticePoint P.L e.1.1) (fun _ => 0) 0 *
            (kernelProt P.L P.γ P.δ LG₂ (t1HB Hr) m₂ (fun x => t1Clock j s u (t1sw x.1.1)) 0 (fun _ => none)
                (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 *
              kernelProt P.L P.γ P.δ LG₃ (t1HC c Hr) m₃ (fun x => t1Clock j s u x.1.1) 0 (fun _ => none)
                (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0)) := by
    intro T hT
    set U : Fin 2 → ℝ := fun t => if t = j then s else T with hU
    have hUj : U j = s := by simp [hU]
    have hUo : U (t1sw j) = T := by simp [hU, t1sw_ne j]
    have hid0 := h.kernelProt_t1Trace P.L P.γ P.δ Hr hHs (gateM S ω F M Fu Mu) _ m₁ m₂ m₃ hMf CM
      (fun A B => (hMc A B).trans (le_max_left _ _))
      (fun κ => (hm₁B κ).trans ((le_max_left _ _).trans (le_max_right _ _)))
      (fun κ => (hm₂B κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
      (fun κ => (hm₃B κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
      U 0 j s hUj.symm.le hlA hlB hlC k
    rw [hUo, tc_t1U_fix h𝔏.symm hT] at hid0
    exact hid0
  have hwin : ∀ y ∈ win (p : ℝ), kernelProt P.L P.γ P.δ LGr Hr (gateM S ω F M Fu Mu)
      (fun b => if b.1.1 = j then s else y 0) 0 (trFix j s) k (fun _ => 0) 0 =
      kernelProt P.L P.γ P.δ LGr Hr (gateM S ω F M Fu Mu)
        (fun b => if b.1.1 = j then s else (p : ℝ) + 1) 0 (trFix j s) k (fun _ => 0) 0 := by
    intro y hy
    rw [hid (y 0) (h𝔏p.trans hy.1), hid _ (by linarith)]
  rw [rn_congr θ hwin]
  refine (rn_const_le θ (fun _ => (p : ℝ)) (fun y hy i => by
    rw [Subsingleton.elim i 0]; exact hy) _).trans ?_
  rw [hid _ (by linarith)]
  -- the pointwise bounds of the sub-couples
  set b₁ : ℝ := P.L ^ (0 : ℝ) * rb P n₁ (LG₁.incoherency Q₁.links) * leafSizeProduct LG₁ (tcBA c Br) *
    starCost (pullS h.ιA S) (fun z => cω (h.ιA z)) with hb₁
  set b₂ : ℝ := P.L ^ (0 : ℝ) * rb P n₂ (LG₂.incoherency Q₂.links) * leafSizeProduct LG₂ (tcBB Br) *
    starCost (pullS h.ιB S) (fun z => cω (h.ιB z)) with hb₂
  set b₃ : ℝ := P.L ^ (0 : ℝ) * rb P n₃ (LG₃.incoherency Q₃.links) * leafSizeProduct LG₃ (tcBC c Br) *
    starCost (pullS h.ιC S) (fun z => cω (h.ιC z)) with hb₃
  set J : Mom P.d → ℝ := fun x => (jbr x ^ (30 * P.d))⁻¹ with hJ
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hsI : s ∈ Icc (p : ℝ) (p + 1) := ⟨hps.le, hsp.le⟩
  have hclk : ∀ u ∈ Ioo (𝔏 : ℝ) (𝔏 + 1), ∀ t : Fin 2,
      t1Clock j s u t ∈ Icc (layerAt LGr (t, []) : ℝ) (layerAt LGr (t, []) + 1) :=
    fun u hu t => tc_clock_mem j hj h𝔏.symm hsI ⟨hu.1.le, hu.2.le⟩ t
  have hKA : ∀ e : T1E P.d, ∀ u ∈ Ioo (𝔏 : ℝ) (𝔏 + 1),
      ‖kernelProt P.L P.γ P.δ LG₁ (t1HA c Hr) m₁ (fun x => t1Clock j s u x.1.1) 0 (fun _ => none)
        (k + latticePoint P.L e.1.1) (fun _ => 0) 0‖ₑ ≤
        ENNReal.ofReal b₁ * ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) := fun e u hu => by
    rw [cut_kernel_couple_m P.L P.γ P.δ LG₁ h.dec₁ (t1HA c Hr) m₁ (fun t => t1Clock j s u t)]
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₁, ← piece_conv hL0 hrb _ _ 0 n₁ _ _]
    exact tc_couple_pt K hFC hp (hle_n n₁ (by omega)) hθc Q₁ LG₁ hw₁ hn₁ h.dec₁ hle₁ (hq 0) (hq 1)
      (hrA 0) (hrA 1) hc₁ _ _ _ hG₁ _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hH₁ _
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₁ (t1HA c Hr) h.dec₁.1.1 m₁ B₁ hm₁B _
        (summable_coset_piece hH₁ hL1 _)) (x := fun t => t1Clock j s u t) ⟨hclk u hu 0, hclk u hu 1⟩
  have e0 : t1sw (0 : Fin 2) = 1 := by decide
  have e1 : t1sw (1 : Fin 2) = 0 := by decide
  have hrB0 : LG₂.layer (GNode.root LG₂.garden.tree 0) ≤ layerAt LGr ((1 : Fin 2), []) := by
    have := hrB 0; rwa [e0] at this
  have hrB1 : LG₂.layer (GNode.root LG₂.garden.tree 1) ≤ layerAt LGr ((0 : Fin 2), []) := by
    have := hrB 1; rwa [e1] at this
  have hxB : ∀ u ∈ Ioo (𝔏 : ℝ) (𝔏 + 1), (fun t : Fin 2 => t1Clock j s u (t1sw t)) ∈
      timeBox ((layerAt LGr ((1 : Fin 2), []) : ℕ) : ℝ) (layerAt LGr ((0 : Fin 2), []) : ℕ) := by
    intro u hu
    refine ⟨?_, ?_⟩
    · show t1Clock j s u (t1sw 0) ∈ _
      rw [e0]; exact hclk u hu 1
    · show t1Clock j s u (t1sw 1) ∈ _
      rw [e1]; exact hclk u hu 0
  have hKB : ∀ e : T1E P.d, ∀ u ∈ Ioo (𝔏 : ℝ) (𝔏 + 1),
      ‖kernelProt P.L P.γ P.δ LG₂ (t1HB Hr) m₂ (fun x => t1Clock j s u (t1sw x.1.1)) 0 (fun _ => none)
        (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0‖ₑ ≤
        ENNReal.ofReal b₂ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) := fun e u hu => by
    rw [cut_kernel_couple_m P.L P.γ P.δ LG₂ h.dec₂ (t1HB Hr) m₂ (fun t => t1Clock j s u (t1sw t))]
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₂, ← piece_conv hL0 hrb _ _ 0 n₂ _ _]
    exact tc_couple_pt K hFC hp (hle_n n₂ (by omega)) hθc Q₂ LG₂ hw₂ hn₂ h.dec₂ hle₂ (hq 1) (hq 0)
      hrB0 hrB1 hc₂ _ _ _ hG₂ _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hH₂ _
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₂ (t1HB Hr) h.dec₂.1.1 m₂ B₂ hm₂B _
        (summable_coset_piece hH₂ hL1 _)) (x := fun t => t1Clock j s u (t1sw t)) (hxB u hu)
  have hKC : ∀ e : T1E P.d, ∀ u ∈ Ioo (𝔏 : ℝ) (𝔏 + 1),
      ‖kernelProt P.L P.γ P.δ LG₃ (t1HC c Hr) m₃ (fun x => t1Clock j s u x.1.1) 0 (fun _ => none)
        (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0‖ₑ ≤
        ENNReal.ofReal b₃ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2)) := fun e u hu => by
    rw [cut_kernel_couple_m P.L P.γ P.δ LG₃ h.dec₃ (t1HC c Hr) m₃ (fun t => t1Clock j s u t)]
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₃, ← piece_conv hL0 hrb _ _ 0 n₃ _ _]
    exact tc_couple_pt K hFC hp (hle_n n₃ (by omega)) hθc Q₃ LG₃ hw₃ hn₃ h.dec₃ hle₃ (hq 0) (hq 1)
      (hrC 0) (hrC 1) hc₃ _ _ _ hG₃ _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hH₃ _
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₃ (t1HC c Hr) h.dec₃.1.1 m₃ B₃ hm₃B _
        (summable_coset_piece hH₃ hL1 _)) (x := fun t => t1Clock j s u t) ⟨hclk u hu 0, hclk u hu 1⟩
  -- the modulus of the constant
  set c2 : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hc2
  have hc20 : 0 ≤ c2 := sq_nonneg _
  set Wb : ℝ≥0∞ := ENNReal.ofReal b₁ * ENNReal.ofReal b₂ * ENNReal.ofReal b₃ with hWb
  have hterm : ∀ e : T1E P.d,
      ‖(fD3' S ω F (fun _ => false) M Fu Mu (h.rt 0) (t1Star c P.L k e 0) *
          fD3' S ω F (fun _ => false) M Fu Mu (h.rt 1) (t1Star c P.L k e 1)) * (t1Eps c e : ℂ) *
        ∫ u in Ioo (𝔏 : ℝ) (𝔏 + 1), t1Ph ζ P.L P.γ P.δ k e s u *
          (kernelProt P.L P.γ P.δ LG₁ (t1HA c Hr) m₁ (fun x => t1Clock j s u x.1.1) 0 (fun _ => none)
              (k + latticePoint P.L e.1.1) (fun _ => 0) 0 *
            (kernelProt P.L P.γ P.δ LG₂ (t1HB Hr) m₂ (fun x => t1Clock j s u (t1sw x.1.1)) 0 (fun _ => none)
                (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 *
              kernelProt P.L P.γ P.δ LG₃ (t1HC c Hr) m₃ (fun x => t1Clock j s u x.1.1) 0 (fun _ => none)
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
    have hint : ‖∫ u in Ioo (𝔏 : ℝ) (𝔏 + 1), t1Ph ζ P.L P.γ P.δ k e s u *
          (kernelProt P.L P.γ P.δ LG₁ (t1HA c Hr) m₁ (fun x => t1Clock j s u x.1.1) 0 (fun _ => none)
              (k + latticePoint P.L e.1.1) (fun _ => 0) 0 *
            (kernelProt P.L P.γ P.δ LG₂ (t1HB Hr) m₂ (fun x => t1Clock j s u (t1sw x.1.1)) 0 (fun _ => none)
                (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 *
              kernelProt P.L P.γ P.δ LG₃ (t1HC c Hr) m₃ (fun x => t1Clock j s u x.1.1) 0 (fun _ => none)
                (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0))‖ₑ ≤
        Wb * (ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) *
          ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2))) := by
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      refine (setLIntegral_mono' (g := fun _ => Wb * (ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) *
          ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2))))
        measurableSet_Ioo fun u hu => ?_).trans (le_of_eq ?_)
      · rw [enorm_mul, enorm_mul, enorm_mul, ← ofReal_norm, norm_t1Ph, ENNReal.ofReal_one, one_mul]
        calc _ ≤ (ENNReal.ofReal b₁ * ENNReal.ofReal (J (k + latticePoint P.L e.1.1))) *
              ((ENNReal.ofReal b₂ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1))) *
                (ENNReal.ofReal b₃ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2)))) :=
              mul_le_mul' (hKA e u hu) (mul_le_mul' (hKB e u hu) (hKC e u hu))
          _ = _ := by rw [hWb]; ring
      · rw [setLIntegral_const, Real.volume_Ioo, show (𝔏 : ℝ) + 1 - 𝔏 = 1 by ring, ENNReal.ofReal_one, mul_one]
    calc ‖fD3' S ω F (fun _ => false) M Fu Mu (h.rt 0) (t1Star c P.L k e 0) *
          fD3' S ω F (fun _ => false) M Fu Mu (h.rt 1) (t1Star c P.L k e 1)‖ₑ * ‖(t1Eps c e : ℂ)‖ₑ * _
        ≤ ENNReal.ofReal Ca * 1 * _ := mul_le_mul' (mul_le_mul' hMe hεe) hint
      _ = _ := by rw [mul_one]
  have hmod : ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' e : T1E P.d,
        (fD3' S ω F (fun _ => false) M Fu Mu (h.rt 0) (t1Star c P.L k e 0) *
          fD3' S ω F (fun _ => false) M Fu Mu (h.rt 1) (t1Star c P.L k e 1)) * (t1Eps c e : ℂ) *
        ∫ u in Ioo (𝔏 : ℝ) (𝔏 + 1), t1Ph ζ P.L P.γ P.δ k e s u *
          (kernelProt P.L P.γ P.δ LG₁ (t1HA c Hr) m₁ (fun x => t1Clock j s u x.1.1) 0 (fun _ => none)
              (k + latticePoint P.L e.1.1) (fun _ => 0) 0 *
            (kernelProt P.L P.γ P.δ LG₂ (t1HB Hr) m₂ (fun x => t1Clock j s u (t1sw x.1.1)) 0 (fun _ => none)
                (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 *
              kernelProt P.L P.γ P.δ LG₃ (t1HC c Hr) m₃ (fun x => t1Clock j s u x.1.1) 0 (fun _ => none)
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
  refine (mul_le_mul' hmod le_rfl).trans ?_
  -- the algebra
  have hg : LGr.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links =
      LG₁.incoherency Q₁.links + LG₂.incoherency Q₂.links + LG₃.incoherency Q₃.links + 1 := by
    rw [tc_t1_incoh h hlA hlB hlC, if_neg]
    intro he
    have hne : layerAt LGr (j, []) ≠ layerAt LGr (t1sw j, []) := by omega
    apply hne
    fin_cases j
    · exact he
    · exact he.symm
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
  set g := LGr.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links with hgdef
  have hval : c2 * Ca * (b₁ * b₂ * b₃) =
      coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) (g - 1)) * leafSizeProduct LGr Br *
        starCost S cω := by
    rw [hb₁, hb₂, hb₃, Real.rpow_zero, hg, Nat.add_sub_cancel, ← hn1, hleaf, hcost, hc2]
    have h3 := rb_three (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := n₁) (n₂ := n₂) (n₃ := n₃)
      (g₁ := LG₁.incoherency Q₁.links) (g₂ := LG₂.incoherency Q₂.links) (g₃ := LG₃.incoherency Q₃.links)
    rw [← h3, hCa]
    ring
  have hpred := rb_pred_le hL1 hC1 K.hδ K.hη0 (n - 1) (show 1 ≤ g by rw [hg]; omega)
  rw [Real.rpow_one] at hpred
  have hY : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 * P.C₁ ^ 2 * leafSizeProduct LGr Br * starCost S cω := by
    have := starCost_nonneg' S cω
    have := hb0 LGr Br
    positivity
  rw [hWb, ← ENNReal.ofReal_mul hb10, ← ENNReal.ofReal_mul (mul_nonneg hb10 hb20),
    ← ENNReal.ofReal_mul (mul_nonneg hc20 hCa0), hval]
  have hfin : coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) (g - 1)) * leafSizeProduct LGr Br *
      starCost S cω ≤ P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) g) *
        leafSizeProduct LGr Br * starCost S cω) :=
    calc coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) (g - 1)) * leafSizeProduct LGr Br * starCost S cω
        = (coupling P.d P.L P.γ P.δ ^ 2 * P.C₁ ^ 2 * leafSizeProduct LGr Br * starCost S cω) *
            rb P (n - 1) (g - 1) := by ring
      _ ≤ (coupling P.d P.L P.γ P.δ ^ 2 * P.C₁ ^ 2 * leafSizeProduct LGr Br * starCost S cω) *
            (P.L * rb P (n - 1) g) := mul_le_mul_of_nonneg_left hpred hY
      _ = _ := by ring
  calc ENNReal.ofReal (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) (g - 1)) * leafSizeProduct LGr Br *
        starCost S cω) * tcWt P.L k * cutNormR θ 1
      ≤ ENNReal.ofReal (P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) g) *
          leafSizeProduct LGr Br * starCost S cω)) * tcWt P.L k * cutNormR θ 1 :=
        mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hfin) le_rfl) le_rfl
    _ = _ := by ring

end WaveTurbulence.Flower.ProtPin
