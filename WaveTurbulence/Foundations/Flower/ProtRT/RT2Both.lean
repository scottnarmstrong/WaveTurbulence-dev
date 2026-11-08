/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.RT2B1
public import WaveTurbulence.Foundations.Flower.ProtRT.RT2B2
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildSym

/-! # RT-GATE (ii), both roots pinned: the assembly (`rt2_both`)

`RtBothOn θ Ct C`: `RtBoth` on the couples with `C Q`, in D3's signed ambient `TcCplAmbS` (= `CplAmbient p p p`). The
shapes with two branching roots: type 1 (`rt2_t1_both`); type 2 with a nonempty `+` chain (`rt2_t2a_both`, from the
one-pinned bound `RtOne`); type 2 with an empty `+` chain and a nonempty `−` chain, by conjugation
(`rt2_bothOn_conj`, D3's `tc_traceOnF_conj` pattern, ProtPin/TChildSym.lean); `triv` and `type2 nil nil` are excluded
(a branching root; `wf`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234 WaveTurbulence.PL234.Conj
open WaveTurbulence.Represents WaveTurbulence.ConjCoh ComplexConjugate

/-- `RtBoth` on the couples with `C Q`, in the signed ambient. -/
def RtBothOn (θ Ct : ℝ) (C : RegCpl → Prop) : Prop :=
  ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) (_hFC : TcFC P)
    (_hC11 : 1 ≤ P.C₁) (_hθc : PieceLoss P θ 0)
    {p : ℕ} (_hp : p < P.D) {nr : ℕ} (_hn : nr ≤ P.N (p + 1) ^ 4) (Q : RegCpl) (LGc : LayeredGarden 2)
    (_hwf : Q.wf = true) (_hsz : Q.size = 2 * nr) (_hdec : Q.Decodes LGc.garden) (_hle : ∀ a, LGc.layer a ≤ p)
    (_hC : C Q) (_hamb : TcCplAmbS p Q LGc)
    (_hj : ∀ j : Fin 2, layerAt LGc (j, []) = p)
    (_hjb : ∀ j : Fin 2, ([] : TTree.Path) ∈ (LGc.garden.tree j).branching)
    {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
    (Hc : LeafProfiles 2 P.d) (Bc : (Fin 2 × TTree.Path) → NNReal) (_hHc : LeafwiseControlled LGc Hc Bc)
    (S : Finset (GNode LGc.garden.tree)) (ω : GNode LGc.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LGc.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LGc.garden.tree)) (M : GBranch LGc.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LGc.garden.tree)) (Mu : GBranch LGc.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (k : Mom P.d),
    ‖kernelProt P.L P.γ P.δ LGc Hc (gateM S ω F M Fu Mu) (fun _ => s) 0 (MkSlotsO.rootPins (fun _ => True) s) k
        (fun _ => 0) 0‖ₑ ≤
      ENNReal.ofReal (Ct * (P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 3 * rb P (nr - 1) (LGc.incoherency Q.links)) +
        coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (nr - 2) (LGc.incoherency Q.links)))) *
        leafSizeProduct LGc Bc * starCost S cω)) * tcWt P.L k

/-- The right side of `RtBoth` dominates each of the one-cut and the two-cut forms. -/
theorem rt2_rhs_ge {P : WTParams} (hL : 1 ≤ P.L) (hC11 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) {Ct : ℝ} (hCt : 0 ≤ Ct)
    (n g : ℕ) {leaf CS : ℝ} (hleaf : 0 ≤ leaf) (hCS : 0 ≤ CS) :
    (Ct * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) g)) * leaf * CS ≤
      Ct * (P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) +
        coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) g))) * leaf * CS)) ∧
    (Ct * (P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) g)))) * leaf * CS ≤
      Ct * (P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) +
        coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) g))) * leaf * CS)) := by
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := by linarith
  have hr1 := rb_nonneg hC1 hδ hL0 (n - 1) g
  have hr2 := rb_nonneg hC1 hδ hL0 (n - 2) g
  have hc2 : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 := sq_nonneg _
  have hlat : 0 ≤ (latC P.d * P.L ^ P.d) ^ 2 := sq_nonneg _
  have hL2 : 1 ≤ P.L ^ 2 := one_le_pow₀ hL
  have h23 : P.C₁ ^ 2 ≤ P.C₁ ^ 3 := pow_le_pow_right₀ hC11 (by norm_num)
  have hA : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) := by positivity
  have hB : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
      (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) g)) := by positivity
  have hlc : 0 ≤ leaf * CS := mul_nonneg hleaf hCS
  constructor
  · have h1 : coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) g) ≤
        P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) +
          coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
            (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) g))) := by
      calc coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) g)
          ≤ coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) := by gcongr
        _ ≤ 1 * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) +
            coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
              (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) g))) := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hL2 (add_nonneg hA hB)
    have := mul_le_mul_of_nonneg_left h1 hCt
    calc Ct * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) g)) * leaf * CS
        = Ct * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 2 * rb P (n - 1) g)) * (leaf * CS) := by ring
      _ ≤ Ct * (P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) +
          coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
            (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) g)))) * (leaf * CS) :=
          mul_le_mul_of_nonneg_right this hlc
      _ = _ := by ring
  · have h1 : P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) g))) ≤
        P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) +
          coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
            (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) g))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have := mul_le_mul_of_nonneg_left h1 hCt
    calc Ct * (P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) g)))) * leaf * CS
        = Ct * (P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) g)))) * (leaf * CS) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this hlc
      _ = _ := by ring

/-- **Type 1.** -/
theorem rt2_bothOn_t1 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    RtBothOn θ 1 (fun Q => ∃ c Q₁ Q₂ Q₃, Q = RegCpl.type1 c Q₁ Q₂ Q₃) := by
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle hC hamb hj hjb s hps hsp Hc Bc hHc S ω cω
    hpres F M hM Fu Mu hMu k
  obtain ⟨c, Q₁, Q₂, Q₃, rfl⟩ := hC
  obtain ⟨LG₁, LG₂, LG₃, h, hlA, hlB, hlC⟩ := T1Data.exists_of_decodes LGc c Q₁ Q₂ Q₃ hdec hwf
  refine (rt2_t1_both hθ0 hθ1 K hFC hθc hp hn h hlA hlB hlC hwf hsz hle hamb hj hps hsp Hc Bc hHc S ω cω hpres
    F M hM Fu Mu hMu k).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have := (rt2_rhs_ge K.hL hC11 K.hδ zero_le_one nr (LGc.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links)
    (leaf := leafSizeProduct LGc Bc) (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg' S cω)).1
  simpa only [one_mul] using this

/-- **Type 2, a nonempty `+` chain.** -/
theorem rt2_bothOn_t2a {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) {Ct₁ : ℝ} (hCt₁ : 0 ≤ Ct₁) (h1 : RtOne θ 0 Ct₁) :
    RtBothOn θ Ct₁ (fun Q => ∃ (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest Xm : RegChain) (Qlp : RegCpl),
      Q = RegCpl.type2 (RegChain.pair m Qr Qg inner rest) Xm Qlp) := by
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle hC hamb hj hjb s hps hsp Hc Bc hHc S ω cω
    hpres F M hM Fu Mu hMu k
  obtain ⟨m, Qr, Qg, inner, rest, Xm, Qlp, rfl⟩ := hC
  obtain ⟨LGZ, LGB, D, hwZ, -, hdB, hsZ⟩ := tc2a_exists LGc m Qr Qg inner rest Xm Qlp hdec hwf
  obtain ⟨LGi, LGr, LGg, Pp⟩ := PairOnly.exists_of_wf LGZ m Qr Qg inner D.decZ hwZ
  refine (rt2_t2a_both hθ0 hθ1 hCt₁ h1 K hFC hC11 hθc hp hn D Pp hdB hsZ hwf hsz hdec hle hamb hj (hjb 1) hps hsp
    Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  exact le_of_eq_of_le (by ring) (rt2_rhs_ge K.hL hC11 K.hδ hCt₁ nr _ (leaf := leafSizeProduct LGc Bc)
    (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _) (starCost_nonneg' S cω)).2

/-- **Conjugation symmetry of the both-pinned bound.** -/
theorem rt2_bothOn_conj {θ Ct : ℝ} {C C' : RegCpl → Prop} (hCC : ∀ Q, C' Q → C (ConjCoh.conjCpl Q))
    (hT : RtBothOn θ Ct C) : RtBothOn θ Ct C' := by
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle hC hamb hj hjb s hps hsp Hc Bc hHc S ω cω
    hpres F M hM Fu Mu hMu k
  set LH := conjLayered LGc (Equiv.swap (0 : Fin 2) 1) with hLH
  have h : IsConjugateCouple LGc LH := conjLayered_isConjugateBy LGc (Equiv.swap (0 : Fin 2) 1)
  set ν := nodeEquiv h with hν
  set β := branchEquiv h with hβ
  have hle' : ∀ a, LH.layer a ≤ p := by
    intro a
    obtain ⟨a0, rfl⟩ := ν.surjective a
    rw [layer_node h]; exact hle a0
  have hj' : ∀ t : Fin 2, layerAt LH (t, []) = p := by
    intro t
    have hm : ([] : TTree.Path) ∈ (LGc.garden.tree (t1sw t)).nodes := TTree.branching_subset_nodes _ (hjb _)
    have e1 := layerAt_node LGc (⟨(t1sw t, []), hm⟩ : GNode LGc.garden.tree)
    have e2 := layerAt_node LH (ν (⟨(t1sw t, []), hm⟩ : GNode LGc.garden.tree))
    have e3 := layer_node h (⟨(t1sw t, []), hm⟩ : GNode LGc.garden.tree)
    have e4 : (ν (⟨(t1sw t, []), hm⟩ : GNode LGc.garden.tree)).1 = (t, []) := by
      show (Equiv.swap (0 : Fin 2) 1 (t1sw t), ([] : TTree.Path)) = _
      rw [tc_swap_eq_t1sw]
      fin_cases t <;> rfl
    rw [e4] at e2
    rw [e2, e3, ← e1, hj]
  have hjb' : ∀ t : Fin 2, ([] : TTree.Path) ∈ (LH.garden.tree t).branching := by
    intro t
    have := hjb (t1sw t)
    have e : t = Equiv.swap (0 : Fin 2) 1 (t1sw t) := by rw [tc_swap_eq_t1sw]; fin_cases t <;> rfl
    rw [e, h.tree_eq]; exact this
  have hpres' : ∀ a ∈ S.map ν.toEmbedding, Flower.IncTop.StarPresented (30 * P.d)
      (fun y => conj (ω (ν.symm a) y)) (cω (ν.symm a)) := by
    intro a ha
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_map.1 ha
    simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    exact tc_starPresented_conj (hpres a0 ha0)
  have hM' : ∀ b ∈ F.map β.toEmbedding, P.L ≤ M (β.symm b) := by
    intro b hb
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_map.1 hb
    simpa using hM b0 hb0
  have hMu' : ∀ b ∈ Fu.map β.toEmbedding, P.L ≤ Mu (β.symm b) := by
    intro b hb
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_map.1 hb
    simpa using hMu b0 hb0
  have key := hT K hFC hC11 hθc hp hn (ConjCoh.conjCpl Q) LH ((wf_conjCpl Q).trans hwf) ((size_conjCpl Q).trans hsz)
    (decodes_conj h hdec) hle' (hCC Q hC) (tc_ambS_conj h hamb) hj' hjb' hps hsp
    (transferProf h Hc) (transferProf h Bc) (leafwiseControlled_conj h hHc) (S.map ν.toEmbedding)
    (fun a y => conj (ω (ν.symm a) y)) (fun a => cω (ν.symm a)) hpres' (F.map β.toEmbedding)
    (fun b => M (β.symm b)) hM' (Fu.map β.toEmbedding) (fun b => Mu (β.symm b)) hMu' k
  have hker : kernelProt P.L P.γ P.δ LH (transferProf h Hc)
      (gateM (S.map ν.toEmbedding) (fun a y => conj (ω (ν.symm a) y)) (F.map β.toEmbedding)
        (fun b => M (β.symm b)) (Fu.map β.toEmbedding) (fun b => Mu (β.symm b)))
      (fun _ => s) 0 (MkSlotsO.rootPins (fun _ => True) s) k (fun _ => 0) 0 =
      conj (kernelProt P.L P.γ P.δ LGc Hc (gateM S ω F M Fu Mu) (fun _ => s) 0
        (MkSlotsO.rootPins (fun _ => True) s) k (fun _ => 0) 0) := by
    refine tc_kernelProt_conj h P.L P.γ P.δ Hc _ _ (fun K => ?_) _ _ (fun b => rfl) 0 _ _ (fun b => ?_) k _ _
      (fun _ => rfl) 0
    · unfold gateM
      have hFu := tc_filtWeight_conj h Fu (fun _ => false) Mu K
      have hF := tc_filtWeight_conj h F (fun _ => false) M K
      rw [tc_starWeight_conj h S ω K, hF, hFu, map_mul, map_mul, tc_conj_filtWeight, tc_conj_filtWeight]
    · show MkSlotsO.rootPins (fun _ => True) s (β b) = MkSlotsO.rootPins (fun _ => True) s b
      unfold MkSlotsO.rootPins
      have e2 : (β b).1.2 = b.1.2 := rfl
      rw [e2]
  have hcs : starCost (S.map ν.toEmbedding) (fun a => cω (ν.symm a)) = starCost S cω := by
    unfold starCost
    rw [Finset.prod_map]
    simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  rw [hker, incoherency_conj h hdec, leafSizeProduct_conj h Bc, hcs] at key
  rw [← ofReal_norm] at key ⊢
  rwa [Complex.norm_conj] at key

/-- **`rt2_both`** (the target of RT-HELPER2 / fork D). -/
theorem rt2_both {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) (h1 : ∃ Ct₁ : ℝ, 0 ≤ Ct₁ ∧ RtOne θ 0 Ct₁) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ RtBoth θ Ct := by
  obtain ⟨Ct₁, hCt₁, hone⟩ := h1
  have hT1 : RtBothOn θ 1 (fun Q => ∃ c Q₁ Q₂ Q₃, Q = RegCpl.type1 c Q₁ Q₂ Q₃) := rt2_bothOn_t1 hθ0 hθ1
  have hTa : RtBothOn θ Ct₁ (fun Q => ∃ (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest Xm : RegChain)
      (Qlp : RegCpl), Q = RegCpl.type2 (RegChain.pair m Qr Qg inner rest) Xm Qlp) :=
    rt2_bothOn_t2a hθ0 hθ1 hCt₁ hone
  have hTam : RtBothOn θ Ct₁ (fun Q => ∃ (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain)
      (Qlp : RegCpl), Q = RegCpl.type2 Xp (RegChain.pair m Qr Qg inner rest) Qlp) := by
    refine rt2_bothOn_conj (fun Q hQ => ?_) hTa
    obtain ⟨Xp, m, Qr, Qg, inner, rest, Qlp, rfl⟩ := hQ
    exact ⟨m, ConjCoh.conjCpl Qr, ConjCoh.conjCpl Qg, ConjCoh.conjChain inner, ConjCoh.conjChain rest,
      ConjCoh.conjChain Xp, ConjCoh.conjCpl Qlp, rfl⟩
  refine ⟨max 1 Ct₁, le_max_of_le_left zero_le_one, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle hamb hj hjb s hps hsp Hc Bc hHc S ω cω
    hpres F M hM Fu Mu hMu k
  have hambS := rt2_ambS hamb
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := by linarith
  have hmono : ∀ Ct : ℝ, Ct ≤ max 1 Ct₁ →
      ENNReal.ofReal (Ct * (P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 3 * rb P (nr - 1) (LGc.incoherency Q.links)) +
        coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (nr - 2) (LGc.incoherency Q.links)))) *
        leafSizeProduct LGc Bc * starCost S cω)) * tcWt P.L k ≤
      ENNReal.ofReal (max 1 Ct₁ * (P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 3 * rb P (nr - 1) (LGc.incoherency Q.links)) +
        coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (nr - 2) (LGc.incoherency Q.links)))) *
        leafSizeProduct LGc Bc * starCost S cω)) * tcWt P.L k := fun Ct hCt => by
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have := rb_nonneg hC1 K.hδ hL0 (nr - 1) (LGc.incoherency Q.links)
    have := rb_nonneg hC1 K.hδ hL0 (nr - 2) (LGc.incoherency Q.links)
    have := starCost_nonneg' S cω
    have : 0 ≤ leafSizeProduct LGc Bc := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 := sq_nonneg _
    have : 0 ≤ (latC P.d * P.L ^ P.d) ^ 2 := sq_nonneg _
    have hX : 0 ≤ P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 3 * rb P (nr - 1) (LGc.incoherency Q.links)) +
        coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (nr - 2) (LGc.incoherency Q.links)))) *
        leafSizeProduct LGc Bc * starCost S cω := by positivity
    calc Ct * (P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 3 * rb P (nr - 1) (LGc.incoherency Q.links)) +
        coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (nr - 2) (LGc.incoherency Q.links)))) *
        leafSizeProduct LGc Bc * starCost S cω)
        = Ct * (P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 3 * rb P (nr - 1) (LGc.incoherency Q.links)) +
        coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (nr - 2) (LGc.incoherency Q.links)))) *
        leafSizeProduct LGc Bc * starCost S cω) := rfl
      _ ≤ _ := mul_le_mul_of_nonneg_right hCt (by
          have := hX; nlinarith [hX])
  cases Q with
  | triv =>
    exfalso
    have ht := tree_of_decodes hdec 0
    have hb := hjb 0
    split_ifs at ht <;> rw [ht] at hb <;> simp [RegCpl.trees, TTree.branching] at hb
  | type1 c Q₁ Q₂ Q₃ =>
    exact (hT1 K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle ⟨c, Q₁, Q₂, Q₃, rfl⟩ hambS hj hjb hps hsp Hc Bc hHc S ω cω
      hpres F M hM Fu Mu hMu k).trans (hmono 1 (le_max_left _ _))
  | type2 Xp Xm Qlp =>
    cases Xp with
    | pair m Qr Qg inner rest =>
      exact (hTa K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle ⟨m, Qr, Qg, inner, rest, Xm, Qlp, rfl⟩ hambS hj hjb hps
        hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k).trans (hmono Ct₁ (le_max_right _ _))
    | nil =>
      cases Xm with
      | pair m Qr Qg inner rest =>
        exact (hTam K hFC hC11 hθc hp hn _ LGc hwf hsz hdec hle ⟨.nil, m, Qr, Qg, inner, rest, Qlp, rfl⟩ hambS hj hjb
          hps hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k).trans (hmono Ct₁ (le_max_right _ _))
      | nil =>
        exfalso
        simp [RegCpl.wf, RegChain.isNil] at hwf

end WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtRT in
/-- The target of fork D (briefs/RT-HELPER2.md), verbatim. -/
example {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) (h1 : ∃ Ct₁ : ℝ, 0 ≤ Ct₁ ∧ RtOne θ 0 Ct₁) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ RtBoth θ Ct :=
  rt2_both hθ0 hθ1 h1
