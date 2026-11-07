/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.ZpObj
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.NullSet

/-! # P4-W1: the window bounds of the clamped time factors and the continuous gate expansions

* `TR η = traceConst (1 - η) χ₀` (as a real `≥ 1`): the cost of the trace (TARGET L1917 weakens `𝔛^{1-η}` to `𝔛^{1-2η}` for the
  constant extension; the Lean trace `XNorm00Restr_trace_cross` costs only the constant `TR η`).
* `clamp_bound_C`, `clamp_bound_T`: for a continuous time factor `Jc` with `‖Jc‖_{𝔛^{1-η}(B_q)} ≤ X` on the gate box at level `q`
  (`timeBox q L₂`, resp. `timeBoxGt q L₂`), the clamped factor `clampJ q Jc` obeys `‖·‖_{𝔛^{1-η}(B_w)} ≤ TR η · X` on the window box at
  every level `w` with `w = q` (native), `q + 1 ≤ w` (trace at `q + 1`) or `w + 1 ≤ q` (zero a.e.).
* `ContExp`: a gate expansion with continuous time factors (`leafwise_cont` applied to `CoherentGateH`); `ContExp.gateC`, `ContExp.gateT`.
* `ObjCert.ofCont`: the certified expansion (`ObjCert`) of a member `f` of an approximant family from a `ContExp` at level `q` and the
  identity set `V`: terms `δⁿ · clampJ q Jᵢ · Mᵢ` (padded to at least one term), `CJ = 2 TR(η) C₁^{n+1}`, `CM = C₁^{n+1} cost`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.LGSpine WaveTurbulence.VineEstS5C
  WaveTurbulence.VineEstS5C.P2 MeasureTheory Set Filter TTree WaveTurbulence.Reg
open scoped ENNReal

/-- The trace constant (real form). -/
noncomputable def TR (η : ℝ) : ℝ := (Regref.traceConst (r := 2) (1 - η) chiUnit).toReal

theorem ofReal_TR (η : ℝ) : ENNReal.ofReal (TR η) = Regref.traceConst (r := 2) (1 - η) chiUnit :=
  ENNReal.ofReal_toReal (traceConst_ne_top _)

theorem one_le_TR {η : ℝ} (hη : η ≤ 1) : 1 ≤ TR η := by
  have h := one_le_traceConst' (r := 2) (θ := 1 - η) (by linarith)
  unfold TR
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top (traceConst_ne_top _)).2 h

theorem vec2_eta (ts : Fin 2 → ℝ) : ![ts 0, ts 1] = ts := by
  funext i; fin_cases i <;> rfl

theorem vec2_update (ts : Fin 2 → ℝ) (c : ℝ) : ![c, ts 1] = Function.update ts 0 c := by
  funext i; fin_cases i <;> simp

/-- The trace points of a tree box are in the closure of the interior of the gate box. -/
theorem gt_trace_mem {q L2 : ℝ} (hq : L2 ≤ q) {s : ℝ} (hs1 : L2 ≤ s) (hs2 : s ≤ L2 + 1) :
    ![q + 1, s] ∈ closure (interior (timeBoxGt q L2)) := by
  by_cases hlt : s < q + 1
  · exact timeBoxGt_subset_closure_interior hq ⟨⟨⟨by simp, by simp⟩, ⟨by simpa using hs1, by simpa using hs2⟩⟩,
      by simpa using hlt⟩
  · have hs : s = q + 1 := le_antisymm (by linarith) (not_lt.1 hlt)
    have hL : L2 = q := by linarith
    have hcl : closure (timeBoxGt q L2) ⊆ closure (interior (timeBoxGt q L2)) :=
      closure_minimal (timeBoxGt_subset_closure_interior hq) isClosed_closure
    refine hcl ?_
    let y : ℝ → Fin 2 → ℝ := fun ε => ![q + 1, q + 1 - ε]
    have hy : Continuous y := by
      refine continuous_pi fun i => ?_
      fin_cases i <;> simp [y] <;> fun_prop
    have hlim : Tendsto y (nhdsWithin 0 (Ioi 0)) (nhds ![q + 1, s]) := by
      have : y 0 = ![q + 1, s] := by simp [y, hs]
      rw [← this]
      exact hy.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    refine ⟨⟨⟨by simp [y], by simp [y]⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp only [y, Matrix.cons_val_zero, Matrix.cons_val_one]
    · linarith [hε.2]
    · linarith [hε.1]
    · linarith [hε.1]

section Clamp
variable {η : ℝ} (hθ : 0 ≤ 1 - η) (hη : η ≤ 1)
include hθ hη

/-- **Window bound of a clamped couple factor.** -/
theorem clamp_bound_C {q w L2 : ℕ} (hL2q : L2 ≤ q) (hcase : w = q ∨ q + 1 ≤ w ∨ w + 1 ≤ q)
    {Jc : (Fin 2 → ℝ) → ℂ} (hJc : Continuous Jc) {X : ℝ} (hX : 0 ≤ X)
    (hJ : XNorm00Restr (V := Unit) (1 - η) (timeBox (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X) :
    XNorm00Restr (V := Unit) (1 - η) (timeBox (w : ℝ) L2) Set.univ (fun ts _ => clampJ q Jc ts) ≤
      ENNReal.ofReal (TR η * X) := by
  have hTR := one_le_TR hη
  have hXle : ENNReal.ofReal X ≤ ENNReal.ofReal (TR η * X) :=
    ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left hX hTR)
  rcases hcase with rfl | hc | hc
  · refine le_trans (le_of_eq ?_) (hJ.trans hXle)
    refine XNorm00Restr_congr_on _ _ fun ts hts v _ => ?_
    have h1 := hts.1
    unfold clampJ
    rw [if_neg (not_lt.2 h1.1), min_eq_left h1.2, vec2_eta]
  · have hcl : ∀ ts ∈ timeBox (w : ℝ) L2, Function.update ts 0 ((q : ℝ) + 1) ∈ closure (interior (timeBox (q : ℝ) L2)) := by
      intro ts hts
      refine timeBox_subset_closure_interior _ _ ⟨⟨by simp, by simp⟩, ?_⟩
      simpa [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)] using hts.2
    have htr := XNorm00Restr_trace_cross hθ ![(w : ℝ), L2] (B := timeBox (q : ℝ) L2) (Bt := timeBox (w : ℝ) L2)
      (fun ts hts i => by fin_cases i; exacts [hts.1, hts.2]) (K := (Set.univ : Set Unit)) (fun ts _ => Jc ts)
      (fun _ _ => hJc) 0 ((q : ℝ) + 1) hcl
    refine le_trans (le_of_eq ?_) (htr.trans ?_)
    · refine XNorm00Restr_congr_on _ _ fun ts hts v _ => ?_
      have hw : ((q : ℝ) + 1) ≤ ts 0 := le_trans (by exact_mod_cast hc) hts.1.1
      unfold clampJ
      rw [if_neg (by linarith), min_eq_right hw, vec2_update]
    · rw [← ofReal_TR]
      calc ENNReal.ofReal (TR η) * XNorm00Restr (V := Unit) (1 - η) (timeBox (q : ℝ) L2) Set.univ (fun ts _ => Jc ts)
          ≤ ENNReal.ofReal (TR η) * ENNReal.ofReal X := mul_le_mul' le_rfl hJ
        _ = ENNReal.ofReal (TR η * X) := (ENNReal.ofReal_mul (by linarith)).symm
  · have hz : XNorm00Restr (V := Unit) (1 - η) (timeBox (w : ℝ) L2) Set.univ (fun ts _ => clampJ q Jc ts) ≤
        XNorm00Restr (V := Unit) (1 - η) (timeBox (w : ℝ) L2) Set.univ (fun _ _ => (0 : ℂ)) := by
      refine XNorm00Restr_le_of_ae_eq _ _ ?_
      have hn : ∀ᵐ ts : Fin 2 → ℝ, ts ∉ {tt : Fin 2 → ℝ | tt 0 = q} :=
        measure_eq_zero_iff_ae_notMem.mp (P4.null_clock_hyperplane 0 (q : ℝ))
      filter_upwards [hn] with ts hts htsB v _
      have hle : ts 0 ≤ (q : ℝ) := le_trans htsB.1.2 (by exact_mod_cast hc)
      have hlt : ts 0 < q := lt_of_le_of_ne hle hts
      unfold clampJ
      rw [if_pos hlt]
    rw [Eng.XNorm00Restr_zero] at hz
    exact hz.trans zero_le

/-- **Window bound of a clamped tree factor.** -/
theorem clamp_bound_T {q w L2 : ℕ} (hL2q : L2 ≤ q) (hcase : w = q ∨ q + 1 ≤ w ∨ w + 1 ≤ q)
    {Jc : (Fin 2 → ℝ) → ℂ} (hJc : Continuous Jc) {X : ℝ} (hX : 0 ≤ X)
    (hJ : XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X) :
    XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (w : ℝ) L2) Set.univ (fun ts _ => clampJ q Jc ts) ≤
      ENNReal.ofReal (TR η * X) := by
  have hTR := one_le_TR hη
  have hXle : ENNReal.ofReal X ≤ ENNReal.ofReal (TR η * X) :=
    ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left hX hTR)
  rcases hcase with rfl | hc | hc
  · refine le_trans (le_of_eq ?_) (hJ.trans hXle)
    refine XNorm00Restr_congr_on _ _ fun ts hts v _ => ?_
    have h1 := hts.1.1
    unfold clampJ
    rw [if_neg (not_lt.2 h1.1), min_eq_left h1.2, vec2_eta]
  · have hcl : ∀ ts ∈ timeBoxGt (w : ℝ) L2,
        Function.update ts 0 ((q : ℝ) + 1) ∈ closure (interior (timeBoxGt (q : ℝ) L2)) := by
      intro ts hts
      rw [← vec2_update]
      exact gt_trace_mem (by exact_mod_cast hL2q) hts.1.2.1 hts.1.2.2
    have htr := XNorm00Restr_trace_cross hθ ![(w : ℝ), L2] (B := timeBoxGt (q : ℝ) L2) (Bt := timeBoxGt (w : ℝ) L2)
      (fun ts hts i => by fin_cases i; exacts [hts.1.1, hts.1.2]) (K := (Set.univ : Set Unit)) (fun ts _ => Jc ts)
      (fun _ _ => hJc) 0 ((q : ℝ) + 1) hcl
    refine le_trans (le_of_eq ?_) (htr.trans ?_)
    · refine XNorm00Restr_congr_on _ _ fun ts hts v _ => ?_
      have hw : ((q : ℝ) + 1) ≤ ts 0 := le_trans (by exact_mod_cast hc) hts.1.1.1
      unfold clampJ
      rw [if_neg (by linarith), min_eq_right hw, vec2_update]
    · rw [← ofReal_TR]
      calc ENNReal.ofReal (TR η) * XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (q : ℝ) L2) Set.univ (fun ts _ => Jc ts)
          ≤ ENNReal.ofReal (TR η) * ENNReal.ofReal X := mul_le_mul' le_rfl hJ
        _ = ENNReal.ofReal (TR η * X) := (ENNReal.ofReal_mul (by linarith)).symm
  · have hz : XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (w : ℝ) L2) Set.univ (fun ts _ => clampJ q Jc ts) ≤
        XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (w : ℝ) L2) Set.univ (fun _ _ => (0 : ℂ)) := by
      refine XNorm00Restr_le_of_ae_eq _ _ ?_
      have hn : ∀ᵐ ts : Fin 2 → ℝ, ts ∉ {tt : Fin 2 → ℝ | tt 0 = q} :=
        measure_eq_zero_iff_ae_notMem.mp (P4.null_clock_hyperplane 0 (q : ℝ))
      filter_upwards [hn] with ts hts htsB v _
      have hle : ts 0 ≤ (q : ℝ) := le_trans htsB.1.1.2 (by exact_mod_cast hc)
      have hlt : ts 0 < q := lt_of_le_of_ne hle hts
      unfold clampJ
      rw [if_pos hlt]
    rw [Eng.XNorm00Restr_zero] at hz
    exact hz.trans zero_le

end Clamp

/-- A gate expansion with continuous time factors. -/
structure ContExp (P : WTParams) (n W : ℕ) (T : Set (Fin 2 → ℝ)) (F : (Fin 2 → ℝ) → Mom P.d → ℂ) (cost : ℝ) where
  m : ℕ
  J : Fin m → (Fin 2 → ℝ) → ℂ
  M : Fin m → Mom P.d → ℝ
  hm : m ≤ 2 ^ n
  hJc : ∀ i, Continuous (J i)
  hexp : ∀ ts ∈ T, ∀ k, F ts k = ∑ i, (P.δ : ℂ) ^ n * J i ts * (M i k : ℂ)
  hJ : ∀ i, XNorm00Restr (V := Unit) (1 - P.η) T Set.univ (fun ts _ => J i ts) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)
  hM : ∀ i, SNormR (30 * P.d) W (M i) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n * cost)

section Gate
variable {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ} {kind : Bool}

/-- The continuous gate expansion of a coherent couple (`CoherentGateH` + `leafwise_cont`). -/
noncomputable def ContExp.gateC (hg : CoherentGateH P) (hB : ProfileBound P h Bh p) (hp : p < P.D) (hθ : 0 ≤ 1 - P.η)
    {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {Q : RegCpl} {LG : LayeredGarden 2} {q q' : ℕ} (hqq : q' ≤ q) (hqp : q ≤ p)
    (hsize : Q.size = 2 * n) (hcoh : IsCoherentCoupleAt p q q' Q LG) :
    ContExp P n (30 * P.d) (timeBox (q : ℝ) q') (fun ts k => SourceApp.couple P.δ h LG Q q q' (ts 0) (ts 1) k)
      (layerCost Bh LG) :=
  Classical.choice (by
    obtain ⟨-, -, hSp⟩ := (hg h Bh p hp hB n hn).1 Q LG q q' hqq hqp hsize hcoh
    obtain ⟨m, J, M, hm, hJc, hexp, hJ, hM⟩ := leafwise_cont (timeBox_subset_closure_interior _ _) hθ
      (fun k => continuous_couple_app P.δ h LG Q q q' k) hSp
    exact ⟨⟨m, J, M, hm, hJc, hexp, hJ, hM⟩⟩)

/-- The continuous gate expansion of a coherent tree. -/
noncomputable def ContExp.gateT (hg : CoherentGateH P) (hB : ProfileBound P h Bh p) (hp : p < P.D) (hθ : 0 ≤ 1 - P.η)
    {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {X : RegChain} {LG : LayeredGarden 1} {q q' : ℕ} (hqq : q' ≤ q) (hqp : q ≤ p)
    (hsize : X.size = 2 * n) (hcoh : IsCoherentTreeAt p q q' X LG) :
    ContExp P n 0 (timeBoxGt (q : ℝ) q') (fun ts k => SourceApp.tree P.δ h LG X q q' (ts 0) (ts 1) k)
      (layerCost Bh LG) :=
  Classical.choice (by
    obtain ⟨-, -, hSp⟩ := (hg h Bh p hp hB n hn).2 X LG q q' hqq hqp hsize hcoh
    obtain ⟨m, J, M, hm, hJc, hexp, hJ, hM⟩ := leafwise_cont
      (timeBoxGt_subset_closure_interior (by exact_mod_cast hqq)) hθ
      (fun k => continuous_tree_app P.δ h LG X q q' k) hSp
    exact ⟨⟨m, J, M, hm, hJc, hexp, hJ, hM⟩⟩)

end Gate

section OfCont
variable {P : WTParams} {n W : ℕ} {T : Set (Fin 2 → ℝ)} {F : (Fin 2 → ℝ) → Mom P.d → ℂ} {cost : ℝ}

/-- The `J` bound of a certified term. -/
noncomputable def certCJ (P : WTParams) (n : ℕ) : ℝ := 2 * (TR P.η * (P.C₁ * P.C₁ ^ n))

/-- The `M` bound of a certified term. -/
noncomputable def certCM (P : WTParams) (n : ℕ) (cost : ℝ) : ℝ := P.C₁ * P.C₁ ^ n * cost

theorem certCJ_pos (hC : 1 ≤ P.C₁) (hη : P.η ≤ 1) (n : ℕ) : 0 < certCJ P n := by
  unfold certCJ
  have := one_le_TR hη
  have : 0 < P.C₁ ^ n := pow_pos (by linarith) n
  have : 0 < P.C₁ := by linarith
  positivity

theorem lt_certCJ (hC : 1 ≤ P.C₁) (hη : P.η ≤ 1) (n : ℕ) :
    ENNReal.ofReal (TR P.η * (P.C₁ * P.C₁ ^ n)) < ENNReal.ofReal (certCJ P n) := by
  have hp := certCJ_pos hC hη n
  unfold certCJ at hp ⊢
  exact (ENNReal.ofReal_lt_ofReal_iff hp).2 (by linarith)

/-- **The certified expansion from a continuous gate expansion at level `q`.**  `hV`: the identity on `V` (from `zpQ_expand` /
`zpT_expand`); `hlo`, `hhi`: the window bounds of the clamped factors (from `clamp_bound_C` / `clamp_bound_T`). -/
noncomputable def ObjCert.ofCont (E : ContExp P n W T F cost) (q : ℝ) (f : ℝ → ℝ → Mom P.d → ℂ) (V : Set (Fin 2 → ℝ))
    (hV : ∀ t s : ℝ, ![t, s] ∈ V → ∀ k, f t s k = ∑ i, sepTerm (P.δ ^ n) (clampJ q (E.J i)) (E.M i) t s k)
    {Blo Bhi : Set (Fin 2 → ℝ)} {qlo qhi : Fin 2 → ℝ} (hclo : Blo ⊆ cell qlo) (hilo : Blo ⊆ closure (interior Blo))
    (hchi : Bhi ⊆ cell qhi) (hihi : Bhi ⊆ closure (interior Bhi)) (hC : 1 ≤ P.C₁) (hη : P.η ≤ 1) (hcost : 0 ≤ cost)
    (hlo : ∀ i, XNorm00Restr (V := Unit) (1 - P.η) Blo Set.univ (fun ts _ => clampJ q (E.J i) ts) ≤
      ENNReal.ofReal (TR P.η * (P.C₁ * P.C₁ ^ n)))
    (hhi : ∀ i, XNorm00Restr (V := Unit) (1 - P.η) Bhi Set.univ (fun ts _ => clampJ q (E.J i) ts) ≤
      ENNReal.ofReal (TR P.η * (P.C₁ * P.C₁ ^ n))) :
    ObjCert P W f Blo Bhi qlo qhi where
  toObjExp := ObjExp.ofPad (P.δ ^ n) (fun i => clampJ q (E.J i)) E.M V hV
  CJ := certCJ P n
  CM := certCM P n cost
  lo := sepTPad hclo hilo (certCJ_pos hC hη n) (by unfold certCM; have h0 : 0 ≤ P.C₁ := (by linarith); exact mul_nonneg (mul_nonneg h0 (pow_nonneg h0 n)) hcost) (P.δ ^ n)
    (fun i => clampJ q (E.J i)) E.M (fun i => (hlo i).trans_lt (lt_certCJ hC hη n)) E.hM
  hi := sepTPad hchi hihi (certCJ_pos hC hη n) (by unfold certCM; have h0 : 0 ≤ P.C₁ := (by linarith); exact mul_nonneg (mul_nonneg h0 (pow_nonneg h0 n)) hcost) (P.δ ^ n)
    (fun i => clampJ q (E.J i)) E.M (fun i => (hhi i).trans_lt (lt_certCJ hC hη n)) E.hM
  lo_c _ := rfl
  lo_J _ := rfl
  lo_M _ := rfl
  hi_c _ := rfl
  hi_J _ := rfl
  hi_M _ := rfl

theorem ObjCert.ofCont_m (E : ContExp P n W T F cost) (q : ℝ) (f : ℝ → ℝ → Mom P.d → ℂ) (V : Set (Fin 2 → ℝ))
    (hV : ∀ t s : ℝ, ![t, s] ∈ V → ∀ k, f t s k = ∑ i, sepTerm (P.δ ^ n) (clampJ q (E.J i)) (E.M i) t s k)
    {Blo Bhi : Set (Fin 2 → ℝ)} {qlo qhi : Fin 2 → ℝ} (hclo : Blo ⊆ cell qlo) (hilo : Blo ⊆ closure (interior Blo))
    (hchi : Bhi ⊆ cell qhi) (hihi : Bhi ⊆ closure (interior Bhi)) (hC : 1 ≤ P.C₁) (hη : P.η ≤ 1) (hcost : 0 ≤ cost)
    (hlo hhi) :
    (ObjCert.ofCont E q f V hV hclo hilo hchi hihi hC hη hcost hlo hhi).m ≤ 2 ^ n :=
  max_le E.hm (Nat.one_le_two_pow)

/-- The certified expansion with no identity set (`ObjExp.triv`, zero certificates). -/
noncomputable def ObjCert.triv (f : ℝ → ℝ → Mom P.d → ℂ) {Blo Bhi : Set (Fin 2 → ℝ)} {qlo qhi : Fin 2 → ℝ}
    (hclo : Blo ⊆ cell qlo) (hilo : Blo ⊆ closure (interior Blo))
    (hchi : Bhi ⊆ cell qhi) (hihi : Bhi ⊆ closure (interior Bhi)) : ObjCert P W f Blo Bhi qlo qhi where
  toObjExp := ObjExp.triv f
  CJ := 1
  CM := 0
  lo _ := ⟨0, fun _ => 0, fun _ => 0, hclo, hilo, zero_le_one, le_rfl,
    by rw [Eng.XNorm00Restr_zero]; exact ENNReal.ofReal_pos.2 one_pos, by rw [SNormR_zero_fn]; exact zero_le⟩
  hi _ := ⟨0, fun _ => 0, fun _ => 0, hchi, hihi, zero_le_one, le_rfl,
    by rw [Eng.XNorm00Restr_zero]; exact ENNReal.ofReal_pos.2 one_pos, by rw [SNormR_zero_fn]; exact zero_le⟩
  lo_c _ := rfl
  lo_J _ := rfl
  lo_M _ := rfl
  hi_c _ := rfl
  hi_J _ := rfl
  hi_M _ := rfl

end OfCont

end WaveTurbulence.VineEstS5C.P4.W13
