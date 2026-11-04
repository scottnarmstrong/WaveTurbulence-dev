/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.RegType1

/-!
# The type 2 recursion under regularization (DH21 (newexp2), (recurtype2))

The chain integral `ClassJR.chainT` (DH21 (newexp2)) is the regularized chain `chainK` whose pair
kernels depend on the variables: `e^{πiε_jα_{σj}(t_a-t_b)} F_j(α, t_a, t_b)` (`chainT_eq_chainK`).
Integrating every variable against its weight (Fubini, `mint_chain`):
* the pair variable `α_{σj}` turns the phase into `gk θ (t_a - t_b)`, or into `hk θ (t_a - t_b)` if
  `σ j ∈ Z`, when `ε_j = ζ_{σj}`;
* the pair coefficient `F_j` becomes its regularized integral `RI_j`;
* the continuation becomes its regularized integral.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

/-! ### `chainT` is a chain with variable-dependent kernels -/

theorem chainK_const_mul (P : ℕ → ℝ → ℝ → ℂ) :
    ∀ (c : LegalCode) (q : ℕ) (t : ℝ) (a : ℂ) (g : ℝ → ℂ),
      chainK P c q t (fun x => a * g x) = a * chainK P c q t g
  | .nil, _, _, _, _ => rfl
  | .node i r, q, t, a, g => by
    simp only [chainK_node]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun ta _ => ?_
    rw [← chainK_const_mul P i (q + 1) ta a]
    congr 1
    funext t'
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun tb _ => ?_
    show P q ta tb * chainK P r (q + i.size + 1) tb (fun x => a * g x) =
      a * (P q ta tb * chainK P r (q + i.size + 1) tb g)
    rw [chainK_const_mul P r _ tb a g]
    ring

variable {V : Type}

/-- The variable-dependent pair kernels of `chainT`: `e^{πiε_jα_{σj}(t_a-t_b)} F_j(α, t_a, t_b)`. -/
@[expose] noncomputable def phaseK (σ : ℕ → V) (ε : ℕ → ℤ) (F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ)
    (α : V → ℝ) (j : ℕ) (ta tb : ℝ) : ℂ :=
  cexp (π * I * (ε j * α (σ j) * (ta - tb))) * F j α ta tb

/-- **`chainT` is the chain with the kernels `phaseK`.** -/
theorem chainT_eq_chainK (σ : ℕ → V) (ε : ℕ → ℤ) (F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ) (α : V → ℝ) :
    ∀ (c : LegalCode) (q : ℕ) (t : ℝ) (g : ℝ → ℂ),
      chainT σ ε c q F α t g = chainK (phaseK σ ε F α) c q t g
  | .nil, _, _, _ => rfl
  | .node i r, q, t, g => by
    rw [chainT_node, chainK_node]
    refine intervalIntegral.integral_congr fun ta _ => ?_
    show cexp (π * I * (ε q * α (σ q) * ta)) * chainT σ ε i (q + 1) F α ta _ = _
    rw [chainT_eq_chainK σ ε F α i (q + 1), ← chainK_const_mul]
    congr 1
    funext t'
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun tb _ => ?_
    simp only [phaseK]
    rw [chainT_eq_chainK σ ε F α r]
    have : cexp (π * I * (ε q * α (σ q) * ta)) * cexp (π * I * (-(ε q * α (σ q)) * tb)) =
        cexp (π * I * (ε q * α (σ q) * (ta - tb))) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [← this]; ring

/-- **Continuity of the chain** with kernels and continuation depending on parameters. -/
theorem continuous_chainK_param {X : Type} [TopologicalSpace X] {P : X → ℕ → ℝ → ℝ → ℂ}
    (hP : ∀ j, Continuous fun p : X × ℝ × ℝ => P p.1 j p.2.1 p.2.2) :
    ∀ (c : LegalCode) (q : ℕ) {g : X → ℝ → ℂ} (_ : Continuous (Function.uncurry g)),
      Continuous fun p : X × ℝ => chainK (P p.1) c q p.2 (g p.1)
  | .nil, _, _, hg => hg
  | .node i r, q, g, hg => by
    simp_rw [chainK_node]
    have hR := continuous_chainK_param hP r (q + i.size + 1) hg
    have hE : Continuous fun p : (X × ℝ) × ℝ => ∫ tb in (0 : ℝ)..p.2,
        P p.1.1 q p.1.2 tb * chainK (P p.1.1) r (q + i.size + 1) tb (g p.1.1) := by
      refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : (X × ℝ) × ℝ) (tb : ℝ) =>
          P p.1.1 q p.1.2 tb * chainK (P p.1.1) r (q + i.size + 1) tb (g p.1.1)) ?_ continuous_snd
      exact ((hP q).comp (f := fun p : ((X × ℝ) × ℝ) × ℝ => (p.1.1.1, p.1.1.2, p.2)) (by fun_prop)).mul
        (hR.comp (f := fun p : ((X × ℝ) × ℝ) × ℝ => (p.1.1.1, p.2)) (by fun_prop))
    have hI := continuous_chainK_param (X := X × ℝ) (P := fun x => P x.1)
      (fun j => (hP j).comp (f := fun p : (X × ℝ) × ℝ × ℝ => (p.1.1, p.2)) (by fun_prop)) i (q + 1)
      (g := fun (x : X × ℝ) (t' : ℝ) => ∫ tb in (0 : ℝ)..t',
        P x.1 q x.2 tb * chainK (P x.1) r (q + i.size + 1) tb (g x.1)) hE
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : X × ℝ) (ta : ℝ) => chainK (P p.1) i (q + 1) ta (fun t' => ∫ tb in (0 : ℝ)..t',
        P p.1 q ta tb * chainK (P p.1) r (q + i.size + 1) tb (g p.1))) ?_ continuous_snd
    exact hI.comp (f := fun p : (X × ℝ) × ℝ => ((p.1.1, p.2), p.2)) (by fun_prop)

/-! ### The variables of a chain -/

variable [DecidableEq V]

/-- The variables of a chain: the pair variables `σ j` and the variables `SF j` of the pair
coefficients. -/
@[expose] def chainVarsF (σ : ℕ → V) (SF : ℕ → Finset V) : LegalCode → ℕ → Finset V
  | .nil, _ => ∅
  | .node i r, q => insert (σ q) (SF q ∪ chainVarsF σ SF i (q + 1) ∪ chainVarsF σ SF r (q + i.size + 1))

/-- The variables of the different factors of a chain are distinct. -/
@[expose] def ChainDisjF (σ : ℕ → V) (SF : ℕ → Finset V) : LegalCode → ℕ → Prop
  | .nil, _ => True
  | .node i r, q => σ q ∉ SF q ∪ chainVarsF σ SF i (q + 1) ∪ chainVarsF σ SF r (q + i.size + 1) ∧
      Disjoint (SF q) (chainVarsF σ SF i (q + 1)) ∧
      Disjoint (SF q ∪ chainVarsF σ SF i (q + 1)) (chainVarsF σ SF r (q + i.size + 1)) ∧
      ChainDisjF σ SF i (q + 1) ∧ ChainDisjF σ SF r (q + i.size + 1)

/-! ### The phase kernels -/

section Phase

variable {σ : ℕ → V} {ε : ℕ → ℤ} {F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ}

omit [DecidableEq V] in
theorem norm_phaseK_le {BF : ℝ} (hBF : ∀ j α, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ‖F j α t s‖ ≤ BF)
    (α : V → ℝ) (j : ℕ) {ta tb : ℝ} (hta : ta ∈ Icc (0 : ℝ) 1) (htb : tb ∈ Icc (0 : ℝ) 1) :
    ‖phaseK σ ε F α j ta tb‖ ≤ BF := by
  unfold phaseK
  rw [norm_mul, show cexp (π * I * (ε j * α (σ j) * (ta - tb))) =
    cexp (π * I * ((ε j * α (σ j) * (ta - tb) : ℝ) : ℂ)) by push_cast; ring_nf, norm_cexp_piI, one_mul]
  exact hBF j α ta hta tb htb

omit [DecidableEq V] in
theorem mass_phaseK {BF : ℝ} (hBF0 : 0 ≤ BF)
    (hBF : ∀ j α, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ‖F j α t s‖ ≤ BF) (α : V → ℝ) :
    ∀ j, ∀ ta ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc (0 : ℝ) 1, ∀ (f : ℝ → ℂ) (G : ℝ),
      (∀ y ∈ Icc (0 : ℝ) x, ‖f y‖ ≤ G) → ‖∫ tb in (0 : ℝ)..x, phaseK σ ε F α j ta tb * f tb‖ ≤
        BF * max G 0 := by
  intro j ta hta x hx f G hG
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := BF * max G 0) fun tb htb => ?_).trans ?_
  · rw [uIoc_of_le hx.1] at htb
    rw [norm_mul]
    exact mul_le_mul (norm_phaseK_le hBF α j hta ⟨htb.1.le, htb.2.trans hx.2⟩)
      ((hG tb ⟨htb.1.le, htb.2⟩).trans (le_max_left _ _)) (norm_nonneg _) hBF0
  · rw [sub_zero, abs_of_nonneg hx.1]
    nlinarith [hx.2, show 0 ≤ BF * max G 0 by positivity]

omit [DecidableEq V] in
theorem continuous_phaseK (hF : ∀ j, Continuous fun p : (V → ℝ) × ℝ × ℝ => F j p.1 p.2.1 p.2.2) (j : ℕ) :
    Continuous fun p : (V → ℝ) × ℝ × ℝ => phaseK σ ε F p.1 j p.2.1 p.2.2 := by
  unfold phaseK
  exact (Continuous.cexp (by fun_prop)).mul (hF j)

/-- The chain only sees the variables of its factors. -/
theorem chainK_phaseK_congr {SF : ℕ → Finset V}
    (hF : ∀ j t s, DependsOn (fun α => F j α t s) ↑(SF j)) :
    ∀ (c : LegalCode) (q : ℕ) {α α' : V → ℝ}, (∀ v ∈ chainVarsF σ SF c q, α v = α' v) →
      ∀ {g g' : ℝ → ℂ}, (∀ x, g x = g' x) → ∀ t,
        chainK (phaseK σ ε F α) c q t g = chainK (phaseK σ ε F α') c q t g'
  | .nil, _, _, _, _, _, _, hg, t => hg t
  | .node i r, q, α, α', h, g, g', hg, t => by
    simp only [chainK_node]
    have hP : ∀ ta tb, phaseK σ ε F α q ta tb = phaseK σ ε F α' q ta tb := by
      intro ta tb
      unfold phaseK
      have hFq : F q α ta tb = F q α' ta tb := hF q ta tb fun w hw => h w (by
        simp only [chainVarsF, Finset.mem_insert, Finset.mem_union]; tauto)
      rw [h (σ q) (by simp [chainVarsF]), hFq]
    have hr : ∀ tb, chainK (phaseK σ ε F α) r (q + i.size + 1) tb g =
        chainK (phaseK σ ε F α') r (q + i.size + 1) tb g' := fun tb =>
      chainK_phaseK_congr hF r _ (fun w hw => h w (by
        simp only [chainVarsF, Finset.mem_insert, Finset.mem_union]; tauto)) hg tb
    refine intervalIntegral.integral_congr fun ta _ => ?_
    refine chainK_phaseK_congr hF i (q + 1) (fun w hw => h w (by
      simp only [chainVarsF, Finset.mem_insert, Finset.mem_union]; tauto)) (fun x => ?_) ta
    refine intervalIntegral.integral_congr fun tb _ => ?_
    simp only [hP, hr]

end Phase

/-! ### Fubini for the chain -/

/-- The factorization at one pair: `∫ e^{πiεα_v(t_a-t_b)} F_q C w = kk · RI_q · ∫ C w`. -/
theorem mint_pair {θ : ℝ} (hθ : 0 < θ) (ζ : V → ℤ) (hζ : ∀ v, ζ v = 1 ∨ ζ v = -1) (Z : Finset V)
    {v : V} {e : ℤ} (he : e = ζ v) {Sq R : Finset V} (hv : v ∉ Sq ∪ R) (hqR : Disjoint Sq R)
    {Fq : (V → ℝ) → ℝ → ℝ → ℂ} (hFq : NiceCoef Sq Fq) {C : (V → ℝ) → ℂ} (hCd : DependsOn C ↑R)
    (hCc : Continuous C) {BC : ℝ} (hCb : ∀ α, ‖C α‖ ≤ BC) {ta tb : ℝ} (hta : ta ∈ Icc (0 : ℝ) 1)
    (htb : tb ∈ Icc (0 : ℝ) 1) :
    mint ({v} ∪ (Sq ∪ R)) (fun α => cexp (π * I * (e * α v * (ta - tb))) * Fq α ta tb * C α *
        wgt θ ζ Z ({v} ∪ (Sq ∪ R)) α) 0 =
      (kk (decide (v ∈ Z)) θ (ta - tb) : ℂ) * RI θ ζ Z Sq Fq ta tb *
        mint R (fun α => C α * wgt θ ζ Z R α) 0 := by
  obtain ⟨BF, hBF⟩ := hFq.bdd
  have hev : e = 1 ∨ e = -1 := he ▸ hζ v
  have hph : DependsOn (fun α : V → ℝ => cexp (π * I * (e * α v * (ta - tb)))) ↑({v} : Finset V) := by
    intro α α' h; simp only; rw [h v (by simp)]
  have hphc : Continuous fun α : V → ℝ => cexp (π * I * (e * α v * (ta - tb))) := by fun_prop
  have hphb : ∀ α : V → ℝ, ‖cexp (π * I * (e * α v * (ta - tb)))‖ ≤ 1 := fun α => by
    rw [show cexp (π * I * (e * α v * (ta - tb))) = cexp (π * I * ((e * α v * (ta - tb) : ℝ) : ℂ)) by
      push_cast; ring_nf, norm_cexp_piI]
  have hFd : DependsOn (fun α => Fq α ta tb) ↑Sq := hFq.dep ta tb
  have hFc : Continuous fun α => Fq α ta tb := continuous_at_times hFq.cont ta tb
  have hFb : ∀ α, ‖Fq α ta tb‖ ≤ BF := fun α => hBF α ta hta tb htb
  have hgd : DependsOn (fun α => Fq α ta tb * C α) ↑(Sq ∪ R) :=
    dependsOn_mul (dependsOn_mono hFd (Finset.coe_subset.2 Finset.subset_union_left))
      (dependsOn_mono hCd (Finset.coe_subset.2 Finset.subset_union_right))
  have hgb : ∀ α, ‖Fq α ta tb * C α‖ ≤ max BF 0 * max BC 0 := fun α => by
    rw [norm_mul]
    exact mul_le_mul ((hFb α).trans (le_max_left _ _)) ((hCb α).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  have hdv : Disjoint ({v} : Finset V) (Sq ∪ R) := Finset.disjoint_singleton_left.2 hv
  have e1 : (fun α => cexp (π * I * (e * α v * (ta - tb))) * Fq α ta tb * C α *
      wgt θ ζ Z ({v} ∪ (Sq ∪ R)) α) = fun α => cexp (π * I * (e * α v * (ta - tb))) *
        (Fq α ta tb * C α) * wgt θ ζ Z ({v} ∪ (Sq ∪ R)) α := by
    funext α; ring
  have hph1 := mint_phase_wgt hθ ζ Z v hev (ta - tb) 0
  push_cast at hph1
  rw [e1, (mint_mul_wgt hθ ζ Z hdv hph hgd hphc (hFc.mul hCc) hphb hgb 0).2,
    (mint_mul_wgt hθ ζ Z hqR hFd hCd hFc hCc hFb hCb 0).2, hph1]
  have hz : (ζ v * e : ℂ) = 1 := by
    rw [he]; rcases hζ v with h | h <;> simp [h]
  by_cases hvZ : v ∈ Z
  · simp only [hvZ, ite_true, hz, one_mul, kk, decide_true]
    unfold RI; ring
  · simp only [hvZ, ite_false, kk, decide_false, Bool.false_eq_true]
    unfold RI; ring

/-- **Fubini for the chain** (DH21 (newexp2) under (gausspv)). -/
theorem mint_chain {θ : ℝ} (hθ : 0 < θ) (ζ : V → ℤ) (hζ : ∀ v, ζ v = 1 ∨ ζ v = -1) (Z : Finset V)
    {σ : ℕ → V} {ε : ℕ → ℤ} (hεζ : ∀ j, ε j = ζ (σ j))
    {F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ} {SF : ℕ → Finset V} (hF : ∀ j, NiceCoef (SF j) (F j))
    {BF : ℝ} (hBF0 : 0 ≤ BF)
    (hBF : ∀ j α, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ‖F j α t s‖ ≤ BF) :
    ∀ (c : LegalCode) (q : ℕ), ChainDisjF σ SF c q → ∀ {B : Finset V},
      Disjoint (chainVarsF σ SF c q) B → ∀ {g : (V → ℝ) → ℝ → ℂ},
      (∀ x, DependsOn (fun α => g α x) ↑B) → Continuous (Function.uncurry g) → ∀ {G : ℝ}, 0 ≤ G →
      (∀ α, ∀ x ∈ Icc (0 : ℝ) 1, ‖g α x‖ ≤ G) → ∀ t ∈ Icc (0 : ℝ) 1,
      mint (chainVarsF σ SF c q ∪ B) (fun α => chainK (phaseK σ ε F α) c q t (g α) *
          wgt θ ζ Z (chainVarsF σ SF c q ∪ B) α) 0 =
        chainK (fun j ta tb => (kk (decide (σ j ∈ Z)) θ (ta - tb) : ℂ) *
          RI θ ζ Z (SF j) (F j) ta tb) c q t (fun x => mint B (fun α => g α x * wgt θ ζ Z B α) 0)
  | .nil, _, _, B, _, g, _, _, _, _, _, t, _ => by
    simp only [chainVarsF, Finset.empty_union, chainK_nil]
  | .node i r, q, hd, B, hB, g, hgd, hgc, G, hG0, hgb, t, ht => by
    obtain ⟨hv, hqi, hqir, hdi, hdr⟩ := hd
    set Pr : ℕ → ℝ → ℝ → ℂ := fun j ta tb => (kk (decide (σ j ∈ Z)) θ (ta - tb) : ℂ) *
      RI θ ζ Z (SF j) (F j) ta tb with hPr
    set Sq := SF q with hSq
    set Si := chainVarsF σ SF i (q + 1) with hSi
    set Sr := chainVarsF σ SF r (q + i.size + 1) with hSr
    set B' := {σ q} ∪ (Sq ∪ (Sr ∪ B)) with hB'
    have hS : chainVarsF σ SF (.node i r) q = insert (σ q) (Sq ∪ Si ∪ Sr) := rfl
    have hSB : chainVarsF σ SF (.node i r) q ∪ B = Si ∪ B' := by
      rw [hS, hB']; ext w; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    have hBS : Disjoint (insert (σ q) (Sq ∪ Si ∪ Sr)) B := hS ▸ hB
    have hiB' : Disjoint Si B' := by
      rw [hB', Finset.disjoint_union_right, Finset.disjoint_union_right, Finset.disjoint_union_right]
      refine ⟨Finset.disjoint_singleton_right.2 fun h => hv (by simp [h]), hqi.symm,
        Finset.disjoint_of_subset_left Finset.subset_union_right hqir, ?_⟩
      exact Finset.disjoint_of_subset_left (by intro w hw; simp [hw]) hBS
    have hrB : Disjoint Sr B := Finset.disjoint_of_subset_left (by intro w hw; simp [hw]) hBS
    have hqrB : Disjoint Sq (Sr ∪ B) := Finset.disjoint_union_right.2
      ⟨Finset.disjoint_of_subset_left Finset.subset_union_left hqir,
        Finset.disjoint_of_subset_left (by intro w hw; simp [hw]) hBS⟩
    have hvqrB : σ q ∉ Sq ∪ (Sr ∪ B) := by
      intro h
      simp only [Finset.mem_union] at h
      rcases h with h | h | h
      · exact hv (by simp [h])
      · exact hv (by simp [h])
      · exact Finset.disjoint_left.1 hBS (Finset.mem_insert_self _ _) h
    have hPc := fun j => continuous_phaseK (σ := σ) (ε := ε) (fun j => (hF j).cont) j
    have hm := mass_phaseK (σ := σ) (ε := ε) hBF0 hBF
    -- the rest of the chain
    set C : (V → ℝ) → ℝ → ℂ := fun α tb => chainK (phaseK σ ε F α) r (q + i.size + 1) tb (g α)
      with hC
    have hCc : Continuous fun p : (V → ℝ) × ℝ => C p.1 p.2 :=
      continuous_chainK_param (X := V → ℝ) (P := phaseK σ ε F) hPc r _ hgc
    have hCb : ∀ α, ∀ tb ∈ Icc (0 : ℝ) 1, ‖C α tb‖ ≤ BF ^ r.size * G := fun α tb htb =>
      norm_chainK_le hBF0 (hm α) r _ hG0 (hgb α) tb htb
    have hCd : ∀ tb, DependsOn (fun α => C α tb) ↑(Sr ∪ B) := by
      intro tb α α' h
      exact chainK_phaseK_congr (fun j => (hF j).dep) r _
        (fun w hw => h w (Finset.mem_coe.2 (Finset.mem_union_left _ hw)))
        (fun x => hgd x fun w hw => h w (Finset.mem_coe.2 (Finset.mem_union_right _
          (Finset.mem_coe.1 hw)))) tb
    -- the continuation of the inner block
    set k : (V → ℝ) → ℝ → ℝ → ℂ := fun α ta x => ∫ tb in (0 : ℝ)..x, phaseK σ ε F α q ta tb * C α tb
      with hk
    have hkc : Continuous fun p : ((V → ℝ) × ℝ) × ℝ => k p.1.1 p.1.2 p.2 :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : ((V → ℝ) × ℝ) × ℝ) tb => phaseK σ ε F p.1.1 q p.1.2 tb * C p.1.1 tb)
        (((hPc q).comp (f := fun p : (((V → ℝ) × ℝ) × ℝ) × ℝ => (p.1.1.1, p.1.1.2, p.2))
          (by fun_prop)).mul (hCc.comp (f := fun p : (((V → ℝ) × ℝ) × ℝ) × ℝ => (p.1.1.1, p.2))
          (by fun_prop))) continuous_snd
    have hkb : ∀ α, ∀ ta ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc (0 : ℝ) 1, ‖k α ta x‖ ≤ BF * (BF ^ r.size * G) := by
      intro α ta hta x hx
      have := hm α q ta hta x hx (C α) (BF ^ r.size * G) fun y hy => hCb α y ⟨hy.1, hy.2.trans hx.2⟩
      rwa [max_eq_left (by positivity)] at this
    have hkd : ∀ ta x, DependsOn (fun α => k α ta x) ↑B' := by
      intro ta x α α' h
      simp only [hk]
      refine intervalIntegral.integral_congr fun tb _ => ?_
      show phaseK σ ε F α q ta tb * C α tb = phaseK σ ε F α' q ta tb * C α' tb
      have hFq : F q α ta tb = F q α' ta tb := (hF q).dep ta tb fun w hw => by
        have hw' : w ∈ Sq := Finset.mem_coe.1 hw
        exact h w (Finset.mem_coe.2 (by rw [hB']; simp [hw']))
      have hCq : C α tb = C α' tb := hCd tb fun w hw =>
        h w (Finset.mem_coe.2 (by
          rw [hB']
          rcases Finset.mem_union.1 (Finset.mem_coe.1 hw) with h' | h' <;> simp [h']))
      unfold phaseK
      rw [h (σ q) (Finset.mem_coe.2 (by rw [hB']; simp)), hFq, hCq]
    -- Step 1: Fubini in the outer time
    have hIc : Continuous fun p : (V → ℝ) × ℝ =>
        chainK (phaseK σ ε F p.1) i (q + 1) p.2 (k p.1 p.2) := by
      have h := continuous_chainK_param (X := (V → ℝ) × ℝ) (P := fun x => phaseK σ ε F x.1)
        (fun j => (hPc j).comp (f := fun p : ((V → ℝ) × ℝ) × ℝ × ℝ => (p.1.1, p.2)) (by fun_prop))
        i (q + 1) (g := fun x => k x.1 x.2) hkc
      exact h.comp (f := fun p : (V → ℝ) × ℝ => (p, p.2)) (by fun_prop)
    have hIb : ∀ α, ∀ ta ∈ Icc (0 : ℝ) 1,
        ‖chainK (phaseK σ ε F α) i (q + 1) ta (k α ta)‖ ≤ BF ^ i.size * (BF * (BF ^ r.size * G)) :=
      fun α ta hta => norm_chainK_le hBF0 (hm α) i (q + 1) (by positivity) (hkb α ta hta) ta hta
    have hwI := (mInt_wgt hθ ζ Z (chainVarsF σ SF (.node i r) q ∪ B) 0).norm
    have h1 : mint (chainVarsF σ SF (.node i r) q ∪ B) (fun α =>
        chainK (phaseK σ ε F α) (.node i r) q t (g α) * wgt θ ζ Z (chainVarsF σ SF (.node i r) q ∪ B) α) 0 =
        ∫ ta in (0 : ℝ)..t, mint (chainVarsF σ SF (.node i r) q ∪ B) (fun α =>
          chainK (phaseK σ ε F α) i (q + 1) ta (k α ta) *
            wgt θ ζ Z (chainVarsF σ SF (.node i r) q ∪ B) α) 0 := by
      have e : (fun α => chainK (phaseK σ ε F α) (.node i r) q t (g α) *
          wgt θ ζ Z (chainVarsF σ SF (.node i r) q ∪ B) α) = fun α => ∫ ta in (0 : ℝ)..t,
            chainK (phaseK σ ε F α) i (q + 1) ta (k α ta) *
              wgt θ ζ Z (chainVarsF σ SF (.node i r) q ∪ B) α := by
        funext α
        rw [chainK_node, ← intervalIntegral.integral_mul_const]
      rw [e]
      refine mint_intervalIntegral 0 (hIc.mul ((continuous_wgt θ ζ Z _).comp continuous_fst))
        (ψ := fun α => BF ^ i.size * (BF * (BF ^ r.size * G)) *
          ‖wgt θ ζ Z (chainVarsF σ SF (.node i r) q ∪ B) α‖) (fun α τ hτ => ?_) (hwI.const_mul _)
      rw [uIcc_of_le ht.1] at hτ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hIb α τ ⟨hτ.1, hτ.2.trans ht.2⟩) (norm_nonneg _)
    rw [h1, chainK_node]
    refine intervalIntegral.integral_congr fun ta hta => ?_
    rw [uIcc_of_le ht.1] at hta
    have hta' : ta ∈ Icc (0 : ℝ) 1 := ⟨hta.1, hta.2.trans ht.2⟩
    -- Step 2: the inner chain
    have hIH := mint_chain hθ ζ hζ Z hεζ hF hBF0 hBF i (q + 1) hdi hiB' (g := fun α => k α ta)
      (fun x => hkd ta x) (hkc.comp (f := fun p : (V → ℝ) × ℝ => ((p.1, ta), p.2)) (by fun_prop))
      (by positivity : 0 ≤ BF * (BF ^ r.size * G)) (fun α x hx => hkb α ta hta' x hx) ta hta'
    rw [hSB, hIH]
    refine chainK_congr i (q + 1) (fun _ _ _ _ _ _ _ => rfl) (fun x hx => ?_) ta hta'
    -- Step 3: the continuation
    have hwB' := (mInt_wgt hθ ζ Z B' 0).norm
    have h3 : mint B' (fun α => k α ta x * wgt θ ζ Z B' α) 0 =
        ∫ tb in (0 : ℝ)..x, mint B' (fun α => phaseK σ ε F α q ta tb * C α tb * wgt θ ζ Z B' α) 0 := by
      have e : (fun α => k α ta x * wgt θ ζ Z B' α) = fun α => ∫ tb in (0 : ℝ)..x,
          phaseK σ ε F α q ta tb * C α tb * wgt θ ζ Z B' α := by
        funext α; simp only [hk]; rw [← intervalIntegral.integral_mul_const]
      rw [e]
      refine mint_intervalIntegral 0 ((((hPc q).comp (continuous_fst.prodMk
        ((continuous_const : Continuous fun _ : (V → ℝ) × ℝ => ta).prodMk continuous_snd))).mul hCc).mul
          ((continuous_wgt θ ζ Z B').comp continuous_fst))
        (ψ := fun α => BF * (BF ^ r.size * G) * ‖wgt θ ζ Z B' α‖) (fun α τ hτ => ?_) (hwB'.const_mul _)
      rw [uIcc_of_le hx.1] at hτ
      have hτ' : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1, hτ.2.trans hx.2⟩
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (norm_phaseK_le hBF α q hta' hτ') (hCb α τ hτ')
        (norm_nonneg _) hBF0) (norm_nonneg _)
    show mint B' (fun α => k α ta x * wgt θ ζ Z B' α) 0 = _
    rw [h3]
    refine intervalIntegral.integral_congr fun tb htb => ?_
    rw [uIcc_of_le hx.1] at htb
    have htb' : tb ∈ Icc (0 : ℝ) 1 := ⟨htb.1, htb.2.trans hx.2⟩
    -- Step 4: the pair
    have hpair := mint_pair hθ ζ hζ Z (hεζ q) hvqrB hqrB (hF q) (hCd tb)
      (hCc.comp (continuous_id.prodMk continuous_const)) (fun α => hCb α tb htb') hta' htb'
    have hIHr := mint_chain hθ ζ hζ Z hεζ hF hBF0 hBF r _ hdr hrB hgd hgc hG0 hgb tb htb'
    show mint B' (fun α => phaseK σ ε F α q ta tb * C α tb * wgt θ ζ Z B' α) 0 = Pr q ta tb * _
    simp only [phaseK, hB'] at hpair ⊢
    rw [hpair, hIHr]

end WaveTurbulence.Cancel
