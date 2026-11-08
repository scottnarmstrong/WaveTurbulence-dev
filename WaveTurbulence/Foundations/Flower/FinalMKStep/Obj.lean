/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKStep.State

/-! # C1a SURV-STEP (3): the re-cut potential step from the object data (`hW_RC'p`)

The true increments of a re-cut `h ↦ h.vinePostG K` with exactly one `α/β` joint of degree `2` (the shared joint
of o75 75-F2; the other joint is `ε`, of any degree `≥ 2`):

* `ΔF = -jeps K` (`numComponents_vineStRC`): the new component is the isolated (deleted) half of the re-cut joint;
  when the `ε` joint has degree `2` too, the whole component goes (`ΔF = -1`, index `-1`);
* `ΔV_β ≤ 1 - jeps K` (`vBeta_vineStRC`);
* `apProd` does not decrease (`apProd_le_vineStRC`, the label refund; `α` labels are `≤ L^{-γ+η}`, so the factor
  `L^{(γ+3η)/2-κη} R ≤ 1` once `5η ≤ γ`).

`hW_RC'p` is `hW_RCp` with these increments (main's `hW_D1'p` for the re-cut). The pending-re-cut drop `hpend` is the
run's bookkeeping (C1b1); `pendRC_step` reduces it to the dartless facts of one survivor removal. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section label
variable {L γ η : ℝ}

/-- **An `α` factor is at most `1`**: `L^{(γ+3η)/2-κη} R ≤ L^{(-γ+5η)/2} ≤ 1` for a label `R ≤ L^{-γ+η}`. -/
theorem apFactor_le_one (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hγη : 5 * η ≤ γ) {c : Cls}
    (hc : ∀ R kp, c = .alpha R kp → IsLabel L γ η R) : apFactor L γ η c ≤ 1 := by
  have hL : 0 < L := by linarith
  cases c with
  | alpha R kp =>
    obtain ⟨-, hR0, hR⟩ := hc R kp rfl
    have hRpos : 0 ≤ R := le_trans (inv_nonneg.2 hL.le) hR0
    show L ^ ((γ + 3 * η) / 2 - (kp : ℝ) * η) * R ≤ 1
    have hk : (0 : ℝ) ≤ (kp : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) hη
    have h1 : L ^ ((γ + 3 * η) / 2 - (kp : ℝ) * η) ≤ L ^ ((γ + 3 * η) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    calc L ^ ((γ + 3 * η) / 2 - (kp : ℝ) * η) * R ≤ L ^ ((γ + 3 * η) / 2) * L ^ (-γ + η) :=
          mul_le_mul h1 hR hRpos (by positivity)
      _ = L ^ ((-γ + 5 * η) / 2) := by rw [← Real.rpow_add hL]; congr 1; ring
      _ ≤ L ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = 1 := Real.rpow_zero L
  | eps => show (1 : ℝ) ≤ 1; exact le_rfl
  | beta => show (1 : ℝ) ≤ 1; exact le_rfl
  | ghost => show (1 : ℝ) ≤ 1; exact le_rfl

theorem apFactor_nonneg (hL : 0 < L) {c : Cls} (hc : ∀ R kp, c = .alpha R kp → 0 < R) : 0 ≤ apFactor L γ η c := by
  cases c with
  | alpha R kp => exact mul_nonneg (by positivity) (hc R kp rfl).le
  | eps => exact zero_le_one
  | beta => exact zero_le_one
  | ghost => exact zero_le_one

/-- The labels of the present `α` atoms (from main's record invariant `HInv`). -/
theorem labels_of_hinv {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h : HSt V D₀} (hI : HInv L γ η w κ h) :
    ∀ a ∈ h.s.M.atoms, ∀ R kp, h.s.cls a = .alpha R kp → IsLabel L γ η R :=
  fun a ha R kp hc => ((hI.ok a ha).1 R kp hc).1

end label

section vals
variable (s : St.{u} V D₀) (K : VineCut s.M)

theorem apProd_vineStRC_mul (L γ η : ℝ) :
    apProd L γ η (vineStG s K) * ∏ a ∈ K.C.atoms, apFactor L γ η (s.cls a) = apProd L γ η s := by
  unfold apProd
  rw [prod_vineStG' s K (apFactor L γ η)]
  have h1 : apFactor L γ η .beta = 1 := rfl
  simp [h1]

/-- **The label refund**: a re-cut does not decrease `apProd` (the removed joints have factors `≤ 1`). -/
theorem apProd_le_vineStRC {L γ η : ℝ} (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hγη : 5 * η ≤ γ) (hap : ApPos s)
    (hlab : ∀ a ∈ s.M.atoms, ∀ R kp, s.cls a = .alpha R kp → IsLabel L γ η R) :
    apProd L γ η s ≤ apProd L γ η (vineStG s K) := by
  have hL : 0 < L := by linarith
  have hpos := apProd_pos (L := L) (γ := γ) (η := η) hL (apPos_vineStG s K hap)
  have hle : ∏ a ∈ K.C.atoms, apFactor L γ η (s.cls a) ≤ 1 := by
    refine Finset.prod_le_one₀ (fun a ha => apFactor_nonneg hL (hap a (objectAtoms_sub K.C ha))) fun a ha => ?_
    exact apFactor_le_one hL1 hη hγη (hlab a (objectAtoms_sub K.C ha))
  rw [← apProd_vineStRC_mul s K L γ η]
  calc apProd L γ η (vineStG s K) * ∏ a ∈ K.C.atoms, apFactor L γ η (s.cls a) ≤ apProd L γ η (vineStG s K) * 1 :=
        mul_le_mul_of_nonneg_left hle hpos.le
    _ = _ := mul_one _

/-- **`β` count after a re-cut**: `V_β' + jdeg2 + (removed β joints) = V_β + 2`. -/
theorem vBeta_vineStRC :
    vBeta (vineStG s K) + jdeg2 K + (K.C.atoms.filter fun a => s.cls a = .beta).card = vBeta s + 2 := by
  have key := prod_vineStG' (α := Multiplicative ℕ) s K (fun x => Multiplicative.ofAdd (if x = Cls.beta then 1 else 0))
  have hv : ∀ t : St.{u} V D₀, vBeta t = ∑ a ∈ t.M.atoms, (if t.cls a = Cls.beta then 1 else 0) := by
    intro t; unfold vBeta; rw [Finset.card_filter]
  have hc : (K.C.atoms.filter fun a => s.cls a = .beta).card = ∑ a ∈ K.C.atoms, (if s.cls a = Cls.beta then 1 else 0) := by
    rw [Finset.card_filter]
  rw [hv, hv, hc]
  have := congrArg Multiplicative.toAdd key
  simp only [toAdd_prod, toAdd_mul, apply_ite Multiplicative.toAdd, toAdd_one, toAdd_ofAdd] at this
  unfold jdeg2
  by_cases h1 : s.M.deg K.C.lower = 2 <;> by_cases h2 : s.M.deg K.C.upper = 2 <;> simp [h1, h2] at this ⊢ <;> omega

theorem vBeta_vineStRC_le : vBeta (vineStG s K) + jdeg2 K ≤ vBeta s + 2 := by
  have := vBeta_vineStRC s K; omega

/-- **Components after a removal with a degree-`2` joint**: `F' + jdeg2 = F + 1`. -/
theorem numComponents_vineStRC (hd2 : s.M.deg K.C.upper = 2 ∨ s.M.deg K.C.lower = 2) :
    (vineStG s K).M.numComponents + jdeg2 K = s.M.numComponents + 1 := by
  have h1 := numComponents_vineStG K
  have h2 := vineCut_F_lt K hd2
  have h3 := vine_F_le_succ K
  omega

/-- **The whole-component removal** (both joints of degree `2`): the object with its joints is a whole component and
disappears with its two ghost halves, `F' + 1 = F`. -/
theorem numComponents_vineStRC_two (hu2 : s.M.deg K.C.upper = 2) (hl2 : s.M.deg K.C.lower = 2) :
    (vineStG s K).M.numComponents + 1 = s.M.numComponents := by
  have h1 := numComponents_vineStRC s K (Or.inl hu2)
  have h2 : jdeg2 K = 2 := by unfold jdeg2; simp [hu2, hl2]
  omega

/-- With exactly one `α/β` joint, `jdeg2 = jeps + 1`. -/
theorem jdeg2_eq_of_one (hu : RCJoint s K.C.upper) (hl : RCJoint s K.C.lower)
    (hrc : s.cls K.C.upper ≠ .eps ∨ s.cls K.C.lower ≠ .eps) (hone : s.cls K.C.upper = .eps ∨ s.cls K.C.lower = .eps) :
    jdeg2 K = jeps K + 1 := by
  unfold jdeg2 jeps jepsAt
  rcases hrc with hu' | hl'
  · have h2 := (hu.resolve_left hu').2
    have hle : s.cls K.C.lower = .eps := hone.resolve_left hu'
    by_cases hd : s.M.deg K.C.lower = 2 <;> simp [h2, hu', hle, hd]
  · have h2 := (hl.resolve_left hl').2
    have hue : s.cls K.C.upper = .eps := hone.resolve_right hl'
    by_cases hd : s.M.deg K.C.upper = 2 <;> simp [h2, hl', hue, hd]

end vals

section pend
variable {M₀ : Molecule V D₀} {m : ℕ}

/-- **One pending re-cut is paid** when survivor `i` (which shares an atom with an earlier survivor) is removed and no
survivor regains darts. -/
theorem pendRC_step (E : Fin m → Object M₀) {h h' : HSt V D₀} (i : Fin m)
    (hmono : ∀ k, Dartless (E k) h → Dartless (E k) h') (hi : ¬ Dartless (E i) h) (hi' : Dartless (E i) h')
    (hj : ∃ j, j < i ∧ ¬ Disjoint (E j).atoms (E i).atoms) : pendRC E h' + 1 ≤ pendRC E h := by
  unfold pendRC
  have hsub : (Finset.univ.filter fun k : Fin m => ¬ Dartless (E k) h' ∧ ∃ j, j < k ∧ ¬ Disjoint (E j).atoms (E k).atoms) ⊆
      (Finset.univ.filter fun k : Fin m => ¬ Dartless (E k) h ∧ ∃ j, j < k ∧ ¬ Disjoint (E j).atoms (E k).atoms).erase i := by
    intro k hk
    rw [Finset.mem_filter] at hk
    refine Finset.mem_erase.2 ⟨fun e => hk.2.1 (e ▸ hi'), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, hk.2.2⟩⟩
    exact fun hd => hk.2.1 (hmono k hd)
  have hmem : i ∈ (Finset.univ.filter fun k : Fin m => ¬ Dartless (E k) h ∧ ∃ j, j < k ∧ ¬ Disjoint (E j).atoms (E k).atoms) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hi, hj⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmem] at h1
  have h2 := Finset.card_pos.2 ⟨i, hmem⟩
  omega

end pend

section hwrc
variable {L γ η : ℝ} {M₀ : Molecule V D₀} {m : ℕ}

/-- **C1a: the potential inequality of the re-cut step from the object data** (main's `hW_D1'p` for a re-cut with
exactly one `α/β` joint of degree `2`; the other joint is `ε` of any degree, including degree `2`: the whole-component
removal). `ΔF`, `ΔV_β`, `apProd`, `ρ`, the critical count and the index of `vinePostG K` are computed. -/
theorem hW_RC'p (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ))
    (hmarg : 2 * min γ (1 - γ) + 4 * η ^ 2 ≤ 1) (hγη : 5 * η ≤ γ) (ε0 : ℝ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2)
    (crit : V → Prop) (Fmax : ℝ) (E : Fin m → Object M₀)
    {h : HSt V D₀} (K : VineCut h.s.M) {R : ℕ} (hI : Inv R h.s) (hap : ApPos h.s)
    (hlab : ∀ a ∈ h.s.M.atoms, ∀ R kp, h.s.cls a = .alpha R kp → IsLabel L γ η R)
    (hu : RCJoint h.s K.C.upper) (hl : RCJoint h.s K.C.lower)
    (hrc : h.s.cls K.C.upper ≠ .eps ∨ h.s.cls K.C.lower ≠ .eps)
    (hone : h.s.cls K.C.upper = .eps ∨ h.s.cls K.C.lower = .eps)
    (hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a)
    (hM : ∀ x ∈ h.s.M.atoms, h.s.M.deg x ≤ 4)
    (hloss : ladderLoss h.s.M (h.s.M.atoms.filter (fun a => a ∉ K.C.atoms)) ≤ 86)
    (hpend : pendRC E (h.vinePostG K) + 1 ≤ pendRC E h) {CN : ℝ} (hCN : 0 ≤ CN) (N : ℕ)
    (hN : (N : ℝ) * CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)))) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (CN * excessRHS2 L γ η [] 1 2) *
      WPot L γ η (Yp (RofS (h.vinePostG K).s)) (g1E γ η crit Fmax E) (h.vinePostG K)) ≤
      WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h := by
  obtain ⟨R', e, hI'⟩ := Inv.vineStRC hI K hu hl
  have hs : (h.vinePostG K).s = vineStG h.s K := rfl
  have hd2 := rc_deg_two K hu hl hrc
  have hFc := numComponents_vineStRC h.s K hd2
  have hVc := vBeta_vineStRC_le h.s K
  have hjj := jdeg2_eq_of_one h.s K hu hl hrc hone
  have hρ := rho_vineStG_le K hM hloss
  refine hW_RCp hL1 hη hη40 hγ0 hmarg ε0 Yp hYp0 hYpd hε0 crit Fmax E (j := jeps K) (R := R) (R' := R') e hI
    (by rw [hs]; exact hI') hap ?_ ?_ ?_ ?_ ?_ hpend hCN N hN
  · rw [hs]; exact apProd_le_vineStRC h.s K hL1 hη hγη hap hlab
  · rw [hs]
    have : (vineStG h.s K).M.numComponents + jeps K = h.s.M.numComponents := by omega
    have : ((vineStG h.s K).M.numComponents : ℝ) + jeps K = h.s.M.numComponents := by exact_mod_cast this
    linarith
  · rw [hs]
    have : vBeta (vineStG h.s K) + jeps K ≤ vBeta h.s + 1 := by omega
    exact_mod_cast this
  · rw [hs]; omega
  · rw [hs]; exact critCount_vineStG h.s K crit hint

/-- `hW_RC'p` under main's smallness hypothesis `8η ≤ 2γ - 1` (which gives both margins). -/
theorem hW_RC'p_h8 (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ))
    (h8 : 8 * η ≤ 2 * γ - 1) (ε0 : ℝ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2)
    (crit : V → Prop) (Fmax : ℝ) (E : Fin m → Object M₀)
    {h : HSt V D₀} (K : VineCut h.s.M) {R : ℕ} (hI : Inv R h.s) (hap : ApPos h.s)
    (hlab : ∀ a ∈ h.s.M.atoms, ∀ R kp, h.s.cls a = .alpha R kp → IsLabel L γ η R)
    (hu : RCJoint h.s K.C.upper) (hl : RCJoint h.s K.C.lower)
    (hrc : h.s.cls K.C.upper ≠ .eps ∨ h.s.cls K.C.lower ≠ .eps)
    (hone : h.s.cls K.C.upper = .eps ∨ h.s.cls K.C.lower = .eps)
    (hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a)
    (hM : ∀ x ∈ h.s.M.atoms, h.s.M.deg x ≤ 4)
    (hloss : ladderLoss h.s.M (h.s.M.atoms.filter (fun a => a ∉ K.C.atoms)) ≤ 86)
    (hpend : pendRC E (h.vinePostG K) + 1 ≤ pendRC E h) {CN : ℝ} (hCN : 0 ≤ CN) (N : ℕ)
    (hN : (N : ℝ) * CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)))) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (CN * excessRHS2 L γ η [] 1 2) *
      WPot L γ η (Yp (RofS (h.vinePostG K).s)) (g1E γ η crit Fmax E) (h.vinePostG K)) ≤
      WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h :=
  hW_RC'p hL1 hη hη40 hγ0 (hmarg_of_h8 hη hη40 h8) (by linarith) ε0 Yp hYp0 hYpd hε0 crit Fmax E K hI hap hlab
    hu hl hrc hone hint hM hloss hpend hCN N hN

end hwrc

end WaveTurbulence.Flower.FinalMKStep
