/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.ThmAOps
import Mathlib.Tactic

/-! # Theorem A: DH23 Prop 9.6, case (4), T-type components, `1/2 < γ < 1`

Case-4 note `docs/research/case4-gamma-above-half.txt` §4. A case-(4) component `𝕄₀` has two β-atoms `b, b′` (in = out =
1) on chains between distinct atoms; `𝕄₁` is `𝕄₀` with each chain replaced by one bond (operation (d)). If `𝕄₁`
(Y)-reduces to `T` by complete (Y2) sequences:
1. operation (c) on the first chain (deviation `(log L)^C L^{γ₀}`, `γ₀ = 1 − γ`);
2. operation (d) on the second chain (deviation `(log L)^C`); the result is `𝕄₁ ∖ ℓ` (`ℓ` = the bond of the first chain);
3. ylem2 along the route, carrying the missing bond (`route_bound`, at most two sequences);
4. `T ∖ ℓ*` by DH23 Lemma A.3(4), `γ > 1/2` (`tMinus_afree`): `L^{−γ₀−κ(γ)}`.
Total: `(log L)^C L^{γ₀} · L^{−γ₀−κ(γ)} ≤ L^{−κ(γ)/2}` for large `L`, `κ(γ) = min((2γ−1)/3, 1−γ)`.

`theorem_A` treats two chains `u → b → v`, `u′ → b′ → v′`; `theorem_A_one` the single chain `u → b → b′ → v`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem YRouteT.isT_of_zero {M : Molecule V D} (h : YRouteT 0 M) : IsT M := by
  cases h with
  | done _ hT => exact hT

theorem YRouteT.inv_succ {M : Molecule V D} {k : ℕ} (h : YRouteT (k + 1) M) :
    ∃ (hcap : ∀ w ∈ M.atoms, M.outdeg w ≤ 2 ∧ M.indeg w ≤ 2) (C : YChain M) (E : Y2End C),
      M.bondsBetween (M.atom (M.mate E.x)) (M.atom (M.mate E.y)) ≠ 2 ∧ YRouteT k (E.toTwoExit hcap).post := by
  cases h with
  | y2 _ _ hcap C E hc h' => exact ⟨hcap, C, E, hc, h'⟩

theorem ennreal_le_sq_mul {a b : ℝ≥0∞} (ha : 1 ≤ a) : a * b ≤ a ^ 2 * b :=
  calc a * b ≤ a * (a * b) := mul_le_mul' le_rfl (le_mul_of_one_le_left bot_le ha)
    _ = a ^ 2 * b := by rw [← mul_assoc, ← sq]

theorem ofReal_mul_ofReal_mul {x y : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal x * ENNReal.ofReal (x * y) = ENNReal.ofReal x ^ 2 * ENNReal.ofReal y := by
  rw [ENNReal.ofReal_mul hx, ← mul_assoc, ← sq]

/-- **Steps 3–4: a route of at most two (Y2) sequences to `T`.** -/
theorem route_bound {d : ℕ} {L γ δ η C1 Kt : ℝ}
    (hK : 1 ≤ 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6)
    (hs1 : Ylem2SecondAt.{u, v} d L γ δ η C1) (hn1 : Ylem2NotRemovedAt.{u, v} d L γ δ η C1)
    (hs2 : Ylem2SecondAt.{u, v} d L γ δ (η / 2) C1) (hn2 : Ylem2NotRemovedAt.{u, v} d L γ δ (η / 2) C1)
    (hbase : ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), IsT M →
      (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      ∀ (e : D) (η' : ℝ) (P : Finset V → ℝ), AFree (MoleProp.eraseBond M e) d L γ δ η' C1 P ≤ ENNReal.ofReal Kt)
    (M : Molecule V D) (k : ℕ) (hk : k ≤ 2) (hroute : YRouteT k M)
    (hcap : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (h4 : ∀ a ∈ M.atoms, M.deg a = 4) (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (e : D) (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) :
    AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
      ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 * ENNReal.ofReal Kt := by
  have hK1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hK
  have hK2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 :=
    one_le_pow₀ hK1
  match k, hk, hroute with
  | 0, _, hroute =>
    exact (hbase M hroute.isT_of_zero hcap hloop e η P).trans (le_mul_of_one_le_left bot_le hK2)
  | 1, _, hroute =>
    obtain ⟨hcap', C, E, _, hroute'⟩ := hroute.inv_succ
    obtain ⟨hcapP, hloopP, _, _⟩ := E.post_props hcap' hloop h4 hconn
    have hT' := hroute'.isT_of_zero
    refine (route_step hs1 hn1 M hcap' h4 hconn C E (X := Kt) (fun e₁ P' _ => hbase _ hT' hcapP hloopP e₁ _ P') e P
      hP).trans ?_
    exact ennreal_le_sq_mul hK1
  | 2, _, hroute =>
    obtain ⟨hcap', C, E, _, hroute'⟩ := hroute.inv_succ
    obtain ⟨hcapP, hloopP, h4P, hconnP⟩ := E.post_props hcap' hloop h4 hconn
    obtain ⟨hcap'', C', E', _, hroute''⟩ := hroute'.inv_succ
    obtain ⟨hcapQ, hloopQ, _, _⟩ := E'.post_props hcap'' hloopP h4P hconnP
    have hT'' := hroute''.isT_of_zero
    have hstep2 := fun e₁ P' (hP' : ∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond (E.toTwoExit hcap').post e₁),
        0 ≤ P' S) => (route_step hs2 hn2 _ hcap'' h4P hconnP C' E' (X := Kt)
          (fun e₂ P'' _ => hbase _ hT'' hcapQ hloopQ e₂ _ P'') e₁ P' hP')
    by_cases hKt : 0 ≤ Kt
    · have hstep2' := fun e₁ P' hP' => (hstep2 e₁ P' hP').trans_eq (ENNReal.ofReal_mul (by positivity)).symm
      exact (route_step hs1 hn1 M hcap' h4 hconn C E hstep2' e P hP).trans_eq
        (ofReal_mul_ofReal_mul (by positivity))
    · push Not at hKt
      have h0 : ∀ e₁ P' hP', AFree (MoleProp.eraseBond (E.toTwoExit hcap').post e₁) d L γ δ (η / 2) C1 P' ≤
          ENNReal.ofReal 0 := fun e₁ P' hP' => by
        refine (hstep2 e₁ P' hP').trans ?_
        rw [ENNReal.ofReal_of_nonpos hKt.le, mul_zero]; exact bot_le
      refine (route_step hs1 hn1 M hcap' h4 hconn C E h0 e P hP).trans ?_
      rw [ENNReal.ofReal_zero, mul_zero]; exact bot_le

omit [DecidableEq D] in
/-- LG off atoms that are not in the molecule is LG. -/
theorem lgAdm_of_lgAdmOff {M : Molecule V D} {B : Finset V} (hB : ∀ x ∈ B, x ∉ M.atoms) {d : ℕ} {L γ η : ℝ}
    {P : Finset V → ℝ} {κ : D → (Fin d → ℤ)} (h : lgAdmOff M B L γ η P κ) : lgAdm M L γ η P κ :=
  ⟨fun x y hxy hdir => h.1 x y hxy (fun hB' => hB _ hB' (M.atom_mem x)) hdir, h.2⟩

omit [DecidableEq D] in
/-- Erasing `Y` keeps the darts of `w` of each direction when none of them goes to `Y`. -/
theorem eraseAtoms_dir_card (M : Molecule V D) (Y : Finset V) {w : V}
    (hno : ∀ x, M.atom x = w → M.atom x ∉ Y ∧ M.atom (M.mate x) ∉ Y) (bo : Bool) :
    (((Degen.eraseAtoms M Y).dartsAt w).filter fun x => (Degen.eraseAtoms M Y).out x = bo).card =
      ((M.dartsAt w).filter fun x => M.out x = bo).card := by
  classical
  refine card_bij (fun x _ => x.val) ?_ (fun x _ y _ h => Subtype.ext h) ?_
  · intro x hx
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and] at hx ⊢
    exact hx
  · intro x hx
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and] at hx
    exact ⟨⟨x, hno x hx.1⟩, by simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]; exact hx, rfl⟩

/-- The chain at `b′` survives the removal of `b` (separate chains). -/
theorem chain_after_erase {M : Molecule V D} (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {b b' : V}
    {y₃ y₄ : D} (hc : crossDarts M {b'} = {y₃, y₄})
    (p₃ : M.atom y₃ ∉ ({b} : Finset V) ∧ M.atom (M.mate y₃) ∉ ({b} : Finset V))
    (p₄ : M.atom y₄ ∉ ({b} : Finset V) ∧ M.atom (M.mate y₄) ∉ ({b} : Finset V)) :
    crossDarts (Degen.eraseAtoms M {b}) {b'} = {⟨y₃, p₃⟩, ⟨y₄, p₄⟩} ∧
      (∀ bo, (((Degen.eraseAtoms M {b}).dartsAt b').filter fun x => (Degen.eraseAtoms M {b}).out x = bo).card =
        ((M.dartsAt b').filter fun x => M.out x = bo).card) := by
  classical
  have hy : ∀ x, M.atom x = b' → x = y₃ ∨ x = y₄ := by
    intro x hx
    have : x ∈ crossDarts M {b'} := mem_crossDarts.mpr ⟨by rw [hx]; exact mem_singleton_self _,
      fun h => hloop x (hx.trans (mem_singleton.mp h).symm)⟩
    rw [hc] at this; simpa using this
  have hno : ∀ x, M.atom x = b' → M.atom x ∉ ({b} : Finset V) ∧ M.atom (M.mate x) ∉ ({b} : Finset V) := by
    intro x hx
    rcases hy x hx with rfl | rfl
    · exact p₃
    · exact p₄
  refine ⟨?_, eraseAtoms_dir_card M {b} hno⟩
  ext z
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hz
    have h0 := mem_crossDarts.mp hz
    have hz' : z.val ∈ crossDarts M {b'} := (mem_crossDarts (N := M)).mpr h0
    rw [hc] at hz'
    rcases mem_insert.mp hz' with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (mem_singleton.mp h))
  · rintro (rfl | rfl)
    · have h0 := mem_crossDarts.mp (show y₃ ∈ crossDarts M {b'} by rw [hc]; exact mem_insert_self _ _)
      exact (mem_crossDarts (N := Degen.eraseAtoms M {b})).mpr h0
    · have h0 := mem_crossDarts.mp (show y₄ ∈ crossDarts M {b'} by
        rw [hc]; exact mem_insert_of_mem (mem_singleton_self _))
      exact (mem_crossDarts (N := Degen.eraseAtoms M {b})).mpr h0

/-- **`𝕄₁` for two chains**: both chains `u → b → v`, `u′ → b′ → v′` replaced by bonds (operation (d) twice). -/
def closureTwo (M₀ : Molecule V D) (b b' : V) (y₁ y₂ y₃ y₄ : D) :=
  Mole.addBond (Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M₀ {b}) {b'}) (M₀.atom (M₀.mate y₃))
    (M₀.atom (M₀.mate y₄))) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))

/-- **Theorem A** (case-4 note §4), two β-chains `u → b → v` and `u′ → b′ → v′`. -/
theorem theorem_A (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) (hopc : OpCInput.{u, v} d γ η) (hopd : OpDInput.{u, v} d γ η) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M₀ : Molecule V D),
        (∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2) → (∀ z, M₀.atom z ≠ M₀.atom (M₀.mate z)) →
        ∀ (b b' : V) (y₁ y₂ y₃ y₄ : D), b ∈ M₀.atoms → b' ∈ M₀.atoms → b ≠ b' →
        (M₀.outdeg b = 1 ∧ M₀.indeg b = 1) → (M₀.outdeg b' = 1 ∧ M₀.indeg b' = 1) →
        crossDarts M₀ {b} = {y₁, y₂} → M₀.out y₁ = false → M₀.out y₂ = true →
        crossDarts M₀ {b'} = {y₃, y₄} → M₀.out y₃ = false → M₀.out y₄ = true →
        M₀.atom (M₀.mate y₁) ≠ M₀.atom (M₀.mate y₂) → M₀.atom (M₀.mate y₃) ≠ M₀.atom (M₀.mate y₄) →
        M₀.atom (M₀.mate y₁) ≠ b' → M₀.atom (M₀.mate y₂) ≠ b' →
        M₀.atom (M₀.mate y₃) ≠ b → M₀.atom (M₀.mate y₄) ≠ b →
        (∀ a ∈ M₀.atoms, ∀ c ∈ M₀.atoms, M₀.SameComponent a c) →
        (∀ a ∈ (Degen.eraseAtoms M₀ {b}).atoms, ∀ c ∈ (Degen.eraseAtoms M₀ {b}).atoms,
          (Degen.eraseAtoms M₀ {b}).SameComponent a c) →
        (∀ a ∈ (Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M₀ {b}) {b'}) (M₀.atom (M₀.mate y₃))
            (M₀.atom (M₀.mate y₄))).atoms,
          ∀ c ∈ (Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M₀ {b}) {b'}) (M₀.atom (M₀.mate y₃))
            (M₀.atom (M₀.mate y₄))).atoms,
          (Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M₀ {b}) {b'}) (M₀.atom (M₀.mate y₃))
            (M₀.atom (M₀.mate y₄))).SameComponent a c) →
        (∀ S ∈ MoleProp.ladderCells (Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M₀ {b}) {b'})
            (M₀.atom (M₀.mate y₃)) (M₀.atom (M₀.mate y₄))),
          GoodCell (Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M₀ {b}) {b'})
            (M₀.atom (M₀.mate y₃)) (M₀.atom (M₀.mate y₄))) S) →
        ∀ k ≤ 2, YRouteT k (closureTwo M₀ b b' y₁ y₂ y₃ y₄) →
        (∀ a ∈ (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms, (closureTwo M₀ b b' y₁ y₂ y₃ y₄).outdeg a ≤ 2 ∧
          (closureTwo M₀ b b' y₁ y₂ y₃ y₄).indeg a ≤ 2) →
        (∀ z, (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atom z ≠
          (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atom ((closureTwo M₀ b b' y₁ y₂ y₃ y₄).mate z)) →
        (∀ a ∈ (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms, (closureTwo M₀ b b' y₁ y₂ y₃ y₄).deg a = 4) →
        (∀ a ∈ (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms, ∀ c ∈ (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms,
          (closureTwo M₀ b b' y₁ y₂ y₃ y₄).SameComponent a c) →
        ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M₀, 0 ≤ P S) →
        ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdmOff M₀ {b, b'} L γ η P κ ∧ κ y₁ ≠ κ y₂) →
          MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) Adm P ≤
            ENNReal.ofReal (L ^ (-(CountLemmas.kappaHalf γ / 2))) := by
  have hκ := CountLemmas.kappaHalf_pos hγ
  have hγ0 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hγ.1], hγ.2⟩
  have hg : 0 < min γ (1 - γ) := lt_min hγ0.1 (by linarith [hγ.2])
  have hη2 : 0 < η / 2 := by linarith
  have hη4 : 0 < η / 2 / 2 := by positivity
  obtain ⟨Cc, hCc, hc⟩ := hopc
  obtain ⟨Cd, hCd, hdd⟩ := hopd
  obtain ⟨Cy1, hCy1, hy1⟩ := ylem2At_of.{u, v} d hd γ hγ0 (η / 2) hη2 (by linarith)
  obtain ⟨Cy2, hCy2, hy2⟩ := ylem2At_of.{u, v} d hd γ hγ0 (η / 2 / 2) hη4 (by linarith)
  obtain ⟨Ct, hCt, ht⟩ := tMinus_afree d hd γ hγ
  refine ⟨max (max Cc Cd) (2 * max Cy1 Cy2), hCc.trans ((le_max_left _ _).trans (le_max_left _ _)),
    fun C1 hC1 δ hδ => ?_⟩
  have e1 : C1 ≥ Cc := (le_max_left _ _).trans ((le_max_left _ _).trans hC1)
  have e2 : C1 ≥ Cd := (le_max_right _ _).trans ((le_max_left _ _).trans hC1)
  have e3 : C1 ≥ 2 * Cy1 := by linarith [le_max_right (max Cc Cd) (2 * max Cy1 Cy2), le_max_left Cy1 Cy2]
  have e4 : C1 ≥ 2 * Cy2 := by linarith [le_max_right (max Cc Cd) (2 * max Cy1 Cy2), le_max_right Cy1 Cy2]
  obtain ⟨Kc, Bc, Rc, hRc⟩ := hc C1 e1 δ hδ
  obtain ⟨Kd, Bd, Rd, hRd⟩ := hdd C1 e2 δ hδ
  obtain ⟨R1, hR1⟩ := hy1 C1 e3 δ hδ
  obtain ⟨R2, hR2⟩ := hy2 C1 e4 δ hδ
  obtain ⟨Lt, hLt⟩ := ht δ hδ
  have hθ : 0 < CountLemmas.kappaHalf γ / 10 := by positivity
  obtain ⟨A1, hA1⟩ := exists_mul_log_rpow_le Kc Bc hθ
  obtain ⟨A2, hA2⟩ := exists_mul_log_rpow_le Kd Bd hθ
  obtain ⟨A3, hA3⟩ := eventually_ylem2Const_le hθ
  obtain ⟨A4, hA4⟩ := exists_mul_log_rpow_le (Ct * δ⁻¹ ^ 2 * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) 0 hθ
  refine ⟨max (max (max Rc Rd) (max R1 R2)) (max (max Lt A1) (max (max A2 A3) (max A4 (Real.exp 1)))),
    fun L hL => ?_⟩
  have l1 : Rc ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have l2 : Rd ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have l3 : R1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have l4 : R2 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have l5 : Lt ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have l6 : A1 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have l7 : A2 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hL)))
  have l8 : A3 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hL)))
  have l9 : A4 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hL)))
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hL)))
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hK := one_le_ylem2Const (L := L) hlog
  intro V D _ _ _ M₀ hcap hloop b b' y₁ y₂ y₃ y₄ hb hb' hbb' hdb hdb' hc1 ho1 ho2 hc2 ho3 ho4 huv huv' hs1 hs2 hs3 hs4 hconn0 hconnb hconnK2 hopenK2
    k hk hroute hcap1 hloop1 h41 hconn1 P hP Adm hAdm
  classical
  -- the chain atoms
  have hy1m : y₁ ∈ crossDarts M₀ {b} := by rw [hc1]; exact mem_insert_self _ _
  have hy2m : y₂ ∈ crossDarts M₀ {b} := by rw [hc1]; exact mem_insert_of_mem (mem_singleton_self _)
  have hy3m : y₃ ∈ crossDarts M₀ {b'} := by rw [hc2]; exact mem_insert_self _ _
  have hy4m : y₄ ∈ crossDarts M₀ {b'} := by rw [hc2]; exact mem_insert_of_mem (mem_singleton_self _)
  have hat1 : M₀.atom y₁ = b := mem_singleton.mp (mem_crossDarts.mp hy1m).1
  have hat2 : M₀.atom y₂ = b := mem_singleton.mp (mem_crossDarts.mp hy2m).1
  have hat3 : M₀.atom y₃ = b' := mem_singleton.mp (mem_crossDarts.mp hy3m).1
  have hat4 : M₀.atom y₄ = b' := mem_singleton.mp (mem_crossDarts.mp hy4m).1
  have hu1 : M₀.atom (M₀.mate y₁) ≠ b := fun h => (mem_crossDarts.mp hy1m).2 (by rw [h]; exact mem_singleton_self _)
  have hu2 : M₀.atom (M₀.mate y₂) ≠ b := fun h => (mem_crossDarts.mp hy2m).2 (by rw [h]; exact mem_singleton_self _)
  -- Step 1: operation (c) on the first chain
  have hstep1 := hRc L l1 M₀ hcap hloop hconn0 {b} {b, b'} y₁ y₂ (by simpa using hb) (by simp)
    (fun x hx => by rw [mem_singleton.mp hx]; exact hdb) hc1 huv
    (fun a ha c hc => by rw [mem_singleton.mp ha, mem_singleton.mp hc]; exact Relation.EqvGen.refl _) hconnb
    P hP Adm (fun κ h => ⟨(hAdm κ h).1, y₁, y₂,
      by rw [hat1]; exact mem_singleton_self _, by rw [hat1, hat2], fun h' => (hAdm κ h).2 (by rw [h']),
      (hAdm κ h).2⟩)
  -- the second chain in `𝕄₀ ∖ b`
  have p₃ : M₀.atom y₃ ∉ ({b} : Finset V) ∧ M₀.atom (M₀.mate y₃) ∉ ({b} : Finset V) :=
    ⟨by rw [hat3]; simpa using hbb'.symm, by simpa using hs3⟩
  have p₄ : M₀.atom y₄ ∉ ({b} : Finset V) ∧ M₀.atom (M₀.mate y₄) ∉ ({b} : Finset V) :=
    ⟨by rw [hat4]; simpa using hbb'.symm, by simpa using hs4⟩
  obtain ⟨hcK, hdir⟩ := chain_after_erase hloop hc2 p₃ p₄
  have hbK : b' ∈ (Degen.eraseAtoms M₀ {b}).atoms := mem_sdiff.mpr ⟨hb', by simpa using hbb'.symm⟩
  have hdbK : (Degen.eraseAtoms M₀ {b}).outdeg b' = 1 ∧ (Degen.eraseAtoms M₀ {b}).indeg b' = 1 := by
    unfold Molecule.outdeg Molecule.indeg; rw [hdir true, hdir false]; exact hdb'
  -- the atoms of the first chain survive in `𝕄₁ ∖ ℓ`
  set K₂ := Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M₀ {b}) {b'}) (M₀.atom (M₀.mate y₃))
    (M₀.atom (M₀.mate y₄)) with hK₂
  have hmemK : ∀ w, w ∈ M₀.atoms → w ≠ b → w ≠ b' → w ∈ K₂.atoms := fun w hw h1 h2 =>
    mem_insert_of_mem (mem_insert_of_mem (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hw, by simpa using h1⟩, by simpa using h2⟩))
  have hu : M₀.atom (M₀.mate y₁) ∈ K₂.atoms := hmemK _ (M₀.atom_mem _) hu1 hs1
  have hv : M₀.atom (M₀.mate y₂) ∈ K₂.atoms := hmemK _ (M₀.atom_mem _) hu2 hs2
  -- Steps 3–4 for `𝕄₁ ∖ ℓ`
  have hbase : ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), IsT M →
      (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      ∀ (e : D) (η' : ℝ) (P : Finset V → ℝ), AFree (MoleProp.eraseBond M e) d L γ δ η' C1 P ≤
        ENNReal.ofReal (Ct * δ⁻¹ ^ 2 * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 * L ^ (-(1 - γ) - CountLemmas.kappaHalf γ)) :=
    fun M hT hcapT hloopT e η' P => hLt L l5 M hT hcapT hloopT e η' C1 P
  have hroute' := route_bound hK (hR1 L l3).1 (hR1 L l3).2 (hR2 L l4).1 (hR2 L l4).2 hbase
    (closureTwo M₀ b b' y₁ y₂ y₃ y₄) k hk hroute hcap1 hloop1 h41 hconn1 (Sum.inr true)
  -- Step 2: operation (d) on the second chain, then relabel
  have hsup : AFreeSupAdm (Degen.eraseAtoms M₀ {b}) d L γ δ C1
      (fun P' κ' => lgAdmOff (Degen.eraseAtoms M₀ {b}) ({b, b'} \ {b}) L γ η P' κ') ≤
      ENNReal.ofReal (Kd * Real.log L ^ Bd) * (ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 *
        (Real.log L ^ 2) ^ 6) ^ 2 * ENNReal.ofReal (Ct * δ⁻¹ ^ 2 * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 *
          L ^ (-(1 - γ) - CountLemmas.kappaHalf γ))) := by
    refine iSup₂_le fun P' hP' => ?_
    have hu3 : M₀.atom (M₀.mate y₃) ∉ (({b, b'} : Finset V) \ {b}) := by
      simp only [mem_sdiff, mem_insert, mem_singleton, not_and, not_not]
      intro h; rcases h with h | h
      · exact absurd h hs3
      · exact absurd h (by simpa using (mem_crossDarts.mp hy3m).2)
    have hu4 : M₀.atom (M₀.mate y₄) ∉ (({b, b'} : Finset V) \ {b}) := by
      simp only [mem_sdiff, mem_insert, mem_singleton, not_and, not_not]
      intro h; rcases h with h | h
      · exact absurd h hs4
      · exact absurd h (by simpa using (mem_crossDarts.mp hy4m).2)
    have hopD := hRd L l2 (Degen.eraseAtoms M₀ {b}) (caps_eraseAtoms {b} hcap) (fun z => hloop z.val) hconnb {b'}
      ({b, b'} \ {b}) ⟨y₃, p₃⟩ ⟨y₄, p₄⟩ (by simpa using hbK) (by simp [hbb'.symm]) (by simp)
      (fun x hx => by rw [mem_singleton.mp hx]; exact hdbK) hcK ho3 ho4 huv' hu3 hu4
      (fun a ha c hc => by rw [mem_singleton.mp ha, mem_singleton.mp hc]; exact Relation.EqvGen.refl _)
      hconnK2 hopenK2 P' hP'
      (fun κ' => lgAdmOff (Degen.eraseAtoms M₀ {b}) ({b, b'} \ {b}) L γ η P' κ') (fun κ' h => h)
    refine hopD.trans (mul_le_mul' le_rfl (iSup₂_le fun P'' hP'' => ?_))
    have hB : ∀ x ∈ (({b, b'} : Finset V) \ {b}) \ {b'}, x ∉ K₂.atoms := by
      intro x hx; simp only [mem_sdiff, mem_insert, mem_singleton] at hx; tauto
    refine (countAFree_mono_adm K₂ (L := L) (γ := γ) (δ := δ) (C1 := C1)
      (B := lgAdm K₂ L γ (η / 2) P'') (fun κ' h => lgAdm_of_lgAdmOff hB h)).trans
      ((afree_le_addBond_erase K₂ hu hv L γ δ (η / 2) C1 P'').trans ?_)
    have hcells := ladderCells_addBond_erase K₂ hu hv
    exact hroute' P'' (fun S hS => hP'' S (by show S ∈ MoleProp.ladderCells K₂; rw [← hcells]; exact hS))
  -- the constants
  have hc1' : Kc * Real.log L ^ Bc ≤ L ^ (CountLemmas.kappaHalf γ / 10) := hA1 L l6
  have hc2' : Kd * Real.log L ^ Bd ≤ L ^ (CountLemmas.kappaHalf γ / 10) := hA2 L l7
  have hc3' := hA3 L l8
  have hc4' : Ct * δ⁻¹ ^ 2 * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 ≤ L ^ (CountLemmas.kappaHalf γ / 10) := by
    have := hA4 L l9; rwa [Real.rpow_zero, mul_one] at this
  have hpos : ∀ x : ℝ, 0 ≤ L ^ x := fun x => Real.rpow_nonneg hLp.le x
  set θ := CountLemmas.kappaHalf γ / 10 with hθdef
  calc MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) Adm P
      ≤ ENNReal.ofReal (Kc * Real.log L ^ Bc * L ^ (1 - γ)) * (ENNReal.ofReal (Kd * Real.log L ^ Bd) *
          (ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
            ENNReal.ofReal (Ct * δ⁻¹ ^ 2 * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 *
              L ^ (-(1 - γ) - CountLemmas.kappaHalf γ)))) := hstep1.trans (mul_le_mul' le_rfl hsup)
    _ ≤ ENNReal.ofReal (L ^ θ * L ^ (1 - γ)) * (ENNReal.ofReal (L ^ θ) *
          (ENNReal.ofReal (L ^ θ) ^ 2 * ENNReal.ofReal (L ^ θ * L ^ (-(1 - γ) - CountLemmas.kappaHalf γ)))) := by
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc1' (hpos _)))
          (mul_le_mul' (ENNReal.ofReal_le_ofReal hc2') (mul_le_mul' (pow_le_pow_left₀ bot_le
            (ENNReal.ofReal_le_ofReal hc3') 2) (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc4' (hpos _)))))
    _ = ENNReal.ofReal (L ^ (-(CountLemmas.kappaHalf γ / 2))) := by
        rw [← ENNReal.ofReal_pow (hpos _), ← ENNReal.ofReal_mul (pow_nonneg (hpos _) _),
          ← ENNReal.ofReal_mul (hpos _), ← ENNReal.ofReal_mul (mul_nonneg (hpos _) (hpos _))]
        congr 1
        rw [sq]
        simp only [← Real.rpow_add hLp]
        congr 1
        rw [hθdef]; ring

/-- **`𝕄₁` for one chain** `u → b → b′ → v`: the chain replaced by a bond. -/
def closureOne (M₀ : Molecule V D) (b b' : V) (x₁ x₂ : D) :=
  Mole.addBond (Degen.eraseAtoms M₀ {b, b'}) (M₀.atom (M₀.mate x₁)) (M₀.atom (M₀.mate x₂))

/-- **Theorem A** (case-4 note §4), one β-chain `u → b → b′ → v` (`σ = 1`): operation (c) gives `𝕄₁ ∖ ℓ` directly. -/
theorem theorem_A_one (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) (hopc : OpCInput.{u, v} d γ η) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M₀ : Molecule V D),
        (∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2) → (∀ z, M₀.atom z ≠ M₀.atom (M₀.mate z)) →
        ∀ (b b' : V) (x₁ x₂ y y' : D), b ∈ M₀.atoms → b' ∈ M₀.atoms →
        (M₀.outdeg b = 1 ∧ M₀.indeg b = 1) → (M₀.outdeg b' = 1 ∧ M₀.indeg b' = 1) →
        crossDarts M₀ {b, b'} = {x₁, x₂} → M₀.atom (M₀.mate x₁) ≠ M₀.atom (M₀.mate x₂) →
        M₀.atom y = b → M₀.atom y' = b → y ≠ y' →
        (∀ a ∈ M₀.atoms, ∀ c ∈ M₀.atoms, M₀.SameComponent a c) →
        (∀ a ∈ ({b, b'} : Finset V), ∀ c ∈ ({b, b'} : Finset V), (piece M₀ {b, b'}).SameComponent a c) →
        (∀ a ∈ (Degen.eraseAtoms M₀ {b, b'}).atoms, ∀ c ∈ (Degen.eraseAtoms M₀ {b, b'}).atoms,
          (Degen.eraseAtoms M₀ {b, b'}).SameComponent a c) →
        ∀ k ≤ 2, YRouteT k (closureOne M₀ b b' x₁ x₂) →
        (∀ a ∈ (closureOne M₀ b b' x₁ x₂).atoms, (closureOne M₀ b b' x₁ x₂).outdeg a ≤ 2 ∧
          (closureOne M₀ b b' x₁ x₂).indeg a ≤ 2) →
        (∀ z, (closureOne M₀ b b' x₁ x₂).atom z ≠ (closureOne M₀ b b' x₁ x₂).atom ((closureOne M₀ b b' x₁ x₂).mate z)) →
        (∀ a ∈ (closureOne M₀ b b' x₁ x₂).atoms, (closureOne M₀ b b' x₁ x₂).deg a = 4) →
        (∀ a ∈ (closureOne M₀ b b' x₁ x₂).atoms, ∀ c ∈ (closureOne M₀ b b' x₁ x₂).atoms,
          (closureOne M₀ b b' x₁ x₂).SameComponent a c) →
        ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M₀, 0 ≤ P S) →
        ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdmOff M₀ {b, b'} L γ η P κ ∧ κ y ≠ κ y') →
          MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) Adm P ≤
            ENNReal.ofReal (L ^ (-(CountLemmas.kappaHalf γ / 2))) := by
  have hκ := CountLemmas.kappaHalf_pos hγ
  have hγ0 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hγ.1], hγ.2⟩
  have hη2 : 0 < η / 2 := by linarith
  obtain ⟨Cc, hCc, hc⟩ := hopc
  obtain ⟨Cy1, hCy1, hy1⟩ := ylem2At_of.{u, v} d hd γ hγ0 η hη hηmax
  obtain ⟨Cy2, hCy2, hy2⟩ := ylem2At_of.{u, v} d hd γ hγ0 (η / 2) hη2 (by linarith)
  obtain ⟨Ct, hCt, ht⟩ := tMinus_afree d hd γ hγ
  refine ⟨max Cc (2 * max Cy1 Cy2), hCc.trans (le_max_left _ _), fun C1 hC1 δ hδ => ?_⟩
  have e1 : C1 ≥ Cc := (le_max_left _ _).trans hC1
  have e3 : C1 ≥ 2 * Cy1 := by linarith [le_max_right Cc (2 * max Cy1 Cy2), le_max_left Cy1 Cy2]
  have e4 : C1 ≥ 2 * Cy2 := by linarith [le_max_right Cc (2 * max Cy1 Cy2), le_max_right Cy1 Cy2]
  obtain ⟨Kc, Bc, Rc, hRc⟩ := hc C1 e1 δ hδ
  obtain ⟨R1, hR1⟩ := hy1 C1 e3 δ hδ
  obtain ⟨R2, hR2⟩ := hy2 C1 e4 δ hδ
  obtain ⟨Lt, hLt⟩ := ht δ hδ
  have hθ : 0 < CountLemmas.kappaHalf γ / 8 := by positivity
  obtain ⟨A1, hA1⟩ := exists_mul_log_rpow_le Kc Bc hθ
  obtain ⟨A3, hA3⟩ := eventually_ylem2Const_le hθ
  obtain ⟨A4, hA4⟩ := exists_mul_log_rpow_le (Ct * δ⁻¹ ^ 2 * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) 0 hθ
  refine ⟨max (max Rc (max R1 R2)) (max (max Lt A1) (max A3 (max A4 (Real.exp 1)))), fun L hL => ?_⟩
  have l1 : Rc ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have l3 : R1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have l4 : R2 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have l5 : Lt ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have l6 : A1 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have l8 : A3 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have l9 : A4 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hL)))
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hL)))
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hK := one_le_ylem2Const (L := L) hlog
  intro V D _ _ _ M₀ hcap hloop b b' x₁ x₂ y y' hb hb' hdb hdb' hc1 huv hy hy' hyy' hconn0 hYconn hconnK k hk hroute hcap1 hloop1 h41
    hconn1 P hP Adm hAdm
  classical
  have hx1m : x₁ ∈ crossDarts M₀ {b, b'} := by rw [hc1]; exact mem_insert_self _ _
  have hx2m : x₂ ∈ crossDarts M₀ {b, b'} := by rw [hc1]; exact mem_insert_of_mem (mem_singleton_self _)
  have hY : ({b, b'} : Finset V) ⊆ M₀.atoms := by
    intro z hz; simp only [mem_insert, mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
  -- Step 1: operation (c) on the chain
  have hstep1 := hRc L l1 M₀ hcap hloop hconn0 {b, b'} {b, b'} x₁ x₂ hY (subset_refl _)
    (fun z hz => by simp only [mem_insert, mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption)
    hc1 huv hYconn hconnK P hP Adm (fun κ h => ⟨(hAdm κ h).1, y, y', by rw [hy]; exact mem_insert_self _ _, by rw [hy, hy'],
      hyy', (hAdm κ h).2⟩)
  set K₂ := Degen.eraseAtoms M₀ {b, b'} with hK₂
  have hu : M₀.atom (M₀.mate x₁) ∈ K₂.atoms := mem_sdiff.mpr ⟨M₀.atom_mem _, (mem_crossDarts.mp hx1m).2⟩
  have hv : M₀.atom (M₀.mate x₂) ∈ K₂.atoms := mem_sdiff.mpr ⟨M₀.atom_mem _, (mem_crossDarts.mp hx2m).2⟩
  have hbase : ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), IsT M →
      (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      ∀ (e : D) (η' : ℝ) (P : Finset V → ℝ), AFree (MoleProp.eraseBond M e) d L γ δ η' C1 P ≤
        ENNReal.ofReal (Ct * δ⁻¹ ^ 2 * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 * L ^ (-(1 - γ) - CountLemmas.kappaHalf γ)) :=
    fun M hT hcapT hloopT e η' P => hLt L l5 M hT hcapT hloopT e η' C1 P
  have hroute' := route_bound hK (hR1 L l3).1 (hR1 L l3).2 (hR2 L l4).1 (hR2 L l4).2 hbase
    (closureOne M₀ b b' x₁ x₂) k hk hroute hcap1 hloop1 h41 hconn1 (Sum.inr true)
  have hsup : AFreeSupAdm K₂ d L γ δ C1 (fun P' κ' => lgAdmOff K₂ ({b, b'} \ {b, b'}) L γ η P' κ') ≤
      ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
        ENNReal.ofReal (Ct * δ⁻¹ ^ 2 * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 * L ^ (-(1 - γ) - CountLemmas.kappaHalf γ)) := by
    refine iSup₂_le fun P' hP' => ?_
    have hB : ∀ z ∈ ({b, b'} : Finset V) \ {b, b'}, z ∉ K₂.atoms := by
      intro z hz; simp at hz
    refine (countAFree_mono_adm K₂ (L := L) (γ := γ) (δ := δ) (C1 := C1)
      (B := lgAdm K₂ L γ η P') (fun κ' h => lgAdm_of_lgAdmOff hB h)).trans
      ((afree_le_addBond_erase K₂ hu hv L γ δ η C1 P').trans ?_)
    have hcells := ladderCells_addBond_erase K₂ hu hv
    exact hroute' P' (fun S hS => hP' S (by show S ∈ MoleProp.ladderCells K₂; rw [← hcells]; exact hS))
  have hc1' : Kc * Real.log L ^ Bc ≤ L ^ (CountLemmas.kappaHalf γ / 8) := hA1 L l6
  have hc3' := hA3 L l8
  have hc4' : Ct * δ⁻¹ ^ 2 * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 ≤ L ^ (CountLemmas.kappaHalf γ / 8) := by
    have := hA4 L l9; rwa [Real.rpow_zero, mul_one] at this
  have hpos : ∀ x : ℝ, 0 ≤ L ^ x := fun x => Real.rpow_nonneg hLp.le x
  set θ := CountLemmas.kappaHalf γ / 8 with hθdef
  calc MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) Adm P
      ≤ ENNReal.ofReal (Kc * Real.log L ^ Bc * L ^ (1 - γ)) *
          (ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
            ENNReal.ofReal (Ct * δ⁻¹ ^ 2 * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 *
              L ^ (-(1 - γ) - CountLemmas.kappaHalf γ))) := hstep1.trans (mul_le_mul' le_rfl hsup)
    _ ≤ ENNReal.ofReal (L ^ θ * L ^ (1 - γ)) *
          (ENNReal.ofReal (L ^ θ) ^ 2 * ENNReal.ofReal (L ^ θ * L ^ (-(1 - γ) - CountLemmas.kappaHalf γ))) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc1' (hpos _)))
          (mul_le_mul' (pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal hc3') 2)
            (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc4' (hpos _))))
    _ = ENNReal.ofReal (L ^ (-(CountLemmas.kappaHalf γ / 2))) := by
        rw [← ENNReal.ofReal_pow (hpos _), ← ENNReal.ofReal_mul (pow_nonneg (hpos _) _),
          ← ENNReal.ofReal_mul (mul_nonneg (hpos _) (hpos _))]
        congr 1
        rw [sq]
        simp only [← Real.rpow_add hLp]
        congr 1
        rw [hθdef]; ring

end WaveTurbulence.MoleProp4
