/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C4Main
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Case23
import Mathlib.Tactic

/-! # Prop 9.6 at `0 < γ ≤ 1/2`, case (4)′: `V_α = 0, V_β = 2` (DH23 L1883–L1887; M2 Lemma 4.8, OM4)

Port of main's `case_four_of_nonexc` (`FinalCount/C4Main.lean`) to `γ ≤ 1/2`, in `𝒱_γ` terms (M2 §4.8):
* `𝕄₁` Y-exceptional of T-type: `M₀` IS a T-vine (D11 `IsTVine`, M2 §4.8 (A2)); this is the internal target
  `C4TBridge` (main's T-route data ⇒ `IsTVine M.atoms b b'`). Then `vineLG` over `𝒱_γ` makes the β-gap LG and
  operation (c) with Prop 10.1′ gives `L^{−η/2}` (CASE4 Lemma 2.4) — exactly main's Q-branch argument. Main's F75
  Theorem A (γ > 1/2) is not used.
* Q-type: `M₀` is a vine (II) (main's `c4_two_vine`), a member of `𝒱_γ`, hence LG; as main.
* not Y-exceptional: main's `Case4NonExc` (γ-agnostic statement; at `γ ≤ 1/2` it is Prop 10.4(2)′ with the low providers,
  owner L6-COUNT).

`C4TBridge` is stated here and proved in `P96/BridgeProof.lean` (`c4TBridge_proved`): main's complete (Y2) sequences are
D11 `Y2Step` paths on the bond multigraph, `IsT` ⇒ `IsDoubledTriangle`, `closureTwo`/`closureOne` = D11 `IsClosure`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedVariables false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount
universe u v
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp WaveTurbulence.MoleProp4

/-- **The T-type bridge of case (4)′** (internal L6 target, M2 §4.8 (A2), REFEREED): if the closure of a case-(4)
component (two β-chains, `closureTwo`, or one chain of two β-atoms, `closureOne`) has a complete (Y)-route to `T`, the
component is a T-vine with joints `b, b'` (D11 `IsTVine`). -/
structure C4TBridge : Prop where
  two : ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (cls : V → Cls)
    (odd : Prop), FinalShape M cls odd → ¬ odd → (alphaAtoms M.atoms cls).card = 0 →
    (betaAtoms M.atoms cls).card = 2 → ∀ (b b' : V) (y₁ y₂ y₃ y₄ : D), Case4TwoData M cls b b' y₁ y₂ y₃ y₄ →
    RegCore (closureTwo M b b' y₁ y₂ y₃ y₄) → ∀ k, YRouteT k (closureTwo M b b' y₁ y₂ y₃ y₄) →
      M.IsTVine M.atoms b b'
  one : ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (cls : V → Cls)
    (odd : Prop), FinalShape M cls odd → ¬ odd → (alphaAtoms M.atoms cls).card = 0 →
    (betaAtoms M.atoms cls).card = 2 → ∀ (b b' : V) (x₁ x₂ y y' : D), Case4OneData M cls b b' x₁ x₂ y y' →
    RegCore (closureOne M b b' x₁ x₂) → ∀ k, YRouteT k (closureOne M b b' x₁ x₂) → M.IsTVine M.atoms b b'

/-- **The final interpolation of case (4)**: `A ≤ L^{E₁}` (roughbd, two atoms of degree `2`) and `A ≤ L^{-η/128}` give
(finalcount) for `V_α = 0`, `V_β = 2`. -/
theorem case4_finish_low {d : ℕ} (hd : 3 ≤ d) {γ η L ρ : ℝ} {A : ℝ≥0∞} (hγ1 : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ γ / 1000) (hL : 1 ≤ L) (hρ : 0 ≤ ρ)
    (hA1 : A ≤ ENNReal.ofReal (L ^ (-η ^ 2 * ρ + (16 * (d : ℝ) + 28) * (2 + 1))))
    (hA2 : A ≤ ENNReal.ofReal (L ^ (-(η / 128)))) : A ≤ ENNReal.ofReal (L ^ (-η ^ 2 - η ^ 5 * ρ)) := by
  obtain ⟨s1, s2, s3, s4⟩ := small_facts_low hd hγ1 hγ2 hη hsm
  have hθ0 : 0 ≤ η ^ 3 := by positivity
  have hθ1 : η ^ 3 ≤ 1 := pow_le_one₀ hη.le (by linarith)
  have h := interp_L hL hA1 hA2 hθ0 hθ1
  refine h.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL ?_))
  have hη3 : η ^ 3 ≤ 1 / 100 := by nlinarith [pow_pos hη 2]
  have hη2 : η ^ 2 ≤ η / 6000 := by nlinarith
  have e2 : η ^ 3 * (-η ^ 2 * ρ) = -(η ^ 5 * ρ) := by ring
  nlinarith [pow_pos hη 2, pow_pos hη 3, mul_pos hη hη]

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]
end

/-- **Case (4)′ at `γ ≤ 1/2`**, given the T-type bridge and the non-exceptional input (conditional helper). -/
theorem case_four_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) (hDT : DrawnTVineInput.{u, v})
    (hbr : C4TBridge.{u, v}) (hNE : Case4NonExc.{u, v} d γ η) :
    EvenCaseLowAt.{u, v} d γ η (fun a b => a = 0 ∧ b = 2) := by
  classical
  have hγ0 : min γ (1 - γ) = γ := min_gamma_low hγ.2
  rw [hγ0] at hsm
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hγ.1, by linarith [hγ.2]⟩
  obtain ⟨h1, h2, h3, h4⟩ := small_facts_low hd hγ.1 hγ.2 hη hsm
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hηγ : η ≤ min γ (1 - γ) := by rw [hγ0]; linarith
  have hηmax : η ≤ min γ (1 - γ) / 2 := by rw [hγ0]; linarith
  obtain ⟨C₀, hC₀, hrough⟩ := rough96.{u, v} d hd γ η hγ01 hη hηγ hηs
  -- the slots of main's Theorem A (T-type, γ > 1/2) are unused at γ ≤ 1/2: the T-type branch uses `C4TBridge`
  obtain ⟨CA, hCA⟩ : ∃ CA : ℝ, 1 ≤ CA := ⟨1, le_rfl⟩
  obtain ⟨CA1, hCA1⟩ : ∃ CA1 : ℝ, 1 ≤ CA1 := ⟨1, le_rfl⟩
  obtain ⟨Cs, hCs, hchain⟩ := chain_A_bound_low.{u, v} d hd γ hγ01 η hη hηmax
  obtain ⟨CN2, hCN2, hN2⟩ := hNE.two
  obtain ⟨CN1, hCN1, hN1⟩ := hNE.one
  refine ⟨max (max (max C₀ CA) (max CA1 Cs)) (max CN2 CN1), le_trans hC₀ ((le_max_left _ _).trans
    ((le_max_left _ _).trans (le_max_left _ _))), fun m C1 hC1 δ hδ => ?_⟩
  have c0 : C1 ≥ C₀ := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hC1))
  have cA : C1 ≥ CA := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hC1))
  have cA1 : C1 ≥ CA1 := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hC1))
  have cs : C1 ≥ Cs := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hC1))
  have cN2 : C1 ≥ CN2 := (le_max_left _ _).trans ((le_max_right _ _).trans hC1)
  have cN1 : C1 ≥ CN1 := (le_max_right _ _).trans ((le_max_right _ _).trans hC1)
  obtain ⟨L₀, hL₀1, hL₀⟩ := hrough m δ hδ C1 c0
  obtain ⟨RA, -⟩ : ∃ RA : ℝ, True := ⟨0, trivial⟩
  obtain ⟨RA1, -⟩ : ∃ RA1 : ℝ, True := ⟨0, trivial⟩
  obtain ⟨Rc, hRc1, hRc⟩ := hchain C1 cs δ hδ
  obtain ⟨RN2, hRN21, hRN2⟩ := hN2 m C1 cN2 δ hδ
  obtain ⟨RN1, hRN11, hRN1⟩ := hN1 m C1 cN1 δ hδ
  obtain ⟨R3, hR31, hR3⟩ := const_log_le_rpow (C := 3 ^ d * ((d : ℝ) * δ⁻¹ + 1)) (ε := η / 2) 8 (by positivity)
  refine ⟨max (max (max L₀ RA) (max RA1 Rc)) (max (max RN2 RN1) (max R3 (Real.exp 1))), ?_, ?_⟩
  · exact le_trans hL₀1 ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  intro L hL V D _ _ _ M cls odd Adm P hS hFL hsz hP hMA hfr hnodd hnc hcase
  have hF : FinalDec M cls L γ η Adm := finalDec_of_low hDT hγ.2 hFL
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLRA : RA ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLRA1 : RA1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hLRc : Rc ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hLRN2 : RN2 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have hLRN1 : RN1 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have hLR3 : R3 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hδ0 := hδ.1
  by_cases hAex : ∃ κ, Adm κ
  swap
  · push Not at hAex
    rw [countA_zero_of_noAdm M L γ δ C1 Adm P hAex]; exact bot_le
  obtain ⟨κ0, hκ0⟩ := hAex
  have hB : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (-(η / 128))) := by
    rcases c4_data hS hnodd hnc hcase.1 hcase.2 with ⟨b, b', y₁, y₂, y₃, y₄, D4⟩ | ⟨b, b', x₁, x₂, y, y', D1⟩
    · -- two chains
      have hy12 : y₁ ≠ y₂ := fun h => D4.hfar1 (by rw [h])
      have hy34 : y₃ ≠ y₄ := fun h => D4.hfar2 (by rw [h])
      have hyd : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), M.atom (M.mate y) ≠ b ∧ M.atom (M.mate y) ≠ b' := fun y hy =>
        ⟨fun h => D4.hnb (h ▸ D4.hendsE y hy), fun h => D4.hnb' (h ▸ D4.hendsE y hy)⟩
      have hat : ∀ {K : Finset V} {p q : D}, crossDarts M K = {p, q} → M.atom p ∈ K ∧ M.atom q ∈ K := by
        intro K p q h
        exact ⟨(mem_crossDarts.mp (by rw [h]; simp)).1, (mem_crossDarts.mp (by rw [h]; simp)).1⟩
      have hat1 : M.atom y₁ = b := mem_singleton.mp (hat D4.hc1).1
      have hat2 : M.atom y₂ = b := mem_singleton.mp (hat D4.hc1).2
      have hat3 : M.atom y₃ = b' := mem_singleton.mp (hat D4.hc2).1
      have hat4 : M.atom y₄ = b' := mem_singleton.mp (hat D4.hc2).2
      have hall1 : ∀ x, M.atom x = b → x = y₁ ∨ x = y₂ := by
        intro x hx
        have : x ∈ crossDarts M {b} := mem_crossDarts.mpr ⟨by rw [hx]; exact mem_singleton_self _,
          fun h => hS.noLoop x (hx.trans (mem_singleton.mp h).symm)⟩
        rw [D4.hc1] at this; simpa using this
      have hall2 : ∀ x, M.atom x = b' → x = y₃ ∨ x = y₄ := by
        intro x hx
        have : x ∈ crossDarts M {b'} := mem_crossDarts.mpr ⟨by rw [hx]; exact mem_singleton_self _,
          fun h => hS.noLoop x (hx.trans (mem_singleton.mp h).symm)⟩
        rw [D4.hc2] at this; simpa using this
      have hends : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), M.atom (M.mate y) ∈ M.atoms ∧ M.atom (M.mate y) ≠ b ∧
          M.atom (M.mate y) ≠ b' := fun y hy => ⟨M.atom_mem _, (hyd y hy).1, (hyd y hy).2⟩
      have hreg := regcore_closureTwo M hS.caps hS.noLoop hS.conn (nocut_M0 hS hF hLp hnodd hκ0 hfr) D4.hdeg4 D4.hbb'
        hat1 hat2 hat3 hat4 hy12 hy34 hall1 hall2 D4.ho1 D4.ho2 D4.ho3 D4.ho4 hends D4.hfar1 D4.hfar2
      have hm : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), M.atom (M.mate y) ∈ (M.atoms \ {b}) \ {b'} := fun y hy =>
        mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨M.atom_mem _, by simpa using (hyd y hy).1⟩, by simpa using (hyd y hy).2⟩
      have hAt := atoms_closureTwo M b b' y₁ y₂ y₃ y₄ (hm y₁ (by simp)) (hm y₂ (by simp)) (hm y₃ (by simp)) (hm y₄ (by simp))
      have htrip := trip_closureTwo M b b' y₁ y₂ y₃ y₄ hS.noTriple hAt
      by_cases hex : YReachesQT (closureTwo M b b' y₁ y₂ y₃ y₄)
      · rcases reach_cases hex 2 hreg htrip with ⟨k, hk, hroute⟩ | hQ
        · -- T-type at γ ≤ 1/2: `M` is a T-vine (`C4TBridge`), hence LG (`vineLG` over 𝒱_γ); operation (c)
          have hT := hbr.two M cls odd hS hnodd hcase.1 hcase.2 b b' y₁ y₂ y₃ y₄ D4 hreg k hroute
          have hlg : ∀ κ, Adm κ → L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) κ y₁ - Molecule.kvec L (0 : Mom d) κ y₂‖ :=
            fun κ hκ => hFL.vineLG (Or.inl ⟨b, b', Or.inl ⟨hγ.2, Or.inr (Or.inr hT)⟩⟩) κ hκ y₁ y₂
              (hat1.trans hat2.symm) (by rw [D4.ho1, D4.ho2]; simp)
          have hAdm : ∀ κ, Adm κ → ∃ p q, M.atom p ∈ ({b} : Finset V) ∧ M.atom q = M.atom p ∧ p ≠ q ∧
              L ^ (-γ + η) ≤ ‖Molecule.kvec L (0 : Mom d) κ p - Molecule.kvec L (0 : Mom d) κ q‖ := fun κ hκ =>
            ⟨y₁, y₂, by rw [hat1]; simp, by rw [hat1, hat2], hy12, (hlg κ hκ).le⟩
          have hA2 := hRc L hLRc (L ^ (-γ + η)) (Real.rpow_pos_of_pos hLp _) M cls odd Adm P hS hF hnodd hnc hP hMA {b}
            D4.hKb hAdm
          exact hA2.trans ((ENNReal.ofReal_le_ofReal (chain_num hL1 hδ0 hη (by linarith [hγ.2]) (hR3 L hLR3))).trans
            (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))))
        · -- Q-type: `M` is a vine (II), hence LG, and operation (c) applies
          obtain ⟨m', φ, hφ⟩ := yrouteQ_zq hQ hreg htrip
          have hV := c4_two_vine hS D4 ⟨m', φ, hφ⟩
          have hlg : ∀ κ, Adm κ → L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) κ y₁ - Molecule.kvec L (0 : Mom d) κ y₂‖ :=
            fun κ hκ => hFL.vineLG (Or.inl ⟨b', b, Or.inl ⟨hγ.2, Or.inr (Or.inl hV)⟩⟩) κ hκ y₁ y₂ (hat1.trans hat2.symm)
              (by rw [D4.ho1, D4.ho2]; simp)
          have hAdm : ∀ κ, Adm κ → ∃ p q, M.atom p ∈ ({b} : Finset V) ∧ M.atom q = M.atom p ∧ p ≠ q ∧
              L ^ (-γ + η) ≤ ‖Molecule.kvec L (0 : Mom d) κ p - Molecule.kvec L (0 : Mom d) κ q‖ := fun κ hκ =>
            ⟨y₁, y₂, by rw [hat1]; simp, by rw [hat1, hat2], hy12, (hlg κ hκ).le⟩
          have hA2 := hRc L hLRc (L ^ (-γ + η)) (Real.rpow_pos_of_pos hLp _) M cls odd Adm P hS hF hnodd hnc hP hMA {b}
            D4.hKb hAdm
          exact hA2.trans ((ENNReal.ofReal_le_ofReal (chain_num hL1 hδ0 hη (by linarith [hγ.2]) (hR3 L hLR3))).trans
            (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))))
      · exact hRN2 L hLRN2 M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcase b b' y₁ y₂ y₃ y₄ D4 hex
    · -- one chain
      have hcard : (crossDarts M {b, b'}).card = 2 := by rw [D1.hc, card_pair D1.hne]
      have heven := shape_even hS hnodd
      have hconnE := connected_erase_of_two_cross M hS.conn heven {b, b'} hcard
      have hM : M.IsMolecule := hS.isMolecule
      have hnocut := nocut_M0 hS hF hLp hnodd hκ0 hfr
      have hreg := regcore_closureOne hS.caps hS.noLoop hS.conn hnocut D1.hb D1.hb' D1.hdeg4 D1.hc D1.hne D1.ho1 D1.ho2
        D1.hfar
      have hend : ∀ w, (cls w).IsEps → w ∉ ({b, b'} : Finset V) := by
        intro w hw hwB
        rcases mem_insert.mp hwB with h | h
        · exact D1.hnb (h ▸ hw)
        · exact D1.hnb' ((mem_singleton.mp h) ▸ hw)
      have hx1 : M.atom (M.mate x₁) ∉ ({b, b'} : Finset V) := hend _ D1.hendsE.1
      have hx2 : M.atom (M.mate x₂) ∉ ({b, b'} : Finset V) := hend _ D1.hendsE.2
      have hAt : (closureOne M b b' x₁ x₂).atoms = M.atoms \ {b, b'} := by
        change insert (M.atom (M.mate x₁)) (insert (M.atom (M.mate x₂)) (M.atoms \ {b, b'})) = _
        rw [insert_eq_of_mem (mem_sdiff.mpr ⟨M.atom_mem _, hx2⟩), insert_eq_of_mem (mem_sdiff.mpr ⟨M.atom_mem _, hx1⟩)]
      have htrip := trip_closureOne M b b' x₁ x₂ hS.noTriple hAt
      by_cases hex : YReachesQT (closureOne M b b' x₁ x₂)
      · rcases reach_cases hex 2 hreg htrip with ⟨k, hk, hroute⟩ | hQ
        · -- T-type at γ ≤ 1/2, one chain: `M` is a T-vine (`C4TBridge`), hence LG; operation (c) on `{b, b'}`
          have hT := hbr.one M cls odd hS hnodd hcase.1 hcase.2 b b' x₁ x₂ y y' D1 hreg k hroute
          have hdb := hS.dir2 b D1.hb D1.hdeg2
          have hlg : ∀ κ, Adm κ → L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ :=
            fun κ hκ => hFL.vineLG (Or.inl ⟨b, b', Or.inl ⟨hγ.2, Or.inr (Or.inr hT)⟩⟩) κ hκ y y'
              (D1.hyb.trans D1.hyb'.symm) (out_ne_of_two M hdb.1 hdb.2 D1.hyb D1.hyb' D1.hyy')
          have hAdm : ∀ κ, Adm κ → ∃ p q, M.atom p ∈ ({b, b'} : Finset V) ∧ M.atom q = M.atom p ∧ p ≠ q ∧
              L ^ (-γ + η) ≤ ‖Molecule.kvec L (0 : Mom d) κ p - Molecule.kvec L (0 : Mom d) κ q‖ := fun κ hκ =>
            ⟨y, y', by rw [D1.hyb]; simp, by rw [D1.hyb, D1.hyb'], D1.hyy', (hlg κ hκ).le⟩
          have hA2 := hRc L hLRc (L ^ (-γ + η)) (Real.rpow_pos_of_pos hLp _) M cls odd Adm P hS hF hnodd hnc hP hMA
            {b, b'} D1.hK hAdm
          exact hA2.trans ((ENNReal.ofReal_le_ofReal (chain_num hL1 hδ0 hη (by linarith [hγ.2]) (hR3 L hLR3))).trans
            (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))))
        · -- Q-type is impossible for one chain
          exfalso
          obtain ⟨m', φ, hφ⟩ := yrouteQ_zq hQ hreg htrip
          refine zq_no_single (c := M.atom (M.mate x₁)) (d := M.atom (M.mate x₂)) hφ (fun p q => ?_)
          by_cases hpq : p ∈ (closureOne M b b' x₁ x₂).atoms ∧ q ∈ (closureOne M b b' x₁ x₂).atoms
          · rw [hAt] at hpq
            rw [bb_closureOne M b b' x₁ x₂ (mem_sdiff.mp hpq.1).2 (mem_sdiff.mp hpq.2).2]
            have := hS.noTriple p q
            split_ifs <;> omega
          · have : (closureOne M b b' x₁ x₂).bondsBetween p q = 0 := by
              by_cases hp : p ∈ (closureOne M b b' x₁ x₂).atoms
              · rw [Degen.bondsBetween_comm]; exact bb_zero_of_not_mem _ (fun hq => hpq ⟨hp, hq⟩) p
              · exact bb_zero_of_not_mem _ hp q
            rw [this]; omega
      · exact hRN1 L hLRN1 M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcase b b' x₁ x₂ y y' D1 hex
  have hA1 := hL₀ L hLL₀ M cls odd Adm P hS hF hsz hP hMA
  have hcard2 : (M.atoms.filter fun a => M.deg a ≠ 4).card = 2 := by
    rw [card_deg_ne_four_even hS hnodd, card_nonEps, hcase.1, hcase.2]
  rw [hcard2] at hA1
  have hρ : (0 : ℝ) ≤ (M.rho : ℝ) := Nat.cast_nonneg _
  have hfin := finalRHS_ge M cls odd hL1 hη.le hF.labRange
  have hexp : ((alphaAtoms M.atoms cls).card : ℝ) * ((γ - 5 * η) / 2) +
      ((min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) -
        (2 * min γ (1 - γ) + 5 * η ^ 2) * (open Classical in if odd then (0 : ℝ) else 1)) +
      (-(η ^ 5) * (M.rho : ℝ)) = -η ^ 2 - η ^ 5 * (M.rho : ℝ) := by
    rw [hcase.1, hcase.2, if_neg hnodd, hγ0]; push_cast; ring
  rw [hexp] at hfin
  exact (case4_finish_low hd hγ.1 hγ.2 hη hsm hL1 hρ (by push_cast at hA1 ⊢; exact hA1) hB).trans
    (ENNReal.ofReal_le_ofReal hfin)

end WaveTurbulence.GammaLow.FinalCount
