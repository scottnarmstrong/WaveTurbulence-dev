/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Rough96
public import WaveTurbulence.Foundations.FinalCount.Interp96
public import WaveTurbulence.Foundations.FinalCount.Cycle96
public import WaveTurbulence.Foundations.FinalCount.P101.Main
public import WaveTurbulence.Foundations.FinalCount.Prop102Bridge
import Mathlib.Tactic

/-! # Prop 9.6, case (1): the odd component (DH23 L1884)

Operations (a), (b) are applied only to `ε`-atoms and to degree-one protected atoms (Prop 10.1', `proposition_one_off_bound`
with `B` the `α`/`β` atoms), giving `𝔄₀ ≲ 1`; interpolating with roughbd gives (finalcount).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.FinalCountG8.P101

section
variable {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

open Classical in
theorem card_nonEps (M : Molecule V D) (cls : V → Cls) :
    (nonEps M.atoms cls).card = (alphaAtoms M.atoms cls).card + (betaAtoms M.atoms cls).card := by
  have hdisj : Disjoint (alphaAtoms M.atoms cls) (betaAtoms M.atoms cls) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h1 := (mem_filter.mp ha).2
    have h2 := (mem_filter.mp hb).2
    cases hc : cls a <;> simp_all [Cls.IsAlpha, Cls.IsBeta]
  have hU : alphaAtoms M.atoms cls ∪ betaAtoms M.atoms cls = nonEps M.atoms cls := by
    ext a
    unfold alphaAtoms betaAtoms nonEps
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by cases hc : cls a <;> simp_all [Cls.IsAlpha, Cls.IsEps]⟩
      · exact ⟨h1, by cases hc : cls a <;> simp_all [Cls.IsBeta, Cls.IsEps]⟩
    · rintro ⟨h1, h2⟩
      rcases cls_cases h2 with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, h⟩
  rw [← card_union_of_disjoint hdisj, hU]

theorem card_deg_ne_four_odd {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd)
    (hodd : odd) :
    (M.atoms.filter fun a => M.deg a ≠ 4).card ≤ (nonEps M.atoms cls).card + 2 := by
  classical
  obtain ⟨u, hu, w, hw, huw, hu1, hw3, hrest⟩ := hS.oddDeg hodd
  have hsub : M.atoms.filter (fun a => M.deg a ≠ 4) ⊆ nonEps M.atoms cls ∪ {u, w} := by
    intro a ha
    obtain ⟨ha1, h4⟩ := mem_filter.mp ha
    by_cases hau : a = u
    · exact mem_union_right _ (by simp [hau])
    by_cases haw : a = w
    · exact mem_union_right _ (by simp [haw])
    refine mem_union_left _ (mem_filter.mpr ⟨ha1, (hS.classes a ha1).mp ?_⟩)
    rcases hrest a ha1 hau haw with h | h <;> omega
  calc _ ≤ (nonEps M.atoms cls ∪ {u, w}).card := card_le_card hsub
    _ ≤ (nonEps M.atoms cls).card + ({u, w} : Finset V).card := card_union_le _ _
    _ ≤ (nonEps M.atoms cls).card + 2 := by
        have := card_le_two (a := u) (b := w); omega

end

/-- Exponent arithmetic of case (1): `η³(16d+28)(p+2) ≤ V_α(γ-5η)/2 + (γ₀+2η²)V_β` for `p = V_α+V_β ≥ 1`. -/
theorem odd_arith {d : ℕ} {γ η Va Vb : ℝ} (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ (1 - γ) / 200) (hηd : (d : ℝ) * η ≤ (1 - γ) / 4) (hVa : 0 ≤ Va) (hVb : 0 ≤ Vb)
    (hp : 1 ≤ Va + Vb) :
    η ^ 3 * (16 * (d : ℝ) + 28) * ((Va + Vb + 2) + 1) ≤ Va * ((γ - 5 * η) / 2) + (1 - γ + 2 * η ^ 2) * Vb := by
  have hη3 : η ≤ 1 / 100 := by linarith
  have h1 : η ^ 3 * (16 * (d : ℝ) + 28) ≤ (1 - γ) / 40 := by
    have e : η ^ 3 * (16 * (d : ℝ) + 28) = η ^ 2 * (16 * ((d : ℝ) * η) + 28 * η) := by ring
    rw [e]
    have h2 : 16 * ((d : ℝ) * η) + 28 * η ≤ 4 * (1 - γ) + 28 * ((1 - γ) / 200) := by
      linarith only [hηd, hη1]
    have h3 : η ^ 2 ≤ 1 / 10000 := by
      calc η ^ 2 = η * η := sq η
        _ ≤ (1 / 100) * (1 / 100) := mul_le_mul hη3 hη3 hη.le (by norm_num)
        _ = 1 / 10000 := by norm_num
    calc η ^ 2 * (16 * ((d : ℝ) * η) + 28 * η) ≤ (1 / 10000) * (4 * (1 - γ) + 28 * ((1 - γ) / 200)) :=
          mul_le_mul h3 h2 (by positivity) (by norm_num)
      _ ≤ (1 - γ) / 40 := by linarith only [hγ2]
  have h4 : (1 - γ) / 10 ≤ (γ - 5 * η) / 2 := by linarith only [hγ1, hη3]
  have h5 : (1 - γ) / 10 ≤ 1 - γ + 2 * η ^ 2 := by linarith only [hγ2, pow_pos hη 2]
  have hq : ((Va + Vb + 2) + 1) ≤ 4 * (Va + Vb) := by linarith
  have hc : 0 ≤ η ^ 3 * (16 * (d : ℝ) + 28) := by positivity
  calc η ^ 3 * (16 * (d : ℝ) + 28) * ((Va + Vb + 2) + 1) ≤ η ^ 3 * (16 * (d : ℝ) + 28) * (4 * (Va + Vb)) :=
        mul_le_mul_of_nonneg_left hq hc
    _ ≤ ((1 - γ) / 40) * (4 * (Va + Vb)) := mul_le_mul_of_nonneg_right h1 (by linarith)
    _ ≤ Va * ((γ - 5 * η) / 2) + (1 - γ + 2 * η ^ 2) * Vb := by
        linarith only [mul_le_mul_of_nonneg_left h4 hVa, mul_le_mul_of_nonneg_left h5 hVb]


section
variable {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem pmol_nonEps {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd)
    {u : V} (hu : u ∈ M.atoms) (hu1 : M.deg u = 1 ∨ M.deg u = 3) : PMol (nonEps M.atoms cls) M := by
  classical
  refine ⟨hS.caps, fun v hv hvB => ?_, fun v hv => ⟨u, hu, hS.conn v hv u hu, ?_⟩⟩
  · exact (hS.classes v hv).mpr (mem_filter.mp hvB).2 |> fun h => h
  · unfold cap
    by_cases huB : u ∈ nonEps M.atoms cls
    · rw [if_pos huB]; omega
    · rw [if_neg huB]; omega

end

/-- Exponent arithmetic of case (1) with `V_α = V_β = 0` (both odd atoms of degree `3`). -/
theorem odd0_arith {η γ ρ K c : ℝ} (hq : 0 < 1 - γ) (hK : η ^ 3 * K ≤ (1 - γ) / 40) (hη3 : η ^ 3 ≤ 1 / 2)
    (hc : c ≤ 2) (hc0 : 0 ≤ c) (hη : 0 ≤ η) (hK0 : 0 ≤ K) :
    η ^ 3 * (-η ^ 2 * ρ + K * (c + 1)) + (1 - η ^ 3) * (-(3 / 5 * (1 - γ))) ≤
      (0 : ℝ) * ((γ - 5 * η) / 2) + ((1 - γ + 2 * η ^ 2) * 0 - (2 * (1 - γ) + 5 * η ^ 2) * 0) +
        (-(η ^ 5) * ρ) := by
  have h1 : η ^ 3 * K * (c + 1) ≤ 3 * ((1 - γ) / 40) :=
    (mul_le_mul_of_nonneg_left (by linarith : c + 1 ≤ 3) (mul_nonneg (pow_nonneg hη 3) hK0)).trans (by linarith)
  have h2 : (1 / 2) * (3 / 5 * (1 - γ)) ≤ (1 - η ^ 3) * (3 / 5 * (1 - γ)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e : η ^ 3 * (-η ^ 2 * ρ) = -(η ^ 5) * ρ := by ring
  have e2 : η ^ 3 * (-η ^ 2 * ρ + K * (c + 1)) = η ^ 3 * (-η ^ 2 * ρ) + η ^ 3 * K * (c + 1) := by ring
  rw [e2, e]
  nlinarith [h1, h2]

/-- **Case (1): the odd component.** -/
theorem case_odd (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ min γ (1 - γ) / 200) (hηd : (d : ℝ) * η ≤ min γ (1 - γ) / 4) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        FinalShape M cls odd → FinalDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm → odd →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η) := by
  classical
  have hγ0 : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith [hγ.1])
  rw [hγ0] at hη1 hηd
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hγ.1], hγ.2⟩
  have hηγ : η ≤ min γ (1 - γ) := by rw [hγ0]; linarith
  have hηmax : η ≤ min γ (1 - γ) / 2 := by rw [hγ0]; linarith
  obtain ⟨C₀, hC₀, hrough⟩ := rough96.{u, v} d hd γ η hγ01 hη hηγ hηs
  obtain ⟨Cs, hCs, hP1⟩ := proposition_one_off_bound.{u, v} d hd γ hγ01 η hη hηmax
  obtain ⟨C102, hC102, h102⟩ := prop102InputSz.{u, v} d hd γ η hγ01 hη hηγ hηs
  refine ⟨max (max C₀ Cs) C102, le_trans hC₀ ((le_max_left _ _).trans (le_max_left _ _)), fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨L₀, hL₀1, hL₀⟩ := hrough m δ hδ C1 (((le_max_left _ _).trans (le_max_left _ _)).trans hC1)
  obtain ⟨Rp, hRp⟩ := hP1 C1 (((le_max_right _ _).trans (le_max_left _ _)).trans hC1) δ hδ
  obtain ⟨R102, hR102⟩ := h102 m C1 ((le_max_right _ _).trans hC1) δ hδ
  refine ⟨max (max (max L₀ Rp) R102) (Real.exp 1),
    le_trans hL₀1 (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))), ?_⟩
  intro L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hodd
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLRp : Rp ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLR102 : R102 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  obtain ⟨u, hu, w, hw, huw, hu1, hw3, hrest⟩ := hS.oddDeg hodd
  have hM : M.IsMolecule := hS.isMolecule
  have hA2 := hL₀ L hLL₀ M cls odd Adm P hS hF hsz hP hMA
  have hθ0 : 0 ≤ η ^ 3 := by positivity
  have hθ1 : η ^ 3 ≤ 1 := pow_le_one₀ hη.le (by linarith)
  have hcR : ((M.atoms.filter fun a => M.deg a ≠ 4).card : ℝ) ≤
      ((alphaAtoms M.atoms cls).card : ℝ) + ((betaAtoms M.atoms cls).card : ℝ) + 2 := by
    have := card_deg_ne_four_odd hS hodd
    rw [card_nonEps] at this; exact_mod_cast this
  by_cases hp0 : (nonEps M.atoms cls).Nonempty
  · -- step A: 𝔄 ≲ 1
    have hPM := pmol_nonEps hS hu hu1
    have hLG : ∀ κ, (Adm κ ∧ CellGapRestriction M L (0 : Mom d) (fun S => P (Mole.appbLinkParent M S)) (GapScale L) κ) →
        P101.LargeGapOff (nonEps M.atoms cls) M L γ η (0 : Mom d) κ := by
      intro κ hκ v hvB x y hx hy hxy
      have hv : v ∈ M.atoms := hx ▸ M.atom_mem x
      have hε : (cls v).IsEps := by
        by_contra hne; exact hvB (mem_filter.mpr ⟨hv, hne⟩)
      exact (hF.epsLG κ hκ.1 v hv hε x y hx hy hxy).le
    have hA1 : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ 1 :=
      (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans
        (hRp L hLRp hlog (nonEps M.atoms cls) M hPM (fun x hx => hS.noLoop x) _ _ hLG (fun κ hκ => hκ.2)
          (fun S _ => hP _))
    have hA1' : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (0 : ℝ)) := by
      rw [Real.rpow_zero, ENNReal.ofReal_one]; exact hA1
    have hi := interp_L hL1 hA2 hA1' hθ0 hθ1
    refine hi.trans (ENNReal.ofReal_le_ofReal ?_)
    refine le_trans ?_ (finalRHS_ge M cls odd hL1 hη.le hF.labRange)
    refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
    rw [if_pos hodd]
    have hp : 1 ≤ ((alphaAtoms M.atoms cls).card : ℝ) + ((betaAtoms M.atoms cls).card : ℝ) := by
      have : 1 ≤ (nonEps M.atoms cls).card := card_pos.mpr hp0
      rw [card_nonEps] at this; exact_mod_cast this
    have hA := odd_arith (d := d) (γ := γ) (η := η) (Va := ((alphaAtoms M.atoms cls).card : ℝ))
      (Vb := ((betaAtoms M.atoms cls).card : ℝ)) hγ.1 hγ.2 hη hη1 hηd (Nat.cast_nonneg _) (Nat.cast_nonneg _) hp
    have hc0 : 0 ≤ η ^ 3 * (16 * (d : ℝ) + 28) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hcR hc0
    rw [hγ0]
    nlinarith [hA, hmul]
  · -- p = 0: both odd atoms have degree 3; Prop 10.2 gives `L^{-3γ₀/5}`
    have hall : ∀ a ∈ M.atoms, (cls a).IsEps := by
      intro a ha; by_contra hn; exact hp0 ⟨a, mem_filter.mpr ⟨ha, hn⟩⟩
    have hdeg4 : ∀ a ∈ M.atoms, a ≠ u → a ≠ w → M.deg a = 4 := by
      intro a ha h1 h2
      have := (hS.classes a ha).not.mpr (fun h => h (hall a ha))
      rcases hrest a ha h1 h2 with h | h <;> omega
    have hdu : M.deg u = 3 := by
      have := (hS.classes u hu).not.mpr (fun h => h (hall u hu)); omega
    have hdw : M.deg w = 3 := by
      have := (hS.classes w hw).not.mpr (fun h => h (hall w hw)); omega
    have hsum := Mole.sum_degrees_eq_two_mul_bonds M
    have hsub : ({u, w} : Finset V) ⊆ M.atoms := by
      intro x hx; rcases mem_insert.mp hx with rfl | h
      · exact hu
      · rw [mem_singleton.mp h]; exact hw
    rw [← sum_sdiff hsub] at hsum
    have e1 : ∑ x ∈ M.atoms \ {u, w}, M.deg x = 4 * (M.atoms.card - 2) := by
      rw [sum_congr rfl (fun x hx => hdeg4 x (mem_sdiff.mp hx).1 (fun h => (mem_sdiff.mp hx).2 (by simp [h]))
        (fun h => (mem_sdiff.mp hx).2 (by simp [h])))]
      rw [sum_const, card_sdiff_of_subset hsub, card_pair huw, smul_eq_mul]; ring
    rw [e1, sum_pair huw, hdu, hdw] at hsum
    have h2V : 2 ≤ M.atoms.card := by have := card_le_card hsub; rw [card_pair huw] at this; exact this
    have hE : (M.bonds.card : ℤ) = 2 * M.atoms.card - 1 := by omega
    set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
    have hA3 : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ)))) := by
      refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
      refine le_trans (WaveTurbulence.MoleProp4.countAFree_mono_adm M (B := WaveTurbulence.MoleProp4.lgAdm M L γ η P')
        (fun κ hκ => ⟨fun x y hxy hdir => ?_, hκ.2⟩)) ?_
      · have hv : M.atom x ∈ M.atoms := M.atom_mem x
        exact (hF.epsLG κ hκ.1 _ hv (hall _ hv) x y rfl hxy.symm hdir).le
      · exact hR102 L hLR102 M hM hS.conn (fun a b => hS.noTriple a b) hE hsz P' (fun S _ => hP _)
    have hVa : (alphaAtoms M.atoms cls).card = 0 := by
      have : nonEps M.atoms cls = ∅ := not_nonempty_iff_eq_empty.mp hp0
      have h := card_nonEps M cls; rw [this] at h; simp at h; omega
    have hVb : (betaAtoms M.atoms cls).card = 0 := by
      have : nonEps M.atoms cls = ∅ := not_nonempty_iff_eq_empty.mp hp0
      have h := card_nonEps M cls; rw [this] at h; simp at h; omega
    have hA3' : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (1 * L ^ (-(3 / 5 * (1 - γ)))) := by
      rw [one_mul, ← hγ0]; exact hA3
    have hcR2 : ((M.atoms.filter fun a => M.deg a ≠ 4).card : ℝ) ≤ 2 := by
      rw [hVa, hVb] at hcR; simpa using hcR
    have hq : 0 < 1 - γ := by linarith [hγ.2]
    have hη3 : η ^ 3 * (16 * (d : ℝ) + 28) ≤ (1 - γ) / 40 := by
      have e : η ^ 3 * (16 * (d : ℝ) + 28) = η ^ 2 * (16 * ((d : ℝ) * η) + 28 * η) := by ring
      rw [e]
      have hm := min_le_right γ (1 - γ)
      have h2 : 16 * ((d : ℝ) * η) + 28 * η ≤ 4 * (1 - γ) + 28 * ((1 - γ) / 200) := by
        linarith only [hηd, hη1, hm]
      have h100 : η ≤ 1 / 100 := by linarith only [hηs, hη]
      have h3 : η ^ 2 ≤ 1 / 10000 := by
        calc η ^ 2 = η * η := sq η
          _ ≤ (1 / 100) * (1 / 100) := mul_le_mul h100 h100 hη.le (by norm_num)
          _ = 1 / 10000 := by norm_num
      calc η ^ 2 * (16 * ((d : ℝ) * η) + 28 * η) ≤ (1 / 10000) * (4 * (1 - γ) + 28 * ((1 - γ) / 200)) :=
            mul_le_mul h3 h2 (by positivity) (by norm_num)
        _ ≤ (1 - γ) / 40 := by linarith only [hq]
    have hc0 : 0 ≤ η ^ 3 * (16 * (d : ℝ) + 28) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hcR2 hc0
    have he := odd0_arith (η := η) (γ := γ) (ρ := (M.rho : ℝ)) (K := 16 * (d : ℝ) + 28)
      (c := ((M.atoms.filter fun a => M.deg a ≠ 4).card : ℝ)) hq hη3 (by
        have h : η ≤ 1 / 2 := by linarith [hγ.1, hγ.2]
        exact (pow_le_of_le_one hη.le (by linarith) (by norm_num)).trans h) hcR2 (Nat.cast_nonneg _) hη.le (by positivity)
    have hend := endgame hL1 le_rfl hA2 hA3' hθ0 hθ1 he
    refine hend.trans (ENNReal.ofReal_le_ofReal ?_)
    have hfin := finalRHS_ge M cls odd hL1 hη.le hF.labRange
    rw [hVa, hVb, if_pos hodd] at hfin
    rw [hγ0] at hfin
    simpa using hfin

end WaveTurbulence.FinalCountG8
