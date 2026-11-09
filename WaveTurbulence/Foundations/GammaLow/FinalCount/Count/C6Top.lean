/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6b2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6Q
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6Struct
public import WaveTurbulence.Foundations.FinalCount.Odd96
import Mathlib.Tactic

/-! # Case (6), sub-cases (6b) and (6d): the case analysis (packet L6-COUNT, Case6TopLow; M2 §4.10)

`c6_top_core`: in case (6) (`V_α = 2`, `V_β = 1`, even, not a cycle) with both `α`-atoms of `κ = 0` and labels
`> L^{−γ−50η}`, at a fixed large `L`,
`𝔄(𝕄₀) ≤ [3^d (d δ⁻¹ (R₁/2)⁻¹ L^{−γ} + L^{γ−1}) (log L)^8] · L^{−3γ/5 + η²/8}` for an `α`-atom `v₁` with label `R₁`.
With `K₁` the chain of `v₁` and `R = nonEps ∖ K₁` (`remaining_cases`):
* `R = ∅`: (6b), `c6b0_bound`;
* `R` one chain with far ends `p, q`: `b(p,q) ≤ 1` is (6b) with one operation (d) (`c6b1_bound`), `b(p,q) = 2` is (6d)
  with a theta chain (`thetaGenData_double`, `c6d_key`);
* `R = {v₂, β}` two singleton chains with far-end pairs `{e₁,e₂}`, `{e₃,e₄}`: a doubly bonded pair is (6d) with a
  theta chain; equal pairs with one bond is (6d) with the generalized theta chain (`thetaGenData_single`); otherwise
  (6b) with two operations (d) (`c6b2_bound`).
The charge hypotheses of operation (e) come from `c6_charges` (`hQ_double`, `hQ_single`). All remainders are
`≤ L^{−3γ/5 + η²/8}` (`(6d)`: `L^{−γ+100η} ≤ L^{−3γ/5}` as `η ≤ γ/250`). -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8 WaveTurbulence.FinalCountG8.P101

/-- The body of `c6d_key` at a fixed `L`. -/
def C6dAt (d : ℕ) (L γ η δ C1 K : ℝ) : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    FinalShape M cls odd → FinalDec M cls L γ η Adm → ¬ odd → (¬ ∀ a ∈ M.atoms, M.deg a = 2) →
    (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm → (∃ w, w ∉ M.atoms) →
    ∀ (v₁ : V) (K₁ : Finset V), v₁ ∈ M.atoms → (cls v₁).IsAlpha → IsChainSet M cls K₁ → v₁ ∈ K₁ →
    ∀ (S : Finset V) (p q : V) (a b z₁ z₂ : D) (C C' : Finset V),
    ThetaGenData M S p q a b z₁ z₂ C C' → Disjoint S K₁ → S.card ≤ 5 → C.card ≤ 3 →
    (∀ c κ, (∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) → M.IsDecoration L 0 c κ → Adm κ →
      L ^ (-γ - 100 * η) / 2 ≤ ‖Molecule.kvec L 0 κ z₁ - Molecule.kvec L 0 κ z₂‖ ∧
      ∑ w ∈ S, ∑ z ∈ M.dartsAt w, M.dartSign z • Molecule.kvec L 0 κ z ≠ 0) →
      M.countA L γ δ C1 (0 : Mom d) Adm P ≤
        ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ((cls v₁).lab / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) *
          Real.log L ^ (8 : ℝ)) *
          ENNReal.ofReal (K * Real.log L ^ (78 : ℕ) * (2 * δ⁻¹ * L ^ (-γ + 100 * η)))

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The charge hypothesis of operation (e) for a theta chain on a chain `C ⊆ {v₂, β}`. -/
theorem hQ_double {M : Molecule V D} {d : ℕ} {L γ η : ℝ} {Adm : (D → (Fin d → ℤ)) → Prop} (hL : 0 < L)
    {v₁ v₂ b : V} (h2b : v₂ ≠ b)
    (hch : ∀ (c : V → Mom d) κ, (∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) → M.IsDecoration L 0 c κ → Adm κ →
      c v₁ + c v₂ + c b = 0 ∧ L ^ (-γ - 100 * η) / 2 ≤ ‖c v₁‖ ∧ L ^ (-γ - 100 * η) / 2 ≤ ‖c v₂‖ ∧
        L ^ (-γ - 100 * η) / 2 ≤ ‖c b‖)
    {C : Finset V} {p q : V} {y₁ y₂ : D} (hCA : C ⊆ M.atoms) (hp : p ∈ M.atoms) (hq : q ∈ M.atoms)
    (hp4 : M.deg p = 4) (hq4 : M.deg q = 4) (hpC : p ∉ C) (hqC : q ∉ C) (hpq : p ≠ q)
    (hcross : crossDarts M C = {y₁, y₂}) (hy12 : y₁ ≠ y₂) (hdir : M.out y₁ ≠ M.out y₂)
    (hCvb : ∀ x ∈ C, x = v₂ ∨ x = b) (hne : C.Nonempty) :
    ∀ (c : V → Mom d) κ, (∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) → M.IsDecoration L 0 c κ → Adm κ →
      L ^ (-γ - 100 * η) / 2 ≤ ‖Molecule.kvec L 0 κ (M.mate y₁) - Molecule.kvec L 0 κ (M.mate y₂)‖ ∧
      ∑ w ∈ insert p (insert q C), ∑ z ∈ M.dartsAt w, M.dartSign z • Molecule.kvec L 0 κ z ≠ 0 := by
  intro c κ hc hκ hA
  obtain ⟨hsum, hb1, hb2, hb3⟩ := hch c κ hc hκ hA
  have hρ : 0 < L ^ (-γ - 100 * η) / 2 := by have := Real.rpow_pos_of_pos hL (-γ - 100 * η); linarith
  have hbig := c6_chain_charge h2b hsum hb1 hb2 hb3 hCvb hne
  refine ⟨by rw [chain_gap_norm hκ hCA hy12 hcross hdir]; exact hbig, ?_⟩
  have hSA : insert p (insert q C) ⊆ M.atoms := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hp
    rcases mem_insert.mp hx with rfl | hx
    · exact hq
    exact hCA hx
  rw [starSum_eq hκ hSA, sum_insert_two_zero hpC hqC hpq (hc p hp hp4) (hc q hq hq4)]
  intro h0
  rw [h0, norm_zero] at hbig
  linarith

/-- The charge hypothesis of operation (e) for the generalized theta chain on `{v₂}`, `{β}`. -/
theorem hQ_single {M : Molecule V D} {d : ℕ} {L γ η : ℝ} {Adm : (D → (Fin d → ℤ)) → Prop} (hL : 0 < L)
    {v₁ v₂ b : V} (h2b : v₂ ≠ b)
    (hch : ∀ (c : V → Mom d) κ, (∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) → M.IsDecoration L 0 c κ → Adm κ →
      c v₁ + c v₂ + c b = 0 ∧ L ^ (-γ - 100 * η) / 2 ≤ ‖c v₁‖ ∧ L ^ (-γ - 100 * η) / 2 ≤ ‖c v₂‖ ∧
        L ^ (-γ - 100 * η) / 2 ≤ ‖c b‖)
    {p q : V} {y₁ y₂ : D} (h2 : v₂ ∈ M.atoms) (h3 : b ∈ M.atoms) (hp : p ∈ M.atoms) (hq : q ∈ M.atoms)
    (hp4 : M.deg p = 4) (hq4 : M.deg q = 4) (hpC : p ∉ ({v₂} : Finset V) ∪ {b})
    (hqC : q ∉ ({v₂} : Finset V) ∪ {b}) (hpq : p ≠ q)
    (hcross : crossDarts M {v₂} = {y₁, y₂}) (hy12 : y₁ ≠ y₂) (hdir : M.out y₁ ≠ M.out y₂) :
    ∀ (c : V → Mom d) κ, (∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) → M.IsDecoration L 0 c κ → Adm κ →
      L ^ (-γ - 100 * η) / 2 ≤ ‖Molecule.kvec L 0 κ (M.mate y₁) - Molecule.kvec L 0 κ (M.mate y₂)‖ ∧
      ∑ w ∈ insert p (insert q (({v₂} : Finset V) ∪ {b})), ∑ z ∈ M.dartsAt w,
        M.dartSign z • Molecule.kvec L 0 κ z ≠ 0 := by
  intro c κ hc hκ hA
  obtain ⟨hsum, hb1, hb2, hb3⟩ := hch c κ hc hκ hA
  have hρ : 0 < L ^ (-γ - 100 * η) / 2 := by have := Real.rpow_pos_of_pos hL (-γ - 100 * η); linarith
  refine ⟨by
    rw [chain_gap_norm hκ (by simpa using h2) hy12 hcross hdir, sum_singleton]; exact hb2, ?_⟩
  have hSA : insert p (insert q (({v₂} : Finset V) ∪ {b})) ⊆ M.atoms := by
    intro x hx
    simp only [mem_insert, mem_union, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  rw [starSum_eq hκ hSA, sum_insert_two_zero hpC hqC hpq (hc p hp hp4) (hc q hq hq4), ← insert_eq,
    sum_pair h2b]
  have e : c v₂ + c b = -c v₁ := by rw [← sub_eq_zero, ← hsum]; abel
  rw [e]
  intro h0
  rw [neg_eq_zero] at h0
  rw [h0, norm_zero] at hb1
  linarith

/-- The degree of an `ε`-atom of an even component. -/
theorem deg_eps_four {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd) (hnodd : ¬ odd)
    {w : V} (hw : w ∈ M.atoms) (hε : (cls w).IsEps) : M.deg w = 4 := by
  have h1 : ¬ M.deg w ≤ 2 := fun h => ((hS.classes w hw).mp h) hε
  rcases hS.evenDeg hnodd w hw with h | h <;> omega

end

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The case analysis of (6b), (6d)** (see the module docstring). -/
theorem c6_top_core {d m : ℕ} {L γ δ η C1 Kd1 Bd1 Kd2 Bd2 Ke : ℝ} (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hη : 0 < η) (hη250 : η ≤ γ / 250) (hL1 : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hC1 : 1 ≤ C1)
    (h102a : Prop102At.{u, v} d L γ δ η C1 m) (h102b : Prop102At.{u, v} d L γ δ (η / 2) C1 m)
    (h102c : Prop102At.{u, v} d L γ δ (η / 2 / 2) C1 m)
    (hRd1 : OpDAt.{u, v} d L γ δ η C1 Kd1 Bd1) (hRd2 : OpDAt.{u, v} d L γ δ (η / 2) C1 Kd2 Bd2)
    (hK1 : Kd1 * Real.log L ^ Bd1 ≤ L ^ (η ^ 2 / 16)) (hK2 : Kd2 * Real.log L ^ Bd2 ≤ L ^ (η ^ 2 / 16))
    (hKe : Ke * (2 * δ⁻¹) * Real.log L ^ (78 : ℕ) ≤ L ^ (η ^ 2 / 8))
    (h6d : C6dAt.{u, v} d L γ η δ C1 Ke)
    (M : Molecule V D) (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (hS : FinalShape M cls odd) (hF : FinalDec M cls L γ η Adm) (hsz : (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m)
    (hP : ∀ S, 0 ≤ P S) (hMA : MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm)
    (hfr : ∃ w, w ∉ M.atoms) (hnodd : ¬ odd) (hnc : ¬ ∀ a ∈ M.atoms, M.deg a = 2)
    (hcase : (alphaAtoms M.atoms cls).card = 2 ∧ (betaAtoms M.atoms cls).card = 1)
    (hlab : ∀ v ∈ alphaAtoms M.atoms cls, (cls v).kap = 0 ∧ L ^ (-γ - 50 * η) < (cls v).lab) :
    ∃ v₁ ∈ alphaAtoms M.atoms cls, M.countA L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ((cls v₁).lab / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) *
        Real.log L ^ (8 : ℝ)) * ENNReal.ofReal (L ^ (-(3 / 5 * γ) + η ^ 2 / 8)) := by
  classical
  have hLp : 0 < L := by linarith
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hγ.1, by linarith [hγ.2]⟩
  have hγ0 : min γ (1 - γ) = γ := min_eq_left (by linarith [hγ.2])
  -- the remainders
  set T : ℝ := -(3 / 5 * γ) + η ^ 2 / 8 with hT
  have hrp : ∀ a b : ℝ, a ≤ b → ENNReal.ofReal (L ^ a) ≤ ENNReal.ofReal (L ^ b) := fun a b h =>
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL1 h)
  have hmulrp : ∀ a b : ℝ, ENNReal.ofReal (L ^ a) * ENNReal.ofReal (L ^ b) = ENNReal.ofReal (L ^ (a + b)) := by
    intro a b
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hLp.le _), ← Real.rpow_add hLp]
  have hX0 : ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ)))) ≤ ENNReal.ofReal (L ^ T) := by
    rw [hγ0]; exact hrp _ _ (by rw [hT]; nlinarith [sq_nonneg η])
  have hX1 : ENNReal.ofReal (Kd1 * Real.log L ^ Bd1) * ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ)))) ≤
      ENNReal.ofReal (L ^ T) := by
    refine (mul_le_mul' (ENNReal.ofReal_le_ofReal hK1) le_rfl).trans ?_
    rw [hγ0, hmulrp]; exact hrp _ _ (by rw [hT]; nlinarith [sq_nonneg η])
  have hX2 : ENNReal.ofReal (Kd1 * Real.log L ^ Bd1) *
      (ENNReal.ofReal (Kd2 * Real.log L ^ Bd2) * ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ))))) ≤
      ENNReal.ofReal (L ^ T) := by
    refine (mul_le_mul' (ENNReal.ofReal_le_ofReal hK1)
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hK2) le_rfl)).trans ?_
    rw [hγ0, hmulrp, hmulrp]; exact hrp _ _ (by rw [hT]; nlinarith [sq_nonneg η])
  have hXd : ENNReal.ofReal (Ke * Real.log L ^ (78 : ℕ) * (2 * δ⁻¹ * L ^ (-γ + 100 * η))) ≤
      ENNReal.ofReal (L ^ T) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have e : Ke * Real.log L ^ (78 : ℕ) * (2 * δ⁻¹ * L ^ (-γ + 100 * η)) =
        (Ke * (2 * δ⁻¹) * Real.log L ^ (78 : ℕ)) * L ^ (-γ + 100 * η) := by ring
    rw [e]
    calc (Ke * (2 * δ⁻¹) * Real.log L ^ (78 : ℕ)) * L ^ (-γ + 100 * η)
        ≤ L ^ (η ^ 2 / 8) * L ^ (-γ + 100 * η) :=
          mul_le_mul_of_nonneg_right hKe (Real.rpow_nonneg hLp.le _)
      _ = L ^ (η ^ 2 / 8 + (-γ + 100 * η)) := (Real.rpow_add hLp _ _).symm
      _ ≤ L ^ T := Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hT]; linarith)
  -- the atoms
  obtain ⟨v₁, v₂, b, h1, h2, h3, hα1, hα2, hβ, h12, h1b, h2b, hαeq, hchar, d1, d2, d3, h4'⟩ :=
    c6_atoms hS hnodd hcase.1 hcase.2
  have h4 : ∀ v ∈ M.atoms, v ≠ v₁ → v ≠ v₂ → v ≠ b → M.deg v = 4 := fun v hv e1 e2 e3 => (h4' v hv e1 e2 e3).1
  have hv₁α : v₁ ∈ alphaAtoms M.atoms cls := by rw [hαeq]; simp
  have hv₂α : v₂ ∈ alphaAtoms M.atoms cls := by rw [hαeq]; simp
  obtain ⟨hk1, hl1⟩ := hlab v₁ hv₁α
  obtain ⟨hk2, hl2⟩ := hlab v₂ hv₂α
  have hn2 : ¬ (cls v₂).IsEps := (hchar v₂ h2).mpr (Or.inr (Or.inl rfl))
  have hnb : ¬ (cls b).IsEps := (hchar b h3).mpr (Or.inr (Or.inr rfl))
  have hch := fun (c : V → Mom d) κ hc hκ hA =>
    c6_charges hS hF hL1 hη.le h1 h2 h3 hα1 hα2 hβ h12 h1b h2b d1 d2 d3 h4 hk1 hk2 hl1 hl2
      (c := c) (κ := κ) hc hκ hA
  obtain ⟨K₁, hK₁, hv₁K⟩ := exists_chainSet M cls h1 (alpha_not_eps hα1)
  refine ⟨v₁, hv₁α, ?_⟩
  have hstep := c6_opc_step hγ01 hL1 hlog hδ hC1 hS hF hnodd hnc hP hMA h1 hα1 hK₁ hv₁K
  have hKeps : ∀ x ∈ K₁, ¬ (cls x).IsEps := hK₁.2.2.1
  have hεK : ∀ w, (cls w).IsEps → w ∉ K₁ := fun w hw hwK => hKeps w hwK hw
  have hdeg2 : ∀ x ∈ M.atoms, ¬ (cls x).IsEps → M.deg x = 2 := by
    intro x hx hn
    have := (hS.classes x hx).mpr hn
    rcases hS.evenDeg hnodd x hx with h | h <;> omega
  have hdir1 : ∀ x ∈ M.atoms, ¬ (cls x).IsEps → M.outdeg x = 1 ∧ M.indeg x = 1 := fun x hx hn =>
    hS.dir2 x hx (hdeg2 x hx hn)
  -- the operation-(e) branch
  have h6 : ∀ (S : Finset V) (p q : V) (a b' z₁ z₂ : D) (C C' : Finset V),
      ThetaGenData M S p q a b' z₁ z₂ C C' → Disjoint S K₁ → S.card ≤ 5 → C.card ≤ 3 →
      (∀ c κ, (∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) → M.IsDecoration L 0 c κ → Adm κ →
        L ^ (-γ - 100 * η) / 2 ≤ ‖Molecule.kvec L 0 κ z₁ - Molecule.kvec L 0 κ z₂‖ ∧
        ∑ w ∈ S, ∑ z ∈ M.dartsAt w, M.dartSign z • Molecule.kvec L 0 κ z ≠ 0) →
      M.countA L γ δ C1 (0 : Mom d) Adm P ≤
        ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ((cls v₁).lab / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) *
          Real.log L ^ (8 : ℝ)) * ENNReal.ofReal (L ^ T) := by
    intro S p q a b' z₁ z₂ C C' hT' hSK hS5 hC3 hQ
    exact (h6d M cls odd Adm P hS hF hnodd hnc hP hMA hfr v₁ K₁ h1 hα1 hK₁ hv₁K S p q a b' z₁ z₂ C C' hT' hSK
      hS5 hC3 hQ).trans (mul_le_mul' le_rfl hXd)
  have hdisj3 : ∀ (p q : V) (C : Finset V), (cls p).IsEps → (cls q).IsEps → Disjoint C K₁ →
      Disjoint (insert p (insert q C)) K₁ := by
    intro p q C hp hq hC
    rw [disjoint_insert_left, disjoint_insert_left]
    exact ⟨hεK p hp, hεK q hq, hC⟩
  -- the remaining chains
  set R := nonEps M.atoms cls \ K₁ with hRdef
  have hRvb : ∀ x ∈ R, x = v₂ ∨ x = b := by
    intro x hx
    obtain ⟨hxN, hxK⟩ := mem_sdiff.mp hx
    obtain ⟨hxA, hxn⟩ := mem_filter.mp hxN
    rcases (hchar x hxA).mp hxn with e | e | e
    · exact absurd (e ▸ hv₁K) hxK
    · exact Or.inl e
    · exact Or.inr e
  have hRK : Disjoint R K₁ := sdiff_disjoint
  have hRA : R ⊆ M.atoms := fun x hx => (mem_filter.mp (mem_sdiff.mp hx).1).1
  have hallR : ∀ x ∈ M.atoms, ¬ (cls x).IsEps → x ∈ K₁ ∨ x ∈ R := by
    intro x hx hn
    by_cases hxK : x ∈ K₁
    · exact Or.inl hxK
    · exact Or.inr (mem_sdiff.mpr ⟨mem_filter.mpr ⟨hx, hn⟩, hxK⟩)
  have hKN : K₁ ⊆ nonEps M.atoms cls := fun x hx => mem_filter.mpr ⟨hK₁.2.1 hx, hKeps x hx⟩
  have hN3 : (nonEps M.atoms cls).card = 3 := by rw [card_nonEps, hcase.1, hcase.2]
  have hcard3 : K₁.card + R.card = 3 := by
    rw [hRdef, card_sdiff_of_subset hKN, hN3]; have := card_le_card hKN; omega
  have hR2 : R.card ≤ 2 := by
    have : R ⊆ {v₂, b} := fun x hx => by rcases hRvb x hx with rfl | rfl <;> simp
    exact (card_le_card this).trans (card_le_two)
  rcases remaining_cases hK₁ hv₁K h2 h3 hn2 hnb h2b hchar with hR0 | hRc | ⟨hReq, hc2, hcb⟩
  · -- (6b), no other chain
    have hR0' : R = ∅ := hR0
    have hall : ∀ x ∈ M.atoms, ¬ (cls x).IsEps → x ∈ K₁ := by
      intro x hx hn
      rcases hallR x hx hn with h | h
      · exact h
      · rw [hR0'] at h; exact absurd h (notMem_empty x)
    exact hstep.trans (mul_le_mul' le_rfl ((c6b0_bound hL1 h102a hS hF hnodd hnc hP hsz h1 h2 h3 h12 h1b h2b
      d1 d2 d3 h4 hchar hK₁ hall).trans hX0))
  · -- one other chain `R`
    obtain ⟨y₃, y₄, hx, hy34, hε3, hε4, hne34⟩ := hS.chains hnodd hnc R hRc
    set p := M.atom (M.mate y₃) with hp
    set q := M.atom (M.mate y₄) with hq
    have hpA : p ∈ M.atoms := M.atom_mem _
    have hqA : q ∈ M.atoms := M.atom_mem _
    by_cases hbb : M.bondsBetween p q ≤ 1
    · exact hstep.trans (mul_le_mul' le_rfl ((c6b1_bound hL1 h102b hRd1 hS hF hnodd hnc hP hsz h1 h2 h3 h12 h1b
        h2b d1 d2 d3 h4 hK₁ hRc hRK hallR hcard3 hx hbb).trans hX1))
    · have hbb2 : M.bondsBetween p q = 2 := by have := hS.noTriple p q; omega
      have hpR : p ∉ R := fun h => (mem_filter.mp (mem_sdiff.mp h).1).2 hε3
      have hqR : q ∉ R := fun h => (mem_filter.mp (mem_sdiff.mp h).1).2 hε4
      have hbal : ∀ x ∈ R, M.outdeg x = M.indeg x := fun x hx' => by
        have := hdir1 x (hRA hx') (mem_filter.mp (mem_sdiff.mp hx').1).2; rw [this.1, this.2]
      have hdir := chain_cross_opposite M R hbal hy34 hx
      obtain ⟨a, b', hTh⟩ := thetaGenData_double hS.noLoop hS.caps hRA hpA hqA hpR hqR hne34 hx rfl rfl
        (fun x hx' => hdir1 x (hRA hx') (mem_filter.mp (mem_sdiff.mp hx').1).2) hdir (chain_piece_connected hRc)
        hbb2
      refine h6 _ p q a b' _ _ R ∅ hTh (hdisj3 p q R hε3 hε4 hRK) ?_ (by omega) ?_
      · exact (card_insert_le _ _).trans (by have := card_insert_le q R; omega)
      · exact hQ_double hLp h2b hch hRA hpA hqA (deg_eps_four hS hnodd hpA hε3) (deg_eps_four hS hnodd hqA hε4)
          hpR hqR hne34 hx hy34 hdir hRvb hRc.1
  · -- two singleton chains `{v₂}`, `{b}`
    have hReq' : R = {v₂, b} := hReq
    have h2K : v₂ ∉ K₁ := fun h => by
      have : v₂ ∉ R := fun h' => (mem_sdiff.mp h').2 h
      rw [hReq'] at this; exact this (by simp)
    have hbK : b ∉ K₁ := fun h => by
      have : b ∉ R := fun h' => (mem_sdiff.mp h').2 h
      rw [hReq'] at this; exact this (by simp)
    have hK₁c : K₁.card = 1 := by
      have : R.card = 2 := by rw [hReq', card_pair h2b]
      omega
    have hall : ∀ x ∈ M.atoms, ¬ (cls x).IsEps → x ∈ K₁ ∨ x = v₂ ∨ x = b := by
      intro x hx hn
      rcases hallR x hx hn with h | h
      · exact Or.inl h
      · right; rw [hReq'] at h; simpa using h
    obtain ⟨y₁, y₂, hx2, hy12, hε1, hε2, hne12⟩ := hS.chains hnodd hnc {v₂} hc2
    obtain ⟨y₃, y₄, hxb, hy34, hε3, hε4, hne34⟩ := hS.chains hnodd hnc {b} hcb
    have hA1 : M.atom (M.mate y₁) ∈ M.atoms := M.atom_mem _
    have hA2 : M.atom (M.mate y₂) ∈ M.atoms := M.atom_mem _
    have hA3 : M.atom (M.mate y₃) ∈ M.atoms := M.atom_mem _
    have hA4 : M.atom (M.mate y₄) ∈ M.atoms := M.atom_mem _
    have hsv₂ : ∀ w, (cls w).IsEps → w ∉ ({v₂} : Finset V) := fun w hw h => hn2 ((mem_singleton.mp h) ▸ hw)
    have hsb : ∀ w, (cls w).IsEps → w ∉ ({b} : Finset V) := fun w hw h => hnb ((mem_singleton.mp h) ▸ hw)
    have hv₂A : ({v₂} : Finset V) ⊆ M.atoms := by simpa using h2
    have hbA : ({b} : Finset V) ⊆ M.atoms := by simpa using h3
    have hdir2 := chain_cross_opposite M {v₂} (fun x hx' => by
      rw [mem_singleton.mp hx', (hdir1 v₂ h2 hn2).1, (hdir1 v₂ h2 hn2).2]) hy12 hx2
    have hdirb := chain_cross_opposite M {b} (fun x hx' => by
      rw [mem_singleton.mp hx', (hdir1 b h3 hnb).1, (hdir1 b h3 hnb).2]) hy34 hxb
    have hdis2 : Disjoint ({v₂} : Finset V) K₁ := disjoint_singleton_left.mpr h2K
    have hdisb : Disjoint ({b} : Finset V) K₁ := disjoint_singleton_left.mpr hbK
    have hcard3' : ∀ (p q : V) (C : Finset V), C.card = 1 → (insert p (insert q C)).card ≤ 5 := by
      intro p q C hC
      exact (card_insert_le _ _).trans (by have := card_insert_le q C; omega)
    have hpin : (∀ x ∈ ({v₂} : Finset V), x = v₂ ∨ x = b) := fun x hx' => Or.inl (mem_singleton.mp hx')
    have hpinb : (∀ x ∈ ({b} : Finset V), x = v₂ ∨ x = b) := fun x hx' => Or.inr (mem_singleton.mp hx')
    by_cases hd2 : M.bondsBetween (M.atom (M.mate y₁)) (M.atom (M.mate y₂)) = 2
    · -- (6d): `{v₂}` doubly bonded
      obtain ⟨a, b', hTh⟩ := thetaGenData_double hS.noLoop hS.caps hv₂A hA1 hA2 (hsv₂ _ hε1) (hsv₂ _ hε2) hne12 hx2
        rfl rfl (fun x hx' => by rw [mem_singleton.mp hx']; exact hdir1 v₂ h2 hn2) hdir2
        (chain_piece_connected hc2) hd2
      exact h6 _ _ _ a b' _ _ {v₂} ∅ hTh (hdisj3 _ _ _ hε1 hε2 hdis2) (hcard3' _ _ _ (card_singleton _))
        (by simp) (hQ_double hLp h2b hch hv₂A hA1 hA2 (deg_eps_four hS hnodd hA1 hε1)
          (deg_eps_four hS hnodd hA2 hε2) (hsv₂ _ hε1) (hsv₂ _ hε2) hne12 hx2 hy12 hdir2 hpin
          (singleton_nonempty _))
    by_cases hdb : M.bondsBetween (M.atom (M.mate y₃)) (M.atom (M.mate y₄)) = 2
    · -- (6d): `{b}` doubly bonded
      obtain ⟨a, b', hTh⟩ := thetaGenData_double hS.noLoop hS.caps hbA hA3 hA4 (hsb _ hε3) (hsb _ hε4) hne34 hxb
        rfl rfl (fun x hx' => by rw [mem_singleton.mp hx']; exact hdir1 b h3 hnb) hdirb
        (chain_piece_connected hcb) hdb
      exact h6 _ _ _ a b' _ _ {b} ∅ hTh (hdisj3 _ _ _ hε3 hε4 hdisb) (hcard3' _ _ _ (card_singleton _))
        (by simp) (hQ_double hLp h2b hch hbA hA3 hA4 (deg_eps_four hS hnodd hA3 hε3)
          (deg_eps_four hS hnodd hA4 hε4) (hsb _ hε3) (hsb _ hε4) hne34 hxb hy34 hdirb hpinb
          (singleton_nonempty _))
    have hb2 : M.bondsBetween (M.atom (M.mate y₁)) (M.atom (M.mate y₂)) ≤ 1 := by
      have := hS.noTriple (M.atom (M.mate y₁)) (M.atom (M.mate y₂)); omega
    have hbb : M.bondsBetween (M.atom (M.mate y₃)) (M.atom (M.mate y₄)) ≤ 1 := by
      have := hS.noTriple (M.atom (M.mate y₃)) (M.atom (M.mate y₄)); omega
    have hopd : (s(M.atom (M.mate y₁), M.atom (M.mate y₂)) = s(M.atom (M.mate y₃), M.atom (M.mate y₄)) →
        M.bondsBetween (M.atom (M.mate y₁)) (M.atom (M.mate y₂)) = 0) →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ((cls v₁).lab / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) *
            Real.log L ^ (8 : ℝ)) * ENNReal.ofReal (L ^ T) := fun hsame =>
      hstep.trans (mul_le_mul' le_rfl ((c6b2_bound hL1 h102c hRd1 hRd2 hS hF hnodd hnc hP hsz h1 h2 h3 h12 h1b
        h2b d1 d2 d3 h4 hK₁ hK₁c h2K hbK hall hc2 hcb hx2 hy12 hne12 hxb hy34 hne34 hb2 hbb hsame).trans hX2))
    by_cases hsym : s(M.atom (M.mate y₁), M.atom (M.mate y₂)) = s(M.atom (M.mate y₃), M.atom (M.mate y₄))
    · by_cases h0 : M.bondsBetween (M.atom (M.mate y₁)) (M.atom (M.mate y₂)) = 0
      · exact hopd fun _ => h0
      -- (6d): the generalized theta chain on `{v₂}`, `{b}` with one bond between the common ends
      have h1b' : M.bondsBetween (M.atom (M.mate y₁)) (M.atom (M.mate y₂)) = 1 := by omega
      set e₁ := M.atom (M.mate y₁) with he₁
      set e₂ := M.atom (M.mate y₂) with he₂
      have hpC : e₁ ∉ ({v₂} : Finset V) ∪ {b} := by
        rw [mem_union, not_or]; exact ⟨hsv₂ _ hε1, hsb _ hε1⟩
      have hqC : e₂ ∉ ({v₂} : Finset V) ∪ {b} := by
        rw [mem_union, not_or]; exact ⟨hsv₂ _ hε2, hsb _ hε2⟩
      have hd1' : M.outdeg v₂ = 1 ∧ M.indeg v₂ = 1 := hdir1 v₂ h2 hn2
      have hdb' : M.outdeg b = 1 ∧ M.indeg b = 1 := hdir1 b h3 hnb
      have hpv : e₁ ≠ v₂ := fun e => hn2 (e ▸ hε1)
      have hpb : e₁ ≠ b := fun e => hnb (e ▸ hε1)
      have hqv : e₂ ≠ v₂ := fun e => hn2 (e ▸ hε2)
      have hqb : e₂ ≠ b := fun e => hnb (e ▸ hε2)
      have hfin : ∀ (y₃' y₄' : D), crossDarts M {b} = {y₃', y₄'} → M.atom (M.mate y₃') = e₁ →
          M.atom (M.mate y₄') = e₂ → M.countA L γ δ C1 (0 : Mom d) Adm P ≤
            ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ((cls v₁).lab / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) *
              Real.log L ^ (8 : ℝ)) * ENNReal.ofReal (L ^ T) := by
        intro y₃' y₄' hxb' h3' h4''
        obtain ⟨a, hTh⟩ := thetaGenData_single hS.noLoop hS.caps h2 h3 hA1 hA2 h2b hpv hpb hqv hqb hne12 hx2 rfl rfl
          hxb' h3' h4'' hd1' hdb' hdir2 h1b'
        refine h6 _ e₁ e₂ a _ _ _ {v₂} {b} hTh ?_ ?_ (by simp) ?_
        · rw [disjoint_insert_left, disjoint_insert_left]
          exact ⟨hεK _ hε1, hεK _ hε2, disjoint_union_left.mpr ⟨hdis2, hdisb⟩⟩
        · refine (card_insert_le _ _).trans ?_
          have := card_insert_le e₂ (({v₂} : Finset V) ∪ {b})
          have := card_union_le ({v₂} : Finset V) {b}
          simp only [card_singleton] at this
          omega
        · exact hQ_single hLp h2b hch h2 h3 hA1 hA2 (deg_eps_four hS hnodd hA1 hε1)
            (deg_eps_four hS hnodd hA2 hε2) hpC hqC hne12 hx2 hy12 hdir2
      rcases Sym2.eq_iff.mp hsym with ⟨e13, e24⟩ | ⟨e14, e23⟩
      · exact hfin y₃ y₄ hxb e13.symm e24.symm
      · exact hfin y₄ y₃ (by rw [hxb]; exact pair_comm _ _) e14.symm e23.symm
    · exact hopd fun h => absurd h hsym

end

end WaveTurbulence.GammaLow.FinalCount.Count
