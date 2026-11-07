/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5Basic
public import WaveTurbulence.Foundations.FinalCount.ChainRemoval96
public import WaveTurbulence.Foundations.FinalCount.Rough96
public import WaveTurbulence.Foundations.FinalCount.Case5Fin
public import WaveTurbulence.Foundations.FinalCount.C5Fold
public import WaveTurbulence.Foundations.FinalCount.C5Vine
import Mathlib.Tactic

/-! # Prop 9.6, case (5), one chain (`α` and `β` in the same chain): operation (c), then Prop 10.4(1) -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8.P101

/-- **DH23 Prop 10.4(1) at a fixed `L`** (the body of `prop104_one`), for molecules over `V : Type u`, `D : Type v`. -/
def P104At.{u', v'} (d : ℕ) (γ δ η C1 L : ℝ) (m : ℕ) : Prop :=
  ∀ {V : Type u'} {D : Type v'} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), M.IsMolecule →
    (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
    (∀ p q r s, 3 ≤ M.bondsBetween p q → 3 ≤ M.bondsBetween r s → s(p, q) = s(r, s)) →
    (∀ p q, M.bondsBetween p q ≤ 3) → (M.bonds.card : ℤ) = 2 * M.atoms.card - 1 →
    (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m → ¬ HasBadBetaCut M → (∃ v₂ : V, v₂ ∉ M.atoms) →
    ¬ IsVineIIHalfClosure M →
    ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
      AFree M d L γ δ η C1 P ≤ ENNReal.ofReal (L ^ (-(4 / 7 * min γ (1 - γ))))

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The erased-count admissibility is below `lgAdm` when no protected atom survives. -/
theorem erased_le_afree (M : Molecule V D) {d : ℕ} {L γ δ η η' C1 : ℝ} (hL : 1 ≤ L) (hη : η' ≤ η)
    (B K : Finset V) (hB : ∀ v ∈ M.atoms, v ∉ K → v ∉ B) (P : Finset V → ℝ)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → LargeGapOff B M L γ η (0 : Mom d) κ ∧ CellGapRestriction M L (0 : Mom d) P (GapScale L) κ) :
    MoleProp.countAFree (Degen.eraseAtoms M K) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M K Adm) P ≤
      AFree (Degen.eraseAtoms M K) d L γ δ η' C1 P := by
  refine countAFree_mono_adm _ (fun κ' hκ' => ?_)
  have h1 := projected_largeGapOff M L γ η (0 : Mom d) B K Adm (fun κ h => (hAdm κ h).1) κ' hκ'
  have h2 := projected_cellGap M L (0 : Mom d) K Adm P (fun κ h => (hAdm κ h).2) κ' hκ'
  refine ⟨fun x y hxy hdir => ?_, h2⟩
  have hv : (Degen.eraseAtoms M K).atom x ∈ (Degen.eraseAtoms M K).atoms := (Degen.eraseAtoms M K).atom_mem x
  have hv' : (Degen.eraseAtoms M K).atom x ∈ M.atoms \ K := hv
  have hvB : (Degen.eraseAtoms M K).atom x ∉ B := hB _ (mem_sdiff.mp hv').1 (mem_sdiff.mp hv').2
  exact (Real.rpow_le_rpow_of_exponent_le hL (by linarith)).trans (h1 _ hvB x y rfl hxy.symm hdir)


/-- The erased molecule has no multi-bond beyond double bonds. -/
theorem bb_erase_le_two (M : Molecule V D) (K : Finset V) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (h2 : ∀ p q, M.bondsBetween p q ≤ 2) (p q : V) : (Degen.eraseAtoms M K).bondsBetween p q ≤ 2 := by
  by_cases hpq : p = q
  · subst hpq
    rw [bondsBetween_self_eq_zero (fun z => hloop z.val)]; omega
  · exact (bondsBetween_eraseAtoms_le M K hpq).trans (h2 p q)


/-- **Case (5), `α` and `β` in one chain `K`.** Operation (c) at `ρ`, then Prop 10.4(1) on `𝕄₀ ∖ K`. -/
theorem s1_key {d : ℕ} {L γ δ η C1 ρ : ℝ} {m : ℕ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (hL1 : 1 ≤ L)
    (hlog : 1 ≤ Real.log L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1) (hρ : 0 < ρ)
    (h104 : P104At.{u, v} d γ δ (η / 2) C1 L m)
    (M : Molecule V D) (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (hS : FinalShape M cls odd) (hF : FinalDec M cls L γ η Adm) (hnodd : ¬ odd) (hnc : ¬ ∀ a ∈ M.atoms, M.deg a = 2)
    (hη : 0 < η) (hP : ∀ S, 0 ≤ P S)
    (hMA : MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm) (hsz : (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m)
    {a₀ b₀ : V} (ha₀ : a₀ ∈ M.atoms) (hb₀ : b₀ ∈ M.atoms) (hab : a₀ ≠ b₀)
    (hdeg2a : M.deg a₀ = 2) (hdeg2b : M.deg b₀ = 2)
    (hdeg4 : ∀ v ∈ M.atoms, v ≠ a₀ → v ≠ b₀ → M.deg v = 4)
    (hEps : ∀ v ∈ M.atoms, v ≠ a₀ → v ≠ b₀ → (cls v).IsEps)
    {K : Finset V} (hK : IsChainSet M cls K) (hKeq : K = {a₀, b₀})
    (hAdm : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ K ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
      ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖)
    (hfr : ∃ w, w ∉ M.atoms)
    (hNB : ∀ v ∈ M.atoms, (cls v).IsEps → ∀ v₂ x₁ x₂, M.IsCutData v v₂ x₁ x₂ → M.IsAlphaCut v v₂ x₁ x₂) :
    M.countA L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ρ⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ)) *
        ENNReal.ofReal (L ^ (-(4 / 7 * min γ (1 - γ)))) := by
  classical
  have hLp : 0 < L := by linarith
  have hM : M.IsMolecule := hS.isMolecule
  set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
  refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
  obtain ⟨y₁, y₂, hcross, hy12, hε1, hε2, hne⟩ := hS.chains hnodd hnc K hK
  have hKA : K ⊆ M.atoms := hK.2.1
  have hch : ∀ b ∈ K, M.outdeg b = 1 ∧ M.indeg b = 1 := by
    intro b hb
    have hb' : b = a₀ ∨ b = b₀ := by rw [hKeq] at hb; simpa using hb
    have hd : M.deg b = 2 := by rcases hb' with rfl | rfl <;> assumption
    exact hS.dir2 b (hKA hb) hd
  have hcard : (crossDarts M K).card = 2 := by rw [hcross, card_pair hy12]
  have hpost := connected_erase_of_two_cross M hS.conn (fun a ha => by
    rcases hS.evenDeg hnodd a ha with h | h <;> omega) K hcard
  have hAdm'' : ∀ κ, (Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) →
      ∃ y y', M.atom y ∈ K ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
        ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ := fun κ hκ => hAdm κ hκ.1
  have hstep := opC_rho (L := L) (γ := γ) (δ := δ) (C1 := C1) (ρ := ρ) hγ hL1 hlog hδ hC1 hρ M hS.caps hS.noLoop
    hS.conn K y₁ y₂ hKA hch hcross hne (chain_piece_connected hK) hpost P' (fun S _ => hP _)
    (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) hAdm''
  refine hstep.trans (mul_le_mul' le_rfl ?_)
  -- the erased molecule
  set N := Degen.eraseAtoms M K with hN
  have hKcard : K.card = 2 := by rw [hKeq, card_pair hab]
  obtain ⟨T, hTY, _⟩ := twoExit_of_chain M hKA (fun v hv => by rw [(hch v hv).1, (hch v hv).2]) hcross hy12 hne
  have hbondsK := erase_chain_bonds M T (fun v hv => by
    rw [hTY] at hv
    have hb' : v = a₀ ∨ v = b₀ := by rw [hKeq] at hv; simpa using hv
    rcases hb' with rfl | rfl <;> assumption)
  rw [hTY, ← hN] at hbondsK
  have hMb := c5_two_bonds ha₀ hb₀ hab hdeg2a hdeg2b hdeg4
  have hNatoms : N.atoms.card = M.atoms.card - 2 := by
    rw [hN]; change (M.atoms \ K).card = _
    rw [card_sdiff_of_subset hKA, hKcard]
  have h2V : 2 ≤ M.atoms.card := by have := card_le_card hKA; omega
  have hE : (N.bonds.card : ℤ) = 2 * N.atoms.card - 1 := by
    have : N.atoms.card + 2 = M.atoms.card := by omega
    omega
  have hcapN := caps_eraseAtoms K hS.caps
  obtain ⟨z, hz, hz4, _⟩ := exists_deg_ne_four N hcapN hE
  have hmolN : N.IsMolecule := isMolecule_of_connected N hcapN hpost hz hz4
  have hle2 : ∀ p q, N.bondsBetween p q ≤ 2 := bb_erase_le_two M K hS.noLoop hS.noTriple
  obtain ⟨c, hc⟩ : K.Nonempty := hK.1
  have hfreshN : ∃ w, w ∉ N.atoms := ⟨c, fun h => (mem_sdiff.mp h).2 hc⟩
  have hszN : (N.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m :=
    le_trans (by rw [hNatoms]; exact_mod_cast Nat.sub_le _ _) hsz
  have hdeg4N : ∀ u ∈ N.atoms, M.deg u = 4 := by
    intro u hu
    have hu' := mem_sdiff.mp hu
    exact hdeg4 u hu'.1 (fun h => hu'.2 (by rw [hKeq, h]; simp)) (fun h => hu'.2 (by rw [hKeq, h]; simp))
  have hbad : ¬ HasBadBetaCut N :=
    not_bad_erase M K hS.conn hpost hfr hdeg4N (fun v hv => hNB v (mem_sdiff.mp hv).1
      (hEps v (mem_sdiff.mp hv).1 (fun h => (mem_sdiff.mp hv).2 (by rw [hKeq, h]; simp))
        (fun h => (mem_sdiff.mp hv).2 (by rw [hKeq, h]; simp))))
  have hvine : ¬ IsVineIIHalfClosure N := fun h => by
    obtain ⟨p, _, q, _, h3⟩ := halfClosure_triple h
    have := hle2 p q; omega
  have hA1 := h104 N hmolN hpost (fun p q r s h1 _ => absurd (hle2 p q) (by omega))
    (fun p q => by have := hle2 p q; omega) hE hszN hbad hfreshN hvine P' (fun S _ => hP _)
  refine le_trans ?_ hA1
  refine erased_le_afree M hL1 (by linarith : η / 2 ≤ η) (nonEps M.atoms cls) K ?_ P' _ ?_
  · intro v hv hvK hvB
    have := mem_filter.mp hvB
    refine this.2 (hEps v hv ?_ ?_)
    · intro h; apply hvK; rw [hKeq, h]; simp
    · intro h; apply hvK; rw [hKeq, h]; simp
  · intro κ hκ
    refine ⟨fun v hvB x y hx hy hxy => ?_, hκ.2⟩
    have hv : v ∈ M.atoms := hx ▸ M.atom_mem x
    have hε : (cls v).IsEps := by
      by_contra hne'; exact hvB (mem_filter.mpr ⟨hv, hne'⟩)
    exact (hF.epsLG κ hκ.1 v hv hε x y hx hy hxy).le

end
end WaveTurbulence.FinalCountG8
