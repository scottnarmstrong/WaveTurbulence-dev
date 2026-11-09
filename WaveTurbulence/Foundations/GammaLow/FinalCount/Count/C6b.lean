/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6Theta
public import WaveTurbulence.Foundations.FinalCount.Case5S2
public import WaveTurbulence.Foundations.FinalCount.ChainRemoval96
import Mathlib.Tactic

/-! # Case (6b): operation (c), operations (d), Prop 10.2(1) (packet L6-COUNT, Case6TopLow; M2 §4.10 (6b))

When the closure `𝕄₁` (operation (c) on the chain `K₁` of `v₁`, operation (d) on every other chain) has no triple bond,
`E = 2V − 1` and Prop 10.2(1) gives `𝔄(𝕄₁) ≲ L^{−3γ/5}`.
* `c6_opc_step`: operation (c) on `K₁` (main's `opC_rho`, the gap of `v₁` by `alphaGap`), after the cell relaxation.
* `c6b0_bound`: `K₁` holds all three non-`ε` atoms; Prop 10.2(1) on `𝕄₀ ∖ K₁` (as main's `s1_key`).
* `c6b1_bound`: the other non-`ε` atoms form one chain `C` with far ends joined by at most one bond: operation (d) on `C`
  (main's `OpDAt`), then Prop 10.2(1) at `η/2` on the post (as main's `s2_key`).
Helpers: `bonds_three` (`2E + 6 = 4V`), `chain_erase` (the exits of a chain away from `K` after erasing `K`),
`chain_far_from` (a chain disjoint from another chain is not adjacent to it). -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8 WaveTurbulence.FinalCountG8.P101

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- `2E + 6 = 4V` with three atoms of degree two, all others of degree four. -/
theorem bonds_three {M : Molecule V D} {v₁ v₂ b : V} (h1 : v₁ ∈ M.atoms) (h2 : v₂ ∈ M.atoms) (h3 : b ∈ M.atoms)
    (h12 : v₁ ≠ v₂) (h1b : v₁ ≠ b) (h2b : v₂ ≠ b) (d1 : M.deg v₁ = 2) (d2 : M.deg v₂ = 2) (d3 : M.deg b = 2)
    (h4 : ∀ v ∈ M.atoms, v ≠ v₁ → v ≠ v₂ → v ≠ b → M.deg v = 4) : 2 * M.bonds.card + 6 = 4 * M.atoms.card := by
  classical
  have hs := Mole.sum_degrees_eq_two_mul_bonds M
  have hsub : ({v₁, v₂, b} : Finset V) ⊆ M.atoms := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl | rfl <;> assumption
  have hsplit := sum_sdiff hsub (f := M.deg)
  have hT : ∑ x ∈ ({v₁, v₂, b} : Finset V), M.deg x = 6 := by
    rw [sum_insert (by simp [h12, h1b]), sum_pair h2b, d1, d2, d3]
    norm_num
  have hR : ∑ x ∈ M.atoms \ {v₁, v₂, b}, M.deg x = ∑ _x ∈ M.atoms \ {v₁, v₂, b}, 4 := sum_congr rfl fun x hx => by
    obtain ⟨hxA, hxn⟩ := mem_sdiff.mp hx
    simp only [mem_insert, mem_singleton, not_or] at hxn
    exact h4 x hxA hxn.1 hxn.2.1 hxn.2.2
  rw [hR, sum_const, smul_eq_mul, hT] at hsplit
  have hc := card_sdiff_of_subset hsub
  have h3c : ({v₁, v₂, b} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [h12, h1b]), card_pair h2b]
  have hle := card_le_card hsub
  omega

/-- The exits of a chain `C` away from `K` after erasing `K`. -/
theorem chain_erase {M : Molecule V D} {K C : Finset V} {y₃ y₄ : D} (hc : crossDarts M C = {y₃, y₄})
    (p₃ : M.atom y₃ ∉ K ∧ M.atom (M.mate y₃) ∉ K) (p₄ : M.atom y₄ ∉ K ∧ M.atom (M.mate y₄) ∉ K) :
    crossDarts (Degen.eraseAtoms M K) C = {⟨y₃, p₃⟩, ⟨y₄, p₄⟩} := by
  ext z
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hz
    have hz' : z.val ∈ crossDarts M C :=
      (mem_crossDarts (N := M)).mpr ((mem_crossDarts (N := Degen.eraseAtoms M K)).mp hz)
    rw [hc] at hz'
    rcases mem_insert.mp hz' with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (mem_singleton.mp h))
  · rintro (rfl | rfl)
    · exact (mem_crossDarts (N := Degen.eraseAtoms M K)).mpr
        ((mem_crossDarts (N := M)).mp (show y₃ ∈ crossDarts M C by rw [hc]; simp))
    · exact (mem_crossDarts (N := Degen.eraseAtoms M K)).mpr
        ((mem_crossDarts (N := M)).mp (show y₄ ∈ crossDarts M C by rw [hc]; simp))

/-- A chain disjoint from the chain `K` has no bond into `K`. -/
theorem chain_far_from {M : Molecule V D} {cls : V → Cls} {K C : Finset V} (hK : IsChainSet M cls K)
    (hC : IsChainSet M cls C) (hCK : Disjoint C K) {x : D} (hx : M.atom x ∈ C) :
    M.atom x ∉ K ∧ M.atom (M.mate x) ∉ K := by
  refine ⟨disjoint_left.mp hCK hx, fun hm => ?_⟩
  have := hK.2.2.2.1 _ hm (M.atom x) ⟨M.mate x, rfl, by rw [M.mate_mate]⟩ (hC.2.2.1 _ hx)
  exact disjoint_left.mp hCK hx this

/-- **Operation (c) on the chain `K₁` of `v₁`**, after the cell relaxation. -/
theorem c6_opc_step {d : ℕ} {L γ δ η C1 : ℝ} (hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1) (hL1 : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1) {M : Molecule V D} {cls : V → Cls} {odd : Prop}
    {Adm : (D → (Fin d → ℤ)) → Prop} {P : Finset V → ℝ} (hS : FinalShape M cls odd) (hF : FinalDec M cls L γ η Adm)
    (hnodd : ¬ odd) (hnc : ¬ ∀ a ∈ M.atoms, M.deg a = 2) (hP : ∀ S, 0 ≤ P S)
    (hMA : MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm) {v₁ : V} {K₁ : Finset V} (hv₁ : v₁ ∈ M.atoms)
    (hα₁ : (cls v₁).IsAlpha) (hK₁ : IsChainSet M cls K₁) (hv₁K : v₁ ∈ K₁) :
    M.countA L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ((cls v₁).lab / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ)) *
        MoleProp.countAFree (Degen.eraseAtoms M K₁) L γ δ C1 (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility M K₁ (fun κ => Adm κ ∧
            CellGapRestriction M L (0 : Mom d) (fun S => P (Mole.appbLinkParent M S)) (GapScale L) κ))
          (fun S => P (Mole.appbLinkParent M S)) := by
  classical
  have hLp : 0 < L := by linarith
  have hM : M.IsMolecule := hS.isMolecule
  refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
  obtain ⟨y₁, y₂, hcross, hy12, _, _, hne⟩ := hS.chains hnodd hnc K₁ hK₁
  have hKA : K₁ ⊆ M.atoms := hK₁.2.1
  have hch : ∀ x ∈ K₁, M.outdeg x = 1 ∧ M.indeg x = 1 := by
    intro x hx
    have h2 : M.deg x ≤ 2 := (hS.classes x (hKA hx)).mpr (hK₁.2.2.1 x hx)
    have h4 := hS.evenDeg hnodd x (hKA hx)
    exact hS.dir2 x (hKA hx) (by omega)
  have hcard : (crossDarts M K₁).card = 2 := by rw [hcross, card_pair hy12]
  have hpost := connected_erase_of_two_cross M hS.conn (fun x hx => by
    rcases hS.evenDeg hnodd x hx with h | h <;> omega) K₁ hcard
  have hlab := hF.labRange v₁ hv₁ hα₁
  have hR0 : 0 < (cls v₁).lab / 2 := by have := lt_of_lt_of_le (inv_pos.mpr hLp) hlab.1; positivity
  have hdv : M.deg v₁ = 2 := by
    have := (hS.classes v₁ hv₁).mpr (alpha_not_eps hα₁)
    rcases hS.evenDeg hnodd v₁ hv₁ with h | h <;> omega
  exact opC_rho (L := L) (γ := γ) (δ := δ) (C1 := C1) (ρ := (cls v₁).lab / 2) hγ01 hL1 hlog hδ hC1 hR0
    M hS.caps hS.noLoop hS.conn K₁ y₁ y₂ hKA hch hcross hne (chain_piece_connected hK₁) hpost _
    (fun S' _ => hP _) _ (fun κ hκ => by
      obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_darts M hdv
      exact ⟨x, y, hx ▸ hv₁K, hy.trans hx.symm, hxy, (hF.alphaGap κ hκ.1 v₁ hv₁ hα₁ x y hx hy hxy).1⟩)

open Classical in
/-- The `ε`-atoms are LG in every admissible decoration (`LargeGapOff` off the non-`ε` atoms), with the cell
restriction. -/
theorem lgoff_of_finalDec {M : Molecule V D} {cls : V → Cls} {d : ℕ} {L γ η : ℝ} {Adm : (D → (Fin d → ℤ)) → Prop}
    (hF : FinalDec M cls L γ η Adm) (P' : Finset V → ℝ) :
    ∀ κ, (Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) →
      LargeGapOff (nonEps M.atoms cls) M L γ η (0 : Mom d) κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ := by
  intro κ hκ
  refine ⟨fun w hwB x y hx hy hxy => ?_, hκ.2⟩
  have hw : w ∈ M.atoms := hx ▸ M.atom_mem x
  have hε : (cls w).IsEps := by by_contra hn; exact hwB (mem_filter.mpr ⟨hw, hn⟩)
  exact (hF.epsLG κ hκ.1 w hw hε x y hx hy hxy).le

/-- **(6b) with no other chain**: `K₁` holds every non-`ε` atom; Prop 10.2(1) on `𝕄₀ ∖ K₁`. -/
theorem c6b0_bound {d m : ℕ} {L γ δ η C1 : ℝ} (hL1 : 1 ≤ L) (h102 : Prop102At.{u, v} d L γ δ η C1 m)
    {M : Molecule V D} {cls : V → Cls} {odd : Prop} {Adm : (D → (Fin d → ℤ)) → Prop} {P : Finset V → ℝ}
    (hS : FinalShape M cls odd) (hF : FinalDec M cls L γ η Adm) (hnodd : ¬ odd)
    (hnc : ¬ ∀ a ∈ M.atoms, M.deg a = 2) (hP : ∀ S, 0 ≤ P S) (hsz : (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m)
    {v₁ v₂ b : V} (h1 : v₁ ∈ M.atoms) (h2 : v₂ ∈ M.atoms) (h3 : b ∈ M.atoms) (h12 : v₁ ≠ v₂) (h1b : v₁ ≠ b)
    (h2b : v₂ ≠ b) (d1 : M.deg v₁ = 2) (d2 : M.deg v₂ = 2) (d3 : M.deg b = 2)
    (h4 : ∀ v ∈ M.atoms, v ≠ v₁ → v ≠ v₂ → v ≠ b → M.deg v = 4)
    (hchar : ∀ v ∈ M.atoms, ¬ (cls v).IsEps ↔ (v = v₁ ∨ v = v₂ ∨ v = b))
    {K₁ : Finset V} (hK₁ : IsChainSet M cls K₁) (hall : ∀ v ∈ M.atoms, ¬ (cls v).IsEps → v ∈ K₁) :
    MoleProp.countAFree (Degen.eraseAtoms M K₁) L γ δ C1 (0 : Mom d)
        (MoleProp.erasedFreeAdmissibility M K₁ (fun κ => Adm κ ∧
          CellGapRestriction M L (0 : Mom d) (fun S => P (Mole.appbLinkParent M S)) (GapScale L) κ))
        (fun S => P (Mole.appbLinkParent M S)) ≤
      ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ)))) := by
  classical
  set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
  obtain ⟨y₁, y₂, hcross, hy12, _, _, hne⟩ := hS.chains hnodd hnc K₁ hK₁
  have hKA : K₁ ⊆ M.atoms := hK₁.2.1
  have hK₁eq : K₁ = {v₁, v₂, b} := by
    ext x; constructor
    · intro hx
      rcases (hchar x (hKA hx)).mp (hK₁.2.2.1 x hx) with rfl | rfl | rfl <;> simp
    · intro hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hall _ h1 ((hchar _ h1).mpr (Or.inl rfl))
      · exact hall _ h2 ((hchar _ h2).mpr (Or.inr (Or.inl rfl)))
      · exact hall _ h3 ((hchar _ h3).mpr (Or.inr (Or.inr rfl)))
  have hdK : ∀ x ∈ K₁, M.deg x = 2 := by
    intro x hx; rw [hK₁eq] at hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hch : ∀ x ∈ K₁, M.outdeg x = M.indeg x := fun x hx => by
    have := hS.dir2 x (hKA hx) (hdK x hx); rw [this.1, this.2]
  have hcard : (crossDarts M K₁).card = 2 := by rw [hcross, card_pair hy12]
  have hpost := connected_erase_of_two_cross M hS.conn (fun x hx => by
    rcases hS.evenDeg hnodd x hx with h | h <;> omega) K₁ hcard
  obtain ⟨T, hTY, _⟩ := twoExit_of_chain M hKA hch hcross hy12 hne
  have hbondsK := erase_chain_bonds M T (fun x hx => by rw [hTY] at hx; exact hdK x hx)
  rw [hTY] at hbondsK
  set N := Degen.eraseAtoms M K₁ with hN
  have hMb := bonds_three h1 h2 h3 h12 h1b h2b d1 d2 d3 h4
  have hK3 : K₁.card = 3 := by rw [hK₁eq, card_insert_of_notMem (by simp [h12, h1b]), card_pair h2b]
  have hNatoms : N.atoms.card + 3 = M.atoms.card := by
    rw [hN]; change (M.atoms \ K₁).card + 3 = _
    rw [card_sdiff_of_subset hKA, hK3]; have := card_le_card hKA; omega
  have hE : (N.bonds.card : ℤ) = 2 * N.atoms.card - 1 := by omega
  have hcapN := caps_eraseAtoms K₁ hS.caps
  obtain ⟨z, hz, hz4, _⟩ := exists_deg_ne_four N hcapN hE
  have hmolN : N.IsMolecule := isMolecule_of_connected N hcapN hpost hz hz4
  have hle2 : ∀ p q, N.bondsBetween p q ≤ 2 := bb_erase_le_two M K₁ hS.noLoop hS.noTriple
  have hszN : (N.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m :=
    le_trans (by exact_mod_cast (by omega : N.atoms.card ≤ M.atoms.card)) hsz
  refine le_trans ?_ (h102 N hmolN hpost hle2 hE hszN P' (fun S _ => hP _))
  refine erased_le_afree M hL1 (le_refl η) (nonEps M.atoms cls) K₁ ?_ P' _ (lgoff_of_finalDec hF P')
  intro w hw hwK hwB
  exact hwK (hall w hw (mem_filter.mp hwB).2)

/-- **(6b) with one other chain `C`**: operation (d) on `C`, then Prop 10.2(1) at `η/2`. -/
theorem c6b1_bound {d m : ℕ} {L γ δ η C1 Kd Bd : ℝ} (hL1 : 1 ≤ L) (h102 : Prop102At.{u, v} d L γ δ (η / 2) C1 m)
    (hRd : OpDAt.{u, v} d L γ δ η C1 Kd Bd)
    {M : Molecule V D} {cls : V → Cls} {odd : Prop} {Adm : (D → (Fin d → ℤ)) → Prop} {P : Finset V → ℝ}
    (hS : FinalShape M cls odd) (hF : FinalDec M cls L γ η Adm) (hnodd : ¬ odd)
    (hnc : ¬ ∀ a ∈ M.atoms, M.deg a = 2) (hP : ∀ S, 0 ≤ P S) (hsz : (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m)
    {v₁ v₂ b : V} (h1 : v₁ ∈ M.atoms) (h2 : v₂ ∈ M.atoms) (h3 : b ∈ M.atoms) (h12 : v₁ ≠ v₂) (h1b : v₁ ≠ b)
    (h2b : v₂ ≠ b) (d1 : M.deg v₁ = 2) (d2 : M.deg v₂ = 2) (d3 : M.deg b = 2)
    (h4 : ∀ v ∈ M.atoms, v ≠ v₁ → v ≠ v₂ → v ≠ b → M.deg v = 4)
    {K₁ C : Finset V} (hK₁ : IsChainSet M cls K₁) (hC : IsChainSet M cls C) (hCK : Disjoint C K₁)
    (hall : ∀ v ∈ M.atoms, ¬ (cls v).IsEps → v ∈ K₁ ∨ v ∈ C) (hcard3 : K₁.card + C.card = 3)
    {y₃ y₄ : D} (hc2 : crossDarts M C = {y₃, y₄})
    (hbb : M.bondsBetween (M.atom (M.mate y₃)) (M.atom (M.mate y₄)) ≤ 1) :
    MoleProp.countAFree (Degen.eraseAtoms M K₁) L γ δ C1 (0 : Mom d)
        (MoleProp.erasedFreeAdmissibility M K₁ (fun κ => Adm κ ∧
          CellGapRestriction M L (0 : Mom d) (fun S => P (Mole.appbLinkParent M S)) (GapScale L) κ))
        (fun S => P (Mole.appbLinkParent M S)) ≤
      ENNReal.ofReal (Kd * Real.log L ^ Bd) * ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ)))) := by
  classical
  set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
  obtain ⟨y₁, y₂, hcross, hy12, _, _, hne⟩ := hS.chains hnodd hnc K₁ hK₁
  obtain ⟨y₃', y₄', hc2', hy34', hε3, hε4, hne2'⟩ := hS.chains hnodd hnc C hC
  have hy34 : y₃ ≠ y₄ := by
    intro e; have := hc2.symm.trans hc2'; rw [e] at this
    have h1 : y₃' ∈ ({y₄, y₄} : Finset D) := by rw [this]; simp
    have h2 : y₄' ∈ ({y₄, y₄} : Finset D) := by rw [this]; simp
    simp at h1 h2; exact hy34' (h1.trans h2.symm)
  have hne2 : M.atom (M.mate y₃) ≠ M.atom (M.mate y₄) := by
    have hpair : ({y₃, y₄} : Finset D) = {y₃', y₄'} := hc2.symm.trans hc2'
    have h3m : y₃ ∈ ({y₃', y₄'} : Finset D) := by rw [← hpair]; simp
    have h4m : y₄ ∈ ({y₃', y₄'} : Finset D) := by rw [← hpair]; simp
    simp only [mem_insert, mem_singleton] at h3m h4m
    rcases h3m with rfl | rfl <;> rcases h4m with rfl | rfl
    · exact absurd rfl hy34
    · exact hne2'
    · exact Ne.symm hne2'
    · exact absurd rfl hy34
  have hKA : K₁ ⊆ M.atoms := hK₁.2.1
  have hCA : C ⊆ M.atoms := hC.2.1
  have hdeg2 : ∀ x ∈ M.atoms, ¬ (cls x).IsEps → M.deg x = 2 := by
    intro x hx hn
    have := (hS.classes x hx).mpr hn
    rcases hS.evenDeg hnodd x hx with h | h <;> omega
  have hdK : ∀ x ∈ K₁, M.deg x = 2 := fun x hx => hdeg2 x (hKA hx) (hK₁.2.2.1 x hx)
  have hdC : ∀ x ∈ C, M.deg x = 2 := fun x hx => hdeg2 x (hCA hx) (hC.2.2.1 x hx)
  have hbalK : ∀ x ∈ K₁, M.outdeg x = M.indeg x := fun x hx => by
    have := hS.dir2 x (hKA hx) (hdK x hx); rw [this.1, this.2]
  have hcard : (crossDarts M K₁).card = 2 := by rw [hcross, card_pair hy12]
  have hpost := connected_erase_of_two_cross M hS.conn (fun x hx => by
    rcases hS.evenDeg hnodd x hx with h | h <;> omega) K₁ hcard
  obtain ⟨Ta, hTaY, _⟩ := twoExit_of_chain M hKA hbalK hcross hy12 hne
  have hbA := erase_chain_bonds M Ta (fun x hx => by rw [hTaY] at hx; exact hdK x hx)
  rw [hTaY] at hbA
  set N := Degen.eraseAtoms M K₁ with hN
  -- the chain `C` in `N`
  have hfar : ∀ x, M.atom x ∈ C → M.atom x ∉ K₁ ∧ M.atom (M.mate x) ∉ K₁ := fun x hx =>
    chain_far_from hK₁ hC hCK hx
  have hy3C : M.atom y₃ ∈ C := (mem_crossDarts.mp (by rw [hc2]; simp : y₃ ∈ crossDarts M C)).1
  have hy4C : M.atom y₄ ∈ C := (mem_crossDarts.mp (by rw [hc2]; simp : y₄ ∈ crossDarts M C)).1
  have hcN := chain_erase hc2 (hfar y₃ hy3C) (hfar y₄ hy4C)
  have hCN : C ⊆ N.atoms := fun x hx => mem_sdiff.mpr ⟨hCA hx, disjoint_left.mp hCK hx⟩
  have hdirN : ∀ x ∈ C, N.outdeg x = 1 ∧ N.indeg x = 1 := by
    intro x hx
    have hno : ∀ z, M.atom z = x → M.atom z ∉ K₁ ∧ M.atom (M.mate z) ∉ K₁ := fun z hz => hfar z (hz ▸ hx)
    have e1 := eraseAtoms_dir_card M K₁ hno true
    have e2 := eraseAtoms_dir_card M K₁ hno false
    unfold Molecule.outdeg Molecule.indeg
    rw [e1, e2]
    exact hS.dir2 x (hCA hx) (hdC x hx)
  have hneN : (⟨y₃, hfar y₃ hy3C⟩ : Degen.RetainedDart M K₁) ≠ ⟨y₄, hfar y₄ hy4C⟩ :=
    fun h => hy34 (congrArg Subtype.val h)
  obtain ⟨Tb, hTbY, hTbxy⟩ := twoExit_of_chain N hCN (fun x hx => by rw [(hdirN x hx).1, (hdirN x hx).2]) hcN hneN
    hne2
  have hcapN := caps_eraseAtoms K₁ hS.caps
  have hloopN : ∀ z, N.atom z ≠ N.atom (N.mate z) := fun z => hS.noLoop z.val
  have hdegN : ∀ x ∈ Tb.Y, N.deg x = 2 := by
    intro x hx; rw [hTbY] at hx; have := Mole.outdeg_add_indeg N x; have := hdirN x hx; omega
  have hbB := erase_chain_bonds N Tb hdegN
  have hpb := Tb.post_bonds_eq
  have hMb := bonds_three h1 h2 h3 h12 h1b h2b d1 d2 d3 h4
  have hpatoms : Tb.post.atoms.card + 3 = M.atoms.card := by
    rw [Tb.post_atoms, card_sdiff_of_subset Tb.sub, hTbY]
    have h1' : N.atoms.card + K₁.card = M.atoms.card := by
      rw [hN]; change (M.atoms \ K₁).card + K₁.card = _
      rw [card_sdiff_of_subset hKA]; have := card_le_card hKA; omega
    have := card_le_card hCN
    omega
  have hEp : (Tb.post.bonds.card : ℤ) = 2 * Tb.post.atoms.card - 1 := by
    have hcY : Tb.Y.card = C.card := by rw [hTbY]
    omega
  have hconnP := Tb.post_connected hpost
  have hcapP := Tb.post_caps hcapN
  obtain ⟨z, hz, hz4, hz3⟩ := exists_deg_ne_four Tb.post hcapP hEp
  have hmolP : Tb.post.IsMolecule := isMolecule_of_connected _ hcapP hconnP hz hz4
  -- at most two bonds per pair in the post
  have hdc : N.bondsBetween Tb.d Tb.c ≤ 1 := by
    have hle : N.bondsBetween Tb.d Tb.c ≤ M.bondsBetween Tb.d Tb.c :=
      bondsBetween_eraseAtoms_le M K₁ Tb.far.symm
    refine hle.trans ?_
    rcases hTbxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · change M.bondsBetween (M.atom (M.mate Tb.y.val)) (M.atom (M.mate Tb.x.val)) ≤ 1
      rw [hx, hy, Degen.bondsBetween_comm]; exact hbb
    · change M.bondsBetween (M.atom (M.mate Tb.y.val)) (M.atom (M.mate Tb.x.val)) ≤ 1
      rw [hx, hy]; exact hbb
  have hle2 : ∀ x y, Tb.post.bondsBetween x y ≤ 2 := by
    intro x y
    have hbbP : Tb.post.bondsBetween x y = (Degen.eraseAtoms N Tb.Y).bondsBetween x y +
        (if s(Tb.d, Tb.c) = s(x, y) then 1 else 0) := addBond_bondsBetween _ _ _ _ _
    rw [hbbP]
    have hE2 : (Degen.eraseAtoms N Tb.Y).bondsBetween x y ≤ 2 :=
      bb_erase_le_two N Tb.Y hloopN (bb_erase_le_two M K₁ hS.noLoop hS.noTriple) x y
    split_ifs with he
    · have hE1 : (Degen.eraseAtoms N Tb.Y).bondsBetween x y ≤ 1 := by
        rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]; exact (bondsBetween_eraseAtoms_le N Tb.Y Tb.far.symm).trans hdc
        · rw [← h1, ← h2, Degen.bondsBetween_comm]
          exact (bondsBetween_eraseAtoms_le N Tb.Y Tb.far.symm).trans hdc
      omega
    · omega
  have hszP : (Tb.post.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m :=
    le_trans (by exact_mod_cast (by omega : Tb.post.atoms.card ≤ M.atoms.card)) hsz
  -- operation (d) on `C`
  have hYconn : ∀ x ∈ Tb.Y, ∀ y ∈ Tb.Y, (piece N Tb.Y).SameComponent x y := by
    intro x hx y hy; rw [hTbY] at hx hy ⊢
    exact sameComponent_piece_erase hCK (chain_piece_connected hC x hx y hy)
  have hgood : ∀ S ∈ MoleProp.ladderCells Tb.post, GoodCell Tb.post S :=
    fun S hS' => goodCell_of_connected_low hconnP hz hz3 hS'
  have hεN : ∀ x ∈ N.atoms, x ∉ C → (cls x).IsEps := by
    intro x hx hxC
    by_contra hn
    rcases hall x (mem_sdiff.mp hx).1 hn with h | h
    · exact (mem_sdiff.mp hx).2 h
    · exact hxC h
  have hLGN : ∀ κ', MoleProp.erasedFreeAdmissibility M K₁ (fun κ => Adm κ ∧
      CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) κ' → lgAdmOff N Tb.Y L γ η P' κ' := by
    intro κ' hκ'
    have h1' := projected_largeGapOff M L γ η (0 : Mom d) (nonEps M.atoms cls) K₁ _
      (fun κ hκ => (lgoff_of_finalDec hF P' κ hκ).1) κ' hκ'
    refine ⟨fun x y hxy hxB hdir => ?_, projected_cellGap M L (0 : Mom d) K₁ _ P' (fun κ hκ => hκ.2) κ' hκ'⟩
    have hvN : N.atom x ∈ N.atoms := N.atom_mem x
    have hvB : N.atom x ∉ nonEps M.atoms cls := by
      intro hB
      exact (mem_filter.mp hB).2 (hεN _ hvN (by rw [← hTbY]; exact hxB))
    exact h1' _ hvB x y rfl hxy.symm hdir
  have hRd' := hRd N hcapN hloopN hpost Tb.Y Tb.Y Tb.y Tb.x Tb.sub subset_rfl
    (by rw [hTbY]; omega)
    (fun x hx => by rw [hTbY] at hx; exact hdirN x hx) (by rw [Tb.cross]; exact pair_comm _ _)
    Tb.out_y Tb.out_x Tb.far.symm Tb.d_notMem Tb.c_notMem hYconn hconnP hgood P' (fun S _ => hP _) _ hLGN
  refine hRd'.trans (mul_le_mul' le_rfl ?_)
  refine iSup₂_le fun P'' hP'' => ?_
  have hsd : Tb.Y \ Tb.Y = ∅ := Finset.sdiff_self _
  calc MoleProp.countAFree Tb.post L γ δ C1 (0 : Mom d) (lgAdmOff Tb.post (Tb.Y \ Tb.Y) L γ (η / 2) P'') P''
      ≤ MoleProp.countAFree Tb.post L γ δ C1 (0 : Mom d) (lgAdm Tb.post L γ (η / 2) P'') P'' := by
        refine countAFree_mono_adm _ (fun κ h => ?_)
        rw [hsd] at h; exact lgAdmOff_empty h
    _ = AFree Tb.post d L γ δ (η / 2) C1 P'' := rfl
    _ ≤ _ := h102 Tb.post hmolP hconnP hle2 hEp hszP P'' hP''

end

end WaveTurbulence.GammaLow.FinalCount.Count
