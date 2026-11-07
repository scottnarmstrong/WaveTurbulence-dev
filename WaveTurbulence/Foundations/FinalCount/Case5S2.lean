/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Case5S1
public import WaveTurbulence.Foundations.FinalCount.G8R.ThmA
import Mathlib.Tactic

/-! # Prop 9.6, case (5), two chains: operation (c) on the `α`-chain, operation (d) on the `β`-chain, Prop 10.4(1) -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8.P101

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **Case (5), `α` and `β` in different chains.** -/
theorem s2_key {d : ℕ} {L γ δ η C1 ρ Kd Bd : ℝ} {m : ℕ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (hL1 : 1 ≤ L)
    (hlog : 1 ≤ Real.log L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1) (hρ : 0 < ρ)
    (h104 : P104At.{u, v} d γ δ (η / 2) C1 L m) (hRd : OpDAt.{u, v} d L γ δ η C1 Kd Bd)
    (M : Molecule V D) (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (hS : FinalShape M cls odd) (hF : FinalDec M cls L γ η Adm) (hnodd : ¬ odd) (hnc : ¬ ∀ a ∈ M.atoms, M.deg a = 2)
    (hη : 0 < η) (hP : ∀ S, 0 ≤ P S)
    (hMA : MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm) (hsz : (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m)
    {a₀ b₀ : V} (ha₀ : a₀ ∈ M.atoms) (hb₀ : b₀ ∈ M.atoms) (hab : a₀ ≠ b₀)
    (hdeg2a : M.deg a₀ = 2) (hdeg2b : M.deg b₀ = 2)
    (hdeg4 : ∀ v ∈ M.atoms, v ≠ a₀ → v ≠ b₀ → M.deg v = 4)
    (hEps : ∀ v ∈ M.atoms, v ≠ a₀ → v ≠ b₀ → (cls v).IsEps)
    (hK : IsChainSet M cls {a₀}) (hKb : IsChainSet M cls {b₀})
    (hAdm : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ ({a₀} : Finset V) ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
      ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖)
    (hfr : ∃ w, w ∉ M.atoms)
    (hNB : ∀ v ∈ M.atoms, (cls v).IsEps → ∀ v₂ x₁ x₂, M.IsCutData v v₂ x₁ x₂ → M.IsAlphaCut v v₂ x₁ x₂)
    (hvine : ∀ T : TwoExit (Degen.eraseAtoms M {a₀}), T.Y = {b₀} → ¬ IsVineIIHalfClosure T.post) :
    M.countA L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ρ⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ)) *
        (ENNReal.ofReal (Kd * Real.log L ^ Bd) * ENNReal.ofReal (L ^ (-(4 / 7 * min γ (1 - γ))))) := by
  classical
  have hLp : 0 < L := by linarith
  have hM : M.IsMolecule := hS.isMolecule
  set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
  refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
  -- the first chain `{a₀}`
  obtain ⟨y₁, y₂, hcross, hy12, _, _, hne⟩ := hS.chains hnodd hnc {a₀} hK
  have hKA : ({a₀} : Finset V) ⊆ M.atoms := by simpa using ha₀
  have hch : ∀ b ∈ ({a₀} : Finset V), M.outdeg b = 1 ∧ M.indeg b = 1 := by
    intro b hb; rw [mem_singleton.mp hb]; exact hS.dir2 a₀ ha₀ hdeg2a
  have hcard : (crossDarts M {a₀}).card = 2 := by rw [hcross, card_pair hy12]
  have hpost := connected_erase_of_two_cross M hS.conn (fun a ha => by
    rcases hS.evenDeg hnodd a ha with h | h <;> omega) {a₀} hcard
  have hAdm'' : ∀ κ, (Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) →
      ∃ y y', M.atom y ∈ ({a₀} : Finset V) ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
        ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ := fun κ hκ => hAdm κ hκ.1
  have hstep := opC_rho (L := L) (γ := γ) (δ := δ) (C1 := C1) (ρ := ρ) hγ hL1 hlog hδ hC1 hρ M hS.caps hS.noLoop
    hS.conn {a₀} y₁ y₂ hKA hch hcross hne (chain_piece_connected hK) hpost P' (fun S _ => hP _)
    (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) hAdm''
  refine hstep.trans (mul_le_mul' le_rfl ?_)
  set N := Degen.eraseAtoms M {a₀} with hN
  -- the second chain `{b₀}` inside `N`
  obtain ⟨y₃, y₄, hcross2, hy34, _, _, hne2⟩ := hS.chains hnodd hnc {b₀} hKb
  have hKbA : ({b₀} : Finset V) ⊆ M.atoms := by simpa using hb₀
  have hy3m : y₃ ∈ crossDarts M {b₀} := by rw [hcross2]; exact mem_insert_self _ _
  have hy4m : y₄ ∈ crossDarts M {b₀} := by rw [hcross2]; exact mem_insert_of_mem (mem_singleton_self _)
  have hat3 : M.atom y₃ = b₀ := mem_singleton.mp (mem_crossDarts.mp hy3m).1
  have hat4 : M.atom y₄ = b₀ := mem_singleton.mp (mem_crossDarts.mp hy4m).1
  have hmateE : ∀ z, M.atom z = b₀ → M.atom (M.mate z) ≠ a₀ := by
    intro z hz hza
    have hz' : M.Adj b₀ a₀ := ⟨z, hz, hza⟩
    have : b₀ ∈ ({a₀} : Finset V) := hK.2.2.2.1 a₀ (mem_singleton_self _) b₀ (by
      obtain ⟨w, hw1, hw2⟩ := hz'; exact ⟨M.mate w, hw2, by rw [M.mate_mate]; exact hw1⟩)
      (hKb.2.2.1 b₀ (mem_singleton_self _))
    exact hab.symm (mem_singleton.mp this)
  have p₃ : M.atom y₃ ∉ ({a₀} : Finset V) ∧ M.atom (M.mate y₃) ∉ ({a₀} : Finset V) :=
    ⟨by rw [hat3]; simpa using hab.symm, by simpa using hmateE y₃ hat3⟩
  have p₄ : M.atom y₄ ∉ ({a₀} : Finset V) ∧ M.atom (M.mate y₄) ∉ ({a₀} : Finset V) :=
    ⟨by rw [hat4]; simpa using hab.symm, by simpa using hmateE y₄ hat4⟩
  obtain ⟨hcK, hdir⟩ := chain_after_erase hS.noLoop hcross2 p₃ p₄
  have hbN : b₀ ∈ N.atoms := mem_sdiff.mpr ⟨hb₀, by simpa using hab.symm⟩
  have hdbN : N.outdeg b₀ = 1 ∧ N.indeg b₀ = 1 := by
    have h := hS.dir2 b₀ hb₀ hdeg2b
    unfold Molecule.outdeg Molecule.indeg; rw [hdir true, hdir false]; exact h
  have hcapN := caps_eraseAtoms {a₀} hS.caps
  have hconnN := hpost
  have hneN : (⟨y₃, p₃⟩ : Degen.RetainedDart M {a₀}) ≠ ⟨y₄, p₄⟩ := fun h => hy34 (congrArg Subtype.val h)
  obtain ⟨Tb, hTbY, _⟩ := twoExit_of_chain N (K := {b₀}) (y₁ := ⟨y₃, p₃⟩) (y₂ := ⟨y₄, p₄⟩)
    (by simpa using hbN) (fun w hw => by rw [mem_singleton.mp hw]; rw [hdbN.1, hdbN.2]) hcK hneN hne2
  have hloopN : ∀ z, N.atom z ≠ N.atom (N.mate z) := fun z => hS.noLoop z.val
  -- bond counts
  have hdegN : ∀ v ∈ Tb.Y, N.deg v = 2 := by
    intro v hv; rw [hTbY] at hv; rw [mem_singleton.mp hv]
    have := Mole.outdeg_add_indeg N b₀; omega
  obtain ⟨Ta, hTaY, _⟩ := twoExit_of_chain M hKA (fun v hv => by rw [(hch v hv).1, (hch v hv).2]) hcross hy12 hne
  have hbA := erase_chain_bonds M Ta (fun v hv => by rw [hTaY] at hv; rw [mem_singleton.mp hv]; exact hdeg2a)
  rw [hTaY, ← hN] at hbA
  have hbB := erase_chain_bonds N Tb hdegN
  have hpb := Tb.post_bonds_eq
  have hMb := c5_two_bonds ha₀ hb₀ hab hdeg2a hdeg2b hdeg4
  have hpatoms : Tb.post.atoms.card + 2 = M.atoms.card := by
    rw [Tb.post_atoms, card_sdiff_of_subset Tb.sub, hTbY]
    have h1 : N.atoms.card + 1 = M.atoms.card := by
      rw [hN]; change (M.atoms \ {a₀}).card + 1 = _
      rw [card_sdiff_of_subset hKA]; have := card_pos.mpr ⟨a₀, ha₀⟩; simp; omega
    simp; omega
  have hEp : (Tb.post.bonds.card : ℤ) = 2 * Tb.post.atoms.card - 1 := by
    have hcY : Tb.Y.card = 1 := by rw [hTbY]; simp
    rw [hcY] at hbB; rw [card_singleton] at hbA; omega
  have hconnP := Tb.post_connected hconnN
  have hcapP := Tb.post_caps hcapN
  obtain ⟨z, hz, hz4, hz3⟩ := exists_deg_ne_four Tb.post hcapP hEp
  have hmolP : Tb.post.IsMolecule := isMolecule_of_connected _ hcapP hconnP hz hz4
  have hleN : ∀ p q, N.bondsBetween p q ≤ 2 := bb_erase_le_two M {a₀} hS.noLoop hS.noTriple
  have hleE : ∀ p q, (Degen.eraseAtoms N Tb.Y).bondsBetween p q ≤ 2 := bb_erase_le_two N Tb.Y hloopN hleN
  have hbbP : ∀ p q, Tb.post.bondsBetween p q = (Degen.eraseAtoms N Tb.Y).bondsBetween p q +
      (if s(Tb.d, Tb.c) = s(p, q) then 1 else 0) := fun p q => addBond_bondsBetween _ _ _ _ _
  have hle3 : ∀ p q, Tb.post.bondsBetween p q ≤ 3 := by
    intro p q; rw [hbbP]; have := hleE p q; split_ifs <;> omega
  have htri : ∀ p q r s, 3 ≤ Tb.post.bondsBetween p q → 3 ≤ Tb.post.bondsBetween r s → s(p, q) = s(r, s) := by
    intro p q r s h1 h2
    rw [hbbP] at h1 h2
    have e1 : s(Tb.d, Tb.c) = s(p, q) := by
      by_contra hn; rw [if_neg hn] at h1; have := hleE p q; omega
    have e2 : s(Tb.d, Tb.c) = s(r, s) := by
      by_contra hn; rw [if_neg hn] at h2; have := hleE r s; omega
    rw [← e1, ← e2]
  have hfreshP : ∃ w, w ∉ Tb.post.atoms := by
    refine ⟨a₀, fun h => ?_⟩
    rw [Tb.post_atoms] at h
    exact (mem_sdiff.mp (mem_sdiff.mp h).1).2 (mem_singleton_self _)
  have hszP : (Tb.post.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m :=
    le_trans (by exact_mod_cast (by omega : Tb.post.atoms.card ≤ M.atoms.card)) hsz
  -- operation (d) on `Tb.Y = {b₀}`
  have hYconn : ∀ a ∈ Tb.Y, ∀ b ∈ Tb.Y, (piece N Tb.Y).SameComponent a b := by
    intro a ha b hb
    rw [hTbY] at ha hb; rw [mem_singleton.mp ha, mem_singleton.mp hb]; exact Relation.EqvGen.refl _
  have hbad : ¬ HasBadBetaCut Tb.post := by
    refine not_bad_post M {a₀} hS.conn Tb hconnP hfr (fun u hu => ?_) (fun u hu => ?_) (fun v hv => ?_)
    · have hu' := mem_sdiff.mp (by rw [Tb.post_atoms] at hu; exact hu)
      have hua := hu'.1; have hub := hu'.2
      exact hdeg4 u (mem_sdiff.mp hua).1 (fun h => (mem_sdiff.mp hua).2 (by simp [h]))
        (fun h => hub (by rw [hTbY]; simp [h]))
    · have := hdegN u hu
      rw [this]
      rw [hTbY] at hu; rw [mem_singleton.mp hu]; exact hdeg2b.symm
    · have hv' := mem_sdiff.mp (by rw [Tb.post_atoms] at hv; exact hv)
      have hva := mem_sdiff.mp hv'.1
      exact hNB v hva.1 (hEps v hva.1 (fun h => hva.2 (by simp [h])) (fun h => hv'.2 (by rw [hTbY]; simp [h])))
  have hgood : ∀ S ∈ MoleProp.ladderCells Tb.post, GoodCell Tb.post S :=
    fun S hS => goodCell_of_connected_low hconnP hz hz3 hS
  have hLGN : ∀ κ', erasedFreeAdmissibility M {a₀}
      (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) κ' →
      lgAdmOff N Tb.Y L γ η P' κ' := by
    intro κ' hκ'
    have hLG : ∀ κ, (Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) →
        LargeGapOff (nonEps M.atoms cls) M L γ η (0 : Mom d) κ := by
      intro κ hκ v hvB x y hx hy hxy
      have hv : v ∈ M.atoms := hx ▸ M.atom_mem x
      have hε : (cls v).IsEps := by
        by_contra hne'; exact hvB (mem_filter.mpr ⟨hv, hne'⟩)
      exact (hF.epsLG κ hκ.1 v hv hε x y hx hy hxy).le
    have h1 := projected_largeGapOff M L γ η (0 : Mom d) (nonEps M.atoms cls) {a₀} _ hLG κ' hκ'
    refine ⟨fun x y hxy hxB hdir => ?_, projected_cellGap M L (0 : Mom d) {a₀} _ P' (fun κ hκ => hκ.2) κ' hκ'⟩
    have hvN : N.atom x ∈ M.atoms \ {a₀} := N.atom_mem x
    have hvB : N.atom x ∉ nonEps M.atoms cls := by
      intro hB
      have := (mem_filter.mp hB).2
      have hne1 : N.atom x ≠ a₀ := fun h => (mem_sdiff.mp hvN).2 (by simp [h])
      have hne2' : N.atom x ≠ b₀ := fun h => hxB (by rw [hTbY, h]; simp)
      exact this (hEps _ (mem_sdiff.mp hvN).1 hne1 hne2')
    exact h1 _ hvB x y rfl hxy.symm hdir
  have hRd' := hRd N hcapN hloopN hconnN Tb.Y Tb.Y Tb.y Tb.x Tb.sub subset_rfl (by rw [hTbY]; simp)
    (fun b hb => by rw [hTbY] at hb; rw [mem_singleton.mp hb]; exact hdbN) (by rw [Tb.cross]; exact pair_comm _ _)
    Tb.out_y Tb.out_x Tb.far.symm Tb.d_notMem Tb.c_notMem hYconn hconnP hgood P' (fun S _ => hP _) _ hLGN
  refine hRd'.trans (mul_le_mul' le_rfl ?_)
  refine iSup₂_le fun P'' hP'' => ?_
  have hsd : Tb.Y \ Tb.Y = ∅ := Finset.sdiff_self _
  calc MoleProp.countAFree Tb.post L γ δ C1 (0 : Mom d) (lgAdmOff Tb.post (Tb.Y \ Tb.Y) L γ (η / 2) P'') P''
      ≤ MoleProp.countAFree Tb.post L γ δ C1 (0 : Mom d) (lgAdm Tb.post L γ (η / 2) P'') P'' := by
        refine countAFree_mono_adm _ (fun κ h => ?_)
        rw [hsd] at h; exact lgAdmOff_empty h
    _ = AFree Tb.post d L γ δ (η / 2) C1 P'' := rfl
    _ ≤ _ := h104 Tb.post hmolP hconnP htri hle3 hEp hszP hbad hfreshP (hvine Tb hTbY) P'' hP''

end
end WaveTurbulence.FinalCountG8
