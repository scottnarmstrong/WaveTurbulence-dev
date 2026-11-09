/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6b
public import WaveTurbulence.Foundations.FinalCount.Split2Iso
public import WaveTurbulence.Foundations.FinalCount.G8R.Step0Post
public import WaveTurbulence.Foundations.FinalCount.G8R.Step0Y1c3
import Mathlib.Tactic

/-! # Case (6b) with two operations (d) (packet L6-COUNT, Case6TopLow; M2 §4.10 (6b))

`c6b2_bound`: after operation (c) on `K₁ = {v₁}`, the other non-`ε` atoms form two singleton chains `{v₂}`, `{β}`
with far-end pairs `{e₁, e₂}`, `{e₃, e₄}`. When neither pair is doubly bonded and the closure has no triple bond
(the pairs differ, or coincide with no bond between them), operation (d) on `{v₂}` (at `η`, protected set `{v₂, β}`),
operation (d) on `{β}` (at `η/2`), and Prop 10.2(1) at `η/4` on the closure (`E = 2V − 1`, at most double bonds)
give `𝔄 ≲ (log L)^{B} L^{−3γ₀/5}` (main's `OpDAt`, `Prop102At`). Helper: `exit_far_eps` (far ends of a chain are
`ε`-atoms), `bb_eq_of_sym2`. -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8 WaveTurbulence.FinalCountG8.P101

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The far end of an exit of a chain is an `ε`-atom. -/
theorem exit_far_eps {M : Molecule V D} {cls : V → Cls} {C : Finset V} (hC : IsChainSet M cls C) {z : D}
    (hz : z ∈ crossDarts M C) : (cls (M.atom (M.mate z))).IsEps := by
  by_contra hn
  obtain ⟨hz1, hz2⟩ := mem_crossDarts.mp hz
  exact hz2 (hC.2.2.2.1 _ hz1 _ ⟨z, rfl, rfl⟩ hn)

theorem bb_eq_of_sym2 {W E : Type*} [DecidableEq W] [Fintype E] [DecidableEq E] (M : Molecule W E) {a b x y : W}
    (h : s(a, b) = s(x, y)) : M.bondsBetween a b = M.bondsBetween x y := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Degen.bondsBetween_comm M _ _

/-- The bonds of a post, bounded by those of the original molecule plus the added bond. -/
theorem post_bb_le {W E : Type*} [DecidableEq W] [Fintype E] [DecidableEq E] {N : Molecule W E} (T : TwoExit N)
    {x y : W} (hxy : x ≠ y) :
    T.post.bondsBetween x y ≤ N.bondsBetween x y + (if s(T.d, T.c) = s(x, y) then 1 else 0) := by
  have h : T.post.bondsBetween x y = (Degen.eraseAtoms N T.Y).bondsBetween x y +
      (if s(T.d, T.c) = s(x, y) then 1 else 0) := addBond_bondsBetween _ _ _ _ _
  rw [h]
  have := bondsBetween_eraseAtoms_le N T.Y hxy
  omega

/-- The degrees of an atom away from the removed set and the added bond do not change in a post. -/
theorem post_dir_card {W E : Type*} [DecidableEq W] [Fintype E] [DecidableEq E] {N : Molecule W E} (T : TwoExit N)
    {w : W} (hno : ∀ z, N.atom z = w → N.atom z ∉ T.Y ∧ N.atom (N.mate z) ∉ T.Y) (hd : T.d ≠ w) (hc : T.c ≠ w) :
    T.post.outdeg w = N.outdeg w ∧ T.post.indeg w = N.indeg w := by
  have h1 := addBond_outdeg (Degen.eraseAtoms N T.Y) T.d T.c w
  have h2 := addBond_indeg' (Degen.eraseAtoms N T.Y) T.d T.c w
  rw [if_neg hd] at h1
  rw [if_neg hc] at h2
  have e1 := eraseAtoms_dir_card N T.Y hno true
  have e2 := eraseAtoms_dir_card N T.Y hno false
  constructor
  · change (Mole.addBond (Degen.eraseAtoms N T.Y) T.d T.c).outdeg w = _
    rw [h1]; unfold Molecule.outdeg; rw [e1]; simp
  · change (Mole.addBond (Degen.eraseAtoms N T.Y) T.d T.c).indeg w = _
    rw [h2]; unfold Molecule.indeg; rw [e2]; simp

end

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **(6b) with two singleton chains**: operations (d) on `{v₂}` and `{β}`, then Prop 10.2(1) at `η/4`. -/
theorem c6b2_bound {d m : ℕ} {L γ δ η C1 Kd Bd Kd' Bd' : ℝ} (hL1 : 1 ≤ L)
    (h102 : Prop102At.{u, v} d L γ δ (η / 2 / 2) C1 m)
    (hRd : OpDAt.{u, v} d L γ δ η C1 Kd Bd) (hRd' : OpDAt.{u, v} d L γ δ (η / 2) C1 Kd' Bd')
    {M : Molecule V D} {cls : V → Cls} {odd : Prop} {Adm : (D → (Fin d → ℤ)) → Prop} {P : Finset V → ℝ}
    (hS : FinalShape M cls odd) (hF : FinalDec M cls L γ η Adm) (hnodd : ¬ odd)
    (hnc : ¬ ∀ a ∈ M.atoms, M.deg a = 2) (hP : ∀ S, 0 ≤ P S) (hsz : (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m)
    {v₁ v₂ b : V} (h1 : v₁ ∈ M.atoms) (h2 : v₂ ∈ M.atoms) (h3 : b ∈ M.atoms) (h12 : v₁ ≠ v₂) (h1b : v₁ ≠ b)
    (h2b : v₂ ≠ b) (d1 : M.deg v₁ = 2) (d2 : M.deg v₂ = 2) (d3 : M.deg b = 2)
    (h4 : ∀ v ∈ M.atoms, v ≠ v₁ → v ≠ v₂ → v ≠ b → M.deg v = 4)
    {K₁ : Finset V} (hK₁ : IsChainSet M cls K₁) (hK₁c : K₁.card = 1) (h2K : v₂ ∉ K₁) (hbK : b ∉ K₁)
    (hall : ∀ v ∈ M.atoms, ¬ (cls v).IsEps → v ∈ K₁ ∨ v = v₂ ∨ v = b)
    (hc2 : IsChainSet M cls {v₂}) (hcb : IsChainSet M cls {b})
    {y₁ y₂ y₃ y₄ : D} (hx2 : crossDarts M {v₂} = {y₁, y₂}) (hy12 : y₁ ≠ y₂)
    (hne12 : M.atom (M.mate y₁) ≠ M.atom (M.mate y₂))
    (hxb : crossDarts M {b} = {y₃, y₄}) (hy34 : y₃ ≠ y₄) (hne34 : M.atom (M.mate y₃) ≠ M.atom (M.mate y₄))
    (hbb2 : M.bondsBetween (M.atom (M.mate y₁)) (M.atom (M.mate y₂)) ≤ 1)
    (hbbb : M.bondsBetween (M.atom (M.mate y₃)) (M.atom (M.mate y₄)) ≤ 1)
    (hsame : s(M.atom (M.mate y₁), M.atom (M.mate y₂)) = s(M.atom (M.mate y₃), M.atom (M.mate y₄)) →
      M.bondsBetween (M.atom (M.mate y₁)) (M.atom (M.mate y₂)) = 0) :
    MoleProp.countAFree (Degen.eraseAtoms M K₁) L γ δ C1 (0 : Mom d)
        (MoleProp.erasedFreeAdmissibility M K₁ (fun κ => Adm κ ∧
          CellGapRestriction M L (0 : Mom d) (fun S => P (Mole.appbLinkParent M S)) (GapScale L) κ))
        (fun S => P (Mole.appbLinkParent M S)) ≤
      ENNReal.ofReal (Kd * Real.log L ^ Bd) *
        (ENNReal.ofReal (Kd' * Real.log L ^ Bd') * ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ))))) := by
  classical
  set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
  obtain ⟨z₁, z₂, hcross, hz12, _, _, hnez⟩ := hS.chains hnodd hnc K₁ hK₁
  have hKA : K₁ ⊆ M.atoms := hK₁.2.1
  have hdeg2 : ∀ x ∈ M.atoms, ¬ (cls x).IsEps → M.deg x = 2 := by
    intro x hx hn
    have := (hS.classes x hx).mpr hn
    rcases hS.evenDeg hnodd x hx with h | h <;> omega
  have hdK : ∀ x ∈ K₁, M.deg x = 2 := fun x hx => hdeg2 x (hKA hx) (hK₁.2.2.1 x hx)
  have hbalK : ∀ x ∈ K₁, M.outdeg x = M.indeg x := fun x hx => by
    have := hS.dir2 x (hKA hx) (hdK x hx); rw [this.1, this.2]
  have hcardK : (crossDarts M K₁).card = 2 := by rw [hcross, card_pair hz12]
  have hpost := connected_erase_of_two_cross M hS.conn (fun x hx => by
    rcases hS.evenDeg hnodd x hx with h | h <;> omega) K₁ hcardK
  obtain ⟨T₁, hT₁Y, _⟩ := twoExit_of_chain M hKA hbalK hcross hz12 hnez
  have hbA := erase_chain_bonds M T₁ (fun x hx => by rw [hT₁Y] at hx; exact hdK x hx)
  rw [hT₁Y] at hbA
  set N := Degen.eraseAtoms M K₁ with hN
  have hcapN := caps_eraseAtoms K₁ hS.caps
  have hloopN : ∀ z, N.atom z ≠ N.atom (N.mate z) := fun z => hS.noLoop z.val
  have hn2 : ¬ (cls v₂).IsEps := hc2.2.2.1 v₂ (mem_singleton_self _)
  have hnb : ¬ (cls b).IsEps := hcb.2.2.1 b (mem_singleton_self _)
  -- the two chains in `N`
  have hfar2 : ∀ x, M.atom x ∈ ({v₂} : Finset V) → M.atom x ∉ K₁ ∧ M.atom (M.mate x) ∉ K₁ := fun x hx =>
    chain_far_from hK₁ hc2 (disjoint_singleton_left.mpr h2K) hx
  have hfarb : ∀ x, M.atom x ∈ ({b} : Finset V) → M.atom x ∉ K₁ ∧ M.atom (M.mate x) ∉ K₁ := fun x hx =>
    chain_far_from hK₁ hcb (disjoint_singleton_left.mpr hbK) hx
  have hy1m : y₁ ∈ crossDarts M {v₂} := by rw [hx2]; simp
  have hy2m : y₂ ∈ crossDarts M {v₂} := by rw [hx2]; simp
  have hy3m : y₃ ∈ crossDarts M {b} := by rw [hxb]; simp
  have hy4m : y₄ ∈ crossDarts M {b} := by rw [hxb]; simp
  have hε1 := exit_far_eps hc2 hy1m
  have hε2 := exit_far_eps hc2 hy2m
  have hε3 := exit_far_eps hcb hy3m
  have hε4 := exit_far_eps hcb hy4m
  have hat1 : M.atom y₁ = v₂ := mem_singleton.mp (mem_crossDarts.mp hy1m).1
  have hat2 : M.atom y₂ = v₂ := mem_singleton.mp (mem_crossDarts.mp hy2m).1
  have hat3 : M.atom y₃ = b := mem_singleton.mp (mem_crossDarts.mp hy3m).1
  have hat4 : M.atom y₄ = b := mem_singleton.mp (mem_crossDarts.mp hy4m).1
  have p₁ := hfar2 y₁ (by rw [hat1]; exact mem_singleton_self _)
  have p₂ := hfar2 y₂ (by rw [hat2]; exact mem_singleton_self _)
  have p₃ := hfarb y₃ (by rw [hat3]; exact mem_singleton_self _)
  have p₄ := hfarb y₄ (by rw [hat4]; exact mem_singleton_self _)
  have hcN2 : crossDarts N {v₂} = {⟨y₁, p₁⟩, ⟨y₂, p₂⟩} := chain_erase hx2 p₁ p₂
  have hcNb : crossDarts N {b} = {⟨y₃, p₃⟩, ⟨y₄, p₄⟩} := chain_erase hxb p₃ p₄
  have hdirN : ∀ x, (x = v₂ ∨ x = b) → N.outdeg x = 1 ∧ N.indeg x = 1 := by
    intro x hx
    have hno : ∀ z, M.atom z = x → M.atom z ∉ K₁ ∧ M.atom (M.mate z) ∉ K₁ := fun z hz => by
      rcases hx with rfl | rfl
      · exact hfar2 z (by rw [hz]; exact mem_singleton_self _)
      · exact hfarb z (by rw [hz]; exact mem_singleton_self _)
    have e1 := eraseAtoms_dir_card M K₁ hno true
    have e2 := eraseAtoms_dir_card M K₁ hno false
    have hxA : x ∈ M.atoms := by rcases hx with rfl | rfl <;> assumption
    have hd2 : M.deg x = 2 := by rcases hx with rfl | rfl <;> assumption
    unfold Molecule.outdeg Molecule.indeg
    rw [e1, e2]
    exact hS.dir2 x hxA hd2
  have hv₂N : v₂ ∈ N.atoms := mem_sdiff.mpr ⟨h2, h2K⟩
  have hbN : b ∈ N.atoms := mem_sdiff.mpr ⟨h3, hbK⟩
  have hne12N : (⟨y₁, p₁⟩ : Degen.RetainedDart M K₁) ≠ ⟨y₂, p₂⟩ := fun h => hy12 (congrArg Subtype.val h)
  obtain ⟨Ta, hTaY, hTaxy⟩ := twoExit_of_chain N (K := {v₂}) (by simpa using hv₂N)
    (fun x hx => by rw [mem_singleton.mp hx, (hdirN v₂ (Or.inl rfl)).1, (hdirN v₂ (Or.inl rfl)).2]) hcN2 hne12N
    hne12
  -- the far ends of `Ta`
  have hTaε : ∀ z ∈ crossDarts N Ta.Y, (cls (N.atom (N.mate z))).IsEps := by
    intro z hz
    rw [hTaY, hcN2] at hz
    rcases mem_insert.mp hz with rfl | e
    · exact hε1
    · rw [mem_singleton.mp e]; exact hε2
  have hTadε : (cls Ta.d).IsEps := hTaε Ta.y Ta.y_mem
  have hTacε : (cls Ta.c).IsEps := hTaε Ta.x Ta.x_mem
  have hsymA : s(Ta.d, Ta.c) = s(M.atom (M.mate y₁), M.atom (M.mate y₂)) := by
    unfold TwoExit.d TwoExit.c
    rcases hTaxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hx, hy]; exact Sym2.eq_swap
    · rw [hx, hy]; rfl
  -- bonds and atoms
  have hdegN2 : ∀ x ∈ Ta.Y, N.deg x = 2 := by
    intro x hx; rw [hTaY] at hx; rw [mem_singleton.mp hx]
    have := Mole.outdeg_add_indeg N v₂; have := hdirN v₂ (Or.inl rfl); omega
  have hbBa := erase_chain_bonds N Ta hdegN2
  have hpba := Ta.post_bonds_eq
  have hMb := bonds_three h1 h2 h3 h12 h1b h2b d1 d2 d3 h4
  have hcY : Ta.Y.card = 1 := by rw [hTaY, card_singleton]
  have hNat : N.atoms.card + 1 = M.atoms.card := by
    rw [hN]; change (M.atoms \ K₁).card + 1 = _
    rw [card_sdiff_of_subset hKA, hK₁c]; have := card_le_card hKA; omega
  have hAat : Ta.post.atoms.card + 2 = M.atoms.card := by
    rw [Ta.post_atoms, card_sdiff_of_subset Ta.sub, hcY]
    have : 1 ≤ N.atoms.card := card_pos.mpr ⟨v₂, hv₂N⟩
    omega
  have hEA : (Ta.post.bonds.card : ℤ) = 2 * Ta.post.atoms.card - 2 := by omega
  have hconnA := Ta.post_connected hpost
  have hcapA := Ta.post_caps hcapN
  have hloopA := Ta.post_loop hloopN
  obtain ⟨za, hza, hza4⟩ := exists_deg_ne_four' Ta.post hEA
  have hza3 : Ta.post.deg za ≤ 3 := by
    have := hcapA za hza; have := Mole.outdeg_add_indeg Ta.post za; omega
  have hgoodA : ∀ S ∈ MoleProp.ladderCells Ta.post, GoodCell Ta.post S :=
    fun S hS' => goodCell_of_connected_low hconnA hza hza3 hS'
  -- operation (d) on `{v₂}` with protected set `{v₂, b}`
  have hεN : ∀ x ∈ N.atoms, x ≠ v₂ → x ≠ b → (cls x).IsEps := by
    intro x hx hx2 hxb
    by_contra hn
    rcases hall x (mem_sdiff.mp hx).1 hn with h | h | h
    · exact (mem_sdiff.mp hx).2 h
    · exact hx2 h
    · exact hxb h
  have hLGN : ∀ κ', MoleProp.erasedFreeAdmissibility M K₁ (fun κ => Adm κ ∧
      CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) κ' → lgAdmOff N {v₂, b} L γ η P' κ' := by
    intro κ' hκ'
    have h1' := projected_largeGapOff M L γ η (0 : Mom d) (nonEps M.atoms cls) K₁ _
      (fun κ hκ => (lgoff_of_finalDec hF P' κ hκ).1) κ' hκ'
    refine ⟨fun x y hxy hxB hdir => ?_, projected_cellGap M L (0 : Mom d) K₁ _ P' (fun κ hκ => hκ.2) κ' hκ'⟩
    have hvN : N.atom x ∈ N.atoms := N.atom_mem x
    have hvB : N.atom x ∉ nonEps M.atoms cls := by
      intro hB
      simp only [mem_insert, mem_singleton, not_or] at hxB
      exact (mem_filter.mp hB).2 (hεN _ hvN hxB.1 hxB.2)
    exact h1' _ hvB x y rfl hxy.symm hdir
  have hY2 : ∀ a ∈ Ta.Y, ∀ c ∈ Ta.Y, (piece N Ta.Y).SameComponent a c := by
    intro a ha c hc; rw [hTaY] at ha hc; rw [mem_singleton.mp ha, mem_singleton.mp hc]
    exact Relation.EqvGen.refl _
  have hnotB : ∀ w, (cls w).IsEps → w ∉ ({v₂, b} : Finset V) := by
    intro w hw hB
    simp only [mem_insert, mem_singleton] at hB
    rcases hB with rfl | rfl
    · exact hn2 hw
    · exact hnb hw
  have hA1 := hRd N hcapN hloopN hpost Ta.Y {v₂, b} Ta.y Ta.x Ta.sub
    (by rw [hTaY]; intro x hx; rw [mem_singleton.mp hx]; simp) (by rw [hcY]; norm_num)
    (fun x hx => by rw [hTaY] at hx; rw [mem_singleton.mp hx]; exact hdirN v₂ (Or.inl rfl))
    (by rw [Ta.cross]; exact pair_comm _ _) Ta.out_y Ta.out_x Ta.far.symm (hnotB _ hTadε) (hnotB _ hTacε) hY2
    hconnA hgoodA P' (fun S _ => hP _) _ hLGN
  refine hA1.trans (mul_le_mul' le_rfl ?_)
  unfold AFreeSupAdm
  refine iSup₂_le fun P'' hP'' => ?_
  change MoleProp.countAFree Ta.post L γ δ C1 (0 : Mom d)
    (lgAdmOff Ta.post (({v₂, b} : Finset V) \ Ta.Y) L γ (η / 2) P'') P'' ≤ _
  -- the chain `{b}` in the post
  have hbY : b ∉ Ta.Y := by rw [hTaY]; simpa using h2b.symm
  have hbd : Ta.d ≠ b := fun e => hnb (e ▸ hTadε)
  have hbc : Ta.c ≠ b := fun e => hnb (e ▸ hTacε)
  have q₃ : N.atom ⟨y₃, p₃⟩ ∉ Ta.Y ∧ N.atom (N.mate ⟨y₃, p₃⟩) ∉ Ta.Y := by
    refine ⟨by change M.atom y₃ ∉ Ta.Y; rw [hat3]; exact hbY, fun h => ?_⟩
    rw [hTaY] at h
    exact hn2 ((mem_singleton.mp h) ▸ hε3)
  have q₄ : N.atom ⟨y₄, p₄⟩ ∉ Ta.Y ∧ N.atom (N.mate ⟨y₄, p₄⟩) ∉ Ta.Y := by
    refine ⟨by change M.atom y₄ ∉ Ta.Y; rw [hat4]; exact hbY, fun h => ?_⟩
    rw [hTaY] at h
    exact hn2 ((mem_singleton.mp h) ▸ hε4)
  have hcE := chain_erase hcNb q₃ q₄
  have hcP : crossDarts Ta.post {b} = {Sum.inl ⟨⟨y₃, p₃⟩, q₃⟩, Sum.inl ⟨⟨y₄, p₄⟩, q₄⟩} := by
    change crossDarts (Mole.addBond (Degen.eraseAtoms N Ta.Y) Ta.d Ta.c) {b} = _
    exact crossDarts_addBond_inl _ (by simpa using hbd) (by simpa using hbc) hcE
  have hbP : b ∈ Ta.post.atoms := by rw [Ta.post_atoms]; exact mem_sdiff.mpr ⟨hbN, hbY⟩
  have hdirP : Ta.post.outdeg b = 1 ∧ Ta.post.indeg b = 1 := by
    have hno : ∀ z, N.atom z = b → N.atom z ∉ Ta.Y ∧ N.atom (N.mate z) ∉ Ta.Y := by
      intro z hz
      refine ⟨by rw [hz]; exact hbY, fun h => ?_⟩
      rw [hTaY] at h
      have hv := mem_singleton.mp h
      -- a bond `b – v₂` would put `v₂` in the chain `{b}`
      have : v₂ ∈ ({b} : Finset V) := hcb.2.2.2.1 b (mem_singleton_self _) v₂
        ⟨z.val, hz, hv⟩ hn2
      exact h2b (mem_singleton.mp this)
    have := post_dir_card Ta hno hbd hbc
    rw [this.1, this.2]; exact hdirN b (Or.inr rfl)
  have hneP : (Sum.inl ⟨⟨y₃, p₃⟩, q₃⟩ : Degen.RetainedDart N Ta.Y ⊕ Bool) ≠ Sum.inl ⟨⟨y₄, p₄⟩, q₄⟩ :=
    fun h => hy34 (congrArg (fun w => w.val.val) (Sum.inl.inj h))
  obtain ⟨Tb, hTbY, hTbxy⟩ := twoExit_of_chain Ta.post (K := {b}) (by simpa using hbP)
    (fun x hx => by rw [mem_singleton.mp hx, hdirP.1, hdirP.2]) hcP hneP hne34
  have hTbε : ∀ z ∈ crossDarts Ta.post Tb.Y, (cls (Ta.post.atom (Ta.post.mate z))).IsEps := by
    intro z hz
    rw [hTbY, hcP] at hz
    rcases mem_insert.mp hz with rfl | e
    · exact hε3
    · rw [mem_singleton.mp e]; exact hε4
  have hTbdε : (cls Tb.d).IsEps := hTbε Tb.y Tb.y_mem
  have hTbcε : (cls Tb.c).IsEps := hTbε Tb.x Tb.x_mem
  have hsymB : s(Tb.d, Tb.c) = s(M.atom (M.mate y₃), M.atom (M.mate y₄)) := by
    unfold TwoExit.d TwoExit.c
    rcases hTbxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hx, hy]; exact Sym2.eq_swap
    · rw [hx, hy]; rfl
  -- the closure
  have hdegP : ∀ x ∈ Tb.Y, Ta.post.deg x = 2 := by
    intro x hx; rw [hTbY] at hx; rw [mem_singleton.mp hx]
    have := Mole.outdeg_add_indeg Ta.post b; omega
  have hbBb := erase_chain_bonds Ta.post Tb hdegP
  have hpbb := Tb.post_bonds_eq
  have hcYb : Tb.Y.card = 1 := by rw [hTbY, card_singleton]
  have hBat : Tb.post.atoms.card + 1 = Ta.post.atoms.card := by
    rw [Tb.post_atoms, card_sdiff_of_subset Tb.sub, hcYb]
    have : 1 ≤ Ta.post.atoms.card := card_pos.mpr ⟨b, hbP⟩
    omega
  have hEB : (Tb.post.bonds.card : ℤ) = 2 * Tb.post.atoms.card - 1 := by omega
  have hconnB := Tb.post_connected hconnA
  have hcapB := Tb.post_caps hcapA
  obtain ⟨zb, hzb, hzb4, hzb3⟩ := exists_deg_ne_four Tb.post hcapB hEB
  have hmolB : Tb.post.IsMolecule := isMolecule_of_connected _ hcapB hconnB hzb hzb4
  have hgoodB : ∀ S ∈ MoleProp.ladderCells Tb.post, GoodCell Tb.post S :=
    fun S hS' => goodCell_of_connected_low hconnB hzb hzb3 hS'
  have hszB : (Tb.post.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m :=
    le_trans (by exact_mod_cast (by omega : Tb.post.atoms.card ≤ M.atoms.card)) hsz
  -- at most double bonds in the closure
  have hNM : ∀ x y, x ≠ y → N.bondsBetween x y ≤ M.bondsBetween x y := fun x y hxy =>
    bondsBetween_eraseAtoms_le M K₁ hxy
  have hle2 : ∀ x y, Tb.post.bondsBetween x y ≤ 2 := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      have h0 : Tb.post.bondsBetween x x = 0 := bondsBetween_self_eq_zero (Tb.post_loop hloopA) x
      omega
    have hB := post_bb_le Tb hxy
    have hA := post_bb_le Ta hxy
    have hM := hNM x y hxy
    have hT := hS.noTriple x y
    by_cases hb' : s(Tb.d, Tb.c) = s(x, y) <;> by_cases ha' : s(Ta.d, Ta.c) = s(x, y)
    · -- both added bonds join `x, y`
      rw [if_pos hb'] at hB; rw [if_pos ha'] at hA
      have e := hsame (hsymA.symm.trans (ha'.trans (hb'.symm.trans hsymB)))
      have := bb_eq_of_sym2 M (hsymA.symm.trans ha')
      omega
    · rw [if_pos hb'] at hB; rw [if_neg ha'] at hA
      have := bb_eq_of_sym2 M (hsymB.symm.trans hb')
      omega
    · rw [if_neg hb'] at hB; rw [if_pos ha'] at hA
      have := bb_eq_of_sym2 M (hsymA.symm.trans ha')
      omega
    · rw [if_neg hb'] at hB; rw [if_neg ha'] at hA
      omega
  -- operation (d) on `{b}`
  have hYb : ∀ a ∈ Tb.Y, ∀ c ∈ Tb.Y, (piece Ta.post Tb.Y).SameComponent a c := by
    intro a ha c hc; rw [hTbY] at ha hc; rw [mem_singleton.mp ha, mem_singleton.mp hc]
    exact Relation.EqvGen.refl _
  have hnotB' : ∀ w, (cls w).IsEps → w ∉ ({v₂, b} : Finset V) \ Ta.Y := fun w hw h => hnotB w hw (mem_sdiff.mp h).1
  have hA2 := hRd' Ta.post hcapA hloopA hconnA Tb.Y (({v₂, b} : Finset V) \ Ta.Y) Tb.y Tb.x Tb.sub
    (by rw [hTbY, hTaY]; intro x hx; rw [mem_singleton.mp hx]; simp [h2b.symm]) (by rw [hcYb]; norm_num)
    (fun x hx => by rw [hTbY] at hx; rw [mem_singleton.mp hx]; exact hdirP)
    (by rw [Tb.cross]; exact pair_comm _ _) Tb.out_y Tb.out_x Tb.far.symm (hnotB' _ hTbdε) (hnotB' _ hTbcε) hYb
    hconnB hgoodB P'' hP'' _ (fun κ h => h)
  refine hA2.trans (mul_le_mul' le_rfl ?_)
  unfold AFreeSupAdm
  refine iSup₂_le fun P₃ hP₃ => ?_
  change MoleProp.countAFree Tb.post L γ δ C1 (0 : Mom d)
    (lgAdmOff Tb.post ((({v₂, b} : Finset V) \ Ta.Y) \ Tb.Y) L γ (η / 2 / 2) P₃) P₃ ≤ _
  have hsd : (({v₂, b} : Finset V) \ Ta.Y) \ Tb.Y = ∅ := by
    apply eq_empty_of_forall_notMem
    intro x h
    obtain ⟨h1', h2'⟩ := mem_sdiff.mp h
    obtain ⟨h3', h4'⟩ := mem_sdiff.mp h1'
    rw [hTbY] at h2'; rw [hTaY] at h4'
    simp only [mem_insert, mem_singleton] at h2' h3' h4'
    rcases h3' with e | e
    · exact h4' e
    · exact h2' e
  calc MoleProp.countAFree Tb.post L γ δ C1 (0 : Mom d)
        (lgAdmOff Tb.post ((({v₂, b} : Finset V) \ Ta.Y) \ Tb.Y) L γ (η / 2 / 2) P₃) P₃
      ≤ MoleProp.countAFree Tb.post L γ δ C1 (0 : Mom d) (lgAdm Tb.post L γ (η / 2 / 2) P₃) P₃ := by
        refine countAFree_mono_adm _ (fun κ h => ?_)
        rw [hsd] at h; exact lgAdmOff_empty h
    _ = AFree Tb.post d L γ δ (η / 2 / 2) C1 P₃ := rfl
    _ ≤ _ := h102 Tb.post hmolB hconnB hle2 hEB hszB P₃ hP₃

end

end WaveTurbulence.GammaLow.FinalCount.Count
