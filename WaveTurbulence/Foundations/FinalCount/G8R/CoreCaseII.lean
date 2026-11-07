/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreBiBridge
import Mathlib.Tactic

/-! # Core case II: a bi-bridge

DH23 L1967–L1969. The decorations split by `Q : k_{ℓ₁} = k_{ℓ₂}` (`ℓ₁, ℓ₂` the bi-bridge):
* `¬Q`: the first alternative — remove `ℓ₁, ℓ₂` (deviation `n (log L)^C L^{γ₀}`), Prop 10.2 on both sides:
  `L^{γ₀} · (L^{−3γ₀/5})² = L^{−γ₀/5}`;
* `Q`: the second alternative — in `𝕄 ∖ ℓ`, replace `ℓ₁, ℓ₂` by one bond `a₁ → a₂` on the side of `ℓ`; both sides have
  `E = 2V − 1` and no triple bond (`bibridge_no_double`), so Prop 10.2 gives `(L^{−3γ₀/5})²`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **Structure of a side with the re-inserted bond**: it is a connected molecule with no triple bond, `E = 2V − 1`,
at most as many atoms as `K`, and has an atom of degree at most three. -/
theorem addBond_facts
    (K : Molecule V D) (hcap : ∀ a ∈ K.atoms, K.outdeg a ≤ 2 ∧ K.indeg a ≤ 2) (hle2 : ∀ a b, K.bondsBetween a b ≤ 2)
    {S : Finset V} (hS : S ⊆ K.atoms) {y₁ y₂ : D} (hs : crossDarts K S = {y₁, y₂}) (ho1 : K.out y₁ = true)
    (ho2 : K.out y₂ = false) (hne : K.atom y₁ ≠ K.atom y₂) (hbb : K.bondsBetween (K.atom y₁) (K.atom y₂) ≤ 1)
    (hconn : ∀ a ∈ S, ∀ b ∈ S, (piece K S).SameComponent a b) {z : V} (hz : z ∈ S) (hz3 : K.deg z ≤ 3)
    (hsum : ∑ v ∈ S, K.deg v + 2 = 4 * S.card) :
    (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).IsMolecule ∧
    (∀ a ∈ (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).atoms, ∀ b ∈ (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).atoms,
      (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).SameComponent a b) ∧
    (∀ a b, (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).bondsBetween a b ≤ 2) ∧
    ((Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).bonds.card : ℤ) =
      2 * (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).atoms.card - 1 ∧
    (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).atoms.card ≤ K.atoms.card ∧
    ((Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).deg z ≤ 3) := by
  classical
  have hy1 : y₁ ∈ crossDarts K S := by rw [hs]; exact mem_insert_self _ _
  have hy2 : y₂ ∈ crossDarts K S := by rw [hs]; exact mem_insert_of_mem (mem_singleton_self _)
  have ha1 : (K.atom y₁) ∈ S := (mem_crossDarts.mp hy1).1
  have ha2 : (K.atom y₂) ∈ S := (mem_crossDarts.mp hy2).1
  have hatoms : (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).atoms = S := by
    change insert (K.atom y₁) (insert (K.atom y₂) (piece K S).atoms) = S
    rw [piece_atoms hS, insert_eq_of_mem ha2, insert_eq_of_mem ha1]
  -- connectivity
  have hconnSg : ∀ a ∈ (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).atoms, ∀ b ∈ (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).atoms, (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).SameComponent a b := by
    rw [hatoms]
    intro a ha b hb
    refine Relation.EqvGen.mono (fun u w huw => ?_) a b (hconn a ha b hb)
    obtain ⟨x, rfl, rfl⟩ := huw
    exact ⟨Sum.inl x, rfl, rfl⟩
  -- bond counts
  have hle2Sg : ∀ a b, (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).bondsBetween a b ≤ 2 := by
    intro a b
    rw [addBond_bondsBetween]
    have hpb : ∀ u w, (piece K S).bondsBetween u w ≤ K.bondsBetween u w := fun u w => erase_bonds_le K _ u w
    by_cases h : s((K.atom y₁), (K.atom y₂)) = s(a, b)
    · rw [ite_of_pos h]
      have : (piece K S).bondsBetween a b = (piece K S).bondsBetween (K.atom y₁) (K.atom y₂) := by
        rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [← h1, ← h2, Degen.bondsBetween_comm]
      have := hpb (K.atom y₁) (K.atom y₂)
      omega
    · rw [ite_of_not h]; have := hpb a b; have := hle2 a b; omega
  have hE : ((Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).bonds.card : ℤ) = 2 * (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).atoms.card - 1 := by
    rw [hatoms, Mole.addBond_card_bonds]
    have h := two_mul_piece_bonds K hS
    rw [hs, card_pair (fun h' => hne (congrArg K.atom h'))] at h
    push_cast
    omega
  -- caps
  have hcapP := caps_eraseAtoms (K.atoms \ S) hcap
  have hcapSg : ∀ a ∈ (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).atoms, (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).outdeg a ≤ 2 ∧ (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).indeg a ≤ 2 := by
    intro a ha
    rw [hatoms] at ha
    have haP : a ∈ (piece K S).atoms := by rw [piece_atoms hS]; exact ha
    have hnot : a ∉ K.atoms \ S := fun h => (mem_sdiff.mp h).2 ha
    constructor
    · rw [addBond_outdeg]
      by_cases h1 : (K.atom y₁) = a
      · rw [ite_of_pos h1]
        have key : (piece K S).outdeg a + 1 ≤ K.outdeg a := card_dir_erase_lt K (K.atoms \ S) hnot true (z := y₁) h1
          (mem_sdiff.mpr ⟨K.atom_mem _, (mem_crossDarts.mp hy1).2⟩) ho1
        have hc := (hcap a (hS ha)).1
        omega
      · rw [ite_of_not h1, add_zero]; exact (hcapP a haP).1
    · rw [addBond_indeg']
      by_cases h2 : (K.atom y₂) = a
      · rw [ite_of_pos h2]
        have key : (piece K S).indeg a + 1 ≤ K.indeg a := card_dir_erase_lt K (K.atoms \ S) hnot false (z := y₂) h2
          (mem_sdiff.mpr ⟨K.atom_mem _, (mem_crossDarts.mp hy2).2⟩) ho2
        have hc := (hcap a (hS ha)).2
        omega
      · rw [ite_of_not h2, add_zero]; exact (hcapP a haP).2
  -- a low-degree atom
  have hz3Sg : (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).deg z ≤ 3 := by
    rw [Mole.addBond_deg]
    have hle : (piece K S).deg z ≤ K.deg z := by
      have := deg_eraseAtoms_add (N := K) (K.atoms \ S) (v := z) (fun h => (mem_sdiff.mp h).2 hz)
      change (Degen.eraseAtoms K (K.atoms \ S)).deg z ≤ _
      omega
    by_cases h1 : K.atom y₁ = z
    · have hlt := piece_deg_lt K hy1
      rw [h1] at hlt
      rw [ite_of_pos h1, ite_of_not (fun h => hne (h1.trans h.symm))]
      omega
    · by_cases h2 : K.atom y₂ = z
      · have hlt := piece_deg_lt K hy2
        rw [h2] at hlt
        rw [ite_of_not h1, ite_of_pos h2]
        omega
      · rw [ite_of_not h1, ite_of_not h2]; omega
  have hzSg : (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).deg z ≠ 4 := by omega
  have hmol := isMolecule_of_connected (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)) hcapSg hconnSg (by rw [hatoms]; exact hz) hzSg
  exact ⟨hmol, hconnSg, hle2Sg, hE, by rw [hatoms]; exact card_le_card hS, hz3Sg⟩

/-- **Every cell of a side with the re-inserted bond is good.** -/
theorem addBond_goodCell
    (K : Molecule V D) (hcap : ∀ a ∈ K.atoms, K.outdeg a ≤ 2 ∧ K.indeg a ≤ 2) (hle2 : ∀ a b, K.bondsBetween a b ≤ 2)
    {S : Finset V} (hS : S ⊆ K.atoms) {y₁ y₂ : D} (hs : crossDarts K S = {y₁, y₂}) (ho1 : K.out y₁ = true)
    (ho2 : K.out y₂ = false) (hne : K.atom y₁ ≠ K.atom y₂) (hbb : K.bondsBetween (K.atom y₁) (K.atom y₂) ≤ 1)
    (hconn : ∀ a ∈ S, ∀ b ∈ S, (piece K S).SameComponent a b) {z : V} (hz : z ∈ S) (hz3 : K.deg z ≤ 3)
    (hsum : ∑ v ∈ S, K.deg v + 2 = 4 * S.card) :
    ∀ S' ∈ MoleProp.ladderCells (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)),
      GoodCell (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)) S' := by
  obtain ⟨_, hc, _, _, _, h3⟩ := addBond_facts K hcap hle2 hS hs ho1 ho2 hne hbb hconn hz hz3 hsum
  have hz' : z ∈ (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)).atoms := by
    have : (K.atom y₁) ∈ S := (mem_crossDarts.mp (by rw [hs]; exact mem_insert_self _ _ : y₁ ∈ crossDarts K S)).1
    change z ∈ insert (K.atom y₁) (insert (K.atom y₂) (piece K S).atoms)
    rw [piece_atoms hS]; exact mem_insert_of_mem (mem_insert_of_mem hz)
  exact fun S' hS' => goodCell_of_connected_low hc hz' h3 hS'

/-- **Prop 10.2 for a side with the re-inserted bond.** -/
theorem afreeSup_addBond_le {d : ℕ} {L γ δ η C1 : ℝ} {m : ℕ} (h102 : Prop102At.{u, v} d L γ δ η C1 m)
    (K : Molecule V D) (hsz : (K.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m)
    (hcap : ∀ a ∈ K.atoms, K.outdeg a ≤ 2 ∧ K.indeg a ≤ 2) (hle2 : ∀ a b, K.bondsBetween a b ≤ 2)
    {S : Finset V} (hS : S ⊆ K.atoms) {y₁ y₂ : D} (hs : crossDarts K S = {y₁, y₂}) (ho1 : K.out y₁ = true)
    (ho2 : K.out y₂ = false) (hne : K.atom y₁ ≠ K.atom y₂) (hbb : K.bondsBetween (K.atom y₁) (K.atom y₂) ≤ 1)
    (hconn : ∀ a ∈ S, ∀ b ∈ S, (piece K S).SameComponent a b) {z : V} (hz : z ∈ S) (hz3 : K.deg z ≤ 3)
    (hsum : ∑ v ∈ S, K.deg v + 2 = 4 * S.card) :
    AFreeSup (Mole.addBond (piece K S) (K.atom y₁) (K.atom y₂)) d L γ δ η C1 ≤
      ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ)))) := by
  obtain ⟨hmol, hconnSg, hle2Sg, hE, hcard, _⟩ := addBond_facts K hcap hle2 hS hs ho1 ho2 hne hbb hconn hz hz3 hsum
  exact iSup₂_le fun P hP => h102 _ hmol hconnSg hle2Sg hE (hsz.trans' (by exact_mod_cast hcard)) P hP

/-- In `𝕄 ∖ ℓ` without bridge, every proper part has at least two crossing darts. -/
theorem IsCore.eraseBond_two_le_cross {M : Molecule V D} (hM : IsCore M) (e : D)
    (hnoB : ∀ S ⊆ M.atoms, (crossDarts (MoleProp.eraseBond M e) S).card ≠ 1) :
    ∀ T ⊆ (MoleProp.eraseBond M e).atoms, ∀ a ∈ T, ∀ b ∈ (MoleProp.eraseBond M e).atoms, b ∉ T →
      2 ≤ (crossDarts (MoleProp.eraseBond M e) T).card := by
  intro T hT a ha b hb hbT
  have h1 := hM.eraseBond_one_le_cross e T hT a ha b hb hbT
  have h2 := hnoB T hT
  omega

/-- **Case II: a bi-bridge** — the decoration split `k_{ℓ₁} = k_{ℓ₂}`. -/
theorem case_bibridge {d : ℕ} {L γ δ η C1 K₁ B₁ K₂ B₂ : ℝ} (hL : 0 < L)
    (hbb : BiBridgeAt.{u, v} d L γ δ η C1 K₁ B₁) (hbe : BiBridgeEqualAt.{u, v} d L γ δ η C1 K₂ B₂)
    {m : ℕ} (h102 : Prop102At.{u, v} d L γ δ η C1 m) {M : Molecule V D}
    (hsz : (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m) (hM : IsCore M) (e : D)
    (hcutv : ∀ w ∈ M.atoms, ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ w → b ≠ w →
      (Degen.eraseAtoms M {w}).SameComponent a b)
    (hnoB : ∀ S ⊆ M.atoms, (crossDarts (MoleProp.eraseBond M e) S).card ≠ 1)
    (hII : ∃ S ⊆ M.atoms, ∃ a ∈ S, ∃ b ∈ M.atoms, b ∉ S ∧ (crossDarts M S).card = 2) :
    SplitBound M e d L γ δ η C1
      (K₁ * Real.log L ^ B₁ * (M.atoms.card + 1) * L ^ min γ (1 - γ) *
        (L ^ (-(3 / 5 * min γ (1 - γ))) * L ^ (-(3 / 5 * min γ (1 - γ)))))
      (K₂ * Real.log L ^ B₂ * (L ^ (-(3 / 5 * min γ (1 - γ))) * L ^ (-(3 / 5 * min γ (1 - γ))))) := by
  classical
  obtain ⟨S, hS, hp, hq, h2, ⟨b, hbM, hbS⟩, hmin⟩ := exists_min_bibridge e hnoB hII
  obtain ⟨x₁, x₂, hx12, hs, ho1, ho2⟩ := bibridge_darts hM hS h2
  have hne := bibridge_atoms_ne hcutv hS hs hp hq (hM.loop e) hbM hbS
  have hnd := bibridge_no_double hM e hnoB hS hp hq ⟨b, hbM, hbS⟩ hmin hs hne
  have hx1 : x₁ ∈ crossDarts M S := by rw [hs]; exact mem_insert_self _ _
  have hx2 : x₂ ∈ crossDarts M S := by rw [hs]; exact mem_insert_of_mem (mem_singleton_self _)
  have hpos : 0 ≤ L ^ (-(3 / 5 * min γ (1 - γ))) := Real.rpow_nonneg hL.le _
  have hT : M.atoms \ S ⊆ M.atoms := sdiff_subset
  -- the two sides in `𝕄`
  have hk := two_le_cross_of_reg M hM.reg hM.conn
  have hcT : (crossDarts M (M.atoms \ S)).card = 2 := by rw [card_crossDarts_compl, h2]
  have hconnS := piece_connected_of_cross M hk hS (by omega : (crossDarts M S).card < 2 * 2)
  have hconnT := piece_connected_of_cross M hk hT (by omega : (crossDarts M (M.atoms \ S)).card < 2 * 2)
  have hEM : ∀ {Y : Finset V}, Y ⊆ M.atoms → (crossDarts M Y).card = 2 →
      ((piece M Y).bonds.card : ℤ) = 2 * Y.card - 1 := by
    intro Y hY hc
    have h := two_mul_piece_bonds M hY
    rw [sum_congr rfl fun v hv => hM.reg v (hY hv), sum_const, smul_eq_mul, hc] at h
    omega
  obtain ⟨xT, hxT⟩ : (crossDarts M (M.atoms \ S)).Nonempty := card_pos.mp (by omega)
  have hzS := piece_deg_lt M hx1
  have hzT := piece_deg_lt M hxT
  rw [hM.reg _ (M.atom_mem _)] at hzS hzT
  have hAS := afreeSup_piece_le h102 M hsz hS hM.cap hM.le2 hconnS (mem_crossDarts.mp hx1).1 (by omega) (hEM hS h2)
  have hAT := afreeSup_piece_le h102 M hsz hT hM.cap hM.le2 hconnT (mem_crossDarts.mp hxT).1 (by omega) (hEM hT hcT)
  -- the darts of the bi-bridge in `𝕄 ∖ ℓ`
  have hxe : ∀ x ∈ crossDarts M S, x ≠ e ∧ x ≠ M.mate e := by
    intro x hx
    obtain ⟨_, h2'⟩ := mem_crossDarts.mp hx
    exact ⟨fun h => h2' (h ▸ hq), fun h => h2' (by rw [h, M.mate_mate]; exact hp)⟩
  let y₁ : MoleProp.WithoutBondDart M e := ⟨x₁, hxe x₁ hx1⟩
  let y₂ : MoleProp.WithoutBondDart M e := ⟨x₂, hxe x₂ hx2⟩
  have hsN : crossDarts (MoleProp.eraseBond M e) S = {y₁, y₂} := by
    ext z
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hz
      have h0 := mem_crossDarts.mp hz
      have hz' : z.val ∈ crossDarts M S := (mem_crossDarts (N := M)).mpr h0
      rw [hs] at hz'
      rcases mem_insert.mp hz' with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext (mem_singleton.mp h))
    · rintro (rfl | rfl)
      · have h0 := mem_crossDarts.mp hx1
        exact (mem_crossDarts (N := (MoleProp.eraseBond M e))).mpr h0
      · have h0 := mem_crossDarts.mp hx2
        exact (mem_crossDarts (N := (MoleProp.eraseBond M e))).mpr h0
  have hy12 : y₁ ≠ y₂ := fun h => hx12 (congrArg Subtype.val h)
  have hk2N := hM.eraseBond_two_le_cross e hnoB
  have hcNS : (crossDarts (MoleProp.eraseBond M e) S).card = 2 := by rw [hsN, card_pair hy12]
  have hcNT : (crossDarts (MoleProp.eraseBond M e) (M.atoms \ S)).card = 2 :=
    (card_crossDarts_compl (MoleProp.eraseBond M e) S : (crossDarts (MoleProp.eraseBond M e) (M.atoms \ S)).card = _).trans hcNS
  have hconnNS := piece_connected_of_cross (MoleProp.eraseBond M e) hk2N hS (by omega : (crossDarts (MoleProp.eraseBond M e) S).card < 2 * 2)
  have hconnNT := piece_connected_of_cross (MoleProp.eraseBond M e) hk2N hT (by omega : (crossDarts (MoleProp.eraseBond M e) (M.atoms \ S)).card < 2 * 2)
  have hcapN := caps_eraseBond M e hM.cap
  have hle2N : ∀ a b, (MoleProp.eraseBond M e).bondsBetween a b ≤ 2 := fun a b => (bondsBetween_eraseBond_le' M e a b).trans (hM.le2 a b)
  have hsumS := hM.eraseBond_sum_deg e hS
  rw [ite_of_pos hp, ite_of_pos hq] at hsumS
  have hsumT := hM.eraseBond_sum_deg e hT
  rw [ite_of_not (fun h => (mem_sdiff.mp h).2 hp), ite_of_not (fun h => (mem_sdiff.mp h).2 hq)] at hsumT
  have hASg := afreeSup_addBond_le h102 (MoleProp.eraseBond M e) hsz hcapN hle2N hS hsN ho1 ho2 hne hnd hconnNS hp
    (by rw [hM.eraseBond_deg_p e]) (by omega)
  have hENT : ((piece (MoleProp.eraseBond M e) (M.atoms \ S)).bonds.card : ℤ) = 2 * (M.atoms \ S).card - 1 := by
    have h := two_mul_piece_bonds (MoleProp.eraseBond M e) (Y := M.atoms \ S) hT
    rw [hcNT] at h
    omega
  obtain ⟨zT, hzT'⟩ : (crossDarts (MoleProp.eraseBond M e) (M.atoms \ S)).Nonempty := card_pos.mp (by omega)
  have hzNT := piece_deg_lt (MoleProp.eraseBond M e) hzT'
  have hdN : (MoleProp.eraseBond M e).deg ((MoleProp.eraseBond M e).atom zT) ≤ 4 := hM.eraseBond_deg_le e (M.atom_mem zT.val)
  have hANT := afreeSup_piece_le h102 (MoleProp.eraseBond M e) hsz hT hcapN hle2N hconnNT (mem_crossDarts.mp hzT').1 (by omega) hENT
  have hgoodSg := addBond_goodCell (MoleProp.eraseBond M e) hcapN hle2N hS hsN ho1 ho2 hne hnd hconnNS hp
    (by rw [hM.eraseBond_deg_p e]) (by omega)
  refine ⟨fun κ => κ x₁ = κ x₂, fun P hP => ?_, fun P hP => ?_⟩
  · have hmain := hbb M hM.cap hM.loop S x₁ x₂ hS hs hx12 (by rw [ho1, ho2]; decide) hM.conn hconnS hconnT P hP
      (fun κ => lgAdm M L γ η P κ ∧ ¬ κ x₁ = κ x₂) (fun κ h => h)
    refine hmain.trans ((mul_le_mul' (mul_le_mul' le_rfl hAS) hAT).trans ?_)
    rw [mul_assoc, ← ENNReal.ofReal_mul hpos, ← ENNReal.ofReal_mul' (mul_nonneg hpos hpos)]
  · have hmain := hbe (MoleProp.eraseBond M e) hcapN (hM.eraseBond_loop e) S y₁ y₂ hS hsN hy12 ho1 ho2 (hM.eraseBond_conn e) hconnNT hgoodSg P hP
      (fun κ => lgAdm (MoleProp.eraseBond M e) L γ η P κ ∧ MoleProp.erasedBondAdmissibility M e
        (fun κ0 => MoleProp.LargeGap M L γ η 0 κ0 ∧ κ0 x₁ = κ0 x₂) κ) (fun κ h => ⟨h.1, by
        obtain ⟨κ0, ⟨_, hQ⟩, _, hκ⟩ := h.2
        rw [← hκ]; exact hQ⟩)
    refine hmain.trans ((mul_le_mul' (mul_le_mul' le_rfl hASg) hANT).trans ?_)
    rw [mul_assoc, ← ENNReal.ofReal_mul hpos, ← ENNReal.ofReal_mul' (mul_nonneg hpos hpos)]

end WaveTurbulence.MoleProp4
