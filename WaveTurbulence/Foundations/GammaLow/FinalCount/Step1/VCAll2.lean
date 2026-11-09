/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCAll2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll1
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCAll2`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 31: structural facts of a VC formed by two double bonds `a = x = b` (`DoubleShape`):
the removed vine has `4` bonds and no ladder (DH23 L1801, last sentence; three atoms host no ladder). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
  {M : Molecule V D} {K : VineCut g M} (S : DoubleShape K)

include S in
/-- A VC formed by two double bonds contains no ladder (a ladder has at least four atoms). -/
theorem double_noLadder : K.vc.maximalLadders = ∅ := by
  ext T
  simp only [Finset.notMem_empty, iff_false]
  intro hT
  obtain ⟨m, u, v, hlad, rfl⟩ := ((mem_maximalLadders_iff K.vc).1 hT).1
  have h1 := card_ladderAtoms K.vc hlad
  have h2 : Molecule.ladderAtoms u v ⊆ K.C.atoms := by
    intro z hz
    obtain ⟨j, hj | hj⟩ := (FinalCount.mem_ladderAtoms u v z).1 hz
    · exact mem_vc_atoms_gen K (hj ▸ (hlad.2.2.1 j).1)
    · exact mem_vc_atoms_gen K (hj ▸ (hlad.2.2.1 j).2)
  have h3 : K.C.atoms.card = 3 := by
    rw [S.atoms_eq]
    have h1 : K.C.upper ≠ S.x := S.x_ne_a.symm
    have h2 : S.x ≠ K.C.lower := S.x_ne_b
    have h3 : K.C.upper ≠ K.C.lower := K.ab_ne
    rw [Finset.card_insert_of_notMem (by simp [h1, h3]), Finset.card_pair h2]
  have := Finset.card_le_card h2
  have hm := hlad.1
  omega


section Bonds
include S

theorem double_cutMol_atom_a (x : D) :
    K.cutMol.atom x = K.C.upper ↔ (M.atom x = K.C.upper ∧ (x = K.x₁ ∨ x = K.x₂)) := by
  rw [← mem_dartsAt, show K.cutMol.dartsAt K.C.upper = K.m1.dartsAt K.C.upper from
    cut_dartsAt_other K.m1 K.cut_b K.ab_ne (K.fb_ne_a.symm)]
  exact cut_mem_dartsAt_v M K.cut_a x

theorem double_cutMol_atom_b (x : D) :
    K.cutMol.atom x = K.C.lower ↔ (x = K.y₁ ∨ x = K.y₂) := by
  have hb : ∀ y, K.m1.atom y = K.C.lower ↔ M.atom y = K.C.lower :=
    fun y => cut_atom_eq_iff M y K.ab_ne.symm K.fa_ne_b.symm
  have := cut_mem_dartsAt_v K.m1 K.cut_b x
  rw [mem_dartsAt] at this
  show (K.m1.cut K.C.lower K.fb K.y₁ K.y₂).atom x = K.C.lower ↔ _
  rw [this, hb]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by rcases h with rfl | rfl; exacts [K.My₁, K.My₂], h⟩

theorem double_cutMol_atom_x (x : D) : K.cutMol.atom x = S.x ↔ M.atom x = S.x := by
  rw [← mem_dartsAt, ← mem_dartsAt, K.dartsAt_other S.x_mem S.x_ne_a S.x_ne_b]

/-- A VC formed by two double bonds has four bonds. -/
theorem double_bonds_card : K.vc.bonds.card = 4 := by
  unfold Molecule.bonds
  show (Finset.univ.filter fun x : PDart K.cutMol (fun a => ¬ (a ∉ K.C.atoms)) => M.out x.1 = true).card = 4
  rw [card_filter_subtype' (fun x : D => ¬ (K.cutMol.atom x ∉ K.C.atoms)) (fun x => M.out x = true)]
  have hmate : ∀ z : D, M.out (M.mate z) = true ↔ M.out z = false := by
    intro z; rw [M.out_mate]; cases M.out z <;> simp
  have hset : (Finset.univ.filter fun x : D => ¬ (K.cutMol.atom x ∉ K.C.atoms) ∧ M.out x = true) =
      {K.x₂, K.y₂, M.mate K.x₁, M.mate K.y₁} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, not_not]
    constructor
    · rintro ⟨hx, ho⟩
      rw [S.atoms_eq] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx
      · obtain ⟨-, h2⟩ := (double_cutMol_atom_a S x).1 hx
        rcases h2 with rfl | rfl
        · rw [K.Mout₁] at ho; exact absurd ho (by simp)
        · exact Or.inl rfl
      · have hx' := (double_cutMol_atom_x S x).1 hx
        have : x ∈ M.dartsAt S.x := (mem_dartsAt M _ _).2 hx'
        rw [S.darts_x] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact absurd ((hmate K.x₂).1 ho) (by rw [K.Mout₂]; simp)
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact absurd ((hmate K.y₂).1 ho) (by rw [K.Mouty₂]; simp)
      · rcases (double_cutMol_atom_b S x).1 hx with rfl | rfl
        · rw [K.Mouty₁] at ho; exact absurd ho (by simp)
        · exact Or.inr (Or.inl rfl)
    · rintro (rfl | rfl | rfl | rfl)
      · refine ⟨?_, K.Mout₂⟩
        rw [(double_cutMol_atom_a S _).2 ⟨K.Mx₂, Or.inr rfl⟩]; exact K.a_mem
      · refine ⟨?_, K.Mouty₂⟩
        rw [(double_cutMol_atom_b S _).2 (Or.inr rfl)]; exact K.b_mem
      · refine ⟨?_, (hmate _).2 K.Mout₁⟩
        have : M.atom (M.mate K.x₁) = S.x := by
          have : M.mate K.x₁ ∈ M.dartsAt S.x := by rw [S.darts_x]; simp
          exact (mem_dartsAt M _ _).1 this
        rw [(double_cutMol_atom_x S _).2 this, S.atoms_eq]; simp
      · refine ⟨?_, (hmate _).2 K.Mouty₁⟩
        have : M.atom (M.mate K.y₁) = S.x := by
          have : M.mate K.y₁ ∈ M.dartsAt S.x := by rw [S.darts_x]; simp
          exact (mem_dartsAt M _ _).1 this
        rw [(double_cutMol_atom_x S _).2 this, S.atoms_eq]; simp
  rw [hset]
  have hxa : ∀ p : D, M.atom p = S.x → M.atom p ≠ K.C.upper := fun p hp e => S.x_ne_a (hp ▸ e)
  have hmx : ∀ p : D, p ∈ M.dartsAt S.x → M.atom p = S.x := fun p hp => (mem_dartsAt M _ _).1 hp
  have m1x : M.atom (M.mate K.x₁) = S.x := hmx _ (by rw [S.darts_x]; simp)
  have m3x : M.atom (M.mate K.y₁) = S.x := hmx _ (by rw [S.darts_x]; simp)
  have h1 : K.x₂ ≠ K.y₂ := K.x_ne_y _ _ K.Mx₂ K.My₂
  have h2 : K.x₂ ≠ M.mate K.x₁ := (K.cut_a.2.2.2.2.1)
  have h3 : K.x₂ ≠ M.mate K.y₁ := fun e => S.x_ne_a (by rw [← m3x, ← e, K.Mx₂])
  have h4 : K.y₂ ≠ M.mate K.x₁ := fun e => S.x_ne_b (by rw [← m1x, ← e, K.My₂])
  have h5 : K.y₂ ≠ M.mate K.y₁ := K.cut_b.2.2.2.2.1
  have h6 : M.mate K.x₁ ≠ M.mate K.y₁ := fun e => K.x_ne_y _ _ K.Mx₁ K.My₁ (mate_inj' M e)
  rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]), Finset.card_insert_of_notMem (by simp [h4, h5]),
    Finset.card_pair h6]

end Bonds

end WaveTurbulence.GammaLow.FinalCount.Step1
