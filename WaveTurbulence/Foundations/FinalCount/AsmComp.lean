/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmSplit
public import WaveTurbulence.Foundations.FinalCount.G3MapBase
/-! **FINALCOUNT-ASSEMBLY, A3b: `𝔄` of a molecule is at most the product of `𝔄` of its components.**

`R` is a set of representatives of the components (`CompRep`).  `circuitRank` and the ladder product are additive over the components, and
the decorations inject into the product of the decoration sets of the components. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- `R` is a set of representatives, one per connected component of `N`. -/
structure CompRep (N : Molecule V D) (R : Finset V) : Prop where
  mem : ∀ a ∈ R, a ∈ N.atoms
  cover : ∀ v ∈ N.atoms, ∃ a ∈ R, N.SameComponent a v
  disj : ∀ a ∈ R, ∀ b ∈ R, N.SameComponent a b → a = b

namespace CompRep
variable {N : Molecule V D} {R : Finset V} (hR : CompRep N R)
include hR

theorem unique {v : V} (hv : v ∈ N.atoms) : ∃! a, a ∈ R ∧ N.SameComponent a v := by
  obtain ⟨a, ha, hav⟩ := hR.cover v hv
  refine ⟨a, ⟨ha, hav⟩, fun b ⟨hb, hbv⟩ => ?_⟩
  exact hR.disj b hb a ha (Relation.EqvGen.trans _ _ _ hbv (Relation.EqvGen.symm _ _ hav))

/-- A sum over atoms is the sum over the components. -/
theorem sum_atoms {β : Type*} [AddCommMonoid β] (f : V → β) :
    ∑ v ∈ N.atoms, f v = ∑ a ∈ R, ∑ v ∈ N.atoms.filter (fun v => N.SameComponent a v), f v := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  obtain ⟨a₀, ⟨ha₀, hsc⟩, hu⟩ := hR.unique hv
  rw [Finset.sum_eq_single a₀]
  · simp [hsc]
  · intro b hb hne
    have : ¬ N.SameComponent b v := fun h => hne (hu b ⟨hb, h⟩)
    simp [this]
  · intro h; exact absurd ha₀ h

/-- A sum over darts is the sum over the components. -/
theorem sum_darts {β : Type*} [AddCommMonoid β] (g : D → β) :
    ∑ x : D, g x = ∑ a ∈ R, ∑ x ∈ (Finset.univ : Finset D).filter (fun x => N.SameComponent a (N.atom x)), g x := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨a₀, ⟨ha₀, hsc⟩, hu⟩ := hR.unique (N.atom_mem x)
  rw [Finset.sum_eq_single a₀]
  · simp [hsc]
  · intro b hb hne
    have : ¬ N.SameComponent b (N.atom x) := fun h => hne (hu b ⟨hb, h⟩)
    simp [this]
  · intro h; exact absurd ha₀ h

theorem numComponents_eq : N.numComponents = R.card := by
  unfold Molecule.numComponents
  let f : R → Quot (fun u v : N.atoms => N.Adj u.1 v.1) := fun a => Quot.mk _ ⟨a.1, hR.mem a.1 a.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun q => ?_⟩
    · have := (quot_mk_eq_iff N a.1 b.1 (hR.mem a.1 a.2) (hR.mem b.1 b.2)).1 hab
      exact Subtype.ext (hR.disj a.1 a.2 b.1 b.2 this)
    · induction q using Quot.ind with
      | _ v =>
        obtain ⟨a, ha, hsc⟩ := hR.cover v.1 v.2
        exact ⟨⟨a, ha⟩, (quot_mk_eq_iff N a v.1 (hR.mem a ha) v.2).2 hsc⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem atoms_card_sum : N.atoms.card = ∑ a ∈ R, (compMol N a).atoms.card := by
  have := hR.sum_atoms (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
  rw [this]
  rfl

theorem bonds_card_sum : N.bonds.card = ∑ a ∈ R, (compMol N a).bonds.card := by
  have h1 : ∀ a ∈ R, (compMol N a).bonds.card =
      (((Finset.univ : Finset D).filter (fun x => N.SameComponent a (N.atom x))).filter (fun x => N.out x = true)).card := by
    intro a _
    unfold Molecule.bonds
    show (Finset.univ.filter fun x : PDart N (compP N a) => N.out x.1 = true).card = _
    rw [card_filter_subtype' (fun x : D => compP N a (N.atom x)) (fun x => N.out x = true), Finset.filter_filter]
    rfl
  rw [Finset.sum_congr rfl h1]
  have := hR.sum_darts (fun x => if N.out x = true then (1 : ℕ) else 0)
  simp only [Finset.sum_boole, Nat.cast_id] at this
  unfold Molecule.bonds
  rw [this]

end CompRep

theorem compRep_comp (N : Molecule V D) {a : V} (ha : a ∈ N.atoms) : CompRep (compMol N a) {a} where
  mem := fun b hb => by
    rw [Finset.mem_singleton] at hb; subst hb
    exact (mem_compMol N b).2 ⟨ha, Relation.EqvGen.refl _⟩
  cover := fun v hv => by
    refine ⟨a, Finset.mem_singleton_self a, ?_⟩
    have := (mem_compMol N a).1 hv
    exact restrictP_sc_of N (compP N a) (compP_closed N a) this.2 (Relation.EqvGen.refl _)
  disj := fun b hb c hc _ => by
    rw [Finset.mem_singleton] at hb hc; rw [hb, hc]

theorem numComponents_comp (N : Molecule V D) {a : V} (ha : a ∈ N.atoms) : (compMol N a).numComponents = 1 := by
  rw [(compRep_comp N ha).numComponents_eq]; simp

namespace CompRep
variable {N : Molecule V D} {R : Finset V} (hR : CompRep N R)
include hR

theorem circuitRank_sum : N.circuitRank = ∑ a ∈ R, (compMol N a).circuitRank := by
  have h1 := hR.bonds_card_sum
  have h2 := hR.atoms_card_sum
  have h3 := hR.numComponents_eq
  have e : ∀ a ∈ R, (compMol N a).circuitRank = ((compMol N a).bonds.card : ℤ) - ((compMol N a).atoms.card : ℤ) + 1 := by
    intro a ha
    unfold Molecule.circuitRank
    rw [numComponents_comp N (hR.mem a ha)]; simp
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  unfold Molecule.circuitRank
  rw [h3]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1' : ((N.bonds.card : ℕ) : ℤ) = ∑ a ∈ R, (((compMol N a).bonds.card : ℕ) : ℤ) := by exact_mod_cast h1
  have h2' : ((N.atoms.card : ℕ) : ℤ) = ∑ a ∈ R, (((compMol N a).atoms.card : ℕ) : ℤ) := by exact_mod_cast h2
  rw [← h1', ← h2']

/-- The maximal ladders of `N` are the disjoint union of those of its components. -/
theorem maximalLadders_eq : N.maximalLadders = R.biUnion fun a => (compMol N a).maximalLadders := by
  ext S
  simp only [Finset.mem_biUnion]
  constructor
  · intro hS
    have hS' := (mem_maximalLadders_iff N).1 hS
    obtain ⟨v, hv⟩ := isLadderSet_nonempty N hS'.1
    obtain ⟨a, ha, hav⟩ := hR.cover v (isLadderSet_subset N hS'.1 hv)
    refine ⟨a, ha, ?_⟩
    show S ∈ (restrictP N (compP N a) (compP_closed N a)).maximalLadders
    rw [restrictP_maximal_iff]
    refine ⟨hS, ?_⟩
    rcases isLadderSet_cases N (compP N a) (compP_closed N a) hS'.1 with H | H
    · exact H
    · exact absurd hav (H v hv)
  · rintro ⟨a, ha, hS⟩
    have : S ∈ (restrictP N (compP N a) (compP_closed N a)).maximalLadders := hS
    rw [restrictP_maximal_iff] at this
    exact this.1

theorem maximalLadders_disj : (↑R : Set V).PairwiseDisjoint fun a => (compMol N a).maximalLadders := by
  intro a ha b hb hne
  rw [Function.onFun, Finset.disjoint_left]
  intro S hSa hSb
  have h1 : S ∈ (restrictP N (compP N a) (compP_closed N a)).maximalLadders := hSa
  have h2 : S ∈ (restrictP N (compP N b) (compP_closed N b)).maximalLadders := hSb
  rw [restrictP_maximal_iff] at h1 h2
  obtain ⟨v, hv⟩ := isLadderSet_nonempty N ((mem_maximalLadders_iff N).1 h1.1).1
  exact hne (hR.disj a ha b hb (Relation.EqvGen.trans _ _ _ (h1.2 v hv) (Relation.EqvGen.symm _ _ (h2.2 v hv))))

theorem prod_ladders (f : Finset V → ℝ) :
    ∏ S ∈ N.maximalLadders, f S = ∏ a ∈ R, ∏ S ∈ (compMol N a).maximalLadders, f S := by
  rw [hR.maximalLadders_eq, Finset.prod_biUnion hR.maximalLadders_disj]

theorem countE_le_prod (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    N.countE L γ δ w Adm ≤ ∏ a ∈ R, (compMol N a).countE L γ δ w (projAdm N (compP N a) Adm) := by
  unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk => ?_
  set S := decSet N L γ δ w Adm c β k0 with hS
  let ρ : (D → (Fin d → ℤ)) → ∀ a : R, (PDart N (compP N a.1) → (Fin d → ℤ)) := fun κ a x => κ x.1
  have hinj : Function.Injective ρ := by
    intro κ κ' e
    funext x
    obtain ⟨a, ha, hsc⟩ := hR.cover _ (N.atom_mem x)
    exact congrFun (congrFun e ⟨a, ha⟩) ⟨x, hsc⟩
  have hp : ParamOK N c k0 := ⟨hc, hk⟩
  have hsub : ρ '' S ⊆ Set.pi Set.univ (fun a : R =>
      decSet (compMol N a.1) L γ δ w (projAdm N (compP N a.1) Adm) c β (fun x => k0 x.1)) := by
    rintro _ ⟨κ, hκ, rfl⟩ a _
    exact decSet_restrict N (compP N a.1) (compP_closed N a.1) L γ δ w Adm c β k0 hκ
  calc S.encard = (ρ '' S).encard := (hinj.injOn.encard_image).symm
    _ ≤ _ := Set.encard_le_encard hsub
    _ = ∏ a : R, (decSet (compMol N a.1) L γ δ w (projAdm N (compP N a.1) Adm) c β (fun x => k0 x.1)).encard :=
        Set.encard_pi_eq_prod_encard
    _ ≤ ∏ a : R, (compMol N a.1).countE L γ δ w (projAdm N (compP N a.1) Adm) := by
        refine Finset.prod_le_prod' fun a _ => ?_
        have pa := paramOK_restrict N (compP N a.1) (compP_closed N a.1) c k0 hp
        exact decSet_encard_le_countE _ L γ δ w _ c pa.1 β _ pa.2
    _ = _ := Finset.prod_coe_sort R fun a => (compMol N a).countE L γ δ w (projAdm N (compP N a) Adm)

/-- **`𝔄(N) ≤ ∏_components 𝔄`.** -/
theorem countA_le_prod (L γ δ C₁ : ℝ) (w : Mom d) (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C₁)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Pl : Finset V → ℝ) (hX : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (Pl S)) :
    N.countA L γ δ C₁ w Adm Pl ≤ ∏ a ∈ R, (compMol N a).countA L γ δ C₁ w (projAdm N (compP N a) Adm) Pl := by
  rw [countA_eq]
  simp only [countA_eq]
  have hrf : rankFactor d L γ δ C₁ N.circuitRank = ∏ a ∈ R, rankFactor d L γ δ C₁ (compMol N a).circuitRank := by
    rw [hR.circuitRank_sum]
    clear hR
    induction R using Finset.induction_on with
    | empty =>
      simp [rankFactor]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, rankFactor_add d hL hδ hC.ne', ih]
  have hlad := hR.prod_ladders (fun S => Molecule.ladderWeight L γ δ (Pl S) ^ Molecule.ladderLength S)
  have n1 : ∀ a ∈ R, 0 ≤ rankFactor d L γ δ C₁ (compMol N a).circuitRank := fun a _ =>
    rankFactor_nonneg d hL.le hδ.le hC.le _
  have l1 : ∀ a ∈ R, 0 ≤ ∏ S ∈ (compMol N a).maximalLadders, Molecule.ladderWeight L γ δ (Pl S) ^ Molecule.ladderLength S :=
    fun a _ => Finset.prod_nonneg fun S _ => pow_nonneg (hX S) _
  have hE : ((N.countE L γ δ w Adm : ℕ∞) : ℝ≥0∞) ≤ ∏ a ∈ R, (((compMol N a).countE L γ δ w (projAdm N (compP N a) Adm) : ℕ∞) : ℝ≥0∞) := by
    have := ENat.toENNReal_le.2 (hR.countE_le_prod L γ δ w Adm)
    have e : (((∏ a ∈ R, (compMol N a).countE L γ δ w (projAdm N (compP N a) Adm) : ℕ∞)) : ℝ≥0∞) =
        ∏ a ∈ R, (((compMol N a).countE L γ δ w (projAdm N (compP N a) Adm) : ℕ∞) : ℝ≥0∞) :=
      map_prod ENat.toENNRealRingHom _ _
    rw [e] at this; exact this
  rw [hrf, hlad, ← Finset.prod_mul_distrib]
  have e : ∀ a ∈ R, rankFactor d L γ δ C₁ (compMol N a).circuitRank *
        ∏ S ∈ (compMol N a).maximalLadders, Molecule.ladderWeight L γ δ (Pl S) ^ Molecule.ladderLength S ≥ 0 :=
    fun a ha => mul_nonneg (n1 a ha) (l1 a ha)
  rw [ENNReal.ofReal_prod_of_nonneg e, Finset.prod_mul_distrib]
  gcongr

end CompRep

end WaveTurbulence.FinalCountAsm
