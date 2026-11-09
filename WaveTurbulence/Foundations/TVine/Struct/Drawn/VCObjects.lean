/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Drawn.VCChain
public import WaveTurbulence.Foundations.FinalCount.S1Overlap

/-!
# Lemma 8.1′ (packet L3D): vine-like objects over `𝒱_γ`

Main's object-level lemmas (`FinalCount/S1Erase`, `S1Split`, `S1Overlap`, `Spine/VineDelObjects`; sha256 in
`COPIED-SHA256SUMS`) restated for L6's carrier `Src.Object γ`:

* `object_overlap_premises`: the premises of the overlap classification DH23 Lemma 4.11 (main's family-free
  `Mole.molecule_overlap_classification`) hold for every designated vine-like object over `𝒱_γ`;
* `exists_object_union`: two chains meeting in one joint form a designated object (VC, or HVC/HV);
* `chain_split`: a chain cut at an atom splits into two chains;
* `member_of_chain_sigma`: a chain which is a block with exactly one bond between its joints is a single member of
  `𝒱_γ` (main: "is a type-V vine"; the DV′ replacement of N2 N6).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.Drawn.VC

open Finset WaveTurbulence.GammaLow.FinalCount WaveTurbulence.Vine

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {γ : ℝ}

/-! ## Deleting a bond outside the group; unions at one joint (main `S1Erase`) -/

theorem chain_eraseBond {S : Finset V} {a b : V} {n : ℕ} (e : D) (h : Src.Chain γ M S a b n)
    (he : ¬ M.InGroup S e) : Src.Chain γ (Molecule.eraseBond M e) S a b n := by
  induction h with
  | single hv => exact Src.Chain.single (member_eraseBond hv e he)
  | @append S' T a b c n hS hT hi hne ih =>
    exact Src.Chain.append (ih (fun h' => he (Stage1.inGroup_mono subset_union_left h')))
      (member_eraseBond hT e (fun h' => he (Stage1.inGroup_mono subset_union_right h'))) hi hne

/-- A chain `P` from `a` to `c` and a chain `Q` from `c` to `b` meeting exactly in `c`, both blocks: the union is a
designated vine-like object (a VC, or a hyper-object if the outer joints are joined by a further bond). -/
theorem exists_object_union (hM : M.IsMolecule) {P Q : Finset V} {a b c : V} {n m : ℕ}
    (hP : Src.Chain γ M P a c n) (hQ : Src.Chain γ M Q c b m) (hPQ : P ∩ Q = {c})
    (hPB : M.IsBlock P a c) (hQB : M.IsBlock Q c b) :
    ∃ W : Src.Object γ M, W.atoms = P ∪ Q ∧ W.upper = a ∧ W.lower = b := by
  have hcon := Mole.blocks_concatenate M hM hPB (Mole.block_swap_joints M hQB)
    (LGSpine.groupConnected_of_block hPB) hPQ
  rcases hcon with hU | ⟨e, he, hBe⟩
  · exact ⟨⟨P ∪ Q, a, b, .vc ⟨hU, n + m, chain_append_chain hP hQ hPQ⟩⟩, rfl, rfl, rfl⟩
  · have hbP : b ∉ P := by
      intro hb
      have : b ∈ P ∩ Q := mem_inter.mpr ⟨hb, (chain_ends hQ).2.1⟩
      rw [hPQ] at this
      exact (chain_ends hQ).2.2 (mem_singleton.mp this).symm
    have haQ : a ∉ Q := by
      intro ha
      have : a ∈ P ∩ Q := mem_inter.mpr ⟨(chain_ends hP).1, ha⟩
      rw [hPQ] at this
      exact (chain_ends hP).2.2 (mem_singleton.mp this)
    have hend := Sym2.eq_iff.mp he
    change (M.atom e = a ∧ M.atom (M.mate e) = b) ∨ (M.atom e = b ∧ M.atom (M.mate e) = a) at hend
    have hnP : ¬ M.InGroup P e := by
      rintro ⟨h1, h2⟩
      rcases hend with ⟨_, h4⟩ | ⟨h3, _⟩
      · exact hbP (h4 ▸ h2)
      · exact hbP (h3 ▸ h1)
    have hnQ : ¬ M.InGroup Q e := by
      rintro ⟨h1, h2⟩
      rcases hend with ⟨h3, _⟩ | ⟨_, h4⟩
      · exact haQ (h3 ▸ h1)
      · exact haQ (h4 ▸ h2)
    have hP' := chain_eraseBond e hP hnP
    have hQ' := chain_eraseBond e hQ hnQ
    exact ⟨⟨P ∪ Q, a, b, .hyper ⟨e, he, ⟨hBe, n + m, chain_append_chain hP' hQ' hPQ⟩⟩⟩, rfl, rfl, rfl⟩

/-! ## Cutting a chain at an atom (main `S1Split`) -/

theorem chain_split (hF1 : TVineF1Input.{u, v}) {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) :
    ∀ {L R : Finset V} {p : V}, S = L ∪ R → L ∩ R = {p} → a ∈ L → b ∈ R → a ≠ p → b ≠ p →
    (∀ x : D, M.atom x ∈ L → M.atom x ≠ p → M.InGroup S x → M.InGroup L x) →
    ∃ n0 n1, Src.Chain γ M L a p n0 ∧ Src.Chain γ M R p b n1 := by
  induction h with
  | @single T a b hv =>
    intro L R p hS hI haL hbR hap hbp HL
    have hX := member_block hv
    have hbL : b ∉ L := by
      intro hb
      have : b ∈ L ∩ R := mem_inter.mpr ⟨hb, hbR⟩
      rw [hI] at this
      exact hbp (mem_singleton.mp this)
    have hcon := member_erase_connected hF1 hv p
    have haT : a ∈ T.erase p := mem_erase.mpr ⟨hap, hX.2.1⟩
    have hbT : b ∈ T.erase p := mem_erase.mpr ⟨hbp, hX.2.2.1⟩
    have := Stage1.side_iff (S := T) (L := L) (X := T.erase p) (erase_subset _ _) (by simp) HL
      (hcon a haT b hbT)
    exact absurd (this.mp haL) hbL
  | @append S' T a q b n hS hT hi hne ih =>
    intro L R p hSLR hI haL hbR hap hbp HL
    have hX := member_block hT
    have hS'S : S' ⊆ S' ∪ T := subset_union_left
    have hTS : T ⊆ S' ∪ T := subset_union_right
    have hq : q ∈ T := hX.2.1
    have hbT : b ∈ T := hX.2.2.1
    have haS' : a ∈ S' := (chain_ends hS).1
    have hqS' : q ∈ S' := (chain_ends hS).2.1
    have hbL : b ∉ L := by
      intro hb
      have : b ∈ L ∩ R := mem_inter.mpr ⟨hb, hbR⟩
      rw [hI] at this
      exact hbp (mem_singleton.mp this)
    have hpLR : p ∈ L ∧ p ∈ R := by
      have : p ∈ L ∩ R := by rw [hI]; exact mem_singleton_self _
      exact mem_inter.mp this
    have hpS : p ∈ S' ∪ T := by rw [hSLR]; exact mem_union_left _ hpLR.1
    have hconS' : ∀ x ∈ S', ∀ y ∈ S', (Mole.induced M S').SameComponent x y := chain_connected hS
    by_cases hpT : p ∈ T
    · by_cases hpq : p = q
      · -- the cut atom is the joint between the last ingredient and the prefix
        subst hpq
        have hc1 : ∀ x ∈ S'.erase p, ∀ y ∈ S'.erase p,
            (Mole.induced M (S'.erase p)).SameComponent x y :=
          chain_erase_first_connected hF1 (chain_swap hS)
        have hc2 := member_erase_connected hF1 hT p
        have haE : a ∈ S'.erase p := mem_erase.mpr ⟨hap, haS'⟩
        have hbE : b ∈ T.erase p := mem_erase.mpr ⟨hbp, hbT⟩
        have hS'L : ∀ x ∈ S'.erase p, x ∈ L := fun x hx =>
          (Stage1.side_iff (S := S' ∪ T) (L := L) (X := S'.erase p) ((erase_subset _ _).trans hS'S)
            (by simp) HL (hc1 a haE x hx)).mp haL
        have hTnL : ∀ x ∈ T.erase p, x ∉ L := fun x hx hL =>
          hbL ((Stage1.side_iff (S := S' ∪ T) (L := L) (X := T.erase p)
            ((erase_subset _ _).trans hTS) (by simp) HL (hc2 x hx b hbE)).mp hL)
        have hLeq : L = S' := by
          ext x
          constructor
          · intro hx
            have hxS : x ∈ S' ∪ T := by rw [hSLR]; exact mem_union_left _ hx
            rcases mem_union.mp hxS with h1 | h1
            · exact h1
            · by_cases hxp : x = p
              · exact hxp ▸ hqS'
              · exact absurd hx (hTnL x (mem_erase.mpr ⟨hxp, h1⟩))
          · intro hx
            by_cases hxp : x = p
            · exact hxp ▸ hpLR.1
            · exact hS'L x (mem_erase.mpr ⟨hxp, hx⟩)
        have hReq : R = T := by
          ext x
          constructor
          · intro hx
            have hxS : x ∈ S' ∪ T := by rw [hSLR]; exact mem_union_right _ hx
            rcases mem_union.mp hxS with h1 | h1
            · by_cases hxp : x = p
              · exact hxp ▸ hpT
              · have hxL := hS'L x (mem_erase.mpr ⟨hxp, h1⟩)
                have : x ∈ L ∩ R := mem_inter.mpr ⟨hxL, hx⟩
                rw [hI] at this
                exact absurd (mem_singleton.mp this) hxp
            · exact h1
          · intro hx
            by_cases hxp : x = p
            · exact hxp ▸ hpLR.2
            · have hxS : x ∈ S' ∪ T := hTS hx
              rw [hSLR] at hxS
              rcases mem_union.mp hxS with h1 | h1
              · exact absurd h1 (hTnL x (mem_erase.mpr ⟨hxp, hx⟩))
              · exact h1
        subst hLeq
        subst hReq
        exact ⟨n, 1, hS, Src.Chain.single hT⟩
      · -- the cut atom is interior to the last vine: impossible
        have hpS' : p ∉ S' := by
          intro hp'
          have : p ∈ S' ∩ T := mem_inter.mpr ⟨hp', hpT⟩
          rw [hi] at this
          exact hpq (mem_singleton.mp this)
        have hqL : q ∈ L := (Stage1.side_iff (S := S' ∪ T) (L := L) (X := S') hS'S hpS' HL
          (hconS' a haS' q hqS')).mp haL
        have hc2 := member_erase_connected hF1 hT p
        have hqE : q ∈ T.erase p := mem_erase.mpr ⟨Ne.symm hpq, hq⟩
        have hbE : b ∈ T.erase p := mem_erase.mpr ⟨hbp, hbT⟩
        exact absurd ((Stage1.side_iff (S := S' ∪ T) (L := L) (X := T.erase p)
          ((erase_subset _ _).trans hTS) (by simp) HL (hc2 q hqE b hbE)).mp hqL) hbL
    · -- the cut atom lies in the prefix
      have hpS' : p ∈ S' := by
        rcases mem_union.mp hpS with h | h
        · exact h
        · exact absurd h hpT
      have hpq : p ≠ q := fun h => hpT (h ▸ hq)
      have hconT := member_connected hT
      have hTnL : ∀ x ∈ T, x ∉ L := fun x hx hL =>
        hbL ((Stage1.side_iff (S := S' ∪ T) (L := L) (X := T) hTS hpT HL (hconT x hx b hbT)).mp hL)
      have hqR : q ∈ R := by
        have hqS : q ∈ S' ∪ T := hTS hq
        rw [hSLR] at hqS
        rcases mem_union.mp hqS with h1 | h1
        · exact absurd h1 (hTnL q hq)
        · exact h1
      have hS'eq : S' = (L ∩ S') ∪ (R ∩ S') := by
        ext x
        constructor
        · intro hx
          have hxS : x ∈ L ∪ R := by rw [← hSLR]; exact hS'S hx
          rcases mem_union.mp hxS with h1 | h1
          · exact mem_union_left _ (mem_inter.mpr ⟨h1, hx⟩)
          · exact mem_union_right _ (mem_inter.mpr ⟨h1, hx⟩)
        · intro hx
          rcases mem_union.mp hx with h1 | h1
          · exact (mem_inter.mp h1).2
          · exact (mem_inter.mp h1).2
      have hI' : (L ∩ S') ∩ (R ∩ S') = {p} := by
        ext x
        constructor
        · intro hx
          have : x ∈ L ∩ R := mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hx).1).1,
            (mem_inter.mp (mem_inter.mp hx).2).1⟩
          rw [hI] at this
          exact this
        · intro hx
          have hxp := mem_singleton.mp hx
          subst hxp
          exact mem_inter.mpr ⟨mem_inter.mpr ⟨hpLR.1, hpS'⟩, mem_inter.mpr ⟨hpLR.2, hpS'⟩⟩
      have HL' : ∀ x : D, M.atom x ∈ L ∩ S' → M.atom x ≠ p → M.InGroup S' x →
          M.InGroup (L ∩ S') x := by
        intro x hx hxp hg
        have h1 := HL x (mem_inter.mp hx).1 hxp (Stage1.inGroup_of_subset hS'S hg)
        exact ⟨mem_inter.mpr ⟨h1.1, hg.1⟩, mem_inter.mpr ⟨h1.2, hg.2⟩⟩
      obtain ⟨n0, n1, hL', hR'⟩ := ih hS'eq hI' (mem_inter.mpr ⟨haL, haS'⟩)
        (mem_inter.mpr ⟨hqR, hqS'⟩) hap (Ne.symm hpq) HL'
      have hLeq : L ∩ S' = L := by
        ext x
        constructor
        · exact fun hx => (mem_inter.mp hx).1
        · intro hx
          refine mem_inter.mpr ⟨hx, ?_⟩
          have hxS : x ∈ S' ∪ T := by rw [hSLR]; exact mem_union_left _ hx
          rcases mem_union.mp hxS with h1 | h1
          · exact h1
          · exact absurd hx (hTnL x h1)
      have hReq : (R ∩ S') ∪ T = R := by
        ext x
        constructor
        · intro hx
          rcases mem_union.mp hx with h1 | h1
          · exact (mem_inter.mp h1).1
          · have hxS : x ∈ S' ∪ T := hTS h1
            rw [hSLR] at hxS
            rcases mem_union.mp hxS with h2 | h2
            · exact absurd h2 (hTnL x h1)
            · exact h2
        · intro hx
          have hxS : x ∈ S' ∪ T := by rw [hSLR]; exact mem_union_right _ hx
          rcases mem_union.mp hxS with h1 | h1
          · exact mem_union_left _ (mem_inter.mpr ⟨hx, h1⟩)
          · exact mem_union_right _ h1
      rw [hLeq] at hL'
      have hRT : (R ∩ S') ∩ T = {q} := by
        ext x
        constructor
        · intro hx
          have : x ∈ S' ∩ T := mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hx).1).2, (mem_inter.mp hx).2⟩
          rw [hi] at this
          exact this
        · intro hx
          have hxq := mem_singleton.mp hx
          subst hxq
          exact mem_inter.mpr ⟨mem_inter.mpr ⟨hqR, hqS'⟩, hq⟩
      have hfin := Src.Chain.append hR' hT hRT (fun h => hbp h.symm)
      rw [hReq] at hfin
      exact ⟨n0, n1 + 1, hL', hfin⟩

/-! ## Objects which are blocks; one bond between the joints (main `S1Overlap`) -/

/-- An object whose atom set is an ordinary block has an ordinary chain shape. -/
theorem chain_of_isBlock (O : Src.Object γ M) (hB : M.IsBlock O.atoms O.upper O.lower) :
    ∃ n, Src.Chain γ M O.atoms O.upper O.lower n := by
  rcases O with ⟨S, a, b, shape⟩
  cases shape with
  | vc h => exact h.2
  | hyper R =>
    exfalso
    have h3 := Mole.hyperBlock_degrees M ⟨R.added, R.ends_eq, R.adjoint.1⟩
    have h2 := Mole.block_joint_degrees M hB
    have := h3.1
    have h2a := h2.1
    simp only at hB h3 h2
    omega

/-- A chain with at least two ingredients that is a block has no bond between its joints. -/
theorem sigma_chain_two (hM : M.IsMolecule) {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain γ M S a b n) (hB : M.IsBlock S a b) (hn : 2 ≤ n) : M.sigma a b = 0 := by
  cases h with
  | single => omega
  | @append S' T a q b n' hS hT hi hne =>
    have hX := member_block hT
    have hBS' := chain_prefix_isBlock hM hS hT hi hB
    have hbT : b ∈ T := hX.2.2.1
    have hqb : q ≠ b := hX.2.2.2.1
    have hbS' : b ∉ S' := by
      intro hb
      have : b ∈ S' ∩ T := mem_inter.mpr ⟨hb, hbT⟩
      rw [hi] at this
      exact hqb (mem_singleton.mp this).symm
    have hne' : a ≠ b := hne
    unfold Molecule.sigma
    rw [Mole.bondsBetween_eq_card_darts M hne']
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx hxb
    have hxa := (Mole.mem_dartsAt M a x).mp hx
    have hS'S : S' ⊆ S' ∪ T := subset_union_left
    have hsub : (M.dartsAt a).filter (M.InGroup S') ⊆ (M.dartsAt a).filter (M.InGroup (S' ∪ T)) := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hy1, Stage1.inGroup_of_subset hS'S hy2⟩
    have hd1 := (Mole.block_joint_degrees M hBS').1
    have hd2 := (Mole.block_joint_degrees M hB).1
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      change M.degIn (S' ∪ T) a ≤ M.degIn S' a
      omega)
    have hxg : x ∈ (M.dartsAt a).filter (M.InGroup (S' ∪ T)) :=
      Finset.mem_filter.mpr ⟨hx, ⟨hxa ▸ hB.2.1, hxb ▸ hB.2.2.1⟩⟩
    rw [← heq] at hxg
    exact hbS' (hxb ▸ (Finset.mem_filter.mp hxg).2.2)

/-- **A vine chain that is a block with exactly one bond between its joints is a single member of `𝒱_γ`** (main:
"is a type-V vine"; N2 N6). -/
theorem member_of_chain_sigma (hM : M.IsMolecule) {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain γ M S a b n) (hB : M.IsBlock S a b) (hs : M.sigma a b = 1) : Src.IsSomeVine γ M S a b := by
  by_cases hn : 2 ≤ n
  · have := sigma_chain_two hM h hB hn
    omega
  · cases h with
    | single hv => exact hv
    | append hS _ _ _ => exact absurd (by have := chain_pos hS; omega) hn

theorem chain_orient {S : Finset V} {x y a b : V} {n : ℕ} (h : Src.Chain γ M S x y n)
    (hj : ({x, y} : Finset V) = {a, b}) : Src.Chain γ M S a b n := by
  rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · exact chain_swap h

theorem block_orient {S : Finset V} {x y a b : V} (h : M.IsBlock S x y)
    (hj : ({x, y} : Finset V) = {a, b}) : M.IsBlock S a b := by
  rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · exact Mole.block_swap_joints M h

/-! ## The premises of the overlap classification (main `VineDelObjects`) -/

section F1

variable (hF1 : TVineF1Input.{u, v})
include hF1

theorem sourceVC_interior_deletion {S : Finset V} {a b : V} (h : Src.IsVC γ M S a b) :
    Mole.InteriorDeletionProperty M S a b := by
  obtain ⟨n, hc⟩ := h.2
  intro x hx hxa hxb
  exact chain_interior_deletion hF1 hc hx hxa hxb

theorem hyperAdjoint_interior_deletion {S : Finset V} {a b : V} {e : D}
    (hends : M.ends e = s(a, b)) (h : Src.IsVC γ (Molecule.eraseBond M e) S a b) :
    Mole.InteriorDeletionProperty M S a b := by
  obtain ⟨n, hc⟩ := h.2
  intro x hx hxa hxb
  have hadj : M.Adj a b := by
    have h2 : s(M.atom e, M.atom (M.mate e)) = s(a, b) := hends
    rcases Sym2.eq_iff.mp h2 with ⟨h1, h3⟩ | ⟨h1, h3⟩
    · exact ⟨e, h1, h3⟩
    · exact ⟨M.mate e, h3, by rw [M.mate_mate]; exact h1⟩
  have tr : ∀ {U : Finset V}, Mole.GroupConnected (Mole.eraseBond M e) U → Mole.GroupConnected M U :=
    fun {U} hU => ⟨hU.1, fun w hw y hy => Vine.eraseBond_induced_path M e U (hU.2 w hw y hy)⟩
  rcases chain_interior_deletion hF1 hc hx hxa hxb with hcn | ⟨U, W, hUW, _, hU, hW, haU, hbW, _⟩
  · exact Or.inl (tr hcn)
  · left
    have hUS : U ⊆ S.erase x := hUW ▸ subset_union_left
    have hWS : W ⊆ S.erase x := hUW ▸ subset_union_right
    have hU' := tr hU
    have hW' := tr hW
    refine ⟨⟨a, hUS haU⟩, fun w hw y hy => ?_⟩
    have all : ∀ z ∈ S.erase x, (Mole.induced M (S.erase x)).SameComponent a z := by
      intro z hz
      have hz' : z ∈ U ∪ W := hUW ▸ hz
      rcases mem_union.mp hz' with hzU | hzW
      · exact induced_path_mono M hUS (hU'.2 a haU z hzU)
      · refine Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _
          ((Mole.induced_adj_iff M (S.erase x) a b).mpr ⟨hadj, hUS haU, hWS hbW⟩))
          (induced_path_mono M hWS (hW'.2 b hbW z hzW))
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (all w hw)) (all y hy)

/-- All premises of the overlap classification (DH23 Lemma 4.11) hold for every designated vine-like object over
`𝒱_γ`. -/
theorem object_overlap_premises (O : Src.Object γ M) :
    Nonempty (Mole.BlockRealization M O.atoms O.upper O.lower) ∧
    Mole.InteriorDeletionProperty M O.atoms O.upper O.lower ∧
    (∀ x ∈ O.atoms \ {O.upper, O.lower}, ∀ y ∈ O.atoms \ {O.upper, O.lower},
      (Mole.induced M (O.atoms \ {O.upper, O.lower})).SameComponent x y) := by
  rcases O with ⟨S, a, b, shape⟩
  cases shape with
  | vc h =>
    obtain ⟨n, hc⟩ := h.2
    exact ⟨⟨Mole.BlockRealization.block h.1 ⟨⟨a, (chain_joints_mem hc).1⟩, chain_connected hc⟩⟩,
      sourceVC_interior_deletion hF1 h, chain_interior_connected hF1 hc⟩
  | hyper R =>
    obtain ⟨n, hc⟩ := R.adjoint.2
    refine ⟨⟨Mole.BlockRealization.hyper R.added R.ends_eq R.adjoint.1
      ⟨⟨a, (chain_joints_mem hc).1⟩, chain_connected hc⟩⟩,
      hyperAdjoint_interior_deletion hF1 R.ends_eq R.adjoint, ?_⟩
    intro x hx y hy
    exact Vine.eraseBond_induced_path M R.added _ (chain_interior_connected hF1 hc x hx y hy)

end F1

end WaveTurbulence.TVine.Struct.Drawn.VC
