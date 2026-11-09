/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceUnits2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceUnits2


/-!
# REDSPLICE-DEF (S2a), A4: existence of the units of every group

`exists_groupUnits`: for `S ∈ maximalGroupsG γ G.molecule` there is a `GroupUnits γ G S`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)]

section cut
variable {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
  {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {S : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {A : Finset (GBranch G.tree)} {x y : GBranch G.tree}

theorem RunCut.mem_LL_ne (rc : RunCut γ G N L S a b A x y) (hxy : x ∈ A ∧ y ∈ A ∧ x ≠ y)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ rc.LL) : t ≠ (A, x, y) := by
  intro h
  subst h
  have hAne : ∀ {Z : Finset (GBranch G.tree)} {z : GBranch G.tree}, A ⊆ Z → Z ∩ A = {z} → False := by
    intro Z z hAZ hZA
    have h1 : x ∈ Z ∩ A := mem_inter.mpr ⟨hAZ hxy.1, hxy.1⟩
    have h2 : y ∈ Z ∩ A := mem_inter.mpr ⟨hAZ hxy.2.1, hxy.2.1⟩
    rw [hZA, mem_singleton] at h1 h2
    exact hxy.2.2 (h1.trans h2.symm)
  rcases rc.left with ⟨h0, _⟩ | ⟨_, _, hLL, hLA⟩
  · rw [h0] at ht; simp at ht
  · exact hAne (hLL.mem_vine (T := A) (p := x) (q := y) ht).2 hLA

theorem RunCut.mem_RR_ne (rc : RunCut γ G N L S a b A x y) (hxy : x ∈ A ∧ y ∈ A ∧ x ≠ y)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ rc.RR) : t ≠ (A, x, y) := by
  intro h
  subst h
  have hAne : ∀ {Z : Finset (GBranch G.tree)} {z : GBranch G.tree}, A ⊆ Z → Z ∩ A = {z} → False := by
    intro Z z hAZ hZA
    have h1 : x ∈ Z ∩ A := mem_inter.mpr ⟨hAZ hxy.1, hxy.1⟩
    have h2 : y ∈ Z ∩ A := mem_inter.mpr ⟨hAZ hxy.2.1, hxy.2.1⟩
    rw [hZA, mem_singleton] at h1 h2
    exact hxy.2.2 (h1.trans h2.symm)
  rcases rc.right with ⟨h0, _⟩ | ⟨_, _, hRR, hRA⟩
  · rw [h0] at ht; simp at ht
  · exact hAne (hRR.mem_vine (T := A) (p := x) (q := y) ht).2 hRA

theorem RunCut.skel (rc : RunCut γ G N L S a b A x y) (hN : N.IsMolecule) (hSB : N.IsBlock S a b)
    (hA : N.IsBlock A x y) : SkelDecomp N S A rc.L0 rc.R0 a b x y := by
  refine ⟨hN, rc.hS, hSB, hA, ?_, ?_, rc.disj⟩
  · rcases rc.left with ⟨_, h⟩ | ⟨h1, h2, _, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h4⟩
  · rcases rc.right with ⟨_, h⟩ | ⟨h1, h2, _, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h4⟩

/-- The units of a group cut around a skipped ingredient. -/
theorem groupUnits_of_cut (hnhv : (∃ a b, Src.IsHV γ G.molecule S a b) → ∃ a b, Src.IsHVC γ G.molecule S a b)
    (rc : RunCut γ G N L S a b A x y) (hAv : Src.IsSomeVine γ G.molecule A x y)
    (hing : IsIngredientG γ G.molecule S A)
    (bond : Option (GardenDart G))
    (hkind : CNMem G (A, x, y) ∨ ((bond = none → IsRootVCG γ G S) ∧ ∃ c : CLVineG γ G, c.atoms = A ∧ IsTopIngredientG S c)) (hNm : N.IsMolecule) (hSB : N.IsBlock S a b) (hAB : N.IsBlock A x y)
    (hvN : ∀ e, bond = some e → Src.IsSomeVine γ (eraseBond G.molecule e) A x y)
    (hskM : bond = none → SkelDecomp G.molecule S A rc.L0 rc.R0 a b x y)
    (hskN : ∀ e, bond = some e → SkelDecomp (eraseBond G.molecule e) S A rc.L0 rc.R0 a b x y)
    (hbM : bond = none → G.molecule.IsBlock S a b)
    (hbN : ∀ e, bond = some e → G.molecule.ends e = s(a, b) ∧ (eraseBond G.molecule e).IsBlock S a b)
    (hV : ∀ t ∈ L, t ≠ (A, x, y) → ∃ c ∈ vinesVG γ G, c.atoms = t.1 ∧ IsIngredientG γ G.molecule S t.1)
    (hcover : G.molecule.IsMolecule → S ∈ maximalGroupsG γ G.molecule → ∀ c : CLVineG γ G, c ∈ vinesVG γ G →
      IsIngredientG γ G.molecule S c.atoms → c.atoms ≠ A ∧ ∃ p q, (c.atoms, p, q) ∈ L)
    (hchM : bond = none → ∃ n, ChainIngredientG γ G.molecule S a b n A x y)
    (hchN : ∀ e, bond = some e → ∃ n, 2 ≤ n ∧ ChainIngredientG γ (eraseBond G.molecule e) S a b n A x y) :
    Nonempty (GroupUnits γ G S) := by
  classical
  have hxy := isSomeVine_ends hAv
  have hLsub : rc.L0 ⊆ S := by
    intro v hv
    have : v ∈ rc.L0 ∪ A ∪ rc.R0 := mem_union_left _ (mem_union_left _ hv)
    rwa [← rc.hS] at this
  have hRsub : rc.R0 ⊆ S := by
    intro v hv
    have : v ∈ rc.L0 ∪ A ∪ rc.R0 := mem_union_right _ hv
    rwa [← rc.hS] at this
  -- the two runs
  have hLu : ∃ ul : List (CLBlock G), (∀ u ∈ ul, u.atoms = rc.L0 ∧ rc.L0 ≠ ∅ ∧
      (u.upper = a ∧ u.lower = x ∨ u.upper = x ∧ u.lower = a)) ∧ ul.length ≤ 1 ∧
      (rc.L0 ≠ ∅ → ∃ u ∈ ul, u.atoms = rc.L0) := by
    by_cases h : rc.L0 = ∅
    · exact ⟨[], by simp, by simp, fun h' => absurd h h'⟩
    · obtain ⟨u, hu, hj⟩ := rc.leftBlock.resolve_left h
      exact ⟨[u], by simpa [h] using ⟨hu, hj⟩, by simp, fun _ => ⟨u, by simp, hu⟩⟩
  have hRu : ∃ ur : List (CLBlock G), (∀ u ∈ ur, u.atoms = rc.R0 ∧ rc.R0 ≠ ∅ ∧
      (u.upper = y ∧ u.lower = b ∨ u.upper = b ∧ u.lower = y)) ∧ ur.length ≤ 1 ∧
      (rc.R0 ≠ ∅ → ∃ u ∈ ur, u.atoms = rc.R0) := by
    by_cases h : rc.R0 = ∅
    · exact ⟨[], by simp, by simp, fun h' => absurd h h'⟩
    · obtain ⟨u, hu, hj⟩ := rc.rightBlock.resolve_left h
      exact ⟨[u], by simpa [h] using ⟨hu, hj⟩, by simp, fun _ => ⟨u, by simp, hu⟩⟩
  obtain ⟨ul, hul, hul1, hul2⟩ := hLu
  obtain ⟨ur, hur, hur1, hur2⟩ := hRu
  -- soundness of the left run
  have hsoundL : rc.L0 ≠ ∅ → ∃ cs : List (Finset (GBranch G.tree)),
      (∀ c ∈ cs, ∃ c' ∈ vinesVG γ G, c'.atoms = c ∧ IsIngredientG γ G.molecule S c) ∧ ∀ v, v ∈ rc.L0 ↔ ∃ c ∈ cs, v ∈ c := by
    intro hne
    rcases rc.left with ⟨_, h0, _⟩ | ⟨_, _, hLL, _⟩
    · exact absurd h0 hne
    · obtain ⟨cs, hcs, hv⟩ := choose_vines (P := fun T => ∃ c' ∈ vinesVG γ G, c'.atoms = T ∧ IsIngredientG γ G.molecule S T) rc.LL (by
        intro t ht
        obtain ⟨c, hc, hc1, hc2⟩ := hV t (by rw [rc.hL]; exact List.mem_append_left _ ht) (rc.mem_LL_ne hxy ht)
        exact ⟨t.1, ⟨c, hc, hc1, hc2⟩, rfl⟩)
      exact ⟨cs, hcs, fun v => (hLL.mem_iff v).trans (hv v)⟩
  have hsoundR : rc.R0 ≠ ∅ → ∃ cs : List (Finset (GBranch G.tree)),
      (∀ c ∈ cs, ∃ c' ∈ vinesVG γ G, c'.atoms = c ∧ IsIngredientG γ G.molecule S c) ∧ ∀ v, v ∈ rc.R0 ↔ ∃ c ∈ cs, v ∈ c := by
    intro hne
    rcases rc.right with ⟨_, h0, _⟩ | ⟨_, _, hRR, _⟩
    · exact absurd h0 hne
    · obtain ⟨cs, hcs, hv⟩ := choose_vines (P := fun T => ∃ c' ∈ vinesVG γ G, c'.atoms = T ∧ IsIngredientG γ G.molecule S T) rc.RR (by
        intro t ht
        obtain ⟨c, hc, hc1, hc2⟩ := hV t (by rw [rc.hL]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ht))
          (rc.mem_RR_ne hxy ht)
        exact ⟨t.1, ⟨c, hc, hc1, hc2⟩, rfl⟩)
      exact ⟨cs, hcs, fun v => (hRR.mem_iff v).trans (hv v)⟩
  refine ⟨{
    units := ul ++ ur
    sub := ?_
    disj := ?_
    sound := ?_
    skip := some {
      A := A, x := x, y := y, a := a, b := b, L0 := rc.L0, R0 := rc.R0, vine := hAv, ingredient := hing
      hS := rc.hS, disj := rc.disj
      left := ?_
      right := ?_
      kind := hkind, bond := bond, blockM := hbM, blockN := hbN, vineN := hvN, skelM := hskM, skelN := hskN,
      chainM := hchM, chainN := hchN }
    skip_units := ?_
    noskip_units := by intro h; cases h
    whole_vc := by intro h; cases h
    ext := ?_
    cover := ?_
    vl := fun _ _ _ => Or.inr ⟨_, rfl⟩
    hv_empty := fun h h2 => absurd (hnhv h) h2 }⟩
  · intro u hu
    rcases List.mem_append.mp hu with h | h
    · rw [(hul u h).1]; exact hLsub
    · rw [(hur u h).1]; exact hRsub
  · rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · -- at most one element on the left
      match ul, hul1 with
      | [], _ => exact List.Pairwise.nil
      | [_], _ => exact List.pairwise_singleton _ _
    · match ur, hur1 with
      | [], _ => exact List.Pairwise.nil
      | [_], _ => exact List.pairwise_singleton _ _
    · intro u hu u' hu'
      rw [(hul u hu).1, (hur u' hu').1]
      exact rc.disj
  · intro u hu
    rcases List.mem_append.mp hu with h | h
    · rw [(hul u h).1]; exact hsoundL (hul u h).2.1
    · rw [(hur u h).1]; exact hsoundR (hur u h).2.1
  · rcases rc.left with h | ⟨h1, _, hLL, h3⟩
    · exact Or.inl h.2
    · exact Or.inr ⟨h1, hLL.ends.1, hLL.ends.2.1, h3⟩
  · rcases rc.right with h | ⟨h1, _, hRR, h3⟩
    · exact Or.inl h.2
    · exact Or.inr ⟨h1, hRR.ends.2.1, hRR.ends.1, h3⟩
  · intro sk hsk
    cases hsk
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact Or.inl ⟨(hul u h).1, (hul u h).2.2⟩
      · exact Or.inr ⟨(hur u h).1, (hur u h).2.2⟩
    · by_cases h : rc.L0 = ∅
      · exact Or.inl h
      · obtain ⟨u, hu, hu'⟩ := hul2 h
        exact Or.inr ⟨u, List.mem_append_left _ hu, hu'⟩
    · by_cases h : rc.R0 = ∅
      · exact Or.inl h
      · obtain ⟨u, hu, hu'⟩ := hur2 h
        exact Or.inr ⟨u, List.mem_append_right _ hu, hu'⟩
  · -- the external dart pairs of the units
    have hLext : rc.L0 ≠ ∅ → HasExtPair G.molecule rc.L0 x := by
      intro hne
      rcases hbond : bond with _ | e
      · have H := hskM hbond
        rcases H.hL with ⟨h0, _⟩ | ⟨_, _, hLA⟩
        · exact absurd h0 hne
        · exact hasExt_of_run H.hA hLA
      · have H := hskN e hbond
        rcases H.hL with ⟨h0, _⟩ | ⟨_, _, hLA⟩
        · exact absurd h0 hne
        · exact hasExt_of_run_erase e H.hA hLA
    have hRext : rc.R0 ≠ ∅ → HasExtPair G.molecule rc.R0 y := by
      intro hne
      rcases hbond : bond with _ | e
      · have H := hskM hbond
        rcases H.hR with ⟨h0, _⟩ | ⟨_, _, hRA⟩
        · exact absurd h0 hne
        · exact hasExt_of_run (block_swap_joints _ H.hA) hRA
      · have H := hskN e hbond
        rcases H.hR with ⟨h0, _⟩ | ⟨_, _, hRA⟩
        · exact absurd h0 hne
        · exact hasExt_of_run_erase e (block_swap_joints _ H.hA) hRA
    intro u hu
    rcases List.mem_append.mp hu with h | h
    · obtain ⟨h1, h2, h3⟩ := hul u h
      refine ⟨x, ?_, h1 ▸ hLext h2⟩
      rcases h3 with ⟨_, h⟩ | ⟨h, _⟩
      · exact Or.inr h.symm
      · exact Or.inl h.symm
    · obtain ⟨h1, h2, h3⟩ := hur u h
      refine ⟨y, ?_, h1 ▸ hRext h2⟩
      rcases h3 with ⟨h, _⟩ | ⟨_, h⟩
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  · intro hM' hS' c hc hci
    obtain ⟨hne, p, q, hm⟩ := hcover hM' hS' c hc hci
    obtain ⟨z, hz⟩ := ingredient_nonempty hci
    rcases member_in_run rc hm hne with h | h
    · have hL0 : rc.L0 ≠ ∅ := by
        intro h0
        have := h hz
        rw [h0] at this
        exact absurd this (by simp)
      obtain ⟨u, hu, hu'⟩ := hul2 hL0
      exact ⟨u, List.mem_append_left _ hu, hu' ▸ h⟩
    · have hR0 : rc.R0 ≠ ∅ := by
        intro h0
        have := h hz
        rw [h0] at this
        exact absurd this (by simp)
      obtain ⟨u, hu, hu'⟩ := hur2 hR0
      exact ⟨u, List.mem_append_right _ hu, hu' ▸ h⟩

end cut

theorem groupUnits_empty_nongroup (S : Finset (GBranch G.tree))
    (h : ¬ (G.molecule.IsMolecule ∧ S ∈ maximalGroupsG γ G.molecule)) : Nonempty (GroupUnits γ G S) :=
  ⟨{ units := [], sub := by simp, disj := List.Pairwise.nil, sound := by simp, skip := none
     skip_units := by intro sk h; cases h
     noskip_units := by simp
     whole_vc := fun _ h => absurd rfl h
     ext := by simp
     hv_empty := fun _ _ => rfl
     cover := fun hM hS => absurd ⟨hM, hS⟩ h
     vl := fun hM hS => absurd ⟨hM, hS⟩ h }⟩

/-- A group that is neither a VC nor an HVC has no vine of `𝒱` among its ingredients. -/
theorem groupUnits_other (hM : G.molecule.IsMolecule) {S : Finset (GBranch G.tree)}
    (hSmax : S ∈ maximalGroupsG γ G.molecule) (hnvc : ¬ ∃ a b, Src.IsVC γ G.molecule S a b)
    (hnhvc : ¬ ∃ a b, Src.IsHVC γ G.molecule S a b) : Nonempty (GroupUnits γ G S) :=
  ⟨{ units := [], sub := by simp, disj := List.Pairwise.nil, sound := by simp, skip := none
     skip_units := by intro sk h; cases h
     noskip_units := by simp
     whole_vc := fun _ h => absurd rfl h
     ext := by simp
     hv_empty := fun _ _ => rfl
     vl := by
       intro _ _ ⟨a', b', h⟩
       rcases h with h | h
       · exact absurd ⟨a', b', h⟩ hnvc
       · exact absurd ⟨a', b', h⟩ hnhvc
     cover := by
       intro hM' hS' c hc hci
       exfalso
       obtain ⟨S1, hS1, hi1, hcond⟩ := hc
       have hSS : S1 = S := group_eq_of_ingredient hM hS1 hSmax hi1 hci
       subst hSS
       rcases hcond with ⟨a', b', hvc, _⟩ | ⟨hh | hroot, _⟩
       · exact hnvc ⟨a', b', hvc⟩
       · exact hnhvc hh
       · obtain ⟨a', b', hvc, _⟩ := hroot
         exact hnvc ⟨a', b', hvc⟩ }⟩

theorem groupUnits_whole (hM : G.molecule.IsMolecule) {S : Finset (GBranch G.tree)}
    (hnhv : (∃ a b, Src.IsHV γ G.molecule S a b) → ∃ a b, Src.IsHVC γ G.molecule S a b)
    (u : CLBlock G) (hu : u.atoms = S)
    (hdeg : 7 ≤ G.molecule.deg u.upper + G.molecule.deg u.lower)
    (hsound : ∃ cs : List (Finset (GBranch G.tree)),
      (∀ c ∈ cs, ∃ c' ∈ vinesVG γ G, c'.atoms = c ∧ IsIngredientG γ G.molecule S c) ∧ ∀ v, v ∈ S ↔ ∃ c ∈ cs, v ∈ c)
    (hvc : ∃ a b, Src.IsVC γ G.molecule S a b) :
    Nonempty (GroupUnits γ G S) :=
  ⟨{ units := [u], sub := by simp [hu], disj := List.pairwise_singleton _ _
     sound := by
       intro u' hu'
       rw [List.mem_singleton.mp hu', hu]
       exact hsound
     skip := none
     skip_units := by intro sk h; cases h
     noskip_units := by intro _ u' hu'; rw [List.mem_singleton.mp hu']; exact hu
     whole_vc := fun _ _ => hvc
     ext := by
       intro u' hu'
       rw [List.mem_singleton.mp hu']
       have hu1 := deg_le_four G.molecule hM (u.isBlock.1 u.isBlock.2.1)
       have hu2 := deg_le_four G.molecule hM (u.isBlock.1 u.isBlock.2.2.1)
       by_cases h4 : G.molecule.deg u.upper = 4
       · exact ⟨u.upper, Or.inl rfl, ext_pair_deg4 hM u.isBlock h4⟩
       · exact ⟨u.lower, Or.inr rfl, ext_pair_deg4 hM (block_swap_joints _ u.isBlock) (by omega)⟩
     cover := fun _ _ c _ hci => ⟨u, List.mem_singleton_self _, hu ▸ ingredient_sub hci⟩
     vl := fun _ _ _ => Or.inl (by simp)
     hv_empty := fun h h2 => absurd (hnhv h) h2 }⟩

/-- **Every group of `𝒞` has its splice units** (A4), with the cover property.  The case split is VC, then HVC,
then the rest (HV, DV: no units, and no vine of `𝒱` among their ingredients). -/
theorem exists_groupUnits (hM : G.molecule.IsMolecule) {S : Finset (GBranch G.tree)}
    (hSmax : S ∈ maximalGroupsG γ G.molecule) : Nonempty (GroupUnits γ G S) := by
  by_cases hvc : ∃ a b, Src.IsVC γ G.molecule S a b
  · -- a VC
    obtain ⟨a, b, h⟩ := hvc
    have hnhv : (∃ a b, Src.IsHV γ G.molecule S a b) → ∃ a b, Src.IsHVC γ G.molecule S a b := by
      rintro ⟨a', b', e, he, hX⟩
      exact (vc_not_hyper h.1 ⟨e, he, (Src.isBlock_of_isSomeVine hX)⟩).elim
    obtain ⟨L, hs, hspec⟩ := vc_group hM hSmax h
    rcases hspec with ⟨hnon, ⟨u, hu, _, hdeg⟩, hV⟩ | ⟨A, x, y, hmem, hAv, hing, hBM, ⟨rc⟩, hV, hkind⟩
    · refine groupUnits_whole hM hnhv u hu hdeg ?_ ⟨a, b, h⟩
      obtain ⟨cs, hcs, hv⟩ := choose_vines (P := fun T => ∃ c' ∈ vinesVG γ G, c'.atoms = T ∧ IsIngredientG γ G.molecule S T) L (by
        intro t ht
        obtain ⟨c, hc, hc1⟩ := hV t ht
        exact ⟨t.1, ⟨c, hc, hc1⟩, rfl⟩)
      exact ⟨cs, hcs, fun v => (hs.mem_iff v).trans (hv v)⟩
    · have hmemb : ∀ T, IsIngredientG γ G.molecule S T → ∃ p q, (T, p, q) ∈ L := by
        intro T hT
        obtain ⟨p, q, h' | h'⟩ := isIngredient_vc hM h.1 hs hT
        · exact ⟨p, q, h'⟩
        · exact ⟨q, p, h'⟩
      refine groupUnits_of_cut hnhv rc hAv hing none ?_ hM hBM (Src.isBlock_of_isSomeVine hAv) (fun e he => by cases he) (fun _ => rc.skel hM hBM (Src.isBlock_of_isSomeVine hAv)) (fun e he => by cases he) (fun _ => hBM) (fun e he => by cases he) hV ?_
        (fun _ => ⟨L.length, hs.ingredient_of_mem hmem⟩) (fun e he => by cases he)
      · rcases hkind with h1 | ⟨hroot, _, c, hc1, hc2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨fun _ => hroot, c, hc1, hc2⟩
      · intro hM' hS' c hc hci
        refine ⟨?_, hmemb _ hci⟩
        refine atoms_ne_A hM' hS' hmemb (fun T p q hm => (hs.mem_vine hm).1) hAv ?_ hc hci
        rcases hkind with h1 | ⟨hroot, hnon, c0, hc1, hc2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨hnon, Or.inl hroot, c0, hc1, hc2⟩
  by_cases hhvc : ∃ a b, Src.IsHVC γ G.molecule S a b
  · -- an HVC
    obtain ⟨a, b, h⟩ := hhvc
    obtain ⟨e, L, hs, hlen, hspec⟩ := hvc_group hM hSmax h
    rcases hspec with ⟨A, x, y, hmem, hAv, hing, hBN, ⟨rc⟩, hV, hkind⟩ | hdeg
    · have hmemb : ∀ T, IsIngredientG γ G.molecule S T → ∃ p q, (T, p, q) ∈ L := by
        intro T hT
        obtain ⟨p, q, h' | h'⟩ := isIngredient_hvc hM hBN.1 hBN.2.1 hs hlen hT
        · exact ⟨p, q, h'⟩
        · exact ⟨q, p, h'⟩
      refine groupUnits_of_cut (fun _ => ⟨a, b, h⟩) rc hAv hing (some e) ?_ hBN.2.2.1 hBN.2.1 (Src.isBlock_of_isSomeVine hBN.2.2.2) (fun e' he' => by cases he'; exact hBN.2.2.2) (fun h => by cases h) (fun e' he' => by cases he'; exact rc.skel hBN.2.2.1 hBN.2.1 (Src.isBlock_of_isSomeVine hBN.2.2.2)) (fun h => by cases h) (fun e' he' => by cases he'; exact ⟨hBN.1, hBN.2.1⟩) hV ?_
        (fun h => by cases h) (fun e' he' => by cases he'; exact ⟨L.length, hlen, hs.ingredient_of_mem hmem⟩)
      · rcases hkind with h1 | ⟨_, c, hc1, hc2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨(fun h => by cases h), c, hc1, hc2⟩
      · intro hM' hS' c hc hci
        refine ⟨?_, hmemb _ hci⟩
        refine atoms_ne_A hM' hS' hmemb (fun T p q hm =>
          (vine_transfer G.molecule hBN.1 (hs.not_both hlen hm) p q).mp (hs.mem_vine hm).1) hAv ?_ hc hci
        rcases hkind with h1 | ⟨hnon, c0, hc1, hc2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨hnon, Or.inr ⟨a, b, h⟩, c0, hc1, hc2⟩
    · exfalso
      obtain ⟨hends, hBe, hnon, hnotop⟩ := hdeg
      obtain ⟨t, ht, c, hc, htop⟩ := hvc_top_exists hM hends hBe hs hlen hnon
      exact hnotop t ht c hc htop
  · exact groupUnits_other hM hSmax hvc hhvc

end WaveTurbulence.GammaLow.Fama
