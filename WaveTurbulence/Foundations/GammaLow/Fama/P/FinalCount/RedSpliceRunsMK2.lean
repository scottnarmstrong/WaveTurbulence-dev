/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceRunsMK2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects


/-!
# B2a MK-RUNS: runs and survivors of a marked group

o75 §2.5: the **runs** of a group `S` of `𝒞` are the maximal segments of consecutive unmarked `𝒱`-ingredients of its
chain; the **survivors** are the other ingredients (the marked ones and the one skipped by T1934).  In main's
vocabulary the chain is a `Spine γ N L S a b` (`N` the garden molecule for a VC, the adjoint `eraseBond` for an HVC),
a member `t` is unmarked-`𝒱` (`UnmMemMK`) when some `c ∈ vinesVG γ G \ Mk` has the atoms `t.1`.

* `exists_markedGroupUnits_of_spine`: the runs and survivors cut from any such spine with a survivor;
* `exists_markedGroupUnits`: **`Nonempty (MarkedGroupUnits γ G S Mk)` for every marked group** (`markedGroup γ G Mk S`),
  with all fields, including B1a's `chain` and B2a's `spine` and `surv_skip`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- A (CL) vine is determined by its atoms. -/
theorem clvine_eq_of_atomsMK {c c' : CLVineG γ G} (h : c.atoms = c'.atoms) : c = c' := by
  have hu : c.upper = c'.upper := clvine_upper_eq h
  have hX := c.isVine
  have hY := c'.isVine
  rw [h] at hX
  have hj := Vine.block_joints_unique G.molecule (Src.isBlock_of_isSomeVine hX) (Src.isBlock_of_isSomeVine hY)
  have hne : c'.upper ≠ c'.lower := (Src.isBlock_of_isSomeVine hY).2.2.2.1
  have hl : c.lower = c'.lower := by
    rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exact absurd (hu.symm.trans h1) hne
  cases c
  cases c'
  simp only at h hu hl
  subst h hu hl
  rfl

/-- A spine member is an unmarked vine of `𝒱` (an ingredient of a run). -/
def UnmMemMK (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (Mk : Set (CLVineG γ G))
    (t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) : Prop :=
  ∃ c : CLVineG γ G, c ∈ vinesVG γ G ∧ c ∉ Mk ∧ c.atoms = t.1

/-- An unmarked-`𝒱` member is not (CN). -/
theorem not_cnMem_of_unmMK {Mk : Set (CLVineG γ G)} {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (hv : Src.IsSomeVine γ G.molecule t.1 t.2.1 t.2.2) (hg : UnmMemMK γ G Mk t) : ¬ CNMem G t := by
  intro hcn
  obtain ⟨c, -, -, hc⟩ := hg
  have hX := c.isVine
  have hY := hv
  rw [hc] at hX
  have hj := Vine.block_joints_unique G.molecule (Src.isBlock_of_isSomeVine hX) (Src.isBlock_of_isSomeVine hY)
  have hp : Mole.InternalParent G c.atoms c.lower := c.parentLower
  rw [hc] at hp
  have hl : c.lower ∈ ({t.2.1, t.2.2} : Finset (GBranch G.tree)) := by rw [← hj]; simp
  rcases mem_insert.mp hl with h | h
  · exact hcn.1 (h ▸ hp)
  · exact hcn.2 ((mem_singleton.mp h) ▸ hp)



/-- The properties of one run used for the fields of `MarkedGroupUnits`. -/
def RunOKMK (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) (Mk : Set (CLVineG γ G)) (u : CLBlock G) : Prop :=
  u.atoms ⊆ S ∧
  (∃ L, Spine γ G.molecule L u.atoms u.upper u.lower ∧ ∀ t ∈ L, ∃ c : CLVineG γ G,
    c ∈ vinesVG γ G ∧ c ∉ Mk ∧ IsIngredientG γ G.molecule S c.atoms ∧ c.atoms = t.1) ∧
  ∃ j, (j = u.upper ∨ j = u.lower) ∧ HasExtPair G.molecule u.atoms j

section core
variable {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
  {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {S : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {Mk : Set (CLVineG γ G)}

/-- **One run.**  A non-empty segment `R` of unmarked-`𝒱` members of the spine, with a survivor (or the end of the
chain) on each side and a survivor on at least one side, is a (CL) block with the run properties. -/
theorem run_of_segMK (hN : N.IsMolecule) (hs : Spine γ N L S a b) (hB : N.IsBlock S a b)
    (hrun : ∀ X x y, X ⊆ S → ¬ (a ∈ X ∧ b ∈ X) → N.IsBlock X x y → G.molecule.IsBlock X x y)
    (hvineM : ∀ t ∈ L, Src.IsSomeVine γ G.molecule t.1 t.2.1 t.2.2)
    (hingr : ∀ t ∈ L, IsIngredientG γ G.molecule S t.1)
    {P R Q : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} (hL : L = P ++ R ++ Q)
    (hR : R ≠ []) (hRg : ∀ t ∈ R, UnmMemMK γ G Mk t)
    (hP : P = [] ∨ ∃ P0 s, P = P0 ++ [s]) (hQ : Q = [] ∨ ∃ s Q', Q = s :: Q') (hne : P ≠ [] ∨ Q ≠ []) :
    ∃ u : CLBlock G, RunOKMK γ G S Mk u ∧ ∀ v, v ∈ u.atoms ↔ ∃ t ∈ R, v ∈ t.1 := by
  classical
  have hRL : ∀ t ∈ R, t ∈ L := fun t ht => by rw [hL]; simp [ht]
  obtain ⟨UR, p, q, hsR, hBR, hsub, hPs, hQs⟩ := (hL ▸ hs).segMK hN hB hR
  have hnab : ¬ (a ∈ UR ∧ b ∈ UR) := by
    rintro ⟨ha, hb⟩
    rcases hne with hne | hne
    · obtain ⟨P0, s, rfl⟩ := hP.resolve_left hne
      exact (hPs P0 s rfl).2.2 ha
    · obtain ⟨s, Q', rfl⟩ := hQ.resolve_left hne
      exact (hQs s Q' rfl).2.2 hb
  have hBG : G.molecule.IsBlock UR p q := hrun UR p q hsub hnab hBR
  have hnon : ∀ t ∈ R, ¬ CNMem G t := fun t ht => not_cnMem_of_unmMK (hvineM t (hRL t ht)) (hRg t ht)
  obtain ⟨u, hu, hj⟩ := Spine.clBlock hsR hnon hBG
  have hsRG : Spine γ G.molecule R UR p q := hsR.monoMK fun t ht => hvineM t (hRL t ht)
  -- the members of `R` as unmarked `𝒱`-ingredients
  have hmemc : ∀ t ∈ R, ∃ c : CLVineG γ G, c ∈ vinesVG γ G ∧ c ∉ Mk ∧ IsIngredientG γ G.molecule S c.atoms ∧
      c.atoms = t.1 := by
    intro t ht
    obtain ⟨c, hcV, hcMk, hc⟩ := hRg t ht
    exact ⟨c, hcV, hcMk, hc ▸ hingr t (hRL t ht), hc⟩
  refine ⟨u, ⟨hu ▸ hsub, ?_, ?_⟩, fun v => hu ▸ hsR.mem_iff v⟩
  · rcases hj with ⟨hup, hlo⟩ | ⟨hup, hlo⟩
    · exact ⟨R, by rw [hu, hup, hlo]; exact hsRG, hmemc⟩
    · refine ⟨_, by rw [hu, hup, hlo]; exact hsRG.reverse, ?_⟩
      intro ⟨T, x, y⟩ ht
      exact hmemc (T, y, x) (mem_revSwap.mp ht)
  · rcases hne with hne | hne
    · obtain ⟨P0, s, hPs'⟩ := hP.resolve_left hne
      obtain ⟨h1, h2, -⟩ := hPs P0 s hPs'
      have hsL : s ∈ L := by rw [hL, hPs']; simp
      have hsB : G.molecule.IsBlock s.1 p s.2.1 :=
        Mole.block_swap_joints G.molecule (h1 ▸ Src.isBlock_of_isSomeVine (hvineM s hsL))
      refine ⟨p, ?_, hu ▸ hasExt_of_run hsB (by rw [inter_comm]; exact h2)⟩
      rcases hj with ⟨hup, _⟩ | ⟨_, hlo⟩
      · exact Or.inl hup.symm
      · exact Or.inr hlo.symm
    · obtain ⟨s, Q', hQs'⟩ := hQ.resolve_left hne
      obtain ⟨h1, h2, -⟩ := hQs s Q' hQs'
      have hsL : s ∈ L := by rw [hL, hQs']; simp
      have hsB : G.molecule.IsBlock s.1 q s.2.2 := h1 ▸ Src.isBlock_of_isSomeVine (hvineM s hsL)
      refine ⟨q, ?_, hu ▸ hasExt_of_run hsB h2⟩
      rcases hj with ⟨_, hlo⟩ | ⟨hup, _⟩
      · exact Or.inr hlo.symm
      · exact Or.inl hup.symm

/-- **All runs of a spine with a survivor.** -/
theorem runs_of_spineMK (hN : N.IsMolecule) (hs : Spine γ N L S a b) (hB : N.IsBlock S a b)
    (hrun : ∀ X x y, X ⊆ S → ¬ (a ∈ X ∧ b ∈ X) → N.IsBlock X x y → G.molecule.IsBlock X x y)
    (hvineM : ∀ t ∈ L, Src.IsSomeVine γ G.molecule t.1 t.2.1 t.2.2)
    (hingr : ∀ t ∈ L, IsIngredientG γ G.molecule S t.1) (hsurv : ∃ t ∈ L, ¬ UnmMemMK γ G Mk t) :
    ∃ runs : List (CLBlock G), (∀ u ∈ runs, RunOKMK γ G S Mk u ∧
      ∀ v ∈ u.atoms, ∃ t ∈ L, UnmMemMK γ G Mk t ∧ v ∈ t.1) ∧
      runs.Pairwise (fun u u' => Disjoint u.atoms u'.atoms) ∧
      ∀ t ∈ L, UnmMemMK γ G Mk t → ∃ u ∈ runs, t.1 ⊆ u.atoms := by
  classical
  -- strong induction on the remaining suffix `L'` of `L = Pre ++ L'`
  suffices key : ∀ n, ∀ Pre L' : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree),
      L'.length = n → Pre ++ L' = L → (Pre = [] ∨ ∃ P0 s, Pre = P0 ++ [s]) →
      ∃ runs : List (CLBlock G), (∀ u ∈ runs, RunOKMK γ G S Mk u ∧
        ∀ v ∈ u.atoms, ∃ t ∈ L', UnmMemMK γ G Mk t ∧ v ∈ t.1) ∧
        runs.Pairwise (fun u u' => Disjoint u.atoms u'.atoms) ∧
        ∀ t ∈ L', UnmMemMK γ G Mk t → ∃ u ∈ runs, t.1 ⊆ u.atoms by
    exact key _ [] L rfl rfl (Or.inl rfl)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Pre L' hlen hPL hPre
  set p : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree → Bool :=
    fun t => decide (UnmMemMK γ G Mk t) with hp
  set R := L'.takeWhile p with hRdef
  have hRg : ∀ t ∈ R, UnmMemMK γ G Mk t := fun t ht => by
    have := List.mem_takeWhile_imp ht
    simpa [hp] using this
  have hsplit : R ++ L'.dropWhile p = L' := List.takeWhile_append_dropWhile
  -- the run made of `R`, if non-empty, given what follows it
  have mkRun : R ≠ [] → ∀ Q, Q = [] ∨ (∃ s Q', Q = s :: Q') → Pre ++ R ++ Q = L → (Pre ≠ [] ∨ Q ≠ []) →
      ∃ u : CLBlock G, RunOKMK γ G S Mk u ∧ ∀ v, v ∈ u.atoms ↔ ∃ t ∈ R, v ∈ t.1 :=
    fun hR Q hQ hL hne => run_of_segMK hN hs hB hrun hvineM hingr hL.symm hR hRg hPre hQ hne
  have hRsub : ∀ t ∈ R, t ∈ L' := fun t ht => List.takeWhile_subset p ht
  rcases hdw : L'.dropWhile p with _ | ⟨s, L''⟩
  · -- no survivor after `R`
    rw [hdw, List.append_nil] at hsplit
    by_cases hR : R = []
    · refine ⟨[], by simp, List.Pairwise.nil, fun t ht hg => ?_⟩
      rw [← hsplit, hR] at ht
      simp at ht
    · have hPne : Pre ≠ [] := by
        rintro rfl
        obtain ⟨t, ht, hg⟩ := hsurv
        rw [← hPL, List.nil_append, ← hsplit] at ht
        exact hg (hRg t ht)
      obtain ⟨u, hu, hua⟩ := mkRun hR [] (Or.inl rfl) (by rw [List.append_nil, hsplit]; exact hPL)
        (Or.inl hPne)
      refine ⟨[u], ?_, List.pairwise_singleton _ _, ?_⟩
      · intro u' hu'
        rw [List.mem_singleton] at hu'
        subst hu'
        refine ⟨hu, fun v hv => ?_⟩
        obtain ⟨t, ht, hvt⟩ := (hua v).mp hv
        exact ⟨t, hRsub t ht, hRg t ht, hvt⟩
      · intro t ht _
        rw [← hsplit] at ht
        exact ⟨u, List.mem_singleton_self _, fun v hv => (hua v).mpr ⟨t, ht, hv⟩⟩
  · -- a survivor `s` after `R`
    have hs_ng : ¬ UnmMemMK γ G Mk s := by
      have := dropWhile_head_falseMK p L' hdw
      simpa [hp] using this
    rw [hdw] at hsplit
    have hlen' : L''.length < n := by
      rw [← hlen, ← hsplit]
      simp only [List.length_append, List.length_cons]
      omega
    have hPL' : (Pre ++ R ++ [s]) ++ L'' = L := by rw [← hPL, ← hsplit]; simp
    obtain ⟨runs, hruns, hdisj, hcov⟩ := ih _ hlen' (Pre ++ R ++ [s]) L'' rfl hPL' (Or.inr ⟨_, s, rfl⟩)
    have hL''sub : ∀ t ∈ L'', t ∈ L' := fun t ht => by rw [← hsplit]; simp [ht]
    -- the atoms of `R` are disjoint from those of `L''`
    have hsep : ∀ t ∈ R, ∀ t' ∈ L'', Disjoint t.1 t'.1 := by
      intro t ht t' ht'
      have hs' : Spine γ N ((Pre ++ R) ++ s :: L'') S a b := by
        rw [← hPL'] at hs; simpa using hs
      exact hs'.sepMK (List.mem_append_right _ ht) ht'
    by_cases hR : R = []
    · refine ⟨runs, ?_, hdisj, ?_⟩
      · intro u hu
        refine ⟨(hruns u hu).1, fun v hv => ?_⟩
        obtain ⟨t, ht, hg, hvt⟩ := (hruns u hu).2 v hv
        exact ⟨t, hL''sub t ht, hg, hvt⟩
      · intro t ht hg
        rw [← hsplit, hR, List.nil_append] at ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact absurd hg hs_ng
        · exact hcov t ht hg
    · obtain ⟨u, hu, hua⟩ := mkRun hR (s :: L'') (Or.inr ⟨s, L'', rfl⟩) (by rw [← hPL, ← hsplit]; simp)
        (Or.inr (by simp))
      refine ⟨u :: runs, ?_, ?_, ?_⟩
      · intro u' hu'
        rcases List.mem_cons.mp hu' with rfl | hu'
        · refine ⟨hu, fun v hv => ?_⟩
          obtain ⟨t, ht, hvt⟩ := (hua v).mp hv
          exact ⟨t, hRsub t ht, hRg t ht, hvt⟩
        · refine ⟨(hruns u' hu').1, fun v hv => ?_⟩
          obtain ⟨t, ht, hg, hvt⟩ := (hruns u' hu').2 v hv
          exact ⟨t, hL''sub t ht, hg, hvt⟩
      · refine List.Pairwise.cons (fun u' hu' => ?_) hdisj
        rw [Finset.disjoint_left]
        intro v hv hv'
        obtain ⟨t, ht, hvt⟩ := (hua v).mp hv
        obtain ⟨t', ht', -, hvt'⟩ := (hruns u' hu').2 v hv'
        exact Finset.disjoint_left.mp (hsep t ht t' ht') hvt hvt'
      · intro t ht hg
        rw [← hsplit] at ht
        rcases List.mem_append.mp ht with ht | ht
        · exact ⟨u, List.mem_cons_self .., fun v hv => (hua v).mpr ⟨t, ht, hv⟩⟩
        · rcases List.mem_cons.mp ht with rfl | ht
          · exact absurd hg hs_ng
          · obtain ⟨u', hu', h'⟩ := hcov t ht hg
            exact ⟨u', List.mem_cons_of_mem _ hu', h'⟩

end core

end WaveTurbulence.GammaLow.Fama
