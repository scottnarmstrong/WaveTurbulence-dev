/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL15
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain2`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, LC-1 (2): the state after Step D1.**  Atoms, classes, `β`-count, `α`-product, number of components,
critical count and the index of `vineStG s K` (the isolated halves of the degree-`2` joints deleted). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section vsg
variable (s : St.{u} V D₀) (K : Step1.VineCut Src.γL s.M)

theorem vineStG_atoms : (vineStG s K).M.atoms = (insert K.fb (insert K.fa s.M.atoms)).filter (VineKeep K) := rfl

theorem vineStG_cls (a : V) : (vineStG s K).cls a = Function.update (Function.update (Function.update (Function.update s.cls K.C.upper .beta)
    K.fa (jcls s.M K.C.upper)) K.C.lower .beta) K.fb (jcls s.M K.C.lower) a := rfl

theorem vineStG_cls_old {a : V} (haC : a ∉ K.C.atoms) (ha : a ∈ s.M.atoms) : (vineStG s K).cls a = s.cls a := by
  rw [vineStG_cls]
  have h1 : a ≠ K.fb := fun e => K.fb_fresh (e ▸ ha)
  have h2 : a ≠ K.fa := fun e => K.fa_fresh (e ▸ ha)
  have h3 : a ≠ K.C.upper := fun e => haC (e ▸ K.a_mem)
  have h4 : a ≠ K.C.lower := fun e => haC (e ▸ K.b_mem)
  simp [Function.update_of_ne, h1, h2, h3, h4]

theorem vineStG_cls_fa : (vineStG s K).cls K.fa = jcls s.M K.C.upper := by
  rw [vineStG_cls]
  have h1 : K.fa ≠ K.C.lower := fun e => K.fa_fresh (e ▸ Step1.objectAtoms_sub K.C K.b_mem)
  simp [Function.update_of_ne, K.fa_ne_fb, h1]

theorem vineStG_cls_fb : (vineStG s K).cls K.fb = jcls s.M K.C.lower := by
  rw [vineStG_cls, Function.update_self]

/-- Products over the atoms of the post state: the surviving halves contribute `F β` each, the removed object contributes `1`. -/
theorem prod_vineStG {α : Type*} [CommMonoid α] (F : Cls → α) (hrem : ∀ a ∈ K.C.atoms, F (s.cls a) = 1)
    (hg : F .ghost = 1) (hb : F .beta = F .beta) :
    ∏ a ∈ (vineStG s K).M.atoms, F ((vineStG s K).cls a) =
      (if s.M.deg K.C.lower = 2 then 1 else F .beta) * (if s.M.deg K.C.upper = 2 then 1 else F .beta) *
        ∏ a ∈ s.M.atoms, F (s.cls a) := by
  have hfa : K.fa ∉ s.M.atoms := K.fa_fresh
  have hfb : K.fb ∉ insert K.fa s.M.atoms := by
    intro h
    rcases Finset.mem_insert.1 h with e | h
    · exact K.fa_ne_fb e.symm
    · exact K.fb_fresh h
  rw [vineStG_atoms, Finset.prod_filter, Finset.prod_insert hfb, Finset.prod_insert hfa]
  have e1 : ∏ a ∈ s.M.atoms, (if VineKeep K a then F ((vineStG s K).cls a) else 1) = ∏ a ∈ s.M.atoms, F (s.cls a) := by
    refine Finset.prod_congr rfl fun a ha => ?_
    by_cases haC : a ∈ K.C.atoms
    · have : ¬ VineKeep K a := fun hk => hk.1 haC
      rw [if_neg this, hrem a haC]
    · have hk : VineKeep K a := by
        refine ⟨haC, ?_, ?_⟩
        · rintro ⟨e, -⟩; exact K.fa_fresh (e ▸ ha)
        · rintro ⟨e, -⟩; exact K.fb_fresh (e ▸ ha)
      rw [if_pos hk, vineStG_cls_old s K haC ha]
  rw [e1]
  have hfaK : (if VineKeep K K.fa then F ((vineStG s K).cls K.fa) else 1) = if s.M.deg K.C.upper = 2 then 1 else F .beta := by
    by_cases hd : s.M.deg K.C.upper = 2
    · have : ¬ VineKeep K K.fa := fun hk => hk.2.1 ⟨rfl, hd⟩
      rw [if_neg this, if_pos hd]
    · have hk : VineKeep K K.fa := ⟨fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h), fun ⟨_, h⟩ => hd h,
        fun ⟨e, _⟩ => K.fa_ne_fb e⟩
      rw [if_pos hk, if_neg hd, vineStG_cls_fa]; unfold jcls; rw [if_neg hd]
  have hfbK : (if VineKeep K K.fb then F ((vineStG s K).cls K.fb) else 1) = if s.M.deg K.C.lower = 2 then 1 else F .beta := by
    by_cases hd : s.M.deg K.C.lower = 2
    · have : ¬ VineKeep K K.fb := fun hk => hk.2.2 ⟨rfl, hd⟩
      rw [if_neg this, if_pos hd]
    · have hk : VineKeep K K.fb := ⟨fun h => K.fb_fresh (Step1.objectAtoms_sub K.C h), fun ⟨e, _⟩ => K.fa_ne_fb e.symm,
        fun ⟨_, h⟩ => hd h⟩
      rw [if_pos hk, if_neg hd, vineStG_cls_fb]; unfold jcls; rw [if_neg hd]
  rw [hfaK, hfbK]
  exact (mul_assoc _ _ _).symm

theorem apProd_vineStG (L γ η : ℝ) (hrem : ∀ a ∈ K.C.atoms, s.cls a = .eps) :
    apProd L γ η (vineStG s K) = apProd L γ η s := by
  unfold apProd
  have := prod_vineStG s K (apFactor L γ η) (fun a ha => by rw [hrem a ha]; rfl) rfl rfl
  rw [this]
  have h1 : apFactor L γ η .beta = 1 := rfl
  simp [h1]

theorem vBeta_vineStG (hrem : ∀ a ∈ K.C.atoms, s.cls a = .eps) :
    vBeta (vineStG s K) + jdeg2 K = vBeta s + 2 := by
  have key := prod_vineStG (α := Multiplicative ℕ) s K (fun x => Multiplicative.ofAdd (if x = Cls.beta then 1 else 0))
    (fun a ha => by rw [hrem a ha]; simp) (by simp) rfl
  have hv : ∀ t : St.{u} V D₀, vBeta t = ∑ a ∈ t.M.atoms, (if t.cls a = Cls.beta then 1 else 0) := by
    intro t; unfold vBeta; rw [Finset.card_filter]
  rw [hv, hv]
  have := congrArg Multiplicative.toAdd key
  simp only [toAdd_prod, toAdd_mul, apply_ite Multiplicative.toAdd, toAdd_one, toAdd_ofAdd] at this
  rw [this]
  unfold jdeg2
  by_cases h1 : s.M.deg K.C.lower = 2 <;> by_cases h2 : s.M.deg K.C.upper = 2 <;> simp [h1, h2] <;> ring

theorem apPos_vineStG (hap : ApPos s) : ApPos (vineStG s K) := by
  intro a ha R' kp' hcl
  rw [vineStG_atoms, Finset.mem_filter] at ha
  obtain ⟨ha1, hk1, hk2, hk3⟩ := ha
  by_cases e1 : a = K.fb
  · rw [e1, vineStG_cls_fb] at hcl; unfold jcls at hcl; split_ifs at hcl
  · by_cases e2 : a = K.fa
    · rw [e2, vineStG_cls_fa] at hcl; unfold jcls at hcl; split_ifs at hcl
    · have haM : a ∈ s.M.atoms := by
        rcases Finset.mem_insert.1 ha1 with h | h
        · exact absurd h e1
        · rcases Finset.mem_insert.1 h with h | h
          · exact absurd h e2
          · exact h
      rw [vineStG_cls_old s K hk1 haM] at hcl
      exact hap a haM R' kp' hcl

/-- Critical count: the removed object loses at most its two joints (interior atoms are not critical). -/
theorem critCount_vineStG (crit : V → Prop) (hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a) :
    critCount crit s ≤ critCount crit (vineStG s K) + 2 := by
  unfold critCount
  set S := s.M.atoms.filter fun a => s.cls a = .eps ∧ crit a
  have hsub : S \ {K.C.upper, K.C.lower} ⊆
      (vineStG s K).M.atoms.filter fun a => (vineStG s K).cls a = .eps ∧ crit a := by
    intro a ha
    obtain ⟨haS, hat⟩ := Finset.mem_sdiff.1 ha
    obtain ⟨ham, hε, hcr⟩ := Finset.mem_filter.1 haS
    have hau : a ≠ K.C.upper := fun e => hat (by simp [e])
    have hal : a ≠ K.C.lower := fun e => hat (by simp [e])
    have haC : a ∉ K.C.atoms := fun h => hint a h hau hal hcr
    refine Finset.mem_filter.2 ⟨?_, ?_, hcr⟩
    · rw [vineStG_atoms, Finset.mem_filter]
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ham), haC, ?_, ?_⟩
      · rintro ⟨e, -⟩; exact K.fa_fresh (e ▸ ham)
      · rintro ⟨e, -⟩; exact K.fb_fresh (e ▸ ham)
    · rw [vineStG_cls_old s K haC ham]; exact hε
  have h1 := Finset.card_le_card hsub
  have h2 : ({K.C.upper, K.C.lower} : Finset V).card ≤ 2 := Finset.card_le_two
  have h3 := Finset.le_card_sdiff ({K.C.upper, K.C.lower} : Finset V) S
  omega

end vsg

section ncomp
variable {s : St.{u} V D₀} (K : Step1.VineCut Src.γL s.M)

theorem fa_mem_post : K.fa ∈ K.post.atoms := by
  rw [post_atoms_eq, Finset.mem_filter]
  exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h)⟩

theorem fb_mem_post : K.fb ∈ K.post.atoms := by
  rw [post_atoms_eq, Finset.mem_filter]
  exact ⟨Finset.mem_insert_self _ _, fun h => K.fb_fresh (Step1.objectAtoms_sub K.C h)⟩

/-- **The number of components after Step D1**: `K.post` minus the `jdeg2 K` isolated halves. -/
theorem numComponents_vineStG : (vineStG s K).M.numComponents + jdeg2 K = K.post.numComponents := by
  classical
  set P₂ : V → Prop := fun a => ¬ (a = K.fa ∧ s.M.deg K.C.upper = 2) ∧ ¬ (a = K.fb ∧ s.M.deg K.C.lower = 2) with hP₂d
  have hPe : ∀ a, VineKeep K a ↔ (a ∉ K.C.atoms) ∧ P₂ a := fun a => Iff.rfl
  have hVK : PClosed K.cutMol (VineKeep K) := VineKeep.closed K
  have hP₂ : PClosed K.post P₂ := pclosed_restrict_of hPe K.closed hVK
  have hno : ∀ x : PDart K.cutMol (fun a => a ∉ K.C.atoms), P₂ (K.post.atom x) := by
    intro x
    refine ⟨fun ⟨he, hd⟩ => ?_, fun ⟨he, hd⟩ => ?_⟩
    · have : x.1 ∈ K.cutMol.dartsAt K.fa := by rw [mem_dartsAt]; exact he
      rw [vineCut_fa_dartless K hd] at this; exact absurd this (Finset.notMem_empty _)
    · have : x.1 ∈ K.cutMol.dartsAt K.fb := by rw [mem_dartsAt]; exact he
      rw [vineCut_fb_dartless K hd] at this; exact absurd this (Finset.notMem_empty _)
  let I : DartIso (restrictP K.post P₂ hP₂) (vineStG s K).M :=
    restrictRestrictIso K.cutMol (fun a => a ∉ K.C.atoms) P₂ (VineKeep K) hPe K.closed hVK
  have h1 : (vineStG s K).M.numComponents = (restrictP K.post P₂ hP₂).numComponents := I.numComponents_eq
  have hadd := numComponents_restrictP_add K.post P₂ hP₂
  have : IsEmpty (PDart K.post (fun a => ¬ P₂ a)) := ⟨fun x => x.2 (hno x.1)⟩
  have hdl := dartless_numComponents (restrictP K.post (fun a => ¬ P₂ a) hP₂.neg)
  have hdl' : (restrictP K.post (fun a => ¬ P₂ a) hP₂.neg).atoms.card = (K.post.atoms.filter fun a => ¬ P₂ a).card := rfl
  rw [hdl, hdl'] at hadd
  have hcard : (K.post.atoms.filter fun a => ¬ P₂ a).card = jdeg2 K := by
    unfold jdeg2
    have hfa := fa_mem_post K
    have hfb := fb_mem_post K
    by_cases h1 : s.M.deg K.C.upper = 2 <;> by_cases h2 : s.M.deg K.C.lower = 2
    · have : K.post.atoms.filter (fun a => ¬ P₂ a) = {K.fa, K.fb} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, hP₂d]
        constructor
        · rintro ⟨-, h⟩
          by_contra hh
          push Not at hh
          exact h ⟨fun e => hh.1 e.1, fun e => hh.2 e.1⟩
        · rintro (rfl | rfl)
          · exact ⟨hfa, fun h => h.1 ⟨rfl, h1⟩⟩
          · exact ⟨hfb, fun h => h.2 ⟨rfl, h2⟩⟩
      rw [this, Finset.card_pair K.fa_ne_fb]; simp [h1, h2]
    · have : K.post.atoms.filter (fun a => ¬ P₂ a) = {K.fa} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_singleton, hP₂d]
        constructor
        · rintro ⟨-, h⟩
          by_contra hh
          exact h ⟨fun e => hh e.1, fun e => h2 e.2⟩
        · rintro rfl
          exact ⟨hfa, fun h => h.1 ⟨rfl, h1⟩⟩
      rw [this]; simp [h1, h2]
    · have : K.post.atoms.filter (fun a => ¬ P₂ a) = {K.fb} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_singleton, hP₂d]
        constructor
        · rintro ⟨-, h⟩
          by_contra hh
          exact h ⟨fun e => h1 e.2, fun e => hh e.1⟩
        · rintro rfl
          exact ⟨hfb, fun h => h.2 ⟨rfl, h2⟩⟩
      rw [this]; simp [h1, h2]
    · have : K.post.atoms.filter (fun a => ¬ P₂ a) = ∅ := by
        ext a
        simp only [Finset.mem_filter, Finset.notMem_empty, hP₂d, iff_false]
        rintro ⟨-, h⟩
        exact h ⟨fun e => h1 e.2, fun e => h2 e.2⟩
      rw [this]; simp [h1, h2]
  omega

end ncomp

section rhoG
variable {s : St.{u} V D₀} (K : Step1.VineCut Src.γL s.M)

theorem vineKeep_of_mem {a : V} (ha : a ∈ s.M.atoms.filter (fun a => a ∉ K.C.atoms)) : VineKeep K a := by
  have := Finset.mem_filter.1 ha
  exact ⟨this.2, fun ⟨e, _⟩ => K.fa_fresh (e ▸ this.1), fun ⟨e, _⟩ => K.fb_fresh (e ▸ this.1)⟩

theorem vineTransferG (hdeg : s.M.deg K.C.upper ≤ 4) (hdegl : s.M.deg K.C.lower ≤ 4) :
    LadderTransfer s.M (vineStG s K).M (s.M.atoms.filter (fun a => a ∉ K.C.atoms)) where
  subM a ha := (Finset.mem_filter.1 ha).1
  subM' a ha := by
    have := Finset.mem_filter.1 ha
    show a ∈ (K.cutMol.atoms).filter (VineKeep K)
    refine Finset.mem_filter.2 ⟨?_, vineKeep_of_mem K ha⟩
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this.1)
  bonds a ha b hb := by
    obtain ⟨hau, hal, haf, haf'⟩ := vineAvoid K ha
    obtain ⟨hbu, hbl, hbf, hbf'⟩ := vineAvoid K hb
    show (restrictP K.cutMol (VineKeep K) (VineKeep.closed K)).bondsBetween a b = s.M.bondsBetween a b
    rw [restrictP_bondsBetween K.cutMol _ (VineKeep.closed K) (vineKeep_of_mem K ha) (vineKeep_of_mem K hb)]
    show ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).bondsBetween a b = _
    rw [cut_bondsBetween_eq (s.M.cut K.C.upper K.fa K.x₁ K.x₂) hal haf' hbl hbf', cut_bondsBetween_eq s.M hau haf hbu hbf]
  dir a ha b hb := by
    obtain ⟨hau, hal, haf, haf'⟩ := vineAvoid K ha
    obtain ⟨hbu, hbl, hbf, hbf'⟩ := vineAvoid K hb
    show (restrictP K.cutMol (VineKeep K) (VineKeep.closed K)).Directed a b ↔ s.M.Directed a b
    rw [restrictP_directed K.cutMol _ (VineKeep.closed K) (vineKeep_of_mem K ha) (vineKeep_of_mem K hb)]
    show ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).Directed a b ↔ _
    rw [cut_directed_iff (s.M.cut K.C.upper K.fa K.x₁ K.x₂) hal haf' hbl hbf', cut_directed_iff s.M hau haf hbu hbf]
  low x hx hxA := by
    have hx' := Finset.mem_filter.1 hx
    have hxc : x ∈ K.cutMol.atoms := hx'.1
    have hxM : x ∉ s.M.atoms := fun h => hxA (Finset.mem_filter.2 ⟨h, hx'.2.1⟩)
    have hfa : x = K.fa ∨ x = K.fb := by
      rcases Finset.mem_insert.1 hxc with h | h
      · exact Or.inr h
      · rcases Finset.mem_insert.1 h with h | h
        · exact Or.inl h
        · exact absurd h hxM
    show (restrictP K.cutMol (VineKeep K) (VineKeep.closed K)).deg x ≤ 2
    rw [restrictP_deg K.cutMol _ (VineKeep.closed K) hx'.2]
    have e1 := cut_deg_v₂ s.M K.cut_a
    have e2 := cut_deg_v₂ (s.M.cut K.C.upper K.fa K.x₁ K.x₂) K.cut_b
    have e3 : (s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = s.M.deg K.C.lower :=
      cut_deg_other K.cut_a K.ab_ne.symm K.fa_ne_b.symm
    rcases hfa with h | h
    · rw [h]
      show ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg K.fa ≤ 2
      rw [cut_deg_other K.cut_b (fun e => K.fa_ne_b e) K.fa_ne_fb]
      omega
    · rw [h]
      show ((s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg K.fb ≤ 2
      omega

/-- **`ρ` after Step D1**: the loss is at most the ladder loss of the removed object. -/
theorem rho_vineStG_le (hM : ∀ x ∈ s.M.atoms, s.M.deg x ≤ 4) {n : ℕ}
    (hn : ladderLoss s.M (s.M.atoms.filter (fun a => a ∉ K.C.atoms)) ≤ n) :
    s.M.rho ≤ (vineStG s K).M.rho + n := by
  have h1 := (vineTransferG K (hM _ K.a_atom) (hM _ K.b_atom)).rho_le
  omega

end rhoG

section hwd1
variable {L γ η : ℝ}

theorem jdeg2_pos {s : St.{u} V D₀} (K : Step1.VineCut Src.γL s.M) (hd2 : s.M.deg K.C.upper = 2 ∨ s.M.deg K.C.lower = 2) : 1 ≤ jdeg2 K := by
  unfold jdeg2
  rcases hd2 with h | h <;> simp [h]

theorem jdeg2_le {s : St.{u} V D₀} (K : Step1.VineCut Src.γL s.M) : jdeg2 K ≤ 2 := by
  unfold jdeg2; split_ifs <;> omega

/-- **LC-1: the potential inequality of Step D1 from the object data** (no assumption on the true increments: `ΔF`, `ΔV_β`, `ρ`, the
critical count and the index of `vinePostG K` are computed). -/
theorem hW_D1' (hL1 : 1 ≤ L) (hη : 0 ≤ η) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ)) (ε0 : ℝ) (crit : V → Prop) (Fmax : ℝ)
    {h : HSt V D₀} (K : Step1.VineCut Src.γL h.s.M) {R : ℕ} (hI : Inv R h.s) (hap : ApPos h.s)
    (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps)
    (hd2 : h.s.M.deg K.C.upper = 2 ∨ h.s.M.deg K.C.lower = 2) (hnew : h.s.M.numComponents < K.post.numComponents)
    (hrem : ∀ a ∈ K.C.atoms, h.s.cls a = .eps) (hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a)
    (hM : ∀ x ∈ h.s.M.atoms, h.s.M.deg x ≤ 4)
    (hloss : ladderLoss h.s.M (h.s.M.atoms.filter (fun a => a ∉ K.C.atoms)) ≤ 86) {CN : ℝ} (hCN : 0 ≤ CN) (N : ℕ)
    (hN : (N : ℝ) * CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)))) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (CN * excessRHS2 L γ η [] 1 2) *
      WPot L γ η (Y0f L γ η ε0 (RofS (h.vinePostGL K).s)) (g1 γ η crit Fmax) (h.vinePostGL K)) ≤
      WPot L γ η (Y0f L γ η ε0 (RofS h.s)) (g1 γ η crit Fmax) h := by
  have hju : 3 ≤ h.s.M.deg K.C.upper ∨ h.s.M.deg K.C.upper = 2 := by
    have := two_le_deg_upper K; omega
  have hjl : 3 ≤ h.s.M.deg K.C.lower ∨ h.s.M.deg K.C.lower = 2 := by
    have := two_le_deg_lower K; omega
  obtain ⟨R', e, hI'⟩ := hI.vineStGL K hu hl hju hjl
  have hs : (h.vinePostGL K).s = vineStG h.s K := rfl
  have hF1 : K.post.numComponents = h.s.M.numComponents + 1 := by
    have := vine_F_le_succ K; omega
  have hFc := numComponents_vineStG K
  have hVc := vBeta_vineStG h.s K hrem
  have hj1 := jdeg2_pos K hd2
  have hj2 := jdeg2_le K
  have hρ := rho_vineStG_le K hM hloss
  refine hW_D1 hL1 hη hη40 hγ0 ε0 crit Fmax (j := jdeg2 K) hj1 hj2 (R := R) (R' := R') e hI (by rw [hs]; exact hI') hap ?_ ?_ ?_ ?_ ?_
    hCN N hN
  · rw [hs]; exact apProd_vineStG h.s K L γ η hrem
  · rw [hs]
    have : (h.s.M.numComponents : ℝ) + 1 = (vineStG h.s K).M.numComponents + jdeg2 K := by
      have : h.s.M.numComponents + 1 = (vineStG h.s K).M.numComponents + jdeg2 K := by omega
      exact_mod_cast this
    linarith
  · rw [hs]
    have : (vBeta (vineStG h.s K) : ℝ) + jdeg2 K = vBeta h.s + 2 := by exact_mod_cast hVc
    linarith
  · rw [hs]; omega
  · rw [hs]; exact critCount_vineStG h.s K crit hint

end hwd1

end WaveTurbulence.GammaLow.FinalCount.H
