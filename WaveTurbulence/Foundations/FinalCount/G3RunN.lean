/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Elig
public import WaveTurbulence.Foundations.FinalCount.G3FinalE3
/-! **FINALCOUNT-G3 (R29 item 1): the run `HRunN` of Operations 1--4 with eligible triangles.**

MODEL DEFINITION (recorded in HANDOFF.md, "DesRec as a model definition"): TARGET L2152 says the atom `v` of Operation 3 is
"SG with fixed `(ℓ₁,ℓ₂)`"; Operation 1 cuts the joints along the two bonds of the vine; S4's `hingeSG` makes the designated
pair of a hinge SG.  So at a hinge the cut pair of Operations 1 and 3 is a designated pair (`Desig`); in Operation 2 this is
part of `Eligible` (A1).  `HStep1C`, `HStep3C` add this to `HStep1`, `HStep3`.  Operation 4 needs nothing (`desRec`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- **Step 1** with the designated pairs at hinge joints. -/
inductive HStep1C (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | vine (h : HSt V D₀) (K : VineCut h.s.M) (R : ℝ) (kp : ℕ) (hR : IsLabel L γ η R) (hkp : kp = 0 ∨ kp = 50)
      (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps)
      (ga : GapSim L w (κ ∘ h.s.down) K.x₁ K.x₂ R) (gb : GapSim L w (κ ∘ h.s.down) K.y₁ K.y₂ R)
      (htwin : pgap L w κ (h.s.pr K.y₁ K.y₂) = pgap L w κ (h.s.pr K.x₁ K.x₂) ∨
        pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂))
      (hι₁ : kp = 50 ↔ IotaHit L η w κ h.alive (h.s.pr K.x₁ K.x₂) R)
      (hι₂ : kp = 50 ↔ IotaHit L η w κ (h.s.pr K.x₁ K.x₂ :: h.alive) (h.s.pr K.y₁ K.y₂) R)
      (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG)
      (h3a : 3 ≤ h.s.M.deg K.C.upper) (h3b : 3 ≤ h.s.M.deg K.C.lower)
      (hdu : Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂)) (hdl : Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂)) :
      HStep1C C L γ η w κ h
        ⟨vineSt h.s K (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp),
         h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist,
         Function.update (Function.update (Function.update (Function.update h.crec K.C.upper
           (some (h.s.pr K.x₁ K.x₂, h.alive))) K.fa (some (h.s.pr K.x₁ K.x₂, h.alive))) K.C.lower
           (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive))) K.fb
           (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive)),
         Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)⟩

  | triple (h : HSt V D₀) (v v₂ : V) (x₁ x₂ : h.s.D) (hc : h.s.M.IsCutData v v₂ x₁ x₂) (R : ℝ) (kp : ℕ)
      (hR : IsLabel L γ η R) (hkp : kp = 0 ∨ kp = 50) (hε : h.s.cls v = .eps)
      (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) x₁ x₂) = .SG)
      (hsim : GapSim L w (κ ∘ h.s.down) x₁ x₂ R)
      (hι : kp = 50 ↔ IotaHit L η w κ h.alive (h.s.pr x₁ x₂) R) (h3 : 3 ≤ h.s.M.deg v)
      (hdes : Desig C (h.anc v) (h.s.pr x₁ x₂)) (hhinge : h.anc v ∈ C.hinges)
      (u : V) (hu : u ≠ v) (hb3 : 3 ≤ h.s.M.bondsBetween v u)
      (hm₁ : h.s.M.atom (h.s.M.mate x₁) = u) (hm₂ : h.s.M.atom (h.s.M.mate x₂) = u) :
      HStep1C C L γ η w κ h
        ⟨h.s.cutSt v v₂ x₁ x₂ (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta)
          (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta),
         h.s.pr x₁ x₂ :: h.hist,
         Function.update (Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive))) v₂
           (some (h.s.pr x₁ x₂, h.alive)),
         Function.update h.anc v₂ (h.anc v)⟩

/-- **R37(b), the Step-1 stop for triple bonds**: no `triple` step applies (gap-level form, like `NoBetaCut`). -/
def NoTripleCut (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∀ v v₂ : V, ∀ x₁ x₂ : h.s.D, h.s.M.IsCutData v v₂ x₁ x₂ → h.s.cls v = .eps → 3 ≤ h.s.M.deg v →
    h.anc v ∈ C.hinges → Desig C (h.anc v) (h.s.pr x₁ x₂) →
    (∃ u, u ≠ v ∧ 3 ≤ h.s.M.bondsBetween v u ∧ h.s.M.atom (h.s.M.mate x₁) = u ∧ h.s.M.atom (h.s.M.mate x₂) = u) →
    Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) x₁ x₂) ≠ .SG

/-- **The named input of R37(b)** (S4 `Subpro.triple_in_designated`, generic form): every triple bond of `M_sub` has a hinge
endpoint whose designated pair lies inside it. (S4 proves it for `bondsBetween = 3`; here `3 ≤`, the `≥ 4` case being a
closed two-atom component of `M_sub`, excluded by connectedness: assembly glue.) -/
def TripleDesig (C : CollData M₀) : Prop :=
  ∀ a b : V, a ∈ M₀.atoms → b ∈ M₀.atoms → a ≠ b → 3 ≤ M₀.bondsBetween a b →
    ∃ v c x y, ((v = a ∧ c = b) ∨ (v = b ∧ c = a)) ∧ v ∈ C.hinges ∧ C.first v = some x ∧ C.second v = some y ∧
      TripleAtM M₀ v x y ∧ M₀.atom (M₀.mate x) = c ∧ M₀.atom (M₀.mate y) = c

/-- **Step 3** with the designated pair at a hinge. -/
inductive HStep3C (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | cut (h : HSt V D₀) (v v₂ : V) (x₁ x₂ : h.s.D) (hc : h.s.M.IsCutData v v₂ x₁ x₂) (R : ℝ) (kp : ℕ)
      (hR : IsLabel L γ η R) (hkp : kp = 0 ∨ kp = 50) (hε : h.s.cls v = .eps)
      (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) x₁ x₂) = .SG)
      (hsim : GapSim L w (κ ∘ h.s.down) x₁ x₂ R)
      (hι : kp = 50 ↔ IotaHit L η w κ h.alive (h.s.pr x₁ x₂) R) (h3 : 3 ≤ h.s.M.deg v)
      (hdes : Desig C (h.anc v) (h.s.pr x₁ x₂)) :
      HStep3C C L γ η w κ h
        ⟨h.s.cutSt v v₂ x₁ x₂ (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta)
          (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta),
         h.s.pr x₁ x₂ :: h.hist,
         Function.update (Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive))) v₂
           (some (h.s.pr x₁ x₂, h.alive)),
         Function.update h.anc v₂ (h.anc v)⟩

theorem HStep3C.toHStep3 {C : CollData M₀} {h h' : HSt V D₀} (hs : HStep3C C L γ η w κ h h') :
    HStep3 L γ η w κ h h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 _ =>
    exact HStep3.cut h v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3

theorem HStep1C.cases {C : CollData M₀} {h h' : HSt V D₀} (hs : HStep1C C L γ η w κ h h') :
    HStep1 L γ η w κ h h' ∨ HStep3C C L γ η w κ h h' := by
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι₁ hι₂ hsg h3a h3b _ _ =>
    exact Or.inl (HStep1.vine h K R kp hR hkp hu hl ga gb htwin hι₁ hι₂ hsg h3a h3b)
  | triple v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes _ _ _ _ _ _ =>
    exact Or.inr (HStep3C.cut h v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes)

theorem HStep1C.anc {C : CollData M₀} {h h' : HSt V D₀} (hs : HStep1C C L γ η w κ h h')
    (hr : AncRel M₀ h.s h.anc) : AncRel M₀ h'.s h'.anc := by
  rcases hs.cases with h1 | h3
  · exact h1.anc hr
  · exact h3.toHStep3.anc hr

theorem InvE.step1C {t : ℕ} {C : CollData M₀} {h h' : HSt V D₀} (hI : InvE M₀ R t L γ η w κ h)
    (hs : HStep1C C L γ η w κ h h') : InvE M₀ R t L γ η w κ h' := by
  rcases hs.cases with h1 | h3
  · exact hI.step1 h1
  · exact hI.step3 h3.toHStep3

/-- **A run of Operations 1--4 (R29 item 1)**: Step 2 acts on eligible triangles only and stops at `NoEligibleTriangle`;
Step 4 makes nonzero-gap `β`-cuts and stops at `NoBetaCut`. -/
def HRunN (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h₀ hf : HSt V D₀) : Prop :=
  ∃ h₁ h₂ h₃ : HSt V D₀,
    Relation.ReflTransGen (HStep1C C L γ η w κ) h₀ h₁ ∧ NoTripleCut C L γ η w κ h₁ ∧
    Relation.ReflTransGen (HStep2C C L γ η w κ) h₁ h₂ ∧ NoEligibleTriangle C L γ η w κ h₂ ∧
    Relation.ReflTransGen (HStep3C C L γ η w κ) h₂ h₃ ∧ NoSGLeft L γ η w κ h₀.s h₃.s ∧
    Relation.ReflTransGen (HStep4 L w κ) h₃ hf ∧ NoBetaCut L w κ hf.s

/-- The phases of a run, as plain `ReflTransGen`s of the underlying steps. -/
theorem HRunN.invN {C : CollData M₀} {h₀ hf : HSt V D₀} (hr : HRunN C L γ η w κ h₀ hf)
    (h0 : InvE M₀ R 0 L γ η w κ h₀) : InvE M₀ R 0 L γ η w κ hf := by
  obtain ⟨h₁, h₂, h₃, a1, -, a2, -, a3, -, a4, -⟩ := hr
  exact rtgH (P := InvE M₀ R 0 L γ η w κ) (fun _ _ hs hI => hI.step4 hs) a4
    (rtgH (P := InvE M₀ R 0 L γ η w κ) (fun _ _ hs hI => hI.step3 hs.toHStep3) a3
    (rtgH (P := InvE M₀ R 0 L γ η w κ) (fun _ _ hs hI => hI.step2 hs.toHStep2) a2
    (rtgH (P := InvE M₀ R 0 L γ η w κ) (fun _ _ hs hI => hI.step1C hs) a1 h0)))


/-! ### `NoEligibleTriangle` is preserved by the cuts of Steps 3 and 4 -/

theorem TriData.pull' {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} {v v₂ : V} {x₁ x₂ : D}
    (hcd : M.IsCutData v v₂ x₁ x₂) (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (T' : TriData (M.cut v v₂ x₁ x₂)) :
    ∃ T : TriData M, (∀ j, T.a j = T'.a j) ∧ (∀ j, T.b j = T'.b j) ∧ ∀ j, T.t j = piV v v₂ (T'.t j) := by
  have hkey := piV_cut_atom M hcd
  have hcons : ∀ k : Fin 3, piV v v₂ (T'.t k) ≠ piV v v₂ (T'.t (k + 1)) := by
    intro k hk
    have h1 : M.atom (T'.b k) = piV v v₂ (T'.t k) := by rw [← hkey, T'.atom_b]
    have h2 : M.atom (M.mate (T'.b k)) = piV v v₂ (T'.t (k + 1)) := by
      have : (M.cut v v₂ x₁ x₂).mate (T'.b k) = T'.a (k + 1) := T'.mate_b k
      have e : M.mate (T'.b k) = T'.a (k + 1) := this
      rw [e, ← hkey, T'.atom_a]
    exact hnl (T'.b k) (by rw [h1, h2]; exact hk)
  refine ⟨⟨fun j => piV v v₂ (T'.t j), T'.f, T'.a, T'.b, ?_, ?_, ?_, T'.f_inj, ?_, ?_, T'.out_a, T'.out_b, T'.mate_b⟩,
    fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · intro j
    exact piV_mem M hcd (T'.t_mem j)
  · intro i j hij
    by_contra hne
    have : j = i + 1 ∨ i = j + 1 := (by decide : ∀ i j : Fin 3, i ≠ j → j = i + 1 ∨ i = j + 1) i j hne
    rcases this with h | h
    · exact hcons i (by rw [← h]; exact hij)
    · exact hcons j (by rw [← h]; exact hij.symm)
  · intro j h
    exact T'.f_fresh j (Finset.mem_insert_of_mem h)
  · intro j; rw [← hkey, T'.atom_a]
  · intro j; rw [← hkey, T'.atom_b]

/-- A cut step with history (`anc` of the new half is the `anc` of the cut atom). -/
theorem NoEligibleTriangle.cutH {C : CollData M₀} {h : HSt V D₀} (hN : NoEligibleTriangle C L γ η w κ h)
    (hnl : ∀ x, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x)) {v v₂ : V} {x₁ x₂ : h.s.D}
    (hcd : h.s.M.IsCutData v v₂ x₁ x₂) (c₁ c₂ : Cls) (hist : List (D₀ × D₀))
    (crec : V → Option ((D₀ × D₀) × List (D₀ × D₀))) :
    NoEligibleTriangle C L γ η w κ
      (⟨h.s.cutSt v v₂ x₁ x₂ c₁ c₂, hist, crec, Function.update h.anc v₂ (h.anc v)⟩ : HSt V D₀) := by
  intro T' hT
  obtain ⟨T, ha, hb, ht⟩ := TriData.pull' hcd hnl T'
  apply hN T
  have hanc : ∀ j, (Function.update h.anc v₂ (h.anc v)) (T'.t j) = h.anc (T.t j) := by
    intro j
    rw [ht j]
    by_cases e : T'.t j = v₂
    · simp [piV, e]
    · simp [piV, e, Function.update_of_ne e]
  obtain ⟨e1, e2, e3⟩ := hT
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have := e1 j
    simp only [HSt.s, St.cutSt] at this
    simpa [ha, hb, HSt.s] using this
  · simpa [ha, hb, HSt.s, St.pr, St.cutSt] using e2
  · intro j
    have := e3 j
    change Desig C (Function.update h.anc v₂ (h.anc v) (T'.t j)) _ at this
    rw [hanc j] at this
    simpa [ha, hb, HSt.s, St.pr, St.cutSt] using this


theorem NoEligibleTriangle.step3 {C : CollData M₀} {h h' : HSt V D₀} (hN : NoEligibleTriangle C L γ η w κ h)
    (hnl : ∀ x, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x)) (hs : HStep3 L γ η w κ h h') :
    NoEligibleTriangle C L γ η w κ h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 => exact hN.cutH hnl hc _ _ _ _

theorem NoEligibleTriangle.step4 {C : CollData M₀} {h h' : HSt V D₀} (hN : NoEligibleTriangle C L γ η w κ h)
    (hnl : ∀ x, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x)) (hs : HStep4 L w κ h h') :
    NoEligibleTriangle C L γ η w κ h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc hε hβ hnz h3 => exact hN.cutH hnl hc _ _ _ _

/-! ### `DesRec` as a theorem -/

/-- Every recorded cut at a hinge ancestor cuts along a designated pair (or its complement). -/
def DesRecN (C : CollData M₀) (h : HSt V D₀) : Prop :=
  ∀ j p vis, h.crec j = some (p, vis) → Desig C (h.anc j) p

theorem DesRecN.init (C : CollData M₀) : DesRecN C (HSt.init M₀) := by
  intro j p vis hj; simp [HSt.init] at hj

theorem DesRecN.step3 {C : CollData M₀} {h h' : HSt V D₀} (hD : DesRecN C h) (hs : HStep3C C L γ η w κ h h') :
    DesRecN C h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes =>
    have hne : v₂ ≠ v := fun e => hc.2.1 (e ▸ hc.1)
    intro j p vis hj
    by_cases e : j = v₂
    · subst e
      simp [Function.update_apply] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa using hdes
    by_cases e' : j = v
    · subst e'
      simp [Function.update_apply, e] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa [e] using hdes
    · simp [Function.update_apply, e, e'] at hj ⊢
      exact hD j p vis hj


theorem DesRecN.step1 {C : CollData M₀} {h h' : HSt V D₀} (hD : DesRecN C h) (hs : HStep1C C L γ η w κ h h') :
    DesRecN C h' := by
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι₁ hι₂ hsg h3a h3b hdu hdl =>
    have n1 : K.fa ≠ K.fb := K.fa_ne_fb
    have n2 : K.fa ≠ K.C.lower := K.fa_ne_b
    have n3 : K.fb ≠ K.C.upper := K.fb_ne_a
    have n4 : K.fa ≠ K.C.upper := fun e => K.fa_fresh (e ▸ K.a_atom)
    have n5 : K.fb ≠ K.C.lower := fun e => K.fb_fresh (e ▸ K.b_atom)
    have n6 : K.C.upper ≠ K.C.lower := K.ab_ne
    intro j p vis hj
    by_cases e1 : j = K.fb
    · subst e1
      simp [Function.update_apply, n1.symm, n5, n3] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa using hdl
    by_cases e2 : j = K.C.lower
    · subst e2
      simp [Function.update_apply, e1, n2.symm, n5.symm] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa [n2.symm, n5.symm] using hdl
    by_cases e3 : j = K.fa
    · subst e3
      simp [Function.update_apply, e1, e2, n1, n2, n4] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa using hdu
    by_cases e4 : j = K.C.upper
    · subst e4
      simp [Function.update_apply, e1, e2, e3, n3.symm, n4.symm] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa [n3.symm, n4.symm] using hdu
    · simp [Function.update_apply, e1, e2, e3, e4] at hj ⊢
      exact hD j p vis hj
  | triple v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes _ _ _ _ _ _ =>
    exact hD.step3 (HStep3C.cut h v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes)

theorem DesRecN.step2 {C : CollData M₀} {h h' : HSt V D₀} (hD : DesRecN C h) (hs : HStep2C C L γ η w κ h h') :
    DesRecN C h' := by
  cases hs with
  | mk T hel hs hT =>
    obtain ⟨Q, kp, hcl, rfl⟩ := hT
    have n01 : T.f 0 ≠ T.f 1 := fun e => by have := T.f_inj e; exact absurd this (by decide)
    have n02 : T.f 0 ≠ T.f 2 := fun e => by have := T.f_inj e; exact absurd this (by decide)
    have n12 : T.f 1 ≠ T.f 2 := fun e => by have := T.f_inj e; exact absurd this (by decide)
    obtain ⟨-, -, hd⟩ := hel
    intro j p vis hj
    by_cases e2 : j = T.f 2
    · subst e2
      simp [Function.update_apply] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa using hd 2
    by_cases e1 : j = T.f 1
    · subst e1
      simp [Function.update_apply, e2, n12] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa [n12] using hd 1
    by_cases e0 : j = T.f 0
    · subst e0
      simp [Function.update_apply, e2, e1, n01, n02] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa [n01, n02] using hd 0
    · simp [Function.update_apply, e0, e1, e2] at hj ⊢
      exact hD j p vis hj

/-- At a hinge atom that is `ε` there is nothing to cut (after Step 3 no `ε`-atom is SG, hinges are SG). -/
def NoEpsHinge (C : CollData M₀) (h : HSt V D₀) : Prop :=
  ∀ v ∈ h.s.M.atoms, h.s.cls v = .eps → v ∉ C.hinges

theorem DesRecN.step4 {C : CollData M₀} {h h' : HSt V D₀} (hD : DesRecN C h) (hs : HStep4 L w κ h h')
    (hA : AncRel M₀ h.s h.anc) (hN : NoEpsHinge C h) : DesRecN C h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc hε hβ hnz h3 =>
    have hvm : v ∈ h.s.M.atoms := hc.1
    have hanc : h.anc v = v := hA.eps v hvm hε
    have hvH : v ∉ C.hinges := hN v hvm hε
    intro j p vis hj
    by_cases e : j = v₂
    · subst e
      simp [Function.update_apply] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      intro hh; rw [hanc] at hh; exact absurd hh hvH
    by_cases e' : j = v
    · subst e'
      simp [Function.update_apply, e] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      intro hh; rw [hanc] at hh; exact absurd hh hvH
    · simp [Function.update_apply, e, e'] at hj ⊢
      exact hD j p vis hj

theorem NoEpsHinge.step4 {C : CollData M₀} {h h' : HSt V D₀} (hN : NoEpsHinge C h) (hs : HStep4 L w κ h h') :
    NoEpsHinge C h' := fun v hv hε => by
  obtain ⟨h1, h2⟩ := step4_eps hs.step hv hε
  exact hN v h1 h2


/-- A hinge atom of `M_sub` is SG (`subpro` (5), `hingeSG`). -/
theorem hinge_sgat {C : CollData M₀} (obl : SubproOblG C L γ η w κ) {v : V} (hv : v ∈ C.hinges) :
    SGat M₀ L γ η w κ v := by
  obtain ⟨f, s, -, -, ⟨hf, hs, hfs, hout⟩, hsg⟩ := obl.hingeSG v hv
  cases hof : M₀.out f
  · have hos : M₀.out s = true := by
      cases h : M₀.out s
      · exact absurd (hof.trans h.symm) hout
      · rfl
    exact ⟨f, s, hf, hs, hof, hos, hfs, hsg⟩
  · have hos : M₀.out s = false := by
      cases h : M₀.out s
      · rfl
      · exact absurd (hof.trans h.symm) hout
    refine ⟨s, f, hs, hf, hos, hof, ?_, ?_⟩
    · intro e; apply hfs; rw [e, M₀.mate_mate]
    · have hsw : Molecule.gapAt L w κ s f = -Molecule.gapAt L w κ f s := by
        unfold Molecule.gapAt; abel
      rw [hsw, gapKind_eq_of_norm_eq (L := L) (γ := γ) (η := η) (norm_neg (Molecule.gapAt L w κ f s))]
      exact hsg

theorem HRunN.desRec {C : CollData M₀} {hf : HSt V D₀} (hr : HRunN C L γ η w κ (HSt.init M₀) hf)
    (obl : SubproOblG C L γ η w κ) : DesRecN C hf ∧ AncRel M₀ hf.s hf.anc := by
  obtain ⟨h₁, h₂, h₃, a1, -, a2, -, a3, hsgl, a4, -⟩ := hr
  have key : ∀ {S : HSt V D₀ → HSt V D₀ → Prop}, (∀ a b, S a b → DesRecN C a ∧ AncRel M₀ a.s a.anc →
      DesRecN C b ∧ AncRel M₀ b.s b.anc) → ∀ {a b : HSt V D₀}, Relation.ReflTransGen S a b →
      DesRecN C a ∧ AncRel M₀ a.s a.anc → DesRecN C b ∧ AncRel M₀ b.s b.anc := fun hS a b hab ha =>
    rtgH (P := fun h => DesRecN C h ∧ AncRel M₀ h.s h.anc) hS hab ha
  have p1 := key (fun a b hs hp => ⟨hp.1.step1 hs, hs.anc hp.2⟩) a1 ⟨DesRecN.init C, AncRel.init M₀⟩
  have p2 := key (fun a b hs hp => ⟨hp.1.step2 hs, hs.toHStep2.anc hp.2⟩) a2 p1
  have p3 := key (fun a b hs hp => ⟨hp.1.step3 hs, hs.toHStep3.anc hp.2⟩) a3 p2
  have hN : NoEpsHinge C h₃ := fun v hv hε hvH => hsgl v hv hε (hinge_sgat obl hvH)
  exact (rtgH (P := fun h => DesRecN C h ∧ AncRel M₀ h.s h.anc ∧ NoEpsHinge C h)
    (fun a b hs hp => ⟨hp.1.step4 hs hp.2.1 hp.2.2, hs.anc hp.2.1, hp.2.2.step4 hs⟩) a4 ⟨p3.1, p3.2, hN⟩).imp_right
    (fun h => h.1)

end WaveTurbulence.FinalCountG3
