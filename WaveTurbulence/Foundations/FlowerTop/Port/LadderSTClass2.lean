/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderSTClass
/-! # FLOWER-P5: `class_fourierST` (copy-and-thread of `class_fourier`) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.LadderDisjoint MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w d : ℕ} {G : Garden w}

theorem class_fourierST (hp : G.IsPlain) {L : ℝ} (hL : 0 < L) (D : SplicedKernelDataST G d)
    (hamp : SplicedAmplitudeBounds G D.toSplicedKernelData)
    (hpend : ∀ S ∈ G.molecule.maximalLadders, ∀ b ∈ D.stubs, b ∉ S)
    (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ) (hδ : 0 ≤ δ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (π0 : PF G)
    (cd : CD G D.toSplicedKernelData L γ δ base roots hp π0 (fun S => 8 * δ * L ^ (2 * γ) * scales S.1))
    (isSmall : LQ G → Prop) (hsm : ∀ S, isSmall S → scales S.1 < 1)
    (Dt : ℝ) (hDt0 : 0 ≤ Dt) (hDt : ∀ v, (D.layer v : ℝ) + 2 ≤ Dt)
    (hs : ∀ v : FrB G D.fix, floorB D v.1 → D.stubTime ≤ (D.layer v.1 : ℝ) + 1)
    (A : Finset (FrB G D.fix)) :
    ∫⁻ α in Wnb (clsPFfree D scales L γ η δ base roots π0),
        ‖Phi (Om0 (chF D) (lsF D) (capF D)) (lsF D) A α‖ₑ ≤
      2 ^ Fintype.card (Jr (cd.Kn isSmall)) *
        ((∏ s : Jr (cd.Kn isSmall), ENNReal.ofReal (2 * rhoS d L γ δ (scales s.1.1))) *
          ((∏ S : LQ G, ENNReal.ofReal (2 ^ (cd.Kn isSmall S) * Dt ^ (cd.Kn isSmall S) /
              (Nat.factorial (cd.Kn isSmall S) : ℝ))) *
            ENNReal.ofReal (Real.pi ^ Fintype.card (FrB G D.fix) *
              3 ^ (Fintype.card (FrB G D.fix) - Fintype.card (Jr (cd.Kn isSmall)))) *
            (2 * ENNReal.ofReal (2 * Real.arsinh (Mv d L) + 1)) ^
              (Fintype.card (FrB G D.fix) - Fintype.card (Jr (cd.Kn isSmall))))) := by
  obtain ⟨Sy, hSy, hKc, hSyW⟩ := exists_Sy hp hL D.toSplicedKernelData hamp scales γ η δ base roots
  have hinj := cd.elim_injective isSmall
  -- free ladder atoms
  have huaF : ∀ s, D.fix (cd.ua isSmall s) = none := fun s => atomAt_free D hpend π0 s.1 true _
  have hvaF : ∀ s, D.fix (cd.va isSmall s) = none := fun s => atomAt_free D hpend π0 s.1 false _
  obtain ⟨uaF, hua_val⟩ : ∃ f : Jr (cd.Kn isSmall) → FrB G D.fix, ∀ s, (f s).1 = cd.ua isSmall s :=
    ⟨fun s => ⟨cd.ua isSmall s, huaF s⟩, fun s => rfl⟩
  obtain ⟨vaF, hva_val⟩ : ∃ f : Jr (cd.Kn isSmall) → FrB G D.fix, ∀ s, (f s).1 = cd.va isSmall s :=
    ⟨fun s => ⟨cd.va isSmall s, hvaF s⟩, fun s => rfl⟩
  have hinjF : Function.Injective (Sum.elim uaF vaF) := by
    intro a b h
    apply hinj
    have h' := congrArg Subtype.val h
    rcases a with a | a <;> rcases b with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr, hua_val, hva_val] at h' ⊢
    all_goals exact h'
  have hxθ : ∀ θ s, (xθ uaF vaF θ s).1 = xθ (cd.ua isSmall) (cd.va isSmall) θ s := by
    intro θ s; unfold xθ; split_ifs
    · exact hua_val s
    · exact hva_val s
  have hFrow : ∀ S j, ¬ (rowN (π0.u S) j ∈ D.stubs) ∧ ¬ (rowN (π0.v S) j ∈ D.stubs) := fun S j =>
    ⟨(fix_none_iff D _).mp (rowN_free D hpend π0 S j).1, (fix_none_iff D _).mp (rowN_free D hpend π0 S j).2⟩
  -- validity of the engine hypotheses
  have hbox : ∀ v : FrB G D.fix, 0 ≤ lsF D v ∧ lsF D v + 1 ≤ Dt := by
    intro v
    have hl := hDt v.1
    have h0 : (0 : ℝ) ≤ D.layer v.1 := Nat.cast_nonneg _
    unfold lsF
    split_ifs with hf
    · have := hs v hf
      refine ⟨h0.trans (le_max_left _ _), ?_⟩
      have : max (D.layer v.1 : ℝ) D.stubTime ≤ D.layer v.1 + 1 := max_le (by linarith) this
      linarith
    · exact ⟨h0, by linarith⟩
  have hval : ∀ t ∈ Om0 (chF D) (lsF D) (capF D), ∀ q : LQ G,
      NP (fun j : Fin (cd.Kn isSmall q) => max (t (uaF ⟨q, j⟩)) (t (vaF ⟨q, j⟩))) := by
    intro t ht q
    have hext := FlowerP5.CD.hval_fr cd isSmall (fun b => b ∉ D.stubs) hFrow (G.extendFix D.fix t) ?_ q
    · have e : ∀ s : Jr (cd.Kn isSmall), G.extendFix D.fix t (cd.ua isSmall s) = t (uaF s) ∧
          G.extendFix D.fix t (cd.va isSmall s) = t (vaF s) :=
        by
        intro s
        constructor
        · rw [extendFix_free D.fix t _ (huaF s)]; congr 1; exact Subtype.ext (hua_val s).symm
        · rw [extendFix_free D.fix t _ (hvaF s)]; congr 1; exact Subtype.ext (hva_val s).symm
      simpa only [(e ⟨q, _⟩).1, (e ⟨q, _⟩).2] using hext
    · intro b' b hch hb'
      have hb'F : D.fix b' = none := (fix_none_iff D b').mpr hb'
      by_cases hb : b ∈ D.stubs
      · rw [extendFix_stub D t b hb, extendFix_free D.fix t b' hb'F]
        exact (ht.2.1 ⟨b', hb'F⟩).trans_le (by
          unfold capF
          refine (min_le_right _ _).trans ?_
          rw [if_pos ⟨b, hb, hch⟩])
      · have hbF : D.fix b = none := (fix_none_iff D b).mpr hb
        rw [extendFix_free D.fix t b' hb'F, extendFix_free D.fix t b hbF]
        exact ht.2.2 ⟨b', hb'F⟩ ⟨b, hbF⟩ hch
  have hloc : ∀ θ : Jr (cd.Kn isSmall) → Bool, ∃ hX : FrB G D.fix → (FrB G D.fix → ℝ) → ℝ,
      (∀ x, Measurable (hX x)) ∧
      (∀ x (β β' : FrB G D.fix → ℝ), (∀ b, b ∉ Finset.univ.image (xθ uaF vaF θ) → β b = β' b) → hX x β = hX x β') ∧
      ∀ α ∈ Wnb (clsPFfree D scales L γ η δ base roots π0),
        (∀ b, b ∉ Finset.univ.image (xθ uaF vaF θ) → α b ∈ Sy b.1) ∧
        ∀ j, |α (xθ uaF vaF θ j) - hX (xθ uaF vaF θ j) α| ≤ rhoS d L γ δ (scales j.1.1) := by
    intro θ
    refine ⟨fun x β => cd.hXf isSmall θ x.1 (ext0F β), fun x => ?_, ?_, ?_⟩
    · exact measurable_comp_ext0F D.fix (cd.hXf isSmall θ x.1) (cd.hXf_measurable isSmall θ x.1)
    · intro x β β' h
      refine FlowerP5.CD.hXf_dep_fr cd isSmall hinj (fun b => b ∉ D.stubs)
        (fun S b i => (fix_none_iff D _).mp (atomAt_free D hpend π0 S b i)) θ x.1 _ _ ?_
      intro b hb hFb
      have hbF : D.fix b = none := (fix_none_iff D b).mpr hFb
      rw [ext0F_free β b hbF, ext0F_free β' b hbF]
      apply h
      intro hmem
      obtain ⟨s, _, hs'⟩ := Finset.mem_image.mp hmem
      apply hb
      refine Finset.mem_image.mpr ⟨s, Finset.mem_univ _, ?_⟩
      rw [← hxθ, hs']
    · rintro αf ⟨αf', ⟨α', hα', hαα'⟩, hclose⟩
      obtain ⟨ᾱ, hbar_free, hbar_stub⟩ : ∃ ᾱ : GBranch G.tree → ℝ,
          (∀ b (h : D.fix b = none), ᾱ b = αf ⟨b, h⟩) ∧ (∀ b, ¬ D.fix b = none → ᾱ b = α' b) :=
        ⟨fun b => if h : D.fix b = none then αf ⟨b, h⟩ else α' b,
          fun b h => by simp [h], fun b h => by simp [h]⟩
      have hcl : ∀ b, |ᾱ b - α' b| ≤ 1 := by
        intro b
        by_cases h : D.fix b = none
        · rw [hbar_free b h, ← hαα' ⟨b, h⟩]; exact hclose ⟨b, h⟩
        · rw [hbar_stub b h]; simp
      have hspec := clsPF_subset_spectrum D.toSplicedKernelData scales L γ η δ base roots π0 hα'
      refine ⟨fun b hb => ?_, fun j => ?_⟩
      · have := hSyW α' hspec ᾱ hcl b.1
        rwa [hbar_free b.1 b.2] at this
      · have hloc := loc_atom hp hL D.toSplicedKernelData hamp scales γ η δ hδ base roots π0 cd isSmall hsm θ j
          ᾱ α' hα' hcl
        have hxF := huaF  -- keep names
        have hxj : D.fix (xθ (cd.ua isSmall) (cd.va isSmall) θ j) = none := by
          rw [← hxθ]; exact (xθ uaF vaF θ j).2
        have h1 : ᾱ (xθ (cd.ua isSmall) (cd.va isSmall) θ j) = αf (xθ uaF vaF θ j) := by
          rw [hbar_free _ hxj]; congr 1; exact Subtype.ext (hxθ θ j).symm
        have h2 : cd.hXf isSmall θ (xθ (cd.ua isSmall) (cd.va isSmall) θ j) ᾱ =
            cd.hXf isSmall θ (xθ uaF vaF θ j).1 (ext0F αf) := by
          rw [hxθ]
          refine FlowerP5.CD.hXf_dep_fr cd isSmall hinj (fun b => b ∉ D.stubs)
            (fun S b i => (fix_none_iff D _).mp (atomAt_free D hpend π0 S b i)) θ _ _ _ ?_
          intro b _ hFb
          have hbF : D.fix b = none := (fix_none_iff D b).mpr hFb
          rw [hbar_free b hbF, ext0F_free αf b hbF]
        rw [h1, h2] at hloc
        exact hloc
  have hcl := class_bound (chF D) (fun b : FrB G D.fix => b.1.1.2.length)
    (fun a b h => isChildOf_length h) (fun a b b' h h' => Subtype.ext (isChildOf_unique h h'))
    uaF vaF hinjF (lsF D) (capF D) Dt hDt0 hbox hval A (fun b => Sy b.1) (fun b => hSy b.1)
    (ENNReal.ofReal (2 * Real.arsinh (Mv d L) + 1)) (fun b β => hKc b.1 β)
    (fun s => rhoS d L γ δ (scales s.1.1)) (Wnb (clsPFfree D scales L γ η δ base roots π0)) hloc
  exact hcl

end WaveTurbulence.FlowerP5
