/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SepPieces

/-!
# Prop 6.1, `q > q'`, couples: the separated representation of the explicit leading term

With `K_J = 2 K_tr(1-η) C²` and `K_M = 2^{30d} d^{30d} C²`:

* **`couple_lower_sep`**: the lower leading term of every lower state has a separated representation with
  `(K_J^{m+1}, K_M^{m+1} β)` (`SepRep.mul` over the blocks of the `+` chain);
* **`couple_sep_gt`**: `LeafApp.coherentCouple` on `[q,q+1]×[q',q'+1]` has one with `(K_J^{n+1}, K_M^{n+1} β)`.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- The time constant of the separated representations. -/
noncomputable def KJ (θ C : ℝ) : ℝ := 2 * Ktr θ * C ^ 2

/-- The momentum constant of the separated representations. -/
noncomputable def KM (A d : ℕ) (C : ℝ) : ℝ := (2 : ℝ) ^ A * (d : ℝ) ^ A * C ^ 2

theorem pow_absorb {X C : ℝ} (hX : 1 ≤ X) (hC : 1 ≤ C) {n : ℕ} (hn : 1 ≤ n) :
    X * (C * C ^ n) ≤ (X * C ^ 2) ^ n := by
  have hC0 : 0 ≤ C := by linarith
  have h1 : X ≤ X ^ n := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ n := pow_le_pow_right₀ hX hn
  have h2 : C * C ^ n ≤ (C ^ 2) ^ n := by
    rw [← pow_succ', ← pow_mul]
    exact pow_le_pow_right₀ hC (by omega)
  rw [mul_pow]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem one_le_KJ {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 1 ≤ C) : 1 ≤ KJ θ C := by
  have hK := one_le_Ktr hθ
  have : 1 ≤ C ^ 2 := one_le_pow₀ hC
  unfold KJ
  nlinarith

theorem one_le_KM (A : ℕ) {d : ℕ} (hd : 1 ≤ d) {C : ℝ} (hC : 1 ≤ C) : 1 ≤ KM A d C := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (1 : ℝ) ≤ 2 ^ A := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ (d : ℝ) ^ A := one_le_pow₀ hd1
  have h3 : 1 ≤ C ^ 2 := one_le_pow₀ hC
  unfold KM
  have : (1 : ℝ) ≤ 2 ^ A * (d : ℝ) ^ A := one_le_mul_of_one_le_of_one_le h1 h2
  exact one_le_mul_of_one_le_of_one_le this h3

/-- The base absorption: `K_tr C^{m+1} ≤ K_J^{m+1}`. -/
theorem sep_base_J {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 1 ≤ C) (m : ℕ) :
    Ktr θ * (C * C ^ m) ≤ KJ θ C ^ (m + 1) := by
  have hK := one_le_Ktr hθ
  have h := pow_absorb (X := 2 * Ktr θ) (by linarith) hC (n := m + 1) (by omega)
  have hC0 : 0 ≤ C := by linarith
  have hle : C * C ^ m ≤ C * C ^ (m + 1) := by
    apply mul_le_mul_of_nonneg_left _ hC0
    exact pow_le_pow_right₀ hC (by omega)
  calc Ktr θ * (C * C ^ m) ≤ (2 * Ktr θ) * (C * C ^ (m + 1)) := by
        apply mul_le_mul (by linarith) hle (by positivity) (by linarith)
    _ ≤ _ := h

theorem sep_base_M (A : ℕ) {d : ℕ} (hd : 1 ≤ d) {C β : ℝ} (hC : 1 ≤ C) (hβ : 0 ≤ β) (m : ℕ) :
    C * C ^ m * β ≤ KM A d C ^ (m + 1) * β := by
  apply mul_le_mul_of_nonneg_right _ hβ
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hX : (1 : ℝ) ≤ 2 ^ A * (d : ℝ) ^ A :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hd1)
  have h := pow_absorb hX hC (n := m + 1) (by omega)
  have hC0 : 0 ≤ C := by linarith
  calc C * C ^ m ≤ 1 * (C * C ^ (m + 1)) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC (by omega)) hC0
    _ ≤ (2 ^ A * (d : ℝ) ^ A) * (C * C ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right hX (by positivity)
    _ ≤ _ := h

/-- The step absorption of the time constants. -/
theorem sep_step_J {θ C : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hC : 1 ≤ C) {nB m₂ : ℕ} (hnB : 1 ≤ nB) :
    2 ^ θ * (C * C ^ nB * Ktr θ) * KJ θ C ^ (m₂ + 1) ≤ KJ θ C ^ (nB + m₂ + 1) := by
  have hK := one_le_Ktr hθ0
  have h2 : (2 : ℝ) ^ θ ≤ 2 := by
    calc (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
      _ = 2 := Real.rpow_one 2
  have h20 : (0 : ℝ) ≤ 2 ^ θ := Real.rpow_nonneg (by norm_num) θ
  have h := pow_absorb (X := 2 * Ktr θ) (by linarith) hC hnB
  have hKJ0 : 0 ≤ KJ θ C ^ (m₂ + 1) := pow_nonneg (by linarith [one_le_KJ hθ0 hC]) _
  have hC0 : 0 ≤ C := by linarith
  calc 2 ^ θ * (C * C ^ nB * Ktr θ) * KJ θ C ^ (m₂ + 1)
      = (2 ^ θ * Ktr θ) * (C * C ^ nB) * KJ θ C ^ (m₂ + 1) := by ring
    _ ≤ (2 * Ktr θ) * (C * C ^ nB) * KJ θ C ^ (m₂ + 1) := by
        apply mul_le_mul_of_nonneg_right _ hKJ0
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right h2 (by linarith)
    _ ≤ KJ θ C ^ nB * KJ θ C ^ (m₂ + 1) := by
        apply mul_le_mul_of_nonneg_right _ hKJ0
        simpa [KJ] using h
    _ = KJ θ C ^ (nB + m₂ + 1) := by rw [← pow_add]; ring_nf

/-- The step absorption of the momentum constants. -/
theorem sep_step_M (A : ℕ) {d : ℕ} (hd : 1 ≤ d) {C β₁ β₂ : ℝ} (hC : 1 ≤ C) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    {nB m₂ : ℕ} (hnB : 1 ≤ nB) :
    (2 : ℝ) ^ A * (d : ℝ) ^ A * (C * C ^ nB * β₁) * (KM A d C ^ (m₂ + 1) * β₂) ≤
      KM A d C ^ (nB + m₂ + 1) * (β₁ * β₂) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hX : (1 : ℝ) ≤ 2 ^ A * (d : ℝ) ^ A :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hd1)
  have h := pow_absorb hX hC hnB
  have hKM0 : 0 ≤ KM A d C ^ (m₂ + 1) := pow_nonneg (by linarith [one_le_KM A hd hC]) _
  calc (2 : ℝ) ^ A * (d : ℝ) ^ A * (C * C ^ nB * β₁) * (KM A d C ^ (m₂ + 1) * β₂)
      = ((2 ^ A * (d : ℝ) ^ A) * (C * C ^ nB)) * KM A d C ^ (m₂ + 1) * (β₁ * β₂) := by ring
    _ ≤ KM A d C ^ nB * KM A d C ^ (m₂ + 1) * (β₁ * β₂) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hβ₁ hβ₂)
        apply mul_le_mul_of_nonneg_right _ hKM0
        simpa [KM, mul_assoc] using h
    _ = KM A d C ^ (nB + m₂ + 1) * (β₁ * β₂) := by rw [← pow_add]; ring_nf

theorem timeBox_closure_interior (q q' : ℕ) :
    ∀ t ∈ timeBox (q : ℝ) q', t ∈ closure (interior (timeBox (q : ℝ) q')) := fun t ht => by
  rw [closure_interior_timeBox]
  exact ht

section Induction

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1)
  {LG : LayeredGarden 2} (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal)
  {Xp Xm : RegChain} {Qlp : RegCpl} {q' : ℕ} (F : CohFacts LG Xp Xm Qlp q' p)
  (T' : Set (Fin 2 → ℝ)) (hTc : ∀ t ∈ T', t ∈ closure (interior T')) (b₀ : ℝ)
  (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox)

include O hC hd hL hη0 hη1 F hTc hT'

/-- **The separated lower leading term**, by induction over the blocks of the `+` chain. -/
theorem couple_lower_sep : ∀ (m : ℕ) (R X : RegChain) (LG' : LayeredGarden 2), Xp = appendChain R X →
    (SourceApp.closeCouple X Xm Qlp).size = 2 * m → m ≤ P.N (p + 1) ^ 4 →
    LowState LG H Bd Xm Qlp R.lonePath X LG' →
    SepRep (1 - P.η) P.δ (30 * P.d) (30 * P.d) m T'
      (fun ts k => lowApp P.δ LG H Xm Qlp q' R.lonePath X (ts 1) k)
      (KJ (1 - P.η) C ^ (m + 1))
      (KM (30 * P.d) P.d C ^ (m + 1) * leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z))) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro R X LG' hXp hsize hmN S
  have hθ : 0 ≤ 1 - P.η := by linarith
  have hθ1 : 1 - P.η ≤ 1 := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hA : 30 * P.d ≠ 0 := by omega
  have hβ0 : 0 ≤ leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) :=
    Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  obtain ⟨hXwf, hmwf, hlwf, hlt2⟩ := F.wf_suffix hXp
  by_cases hbase : X = .nil ∨ layerAt LG ((0 : Fin 2), R.lonePath) ≤ q'
  · obtain ⟨hu, hTA, hlayq⟩ := base_layers P F hXp S hbase
    have hwfc : (SourceApp.closeCouple X Xm Qlp).wf = true := closeCouple_wf hXwf hmwf hlwf hlt2
    obtain ⟨-, hJ, hM⟩ := O.couple q' m F.qp hmN _ hwfc hsize LG' S.dec hlayq _ _ S.ctrl
    have hsep := sep_bottom_couple P hη1 (fun z => H (botAddr R.lonePath z)) (SourceApp.closeCouple X Xm Qlp)
      hsize hJ hM T' b₀ hT'
    refine (hsep.congr fun ts _ k => lowApp_base P H hu hTA (ts 1) k).mono
      (by simpa [mul_comm] using sep_base_J hθ hC m) (sep_base_M _ hd hC hβ0 m)
  · push Not at hbase
    obtain ⟨hXn, hqu⟩ := hbase
    set π := R.lonePath with hπ
    set u := layerAt LG ((0 : Fin 2), π) with hu
    obtain ⟨hBlay, hlt, hlow'', hwf2, hSMD⟩ := block_facts F hXp hXn hu.symm hqu
    set B := takeLayer LG ((0 : Fin 2), π) u X with hBdef
    set D := dropLayer LG ((0 : Fin 2), π) u X with hDdef
    have hXe : appendChain B D = X := appendChain_take_drop LG _ u X
    have hSM := F.sm_suffix hXp
    obtain ⟨G₁, LG'', hdec₁, hsig₁, hlay₁, hctrl₁, S'', hβ, -⟩ :=
      couple_block_step S P.L P.γ P.δ hd hL hXn hwf2 hu.symm hlt hBlay
    have hsz : (SourceApp.closeCouple X Xm Qlp).size = B.size + (SourceApp.closeCouple D Xm Qlp).size := by
      rw [← hXe, closeCouple_size, closeCouple_size, appendChain_size]
      ring
    obtain ⟨nB, hnB⟩ := size_even_chain B
    obtain ⟨m₂, hm₂⟩ := size_even_cpl (SourceApp.closeCouple D Xm Qlp)
    have hB2 := two_le_size_of_ne_nil B (takeLayer_ne_nil LG X _ hXn)
    have hBsize : B.size = 2 * nB := by omega
    have hsz₂ : (SourceApp.closeCouple D Xm Qlp).size = 2 * m₂ := by omega
    have hmm : m = nB + m₂ := by omega
    have hnB1 : 1 ≤ nB := by omega
    have hup : u ≤ p := by
      apply F.high
      apply CohFacts.sub_suffix hXp
      cases hXc : X with
      | nil => exact absurd hXc hXn
      | pair m' Qr' Qg' inner' rest' => exact root_mem_chainNodesSet _ _ _ _ _ _ _
    have hBwf : B.wf = true := (wf_split (hXe ▸ hwf2 : (RegCpl.type2 (appendChain B D) Xm Qlp).wf = true)).1
    set HT := LeafApp.sliceProfiles LG H ((0 : Fin 2), π) u X with hHT
    set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 2), π) u X z.2) with hBT
    have hβT0 : 0 ≤ leafSizeProduct G₁ BT := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    obtain ⟨-, hJT, hMT⟩ := O.tree u _ nB hup hlt.le (by omega) B hBwf hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
    rw [hsig₁] at hMT
    have hmid := sep_middle_tree P hη1 HT B 1 hlt hBsize (by positivity) hJT hMT T' ![b₀, -(q' : ℝ)] hT'
    have hsl : SourceApp.chainSlice LG ((0 : Fin 2), π) u X = B :=
      chainSlice_eq_take LG _ X hSM fun _ => le_refl _
    have hXp' : Xp = appendChain (appendChain R B) D := by rw [appendChain_assoc, hXe]; exact hXp
    have hlp : (appendChain R B).lonePath = π ++ B.lonePath := appendChain_lonePath R B
    have S''' : LowState LG H Bd Xm Qlp (appendChain R B).lonePath D LG'' := by rw [hlp]; exact S''
    have hrest := ih m₂ (by omega) (appendChain R B) D LG'' hXp' hsz₂ (by omega) S'''
    rw [hlp] at hrest
    have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)) :=
      Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hprod := SepRep.mul hθ hTc hd hA (mul_nonneg (by positivity) (Ktr_nonneg _)) (by positivity)
      (mul_nonneg (pow_nonneg (zero_le_one.trans (one_le_KM _ hd hC)) _) hβ₂0) hmid hrest
    have hsplit := lowApp_split P.δ LG H Xm Qlp π X hu.symm hqu hXn hSM hSMD hlow'' hlt
    rw [← hmm] at hprod
    refine (hprod.congr fun ts _ k => ?_).mono ?_ ?_
    · rw [hsplit (ts 1) k]
      unfold sliceFactor
      rw [hsl]
    · rw [hmm]
      exact sep_step_J hθ hθ1 hC hnB1
    · rw [hβ, hmm]
      exact sep_step_M _ hd hC hβT0 hβ₂0 hnB1

end Induction

section Top

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1)

include O hC hd hL hη0 hη1

omit hL hη0 in
/-- **Trivial and type-1 codes.** -/
theorem couple_sep_type1 {q q' n : ℕ} (hqq : q' < q) (hnN : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (hsize : Q.size = 2 * n) (LG : LayeredGarden 2) (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (ht : Q.isType2 = false) (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal)
    (hH : LeafwiseControlled LG H Bd) (hqp : q ≤ p) :
    SepRep (1 - P.η) P.δ (30 * P.d) (30 * P.d) n (timeBox q q')
      (fun ts k => LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k)
      (KJ (1 - P.η) C ^ (n + 1)) (KM (30 * P.d) P.d C ^ (n + 1) * leafSizeProduct LG Bd) := by
  have hθ : 0 ≤ 1 - P.η := by linarith
  have hβ0 : 0 ≤ leafSizeProduct LG Bd := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hwf := hcoh.1
  have hQ := hcoh.2.1
  have hlayq := layers_type1 hqq.le hcoh ht
  obtain ⟨-, hJ, hM⟩ := O.couple q' n (by omega) hnN Q hwf hsize LG hQ hlayq H Bd hH
  have hsep := sep_bottom_couple P hη1 H Q hsize hJ hM (timeBox (q : ℝ) q') (-(q : ℝ)) (timeBox_shift_unit q q')
  refine (hsep.congr fun ts _ k => ?_).mono (by simpa [mul_comm] using sep_base_J hθ hC n)
    (sep_base_M _ hd hC hβ0 n)
  have hne : q ≠ q' := by omega
  cases Q with
  | triv => simp only [LeafApp.coherentCouple, hne, hqq, ↓reduceIte]
  | type1 c Q₁ Q₂ Q₃ => simp only [LeafApp.coherentCouple, hne, hqq, ↓reduceIte]
  | type2 Xp Xm Qlp => simp [RegCpl.isType2] at ht

/-- **Type-2 codes whose root is below `q`.** -/
theorem couple_sep_low {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (Xp Xm : RegChain) (Qlp : RegCpl) (hsize : (RegCpl.type2 Xp Xm Qlp).size = 2 * n) (LG : LayeredGarden 2)
    (hcoh : IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) LG) (H : LeafProfiles 2 P.d)
    (Bd : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd)
    (hr₁lt : layerAt LG ((0 : Fin 2), []) < q) :
    SepRep (1 - P.η) P.δ (30 * P.d) (30 * P.d) n (timeBox q q')
      (fun ts k => LeafApp.coherentCouple P.δ LG H (.type2 Xp Xm Qlp) q q' (ts 0) (ts 1) k)
      (KJ (1 - P.η) C ^ (n + 1)) (KM (30 * P.d) P.d C ^ (n + 1) * leafSizeProduct LG Bd) := by
  have F := cohFacts_of_coherent hqq.le hqp hcoh
  have hQ := hcoh.2.1
  have hwf := F.wf
  have hnn : (Xp.isNil && Xm.isNil) = false := by
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hwf
    exact hwf.2
  have hcl : SourceApp.closeCouple Xp Xm Qlp = RegCpl.type2 Xp Xm Qlp := by
    unfold SourceApp.closeCouple
    rw [hnn]
    rfl
  have hHe : (fun z => H (botAddr [] z)) = H := funext fun z => by rw [botAddr_nil]
  have hBe : (fun z => Bd (botAddr [] z)) = Bd := funext fun z => by rw [botAddr_nil]
  have S₀ : LowState LG H Bd Xm Qlp RegChain.nil.lonePath Xp LG := by
    refine ⟨by rw [hcl]; exact hQ, fun z => by simp [RegChain.lonePath, botAddr_nil], ?_⟩
    show LeafwiseControlled LG (fun z => H (botAddr [] z)) (fun z => Bd (botAddr [] z))
    rw [hHe, hBe]
    exact hH
  have hsizeC : (SourceApp.closeCouple Xp Xm Qlp).size = 2 * n := by rw [hcl]; exact hsize
  set r₁ := layerAt LG ((0 : Fin 2), []) with hr₁
  have hlowr₁ : q' ≤ r₁ := by
    by_cases hXpn : Xp = .nil
    · have := F.lone_suffix (R := .nil) (X := Xp) rfl
      rw [hXpn] at this
      simp only [RegChain.lonePath, addrExt, List.append_nil] at this
      rw [hr₁, this]
    · obtain ⟨m', Qr', Qg', inner', rest', hX'⟩ : ∃ m' Qr' Qg' inner' rest', Xp = .pair m' Qr' Qg' inner' rest' := by
        cases hXc : Xp with
        | nil => exact absurd hXc hXpn
        | pair m' Qr' Qg' inner' rest' => exact ⟨m', Qr', Qg', inner', rest', rfl⟩
      apply F.low
      rw [hX']
      exact root_mem_chainNodesSet _ _ _ _ _ _ _
  have hsep := couple_lower_sep P O hC hd hL hη0 hη1 H Bd F (timeBox (q : ℝ) q') (timeBox_closure_interior q q')
    (-(q : ℝ)) (timeBox_shift_unit q q') n .nil Xp LG rfl hsizeC hnN S₀
  simp only [RegChain.lonePath] at hsep
  rw [hBe] at hsep
  refine hsep.congr fun ts _ k => ?_
  have hslq : SourceApp.chainSlice LG ((0 : Fin 2), []) q Xp = .nil :=
    chainSlice_eq_nil LG _ Xp F.sm fun _ => hr₁lt
  rw [coherentCouple_type2_eq P.δ LG H Xp Xm Qlp hqq, hslq, LeafApp.tree_nil, mul_one]
  unfold lowApp lowSlices
  congr 1
  rw [← hr₁, Ioo_eq_Ico_succ, Ioo_eq_Ico_succ, ← prod_Ico_consecutive _ (show q' + 1 ≤ r₁ + 1 by omega)
    (show r₁ + 1 ≤ q by omega)]
  rw [Finset.prod_eq_one (s := Ico (r₁ + 1) q) fun r hr => by
    unfold sliceFactor
    rw [chainSlice_eq_nil LG _ Xp F.sm fun _ => by simp only [Finset.mem_Ico] at hr; omega]
    exact LeafApp.tree_nil _ _ _ _ _ _ _, mul_one]

/-- **Type-2 codes with a top block in layer `q`.** -/
theorem couple_sep_top {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (Xp Xm : RegChain) (Qlp : RegCpl) (hsize : (RegCpl.type2 Xp Xm Qlp).size = 2 * n) (LG : LayeredGarden 2)
    (hcoh : IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) LG) (H : LeafProfiles 2 P.d)
    (Bd : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd)
    (htop : layerAt LG ((0 : Fin 2), []) = q) :
    SepRep (1 - P.η) P.δ (30 * P.d) (30 * P.d) n (timeBox q q')
      (fun ts k => LeafApp.coherentCouple P.δ LG H (.type2 Xp Xm Qlp) q q' (ts 0) (ts 1) k)
      (KJ (1 - P.η) C ^ (n + 1)) (KM (30 * P.d) P.d C ^ (n + 1) * leafSizeProduct LG Bd) := by
  have hθ : 0 ≤ 1 - P.η := by linarith
  have hθ1 : 1 - P.η ≤ 1 := by linarith
  have hA : 30 * P.d ≠ 0 := by omega
  have F := cohFacts_of_coherent hqq.le hqp hcoh
  have hQ := hcoh.2.1
  have hwf := F.wf
  have hnn : (Xp.isNil && Xm.isNil) = false := by
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hwf
    exact hwf.2
  have hcl : SourceApp.closeCouple Xp Xm Qlp = RegCpl.type2 Xp Xm Qlp := by
    unfold SourceApp.closeCouple
    rw [hnn]
    rfl
  have hHe : (fun z => H (botAddr [] z)) = H := funext fun z => by rw [botAddr_nil]
  have hBe : (fun z => Bd (botAddr [] z)) = Bd := funext fun z => by rw [botAddr_nil]
  have S₀ : LowState LG H Bd Xm Qlp RegChain.nil.lonePath Xp LG := by
    refine ⟨by rw [hcl]; exact hQ, fun z => by simp [RegChain.lonePath, botAddr_nil], ?_⟩
    show LeafwiseControlled LG (fun z => H (botAddr [] z)) (fun z => Bd (botAddr [] z))
    rw [hHe, hBe]
    exact hH
  have hT := timeBox_shift_unit q q'
  have hXpn : Xp ≠ .nil := by
    intro hXpn
    have := F.lone_suffix (R := .nil) (X := Xp) rfl
    rw [hXpn] at this
    simp only [RegChain.lonePath, addrExt, List.append_nil] at this
    rw [htop] at this
    omega
  obtain ⟨hBlay, hlt, hlow'', hwf2, hSMD⟩ := block_facts F (R := .nil) rfl hXpn htop hqq
  simp only [RegChain.lonePath, List.nil_append] at hBlay hlt hlow'' hSMD
  set B := takeLayer LG ((0 : Fin 2), []) q Xp with hBdef
  set D := dropLayer LG ((0 : Fin 2), []) q Xp with hDdef
  set r'' := layerAt LG ((0 : Fin 2), B.lonePath) with hr''
  have hXe : appendChain B D = Xp := appendChain_take_drop LG _ q Xp
  obtain ⟨G₁, LG'', hdec₁, hsig₁, hlay₁, hctrl₁, S'', hβ, -⟩ :=
    couple_block_step S₀ P.L P.γ P.δ hd hL hXpn hwf2 htop hlt hBlay
  simp only [RegChain.lonePath, List.nil_append] at hlay₁ S'' hβ
  have hsz : (RegCpl.type2 Xp Xm Qlp).size = B.size + (SourceApp.closeCouple D Xm Qlp).size := by
    rw [← hXe, closeCouple_size]
    simp only [RegCpl.size, appendChain_size]
    ring
  obtain ⟨nB, hnB⟩ := size_even_chain B
  obtain ⟨m₂, hm₂⟩ := size_even_cpl (SourceApp.closeCouple D Xm Qlp)
  have hBne : B ≠ .nil := by
    have := takeLayer_ne_nil LG Xp ((0 : Fin 2), []) hXpn
    rw [htop] at this
    exact this
  have hB2 := two_le_size_of_ne_nil B hBne
  have hBsize : B.size = 2 * nB := by omega
  have hsz₂ : (SourceApp.closeCouple D Xm Qlp).size = 2 * m₂ := by omega
  have hnn' : n = nB + m₂ := by omega
  have hnB1 : 1 ≤ nB := by omega
  have hBwf : B.wf = true :=
    (wf_split (hXe ▸ hwf2 : (RegCpl.type2 (appendChain B D) Xm Qlp).wf = true)).1
  set HT := LeafApp.sliceProfiles LG H ((0 : Fin 2), []) q Xp with hHT
  set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 2), []) q Xp z.2) with hBT
  have hβT0 : 0 ≤ leafSizeProduct G₁ BT := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  obtain ⟨-, hJT, hMT⟩ := O.tree q r'' nB hqp hlt.le (by omega) B hBwf hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
  rw [hsig₁] at hMT
  have htopsep := sep_top_tree P hη1 HT B 1 hlt hBsize hJT hMT (timeBox (q : ℝ) q') (-(q' : ℝ)) hT
  have S''' : LowState LG H Bd Xm Qlp B.lonePath D LG'' := S''
  have hrest := couple_lower_sep P O hC hd hL hη0 hη1 H Bd F (timeBox (q : ℝ) q') (timeBox_closure_interior q q')
    (-(q : ℝ)) hT m₂ B D LG'' hXe.symm hsz₂ (by omega) S'''
  have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) :=
    Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hC0 : 0 ≤ C := by linarith
  have hprod := SepRep.mul hθ (timeBox_closure_interior q q') hd hA (mul_nonneg (Ktr_nonneg _) (by positivity))
    (by positivity) (mul_nonneg (pow_nonneg (zero_le_one.trans (one_le_KM _ hd hC)) _) hβ₂0) htopsep hrest
  rw [← hnn'] at hprod
  have hsl : SourceApp.chainSlice LG ((0 : Fin 2), []) q Xp = B :=
    chainSlice_eq_take LG _ Xp F.sm fun _ => by rw [htop]
  have hβe : leafSizeProduct LG Bd = leafSizeProduct G₁ BT *
      leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) := by
    have h' := hβ
    rw [hBe] at h'
    exact h'
  refine (hprod.congr fun ts _ k => ?_).mono ?_ ?_
  · have hrest' : (∏ r ∈ Finset.Ioo q' q, sliceFactor P.δ LG H [] Xp r k) *
        lowBot P.δ LG H Xm Qlp q' [] Xp (ts 1) k = lowApp P.δ LG H Xm Qlp q' B.lonePath D (ts 1) k :=
      lowRest_eq P.δ LG H Xm Qlp [] Xp htop hqq hSMD hlow'' hlt (ts 1) k
    rw [coherentCouple_type2_eq P.δ LG H Xp Xm Qlp hqq, hsl, ← hrest']
    ring
  · have h1 : 2 ^ (1 - P.η) * (Ktr (1 - P.η) * (C * C ^ nB)) * KJ (1 - P.η) C ^ (m₂ + 1) =
        2 ^ (1 - P.η) * (C * C ^ nB * Ktr (1 - P.η)) * KJ (1 - P.η) C ^ (m₂ + 1) := by ring
    rw [h1, hnn']
    exact sep_step_J hθ hθ1 hC hnB1
  · rw [hβe, hnn']
    exact sep_step_M _ hd hC hβT0 hβ₂0 hnB1

/-- **Prop 6.1, couples, `q > q'`: the separated representation** (TARGET prooflayer1-1). -/
theorem couple_sep_gt {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (hsize : Q.size = 2 * n) (LG : LayeredGarden 2) (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    SepRep (1 - P.η) P.δ (30 * P.d) (30 * P.d) n (timeBox q q')
      (fun ts k => LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k)
      (KJ (1 - P.η) C ^ (n + 1)) (KM (30 * P.d) P.d C ^ (n + 1) * leafSizeProduct LG Bd) := by
  cases Q with
  | triv => exact couple_sep_type1 P O hC hd hη1 hqq hnN _ hsize LG hcoh rfl H Bd hH hqp
  | type1 c Q₁ Q₂ Q₃ => exact couple_sep_type1 P O hC hd hη1 hqq hnN _ hsize LG hcoh rfl H Bd hH hqp
  | type2 Xp Xm Qlp =>
    by_cases htop : layerAt LG ((0 : Fin 2), []) = q
    · exact couple_sep_top P O hC hd hL hη0 hη1 hqq hqp hnN Xp Xm Qlp hsize LG hcoh H Bd hH htop
    · exact couple_sep_low P O hC hd hL hη0 hη1 hqq hqp hnN Xp Xm Qlp hsize LG hcoh H Bd hH
        (lt_of_le_of_ne (root_le_type2 hqq.le hcoh) htop)

end Top

end WaveTurbulence.PL234
