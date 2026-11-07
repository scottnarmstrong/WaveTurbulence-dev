/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Lattice
/-! FLOWER-P7: the selection lemma for sums over the outer labels, and the generic configuration bound. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

variable {d : ℕ}

theorem OL_rel0 (n : OuterLabels d) : n.1 0 - n.1 1 + n.1 2 = 0 := n.2 0

theorem OL_rel1 (n : OuterLabels d) : n.1 3 - n.1 4 + n.1 5 = 0 := n.2 1

/-- Selection lemma: a sum over outer labels of `K ∏_{j ∈ F} g(n_j)` on a set `D` on which the labels are
determined by the coordinates in `F` is at most `K (∑ g)^{|F|}`. -/
theorem sum_sel_le (g : (Fin d → ℤ) → ℝ) (hg0 : ∀ m, 0 ≤ g m) (hgs : Summable g)
    (D : (Fin 6 → Fin d → ℤ) → Prop) [DecidablePred D] (F : Finset (Fin 6))
    (hinj : ∀ n n' : OuterLabels d, D n.1 → D n'.1 → (∀ j ∈ F, n.1 j = n'.1 j) → n = n')
    (K : ℝ) (hK : 0 ≤ K) (u : Finset (OuterLabels d)) :
    ∑ n ∈ u, (if D n.1 then K * ∏ j ∈ F, g (n.1 j) else 0) ≤
      K * (∑' m, g m) ^ F.card := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not u (fun n => D n.1)]
  have h0 : ∑ n ∈ u.filter (fun n => ¬ D n.1), (if D n.1 then K * ∏ j ∈ F, g (n.1 j) else 0) = 0 :=
    Finset.sum_eq_zero fun n hn => if_neg (Finset.mem_filter.1 hn).2
  rw [h0, add_zero]
  set u' := u.filter (fun n => D n.1) with hu'
  rw [Finset.sum_congr rfl fun n hn => if_pos (Finset.mem_filter.1 hn).2]
  set π : OuterLabels d → (F → Fin d → ℤ) := fun n j => n.1 j with hπ
  have hinjπ : Set.InjOn π u' := by
    intro n hn n' hn' h
    exact hinj n n' (Finset.mem_filter.1 hn).2 (Finset.mem_filter.1 hn').2 fun j hj => congrFun h ⟨j, hj⟩
  have e1 : ∑ n ∈ u', K * ∏ j ∈ F, g (n.1 j) = ∑ x ∈ u'.image π, K * ∏ j : F, g (x j) := by
    rw [Finset.sum_image hinjπ]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.prod_coe_sort]
  rw [e1]
  set T : Finset (Fin d → ℤ) := (u'.image π).biUnion (fun x => Finset.univ.image x) with hT
  have hsub : u'.image π ⊆ Fintype.piFinset (fun _ : F => T) := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩
  calc ∑ x ∈ u'.image π, K * ∏ j : F, g (x j) ≤ ∑ x ∈ Fintype.piFinset (fun _ : F => T), K * ∏ j : F, g (x j) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => mul_nonneg hK (Finset.prod_nonneg fun j _ => hg0 _))
    _ = K * ∏ _j : F, ∑ m ∈ T, g m := by
        rw [← Finset.mul_sum, ← Finset.prod_univ_sum]
    _ = K * (∑ m ∈ T, g m) ^ F.card := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    _ ≤ K * (∑' m, g m) ^ F.card := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact pow_le_pow_left₀ (Finset.sum_nonneg fun m _ => hg0 m) (hgs.sum_le_tsum T fun m _ => hg0 m) _

/-- The Peetre trichotomy for a difference triple. -/
theorem jbr_tri (x y z : Mom d) :
    jbr (x - y + z) ≤ 3 * jbr x ∨ jbr (x - y + z) ≤ 3 * jbr y ∨ jbr (x - y + z) ≤ 3 * jbr z := by
  have hn : ‖x - y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
    calc ‖x - y + z‖ ≤ ‖x - y‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by gcongr; exact norm_sub_le _ _
  have key : ∀ w : Mom d, ‖x - y + z‖ ≤ 3 * ‖w‖ → jbr (x - y + z) ≤ 3 * jbr w := by
    intro w hw
    unfold jbr
    have h3 : (0:ℝ) ≤ 3 := by norm_num
    rw [show (3:ℝ) * √(1 + ‖w‖ ^ 2) = √(9 * (1 + ‖w‖ ^ 2)) by
      rw [Real.sqrt_mul (by norm_num), show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq h3]]
    apply Real.sqrt_le_sqrt
    have : ‖x - y + z‖ ^ 2 ≤ (3 * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    nlinarith
  rcases le_total ‖y‖ ‖x‖ with h1 | h1 <;> rcases le_total ‖z‖ ‖x‖ with h2 | h2 <;>
    rcases le_total ‖z‖ ‖y‖ with h3 | h3
  · exact Or.inl (key x (by linarith [norm_nonneg x]))
  · exact Or.inl (key x (by linarith [norm_nonneg x]))
  · exact Or.inr (Or.inr (key z (by linarith [norm_nonneg x])))
  · exact Or.inr (Or.inr (key z (by linarith [norm_nonneg x])))
  · exact Or.inr (Or.inl (key y (by linarith [norm_nonneg x])))
  · exact Or.inr (Or.inr (key z (by linarith [norm_nonneg x])))
  · exact Or.inr (Or.inl (key y (by linarith [norm_nonneg x])))
  · exact Or.inr (Or.inr (key z (by linarith [norm_nonneg x])))

theorem tri_labels {L : ℝ} (k : Mom d) (a b c : Fin d → ℤ) (h : a - b + c = 0) :
    (k + latticePoint L a) - (k + latticePoint L b) + (k + latticePoint L c) = k := by
  have : latticePoint L (a - b + c) = 0 := by rw [h, lat_zero]
  rw [lat_add, lat_sub] at this
  calc _ = k + (latticePoint L a - latticePoint L b + latticePoint L c) := by abel
    _ = k := by rw [this, add_zero]

theorem tri_cases {L : ℝ} (k : Mom d) (a b c : Fin d → ℤ) (h : a - b + c = 0) :
    jbr k ≤ 3 * jbr (k + latticePoint L a) ∨ jbr k ≤ 3 * jbr (k + latticePoint L b) ∨
      jbr k ≤ 3 * jbr (k + latticePoint L c) := by
  have := jbr_tri (k + latticePoint L a) (k + latticePoint L b) (k + latticePoint L c)
  rwa [tri_labels k a b c h] at this

theorem gw_le_of_jbr {L : ℝ} (k : Mom d) {a : ℝ} (ha : 0 ≤ a) (m : Fin d → ℤ)
    (h : jbr k ≤ 3 * jbr (k + latticePoint L m)) : gw L k a m ≤ 3 ^ a * jbr k ^ (-a) := by
  unfold gw
  have h1 := WaveTurbulence.Induct.jbr_pos k
  have h2 := WaveTurbulence.Induct.jbr_pos (k + latticePoint L m)
  have : jbr (k + latticePoint L m) ^ (-a) ≤ (jbr k / 3) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [div_le_iff₀ (by norm_num)]; linarith) (by linarith)
  refine this.trans ?_
  rw [Real.div_rpow h1.le (by norm_num), Real.rpow_neg h1.le, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]
  rw [div_eq_mul_inv, mul_comm, inv_inv]

/-- The generic configuration bound: weights `∏_{j∈S} g(n_j)` on a set `D`, with decay from a labelled
case split. -/
theorem cfg_sum {L : ℝ} (hL : 1 ≤ L) (k : Mom d) {a : ℝ} (ha : (d : ℝ) + 1 ≤ a)
    (D : (Fin 6 → Fin d → ℤ) → Prop) [DecidablePred D] (S : Finset (Fin 6))
    (cs : Finset (Fin 6 × Finset (Fin 6)))
    (hz : ∀ c ∈ cs, c.1 ∈ S ∧ c.2 ⊆ S.erase c.1)
    (hinj : ∀ c ∈ cs, ∀ n n' : OuterLabels d, D n.1 → D n'.1 → (∀ j ∈ c.2, n.1 j = n'.1 j) → n = n')
    (hcov : ∀ n : OuterLabels d, D n.1 → ∃ c ∈ cs, jbr k ≤ 3 * jbr (k + latticePoint L (n.1 c.1)))
    (u : Finset (OuterLabels d)) :
    ∑ n ∈ u, (if D n.1 then ∏ j ∈ S, gw L k a (n.1 j) else 0) ≤
      cs.card * (3 ^ a * jbr k ^ (-a)) * (max 1 (∑' m, gw L k a m)) ^ 6 := by
  classical
  have ha0 : 0 ≤ a := by have : (0:ℝ) ≤ d := Nat.cast_nonneg d; linarith
  set M := max 1 (∑' m, gw L k a m) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  set K : ℝ := 3 ^ a * jbr k ^ (-a) with hK
  have hK0 : 0 ≤ K := mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (WaveTurbulence.Induct.jbr_pos k).le _)
  have hpt : ∀ n : OuterLabels d, (if D n.1 then ∏ j ∈ S, gw L k a (n.1 j) else 0) ≤
      ∑ c ∈ cs, (if D n.1 then K * ∏ j ∈ c.2, gw L k a (n.1 j) else 0) := by
    intro n
    by_cases hD : D n.1
    · simp only [hD, ite_true]
      obtain ⟨c, hc, hcov'⟩ := hcov n hD
      have hterm : ∏ j ∈ S, gw L k a (n.1 j) ≤ K * ∏ j ∈ c.2, gw L k a (n.1 j) := by
        obtain ⟨hcS, hcF⟩ := hz c hc
        rw [← Finset.mul_prod_erase S _ hcS]
        have h1 : gw L k a (n.1 c.1) ≤ K := gw_le_of_jbr k ha0 _ hcov'
        have h2 : ∏ j ∈ S.erase c.1, gw L k a (n.1 j) ≤ ∏ j ∈ c.2, gw L k a (n.1 j) := by
          have e := Finset.prod_sdiff hcF (f := fun j => gw L k a (n.1 j))
          have h3 : (∏ j ∈ (S.erase c.1) \ c.2, gw L k a (n.1 j)) ≤ 1 :=
            Finset.prod_le_one₀ (fun j _ => gw_nonneg _ _ _ _) (fun j _ => gw_le_one L k ha0 _)
          have hnn : 0 ≤ ∏ j ∈ c.2, gw L k a (n.1 j) := Finset.prod_nonneg fun j _ => gw_nonneg _ _ _ _
          calc ∏ j ∈ S.erase c.1, gw L k a (n.1 j)
              = (∏ j ∈ (S.erase c.1) \ c.2, gw L k a (n.1 j)) * ∏ j ∈ c.2, gw L k a (n.1 j) := e.symm
            _ ≤ 1 * ∏ j ∈ c.2, gw L k a (n.1 j) := mul_le_mul_of_nonneg_right h3 hnn
            _ = _ := one_mul _
        exact mul_le_mul h1 h2 (Finset.prod_nonneg fun j _ => gw_nonneg _ _ _ _) hK0
      refine hterm.trans ?_
      have := Finset.single_le_sum (f := fun c : Fin 6 × Finset (Fin 6) => K * ∏ j ∈ c.2, gw L k a (n.1 j))
        (fun c _ => mul_nonneg hK0 (Finset.prod_nonneg fun j _ => gw_nonneg _ _ _ _)) hc
      exact this
    · simp [hD]
  calc ∑ n ∈ u, (if D n.1 then ∏ j ∈ S, gw L k a (n.1 j) else 0)
      ≤ ∑ n ∈ u, ∑ c ∈ cs, (if D n.1 then K * ∏ j ∈ c.2, gw L k a (n.1 j) else 0) :=
        Finset.sum_le_sum fun n _ => hpt n
    _ = ∑ c ∈ cs, ∑ n ∈ u, (if D n.1 then K * ∏ j ∈ c.2, gw L k a (n.1 j) else 0) := Finset.sum_comm
    _ ≤ ∑ c ∈ cs, K * M ^ 6 := by
        refine Finset.sum_le_sum fun c hc => ?_
        refine (sum_sel_le (gw L k a) (gw_nonneg L k a) (summable_gw hL k ha) D c.2 (hinj c hc) K hK0 u).trans ?_
        apply mul_le_mul_of_nonneg_left _ hK0
        calc (∑' m, gw L k a m) ^ c.2.card ≤ M ^ c.2.card :=
              pow_le_pow_left₀ (tsum_nonneg fun m => gw_nonneg _ _ _ _) (le_max_right _ _) _
          _ ≤ M ^ 6 := pow_le_pow_right₀ hM1 (by
              have := Finset.card_le_univ c.2
              simpa using this)
    _ = cs.card * K * M ^ 6 := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end WaveTurbulence.FlowerP7
