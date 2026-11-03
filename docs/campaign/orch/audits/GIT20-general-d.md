# Audit: the claimed general-d proof of the GIT20 trilinear estimate (Task 5, refute-first)

Auditor: `wt-orch`. Date: 2026-11-03.

**Object.** `docs/research/git20-general-d.md` (main `69cbfbe`, 253 lines), Theorem 7:
‖𝒦_j(φ₁,φ₂,φ₃)‖_{Z_s} ≤ C(d,s)∏‖φ_i‖_{Z_s} for all d ≥ 3, s > d/2 − 1, j = 0,…,3. This is TARGET (schappend8), L2516.
It also claims (§10) that the blow-up clause of the frozen `wkelwp` follows through Appendix C.

**Method.**

- I re-derived every step by hand: each change of variables and Jacobian, each Hölder exponent window, and each
  AM–GM pairing.
- I checked the normalization against the frozen `collisionOp`, the four 𝒦_j against (schappend1–4), the sharpness
  claims, and the Appendix C passage.
- I checked the worst-case uniform integral numerically with an independent quadrature script (scratchpad, outside
  the repo).

## Verdict: **CORRECT** (Theorem 7 and §8.1–§8.2), with no mathematical fix needed

§10's passage to the blow-up criterion is correct. It needs three routine supporting lemmas that the note does not
list (§3 below). These are formalization obligations, not gaps. §9 (the repair of GIT's own route) is off the proof
route, and I did not audit it.

## 1. Step-by-step check

| Step | Claim | Check | Status |
|---|---|---|---|
| §0 normalization | δ(2⟨ℓ₁,ℓ₃⟩)dℓ₁dℓ₃ := ∫(2\|ℓ₁\|)⁻¹∫_{ℓ₁^⊥}·dσ dℓ₁ | Identical to the frozen `collisionOp` (Task 1 §1a; Foundations `tendsto_mollified_collisionOp_k` confirms it is the delta of the *unscaled* Ω). | ✓ |
| §0 the four terms | 𝒦₁ = φ₁(k)Q₁(φ₂,φ₃), 𝒦₂ = φ₂(k)Q₂(φ₁,φ₃), 𝒦₃ = φ₃(k)Q₁(φ₂,φ₁) | From (schappend2–4) with k₁ = k+ℓ₁, k₃ = k+ℓ₃, k₂ = k+ℓ₁+ℓ₃. For 𝒦₃, the ℓ₁ ↔ ℓ₃ swap (Lemma 1) gives φ₁(k+ℓ₃)φ₂(k+ℓ₁+ℓ₃) = the Q₁(φ₂,φ₁) integrand. | ✓ |
| §0 reduction to φ ≥ 0 | \|𝒦_j(φ)\| ≤ 𝒦_j(\|φ\|) | Each 𝒦_j is a positive trilinear form. Finiteness of the RHS gives absolute convergence (every k for j ≥ 1, a.e. k for j = 0). | ✓ |
| Lemma 1 (symmetry) | ∫\|a\|⁻¹∫_{a^⊥}F dσ(b)da = ∫\|b\|⁻¹∫_{b^⊥}F dσ(a)db | ε-slab limit: b = t·â + y, \|a·b\| < ε ⟺ \|t\| < ε/\|a\|, giving (2ε)⁻¹∫ → Φ_a(0)/\|a\|. Dominated by ‖F‖_∞\|B^{d−1}_L\|\|a\|⁻¹1_{\|a\|≤L} ∈ L¹ (d ≥ 2). The slab is swap-invariant. Both sides are locally finite and agree on C_c, hence are equal. | ✓ |
| Corollary 2 (polar form, ν symmetric) | weight ρ^{d−2}r^{d−2} | da = ρ^{d−1}dρdφ with \|a\|⁻¹ gives ρ^{d−2}. In φ^⊥ ≅ ℝ^{d−1}, dσ(b) = r^{d−2}dr dσ_φ(θ). Symmetry: Lemma 1 applied to G(â,b̂)η(\|a\|)η(\|b\|) with ∫η ρ^{d−2} = 1. | ✓ |
| A_k finite | ∫₀^∞⟨k+ρθ⟩^{−2s}ρ^{d−3}dρ < ∞ | Near 0: ρ^{d−3} is integrable (d ≥ 3). Near ∞: ρ^{d−3−2s}, integrable iff 2s > d−2. | ✓ |
| Lemma 3 | ∫f(k+ρθ)ρ^{d−2} ≤ Γ_f A_k^{1/2} | Split ρ^{d−2} = ρ^{(d−1)/2}·ρ^{(d−3)/2}; ∫_SΓ² = ‖f‖²_{Z_s} for every centre k. | ✓ |
| Lemma 4(a), M₂ | sup_{k,φ}∫_{S∩φ^⊥}A_k dσ_φ < ∞ | Polar coordinates in φ^⊥ give ρ^{d−3}dρdσ_φ = \|u\|⁻¹du_{d−1}, and \|k+u\| ≥ \|P_{φ^⊥}k+u\|. Exponents: p > d−1 ⟺ p′ < (d−1)/(d−2), and we need p′ > (d−1)/(2s); the window is nonempty ⟺ 2s > d−2. The \|u\| < 1 part is finite since d−1 ≥ 2. *Simpler:* both factors are radially decreasing in ℝ^{d−1}, so by rearrangement the supremum is the k′ = 0 value, \|S^{d−2}\|∫₀^∞(1+r²)^{−s}r^{d−3}dr. | ✓ |
| Lemma 4(b), M₁ | sup_{k,θ}∫_S A_k(θ′)/\|sin∠(θ,θ′)\| dθ′ < ∞ | u = ρθ′ gives ρ^{d−3}dρdθ′ = \|u\|⁻²du and 1/\|sin\| = \|u\|/\|u_⊥\|, so the kernel is \|u\|⁻¹\|u_⊥\|⁻¹. Near 0: R^{d−3}sin^{d−3}ψ, integrable for d ≥ 3. f₂ ∈ L^p ⟺ d/2 < p < d−1, i.e. p′ ∈ ((d−1)/(d−2), d/(d−2)); we need p′ > d/(2s), and d/(2s) < d/(d−2) ⟺ 2s > d−2. The window is nonempty for every d ≥ 3 (at d = 3: p ∈ (3/2, 2)). The bound is uniform in k (translation) and θ (rotation). | ✓ |
| Prop 5, Q₂ | Q₂ ≤ ½M₂‖g‖‖h‖ for every k | Q₂ = ½∬𝒢(φ)ℋ(θ)dν. Pair Γ_g(φ) with A(θ)^{1/2} and Γ_h(θ) with A(φ)^{1/2}. The first AM–GM term disintegrates over θ ∈ S∩φ^⊥ (≤ M₂‖g‖²); the second needs the ν-swap (≤ M₂‖h‖²). Optimizing λ gives ½M₂. | ✓ |
| Prop 6, Q₁ | Q₁ ≤ ½(c_{d,s}M₁)^{1/2}‖g‖‖h‖ | Lemma 1 (ℓ₃ as the base), then ℓ₃ = tθ ((2t)⁻¹t^{d−1} = ½t^{d−2}), then (t,a) ↦ w = tθ+a on the half-space w·θ > 0 (dw = dt dσ). Cauchy–Schwarz gives N² = ∫⟨k+w⟩^{−2s}(𝒮h)². The change w ↦ (w·θ, w·θ′, P_V w) has \|det\| = \|sin∠(θ,θ′)\| (parallelogram area), and ∫_V⟨k+x+v⟩^{−2s}dv ≤ c_{d,s} uniformly (c_{d,s} < ∞ ⟺ 2s > d−2). The final AM–GM uses the symmetry of 1/\|sin\|. | ✓ |
| §5 weight transfer | \|k\|² ≤ \|k₁\|² + \|k₃\|² on the resonant set | For ℓ₁ ⊥ ℓ₃: \|k+ℓ₁\|² + \|k+ℓ₃\|² = \|k\|² + \|k+ℓ₁+ℓ₃\|² (energy conservation). Hence ⟨k⟩² ≤ ⟨k₁⟩² + ⟨k₃⟩² and ⟨k⟩^s ≤ 2^{s/2}(⟨k₁⟩^s + ⟨k₃⟩^s). | ✓ |
| Prop 7a, gain Schur test | Λ ≤ C_Q‖F₁‖‖F₄‖‖f₂‖_{Z_s}‖f₃‖_{Z_s} | The F₄² term is ∫F₄²Q₁(f₂,f₃). For the F₁² term: k = k₁−a for fixed (a,b), then a ↦ −a (preserves a^⊥), giving ∫F₁²Q₁(f₃,f₂). Optimizing λ gives C_Q. L² duality for nonnegative functions. | ✓ |
| Gain conclusion | ‖𝒦₀‖_{Z_s} ≤ 2^{1+s/2}C_Q∏‖φ_i‖ | Positivity plus weight transfer, and 𝒦₀(φ₁,φ₂,F) = 𝒦₀(F,φ₂,φ₁) by Lemma 1 (φ₂ sits at k+ℓ₁+ℓ₃, which is symmetric). | ✓ |
| Theorem 7 | all j | j = 1, 3: ‖φ₁‖_{Z_s}·sup_k Q₁. j = 2: ‖φ₂‖_{Z_s}·sup_k Q₂. j = 0: as above. | ✓ |
| §8.1 scaling | ratio ∼ λ^{d−2−2s} | The resonant measure scales as λ^{2d−2}, and ‖f(·/λ)‖_{Z_s} ∼ λ^{s+d/2}. | ✓ |
| §8.2 endpoint | at s = d/2−1, Q₁(h,·), Q₂(·,h) = ∞ | h = ⟨x⟩^{−(d−1)}log^{−1}(2+\|x\|): ‖h‖²_{Z_{d/2−1}} = ∫⟨x⟩^{−d}log^{−2} < ∞, while every affine-hyperplane integral behaves like ∫dr/(r log r) = ∞. | ✓ |
| §8.3 d = 2 | loss bound fails | g = \|u\|⁻¹log⁻¹(1/\|u\|) on \|u\| < ½ is in L² with divergent radial integrals (ρ^{d−2} = 1). The Fatou and indicator argument is fine. Irrelevant for DH (d ≥ 3). | ✓ (cursory) |

**Exponent bookkeeping as s ↓ d/2−1, for large d.** Every condition reduces to the single inequality 2s > d−2:

- A_k < ∞;
- c_{d,s} < ∞;
- the M₂ window (d−1)/(2s) < (d−1)/(d−2);
- the M₁ window d/(2s) < d/(d−2).

No hidden lower bound on s − (d/2 − 1) appears for large d. The constants blow up only as s ↓ d/2−1, which is
expected and allowed (C = C(d,s)).

## 2. Numerical check (independent script, numpy quadrature)

The M₁ integral I(k,θ) = ∫_{ℝ^d}⟨k+u⟩^{−2s}\|u\|⁻¹\|u_⊥\|⁻¹du at s = d/2 − 1 + 0.05:

| d | aligned k = −Rθ, R = 0 / 1 / 10 / 10² / 10³ / 10⁴ | perpendicular k ⊥ θ, R = 0 / 10 / 10³ |
|---|---|---|
| 4 | 178 / 175 / 144 / 102 / 66.4 / 37.7 | 178 / 135 / 58.2 |
| 6 | 230 / 227 / 193 / 137 / 88.4 / 48.8 | 230 / 180 / 76.0 |
| 8 | 223 / 221 / 191 / 136 / 87.4 / 47.9 | 223 / 178 / 74.7 |

The integral is bounded and decreasing in R in both alignments, with the maximum at k = 0, so it is uniform as
claimed. GIT's sup_θ A_k ∼ R^{d−3} would be unbounded here.

My values include the factor \|S^{d−2}\|. The note's sanity numbers (16.1 at d = 4) appear to omit part of this
normalization. That is immaterial.

## 3. The passage to the blow-up criterion (§10)

The Appendix C argument goes through for all d ≥ 3 with Theorem 7:

- Picard local well-posedness in Z_s, with T ≳ (C‖φ₀‖²_{Z_s})⁻¹;
- the Z_{s,m} trilinear bounds;
- the Gronwall induction (schappend10);
- equality of all τ_max^{(s,m)};
- the full limit (not only limsup) from the local existence time. This matches my Task 2 analysis and the frozen
  ∀M ∃τ₀ form.

Three supporting facts are used implicitly. None is in doubt, but each should be a node:

1. **Leibniz (schappend6) and the weight identity (schappend7) for Z_{s,m} inputs, not only Schwartz ones.** DH's
   induction applies them to the Z_{s,m} solution. The landed Foundations versions (`hasFDerivAt_collisionTerm`,
   `weight_collisionTerm_zero`) are for Schwartz or decaying continuous inputs. Extend them by density of 𝒮 in Z_{s,m}
   and the continuity that Theorem 7 provides.
2. **Equivalence of the Lean solution class `IsWKESolution` with the Z_s mild solution.** This class is continuous into
   𝒮 with a pointwise ODE. Passing between the two needs τ ↦ 𝒦(φ(τ))(k) to be continuous for fixed k, i.e. a
   *pointwise* bound. The landed weighted-L^∞ estimate `abs_collisionTerm_le` (s > 2d), together with telescoping,
   supplies it for Schwartz-valued curves. The Z_s estimate alone does not.
3. **𝒮 = ⋂_{s,m} Z_{s,m} with equivalent topologies** (weighted Sobolev embedding). This is standard.

**Remark (agreeing with the note's §10).** The criterion "for every s > d/2−1" genuinely needs the Z_s estimate down to
the threshold. A bound valid only for s ≥ s₀ would give the clause only for s ≥ s₀. Theorem 7 removes that obstacle,
so FINDINGS F32 can be closed **on the mathematics**. The formalization still needs Theorem 7 and items 1–3 above.

## 4. Not audited

- **§9.** The repair of GIT's own route ((bil7) via Lemma 4(b), and the Fourier/Strichartz kernel bound (ma13)). It is
  not used by Theorem 7's proof.
- **§11.** The literature search.

## 5. Notes for the Lean route

- **Lemma 1** is the only measure-theoretic input. In Lean the hyperplane integral is over the dependent subtype
  `↥(ℝ ∙ ℓ₁)ᗮ`. The landed `sliceEquiv` and `integral_eq_integral_slice` (`Foundations/WKE/Hyperplane.lean`) give the
  slab decomposition the ε-limit proof uses. Alternatively, prove symmetry directly from the mollifier
  characterization `tendsto_mollified_collisionOp_k`, which is symmetric in (k₁, k₃) by inspection. That may be
  shorter.
- **The reduction |𝒦_j(φ)| ≤ 𝒦_j(|φ|)** for the Lean iterated Bochner integral needs the inner integrability for
  a.e. ℓ₁ and the outer integrability. These follow from the finiteness that Theorem 7 gives for the nonnegative
  integrals, plus measurability of ℓ₁ ↦ ∫_{ℓ₁^⊥}…, which `Hyperplane.lean` provides.
- **Use the rearrangement form of Lemma 4(a)** (an explicit radial integral). It avoids a Hölder step.
