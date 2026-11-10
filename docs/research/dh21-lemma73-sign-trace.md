# F61: tracing the Z-factor sign (DH21 Lemma 7.3 vs Lemma 5.8), for J3/MAINCOEF

Date 2026-11-04. Worker wt-wke (w/jr-ops).

Sources:
- DH21 = `references/src-2104.11204/Inventiones-Final_Version.tex`;
- TARGET = `paper/source/WKE-Longer_times_Final_arXiv.tex`;
- B2 = `<scratch>/waveb2/WaveB2-Regular.lean`, sha256 `ad72ce4b…c3c53`.

## 1. The kernel (direct computation and machine check)

For `I_β f(t) = ∫_0^t e^{πiβs} f(s) ds`, the composition is
`I_a I_b f(t) = ∫_0^t f(s) e^{πibs} (e^{πiat} − e^{πias})/(πia) ds`. With `a = εα` and `b = μ − εα`, its kernel is

    e^{πiμs} (e^{πiεα(t−s)} − 1)/(πiεα)  =  [e^{πiμs} e^{πiεα(t−s)}]/(πiεα)  −  (1/(επiα)) · e^{πiμs}.

So the `χ_∞` part contains **`−χ_∞(α)/(επiα) · I_μ`**. This is:
- DH21 Lemma 5.8's own term `II = −χ_∞(εα₁)/(επiα₁) J_{0;0,μ₁}` (L1075–L1076);
- the machine-checked `T₀ μ α = −iker μ` on the triangle, in Lean `iker_comp_decompP`
  (`Foundations/ClassJR/Lemma58.lean`, landed a5a86c4).

Lean Lemma 5.10 (`lemma510`, `Chain2.lean`) then gives
`I_{β₁+λ₁}⋯I_{β_{2m}+λ_{2m}} = Σ_{Z⊆adj} ∏_{j∈Z} χ_∞(α_j)/(ε_jπiα_j) · Ĩ_Z`. In `Ĩ_Z` the factor of an adjacent pair
`j ∈ Z` is `T0 = −I_{μ_j}` (`piece58`), and the factor of `j ∉ Z` is `TR58 = I_{εα}I_{μ−εα} + Φ(εα)·I_μ`.

## 2. DH21 Lemma 7.3 (L1732–L1746) misses a sign

- The proof writes `I_{ε_jα_j}I_{μ_j−ε_jα_j} = χ_∞(α_j)/(ε_jπiα_j) I_{μ_j} + 𝒥 + ℛ` (**+**), and takes the `j`-th
  factor of `Ĩ` to be `I_{μ_j}` for `j ∈ Z`.
- With the correct `−I_{μ_j}`, `Ĩ` contains `∏_{j∈Z}(−I_{μ_j})`.
- The `[G]`-integral of each `j ∈ W` factor `TR58_j` is unchanged:
  - `[G]∫ I_{εα}I_{μ−εα} dα = I_μ` by (approxid);
  - `[G]∫ Φ(εα)·I_μ dα = 0` by oddness.
- Hence the correct (regchaincalref) is

      ∫ K̃(α[W]) dα[W] = (−1)^{|Z|} ∫_{t>t_1>⋯>t_m>0} e^{πi(μ_1t_1+⋯+μ_mt_m)+πiλ_0t_m} dt.

## 3. Propagation in DH21 §7, and the Ω convention (the second sign source) does not compensate

- **Prop 6.7 (asymptotics1, L1665–L1700).** `K_{Q,Z} ≈ 2^{−2n}δ^n ζ*(Q) ∏_{𝔫∈Z} 1/(ζ_𝔫πi) · 𝒥B̃_{Q,Z} · M*_{Q,Z}` is
  correct as stated, for whatever value `𝒥B̃_{Q,Z} = ∫ B̃_{Q,Z} dα` takes.
  - (newsum1) substitutes `x_𝔫 = k_{𝔫₁} − k_𝔫` and `y_𝔫 = k_𝔫 − k_{𝔫₃}`, so `Ω_𝔫 = 2⟨x_𝔫, y_𝔫⟩` (by (res)).
  - This is the same `Ω_𝔫` as in `α_𝔫 = δL²Ω_𝔫`, and the same one appearing as `1/Ω_𝔫` in (defintegral).
    (Equivalently `Ω = −2⟨k₁−k, k₃−k⟩`, the audit's form: the same quantity.)
  - So `χ_∞(δL²Ω)/(ζπi δL²Ω) → (1/(ζπi))·p.v.(1/Ω)` carries **no** compensating sign.
- **Prop 7.5 (regcplcal, L1767–L1807).** "𝒥B̃_{Q,Z} independent of Z" is false.
  - Inductively, type 1 multiplies the `(−1)^{|Z_j|}`; type 2 contributes `(−1)^{|Z^+|+|Z^-|}` from Lemma 7.3.
  - So `𝒥B̃_{Q,Z} = (−1)^{|Z|} 𝒥B̃_Q`, with `𝒥B̃_Q` given by (recurtype1)/(recurtype2).
- **Prop 7.6 (domasymp1, (reducedom)).** The weight should be `∏_{𝔫∈Z} (−1)/(ζ_𝔫πi)`.
- **Prop 7.8 (nonemptyZ).** Still true. `|Z|` is constant on an equivalence class (DH21 says so in the proof), so the
  corrected weight is `(−1)^{|Z|}` times the stated one, a common factor on each class.
- **Props 7.9–7.10 and the main theorem.** Unaffected. The `Z = ∅` terms have no sign, and the `Z ≠ ∅` classes cancel
  either way.

## 4. TARGET and B2

- **TARGET (regref1-3) (L1154).** `(K*_Q)_app = 2^{−2n}δ^n ζ(Q) Σ_Z ∏_{𝔫∈Z} 1/(ζ_𝔫πi) 𝒥ℬ*_Q M*_Qs` with `𝒥ℬ*`
  Z-independent. This copies DH21 (reducedom) and is off by `(−1)^{|Z|}` **per (Q,Z) term**.
  - (regref2-3) and (regref1-5) remain true.
  - The per-couple remainder bound (regref1-1) for `R*_Q = K*_Q − (K*_Q)_app` is then **false** for dominant `Q` with
    odd `|Z|` terms, since `M*_{Q,Z} ≢ 0`.
- **B2 `RegCpl.app` / `RegChain.app`** (`specialWeight σ Z = ∏_{z∈Z} (ζ_z π i)⁻¹`, Z-independent `JB`,
  `pvResonantIntegral` with the same Ω) inherit the error.
  - B2.1 item (1) (`regularAsymptotics`, per couple) would be a false frozen statement.
  - **Fix:** `specialWeight σ Z = ∏_{z∈Z} (−ζ_z π i)⁻¹`, i.e. TARGET (regref1-3) with `∏_{𝔫∈Z} (−1)/(ζ_𝔫 π i)`. The
    tree version must be fixed in the same way.

QUESTION (to the source authors / orchestrator): DH21 Lemma 7.3 (L1737) writes `+χ_∞(α_j)/(ε_jπiα_j) I_{μ_j}`, but
the composition kernel (and DH21 Lemma 5.8's own term II) gives `−χ_∞(α_j)/(ε_jπiα_j) I_{μ_j}`. Hence
`𝒥B̃_{Q,Z} = (−1)^{|Z|}𝒥B̃_Q`, and the per-couple leading term in DH21 (reducedom) / TARGET (regref1-3) needs
`∏_{𝔫∈Z}(−1)/(ζ_𝔫πi)`. Is there a convention (e.g. for `Z`, `ζ_𝔫` on chains, or `Ω`) under which the printed sign is
correct? I find none: (newsum1) uses the same `Ω_𝔫 = 2⟨x_𝔫,y_𝔫⟩` as `α_𝔫`.
