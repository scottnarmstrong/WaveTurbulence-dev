# Packets V1 + V2 SUMINT (pre-freeze) — prove the Wave B statement `sumint` (TARGET Prop `sumint`, L1595–L1722)

Read `COMMON.md` first. `sumint` (B1.6) is in the Wave B freeze set; its exact drafted statement and datum
(`SumintShape`, the `XNorm00` restriction norm, size hypothesis M ≤ N₁⁴, all Λ_v ≥ 1, shifts per Q9) are in
`/home/scott/wt-scratch/waveb-snap-5/WaveB1-Sumint.lean` (+ `WaveB1-System.lean` for the norms). Prove it, in scratch
`/home/scott/wt-scratch/sumint/` against a local copy of snapshot 5, under your own name with exactly the drafted type
(after the freeze it moves to Foundations and the orchestrator seals the anchor). Blueprint rows `T.sumint.S1`–`S3`,
`GAP.sumintD`, `T.sumint`; map `maps/T-part2.md` (`sumint` entry; Q5 = FINDINGS F23: case (d) for γ > 8/9 needs the
second `lemlin` bound — landed by wt-cumul in `Foundations/LemLin/**`; an extra δ^{−1/2} per bad vine; the extension
behind 𝔛(ℬ) is unspecified; typos L1615, L1687).
Landed inputs (import): `Foundations/LemLin/**` (lemlin + F23 bound, lemcubic0), `Foundations/WeylSums/**` (lemlayer2,
lemcubic in the drafted forms), `Foundations/NTSP/**` (TARGET Lemma 5.2 = lemlayer1), `Foundations/Fourier/**` (your
χ₀, Gevrey, time-Fourier norms incl. `mixedFourierNorm00` over V by wt-cumul, Fourier-L¹ products, Hausdorff–Young,
interpolation); the norm bridges `XNorm00 = mixedFourierNorm00` are in `/home/scott/wt-scratch/norm-bridge/` (wt-cumul).
Goals (do not end your turn at milestones): Step 1 (localization, Fourier expansion of the weights), Step 2 (the L^∞
bound by factorization over i and the gains (a)–(d)), Step 3 (passage to 𝔛^{2η⁸,0,0}(ℬ): shifts, L^{−β} partitions,
domain enlargement, Plancherel, interpolation, the explicit extension), and the assembly with exactly the drafted type.
Done: `READY sumint`.
