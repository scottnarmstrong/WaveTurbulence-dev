# Scalar clamped-clock Fourier checkpoint

Proof author: Terra-medium v5_w13. Recorded 2026-11-06 03:01 UTC.

For every0<a<1 and epsilon>0, localClampMode_weighted_mass constructs K depending only on a and epsilon, nonnegative, with the full angular Fourier mass weighted by(1+abs frequency)^a bounded by K*(1+abs mode)^(a+epsilon) for every real mode. Global integrability is proved internally; no integrability or desired-bound premise is assumed. It combines continuous central frequencies and both dominated tails, with exact interval-IBP identity and separate smooth/resonant frequency estimates. This is an auxiliary mode estimate, not VINEEST or TermCertW.

The cutoff was widened before the actual full adjacent-cell restriction: inner7/4, outer9/4 around1/2, plateau[-5/4,9/4] containing[-1,2] with margin, support inside[-2,3]. Earlier exact cutoff sources are separately preserved. All31 dependent modules rebuilt sequentially, and the later scalar/negative/smooth integrability/mass modules compiled. The preserved SmallMode log records an additional later successful rebuild, as documented by its author. The scalar axiom source is preserved verbatim as AxClampScalar.lean.txt together with the completed log and runner; three checked exports have only propext, Classical.choice and Quot.sound.

Root independently verified/copies all74 source/evidence pins into /home/scott/wt-scratch/codex-takeover/root-checkpoints/20261106-025900-CLAMP-SCALAR. Root inspected the exact conclusion/binders, global-domain assembly and audit output; this is a bounded helper review, not an independent full source-theorem audit. Native2pi normalization, zero-weight bound, two-coordinate additive-weight lift, full adjacent rectangle agreement, same source-denominator extraction, operative W13 certificate, modulation/R57 final prefix and canonical integration remain outside this checkpoint. Some native scalar ingredients have since compiled separately; no2D/source certificate closure is claimed here.

READY scalar helper checkpoint; V5 source endpoint remains open.
