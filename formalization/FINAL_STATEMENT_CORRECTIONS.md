# Applied final statement corrections

[FINAL_STATEMENT_CORRECTIONS.patch](FINAL_STATEMENT_CORRECTIONS.patch) is
approved by the user on 2026-10-10 and applied to both TeX files. The
source statement mappings and hashes are reviewed and refreshed.

The patch makes two changes.

1. In `cor:uniform-polynomial`, add **for all sufficiently large n**. The
   corollary's existing proof already uses this condition to obtain the
   uniform logarithmic-degree threshold. The checked target
   `UniformPolynomialSmallestSingularTheorem` supplies one absolute positive
   probability constant before quantifying over epsilon, then one exponent
   depending on epsilon and an eventual dimension threshold uniform over
   every allowed degree and spectral shift. It is proved by
   `uniform_polynomial_smallest_singular_theorem`. The corrected printed statement includes that asymptotic condition
   and is counted as a completed literal result.

2. In the proof of `prop:Bernoulli-hermitization`, remove the rounded `T2`
   formula and its false deterministic upper comparison. Use the proved
   convergence of the actual minor prefix `T` directly. The named
   proposition's hypotheses and conclusions do not change. The counterexample
   in [HERMITIZATION_REVIEW.md](HERMITIZATION_REVIEW.md) checks failure of
   the old comparison on an actual positive-probability Bernoulli sample.

The replacement retains the exact manuscript floors for `m` and `ell`,
the actual ambient normalization `d^(-1/2)`, and denominator `n` for both
prefixes. At minor ratio `r`, the Gaussian singular scale is `sqrt(r)`;
the normalized limiting negative logarithmic value is

```
r * (U_circle(z/sqrt(r)) - log(r)/2).
```

This tends to the full circular potential as `r` tends to one. The checked
minor Gaussian small-value and support estimates control logarithmic
clipping; the actual minor second moment controls positive tails. A common
slow choice of the prefix fraction enforces the clipping errors, both
prefix limits and the already proved exposure upper estimate. The exact
proof is `bernoulli_common_minor_log_prefix_with_constraints`, with the
complete full-log assembly in `bernoulli_hermitization_theorem`. No estimate
for the removed `T2` expression is used.

The other final quantitative result, `prop:LLY-smallest`, needs no source
correction. `lly_smallest_singular_theorem : LLYSmallestSingularTheorem`
proves it for every admissible dimension: enlarging its absolute degree
coefficient excludes the finite initial segment. Both exponents are
`(2*llySourceLoglogRatioConstant+12)*log(log(n))`, strictly above two and
with the required common upper bound. Both probabilities use the actual
matrix laws and the literal non-strict singular-value event. The model's
`1 <= d <= n` convention means its degree window has `n >= 2`.

The tensorization correction approved on 2026-10-10 is already applied
and is separate from these final corrections. The corrected October
manuscript PDF has been regenerated from the current TeX sources.
