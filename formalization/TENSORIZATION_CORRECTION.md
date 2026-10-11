# Applied tensorization correction

The original manuscript used one identical constant in the event threshold
and its probability bound. The reviewed example in [the development history](DEVELOPMENT_HISTORY.md#tensorization-statement-review) shows that
the literal shared-constant form is false.

[TENSORIZATION_CORRECTION.patch](TENSORIZATION_CORRECTION.patch) records
only two changes inside `lem:tensorization`: require the probability
constant to be positive, and use coefficient one in the squared-radius
threshold. The corrected conclusion is

```
P(sum_i |xi_i|^2 <= tau^2*t^2*K) <= (C*A*tau^2)^K.
```

The existing theorem `tensorization_source_lemma` proves this statement
with `C=4*exp(1)`, including every deterministic shift, independent
complex variables, and nonnegative radii. The concentration hypothesis
is unchanged. The later profile application already uses the compatible
`sqrt(K)*t` scale and remains valid with its positive absolute constants.

The user approved this exact correction on 2026-10-10, and it is applied
to `sections/02_preliminaries.tex`. The source-to-Lean mapping and the
manuscript hashes are updated. The named lemma is now counted as proved
by `tensorization_source_lemma : TensorizationSourceLemma`.

The corrected statement is present in the TeX source, the checked Lean
target, and the regenerated October manuscript PDF.
