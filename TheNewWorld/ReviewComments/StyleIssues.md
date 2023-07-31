# Style Guide for `mathlib4`

This is a colection of style comments I received for PRs in `mathlib4`.

1. Operators have spaces on both side:
    * A + B not A+B
    * A colon is an operator
2. [`Usually`] Use lower case letters for indexing types.
3. Spaces between assupmtions i.e.:
 * `[Fintype m][Field K]` becomes `[Fintype m] [Field K]`
4. [`Usually`] Drop namespace prefix from open namespaces.
    * `def A  ... := Matrix.of fun i j => ...` becomes `def A ... := of fun i j => ...`
5. [`Recommend`] Look for simp lemmas. A simp lemma should have the simpler statement on the RHS.
6. "Too much" unfolding indicates some simp lemmas are missing in the API for your type.
7. [`Recommend`] Leave hypothesis and conclusions on separate lines.
