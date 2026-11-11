# Correspondence with Erdős Problem 736

## Original problem

The original assertion asks whether a graph `G` of chromatic number `aleph_1` admits, for every cardinal `m`, a graph `H` of chromatic number `m` such that every finite ordinary subgraph of `H` occurs in `G`.

The source is Paul Erdős, *On the combinatorial problems which I would most like to see solved*, Combinatorica **1** (1981), 25–42, the Taylor-conjecture paragraph on printed page 14 of the author scan. It is listed as [Erdős Problem 736](https://www.erdosproblems.com/736) and corresponds to [JSP-000604](https://github.com/TheJustinSunPrize/awards/blob/f8801a856529dce27e738c6b305e46d76e7c387c/problems/catalog-0601-0700.md#JSP-000604).

## Formal statement

`Erdos736.erdos_736` in [Erdos736.lean](Erdos736.lean) proves the negation of the full assertion. `StatementCheck.OriginalAssertion` in [StatementCheck.lean](StatementCheck.lean) writes out the ordinary finite-copy quantifiers independently. `StatementCheck.original_assertion_false` proves its negation directly from the main theorem.

| Mathematical requirement | Formal representation and check |
| --- | --- |
| Simple undirected graphs of arbitrary cardinality | `SimpleGraph V`, where `V : Type u` and the theorem is polymorphic in `u`. |
| Exact chromatic cardinal | `Erdos736.chromaticCardinal`; `chromaticCardinal_spec` proves attainment and `chromaticCardinal_le_iff` characterizes upper bounds by proper colorings. |
| Host chromatic number exactly `aleph_1` | `Erdos736.ActualHost.small_chromaticCardinal`, with both the rank-coloring upper bound and the diagonal noncolorability lower bound proved. |
| Every target cardinal | `∀ m : Cardinal.{u}` in `Erdos736.erdos_736`. The counterexample uses the successor of the continuum. |
| Finite ordinary subgraphs | `ContainsCopy` uses injective adjacency-preserving maps. `StatementCheck.OriginalAssertion` expands this into the map, injectivity, and edge-preservation conditions. |
| All finite graph types | The quantifier ranges over every `U : Type u` with a `Fintype` instance and every `F : SimpleGraph U`. |
| Containment direction | A copy of `F` in `H` implies a copy of `F` in `G`. `finiteAgeIncluded_iff` proves its equivalence to the finite-restriction formulation used in the compactness proof. |
| Unconditional ZFC counterexample | `Erdos736.full_solution` constructs the host and bounds every compatible `H` by the continuum. The final theorem has no auxiliary mathematical hypotheses. |

The original problem restricts the host's chromatic number. It imposes no `aleph_1` bound on the number of host vertices. The construction is therefore permitted by the original statement.

The formalization's memory functions have values on the entire transitive base. It stores the ordinal height explicitly, chooses an arbitrary eligible predecessor at each label, and uses sufficient coordinate inequalities. These representation choices are all proved adequate within the construction.

## Proof coverage

1. Hereditarily countable vertex data form a set. Their codes are injective, and predecessor membership strictly decreases rank.
2. Rank gives an `aleph_1` coloring. Every individual label layer is bipartite.
3. The coordinate-walk argument excludes short odd closed walks with the explicit widths `4(s+1)^2+1`.
4. Countable closure supplies transitive bases, strict ordinal heights, and the diagonal vertex.
5. Prefix reflection and gap selection produce an eligible predecessor of the same proposed countable color.
6. Every countable coloring fails. Together with the upper bound, this proves exact chromatic number `aleph_1`.
7. Compactness transfers the finite odd-walk colorings to every graph with the required finite copies. A combined coloring and a binary fiber coloring give the continuum bound.
8. The successor of the continuum contradicts the universal Taylor assertion.

## Trust and review

The axiom audit reports the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. These are disclosed dependencies. The submitted proof introduces no mathematical axiom in place of a missing step. Local build, statement, and kernel checks are recorded separately from official mathematical and prize review.
