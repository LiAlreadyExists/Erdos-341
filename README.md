# Lean verification of Erdős Problem 341

(With the help of GPT-5.6 Sol)

The main kernel-checked theorem for the fixed seed is:

```lean
Erdos341.erdos_341_negative
```

It verifies, for the fixed seed

```text
{1, 2, 3, 5, 7, 13, 22, 27, 28, 32, 36, 40,
 47, 48, 52, 63, 71, 77, 81, 89, 97},
```

all of the following:

- the exact scale-eight controller identities;
- the complete modulus-49 residue and carry certificate;
- all pair sums, including equal summands;
- the prescribed finite seed with no retroactive greedy condition;
- the exact least-admissible-next-term rule after the seed;
- non-eventual-periodicity of the resulting consecutive gap sequence.

The main kernel-checked theorem for the uniform modulus-`7p` family is:

```lean
Erdos3417p.theorem_5_1_nonperiodicity
```

For every natural number `p ≥ 18`, it verifies the explicit seed predicate
`Erdos3417p.Seed p`, its exact greedy extension `Erdos3417p.S p`, the
least-admissible-next-term rule after the seed, and the quantified assertion
that the consecutive gaps have no eventual period. The separate elementary
cardinality identity `|A_p| = 7p - 20` is not part of this formalization.

## Files

- `LeanProject/Erdos341.lean`: controller, exact greedy semantics,
  enumeration, gap-periodicity bridge, and fixed-seed final theorem.
- `LeanProject/Erdos341Shield.lean`: kernel-evaluated finite residue
  certificate and the general modulus-49 shield theorem.
- `LeanProject/Erdos341g.lean`: The uniform modulus-`7p`
  construction and nonperiodicity theorem. It imports `Erdos341.lean` for the
  controller and general enumeration lemmas.
- `LeanProject.lean`: project build target; it imports both formalizations and
  prints the axiom dependencies of their final theorems.
- `lean-toolchain`: pinned Lean version.
- `lakefile.toml` and `lake-manifest.json`: pinned Mathlib dependency graph.

## Verify

From the repository root, run:

```bash
lake exe cache get
lake build
```

```text
'Erdos341.erdos_341_negative' depends on axioms:
[propext, Classical.choice, Quot.sound]

'Erdos3417p.theorem_5_1_nonperiodicity' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

These are standard Lean/Mathlib logical axioms. The proofs contain no `sorry`, `admit`, custom axiom, or `native_decide` invocation. The fixed finite certificates use kernel `decide`; the uniform family is proved symbolically for arbitrary `p ≥ 18`.
