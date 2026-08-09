# Lean verification of Erdős Problem 341

(With the help of GPT-5.6 Sol)

The main kernel-checked theorem is:

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

## Files

- `LeanProject/Erdos341.lean`: controller, exact greedy semantics,
  enumeration, gap-periodicity bridge, and final theorem.
- `LeanProject/Erdos341Shield.lean`: kernel-evaluated finite residue
  certificate and the general modulus-49 shield theorem.
- `LeanProject.lean`: project build target.
- `lean-toolchain`: pinned Lean version.
- `lakefile.toml` and `lake-manifest.json`: pinned Mathlib dependency graph.

## Verify

From this directory, run:

```sh
source "$HOME/.elan/env"
lake build
```

The final axiom audit should report:

```text
'Erdos341.erdos_341_negative' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

These are standard Lean/Mathlib logical axioms. The proof contains no
`sorry`, `admit`, custom axiom, or `native_decide` invocation. Finite
certificates use kernel `decide`.
