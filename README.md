# formal-conformal

A Lean 4 formalization of **Conformal Field Theory**.

## Purpose

This project aims to give fully formal, machine-checked definitions and
theorems from two-dimensional conformal field theory — starting with vertex
algebras and vertex operator algebras (VOAs) — and to build up, over time,
toward the structural results of CFT.

The current state of the library is in [FormalConformal/Basic.lean](FormalConformal/Basic.lean),
which sets up `VertexAlgebra` and `VertexOperatorAlgebra` following
[Gannon06, Definition 5.1.3], with axioms in one-to-one correspondence with
the standard FLM / Kac / Borcherds formulations.

## Authors

This project is developed at **Stony Brook University** by:

- **Jack McCarthy** — graduate student (email: `jack.mccarthy.1` [at] `stonybrook` [dot] `edu`)
- **Fedor Popov** — postdoctoral researcher

## Building

The project uses [Lake](https://github.com/leanprover/lean4/tree/master/src/lake),
the Lean build tool. After installing [elan](https://github.com/leanprover/elan):

```sh
lake exe cache get   # fetch prebuilt Mathlib artifacts
lake build
```

The Lean toolchain version is pinned in [lean-toolchain](lean-toolchain).

## AI disclaimer

Portions of this project — including code, proofs, and documentation — were
drafted or refined with the assistance of Anthropic's **Claude** large
language model.

## License

Released under the Apache 2.0 license. See [LICENSE](LICENSE) for details.
