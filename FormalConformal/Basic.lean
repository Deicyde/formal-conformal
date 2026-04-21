/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Vertex.VertexOperator
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Vertex Operator Algebras

This file formalizes the definition of a vertex algebra and of a vertex operator
algebra (VOA) following the Wikipedia article

  https://en.wikipedia.org/wiki/Vertex_operator_algebra

and the standard references [FLM88], [Kac98], [Borcherds86].

## Main definitions

* `VertexAlgebra R V`: a vertex algebra structure on an `R`-module `V`,
  consisting of a state–field correspondence `Y`, a vacuum vector, a
  translation operator `T`, and the vacuum, creation, translation, and
  locality axioms.
* `VertexOperatorAlgebra R V`: a vertex algebra on an `R`-module `V` over a
  field `R` of characteristic zero, equipped with a conformal element `ω`
  whose modes `L_n := ω_{(n+1)}` satisfy the Virasoro relations with central
  charge `c`, with `L_{-1} = T`, and with `L_0` giving a bounded-below
  `ℤ`-grading on `V`.

## Conventions

For `a ∈ V` the vertex operator `Y(a, z)` is expanded as
$$Y(a, z) = \sum_{n \in \mathbb{Z}} a_{(n)}\, z^{-n-1},$$
so in Mathlib notation `a_{(n)} = (Y a)[[n]] : V →ₗ[R] V`. The conformal element
is expanded as
$$Y(\omega, z) = \sum_{n \in \mathbb{Z}} L_n\, z^{-n-2},$$
so that `L_n = ω_{(n+1)} = (Y ω)[[n+1]]`.

## Implementation notes

Our axiomatisation is equivalent to [Gannon06, Definition 5.1.3], with three
bookkeeping differences:

1. **Grading.** Gannon builds the `ℤ`-grading into the vertex algebra; we
   follow FLM/Kac and attach it only at the VOA level, via `weight` and
   friends.
2. **Translation operator.** We carry `T` as data in `VertexAlgebra` (FLM/
   Kac/Borcherds style); `L_neg_one_eq_T` identifies it with `ω_{(0)}`,
   recovering Gannon's voa3.
3. **Truncation (Gannon's va5).** Automatic: `VertexOperator R V` is built
   on `HahnModule ℤ R V`, whose series have bounded-below support.

The remaining axioms correspond one-to-one (va2↔`Y_vacuum_ncoeff`,
va3↔`Y_creation_regular`+`Y_creation_lowest`, va4↔`locality`,
voa1↔`virasoro`, voa2↔`weight_isEigenspace`, voa4↔`weight_zero_eq_span_vacuum`
+ `weight_neg_eq_bot` + `weight_finiteDimensional`).

## References

* [Wikipedia, *Vertex operator algebra*][wiki]
* [I. Frenkel, J. Lepowsky, A. Meurman, *Vertex Operator Algebras and
  the Monster*, Academic Press, 1988][FLM88]
* [V. Kac, *Vertex Algebras for Beginners*, AMS, 1998][Kac98]
* [R. Borcherds, *Vertex Algebras, Kac–Moody Algebras, and the Monster*,
  PNAS 83 (1986)][Borcherds86]
* [T. Gannon, *Moonshine Beyond the Monster: The Bridge Connecting
  Algebra, Modular Forms and Physics*, Cambridge Univ. Press, 2006][Gannon06];
  see Definition 5.1.3 on p. 318 for the axiomatic definition of VOA adopted
  here (`voa1`–`voa4`).
-/

noncomputable section

open scoped VertexOperator

namespace FormalConformal

/-! ## Vertex algebras -/

/-- A **vertex algebra** over a commutative ring `R` on an `R`-module `V`
consists of:

* a state–field correspondence `Y : V →ₗ[R] VertexOperator R V`, sending
  `a ↦ Y(a, z) = Σ a_{(n)} z^{-n-1}`;
* a vacuum vector `vacuum ∈ V`;
* a translation operator `T : V →ₗ[R] V`;

satisfying the vacuum, creation, translation-covariance, and locality
axioms. -/
structure VertexAlgebra (R V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] where
  /-- The state–field correspondence `a ↦ Y(a, z)`. -/
  Y : V →ₗ[R] VertexOperator R V
  /-- The vacuum vector, often denoted `𝟙` or `|0⟩`. -/
  vacuum : V
  /-- The translation operator `T : V → V`. -/
  T : V →ₗ[R] V
  /-- **Vacuum (identity) axiom**: `Y(𝟙, z) = Id_V`. In coefficients,
  `𝟙_{(n)} = Id` for `n = -1` and `𝟙_{(n)} = 0` otherwise. -/
  Y_vacuum_ncoeff :
    ∀ n : ℤ, (Y vacuum)[[n]] = if n = -1 then (1 : Module.End R V) else 0
  /-- **Creation axiom (regularity)**: `Y(a, z) 𝟙 ∈ V⟦z⟧`. In coefficients,
  `a_{(n)} 𝟙 = 0` for `n ≥ 0`. -/
  Y_creation_regular :
    ∀ (a : V) (n : ℤ), 0 ≤ n → ((Y a)[[n]]) vacuum = 0
  /-- **Creation axiom (lowest term)**: `Y(a, z) 𝟙 |_{z = 0} = a`. In
  coefficients, `a_{(-1)} 𝟙 = a`. -/
  Y_creation_lowest :
    ∀ a : V, ((Y a)[[-1]]) vacuum = a
  /-- The translation operator annihilates the vacuum: `T 𝟙 = 0`. -/
  T_vacuum : T vacuum = 0
  /-- **Translation covariance**: `[T, Y(a, z)] = ∂_z Y(a, z)`. In
  coefficients, `[T, a_{(n)}] = -n · a_{(n-1)}`. -/
  T_Y_commutator :
    ∀ (a : V) (n : ℤ),
      T ∘ₗ ((Y a)[[n]]) - ((Y a)[[n]]) ∘ₗ T =
        (-(n : R)) • ((Y a)[[n - 1]])
  /-- **Locality axiom**: for every `a, b ∈ V` there exists `N : ℕ` such that
  `(z - w)^N [Y(a, z), Y(b, w)] = 0`. Equivalently, in coefficients, for all
  `p, q : ℤ`:
  $$\sum_{i=0}^{N} (-1)^i \binom{N}{i}
      \bigl(a_{(N-i+p)}\, b_{(i+q)} - b_{(i+q)}\, a_{(N-i+p)}\bigr) = 0.$$
  -/
  locality :
    ∀ (a b : V), ∃ N : ℕ, ∀ (p q : ℤ),
      ∑ i ∈ Finset.range (N + 1),
          ((-1 : R) ^ i * (N.choose i : R)) •
            (((Y a)[[(N : ℤ) - (i : ℤ) + p]]) ∘ₗ ((Y b)[[(i : ℤ) + q]]) -
              ((Y b)[[(i : ℤ) + q]]) ∘ₗ ((Y a)[[(N : ℤ) - (i : ℤ) + p]])) = 0

namespace VertexAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  (𝒱 : VertexAlgebra R V)

/-- The `n`-th mode `a_{(n)}` of a state `a ∈ V`. -/
abbrev mode (a : V) (n : ℤ) : Module.End R V := (𝒱.Y a)[[n]]

end VertexAlgebra

/-! ## Vertex operator algebras -/

/-- A **vertex operator algebra** (VOA) over a field `R` of characteristic zero,
on an `R`-module `V`, is a vertex algebra together with a distinguished
*conformal element* `ω ∈ V` and a *central charge* `c ∈ R` such that:

* **voa1** (conformal symmetry): the modes `L_n := ω_{(n+1)}` of
  `Y(ω, z) = Σ L_n z^{-n-2}` satisfy the Virasoro relations with central
  charge `c`;
* **voa2** (conformal weight): `L_0` acts semisimply on `V` giving a
  `ℤ`-grading `V = ⨁_{n ∈ ℤ} V_n` with `L_0 v = n · v` for `v ∈ V_n`;
* **voa3** (translation generator): `L_{-1}` agrees with the translation
  operator `T`, so `Y(L_{-1} v, z) = ∂_z Y(v, z)`;
* **voa4** (CFT type): `V_0 = R · 𝟙`, `V_n = 0` for `n < 0`, and each
  homogeneous subspace `V_n` is finite-dimensional.

This matches [Gannon06, Definition 5.1.3 (b)] on p. 318; see also Wikipedia,
[FLM88, Kac98]. -/
structure VertexOperatorAlgebra (R V : Type*) [Field R] [CharZero R]
    [AddCommGroup V] [Module R V] extends VertexAlgebra R V where
  /-- The conformal (Virasoro) element `ω ∈ V`. -/
  conformal : V
  /-- The central charge `c ∈ R`. -/
  centralCharge : R
  /-- **voa1 — Virasoro relations**: the modes `L_n := ω_{(n+1)}` satisfy
  `[L_m, L_n] = (m - n) L_{m+n} + c · (m³ - m)/12 · δ_{m+n,0} · Id`. -/
  virasoro :
    ∀ (m n : ℤ),
      ((Y conformal)[[m + 1]]) ∘ₗ ((Y conformal)[[n + 1]]) -
          ((Y conformal)[[n + 1]]) ∘ₗ ((Y conformal)[[m + 1]]) =
        ((m : R) - n) • ((Y conformal)[[m + n + 1]]) +
          (if m + n = 0 then
              (centralCharge * ((m : R) ^ 3 - m) / 12) •
                (1 : Module.End R V)
            else 0)
  /-- **voa3 — `L_{-1} = T`**: the translation operator agrees with
  `ω_{(0)}`. Equivalently, `Y(L_{-1} v, z) = ∂_z Y(v, z)`. -/
  L_neg_one_eq_T : ((Y conformal)[[0]]) = T
  /-- The weight-`n` subspace `V_n`, intended to be the `L_0`-eigenspace for
  the eigenvalue `n`. -/
  weight : ℤ → Submodule R V
  /-- `V` is the internal direct sum of its weight spaces, `V = ⨁_{n ∈ ℤ} V_n`. -/
  weight_isInternal : DirectSum.IsInternal weight
  /-- **voa2 — Conformal weight**: every element of `weight n` is an
  `L_0`-eigenvector with eigenvalue `n`. -/
  weight_isEigenspace :
    ∀ (n : ℤ) (v : V), v ∈ weight n → ((Y conformal)[[1]]) v = (n : R) • v
  /-- **voa4 — CFT type, `V_0 = R · 𝟙`**: the weight-zero subspace is
  spanned by the vacuum vector. -/
  weight_zero_eq_span_vacuum : weight 0 = Submodule.span R {vacuum}
  /-- **voa4 — CFT type, no negative weights**: `V_n = 0` for `n < 0`. -/
  weight_neg_eq_bot : ∀ n : ℤ, n < 0 → weight n = ⊥
  /-- **voa4 — finite-dimensional homogeneous components**: each `V_n`
  is finite-dimensional over `R`. -/
  weight_finiteDimensional : ∀ n : ℤ, FiniteDimensional R (weight n)

namespace VertexOperatorAlgebra

variable {R V : Type*} [Field R] [CharZero R] [AddCommGroup V] [Module R V]
  (𝒱 : VertexOperatorAlgebra R V)

/-- The `n`-th Virasoro mode `L_n = ω_{(n+1)}`. -/
abbrev L (n : ℤ) : Module.End R V := (𝒱.Y 𝒱.conformal)[[n + 1]]

end VertexOperatorAlgebra

end FormalConformal
