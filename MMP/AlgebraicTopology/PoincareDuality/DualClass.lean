module

public import MMP.AlgebraicTopology.CapProduct.Basic
public import MMP.AlgebraicTopology.FundamentalClass.Basic

/-!
# Dual classes on an oriented manifold (Fulton, §19.1)

Let `M` be an oriented real `n`-manifold with fundamental class `μ_M ∈ H_n M`, `A ⊆ M` closed and
`a ∈ H_k A`. A class `c ∈ H^{n-k}(M, M - A)` is *dual to `a`* if `c ∩ μ_M = a`. Poincaré–Alexander
duality says that there is exactly one such class, written `cl^M(a)`.

This file treats the absolute case `A = M`: a class `c ∈ H^{n-k} M` is dual to `a ∈ H_k M` with
respect to a class `μ ∈ H_n M` when `c ∩ μ = a`. Dual classes are compatible with the module
structure: if `c` is dual to `a` and `c'` to `a'`, then `c + c'` is dual to `a + a'` and `r • c`
to `r • a`.

## Main definitions

* `MMP.borelMooreHomology.IsDualClass`: `c ∈ H^{n-k} M` is dual to `a ∈ H_k M`
  with respect to `μ ∈ H_n M`, i.e. `c ∩ μ = a`.

## Main results

* `MMP.borelMooreHomology.IsDualClass.add`,
  `MMP.borelMooreHomology.IsDualClass.smul`,
  `MMP.borelMooreHomology.IsDualClass.zero`: dual classes form a submodule of
  the product.

## Implementation notes

The class `μ` is an argument; for Fulton's notion it is a fundamental class
(`MMP.IsFundamentalClass`) of an oriented manifold. The cap product lands in
degree `n - (n - k)`, which is identified with `k` by `BorelMooreCross.congrDegree`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

universe u

namespace MMP

namespace borelMooreHomology

variable {R : Type u} [CommRing R] {M : TopCat.{u}} {n : ℕ} {k : ℤ}

variable (R) in
/-- A class `c ∈ H^{n-k} M` is *dual* to `a ∈ H_k M` with respect to `μ ∈ H_n M` (Fulton, §19.1,
for `A = M` and `μ` the fundamental class of an oriented manifold) when `c ∩ μ = a`. -/
def IsDualClass (μ : borelMooreHomology R (ModuleCat.of R R) M n)
    (c : cohomologyWithSupports R (ModuleCat.of R R) M Set.univ (n - k))
    (a : borelMooreHomology R (ModuleCat.of R R) M k) : Prop :=
  BorelMooreCross.congrDegree R M (by omega) (capProduct R M Set.univ (n - k) n c μ) = a

/-- `c` is dual to `a` with respect to `μ` if and only if `c ∩ μ = a`. -/
lemma isDualClass_iff (μ : borelMooreHomology R (ModuleCat.of R R) M n)
    (c : cohomologyWithSupports R (ModuleCat.of R R) M Set.univ (n - k))
    (a : borelMooreHomology R (ModuleCat.of R R) M k) :
    IsDualClass R μ c a ↔
      BorelMooreCross.congrDegree R M (by omega) (capProduct R M Set.univ (n - k) n c μ) = a :=
  Iff.rfl

/-- Every class `c` is dual to `c ∩ μ`. -/
lemma isDualClass_capProduct (μ : borelMooreHomology R (ModuleCat.of R R) M n)
    (c : cohomologyWithSupports R (ModuleCat.of R R) M Set.univ (n - k)) :
    IsDualClass R μ c
      (BorelMooreCross.congrDegree R M (by omega) (capProduct R M Set.univ (n - k) n c μ)) :=
  rfl

/-- If `c` is dual to both `a` and `a'` with respect to `μ`, then `a = a'`. -/
lemma IsDualClass.right_unique {μ : borelMooreHomology R (ModuleCat.of R R) M n}
    {c : cohomologyWithSupports R (ModuleCat.of R R) M Set.univ (n - k)}
    {a a' : borelMooreHomology R (ModuleCat.of R R) M k} (h : IsDualClass R μ c a)
    (h' : IsDualClass R μ c a') : a = a' :=
  h.symm.trans h'

/-- The zero class is dual to `0`. -/
lemma IsDualClass.zero (μ : borelMooreHomology R (ModuleCat.of R R) M n) :
    IsDualClass R μ (0 : cohomologyWithSupports R (ModuleCat.of R R) M Set.univ (n - k)) 0 := by
  simp [IsDualClass]

/-- If `c` is dual to `a` and `c'` to `a'`, then `c + c'` is dual to `a + a'`. -/
lemma IsDualClass.add {μ : borelMooreHomology R (ModuleCat.of R R) M n}
    {c c' : cohomologyWithSupports R (ModuleCat.of R R) M Set.univ (n - k)}
    {a a' : borelMooreHomology R (ModuleCat.of R R) M k} (h : IsDualClass R μ c a)
    (h' : IsDualClass R μ c' a') : IsDualClass R μ (c + c') (a + a') := by
  rw [IsDualClass, map_add, LinearMap.add_apply, map_add]
  exact congrArg₂ (· + ·) h h'

/-- If `c` is dual to `a`, then `r • c` is dual to `r • a`. -/
lemma IsDualClass.smul {μ : borelMooreHomology R (ModuleCat.of R R) M n}
    {c : cohomologyWithSupports R (ModuleCat.of R R) M Set.univ (n - k)}
    {a : borelMooreHomology R (ModuleCat.of R R) M k} (h : IsDualClass R μ c a) (r : R) :
    IsDualClass R μ (r • c) (r • a) := by
  rw [IsDualClass, map_smul, LinearMap.smul_apply, map_smul]
  exact congrArg (r • ·) h

end borelMooreHomology

end MMP
