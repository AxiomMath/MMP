module

public import MMP.AlgebraicGeometry.Resolution.MaximalContact.Derivative
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocal.Basic
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents

/-!
# Monomial parts, coefficient ideals and monomial order reduction (Kollár, *Resolution*, §3.e)

For a triple `(X, I, E)`, `E = (E^1, …, E^s)` with irreducible components `E^{ik}` of `E^i`,
the *monomial part* of `I` is `M(I) = 𝒪_X(-A(I))`, `A(I) = ∑ ord_{E^{ik}}(I)·E^{ik}`, and the
*nonmonomial part* is `N(I) = 𝒪_X(A(I))·I` (Kollár Def.–Lemma 3.110). For *monomial data*
`(X, E, A)` — an ordered snc divisor and an effective divisor `A` supported on `⋃ E^i` — the
numbers `m_r(E, A)` and `n_r(E, A)` measure the maximal weight `∑_t a_{j_t}` along the `r`-fold
intersections `E^J`, and blowing up the pieces of maximal weight decreases them (Kollár 3.111,
Step 3); iterating gives the *monomial order reduction sequence*. This file also states the
*maximal coefficient ideals* `W_s(I)` and the *well-tuned ideal* `W(I) = W_{m!}(I)` (Kollár 3.98,
(3.54.1)), the centre `Z_{-1}(K, μ, D)` of Lemma 3.102, MC-hypersurfaces (3.80), extension of a
blow-up sequence from an open subset by closure, open cover maps, and the formal transforms
`T_i(K, μ)` along a blow-up sequence (the formula of 3.60/3.77).

## Main definitions

* `MMP.Resolution.divisorIdeal`: `𝒪_X(-A)` for an effective divisor `A`.
* `MMP.Resolution.IsMonomialDecomposition`, `MMP.Resolution.monomialPartCoeff` (`A(I)`),
  `MMP.Resolution.monomialPart` (`M(I)`), `MMP.Resolution.nonmonomialPart` (`N(I)`),
  `MMP.Resolution.mixedIdeal` (`K_s(I, m)`).
* `MMP.Resolution.MonomialData`, `MMP.Resolution.MonomialData.monomialIdeal`,
  `…maxStratumWeight` (`m_r`), `…maxStratumCount` (`n_r`), `…step`, `…stepSequence`,
  `MMP.Resolution.MonomialData.monomialOrderReduction`.
* `MMP.Resolution.ClosedBlowupSequence.extendByClosure`.
* `MMP.Resolution.maximalCoefficientIdeal` (`W_s(I)`), `MMP.Resolution.wellTunedIdeal`.
* `MMP.Resolution.divisorComponentCentre` (`Z_{-1}(K, μ, D)`).
* `MMP.Resolution.IsMCHypersurface`, `MMP.Resolution.IsOpenCoverMap`.
* `MMP.Resolution.ClosedBlowupSequence.formalTransform` (`T_i(K, μ)`).

## Implementation notes

An effective divisor `A = ∑ a_D D` is its coefficient function `PrimeDivisor X → ℕ`, and
`𝒪_X(-A) = ∏ I_D^{a_D}` (a finite product when `A` has finite support; `𝒪_X` otherwise). The
order `ord_{E^{ik}}(I)` along a prime divisor `D` is the order `multAt I η_D` at its generic
point. The nonmonomial part `N(I) = 𝒪_X(A(I))·I` is a fractional ideal sheaf; on a triple `I` is
divisible by the invertible ideal `M(I)`, and `N(I)` is defined as the ideal quotient
`(I : M(I))`. That `M(I)·N(I) = I` is stated as a theorem (`monomialPart_mul_nonmonomialPart`).

The coefficient `a_j(x)` of the component of `E^j` through `x` is the sum of the coefficients of
the components of `E^j` containing `x` (there is exactly one when `E^j` is smooth). The pull-back
`π^*A` along a blow-up of a smooth variety has coefficient `ord_{D'}(π^*𝒪_X(-A))` at a prime
divisor `D'`, and the reduced exceptional divisor `F = π⁻¹(Z)` coefficient `ord_{D'}(I_F)`; the
new coefficients `π^*A - mF` are their (truncated) difference.

The steps of a monomial order reduction are recorded with continuations: `stepPhase` performs `q`
Step-3.`r` blow-ups and continues with a given blow-up sequence at the end, so that consecutive
phases are concatenated without transport along equalities of schemes.

The formal transforms `T_i(K, μ)` are fractional ideal sheaves; `T_i = N_i·D_i⁻¹` is recorded by
the pair `(N_i, D_i)` with `D_i` an invertible ideal (`FractionalIdealRep`): `T_0 = (K, 𝒪_X)`
and `T_{i+1} = (π_i^*N_i, π_i^*D_i · I_{F_{i+1}}^μ)`.

The dimension of `X` is read in `ℕ` (`dimNat`): an infinite or negative Krull dimension, outside
the source's domain, is read as `0`. Hypotheses of the source that only restrict the domain are
dropped (smoothness, `dim X ≥ 1`, `maxord I ≥ 1`, that the input is a triple).

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.54, 3.60, 3.77, 3.80, 3.98, 3.102–3.104,
  3.110, 3.111]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

open Aux

/-- The dimension `dim X ∈ ℕ` of a scheme: its Krull dimension, read as `0` when it is infinite
or `X` is empty. -/
def dimNat (X : Scheme.{u}) : ℕ :=
  ((topologicalKrullDim X).unbotD 0).toNat

/-! ### Monomial and nonmonomial parts -/

section MonomialPart

variable {X : Scheme.{u}}

/-- The ideal sheaf `𝒪_X(-A) = ∏_D I_D^{a_D}` of an effective divisor `A = ∑_D a_D D`, given by
its coefficients (`𝒪_X` if infinitely many are nonzero). -/
def divisorIdeal (A : AlgebraicGeometry.PrimeDivisor X → ℕ) : X.IdealSheafData :=
  ∏ᶠ D : AlgebraicGeometry.PrimeDivisor X, D.idealSheaf ^ A D

/-- The prime divisor `D` is an irreducible component `E^{ik}` of one of the `E^i`. -/
def OrderedDivisor.IsComponent (E : OrderedDivisor X) (D : AlgebraicGeometry.PrimeDivisor X) :
    Prop :=
  ∃ i, D.support ∈ componentsOf ((E.E i).support : Set X)

/-- A *monomial decomposition* of `I` with respect to `E = (E^1, …, E^s)` (Kollár Def.–Lemma
3.110, corrected): an effective divisor `A = ∑ a_{ik} E^{ik}` supported on `⋃ E^i` (given by its
coefficients) and an ideal sheaf `N` with `I = 𝒪_X(-A)·N` such that no `E^{ik}` is contained in
`cosupp N`. -/
@[mmp "def_kr3e_monomial_decomposition"]
structure IsMonomialDecomposition (I : X.IdealSheafData) (E : OrderedDivisor X)
    (A : AlgebraicGeometry.PrimeDivisor X → ℕ) (N : X.IdealSheafData) : Prop where
  /-- Only finitely many coefficients of `A` are nonzero. -/
  finite_support : (Function.support A).Finite
  /-- Every prime divisor with nonzero coefficient in `A` is a component of some `E^i`. -/
  isComponent_of_ne_zero : ∀ D, A D ≠ 0 → E.IsComponent D
  /-- `I = 𝒪_X(-A)·N`. -/
  eq_mul : I = divisorIdeal A * N
  /-- No component of an `E^i` is contained in the cosupport of `N`. -/
  not_subset_cosupport : ∀ D, E.IsComponent D → ¬ D.support ⊆ (N.support : Set X)

open Classical in
/-- The coefficients of `A(I) = ∑_{i,k} ord_{E^{ik}}(I)·E^{ik}` (Kollár Def.–Lemma 3.110): the
order of `I` along each irreducible component `E^{ik}` of an `E^i`, and `0` along every other
prime divisor. -/
@[mmp "def_kr3e_monomial_part"]
def monomialPartCoeff (I : X.IdealSheafData) (E : OrderedDivisor X)
    (D : AlgebraicGeometry.PrimeDivisor X) : ℕ :=
  if E.IsComponent D then (multAt I D.genericPoint).toNat else 0

/-- The *monomial part* `M(I) = 𝒪_X(-A(I))` of `I` with respect to `E` (Kollár Def.–Lemma 3.110,
corrected). -/
@[mmp "def_kr3e_monomial_part"]
def monomialPart (I : X.IdealSheafData) (E : OrderedDivisor X) : X.IdealSheafData :=
  divisorIdeal (monomialPartCoeff I E)

/-- The *nonmonomial part* `N(I) = 𝒪_X(A(I))·I` of `I` with respect to `E` (Kollár Def.–Lemma
3.110), as the ideal quotient `(I : M(I))`. -/
@[mmp "def_kr3e_nonmonomial_part"]
def nonmonomialPart (I : X.IdealSheafData) (E : OrderedDivisor X) : X.IdealSheafData :=
  idealColon I (monomialPart I E)

/-- For a triple `(X, I, E)`, the nonmonomial part is `𝒪_X(A(I))·I`: multiplied by
`M(I) = 𝒪_X(-A(I))` it gives back `I`. -/
@[mmp "def_kr3e_nonmonomial_part"]
theorem monomialPart_mul_nonmonomialPart {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (E : OrderedDivisor X) (h : IsTriple sX I E) :
    monomialPart I E * nonmonomialPart I E = I := by
  classical
  obtain ⟨-, hsm, hlft, hqc, -⟩ := h
  haveI : LocallyOfFiniteType sX := hlft
  haveI : QuasiCompact sX := hqc
  set A := monomialPartCoeff I E with hAdef
  have hfin : (Function.support A).Finite := by
    refine (finite_primeDivisor_of_isComponent sX E.E).subset fun D hD => ?_
    by_contra hnc
    exact hD (by simp [hAdef, monomialPartCoeff, OrderedDivisor.IsComponent] at hnc ⊢; simp_all)
  have hM : monomialPart I E = ∏ D ∈ hfin.toFinset, D.idealSheaf ^ A D := by
    rw [show monomialPart I E = ∏ᶠ D : AlgebraicGeometry.PrimeDivisor X, D.idealSheaf ^ A D from
      rfl]
    refine finprod_eq_prod_of_mulSupport_subset _ fun D hD => ?_
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    intro h0
    exact hD (by simp [h0])
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor (monomialPart I E) := by
    rw [hM]
    exact Stacks.Divisors.isEffectiveCartierDivisor_prod _ _ _
      fun D _ => isEffectiveCartierDivisor_idealSheaf sX hsm D
  have hle : I ≤ monomialPart I E := by
    rw [hM]
    refine le_prod_of_stalk_le sX hsm A _ I fun D hD => ?_
    by_cases hc : E.IsComponent D
    · have hA : A D =
          (idealOrder (AlgebraicGeometry.IdealSheafData.stalk I D.genericPoint)).toNat := by
        simp [hAdef, monomialPartCoeff, hc, multAt]
      rw [hA]
      exact le_pow_of_le_idealOrder (ENat.coe_toNat_le_self _)
    · have : A D = 0 := by simp [hAdef, monomialPartCoeff, hc]
      simp [this]
  have hcol : idealColon I (monomialPart I E) =
      Scheme.IdealSheafData.colon I (monomialPart I E)
        (AlgebraicGeometry.fg_ideal_of_isEffectiveCartierDivisor _ hcart) := by
    unfold idealColon
    exact Scheme.IdealSheafData.ofIdeals_ideal
      (Scheme.IdealSheafData.colon I (monomialPart I E)
        (AlgebraicGeometry.fg_ideal_of_isEffectiveCartierDivisor _ hcart))
  rw [nonmonomialPart, hcol]
  exact AlgebraicGeometry.mul_colon_eq_of_isEffectiveCartierDivisor _ _ hcart hle

/-- The ideal `K_s(I, m) = N(I)^m + I^s` (Kollár 3.111, Step 2). -/
@[mmp "def_kr3e_mixed_ideal"]
def mixedIdeal (I : X.IdealSheafData) (E : OrderedDivisor X) (m s : ℕ) : X.IdealSheafData :=
  nonmonomialPart I E ^ m + I ^ s

end MonomialPart

/-! ### Monomial data -/

/-- *Monomial data* `(X, E, A)` on `X` (Kollár 3.111, Step 3): a structure morphism `X → Spec k`,
an ordered divisor `E = (E^1, …, E^s)` and an effective divisor `A = ∑ a_{ik} E^{ik}`, given by
its coefficients. The conditions are `MonomialData.IsMonomialData`. -/
@[mmp "def_kr3e_monomial_marked_ideal"]
structure MonomialData (X : Scheme.{u}) where
  /-- The ground field. -/
  k : Type u
  [field : Field k]
  /-- The structure morphism `X → Spec k`. -/
  sX : X ⟶ Spec (.of k)
  /-- The ordered divisor `E`. -/
  E : OrderedDivisor X
  /-- The coefficients of `A`. -/
  A : AlgebraicGeometry.PrimeDivisor X → ℕ

attribute [instance] MonomialData.field

namespace MonomialData

variable {X : Scheme.{u}} (C : MonomialData X)

/-- `(X, E, A)` are *monomial data* (Kollár 3.111, Step 3): `X` is smooth, of finite type over
`k`, `E` is an ordered snc divisor, and `A` is an effective divisor (finitely many nonzero
coefficients) supported on `⋃ E^i`, i.e. `A = ∑ a_{ik} E^{ik}`. -/
@[mmp "def_kr3e_monomial_marked_ideal"]
def IsMonomialData : Prop :=
  MMP.Mori.IsSmoothScheme C.sX ∧ LocallyOfFiniteType C.sX ∧ QuasiCompact C.sX ∧
    C.E.IsOrderedSNC C.sX ∧ (Function.support C.A).Finite ∧
    ∀ D, C.A D ≠ 0 → C.E.IsComponent D

/-- The *monomial ideal* `I_{E,A} = 𝒪_X(-A)` of monomial data (Kollár 3.111, Step 3). -/
@[mmp "def_kr3e_monomial_marked_ideal"]
def monomialIdeal : X.IdealSheafData :=
  divisorIdeal C.A

open Classical in
/-- The coefficient `a_j(x)` in `A` of the component of `E^j` through `x ∈ E^j`. -/
@[mmp "def_kr3e_max_stratum_weight"]
def coeffAt (j : Fin C.E.s) (x : X) : ℕ :=
  ∑ᶠ D : AlgebraicGeometry.PrimeDivisor X,
    if D.support ∈ componentsOf ((C.E.E j).support : Set X) ∧ x ∈ D.support then C.A D else 0

/-- The intersection `E^J = E^{j_1} ∩ ⋯ ∩ E^{j_r}` for `J = {j_1 < ⋯ < j_r}`. -/
@[mmp "def_kr3e_max_stratum_weight"]
def stratum (J : Finset (Fin C.E.s)) : Set X :=
  ⋂ j ∈ J, ((C.E.E j).support : Set X)

/-- A point lies in `E^J` iff it lies in every `E^j`, `j ∈ J`. -/
@[simp] theorem mem_stratum_iff {J : Finset (Fin C.E.s)} {x : X} :
    x ∈ C.stratum J ↔ ∀ j ∈ J, x ∈ ((C.E.E j).support : Set X) := by
  simp [stratum]

/-- The weight `σ_J(x) = ∑_{t=1}^r a_{j_t}(x)` at `x ∈ E^J`. -/
@[mmp "def_kr3e_max_stratum_weight"]
def stratumWeight (J : Finset (Fin C.E.s)) (x : X) : ℕ :=
  ∑ j ∈ J, C.coeffAt j x

/-- `m_r(E, A) = max {σ_J(x) : |J| = r, x ∈ E^J}`, and `0` if all `r`-fold intersections are
empty (Kollár 3.111, Steps 3.2, 3.`r`). -/
@[mmp "def_kr3e_max_stratum_weight"]
def maxStratumWeight (r : ℕ) : ℕ :=
  ⨆ (J : Finset (Fin C.E.s)) (_ : J.card = r) (x : X) (_ : x ∈ C.stratum J), C.stratumWeight J x

/-- For monomial data, `σ_J` is constant on the connected components (the *pieces*) of `E^J`. -/
@[mmp "def_kr3e_max_stratum_weight"]
theorem stratumWeight_eq_of_mem_connectedComponentIn (hC : C.IsMonomialData)
    (J : Finset (Fin C.E.s)) {x y : X} (hx : x ∈ C.stratum J)
    (hy : y ∈ connectedComponentIn (C.stratum J) x) :
    C.stratumWeight J y = C.stratumWeight J x := by
  obtain ⟨-, hlft, hqc, hsnc, hfin, -⟩ := hC
  haveI : LocallyOfFiniteType C.sX := hlft
  haveI : QuasiCompact C.sX := hqc
  unfold stratumWeight
  refine Finset.sum_congr rfl fun j hj => ?_
  have hsub : connectedComponentIn (C.stratum J) x ⊆ ((C.E.E j).support : Set X) :=
    (connectedComponentIn_subset _ _).trans fun _ hz => C.mem_stratum_iff.1 hz j hj
  exact componentCoeff_eq_of_isPreconnected C.sX (C.E.E j) ((hsnc.2.1 j).2.2) C.A hfin
    isPreconnected_connectedComponentIn hsub (mem_connectedComponentIn hx) hy

/-- `P` is a piece of `E^J`, `|J| = r`, on which `σ_J = m_r(E, A)`. -/
@[mmp "def_kr3e_max_stratum_count"]
def IsMaxPiece (r : ℕ) (J : Finset (Fin C.E.s)) (P : Set X) : Prop :=
  J.card = r ∧ (∃ x ∈ C.stratum J, P = connectedComponentIn (C.stratum J) x) ∧
    ∀ y ∈ P, C.stratumWeight J y = C.maxStratumWeight r

/-- `n_r(E, A)`: the number of pairs `(J, P)` with `|J| = r` and `P` a piece of `E^J` on which
`σ_J = m_r(E, A)` (Kollár 3.111, Steps 3.2, 3.`r`). -/
@[mmp "def_kr3e_max_stratum_count"]
def maxStratumCount (r : ℕ) : ℕ :=
  Set.ncard {p : Finset (Fin C.E.s) × Set X | C.IsMaxPiece r p.1 p.2}

open Classical in
/-- `J_*`: the lexicographically smallest `r`-tuple `J = (j_1 < ⋯ < j_r)` such that
`σ_J = m_r(E, A)` on some piece of `E^J` (`∅` if there is none). -/
@[mmp "def_kr3e_monomial_step"]
def stepIndex (r : ℕ) : Finset (Fin C.E.s) :=
  let S := Finset.univ.filter fun J => ∃ P, C.IsMaxPiece r J P
  if h : S.Nonempty then (S.exists_min_image (fun J => J.sort (· ≤ ·)) h).choose else ∅

/-- The centre `Z` of the Step-3.`r` blow-up: the union of the pieces of `E^{J_*}` on which
`σ_{J_*} = m_r(E, A)`, with its reduced structure. -/
@[mmp "def_kr3e_monomial_step"]
def stepCenter (r : ℕ) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure (⋃₀ {P | C.IsMaxPiece r (C.stepIndex r) P}))

/-- The *Step-3.`r` blow-up* of monomial data `(X, E, A)` with marking `m` (Kollár 3.111,
Steps 3.1–3.`r`): `π : X' = B_ZX → X`, `Z` the centre `stepCenter`, with the new data
`(X', E', A')`, `E' = π⁻¹_tot E` and `A' = π^*A - mF`, `F = π⁻¹(Z)` the exceptional divisor. -/
@[mmp "def_kr3e_monomial_step"]
def step (m r : ℕ) : MonomialData (blowUp (C.stepCenter r)) where
  k := C.k
  sX := blowUpToBase (C.stepCenter r) ≫ C.sX
  E := C.E.totalTransform (C.stepCenter r)
  A D' :=
    (multAt ((divisorIdeal C.A).comap (blowUpToBase (C.stepCenter r))) D'.genericPoint).toNat -
      m * (multAt ((C.stepCenter r).comap (blowUpToBase (C.stepCenter r)))
        D'.genericPoint).toNat

/-- The data `C_q` after `q` Step-3.`r` blow-ups. -/
@[mmp "def_kr3e_monomial_order_reduction"]
def iterate (m r : ℕ) : ℕ → {X : Scheme.{u}} → MonomialData X → Σ Y : Scheme.{u}, MonomialData Y
  | 0, X, C => ⟨X, C⟩
  | q + 1, _, C => iterate m r q (C.step m r)

/-- `q` Step-3.`r` blow-ups `C_0 → C_1 → ⋯ → C_q`, followed by the blow-up sequence `K C_q`. -/
@[mmp "def_kr3e_monomial_order_reduction"]
def stepPhase (m r : ℕ) (K : ∀ {Y : Scheme.{u}}, MonomialData Y → ClosedBlowupSequence Y) :
    ℕ → {X : Scheme.{u}} → MonomialData X → ClosedBlowupSequence X
  | 0, _, C => K C
  | q + 1, _, C => .cons (C.stepCenter r) (stepPhase m r K q (C.step m r))

open Classical in
/-- The *Step-3.`r` sequence* of monomial data `C_0` with marking `m` (Kollár 3.111, Step 3):
`C_0, C_1, …, C_N`, `C_{q+1}` the Step-3.`r` blow-up of `C_q` and `N` the least index with
`m_r(C_N) < m`; the empty sequence if there is no such `N`. -/
@[mmp "def_kr3e_monomial_order_reduction"]
def stepSequence (m r : ℕ) : ClosedBlowupSequence X :=
  if h : ∃ N, ((C.iterate m r N).2.maxStratumWeight r) < m then
    stepPhase m r (fun {Y} _ => .nil Y) (Nat.find h) C
  else .nil X

open Classical in
/-- The concatenation of the Step-3.`r`, Step-3.`(r+1)`, …, Step-3.`(r+j-1)` sequences, each
starting at the end of the previous one. -/
@[mmp "def_kr3e_monomial_order_reduction"]
def monomialOrderReductionFrom (m : ℕ) : ℕ → ℕ → {X : Scheme.{u}} → MonomialData X →
    ClosedBlowupSequence X
  | 0, _, X, _ => .nil X
  | j + 1, r, _, C =>
    if h : ∃ N, ((C.iterate m r N).2.maxStratumWeight r) < m then
      stepPhase m r (fun D => monomialOrderReductionFrom m j (r + 1) D) (Nat.find h) C
    else monomialOrderReductionFrom m j (r + 1) C

/-- The *monomial order reduction sequence* of `(X, E, A, m)`, `n = dim X` (Kollár 3.111, Step 3,
Steps 3.1, …, 3.`n`): the concatenation of the Step-3.1, …, Step-3.`n` sequences, each starting at
the end of the previous one, as a blow-up sequence starting with `X`. -/
@[mmp "def_kr3e_monomial_order_reduction"]
def monomialOrderReduction (m : ℕ) : ClosedBlowupSequence X :=
  monomialOrderReductionFrom m (dimNat X) 1 C

end MonomialData

/-! ### Extension of a blow-up sequence by closure -/

namespace ClosedBlowupSequence

open Classical in
/-- The *extension by closure* along `ι : U → X` of a blow-up sequence `(U_i, Z_i^U)` starting
with `U` (Kollár 3.104 Step 2.2, 3.111 Step 2), `ι` the inclusion of an open subset: `X_0 = X`,
`ι_0 = ι`, `Z_i` the scheme-theoretic closure (image) of `ι_i(Z_i^U)`, `X_{i+1} = B_{Z_i}X_i`, and
`ι_{i+1} : U_{i+1} = B_{Z_i^U}U_i → X_{i+1}` the morphism induced by `ι_i`, the canonical lift
along `Z_i`, as `ι_i⁻¹Z_i = Z_i^U`. (If `ι_i⁻¹Z_i ≠ Z_i^U`, which does not happen for an open
inclusion, the sequence stops.) -/
@[mmp "def_kr3e_extension_by_closure"]
def extendByClosure : {U X : Scheme.{u}} → ClosedBlowupSequence U → (U ⟶ X) →
    ClosedBlowupSequence X
  | _, X, nil _, _ => nil X
  | _, _, cons Z B, ι =>
    if h : (Z.map ι).comap ι = Z then
      cons (Z.map ι)
        (extendByClosure B (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι)))
    else nil _

/-- For a quasi-compact open immersion `ι : U → X`, the inverse image of the scheme-theoretic
image of `Z ⊆ U` is `Z`, so the morphisms `ι_{i+1}` of the extension by closure exist. -/
@[mmp "def_kr3e_extension_by_closure"]
theorem comap_map_eq_of_isOpenImmersion {U X : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]
    [QuasiCompact ι] (Z : U.IdealSheafData) : (Z.map ι).comap ι = Z := by
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  intro V x hx
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  have hV : IsAffineOpen (ι ⁻¹ᵁ (ι ''ᵁ V.1)) := by
    rw [Scheme.Hom.preimage_image_eq]
    exact V.2
  rw [Scheme.IdealSheafData.ideal_map _ _ _ hV]
  have hle : (⟨_, hV⟩ : U.affineOpens) ≤ V := (Scheme.Hom.preimage_image_eq ι V.1).le
  have h2 := Z.ideal_le_comap_ideal hle hx
  simp only [Ideal.mem_comap] at h2 ⊢
  convert h2 using 2
  exact congrArg (fun f => (CommRingCat.Hom.hom f) x) (Scheme.Hom.appIso_inv_app ι V.1)

end ClosedBlowupSequence

/-! ### Maximal coefficient ideals -/

section Coefficient

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The *weight* `∑_{j=0}^m (m - j)c_j` of `c = (c_0, …, c_m) ∈ ℕ^{m+1}` (Kollár Def. 3.98). -/
@[mmp "def_kr3e_maximal_coefficient_ideal"]
def coefficientWeight (m : ℕ) (c : Fin (m + 1) → ℕ) : ℕ :=
  ∑ j, (m - j) * c j

/-- The *maximal coefficient ideal of order `s`* (Kollár Def. 3.98):
`W_s(I) = ∑_{c ∈ C_s} ∏_{j=0}^m (D^j(I))^{c_j}`, `m = maxord I`, over
`C_s = {c ∈ ℕ^{m+1} : ∑_j (m - j)c_j ≥ s}`, the sum being the ideal sheaf generated. -/
@[mmp "def_kr3e_maximal_coefficient_ideal"]
def maximalCoefficientIdeal (I : X.IdealSheafData) (s : ℤ) : X.IdealSheafData :=
  ⨆ (c : Fin ((maxOrder I).toNat + 1) → ℕ) (_ : s ≤ (coefficientWeight _ c : ℤ)),
    ∏ j : Fin ((maxOrder I).toNat + 1), higherDerivativeIdeal sX I (j : ℕ) ^ c j

/-- The *well-tuned ideal* `W(I) = W_{m!}(I)`, `m = maxord I` (Kollár (3.54.1), relocated). -/
@[mmp "def_kr3e_well_tuned_ideal"]
def wellTunedIdeal (I : X.IdealSheafData) : X.IdealSheafData :=
  maximalCoefficientIdeal sX I ((maxOrder I).toNat.factorial)

end Coefficient

/-! ### The centre `Z_{-1}` and MC-hypersurfaces -/

section Hypersurface

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- `Z_{-1}(K, μ, D)` (Kollár, proof of Lemma 3.102): the union of the irreducible components of
the divisor `D` that are contained in `cosupp(K, μ)`, with its reduced structure. -/
@[mmp "def_kr3e_divisor_component_centre"]
def divisorComponentCentre (K : MarkedIdeal X) (D : X.IdealSheafData) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
    (⋃₀ {W | W ∈ componentsOf (D.support : Set X) ∧ W ⊆ K.cosupport}))

/-- For a smooth divisor `D` (possibly reducible or empty) on `X` of finite type over `k`,
`Z_{-1}(K, μ, D)` is a closed, smooth subscheme of pure codimension `1`, a union of connected
components of `D`, possibly empty. -/
@[mmp "def_kr3e_divisor_component_centre"]
theorem divisorComponentCentre_spec [LocallyOfFiniteType sX] [QuasiCompact sX]
    (K : MarkedIdeal X) (D : X.IdealSheafData) (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
    (hD' : MMP.Mori.IsPureCodimOne D.support) :
    MMP.Mori.IsSmoothScheme ((divisorComponentCentre K D).subschemeι ≫ sX) ∧
      MMP.Mori.IsPureCodimOne (divisorComponentCentre K D).support ∧
      (divisorComponentCentre K D).support ≤ D.support ∧
      ∀ x ∈ ((divisorComponentCentre K D).support : Set X),
        connectedComponentIn (D.support : Set X) x ⊆ (divisorComponentCentre K D).support := by
  set S : Set (Set X) := {W | W ∈ componentsOf (D.support : Set X) ∧ W ⊆ K.cosupport} with hSdef
  have hS : S ⊆ componentsOf (D.support : Set X) := fun W hW => hW.1
  have hU := isClosed_sUnion_of_subset_componentsOf sX D S hS
  have hT : ((Closeds.closure (⋃₀ S) : Closeds X) : Set X) = ⋃₀ S := by
    simp [hU.closure_eq]
  have hsupC : (divisorComponentCentre K D).support = Closeds.closure (⋃₀ S) := by
    ext x
    simp [divisorComponentCentre, hSdef]
  have hsupS : ((divisorComponentCentre K D).support : Set X) = ⋃₀ S := by
    rw [hsupC, hT]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isSmoothScheme_vanishingIdeal_union_components sX D hD S hS _ hT
  · rw [hsupC]
    exact isPureCodimOne_union_components sX D hD' S hS _ hT
  · intro x hx
    have hx' : x ∈ ⋃₀ S := hsupS ▸ hx
    obtain ⟨W, hW, hxW⟩ := hx'
    exact hW.1.1.2 hxW
  · intro x hx
    rw [hsupS] at hx ⊢
    exact connectedComponentIn_subset_union_components sX D hD S hS hx

/-- `H ⊆ X` is a *smooth hypersurface*: a closed subscheme smooth over `k` of pure codimension
`1` (possibly reducible or empty). -/
def IsSmoothHypersurface (H : X.IdealSheafData) : Prop :=
  MMP.Mori.IsSmoothScheme (H.subschemeι ≫ sX) ∧ MMP.Mori.IsPureCodimOne H.support

/-- A smooth hypersurface `H ⊆ X` is an *MC-hypersurface* for `I` (Kollár 3.80, 3.103 Step 2):
`𝒪_X(-H) ⊆ MC(I)`. -/
@[mmp "def_kr3e_mc_hypersurface"]
def IsMCHypersurface (I H : X.IdealSheafData) : Prop :=
  IsSmoothHypersurface sX H ∧ H ≤ maximalContactIdeal sX I

/-- For an effective Cartier divisor `H`, `𝒪_X(-H) ⊆ MC(I)` if and only if every point has an
affine open neighbourhood `W` on which `H.ideal W = (h)` for some `h ∈ MC(I)(W)`. -/
@[mmp "def_kr3e_mc_hypersurface"]
theorem le_maximalContactIdeal_iff (I H : X.IdealSheafData)
    (hH : Stacks.Divisors.IsEffectiveCartierDivisor H) :
    H ≤ maximalContactIdeal sX I ↔
      ∀ x : X, ∃ (W : X.affineOpens) (h : Γ(X, W)), x ∈ W.1 ∧ H.ideal W = Ideal.span {h} ∧
        h ∈ (maximalContactIdeal sX I).ideal W := by
  refine ⟨fun hle x => ?_, fun h => ?_⟩
  · obtain ⟨V, hxV, g, -, hg⟩ := Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor H hH x
    exact ⟨V, g, hxV, hg, hle V (hg ▸ Ideal.mem_span_singleton_self g)⟩
  · choose W g hxW hg hgm using h
    refine Scheme.IdealSheafData.le_of_iSup_eq_top W ?_ ?_
    · exact eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩
    · intro x
      rw [hg x, Ideal.span_le]
      simpa using hgm x

end Hypersurface

/-! ### Open cover maps -/

/-- `g : X^* → X` is an *open cover map* (Kollár Thm. 3.103 proof Step 3, 3.105): `X^*` is a
finite disjoint union `∐_{α=1}^t U_α` of open subschemes and each `g|_{U_α}` is an open
immersion. -/
@[mmp "def_kr3e_open_cover_map"]
def IsOpenCoverMap {X' X : Scheme.{u}} (g : X' ⟶ X) : Prop :=
  ∃ (t : ℕ) (U : Fin t → X'.Opens), Pairwise (fun a b => Disjoint (U a) (U b)) ∧
    (⨆ a, U a) = ⊤ ∧ ∀ a, IsOpenImmersion ((U a).ι ≫ g)

/-! ### Formal transforms -/

/-- A fractional ideal sheaf `N·D⁻¹`, recorded by an ideal sheaf `N` and an ideal sheaf `D`
(intended to be invertible; not enforced). -/
structure FractionalIdealRep (X : Scheme.{u}) where
  /-- The numerator `N`. -/
  num : X.IdealSheafData
  /-- The denominator `D` (intended to be invertible). -/
  den : X.IdealSheafData

namespace ClosedBlowupSequence

/-- The last formal transform `T_r = N_r·D_r⁻¹` of `N·D⁻¹`:
`T_{i+1} = 𝒪(μF_{i+1})·π_i^*T_i = π_i^*N_i·(π_i^*D_i·I_{F_{i+1}}^μ)⁻¹`, `F_{i+1} = π_i⁻¹(Z_i)`. -/
def formalTransformAux : {X : Scheme.{u}} → (B : ClosedBlowupSequence X) → X.IdealSheafData →
    X.IdealSheafData → ℕ → FractionalIdealRep B.target
  | _, nil _, N, D, _ => ⟨N, D⟩
  | _, cons Z B, N, D, μ =>
    B.formalTransformAux (N.comap (blowUpToBase Z))
      (D.comap (blowUpToBase Z) * Z.comap (blowUpToBase Z) ^ μ) μ

/-- The *formal transforms* `T_i(K, μ)`, `0 ≤ i ≤ r`, of an ideal sheaf `K ⊆ 𝒪_X` along a
blow-up sequence `(X_i, Z_i)` (the formula of Kollár 3.60/3.77 for an arbitrary marking):
`T_0(K, μ) = K` and `T_{i+1}(K, μ) = 𝒪_{X_{i+1}}(μF_{i+1})·π_i^*T_i(K, μ)`,
`F_{i+1} = π_i⁻¹(Z_i)`, a fractional ideal sheaf on `X_i` (the target of the truncation at `i`). -/
@[mmp "def_kr3e_formal_transform"]
def formalTransform {X : Scheme.{u}} (B : ClosedBlowupSequence X) (K : X.IdealSheafData) (μ i : ℕ) :
    FractionalIdealRep (B.truncate i).target :=
  (B.truncate i).formalTransformAux K ⊤ μ

end ClosedBlowupSequence

end MMP.Resolution
