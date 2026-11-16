module

public import MMP.AlgebraicGeometry.Intersection.Surface.BlowupGenusDropAdjunction
public import MMP.AlgebraicGeometry.Divisor.RationalFunctionsProduct
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.ProjectiveLine
public import MMP.AlgebraicGeometry.Curves.DegreeEuler

/-!
# Adjunction and `K`-negative curves on surfaces over a perfect field

This file collects three results on surfaces over fields that need not be algebraically closed.

**Adjunction over a perfect field.** For a reduced curve `C` proper over a perfect field `k` on a
smooth surface `Y` with canonical divisor `K`, `(K + C) · C = -2 χ(C, 𝒪_C)`. The intersection
number is the degree `χ(C, 𝒪(K + C)|_C) - χ(C, 𝒪_C)` with `𝒪(K + C) ≅ Ω²_{Y/k} ⊗ 𝒪_Y(C)`, and
this identity of Euler characteristics is invariant under extension of scalars to an algebraic
closure `k̄`. There the surface is a disjoint union of smooth integral surfaces, `C` stays reduced
because `k` is perfect, and the algebraically closed case applies on each component.

**`K`-negative exceptional curves.** Let `f : X ⟶ Y` be projective and generically finite, `X` a
smooth surface over a perfect field `k`, and `E` an `f`-exceptional curve with `K_X · E < 0`.
With `κ = H⁰(E, 𝒪_E)` and `d = [κ : k]`, every degree on `E` over `k` is `d` times its degree
over `κ`, so `E² = -a d` and `K_X · E = -b d` with `a, b > 0` (`E² < 0` by negative
definiteness). Adjunction gives `-(a + b) d = 2 d h¹_κ(𝒪_E) - 2 d`, whence `a = b = 1` and
`h¹_κ(𝒪_E) = 0`; so `E ≅ ℙ¹_κ` and `𝒪_X(E)|_E ≅ 𝒪(-1)`, and `E² = K_X · E = -d`.

**Contraction.** On a resolution `f : X ⟶ Y` of a quasi-projective surface over a perfect field,
such a curve is an exceptional curve of the first kind, and Castelnuovo's theorem contracts it:
`f = h ≫ f₁` with `h` the blow-up of a regular closed point of `X₁` and `f₁` again a resolution.
The target is regular, hence smooth over the perfect field, integral as the image of `X`, and
`f₁` is birational because `h` and `f` are.

## Main results

* `isIntersectionNumber_canonical_add_eq_neg_two_mul_eulerCharacteristic_of_perfectField`
  (in `MMP.Threefold`): adjunction `((K + C) · C) = -2 χ(C, 𝒪_C)` over a perfect field.
* `MMP.Threefold.exists_isExceptionalCurveOfFirstKind_of_canonical_intersection_neg`: a
  `K`-negative exceptional curve is a `(-1)`-curve over its field of constants.
* `MMP.Resolution.exists_isProjectiveSurfaceResolution_of_cartierCurveIntersection_neg`:
  contracting a `K`-negative exceptional curve of a resolution.

## Implementation notes

* A reduced curve on a surface is encoded by its Weil divisor with all nonzero coefficients `1`;
  the curve is the reduced closed subscheme `C.suppIdeal.subscheme` on its support.
* The field `κ` of constants is given abstractly, as a `k`-algebra with an isomorphism
  `ℙ¹_κ ≅ E` over `k`; since `H⁰(ℙ¹_κ, 𝒪) = κ`, this identifies `κ` with `H⁰(E, 𝒪_E)`.
  `E ≅ ℙ¹_κ` with `𝒪_X(E)|_E ≅ 𝒪(-1)` is
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`.
* The canonical divisor of a resolution is a Cartier divisor whose Weil divisor is `div_X(ω)`
  for a nonzero rational `2`-form `ω`, as in `MMP.Resolution.IsMinimalSurfaceResolution`.

## References

* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], Chapter 2
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [Stacks Project, Tags 0C2N, 0C6U]
-/

@[expose] public section

universe u

open CategoryTheory

/-! ### Adjunction for reduced curves on a smooth surface over a perfect field -/

namespace MMP.Threefold

open AlgebraicGeometry MMP.Mori MonoidalCategory

section Dimension

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- A prime divisor on a surface is one-dimensional. -/
private theorem topologicalKrullDim_support_primeDivisor_eq_one (hY : MMP.Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) (E : MMP.Mori.PrimeDivisor Y) :
    topologicalKrullDim E.support = 1 := by
  haveI : IsIntegral Y := hY.toIsIntegral
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY E.genericPoint
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint, hYd,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  have hne : topologicalKrullDim E.support ≠ ⊥ := by
    rw [ne_eq, topologicalKrullDim_eq_bot_iff_isEmpty, not_isEmpty_iff]
    exact ⟨⟨E.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩⟩
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd] at h ⊢
  induction d with
  | top => exact absurd h (by decide)
  | coe n =>
    have h2 : (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      push_cast; exact h
    have := Nat.cast_injective (WithBot.coe_injective h2)
    have hn : n = 1 := by omega
    subst hn
    rfl

/-- The reduced support of a divisor on a surface has dimension at most one. -/
private theorem topologicalKrullDim_suppIdeal_subscheme_le_one (hY : MMP.Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) (C : Divisor Y) :
    topologicalKrullDim C.suppIdeal.subscheme ≤ 1 := by
  rw [MMP.Mori.topologicalKrullDim_subscheme_eq, DivisorWithCoeffs.coe_support_suppIdeal,
    DivisorWithCoeffs.coe_supp]
  exact topologicalKrullDim_biUnion_le C.support (fun E => E.idealSheaf.support.isClosed)
    (fun E _ => (topologicalKrullDim_support_primeDivisor_eq_one hY hYd E).le)

end Dimension

section LocalEquations

variable {Y : Scheme.{u}}

/-- If `g j` divides `g i * a` only when it divides `a` (for `i ≠ j`), then `g j` divides
`(∏_{i ∈ s} g i) * b` only when it divides `b`, for `j ∉ s`. -/
private theorem dvd_of_dvd_prod_mul {R ι : Type*} [CommMonoid R] [DecidableEq ι] {s : Finset ι}
    {g : ι → R} {j : ι} (hj : j ∉ s) (hg : ∀ i ∈ s, ∀ a, g j ∣ g i * a → g j ∣ a) {b : R}
    (h : g j ∣ (∏ i ∈ s, g i) * b) : g j ∣ b := by
  induction s using Finset.induction_on generalizing b with
  | empty => simpa using h
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, mul_assoc] at h
    exact ih (fun h' => hj (Finset.mem_insert_of_mem h'))
      (fun i' hi' => hg i' (Finset.mem_insert_of_mem hi'))
      (hg i (Finset.mem_insert_self i s) _ h)

/-- **An intersection of principal ideals is principal**, generated by the product, when no
generator divides a product with another generator without dividing the cofactor. -/
private theorem finset_inf_span_singleton_eq_span_prod {R ι : Type*} [CommSemiring R]
    [DecidableEq ι] (s : Finset ι) (g : ι → R)
    (hg : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a, g j ∣ g i * a → g j ∣ a) :
    s.inf (fun i => Ideal.span {g i}) = Ideal.span {∏ i ∈ s, g i} := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.inf_insert, ih (fun i hi i' hi' => hg i (Finset.mem_insert_of_mem hi) i'
      (Finset.mem_insert_of_mem hi')), Finset.prod_insert hj]
    refine le_antisymm (fun x hx => ?_) (le_inf ?_ ?_)
    · rw [Ideal.mem_inf, Ideal.mem_span_singleton, Ideal.mem_span_singleton] at hx
      obtain ⟨b, rfl⟩ := hx.2
      obtain ⟨c, rfl⟩ := dvd_of_dvd_prod_mul hj (fun i hi => hg i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_self j s) (fun h => hj (h ▸ hi))) hx.1
      exact Ideal.mem_span_singleton.mpr ⟨c, by ring⟩
    · exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _)
    · exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)

/-- The vanishing ideal of a finite union of closed subsets is the intersection of the vanishing
ideals, on every affine open. -/
private theorem ideal_vanishingIdeal_finset_sup {ι : Type*} (s : Finset ι)
    (Z : ι → TopologicalSpace.Closeds Y) (U : Y.affineOpens) :
    (Scheme.IdealSheafData.vanishingIdeal (s.sup Z)).ideal U =
      s.inf (fun i => (Scheme.IdealSheafData.vanishingIdeal (Z i)).ideal U) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sup_insert, Scheme.IdealSheafData.vanishingIdeal_sup, Finset.inf_insert, ← ih]
    rfl

/-- A reduced divisor is the sum of its prime components. -/
private theorem eq_sum_single_of_reduced {X : Scheme.{u}}
    (C : Divisor X) (hC : ∀ E ∈ C.support, C E = 1) :
    C = ∑ P ∈ C.support, Finsupp.single P (1 : ℤ) := by
  conv_lhs => rw [← Finsupp.sum_single C]
  exact Finset.sum_congr rfl fun P hP => by rw [hC P hP]

/-- The ideal sheaf of a prime divisor is the vanishing ideal of its support. -/
private theorem idealSheaf_eq_vanishingIdeal (P : MMP.Mori.PrimeDivisor Y) :
    P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal P.idealSheaf.support := by
  have := P.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl

/-- On an affine open `V` meeting a prime divisor `P`, the ideal of `P` on `V` is prime. -/
private theorem isPrime_ideal_primeDivisor (P : MMP.Mori.PrimeDivisor Y) (V : Y.affineOpens)
    (hPV : (P.support ∩ (V : Set Y)).Nonempty) : (P.idealSheaf.ideal V).IsPrime := by
  have hU : IsAffineOpen (V : Y.Opens) := V.2
  rw [idealSheaf_eq_vanishingIdeal, Scheme.IdealSheafData.vanishingIdeal_ideal,
    ← PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime]
  change IsIrreducible (hU.fromSpec ⁻¹' (P.support))
  refine IsIrreducible.preimage ?_ hU.fromSpec.isOpenEmbedding ?_
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  · rw [hU.range_fromSpec]
    exact hPV

/-- On an affine open `V` not meeting `P`, the ideal of `P` on `V` is the unit ideal. -/
private theorem ideal_primeDivisor_eq_top (P : MMP.Mori.PrimeDivisor Y) (V : Y.affineOpens)
    (hPV : ¬ (P.support ∩ (V : Set Y)).Nonempty) : P.idealSheaf.ideal V = ⊤ := by
  have hU : IsAffineOpen (V : Y.Opens) := V.2
  rw [idealSheaf_eq_vanishingIdeal, Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' (P.support)) = ⊤
  convert PrimeSpectrum.vanishingIdeal_empty
  refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => hPV ⟨_, hz, ?_⟩
  rw [← hU.range_fromSpec]
  exact ⟨z, rfl⟩

/-- Two prime divisors are equal if, on an affine open containing the generic point of the
second, the ideal of the first is contained in that of the second. -/
private theorem eq_of_ideal_le_ideal (P Q : MMP.Mori.PrimeDivisor Y) (V : Y.affineOpens)
    (hQ : Q.genericPoint ∈ (V : Set Y)) (hle : P.idealSheaf.ideal V ≤ Q.idealSheaf.ideal V) :
    P = Q := by
  have hQQ : Q.genericPoint ∈ Q.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hQP : Q.genericPoint ∈ P.support := by
    have h1 := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := Q.idealSheaf) hQ).mp hQQ
    refine (Scheme.IdealSheafData.mem_support_iff_of_mem (I := P.idealSheaf) hQ).mpr ?_
    rw [Scheme.mem_zeroLocus_iff] at h1 ⊢
    exact fun f hf => h1 f (hle hf)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hQP
  have hle' : Q.genericPoint ≤ P.genericPoint := Scheme.le_iff_specializes.mpr hQP
  by_contra hne
  have hlt : Q.genericPoint < P.genericPoint := by
    refine lt_of_le_not_ge hle' fun h => hne ?_
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (hQP.antisymm (Scheme.le_iff_specializes.mp h)).eq
  have := Order.coheight_add_one_le hlt
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint, MMP.Mori.PrimeDivisor.coheight_genericPoint]
    at this
  exact absurd this (by decide)

/-- **Local equations of a reduced curve.** On a locally Noetherian normal scheme on which the
ideal of every prime divisor is locally generated by a local equation, every point has an affine
neighbourhood `V` carrying, for each component `P` of a divisor `C`, a local equation `φ_P` of `P`
with regular representative `g_P` generating the ideal of `P` on `V`; and the ideal of the reduced
support of `C` on `V` is generated by `∏_P g_P`, since distinct components have non-associate
prime local equations. -/
private theorem exists_affineOpen_ideal_suppIdeal_eq_span_prod
    [IsLocallyNoetherian Y] [IsNormal Y]
    (hloc : ∀ (P : MMP.Mori.PrimeDivisor Y) (x : Y), ∃ U : Y.affineOpens, x ∈ (U : Y.Opens) ∧
      ∃ (g : Γ(Y, U)) (φ : (RationalFunctions Y)ˣ),
        (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (U : Y.Opens)),
          (φ : RationalFunctions Y) Z = Y.presheaf.germ U _ hZ g) ∧
        Divisor.IsLocalEquation (Finsupp.single P 1) U φ ∧
        P.idealSheaf.ideal U = Ideal.span {g})
    (C : Divisor Y) (x : Y) :
    ∃ V : Y.affineOpens, x ∈ (V : Y.Opens) ∧ ∃ (gP : MMP.Mori.PrimeDivisor Y → Γ(Y, V))
      (φP : MMP.Mori.PrimeDivisor Y → (RationalFunctions Y)ˣ),
      (∀ P ∈ C.support,
        (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
          (φP P : RationalFunctions Y) Z = Y.presheaf.germ V _ hZ (gP P)) ∧
        Divisor.IsLocalEquation (Finsupp.single P 1) V (φP P) ∧
        P.idealSheaf.ideal V = Ideal.span {gP P}) ∧
      C.suppIdeal.ideal V = Ideal.span {∏ P ∈ C.support, gP P} := by
  classical
  choose U hxU g φ hgerm hlocE hideal using hloc
  -- an affine neighbourhood of `x` inside the neighbourhoods of all components of `C`
  have hWo : IsOpen (⋂ P ∈ C.support, ((U P x : Y.Opens) : Set Y)) :=
    isOpen_biInter_finset fun P _ => (U P x : Y.Opens).isOpen
  have hxW : x ∈ ⋂ P ∈ C.support, ((U P x : Y.Opens) : Set Y) :=
    Set.mem_iInter₂.mpr fun P _ => hxU P x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hxW hWo
  let V' : Y.affineOpens := ⟨V, hV⟩
  have hVU : ∀ P ∈ C.support, V' ≤ U P x := fun P hP y hy =>
    Set.mem_iInter₂.mp (hVW hy) P hP
  -- the local data of each component, restricted to `V`
  have hdata : ∀ P ∈ C.support, ∃ gP : Γ(Y, V'),
      (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V' : Y.Opens)),
        (φ P x : RationalFunctions Y) Z = Y.presheaf.germ V' _ hZ gP) ∧
      Divisor.IsLocalEquation (Finsupp.single P 1) V' (φ P x) ∧
      P.idealSheaf.ideal V' = Ideal.span {gP} := by
    intro P hP
    refine ⟨Y.presheaf.map (homOfLE (hVU P hP)).op (g P x), fun Z hZ => ?_,
      (hlocE P x).mono (hVU P hP), ?_⟩
    · rw [hgerm P x Z (hVU P hP hZ)]
      exact (Y.presheaf.germ_res_apply _ _ _ _).symm
    · rw [← Scheme.IdealSheafData.map_ideal _ (hVU P hP), hideal P x, Ideal.map_span,
        Set.image_singleton]
  haveI : Nonempty Γ(Y, V') := ⟨0⟩
  choose! gP hgP hlP hiP using hdata
  refine ⟨V', hxV, gP, fun P => φ P x, fun P hP => ⟨hgP P hP, hlP P hP, hiP P hP⟩, ?_⟩
  rw [DivisorWithCoeffs.suppIdeal, DivisorWithCoeffs.supp, ideal_vanishingIdeal_finset_sup]
  rw [Finset.inf_congr rfl fun P hP => by rw [← idealSheaf_eq_vanishingIdeal, hiP P hP]]
  refine finset_inf_span_singleton_eq_span_prod _ _ fun i hi j hj hij a hdiv => ?_
  by_cases hjV : (j.support ∩ (V' : Set Y)).Nonempty
  · have hprime : (Ideal.span {gP j}).IsPrime := hiP j hj ▸ isPrime_ideal_primeDivisor j V' hjV
    rw [← Ideal.mem_span_singleton] at hdiv ⊢
    refine (hprime.mem_or_mem hdiv).resolve_left fun h => ?_
    obtain ⟨y, hyj, hyV⟩ := hjV
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hyj
    refine hij (eq_of_ideal_le_ideal i j V' (hyj.mem_open (V' : Y.Opens).isOpen hyV) ?_)
    rw [hiP i hi, hiP j hj]
    exact Ideal.span_singleton_le_span_singleton.mpr (Ideal.mem_span_singleton.mp h)
  · have hu : IsUnit (gP j) := by
      rw [← Ideal.span_singleton_eq_top, ← hiP j hj]
      exact ideal_primeDivisor_eq_top j V' hjV
    exact hu.dvd

end LocalEquations

section DivisorialSheaf

variable {F : Type u} [Field F] {X : Scheme.{u}} {sX : X ⟶ Spec (.of F)}

/-- **The adjunction sheaf of a reduced divisor.** On a smooth variety `X` of dimension `n` over a
field, with canonical divisor `K`, a reduced divisor `C` has an ideal sheaf which is an effective
Cartier divisor, and `𝒪_X(K + C) ≅ Ω^n_{X/F} ⊗ 𝒪_X(C)`, where `𝒪_X(C)` is the invertible sheaf of
the effective Cartier divisor `C.suppIdeal`. -/
private theorem nonempty_divisorialSheaf_add_iso [IsLocallyNoetherian X] [IsNormal X]
    (hX : MMP.Mori.IsVariety F sX) (hXs : IsSmoothScheme sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (C : Divisor X) (hC : ∀ E ∈ C.support, C E = 1) :
    Stacks.Divisors.IsEffectiveCartierDivisor C.suppIdeal ∧
      Nonempty ((K + C).divisorialSheaf ≅
        Scheme.Hom.relativeDifferentialForms sX n ⊗
          (Stacks.Divisors.invertibleSheaf' C.suppIdeal : X.Modules)) := by
  classical
  haveI := hX
  haveI : IsIntegral X := hX.toIsIntegral
  haveI hXsm : Smooth sX := (isSmoothScheme_iff sX).mp hXs
  haveI : IsSmoothVariety F sX := { toIsVariety := hX, toSmooth := hXsm }
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨hcart, hloc, -, -, -, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety F sX
  have hlocal : ∀ x : X, ∃ (W : X.affineOpens) (_ : x ∈ (W : X.Opens))
      (f : Γ(X, (W : X.Opens))) (φ : (RationalFunctions X)ˣ),
      C.suppIdeal.ideal W = Ideal.span {f} ∧ Divisor.IsLocalEquation C W φ ∧
      ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ (W : X.Opens)),
        (φ : RationalFunctions X) Z = (X.presheaf.germ W _ hZ).hom f := by
    intro x
    obtain ⟨V, hxV, gP, φP, hV, hCV⟩ := exists_affineOpen_ideal_suppIdeal_eq_span_prod hloc C x
    refine ⟨V, hxV, ∏ P ∈ C.support, gP P, ∏ P ∈ C.support, φP P, hCV, ?_, fun Z hZ => ?_⟩
    · have key : ∀ t ⊆ C.support, Divisor.IsLocalEquation (∑ P ∈ t, Finsupp.single P (1 : ℤ))
          V (∏ P ∈ t, φP P) := by
        intro t ht
        induction t using Finset.induction_on with
        | empty => simpa using Divisor.isLocalEquation_zero (V : X.Opens)
        | insert P t hPt ih =>
          rw [Finset.sum_insert hPt, Finset.prod_insert hPt]
          exact (hV P (ht (Finset.mem_insert_self P t))).2.1.add
            (ih fun Q hQ => ht (Finset.mem_insert_of_mem hQ))
      have h := key _ subset_rfl
      rwa [← eq_sum_single_of_reduced C hC] at h
    · rw [map_prod, Units.coe_prod, Finset.prod_apply]
      exact Finset.prod_congr rfl fun P hP => (hV P hP).1 Z hZ
  have hI : Stacks.Divisors.IsEffectiveCartierDivisor C.suppIdeal := by
    rw [Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal]
    intro x _
    obtain ⟨W, hxW, f, φ, hspan, -, hφ⟩ := hlocal x
    obtain ⟨e, he⟩ :=
      Stacks.Divisors.exists_quotient_chart_of_ideal_span C.suppIdeal W W.2 f hspan
    refine ⟨W, W.2, hxW, f, ?_, e, he⟩
    haveI : Nonempty (W : X.Opens) := ⟨⟨x, hxW⟩⟩
    have hf0 : f ≠ 0 := by
      intro h0
      let Z := MMP.Mori.pointComponent x
      have hmem : x ∈ Z.1 := by
        have h := Z.2
        simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h
        rw [h]
        trivial
      have hZW : componentGenericPoint X Z ∈ (W : X.Opens) :=
        ((isGenericPoint_componentGenericPoint X Z).specializes hmem).mem_open
          (W : X.Opens).isOpen hxW
      have h1 := hφ Z hZW
      rw [h0, map_zero] at h1
      haveI := (RationalFunctions.isField_stalk X Z).nontrivial
      exact (Pi.isUnit_iff.1 φ.isUnit Z).ne_zero h1
    exact IsRegular.of_ne_zero hf0
  have h0 : 0 ≤ C := fun P => by
    by_cases hP : P ∈ C.support
    · rw [hC P hP]; exact zero_le_one
    · rw [Finsupp.notMem_support_iff.mp hP]; rfl
  obtain ⟨eC⟩ := Resolution.nonempty_divisorialSheaf_iso_invertibleSheaf'_of_isLocalEquation
    C.suppIdeal C h0 (hcart C) hlocal
  obtain ⟨eK⟩ := MMP.Mori.nonempty_divisorialSheaf_iso_of_isCanonicalDivisor hXs hK
  exact ⟨hI, ⟨((hcart K).divisorialSheafTensorIso (hcart C)).symm ≪≫ whiskerRightIso eK _ ≪≫
    whiskerLeftIso _ eC⟩⟩

/-- **The degree as an Euler characteristic.** The degree of a Cartier divisor `D` along a curve
`i : C ⟶ X` proper over `k` is `χ(C, i^* M) - χ(C, 𝒪_C)` for every module `M ≅ 𝒪_X(D)`. -/
private theorem degreeOn_eq_eulerCharacteristic_sub_of_iso [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {D : Divisor X} (hD : D.IsCartier) {M : X.Modules}
    (e : D.divisorialSheaf ≅ M) [((Scheme.Modules.pullback i).obj M).IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent] :
    D.degreeOn F sX i hdim hD =
      eulerCharacteristic F (i ≫ sX) ((Scheme.Modules.pullback i).obj M) -
        eulerCharacteristic F (i ≫ sX) (SheafOfModules.unit C.ringCatSheaf) := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI : Stacks.Ample.IsInvertibleModule X M :=
    Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso e
  exact (invertibleCurveDegree_eq_of_iso F (i ≫ sX) hdim
    ((Scheme.Modules.pullback i).mapIso e)).trans
    (invertibleCurveDegree_eq_eulerCharacteristic_sub F _ hdim _)

end DivisorialSheaf

section ReducedCartier

/-- **A reduced effective Cartier divisor is the reduced support of a Weil divisor.** On a
Noetherian normal scheme, let `J` be an effective Cartier divisor with reduced closed subscheme.
Then there is a reduced divisor `D` with `D.suppIdeal = J`. -/
private theorem exists_divisor_suppIdeal_eq {Z : Scheme.{u}} [IsLocallyNoetherian Z] [IsNormal Z]
    [CompactSpace Z] (J : Z.IdealSheafData) [hJ : Stacks.Divisors.IsEffectiveCartierDivisor J]
    [IsReduced J.subscheme] :
    ∃ D : Divisor Z, (∀ E ∈ D.support, D E = 1) ∧ D.suppIdeal = J := by
  classical
  haveI : IsLocallyNoetherian J.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  haveI : CompactSpace J.subscheme := J.subschemeι.isClosedEmbedding.compactSpace
  haveI : IsNoetherian J.subscheme := ⟨⟩
  haveI : Finite (irreducibleComponents J.subscheme) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).to_subtype
  haveI : Fintype (irreducibleComponents J.subscheme) := Fintype.ofFinite _
  let ξ : irreducibleComponents J.subscheme → J.subscheme := fun Zc => Zc.2.1.genericPoint
  have hξ : ∀ Zc : irreducibleComponents J.subscheme, IsGenericPoint (ξ Zc) (Zc : Set _) := by
    intro Zc
    have h := Zc.2.1.isGenericPoint_genericPoint_closure
    rwa [(isClosed_of_mem_irreducibleComponents _ Zc.2).closure_eq] at h
  have hcoh : ∀ Zc, Order.coheight (J.subschemeι (ξ Zc)) = 1 := by
    intro Zc
    have h := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor J hJ (ξ Zc) ⟨Zc, hξ Zc⟩
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  let Q : irreducibleComponents J.subscheme → MMP.Mori.PrimeDivisor Z := fun Zc =>
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne (J.subschemeι (ξ Zc)) (hcoh Zc)
  let T : Finset (MMP.Mori.PrimeDivisor Z) := Finset.univ.image Q
  let D : Divisor Z := ∑ E ∈ T, Finsupp.single E (1 : ℤ)
  have hDapply : ∀ E, D E = if E ∈ T then 1 else 0 := by
    intro E
    simp only [D, Finsupp.finset_sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hDsupport : D.support = T := by
    ext E
    rw [Finsupp.mem_support_iff, hDapply]
    split_ifs with h <;> simp [h]
  refine ⟨D, fun E hE => ?_, ?_⟩
  · rw [hDsupport] at hE
    rw [hDapply, if_pos hE]
  · rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme J J.support rfl,
      DivisorWithCoeffs.suppIdeal]
    congr 1
    apply TopologicalSpace.Closeds.ext
    rw [DivisorWithCoeffs.coe_supp, hDsupport]
    apply subset_antisymm
    · refine Set.iUnion₂_subset fun E hE => ?_
      obtain ⟨Zc, -, rfl⟩ := Finset.mem_image.mp hE
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
      refine (J.support.isClosed.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr ?_)
      change J.subschemeι (ξ Zc) ∈ (J.support : Set Z)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨_, rfl⟩
    · intro z hz
      change z ∈ (J.support : Set Z) at hz
      rw [← Scheme.IdealSheafData.range_subschemeι] at hz
      obtain ⟨c, rfl⟩ := hz
      let Zc : irreducibleComponents J.subscheme :=
        ⟨irreducibleComponent c, irreducibleComponent_mem_irreducibleComponents c⟩
      refine Set.mem_iUnion₂.mpr ⟨Q Zc, Finset.mem_image_of_mem Q (Finset.mem_univ _), ?_⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne,
        ← specializes_iff_mem_closure]
      have hc : ξ Zc ⤳ c := by
        rw [specializes_iff_mem_closure, (hξ Zc).def]
        exact mem_irreducibleComponent
      exact hc.map J.subschemeι.continuous

end ReducedCartier

section AlgClosed

/-- **Adjunction over an algebraically closed field, at the level of Euler characteristics.**
Let `Z` be a smooth integral surface over an algebraically closed field `k` and `J` an effective
Cartier divisor on `Z` whose closed subscheme `C = V(J)` is reduced and proper over `k`. Then
`χ(C, i^*(Ω²_{Z/k} ⊗ 𝒪_Z(C))) = -χ(C, 𝒪_C)`. -/
private theorem eulerCharacteristic_adjunction_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    [IsIntegral Z] [IsSeparated sZ] [LocallyOfFiniteType sZ] [QuasiCompact sZ] [Smooth sZ]
    (hZd : topologicalKrullDim Z = 2)
    (J : Z.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor J] [IsReduced J.subscheme]
    [IsProper (J.subschemeι ≫ sZ)]
    [((Scheme.Modules.pullback J.subschemeι).obj
      (Scheme.Hom.relativeDifferentialForms sZ 2 ⊗
        (Stacks.Divisors.invertibleSheaf' J : Z.Modules))).IsCoherent]
    [(SheafOfModules.unit J.subscheme.ringCatSheaf).IsCoherent] :
    eulerCharacteristic k (J.subschemeι ≫ sZ)
        ((Scheme.Modules.pullback J.subschemeι).obj
          (Scheme.Hom.relativeDifferentialForms sZ 2 ⊗
            (Stacks.Divisors.invertibleSheaf' J : Z.Modules))) =
      -eulerCharacteristic k (J.subschemeι ≫ sZ)
        (SheafOfModules.unit J.subscheme.ringCatSheaf) := by
  haveI hvar : AlgebraicGeometry.IsVariety k sZ := ⟨⟩
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNormal Z := isNormal_of_smooth_over_field sZ
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsSmoothVariety k sZ := { toIsVariety := hvar, toSmooth := ‹_› }
  have hZs : IsSmoothScheme sZ := isSmoothScheme_of_smooth ‹_›
  obtain ⟨D, hD1, hDJ⟩ := exists_divisor_suppIdeal_eq J
  obtain ⟨K, hK⟩ := exists_isCanonicalDivisor_of_isSmoothScheme sZ hZs (n := 2)
    (by exact_mod_cast hZd)
  subst hDJ
  obtain ⟨hcart, -, -, -, -, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sZ
  obtain ⟨-, ⟨e⟩⟩ : _ ∧ Nonempty (_ ≅ Scheme.Hom.relativeDifferentialForms sZ 2 ⊗ _) :=
    nonempty_divisorialSheaf_add_iso hvar hZs hK D hD1
  obtain ⟨_, hdim, _, hval⟩ :=
    MMP.Threefold.isIntersectionNumber_canonical_add_eq_neg_two_mul_eulerCharacteristic
      hvar hZs hZd hK D hD1 ‹_›
  rw [QDivisor.intersectionNumber_toQDivisor k sZ _ hdim (K + D) (hcart _),
    degreeOn_eq_eulerCharacteristic_sub_of_iso _ hdim (hcart _) e] at hval
  rw [← Int.cast_inj (α := ℚ)]
  push_cast at hval ⊢
  linarith

end AlgClosed

section Decomposition

open Limits

/-- **A module on a finite disjoint union.** Let `f i : A i ⟶ Y` be finitely many immersions,
each open and closed, with pairwise disjoint ranges covering `Y`. Every `𝒪_Y`-module `M` is the
coproduct of the pushforwards of its restrictions: `M ≅ M ⊗ 𝒪_Y ≅ M ⊗ ∐ (f i)_* 𝒪_{A i}`, the
tensor product commutes with finite coproducts, and `M ⊗ (f i)_* 𝒪_{A i} ≅ (f i)_* (f i)^* M` by
the projection formula. -/
private noncomputable def disjointCoverIso {ι : Type u} [Fintype ι] {Y : Scheme.{u}}
    {A : ι → Scheme.{u}} (f : ∀ i, A i ⟶ Y) [∀ i, IsOpenImmersion (f i)]
    [∀ i, IsClosedImmersion (f i)]
    (hcover : ∀ y : Y, ∃ i x, (f i).base x = y)
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (f i).base) (Set.range (f j).base))
    (M : Y.Modules) :
    M ≅ ∐ fun i => (Scheme.Modules.pushforward (f i)).obj
      ((Scheme.Modules.pullback (f i)).obj M) := by
  let B := fun i ↦ (Scheme.Modules.pushforward (f i)).obj
    (SheafOfModules.unit (A i).ringCatSheaf)
  let G := (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj M
  haveI : PreservesFiniteColimits G :=
    Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj Y.sheaf M
  haveI : PreservesColimitsOfShape (Discrete ι) G :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence (Fintype.equivFin ι).symm) G
  let eO : SheafOfModules.unit Y.ringCatSheaf ≅ ∐ B :=
    structureSheafDisjointCoverIso A f hcover hdisj ≪≫ (biproduct.isoProduct B).symm ≪≫
      biproduct.isoCoproduct B
  exact (ρ_ M).symm ≪≫ G.mapIso eO ≪≫ PreservesCoproduct.iso G B ≪≫
    Sigma.mapIso fun i =>
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding Y.sheaf).app M).app (B i) ≪≫
        Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso (f i)
          (SheafOfModules.unit (A i).ringCatSheaf) M ≪≫
        (Scheme.Modules.pushforward (f i)).mapIso (λ_ ((Scheme.Modules.pullback (f i)).obj M))

/-- **The Euler characteristic is additive over a finite disjoint union.** Let `Y` be proper of
dimension at most one over a field, and `f i : A i ⟶ Y` finitely many immersions, each open and
closed, with pairwise disjoint ranges covering `Y`. Then `χ(Y, M) = ∑ i, χ(A i, (f i)^* M)` for
every coherent `M` whose restrictions are coherent. -/
private theorem eulerCharacteristic_eq_sum_of_disjoint_cover (k : Type u) [Field k]
    {ι : Type u} [Fintype ι] {Y : Scheme.{u}} {A : ι → Scheme.{u}} (f : ∀ i, A i ⟶ Y)
    [∀ i, IsOpenImmersion (f i)] [∀ i, IsClosedImmersion (f i)]
    (hcover : ∀ y : Y, ∃ i x, (f i).base x = y)
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (f i).base) (Set.range (f j).base))
    (p : Y ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim Y ≤ 1)
    (M : Y.Modules) [M.IsCoherent] [∀ i, ((Scheme.Modules.pullback (f i)).obj M).IsCoherent] :
    eulerCharacteristic k p M =
      ∑ i, eulerCharacteristic k (f i ≫ p) ((Scheme.Modules.pullback (f i)).obj M) := by
  classical
  let G := fun i => (Scheme.Modules.pullback (f i)).obj M
  let E := fun i => (Scheme.Modules.pushforward (f i)).obj (G i)
  have hdimA : ∀ i, topologicalKrullDim (A i) ≤ 1 := fun i =>
    (f i).isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  have hvan : ∀ m, 2 ≤ m → Limits.IsZero (cohomologyOverField k p M m) := fun m hm =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le k p M (d := 1)
      (by exact_mod_cast hdim) (by omega)
  have hvanA : ∀ i m, 2 ≤ m → Limits.IsZero (cohomologyOverField k (f i ≫ p) (G i) m) :=
    fun i m hm => isZero_cohomologyOverField_of_topologicalKrullDim_le k (f i ≫ p) (G i)
      (d := 1) (by exact_mod_cast hdimA i) (by omega)
  have hfr : ∀ n, Module.finrank k (cohomologyOverField k p M n) =
      ∑ i, Module.finrank k (cohomologyOverField k (f i ≫ p) (G i) n) := by
    intro n
    have e : M ≅ ⨁ E := disjointCoverIso f hcover hdisj M ≪≫ (biproduct.isoCoproduct E).symm
    have hpush : ∀ i, cohomologyOverField k (f i ≫ p) (G i) n ≅ cohomologyOverField k p (E i) n :=
      fun i => cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k (f i) p (G i) n
    have hfin : ∀ i, FiniteDimensional k (cohomologyOverField k p (E i) n) := fun i => by
      haveI := finiteDimensional_cohomologyOverField_of_isProper k (f i ≫ p) (G i) n
      exact Module.Finite.equiv (hpush i).toLinearEquiv
    rw [(cohomologyOverFieldIso k p e n).toLinearEquiv.finrank_eq,
      finrank_cohomologyOverField_biproduct k p E n hfin]
    exact Finset.sum_congr rfl fun i _ => ((hpush i).toLinearEquiv.finrank_eq).symm
  rw [eulerCharacteristic_eq_sub_of_isZero k p M hvan, hfr 0, hfr 1]
  rw [Finset.sum_congr rfl fun i _ =>
    eulerCharacteristic_eq_sub_of_isZero k (f i ≫ p) (G i) (hvanA i)]
  push_cast
  rw [Finset.sum_sub_distrib]

end Decomposition

section Components

open Limits

/-- **Pulling back the adjunction sheaf.** Along a flat morphism `ψ : Z ⟶ X` over a commutative
square `ψ ≫ p = p' ≫ g` on which the comparison map of differential forms is an isomorphism, the
adjunction sheaf `Ω^n_{X/S} ⊗ 𝒪_X(J)` pulls back to `Ω^n_{Z/S'} ⊗ 𝒪_Z(ψ⁻¹ J)`. -/
private noncomputable def pullbackAdjunctionSheafIso {S S' X Z : Scheme.{u}}
    (p : X ⟶ S) (p' : Z ⟶ S') (g : S' ⟶ S) (ψ : Z ⟶ X) (hc : ψ ≫ p = p' ≫ g) [Flat ψ]
    (n : ℤ) (J : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor J]
    (hiso : IsIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' g hc n)) :
    (Scheme.Modules.pullback ψ).obj (Scheme.Hom.relativeDifferentialForms p n ⊗
        (Stacks.Divisors.invertibleSheaf' J : X.Modules)) ≅
      Scheme.Hom.relativeDifferentialForms p' n ⊗
        (Stacks.Divisors.invertibleSheaf' (J.comap ψ) : Z.Modules) := by
  haveI : Stacks.Divisors.IsPullbackDefined ψ J := Stacks.Divisors.isPullbackDefined_of_flat ψ J ‹_›
  exact (Stacks.PullbackTensorIso.pullbackTensorIso ψ.toLRSHom.toShHom).app
      (Scheme.Hom.relativeDifferentialForms p n,
        (Stacks.Divisors.invertibleSheaf' J : X.Modules)) ≪≫
    tensorIso (@asIso _ _ _ _ (Scheme.Hom.relativeDifferentialFormsMap ψ p p' g hc n) hiso)
      (Stacks.Divisors.invertibleSheafPullbackIso ψ J)

/-- The Euler characteristic depends on the structure morphism only through its value. -/
private theorem eulerCharacteristic_congr_hom {k : Type u} [Field k] {X : Scheme.{u}}
    {f g : X ⟶ Spec (.of k)} (h : f = g) [IsProper f] [IsProper g] (M : X.Modules)
    [M.IsCoherent] : eulerCharacteristic k f M = eulerCharacteristic k g M := by
  subst h
  rfl

/-- The closed subscheme of the pullback of an ideal sheaf is the fibre product. -/
private theorem isPullback_comap_subschemeι {X Z : Scheme.{u}} (ψ : Z ⟶ X)
    (J : X.IdealSheafData) :
    IsPullback (J.comap ψ).subschemeι (Scheme.IdealSheafData.subschemeMap (J.comap ψ) J ψ
      (J.le_map_comap ψ)) ψ J.subschemeι :=
  IsPullback.of_iso_pullback ⟨(Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm⟩
    (J.comapIso ψ) (by simp) (by simp)

/-- **Pulling back the adjunction sheaf to the subscheme of a pulled-back divisor.** In the
situation of `pullbackAdjunctionSheafIso`, the restriction of `Ω^n_{X/S} ⊗ 𝒪_X(J)` to `V(J)`
pulls back along `V(ψ⁻¹ J) ⟶ V(J)` to the restriction of `Ω^n_{Z/S'} ⊗ 𝒪_Z(ψ⁻¹ J)`. -/
private noncomputable def comapAdjunctionSheafIso {S S' X Z : Scheme.{u}}
    (p : X ⟶ S) (p' : Z ⟶ S') (g : S' ⟶ S) (ψ : Z ⟶ X) (hc : ψ ≫ p = p' ≫ g) [Flat ψ]
    (n : ℤ) (J : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor J]
    (hiso : IsIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' g hc n)) :
    (Scheme.Modules.pullback (Scheme.IdealSheafData.subschemeMap (J.comap ψ) J ψ
        (J.le_map_comap ψ))).obj ((Scheme.Modules.pullback J.subschemeι).obj
          (Scheme.Hom.relativeDifferentialForms p n ⊗
            (Stacks.Divisors.invertibleSheaf' J : X.Modules))) ≅
      (Scheme.Modules.pullback (J.comap ψ).subschemeι).obj
        (Scheme.Hom.relativeDifferentialForms p' n ⊗
          (Stacks.Divisors.invertibleSheaf' (J.comap ψ) : Z.Modules)) :=
  (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (pullbackAdjunctionSheafIso p p' g ψ hc n J hiso)

/-- A clopen irreducible component equals every irreducible component it meets. -/
private theorem eq_of_mem_irreducibleComponents {X : Type*} [TopologicalSpace X]
    {Z Z' : Set X} (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X)
    (hc : IsClopen Z) (h : (Z ∩ Z').Nonempty) : Z = Z' := by
  have hsub : Z' ⊆ Z := hZ'.prop.2.isPreconnected.subset_isClopen hc (by rwa [Set.inter_comm])
  exact (hZ'.eq_of_subset hZ.1 hsub).symm

/-- For a scheme over a field, the local dimension of the fibre agrees with that of the scheme. -/
private theorem topologicalKrullDimAt_fiber_eq_of_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = topologicalKrullDimAt X x := by
  have := isIso_fromSpecResidueField_of_field k (f x)
  have : IsIso (f.fiberι (f x)) := by
    change IsIso (pullback.fst f ((Spec (.of k)).fromSpecResidueField (f x))); infer_instance
  let he := (asIso (f.fiberι (f x))).hom.homeomorph
  rw [topologicalKrullDimAt_eq_of_homeomorph he]
  have hpoint : he (f.asFiber x) = x := by
    simp [he]
  rw [hpoint]

/-- **Local dimension is unchanged by extension of the ground field.** -/
private theorem topologicalKrullDimAt_eq_of_isPullback (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] {X' X : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of k'))
    (f : X ⟶ Spec (.of k)) (h : IsPullback g' f' f (specMapAlgebraMap k k'))
    [LocallyOfFiniteType f] (x' : X') :
    topologicalKrullDimAt X' x' = topologicalKrullDimAt X (g' x') := by
  rw [← topologicalKrullDimAt_fiber_eq_of_field k' f' x',
    topologicalKrullDimAt_fiber_eq_of_isPullback h x',
    topologicalKrullDimAt_fiber_eq_of_field k f (g' x')]

end Components

section Assembly

open Limits

/-- **Adjunction over an algebraically closed field, for a possibly disconnected surface.** Let
`W` be smooth, separated and of finite type over an algebraically closed field, of dimension two
at every point, and `J` an effective Cartier divisor with reduced proper subscheme `C` of
dimension at most one. Then `χ(C, i^*(Ω²_{W/k} ⊗ 𝒪_W(C))) = -χ(C, 𝒪_C)`. -/
private theorem eulerCharacteristic_adjunction_of_isAlgClosed_of_smooth
    {k : Type u} [Field k] [IsAlgClosed k] {W : Scheme.{u}} (sW : W ⟶ Spec (.of k))
    [IsSeparated sW] [LocallyOfFiniteType sW] [QuasiCompact sW] [Smooth sW]
    (hWd : ∀ w : W, topologicalKrullDimAt W w = 2)
    (J : W.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor J] [IsReduced J.subscheme]
    [IsProper (J.subschemeι ≫ sW)] (hdim : topologicalKrullDim J.subscheme ≤ 1)
    [Stacks.Ample.IsInvertibleModule W (Scheme.Hom.relativeDifferentialForms sW 2 ⊗
        (Stacks.Divisors.invertibleSheaf' J : W.Modules) : W.Modules)]
    [((Scheme.Modules.pullback J.subschemeι).obj
      (Scheme.Hom.relativeDifferentialForms sW 2 ⊗
        (Stacks.Divisors.invertibleSheaf' J : W.Modules))).IsCoherent]
    [(SheafOfModules.unit J.subscheme.ringCatSheaf).IsCoherent] :
    eulerCharacteristic k (J.subschemeι ≫ sW)
        ((Scheme.Modules.pullback J.subschemeι).obj
          (Scheme.Hom.relativeDifferentialForms sW 2 ⊗
            (Stacks.Divisors.invertibleSheaf' J : W.Modules))) =
      -eulerCharacteristic k (J.subschemeι ≫ sW)
        (SheafOfModules.unit J.subscheme.ringCatSheaf) := by
  classical
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsNormal W := isNormal_of_smooth_over_field sW
  haveI : IsNoetherian W := ⟨⟩
  haveI : IsLocallyNoetherian J.subscheme := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  haveI : Finite (irreducibleComponents W) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).to_subtype
  haveI : Fintype (irreducibleComponents W) := Fintype.ofFinite _
  have hclopen : ∀ Z : irreducibleComponents W, IsClopen (Z : Set W) := fun Z =>
    isClopen_of_mem_irreducibleComponents Z.2
  let U : irreducibleComponents W → W.Opens := fun Z => ⟨Z, (hclopen Z).isOpen⟩
  let g : ∀ Z, (J.comap (U Z).ι).subscheme ⟶ J.subscheme := fun Z =>
    Scheme.IdealSheafData.subschemeMap (J.comap (U Z).ι) J (U Z).ι (J.le_map_comap _)
  have hg : ∀ Z, g Z = (J.comapIso (U Z).ι).hom ≫ pullback.snd (U Z).ι J.subschemeι := fun Z =>
    (Scheme.IdealSheafData.comapIso_hom_snd _ _).symm
  haveI : ∀ Z, IsClosedImmersion (U Z).ι := fun Z =>
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact (hclopen Z).isClosed)
  haveI : ∀ Z, IsOpenImmersion (g Z) := fun Z => by rw [hg]; infer_instance
  haveI : ∀ Z, IsClosedImmersion (g Z) := fun Z => by rw [hg]; infer_instance
  have hcover : ∀ y : J.subscheme, ∃ Z x, (g Z) x = y := by
    intro y
    let Z : irreducibleComponents W := ⟨irreducibleComponent (J.subschemeι y),
      irreducibleComponent_mem_irreducibleComponents _⟩
    have hw : J.subschemeι y ∈ U Z := mem_irreducibleComponent
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := (U Z).ι)
      (g := J.subschemeι) ⟨_, hw⟩ y rfl
    refine ⟨Z, (J.comapIso (U Z).ι).inv z, ?_⟩
    rw [hg, ← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc, hz]
  have hmem : ∀ (Z : irreducibleComponents W) a, J.subschemeι (g Z a) ∈ (Z : Set W) := by
    intro Z a
    rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.subschemeMap_subschemeι,
      Scheme.Hom.comp_apply]
    have h := Set.mem_range_self (f := (U Z).ι) ((J.comap (U Z).ι).subschemeι a)
    rwa [Scheme.Opens.range_ι] at h
  have hdisj : Pairwise fun Z Z' ↦ Disjoint (Set.range (g Z)) (Set.range (g Z')) := by
    intro Z Z' hne
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact hne (Subtype.ext
      (eq_of_mem_irreducibleComponents Z.2 Z'.2 (hclopen Z) ⟨_, hmem Z a, hb ▸ hmem Z' b⟩))
  haveI : ∀ Z, IsLocallyNoetherian (J.comap (U Z).ι).subscheme := fun Z =>
    LocallyOfFiniteType.isLocallyNoetherian (J.comap (U Z).ι).subschemeι
  haveI : ∀ Z, ((Scheme.Modules.pullback (g Z)).obj ((Scheme.Modules.pullback J.subschemeι).obj
      (Scheme.Hom.relativeDifferentialForms sW 2 ⊗
        (Stacks.Divisors.invertibleSheaf' J : W.Modules)))).IsCoherent := fun Z =>
    isCoherent_pullback _ _
  haveI : ∀ Z, ((Scheme.Modules.pullback (g Z)).obj
      (SheafOfModules.unit J.subscheme.ringCatSheaf)).IsCoherent := fun Z =>
    isCoherent_pullback _ _
  rw [eulerCharacteristic_eq_sum_of_disjoint_cover k g hcover hdisj _ hdim,
    eulerCharacteristic_eq_sum_of_disjoint_cover k g hcover hdisj _ hdim
      (SheafOfModules.unit J.subscheme.ringCatSheaf), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun Z _ => ?_
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor (J.comap (U Z).ι) :=
    Stacks.Divisors.isPullbackDefined_of_flat (U Z).ι J ‹_›
  have hc : (U Z).ι ≫ sW = ((U Z).ι ≫ sW) ≫ 𝟙 _ := (Category.comp_id _).symm
  have hiso := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale (U Z).ι sW ((U Z).ι ≫ sW)
    (𝟙 _) hc 2
  have hfac : g Z ≫ J.subschemeι ≫ sW = (J.comap (U Z).ι).subschemeι ≫ (U Z).ι ≫ sW := by
    rw [← Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι, Category.assoc]
  haveI : IsProper ((J.comap (U Z).ι).subschemeι ≫ (U Z).ι ≫ sW) := by
    rw [← hfac]; infer_instance
  haveI : IsReduced (J.comap (U Z).ι).subscheme := isReduced_of_isOpenImmersion (g Z)
  haveI : IrreducibleSpace (U Z) := Subtype.irreducibleSpace Z.2.1
  haveI : IsIntegral (U Z) := isIntegral_of_irreducibleSpace_of_isReduced _
  have hUd : topologicalKrullDim (U Z) = 2 := by
    obtain ⟨w, hw⟩ := Z.2.1.nonempty
    let x : (U Z).toScheme := ⟨w, hw⟩
    rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k (U Z) ((U Z).ι ≫ sW) x,
      ← (U Z).ι.isOpenEmbedding.topologicalKrullDimAt_eq x]
    exact hWd _
  haveI : Stacks.Ample.IsInvertibleModule (U Z)
      (Scheme.Hom.relativeDifferentialForms ((U Z).ι ≫ sW) 2 ⊗
        (Stacks.Divisors.invertibleSheaf' (J.comap (U Z).ι) : (U Z).toScheme.Modules) :
          (U Z).toScheme.Modules) :=
    Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
      (pullbackAdjunctionSheafIso sW ((U Z).ι ≫ sW) (𝟙 _) (U Z).ι hc 2 J hiso)
  haveI : ((Scheme.Modules.pullback (J.comap (U Z).ι).subschemeι).obj
      (Scheme.Hom.relativeDifferentialForms ((U Z).ι ≫ sW) 2 ⊗
        (Stacks.Divisors.invertibleSheaf' (J.comap (U Z).ι) :
          (U Z).toScheme.Modules))).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible _ _
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    ((J.comap (U Z).ι).subschemeι ≫ (U Z).ι ≫ sW)
  rw [eulerCharacteristic_congr_hom hfac, eulerCharacteristic_congr_hom hfac,
    eulerCharacteristic_eq_of_iso _ _
      (comapAdjunctionSheafIso sW ((U Z).ι ≫ sW) (𝟙 _) (U Z).ι hc 2 J hiso),
    eulerCharacteristic_eq_of_iso _ _
      (Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjUnitIso _)]
  exact eulerCharacteristic_adjunction_of_isAlgClosed ((U Z).ι ≫ sW) hUd (J.comap (U Z).ι)

/-- **Adjunction over a perfect field, at the level of Euler characteristics.** Let `Y` be a
smooth surface over a perfect field `k` and `J` an effective Cartier divisor on `Y` whose closed
subscheme `C` is reduced, proper over `k` and of dimension at most one. Then
`χ(C, i^*(Ω²_{Y/k} ⊗ 𝒪_Y(C))) = -χ(C, 𝒪_C)`. -/
private theorem eulerCharacteristic_adjunction_of_perfectField
    {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsIntegral Y] [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY] [Smooth sY]
    (hYd : topologicalKrullDim Y = 2)
    (J : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor J] [IsReduced J.subscheme]
    [IsProper (J.subschemeι ≫ sY)] (hdim : topologicalKrullDim J.subscheme ≤ 1)
    [Stacks.Ample.IsInvertibleModule Y (Scheme.Hom.relativeDifferentialForms sY 2 ⊗
        (Stacks.Divisors.invertibleSheaf' J : Y.Modules) : Y.Modules)]
    [((Scheme.Modules.pullback J.subschemeι).obj
      (Scheme.Hom.relativeDifferentialForms sY 2 ⊗
        (Stacks.Divisors.invertibleSheaf' J : Y.Modules))).IsCoherent]
    [(SheafOfModules.unit J.subscheme.ringCatSheaf).IsCoherent] :
    eulerCharacteristic k (J.subschemeι ≫ sY)
        ((Scheme.Modules.pullback J.subschemeι).obj
          (Scheme.Hom.relativeDifferentialForms sY 2 ⊗
            (Stacks.Divisors.invertibleSheaf' J : Y.Modules))) =
      -eulerCharacteristic k (J.subschemeι ≫ sY)
        (SheafOfModules.unit J.subscheme.ringCatSheaf) := by
  have hPB := IsPullback.of_hasPullback sY (specMapAlgebraMap k (AlgebraicClosure k))
  set g := specMapAlgebraMap k (AlgebraicClosure k)
  set ψ := pullback.fst sY g
  set sW := pullback.snd sY g
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor (J.comap ψ) :=
    Stacks.Divisors.isPullbackDefined_of_flat ψ J ‹_›
  have hsq : IsPullback (Scheme.IdealSheafData.subschemeMap (J.comap ψ) J ψ (J.le_map_comap ψ))
      ((J.comap ψ).subschemeι ≫ sW) (J.subschemeι ≫ sY) g :=
    (isPullback_comap_subschemeι ψ J).flip.paste_vert hPB
  haveI : IsProper ((J.comap ψ).subschemeι ≫ sW) :=
    isProper_of_isPullback_specMapAlgebraMap k _ _ _ _ hsq
  haveI : GeometricallyReduced (J.subschemeι ≫ sY) := geometricallyReduced_of_isReduced _
  haveI : IsReduced (J.comap ψ).subscheme :=
    GeometricallyReduced.geometrically_isReduced _ _ _ hsq
  have hdim' : topologicalKrullDim (J.comap ψ).subscheme ≤ 1 := by
    rwa [topologicalKrullDim_baseChange k _ _ _ _ hsq]
  have hWd : ∀ w : ↥(pullback sY g), topologicalKrullDimAt ↥(pullback sY g) w = 2 := by
    intro w
    rw [topologicalKrullDimAt_eq_of_isPullback k _ ψ sW sY hPB w,
      ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Y sY, hYd]
  have hiso := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback ψ sY sW g hPB 2
  haveI : Stacks.Ample.IsInvertibleModule (pullback sY g)
      (Scheme.Hom.relativeDifferentialForms sW 2 ⊗
        (Stacks.Divisors.invertibleSheaf' (J.comap ψ) : (pullback sY g).Modules) :
          (pullback sY g).Modules) :=
    Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
      (pullbackAdjunctionSheafIso sY sW g ψ hPB.w 2 J hiso)
  haveI : IsLocallyNoetherian (pullback sY g) := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsLocallyNoetherian (J.comap ψ).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (J.comap ψ).subschemeι
  haveI : ((Scheme.Modules.pullback (J.comap ψ).subschemeι).obj
      (Scheme.Hom.relativeDifferentialForms sW 2 ⊗
        (Stacks.Divisors.invertibleSheaf' (J.comap ψ) : (pullback sY g).Modules))).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible _ _
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit (AlgebraicClosure k)
    ((J.comap ψ).subschemeι ≫ sW)
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsLocallyNoetherian J.subscheme := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  rw [eulerCharacteristic_baseChange_field k _ _ _ _ hsq,
    eulerCharacteristic_baseChange_field k _ _ _ _ hsq (SheafOfModules.unit _)]
  haveI := isCoherent_pullback (Scheme.IdealSheafData.subschemeMap (J.comap ψ) J ψ
    (J.le_map_comap ψ)) (SheafOfModules.unit J.subscheme.ringCatSheaf)
  haveI := isCoherent_pullback (Scheme.IdealSheafData.subschemeMap (J.comap ψ) J ψ
    (J.le_map_comap ψ)) ((Scheme.Modules.pullback J.subschemeι).obj
      (Scheme.Hom.relativeDifferentialForms sY 2 ⊗
        (Stacks.Divisors.invertibleSheaf' J : Y.Modules)))
  rw [eulerCharacteristic_eq_of_iso _ _ (comapAdjunctionSheafIso sY sW g ψ hPB.w 2 J hiso),
    eulerCharacteristic_eq_of_iso _ _ (Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjUnitIso _)]
  exact eulerCharacteristic_adjunction_of_isAlgClosed_of_smooth sW hWd (J.comap ψ) hdim'

end Assembly

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- **Adjunction for a reduced curve on a smooth surface over a perfect field.** Let `Y` be a
smooth surface over a perfect field `k`, `K` a canonical divisor of `Y` and `C = ∑ Cᵢ` a reduced
divisor whose support is proper over `k`. Then the intersection number `((K + C) · C)` is defined
and equals `-2 χ(C, 𝒪_C)`, where `C` is the reduced closed subscheme on the support. -/
@[mmp "thm_mmp_threefold_surface_adjunction_perfect_field"]
public theorem isIntersectionNumber_canonical_add_eq_neg_two_mul_eulerCharacteristic_of_perfectField
    [PerfectField k] [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : Mori.IsVariety k sY) (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor sY 2)
    (C : Divisor Y) (hC : ∀ E ∈ C.support, C E = 1)
    (hCp : IsProper (C.suppIdeal.subschemeι ≫ sY)) :
    haveI := hCp
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (C.suppIdeal.subschemeι ≫ sY)
    IsIntersectionNumber sY (Divisor.toQDivisor (K + C)) C.suppIdeal
      (-2 * eulerCharacteristic k (C.suppIdeal.subschemeι ≫ sY)
        (SheafOfModules.unit C.suppIdeal.subscheme.ringCatSheaf)) := by
  haveI := hCp
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    (C.suppIdeal.subschemeι ≫ sY)
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI := hY
  haveI hYsm : Smooth sY := (isSmoothScheme_iff sY).mp hYs
  haveI : IsSmoothVariety k sY := { toIsVariety := hY, toSmooth := hYsm }
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsReduced C.suppIdeal.subscheme := by
    unfold DivisorWithCoeffs.suppIdeal
    infer_instance
  obtain ⟨hcart, -, -, -, -, hQ⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sY
  obtain ⟨hJ, ⟨e⟩⟩ : _ ∧ Nonempty (_ ≅ Scheme.Hom.relativeDifferentialForms sY 2 ⊗ _) :=
    nonempty_divisorialSheaf_add_iso hY hYs hK C hC
  haveI := hJ
  have hdim := topologicalKrullDim_suppIdeal_subscheme_le_one hY hYd C
  haveI := (hcart (K + C)).isInvertibleModule_divisorialSheaf
  haveI : Stacks.Ample.IsInvertibleModule Y
      (Scheme.Hom.relativeDifferentialForms sY 2 ⊗
        (Stacks.Divisors.invertibleSheaf' C.suppIdeal : Y.Modules) : Y.Modules) :=
    Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso e
  haveI : IsLocallyNoetherian C.suppIdeal.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian C.suppIdeal.subschemeι
  haveI : ((Scheme.Modules.pullback C.suppIdeal.subschemeι).obj
      (Scheme.Hom.relativeDifferentialForms sY 2 ⊗
        (Stacks.Divisors.invertibleSheaf' C.suppIdeal : Y.Modules))).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible _ _
  refine ⟨hCp, hdim, hQ _, ?_⟩
  rw [QDivisor.intersectionNumber_toQDivisor k sY _ hdim (K + C) (hcart _),
    degreeOn_eq_eulerCharacteristic_sub_of_iso _ hdim (hcart _) e,
    eulerCharacteristic_adjunction_of_perfectField sY hYd C.suppIdeal hdim]
  push_cast
  ring

end MMP.Threefold

/-! ### A canonical-negative exceptional curve over a perfect field -/

namespace MMP.Threefold

open AlgebraicGeometry MMP.Mori

/-- **The degree over a subfield.** For two compatible structure morphisms of a proper scheme `Z`
of dimension at most one, to `Spec k` and to `Spec κ` with `κ / k` a field extension, the degree
of an invertible module over `k` is `[κ : k]` times its degree over `κ`. -/
private theorem invertibleCurveDegree_eq_finrank_mul (k κ : Type u) [Field k] [Field κ]
    [Algebra k κ] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) [IsProper f]
    (g : Z ⟶ Spec (.of κ)) [IsProper g]
    (hcompat : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom =
      ((Scheme.ΓSpecIso (.of κ)).inv ≫ g.appTop).hom.comp (algebraMap k κ))
    (hdim : topologicalKrullDim Z ≤ 1) (L : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L] :
    invertibleCurveDegree k f hdim L =
      (Module.finrank k κ : ℤ) * invertibleCurveDegree κ g hdim L := by
  rw [invertibleCurveDegree_eq_sub_of_isZero k f hdim L
      (isZero_cohomologyOverField_two_le k f hdim L)
      (isZero_cohomologyOverField_two_le k f hdim _),
    invertibleCurveDegree_eq_sub_of_isZero κ g hdim L
      (isZero_cohomologyOverField_two_le κ g hdim L)
      (isZero_cohomologyOverField_two_le κ g hdim _)]
  rw [finrank_cohomologyOverField_eq_finrank_mul k κ f g hcompat L 0,
    finrank_cohomologyOverField_eq_finrank_mul k κ f g hcompat L 1,
    finrank_cohomologyOverField_eq_finrank_mul k κ f g hcompat
      (SheafOfModules.unit Z.ringCatSheaf) 0,
    finrank_cohomologyOverField_eq_finrank_mul k κ f g hcompat
      (SheafOfModules.unit Z.ringCatSheaf) 1]
  push_cast
  ring

/-- **The numerical core of adjunction over the field of constants.** If `d > 0`, the integers
`d a` and `d b` are negative and `d b + d a = -2 (d - d g)` with `g` a natural number, then
`a = b = -1` and `g = 0`. -/
private theorem eq_neg_one_of_mul_add_mul_eq {d a b : ℤ} {g : ℕ} (hd : 0 < d) (ha : d * a < 0)
    (hb : d * b < 0) (h : d * b + d * a = -2 * (d - d * g)) : a = -1 ∧ b = -1 ∧ g = 0 := by
  have hab : b + a = 2 * g - 2 := mul_left_cancel₀ hd.ne' (by linarith)
  have := neg_of_mul_neg_right ha hd.le
  have := neg_of_mul_neg_right hb hd.le
  omega

open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff) in
/-- **A curve isomorphic to `ℙ¹_κ` with conormal degree one is of the first kind.** Let `D` be an
effective Cartier divisor on `X`, proper over a field `κ` through `g`, and `e : ℙ¹_κ ≅ D` an
isomorphism over `κ`. If `𝒪_X(D)|_D` has degree `-1` over `κ`, then the normal sheaf of `D`
pulls back along `e` to `𝒪(-1)`. -/
private theorem isExceptionalCurveOfFirstKind_of_invertibleCurveDegree_eq_neg_one
    {X : Scheme.{u}} (κ : Type u) [Field κ] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (g : D.subscheme ⟶ Spec (.of κ))
    [IsProper g] (hdim : topologicalKrullDim D.subscheme ≤ 1)
    (e : projectiveLineProj κ ≅ D.subscheme) (he : e.hom ≫ g = projToSpecCoeff κ 1)
    [SheafOfModules.IsInvertible D.subscheme.presheaf D.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback D.subschemeι).obj
        (Stacks.Divisors.invertibleSheaf' D : X.Modules))]
    (hdeg : invertibleCurveDegree κ g hdim ((Scheme.Modules.pullback D.subschemeι).obj
      (Stacks.Divisors.invertibleSheaf' D : X.Modules)) = -1) :
    D.IsExceptionalCurveOfFirstKind κ e := by
  refine ⟨hD, ?_⟩
  obtain ⟨n, ⟨φ⟩⟩ := AlgebraicGeometry.ExceptionalCurveContraction.exists_iso_twistingSheaf_pullback
    (e := e) (Stacks.Divisors.invertibleSheaf' D)
  suffices n = -1 by
    subst this
    exact ⟨(RingedSpaceModuleAdjunction.modulePullback e.hom.toLRSHom.toShHom).mapIso
      (Stacks.Divisors.normalSheafIsoInvertibleSheaf D) ≪≫ φ⟩
  haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff κ 1
  have hdimP := (topologicalKrullDim_projectiveLineProj κ).le
  haveI hP : SheafOfModules.IsInvertible (projectiveLineProj κ).presheaf
      (projectiveLineProj κ).ringCatSheaf.2 ((Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback D.subschemeι).obj
          (Stacks.Divisors.invertibleSheaf' D : X.Modules))) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      e.hom.toLRSHom.toShHom _ inferInstance
  have h : ∀ (g' : projectiveLineProj κ ⟶ Spec (.of κ)) [IsProper g'], e.hom ≫ g = g' →
      invertibleCurveDegree κ g' hdimP ((Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback D.subschemeι).obj
          (Stacks.Divisors.invertibleSheaf' D : X.Modules))) = -1 := by
    rintro _ _ rfl
    rw [← hdeg]
    unfold invertibleCurveDegree
    congr 1
    · exact finsum_congr fun n => by rw [finrank_cohomologyOverField_pullback κ e.hom _ _ n]
    · exact finsum_congr fun n => by rw [finrank_cohomologyOverField_unit_pushforward κ e.hom _ n]
  have := h _ he
  have h' := (@invertibleCurveDegree_eq_of_iso κ _ _ (projToSpecCoeff κ 1) _ hdimP _ _ hP
    (Stacks.PicardUFD.isInvertible_twistingSheaf κ 1 n) φ).trans
    (invertibleCurveDegree_twistingSheaf_projectiveLineProj κ n)
  omega

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)}

open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff) in
/-- **A canonical-negative exceptional curve over a perfect field is a `(-1)`-curve over its
field of constants.** Let `f : X ⟶ Y` be a projective, generically finite morphism of varieties
over a perfect field `k`, with `Y` quasi-projective and `X` a smooth surface with canonical
divisor `K`, and let `E` be an `f`-exceptional prime divisor with `(K · E) < 0`. Then there are a
finite separable extension `κ / k` and an isomorphism `e : ℙ¹_κ ≅ E` over `k` making `E` an
exceptional curve of the first kind, i.e. `𝒪_X(E)|_E ≅ 𝒪(-1)`, and `(E · E) = (K · E) = -[κ : k]`.
-/
@[mmp "lem_mmp_threefold_k_negative_curve_perfect"]
public theorem exists_isExceptionalCurveOfFirstKind_of_canonical_intersection_neg
    [PerfectField k] [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (hX : Mori.IsVariety k sX) (hsm : IsSmoothScheme sX) (hdim : topologicalKrullDim X = 2)
    (hY : Mori.IsVariety k sY) (hYqp : Stacks.HProjective.IsHQuasiProjective sY)
    {f : X ⟶ Y} (hfs : f ≫ sY = sX) (hproj : IsProjectiveMorphism f)
    (hgf : ∃ V : Y.Opens, ((V : Set Y) ∩ Set.range f.base).Nonempty ∧ IsFinite (f ∣_ V))
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2)
    (E : Mori.PrimeDivisor X) (hE : Mori.IsExceptionalCurve f E.idealSheaf)
    (hKE : ∃ n : ℚ, n < 0 ∧ IsIntersectionNumber sX (Divisor.toQDivisor K) E.idealSheaf n) :
    ∃ (κ : Type u) (_ : Field κ) (_ : Algebra k κ),
      FiniteDimensional k κ ∧ Algebra.IsSeparable k κ ∧
      ∃ e : projectiveLineProj κ ≅ E.idealSheaf.subscheme,
        e.hom ≫ E.idealSheaf.subschemeι ≫ sX =
            projToSpecCoeff κ 1 ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)) ∧
          E.idealSheaf.IsExceptionalCurveOfFirstKind κ e ∧
          IsIntersectionNumber sX (Divisor.toQDivisor (Finsupp.single E 1)) E.idealSheaf
            (-(Module.finrank k κ : ℚ)) ∧
          IsIntersectionNumber sX (Divisor.toQDivisor K) E.idealSheaf
            (-(Module.finrank k κ : ℚ)) := by
  classical
  obtain ⟨⟨hint, hdimE⟩, y, hy⟩ := hE
  haveI : IsIntegral E.idealSheaf.subscheme := hint
  have hdim1 : topologicalKrullDim E.idealSheaf.subscheme ≤ 1 := hdimE.le
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hproj
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have hyc : IsClosed ({y} : Set Y) := by
    rw [← hy]
    exact f.isClosedMap _ E.idealSheaf.support.isClosed
  haveI hprop : IsProper (E.idealSheaf.subschemeι ≫ sX) := by
    have := MMP.Mori.isProper_comp_of_range_subset_singleton sY (E.idealSheaf.subschemeι ≫ f)
      hyc (by
        rintro _ ⟨z, rfl⟩
        rw [← hy]
        refine ⟨E.idealSheaf.subschemeι z, ?_, rfl⟩
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨z, rfl⟩)
    rwa [Category.assoc, hfs] at this
  -- the field of constants `κ = Γ(E, 𝒪_E)` and the structure morphism `g : E ⟶ Spec κ`
  set Es := E.idealSheaf.subscheme
  set sE := E.idealSheaf.subschemeι ≫ sX
  letI : Field Γ(Es, ⊤) := (isField_of_universallyClosed k sE).toField
  letI : Algebra k Γ(Es, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ sE.appTop).hom.toAlgebra
  haveI hfin : Module.Finite k Γ(Es, ⊤) := (isField_and_finite_globalSections k sE).2
  haveI : IsProper Es.toSpecΓ := Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ sE
  haveI : IsIso ((Scheme.ΓSpecIso (.of Γ(Es, ⊤))).inv ≫ Es.toSpecΓ.appTop) := by
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  have hgs : Es.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(Es, ⊤))) = sE := by
    change Es.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ sE.appTop) = sE
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have hcompat : ((Scheme.ΓSpecIso (.of k)).inv ≫ sE.appTop).hom =
      ((Scheme.ΓSpecIso (.of Γ(Es, ⊤))).inv ≫ Es.toSpecΓ.appTop).hom.comp
        (algebraMap k Γ(Es, ⊤)) := by
    have hid : (Scheme.ΓSpecIso (.of Γ(Es, ⊤))).inv ≫ Es.toSpecΓ.appTop = 𝟙 Γ(Es, ⊤) := by
      rw [Scheme.toSpecΓ_appTop]
      exact (Scheme.ΓSpecIso Γ(Es, ⊤)).inv_hom_id
    rw [hid, RingHom.algebraMap_toAlgebra]
    ext x
    rfl
  have hdpos : 0 < Module.finrank k Γ(Es, ⊤) := Module.finrank_pos
  -- intersection numbers with `E` are degrees along `E`
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hcartX := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
  have hIN : ∀ D : Divisor X, IsIntersectionNumber sX (Divisor.toQDivisor D) E.idealSheaf
      (Divisor.degreeOn k sX E.idealSheaf.subschemeι hdim1 D (hcartX D)) := fun D =>
    ⟨hprop, hdim1, QDivisor.isQCartier_toQDivisor (hcartX D),
      QDivisor.intersectionNumber_toQDivisor k sX _ hdim1 D (hcartX D) _⟩
  have hdegD : ∀ D : Divisor X,
      Divisor.degreeOn k sX E.idealSheaf.subschemeι hdim1 D (hcartX D) =
        (Module.finrank k Γ(Es, ⊤) : ℤ) *
          (haveI := (hcartX D).isInvertibleModule_divisorialSheaf
          invertibleCurveDegree Γ(Es, ⊤) Es.toSpecΓ hdim1
            ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj D.divisorialSheaf)) := by
    intro D
    haveI := (hcartX D).isInvertibleModule_divisorialSheaf
    exact invertibleCurveDegree_eq_finrank_mul k Γ(Es, ⊤) sE Es.toSpecΓ hcompat hdim1 _
  -- `E² < 0`, by negative definiteness
  have hEE : Divisor.degreeOn k sX E.idealSheaf.subschemeι hdim1 (Finsupp.single E 1)
      (hcartX _) < 0 := by
    have hvan := MMP.Mori.vanishingIdeal_closure_genericPoint_eq_idealSheaf E
    let C : ProperCurve sX := ⟨E.genericPoint, ⟨by
        change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal _).subscheme = 1
        rwa [hvan], by
        change IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫ sX)
        rwa [hvan]⟩⟩
    have hcl : closure ({E.genericPoint} : Set X) = E.support :=
      (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
    have hcon : C.IsContractedBy f := by
      intro x hx
      change x ∈ closure ({E.genericPoint} : Set X) at hx
      rw [hcl] at hx
      have h1 : f x ∈ ({y} : Set Y) := hy ▸ ⟨x, hx, rfl⟩
      have hg : E.genericPoint ∈ E.support := hcl ▸ subset_closure rfl
      have h2 : f E.genericPoint ∈ ({y} : Set Y) := hy ▸ ⟨_, hg, rfl⟩
      exact h1.trans h2.symm
    haveI : IsProper (C.ι ≫ sX) := C.isProper_ι_comp
    open MMP.Threefold.Resolution Stacks.HQuasiProjectiveDimensionOne in
    have hpd := (posDef_neg_intersectionMatrix_of_isContractedProjectiveCurve
      hX hsm hdim hY hYqp hfs hproj hgf (fun _ : Fin 1 => E) (fun a b _ => Subsingleton.elim a b)
      (fun _ => C) (fun _ => rfl) fun _ =>
        ⟨isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one _ C.dim_le,
          hcon⟩).diag_pos (i := 0)
    simp only [Matrix.neg_apply, Matrix.of_apply, neg_pos] at hpd
    have h1 := MMP.Mori.isIntersectionNumber_of_properCurve _
      (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm E) C E rfl
    have h2 := (hIN (Finsupp.single E 1)).unique h1
    have h3 : ((Divisor.toQDivisor (Finsupp.single E 1)).intersectionNumber k sX C.ι C.dim_le
        (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm E) : ℚ) < 0 := by
      exact_mod_cast hpd
    rw [← h2] at h3
    exact_mod_cast h3
  -- `K · E < 0`
  have hKE' : Divisor.degreeOn k sX E.idealSheaf.subschemeι hdim1 K (hcartX K) < 0 := by
    obtain ⟨n, hn, hKn⟩ := hKE
    rw [← (hIN K).unique hKn] at hn
    exact_mod_cast hn
  -- adjunction: `(K + E) · E = -2 χ_k(𝒪_E)`
  have hsupp : DivisorWithCoeffs.suppIdeal (Finsupp.single E 1 : Divisor X) = E.idealSheaf := by
    rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme E.idealSheaf _ rfl]
    unfold DivisorWithCoeffs.suppIdeal
    congr 1
    apply TopologicalSpace.Closeds.ext
    rw [DivisorWithCoeffs.coe_supp, Finsupp.support_single_ne_zero _ one_ne_zero]
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
  have hadj : ∀ J : X.IdealSheafData,
      DivisorWithCoeffs.suppIdeal (Finsupp.single E 1 : Divisor X) = J →
      ∀ [IsProper (J.subschemeι ≫ sX)],
      haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (J.subschemeι ≫ sX)
      IsIntersectionNumber sX (Divisor.toQDivisor (K + Finsupp.single E 1)) J
        (-2 * eulerCharacteristic k (J.subschemeι ≫ sX)
          (SheafOfModules.unit J.subscheme.ringCatSheaf)) := by
    rintro J rfl _
    refine isIntersectionNumber_canonical_add_eq_neg_two_mul_eulerCharacteristic_of_perfectField
      hX hsm hdim hK _ (fun P hP => ?_) inferInstance
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hP
    subst hP
    simp
  have hA := hadj _ hsupp
  have hχ := eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus k sE hdim1
  have hgen := genus_eq_finrank_globalSections_mul_genus_toSpecΓ k sE
    (isField_of_universallyClosed k sE)
  have hsum := MMP.Flips.isIntersectionNumber_add (hIN K) (hIN (Finsupp.single E 1))
  rw [← map_add] at hsum
  have hrel := hsum.unique hA
  rw [hχ, hgen] at hrel
  obtain ⟨b, hb⟩ : ∃ b : ℤ, Divisor.degreeOn k sX E.idealSheaf.subschemeι hdim1 K (hcartX K) =
      (Module.finrank k Γ(Es, ⊤) : ℤ) * b := ⟨_, hdegD K⟩
  haveI := (hcartX (Finsupp.single E 1)).isInvertibleModule_divisorialSheaf
  set a := invertibleCurveDegree Γ(Es, ⊤) Es.toSpecΓ hdim1
    ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
      (Divisor.divisorialSheaf (Finsupp.single E (1 : ℤ) : Divisor X))) with ha
  have hEa : Divisor.degreeOn k sX E.idealSheaf.subschemeι hdim1 (Finsupp.single E 1)
      (hcartX _) = (Module.finrank k Γ(Es, ⊤) : ℤ) * a := hdegD _
  rw [hb, hEa] at hrel
  rw [hEa] at hEE
  rw [hb] at hKE'
  obtain ⟨ha1, hb1, hg0⟩ := eq_neg_one_of_mul_add_mul_eq (by exact_mod_cast hdpos) hEE hKE'
    (by exact_mod_cast hrel)
  -- `𝒪_X(-E)|_E` has degree one over `κ`, so `E ≅ ℙ¹_κ`
  haveI := (hcartX (-Finsupp.single E 1)).isInvertibleModule_divisorialSheaf
  have hdeg1 : invertibleCurveDegree Γ(Es, ⊤) Es.toSpecΓ hdim1
      ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
        (Divisor.divisorialSheaf (-Finsupp.single E (1 : ℤ) : Divisor X))) = 1 := by
    have h1 := hdegD (-Finsupp.single E 1)
    rw [Divisor.degreeOn_neg' k sX _ hdim1 _ (hcartX _), hEa, ha1] at h1
    exact Int.eq_of_mul_eq_mul_left (a := (Module.finrank k Γ(Es, ⊤) : ℤ))
      (by exact_mod_cast hdpos.ne') (by linarith)
  obtain ⟨e', he'⟩ :=
    AlgebraicGeometry.ProjectiveLineCriterion.exists_iso_proj_of_invertibleCurveDegree_eq_one
      Es.toSpecΓ hdim1 hg0 _ hdeg1
  refine ⟨Γ(Es, ⊤), inferInstance, inferInstance, hfin, inferInstance, e'.symm, ?_, ?_, ?_, ?_⟩
  · change e'.inv ≫ sE = _
    rw [← hgs, ← he']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  · -- the normal sheaf `𝒪_X(E)|_E` has degree `-1` over `κ`
    have hcart := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme
      hsm E
    obtain ⟨bb⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' E
      hcart (hcartX _)
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible E.idealSheaf.subscheme.presheaf
        E.idealSheaf.subscheme.ringCatSheaf.2
        ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
          (Stacks.Divisors.invertibleSheaf' E.idealSheaf : X.Modules)) :=
      Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      E.idealSheaf.subschemeι.toLRSHom.toShHom _
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
        (Stacks.Divisors.isTensorInvertible_invertibleSheaf E.idealSheaf))
    refine isExceptionalCurveOfFirstKind_of_invertibleCurveDegree_eq_neg_one _ _ hcart
      Es.toSpecΓ hdim1 e'.symm (by simp [← he']) ?_
    rw [← ha1, ha]
    exact invertibleCurveDegree_eq_of_iso _ _ _
      ((Scheme.Modules.pullback E.idealSheaf.subschemeι).mapIso bb.symm)
  · have h := hIN (Finsupp.single E 1)
    rwa [hEa, ha1, mul_neg_one, Int.cast_neg, Int.cast_natCast] at h
  · have h := hIN K
    rwa [hb, hb1, mul_neg_one, Int.cast_neg, Int.cast_natCast] at h

end

end MMP.Threefold

/-! ### Contracting a `K`-negative exceptional curve over a perfect field -/

namespace MMP.Resolution

open AlgebraicGeometry MMP.Mori

section Helpers

open TopologicalSpace

/-- The stalks of the target of `c` at the points of an open `U` over which `c` is an
isomorphism are regular if the stalks of the source are. -/
private theorem isRegularLocalRing_stalk_of_isIso_morphismRestrict {X X' : Scheme.{u}}
    (c : X ⟶ X') (U : X'.Opens) [IsIso (c ∣_ U)]
    (hX : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y)) (x : X') (hx : x ∈ U) :
    IsRegularLocalRing (X'.presheaf.stalk x) := by
  let e : (c ⁻¹ᵁ U).toScheme ≅ U.toScheme := asIso (c ∣_ U)
  let x' : U := ⟨x, hx⟩
  let w : (c ⁻¹ᵁ U).toScheme := e.inv x'
  have h1 : IsRegularLocalRing ((c ⁻¹ᵁ U).toScheme.presheaf.stalk w) := by
    have := hX w.1
    exact IsRegularLocalRing.of_ringEquiv ((c ⁻¹ᵁ U).stalkIso w).commRingCatIsoToRingEquiv.symm
  have h2 : IsRegularLocalRing (U.toScheme.presheaf.stalk x') := by
    have : IsIso (e.inv.stalkMap x') := IsOpenImmersion.instIsIsoCommRingCatStalkMap e.inv x'
    exact IsRegularLocalRing.of_ringEquiv (asIso (e.inv.stalkMap x')).commRingCatIsoToRingEquiv
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso x').commRingCatIsoToRingEquiv

/-- The complement of a point whose local ring has dimension two is dense. -/
private theorem dense_compl_singleton_of_ringKrullDim_stalk_eq_two {Z : Scheme.{u}} (z : Z)
    (hdim : ringKrullDim (Z.presheaf.stalk z) = 2) : Dense ({z}ᶜ : Set Z) := by
  have hdim' : Order.coheight z = 2 := by
    have h1 : (Order.coheight z : WithBot ℕ∞) = 2 := by
      rw [← ringKrullDim_stalk_eq_coheight, hdim]
    exact WithBot.coe_injective (h1.trans rfl)
  have hnm : ¬ IsMax z := by
    intro h
    have := Order.coheight_eq_zero.2 h
    rw [hdim'] at this
    simp at this
  obtain ⟨y, hzy, hyz⟩ := not_isMax_iff.1 hnm
  have hspec : y ⤳ z := hzy
  exact dense_compl_singleton_iff_not_open.2 fun ho =>
    hyz (by rw [Set.mem_singleton_iff.1 (hspec.mem_open ho rfl)])

/-- A universally closed morphism which is an isomorphism over a dense open is surjective. -/
private theorem surjective_of_isIso_morphismRestrict {X X' : Scheme.{u}} (c : X ⟶ X')
    [UniversallyClosed c] (W : X'.Opens) (hW : Dense (W : Set X')) [IsIso (c ∣_ W)] :
    Surjective c := by
  have hW' : (W : Set X') ⊆ Set.range c.base := by
    intro y hyW
    obtain ⟨x, hx⟩ := (asIso (c ∣_ W)).hom.homeomorph.surjective ⟨y, hyW⟩
    refine ⟨(c ⁻¹ᵁ W).ι x, ?_⟩
    have : ((c ∣_ W) ≫ W.ι) x = y := congrArg (fun t : W => (t : X')) hx
    rwa [morphismRestrict_ι] at this
  have hclosed : IsClosed (Set.range c.base) := c.isClosedMap.isClosed_range
  refine ⟨fun y => ?_⟩
  have : closure (W : Set X') ⊆ Set.range c.base := closure_minimal hW' hclosed
  rw [hW.closure_eq] at this
  exact this (Set.mem_univ y)

/-- A morphism from an irreducible scheme which is an isomorphism over a dense open with nonempty
preimage is a birational morphism. -/
private theorem isBirationalMorphism_of_isIso_morphismRestrict {X X' : Scheme.{u}}
    [IrreducibleSpace X] (c : X ⟶ X') (U : X'.Opens) (hU : Dense (U : Set X'))
    (hne : ((c ⁻¹ᵁ U : X.Opens) : Set X).Nonempty) [IsIso (c ∣_ U)] :
    IsBirationalMorphism c := by
  have hdY : Dense ((c ⁻¹ᵁ U : X.Opens) : Set X) := (c ⁻¹ᵁ U).isOpen.dense hne
  refine ⟨⟨c ⁻¹ᵁ U, hdY, U, hU, asIso (c ∣_ U)⟩, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨c ⁻¹ᵁ U, hdY, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, asIso_hom, Scheme.topIso_hom]
  rw [morphismRestrict_ι]
  erw [Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι_assoc]

/-- If `b ≫ g` and `b` are birational (Stacks, Tag 01RO) morphisms of integral schemes, then so
is `g`. -/
private theorem isBirational_of_isBirational_comp {X X' Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral X'] [IsIntegral Y] (b : X ⟶ X') (g : X' ⟶ Y) (hb : IsBirational b)
    (hbg : IsBirational (b ≫ g)) : IsBirational g := by
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hbg1, hbg2⟩ := hbg
  rw [genericPoints_eq_singleton, genericPoints_eq_singleton] at hb1
  rw [genericPoints_eq_singleton, genericPoints_eq_singleton] at hbg1
  have hη : b (genericPoint X) = genericPoint X' := hb1.mapsTo rfl
  have hηY : g (b (genericPoint X)) = genericPoint Y := hbg1.mapsTo rfl
  refine ⟨?_, fun x hx => ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    refine Set.bijOn_singleton.mpr ?_
    rwa [← hη]
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    have h1 := hbg2 (genericPoint X) (by rw [genericPoints_eq_singleton]; rfl)
    have h2 := hb2 (genericPoint X) (by rw [genericPoints_eq_singleton]; rfl)
    rw [Scheme.Hom.stalkMap_comp] at h1
    have := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h2 h1
    rw [← hη]
    exact this

/-- A birational (Stacks, Tag 01RO) morphism of integral schemes, locally of finite type, is a
birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

section Curves

variable {k : Type u} [Field k] {S : Scheme.{u}}

/-- The closure of the generic point of a proper curve has dimension one. -/
private theorem topologicalKrullDim_closure_singleton_point_eq_one {sS : S ⟶ Spec (.of k)}
    (C : ProperCurve sS) :
    topologicalKrullDim (closure ({C.point} : Set S)) = 1 := by
  rw [← C.dim_eq]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    (C.ι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (range_curveSubschemeAtι C.point))).isHomeomorph).symm

/-- The generic point of a proper curve is not closed. -/
private theorem not_isClosed_singleton_point {sS : S ⟶ Spec (.of k)} (C : ProperCurve sS) :
    ¬ IsClosed ({C.point} : Set S) := fun hcl => by
  have h : topologicalKrullDim ({C.point} : Set S) ≤ 0 :=
    @topologicalKrullDim_zero_of_discreteTopology _ _
      (@Subsingleton.discreteTopology _ _ (Set.subsingleton_singleton (a := C.point)).coe_sort)
  rw [← hcl.closure_eq, topologicalKrullDim_closure_singleton_point_eq_one] at h
  exact absurd h (by decide)

/-- The generic point of a proper curve on an integral surface of dimension two is not the
generic point of the surface. -/
private theorem point_ne_genericPoint {sS : S ⟶ Spec (.of k)} [IsIntegral S]
    (hS : topologicalKrullDim S = 2) (C : ProperCurve sS) : C.point ≠ genericPoint S := by
  intro h
  have h1 := topologicalKrullDim_closure_singleton_point_eq_one C
  rw [h, (genericPoint_spec S).def, (Homeomorph.Set.univ S).isHomeomorph.topologicalKrullDim_eq,
    hS] at h1
  exact absurd h1 (by decide)

/-- On an integral surface, a point which is neither closed nor the generic point has coheight
one. -/
private theorem coheight_eq_one_of_ne_genericPoint_of_not_isClosed [IsIntegral S]
    (hS : topologicalKrullDim S = 2) {a : S} (hgen : a ≠ genericPoint S)
    (hna : ¬ IsClosed ({a} : Set S)) : Order.coheight a = 1 := by
  let : PartialOrder S := specializationOrder S
  have hlt : a < genericPoint S :=
    lt_of_le_of_ne ((genericPoint_spec S).specializes (Set.mem_univ a)) hgen
  obtain ⟨z, hza, hzne⟩ : ∃ z ∈ closure ({a} : Set S), z ≠ a := by
    by_contra! hcon
    exact hna (closure_subset_iff_isClosed.mp fun z hz => hcon z hz)
  have hzlt : z < a := lt_of_le_of_ne (specializes_iff_mem_closure.mpr hza) hzne
  have h1 : ((Order.height a + Order.coheight a : ℕ∞) : WithBot ℕ∞) ≤ 2 := by
    rw [← hS, ← Stacks.AlgebraicGeometry.AmpleDimensionOne.krullDim_eq_topologicalKrullDim,
      Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun b : S => Order.height b + Order.coheight b) a)
  have h2 : 1 ≤ Order.height a := le_trans (by simp) (Order.height_add_one_le hzlt)
  refine le_antisymm ?_ (le_trans (by simp) (Order.coheight_add_one_le hlt))
  exact (ENat.add_le_add_iff_left ENat.one_ne_top).mp
    ((add_le_add_left h2 _).trans (WithBot.coe_le_coe.mp h1) : 1 + Order.coheight a ≤ 1 + 1)

/-- If `𝒪_X(D)` is the divisorial sheaf of a Cartier Weil divisor `D'`, then the intersection
number of `D` with a projective curve is the degree of `D'` along it. -/
private theorem cartierCurveIntersection_eq_degreeOn {sS : S ⟶ Spec (.of k)} [IsNormal S]
    [IsLocallyNoetherian S] [QuasiCompact sS]
    {D : S.CartierDivisor} {D' : Divisor S} (hD' : D'.IsCartier)
    (e : MMP.CartierDivisor.sheaf D ≅ D'.divisorialSheaf) (C : ProperCurve sS)
    (hC : IsProjectiveMorphism (C.ι ≫ sS)) :
    cartierCurveIntersection D C = D'.degreeOn k sS C.ι C.dim_le hD' := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sS
  haveI hinv := hD'.isInvertibleModule_divisorialSheaf
  haveI : Stacks.Ample.IsInvertibleModule S (MMP.CartierDivisor.sheaf D) :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso e.symm hinv
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      (MMP.CartierDivisor.sheaf D) := this
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf := hinv
  have hcurve : AlgebraicGeometry.IsCurve k (C.ι ≫ sS) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := C.dim_eq }
  have : AlgebraicGeometry.IsProjectiveVariety k (C.ι ≫ sS) :=
    { toIsVariety := hcurve.toIsVariety
      isProjective := hC }
  have : Stacks.Ample.IsInvertibleModule C.scheme
      ((Scheme.Modules.pullback C.ι).obj (MMP.CartierDivisor.sheaf D)) :=
    MMP.Mori.isInvertible_pullback_obj C.ι _
  unfold cartierCurveIntersection lineBundleCurveIntersection
  rw [MMP.Resolution.degree_eq_invertibleCurveDegree (C.ι ≫ sS) _ C.dim_le,
    ← MMP.Mori.degreeOn_eq_invertibleCurveDegree, MMP.Mori.degreeOn_eq_of_iso k sS C.ι C.dim_le e]
  rfl

end Curves

/-- On a resolution `f : X ⟶ Y` of a quasi-projective surface over a perfect field, an
`f`-exceptional curve `E` with `(K_X · E) < 0` is cut out by an ideal sheaf which is an
exceptional curve of the first kind over some field `κ`. -/
private theorem exists_isExceptionalCurveOfFirstKind_of_cartierCurveIntersection_neg
    {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : Stacks.HProjective.IsQuasiProjective sY)
    [IsIntegral X] [IsNoetherian X] (f : X ⟶ Y) [LocallyOfFiniteType (f ≫ sY)]
    (hf : IsProjectiveSurfaceResolution sY f) (E : ProperCurve (f ≫ sY))
    (hE : IsContractedProjectiveCurve (f ≫ sY) f E) (K : X.CartierDivisor)
    (hK : ∃ ω : RationalPluriForms (f ≫ sY) 2 1, ω ≠ 0 ∧
      ∀ P : AlgebraicGeometry.PrimeDivisor X,
        (cartierWeilDivisor K).1 P = (divisorOfFormOnSmoothLocus ω) P)
    (hKE : cartierCurveIntersection K E < 0) :
    ∃ (D : X.IdealSheafData) (κ : Type u) (_ : Field κ) (e : projectiveLineProj κ ≅ D.subscheme),
      D.IsExceptionalCurveOfFirstKind κ e ∧ (D.support : Set X) = closure {E.point} := by
  obtain ⟨ω, hω0, hωK⟩ := hK
  -- `X` and `Y` are varieties, `X` is smooth, normal and locally Noetherian
  haveI hYv : AlgebraicGeometry.IsVariety k sY := hf.isVariety
  haveI : IsNoetherian Y := isNoetherian_of_finiteType sY
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  haveI hXv : AlgebraicGeometry.IsVariety k (f ≫ sY) := {}
  obtain ⟨hXln, hXn⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hf.isSmoothScheme
  haveI : IsSmoothVariety k (f ≫ sY) :=
    { toIsVariety := hXv,
      toSmooth := (@isSmoothScheme_iff _ _ _
        (LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance)).mp
          hf.isSmoothScheme }
  -- `Y` is H-quasi-projective
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of k))
  have hYhqp : Stacks.HProjective.IsHQuasiProjective sY :=
    Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAmple sY
      (Stacks.Ample.unitModule (Spec (.of k))) (Stacks.Ample.isAmple_unitModule_of_isAffine _) hY
  -- the divisor `B = div(ω)` is a canonical divisor, and is the Weil divisor of `K`
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sY)
    hf.isSmoothScheme hf.dim_source_eq
  set B : Divisor X := divisorOfForm ω
  have hB : B.IsCanonicalDivisor (f ≫ sY) 2 := by
    have hlin := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul (sX := f ≫ sY)
      ⟨hXv, inferInstance⟩ hK₀ hω0
    rw [one_smul] at hlin
    exact hK₀.of_linearlyEquivalent hlin
  have hBK : weilDivisorEquivFinsupp (cartierWeilDivisor K) = B := by
    ext P
    refine (hωK P).trans ?_
    simp only [divisorOfFormOnSmoothLocus, Finsupp.filter_apply]
    split_ifs with hP
    · rfl
    · refine absurd ⟨AlgebraicGeometry.PrimeDivisor.genericPoint P, ?_, ?_⟩ hP
      · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      · rw [show smoothLocus (f ≫ sY) = ⊤ from hf.isSmoothScheme]; trivial
  obtain ⟨hcart, -, -, hdict, -, hQ⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k (f ≫ sY)
  have eB : MMP.CartierDivisor.sheaf K ≅ B.divisorialSheaf := by
    have e := (hdict K).some
    rw [hBK] at e
    exact e.symm
  -- the prime divisor `P` with generic point that of `E`
  set P : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne E.point
    (coheight_eq_one_of_ne_genericPoint_of_not_isClosed hf.dim_source_eq
      (point_ne_genericPoint hf.dim_source_eq E)
      (not_isClosed_singleton_point E))
  have hPpt : AlgebraicGeometry.PrimeDivisor.genericPoint P = E.point :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hPsupp : (P.support : Set X) = closure {E.point} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hPpt]
  have hPexc : MMP.Mori.IsExceptionalCurve f P.idealSheaf := by
    have hPideal : Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({E.point} : Set X)) =
        P.idealSheaf := by
      rw [← hPpt]; exact MMP.Mori.vanishingIdeal_closure_genericPoint_eq_idealSheaf P
    refine ⟨⟨P.integral, by rw [← hPideal]; exact E.dim_eq⟩, f E.point,
      Set.eq_singleton_iff_unique_mem.2 ⟨⟨E.point, ?_, rfl⟩, ?_⟩⟩
    · change E.point ∈ (P.support : Set X)
      rw [hPsupp]; exact subset_closure rfl
    · rintro _ ⟨x, hx, rfl⟩
      exact hE.2 x (by rw [← hPsupp]; exact hx)
  have hPint : ∃ n : ℚ, n < 0 ∧
      IsIntersectionNumber (f ≫ sY) (Divisor.toQDivisor B) P.idealSheaf n := by
    refine ⟨_, ?_, MMP.Mori.isIntersectionNumber_of_properCurve (Divisor.toQDivisor B) (hQ _) E P
      hPpt.symm⟩
    rw [QDivisor.intersectionNumber_toQDivisor k (f ≫ sY) E.ι E.dim_le B (hcart B),
      ← cartierCurveIntersection_eq_degreeOn (hcart B) eB E hE.1]
    exact_mod_cast hKE
  obtain ⟨κ, _, _, -, -, e, -, hfirst, -, -⟩ :=
    MMP.Threefold.exists_isExceptionalCurveOfFirstKind_of_canonical_intersection_neg hXv
      hf.isSmoothScheme hf.dim_source_eq hYv hYhqp rfl hf.isProjectiveMorphism
      (MMP.Threefold.Resolution.exists_isFinite_morphismRestrict_of_isBirationalMorphism
        hf.isBirationalMorphism) hB P hPexc hPint
  exact ⟨P.idealSheaf, κ, _, e, hfirst, hPsupp⟩

/-- The target of a contraction of a resolution is a resolution. If `f = b ≫ g` with `f` a
resolution of a quasi-projective surface over a perfect field, `b` the contraction of an
exceptional curve of the first kind and `g` projective, then `g` is a resolution. -/
private theorem isProjectiveSurfaceResolution_of_isContractionOfExceptionalCurve {k : Type u}
    [Field k] [PerfectField k] {X X₁ Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (hY : Stacks.HProjective.IsQuasiProjective sY) [IsIntegral X] (f : X ⟶ Y)
    (hf : IsProjectiveSurfaceResolution sY f) {D : X.IdealSheafData} {b : X ⟶ X₁} {g : X₁ ⟶ Y}
    (hc : IsContractionOfExceptionalCurve D b) (hbg : b ≫ g = f) (hg : IsProjective g) :
    IsProjectiveSurfaceResolution sY g := by
  haveI : AlgebraicGeometry.IsVariety k sY := hf.isVariety
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  obtain ⟨z, hz, hreg, hdimz, -, φ, hφ⟩ := hc.exists_blowUp_iso
  let U : X₁.Opens := ⟨{z}ᶜ, hz.isOpen_compl⟩
  haveI : IsIso (b ∣_ U) := isIso_morphismRestrict_compl_of_blowUp_iso _ z hz
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _) φ hφ
  have hdense : Dense (U : Set X₁) := dense_compl_singleton_of_ringKrullDim_stalk_eq_two z hdimz
  haveI : IsProper b := hc.isProper
  -- `X₁` is regular
  have hreg₁ : ∀ x : X₁, IsRegularLocalRing (X₁.presheaf.stalk x) := by
    intro x
    by_cases hx : x = z
    · subst hx; exact hreg
    · exact isRegularLocalRing_stalk_of_isIso_morphismRestrict b U ((isRegular_iff_regular_stalks
        X).1 (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hf.isSmoothScheme)).2 x hx
  -- `X₁` is integral: reduced, and the image of the irreducible `X`
  haveI : Nonempty X₁ := ⟨z⟩
  haveI : IrreducibleSpace X₁ := by
    have h := (IrreducibleSpace.isIrreducible_univ X).image b.base b.continuous.continuousOn
    rw [Set.image_univ, (surjective_of_isIso_morphismRestrict b U hdense).surj.range_eq] at h
    exact (irreducibleSpace_def X₁).2 h
  haveI : ∀ x : X₁, IsReduced (X₁.presheaf.stalk x) := fun x =>
    haveI := hreg₁ x
    haveI : IsDomain (X₁.presheaf.stalk x) := IsRegularLocalRing.isDomain _
    isReduced_of_noZeroDivisors
  haveI : IsReduced X₁ := isReduced_of_isReduced_stalk X₁
  haveI : IsIntegral X₁ := isIntegral_of_irreducibleSpace_of_isReduced X₁
  haveI : IsIntegral Y := hf.isVariety.toIsIntegral
  -- `g` is projective
  obtain ⟨-, L, hLinv, hLamp⟩ := hY
  haveI := hLinv
  have hgp : IsProjectiveMorphism g := isProjectiveMorphism_of_isProjective g L
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sY L hLamp) hg
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hgp
  -- `g` is birational, since `b` and `b ≫ g = f` are
  have hne : ((b ⁻¹ᵁ U : X.Opens) : Set X).Nonempty := by
    obtain ⟨y, hy⟩ := hdense.nonempty
    obtain ⟨x, -⟩ := (asIso (b ∣_ U)).hom.homeomorph.surjective ⟨y, hy⟩
    exact ⟨x.1, x.2⟩
  have hgB : IsBirational g := isBirational_of_isBirational_comp b g
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
      (isBirationalMorphism_of_isIso_morphismRestrict b U hdense hne))
    (hbg ▸ MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf.isBirationalMorphism)
  refine ⟨hf.isVariety, hf.dim_eq, hgp, isBirationalMorphism_of_isBirational g hgB, ?_, ?_⟩
  · -- `X₁` is regular, hence smooth over the perfect field `k`
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨V, hxV, hV⟩ := (InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp _ x).1
      ((smoothAt_locus_eq_regular_locus k (g ≫ sY)).symm.subset (hreg₁ x))
    exact MMP.Mori.le_smoothLocus (g ≫ sY) hV hxV
  · -- `X₁` has dimension two, the dimension of the isomorphic opens `X ∖ E` and `X₁ ∖ {z}`
    haveI : AlgebraicGeometry.IsVariety k (f ≫ sY) := {}
    have h : topologicalKrullDim ((b ⁻¹ᵁ U : X.Opens) : Set X) =
        topologicalKrullDim (U : Set X₁) :=
      IsHomeomorph.topologicalKrullDim_eq _ (asIso (b ∣_ U)).hom.homeomorph.isHomeomorph
    rw [topologicalKrullDim_eq_of_isOpen k X₁ (g ≫ sY) _ U.isOpen hdense.nonempty, ← h,
      ← topologicalKrullDim_eq_of_isOpen k X (f ≫ sY) _ (b ⁻¹ᵁ U).isOpen hne, hf.dim_source_eq]

end Helpers

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Contracting a `K`-negative exceptional curve over a perfect field.** Let `k` be a perfect
field, `Y` a quasi-projective surface over `k`, `f : X ⟶ Y` a resolution of `Y`, `E ⊆ X` an
`f`-exceptional curve and `K` a canonical divisor of `X` (a Cartier divisor with Weil divisor
`div_X(ω)` for a nonzero rational `2`-form `ω`) with `(K · E) < 0`. Then `f = h ≫ f₁` for a
resolution `f₁ : X₁ ⟶ Y` and a morphism `h : X ⟶ X₁` which is the blow-up of a closed point
`x₁ ∈ X₁` with regular local ring, whose fibre over `x₁` is `E`, and which is an isomorphism over
`X₁ ∖ {x₁}`. -/
@[mmp "lem_mmp_threefold_contract_k_negative_perfect"]
public theorem exists_isProjectiveSurfaceResolution_of_cartierCurveIntersection_neg
    {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (hY : Stacks.HProjective.IsQuasiProjective sY) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Y) [LocallyOfFiniteType (f ≫ sY)] (hf : IsProjectiveSurfaceResolution sY f)
    (E : ProperCurve (f ≫ sY)) (hE : IsContractedProjectiveCurve (f ≫ sY) f E)
    (K : X.CartierDivisor)
    (hK : ∃ ω : RationalPluriForms (f ≫ sY) 2 1, ω ≠ 0 ∧
      ∀ P : AlgebraicGeometry.PrimeDivisor X,
        (cartierWeilDivisor K).1 P = (divisorOfFormOnSmoothLocus ω) P)
    (hKE : cartierCurveIntersection K E < 0) :
    ∃ (X₁ : Scheme.{u}) (h : X ⟶ X₁) (f₁ : X₁ ⟶ Y), h ≫ f₁ = f ∧
      IsProjectiveSurfaceResolution sY f₁ ∧
      ∃ (x₁ : X₁) (hx₁ : IsClosed ({x₁} : Set X₁)),
        IsRegularLocalRing (X₁.presheaf.stalk x₁) ∧
        (∃ φ : X ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x₁}, hx₁⟩),
          h = φ.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x₁}, hx₁⟩)) ∧
        h.base ⁻¹' {x₁} = closure {E.point} ∧
        IsIso (h ∣_ ⟨{x₁}ᶜ, hx₁.isOpen_compl⟩) := by
  haveI : AlgebraicGeometry.IsVariety k sY := hf.isVariety
  haveI : IsNoetherian Y := isNoetherian_of_finiteType sY
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  obtain ⟨D, κ, _, e, hfirst, hDsupp⟩ :=
    exists_isExceptionalCurveOfFirstKind_of_cartierCurveIntersection_neg sY hY f hf E hE K hK hKE
  -- Castelnuovo's contraction
  obtain ⟨X₁, b, g, hc, hbg, hg⟩ := exists_isContractionOfExceptionalCurve_isProjective f hfirst
    (f E.point) (fun x hx => hE.2 x (hDsupp ▸ hx)) hf.isProjectiveMorphism.isProjective
  obtain ⟨z, hz, hreg, -, hD, φ, hφ⟩ := hc.exists_blowUp_iso
  have hI : ((Scheme.IdealSheafData.vanishingIdeal
      (⟨{z}, hz⟩ : TopologicalSpace.Closeds X₁)).support : Set X₁) = {z} :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  refine ⟨X₁, b, g, hbg,
    isProjectiveSurfaceResolution_of_isContractionOfExceptionalCurve sY hY f hf hc hbg hg,
    z, hz, hreg, ⟨φ, hφ.symm⟩, ?_, isIso_morphismRestrict_compl_of_blowUp_iso _ z hz hI φ hφ⟩
  rw [← hDsupp, hD, Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hI]

end

end MMP.Resolution

end
