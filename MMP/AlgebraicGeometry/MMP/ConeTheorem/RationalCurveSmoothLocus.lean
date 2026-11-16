module

public import MMP.RingTheory.DualizingComplex.FlatLocalExtension
public import MMP.AlgebraicGeometry.Positivity.AmpleTwistRealPerturbation
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RationalCurveCharP
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle

/-!
# A bounded rational curve from a curve in the smooth locus of a normal complex variety

Let `V` be a normal projective complex variety, let `U ⊆ V` be an open subscheme which is smooth
of pure relative dimension `n` over `ℂ` (for instance the smooth locus `V_sm` when `dim V = n`),
with canonical sheaf `ω_U = Ωⁿ_{U/ℂ}`, and let `C ⊆ U` be a smooth projective curve of genus
`g ≥ 1`. Suppose `κ = -deg(ω_U|_C) > 0`. Then for every ample `ℚ`-Cartier `ℚ`-divisor `H` on `V`
there is a rational curve `L ⊆ V` with

`0 < H · L ≤ 2n (H · C) / κ`.

No `ℚ`-Cartier condition on `K_V` is needed: only the canonical sheaf of the smooth open `U`
enters.

The statement is homogeneous in `H`: writing `mH = D` with `D` an ample Cartier divisor, both
sides are `1/m` times the corresponding degrees of the ample invertible sheaf `𝒪_V(D)`. The
proof therefore reduces to the bound for `𝒪(1)` of an embedding `V ⊆ ℙᴺ_ℂ` by a power of `D`,
which is obtained from the positive-characteristic bound by reduction modulo `p`.

`V`, `U` and `C` spread out over a finitely generated subring `R ⊆ ℂ`, over which `U` and `C`
become smooth of relative dimension `n` and `1`. Over a nonempty open subset of `Spec R` the
closed fibres of `C` are smooth projective curves of genus at least `g` (semicontinuity of
cohomology) on which `ω_U` and `𝒪(1)` have the degrees they have on `C` (constancy of Euler
characteristics in a flat proper family), and the equations of `V` vanish on the fibres of `V`.
The positive-characteristic bound then gives, on the geometric fibre over every closed point of
that open, a rational curve of `𝒪(1)`-degree at most `e = ⌊2n (𝒪(1) · C) / κ⌋`.

A rational curve of degree at most `e` on `V ⊆ ℙᴺ` amounts to `N + 1` binary forms of degree at
most `e`, not all proportional, solving the equations of `V`. The existence of such forms is a
constructible condition on `Spec R` (Chevalley), so forms over a dense set of closed points give
forms over the generic point, hence over `ℂ`, hence a rational curve of degree at most `e` on `V`.

## Main definitions

* `MMP.Fourfold.SmoothLocusSlopeBound.HasBinarySolution`: a nonconstant solution of homogeneous
  equations in binary forms of degree at most `e`.
* `MMP.Fourfold.SmoothLocusSlopeBound.projBasicOpen`: the open `D₊(F) ⊆ ℙᴺ_A`.

## Main results

* `MMP.Fourfold.exists_isRationalCurve_intersectionNumber_le`: the bounded rational curve.
* `MMP.Mori.isRationalCurve_bot_projectiveLine`: `ℙ¹_K` is a rational curve in itself.
* `MMP.Fourfold.SmoothLocusSlopeBound.hasBinarySolution_of_isRationalCurve` and
  `MMP.Fourfold.SmoothLocusSlopeBound.exists_isRationalCurve_of_hasBinarySolution`: on a closed
  subscheme `Z ⊆ ℙᴺ_K`, `K` algebraically closed, rational curves of degree at most `e` and binary
  solutions of degree at most `e` of the equations of `Z` determine each other.
* `MMP.Fourfold.SmoothLocusSlopeBound.mem_closedSubschemeIdeal_of_preimage_eq_bot` and
  `MMP.Fourfold.SmoothLocusSlopeBound.preimage_eq_bot_of_mem_closedSubschemeIdeal`: a form lies in
  the ideal of a reduced closed subscheme exactly when `D₊(F)` misses it.

## Implementation notes

The smooth locus `V_sm` of pure dimension `n` is generalized to any open `U ⊆ V` with
`U ⟶ Spec ℂ` smooth of relative dimension `n`; every such `U` lies in `V_sm`, and
`U = MMP.Mori.smoothLocus sV` is the case of the source (it is smooth of relative dimension
`dim V`). The sheaf `ω_U` is `AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms` in degree
`n`, invertible by `Stacks.Discriminant.isInvertible_relativeDifferentialForms`, and its degree
on `C` is `MMP.Mori.degreeOn`. Intersection numbers of the `ℚ`-Cartier divisor `H` with curves
are `MMP.Mori.QDivisor.intersectionNumber`, and ampleness is `MMP.Mori.QDivisor.IsAmple`. The
curve `C` is a closed immersion `i : C ⟶ U`; being proper over `ℂ`, it is also closed in `V`.
A curve (`AlgebraicGeometry.IsCurve`) is integral, so in particular connected.

The relative dimension is spread out through the closed set of points near which `U_R ⟶ Spec R`
is not smooth of relative dimension `n`: its image misses the generic point of `Spec R`, so it
lies in a proper closed subset, which is removed by inverting one element of `R`. The vanishing of
the equations of `V` on a closed fibre is checked set-theoretically, on the reduced rational
curve, through the opens `D₊(F) ⊆ ℙᴺ`, which are compatible with base change.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 1.13
-/

open CategoryTheory AlgebraicGeometry MMP

namespace MMP.Fourfold.SmoothLocusSlopeBound

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Rational curves of bounded degree and binary forms -/

open Polynomial in
/-- A tuple of `N + 1` binary forms of degree at most `e` over `K`, written dehomogenised as
polynomials of degree at most `e`, which are not all proportional and on which every `G l`
vanishes. -/
@[expose] public def HasBinarySolution (K : Type*) [Field K] {ι : Type*} {N : ℕ}
    (G : ι → MvPolynomial (Fin (N + 1)) K) (e : ℕ) : Prop :=
  ∃ f : Fin (N + 1) → K[X], (∀ k, (f k).natDegree ≤ e) ∧
    (∀ l, MvPolynomial.aeval f (G l) = 0) ∧
    ∃ k k' a b, (f k).coeff a * (f k').coeff b ≠ (f k).coeff b * (f k').coeff a

section Generisation

open Polynomial Topology

/-- A constructible set meeting every nonempty open contains a point lying in every nonempty
open. -/
private theorem mem_of_isConstructible {X : Type*} [TopologicalSpace X] (η : X)
    (hη : ∀ U : Set X, IsOpen U → U.Nonempty → η ∈ U) {T : Set X} (hT : IsConstructible T)
    (hd : ∀ U : Set X, IsOpen U → U.Nonempty → (U ∩ T).Nonempty) : η ∈ T := by
  have key : ∀ s : Set X, IsConstructible s →
      (η ∈ s → ∃ U, IsOpen U ∧ U.Nonempty ∧ U ⊆ s) ∧
        (η ∉ s → ∃ U, IsOpen U ∧ U.Nonempty ∧ U ∩ s = ∅) := by
    intro s hs
    induction hs using IsConstructible.empty_union_induction with
    | open_retrocompact U hU _ =>
      refine ⟨fun h => ⟨U, hU, ⟨η, h⟩, le_rfl⟩, fun h => ⟨Set.univ, isOpen_univ, ⟨η, trivial⟩, ?_⟩⟩
      rw [Set.univ_inter]
      by_contra hne
      exact h (hη U hU (Set.nonempty_iff_ne_empty.2 hne))
    | union s _ t _ hs ht =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases h with h | h
        · obtain ⟨U, hU, hne, hsub⟩ := hs.1 h
          exact ⟨U, hU, hne, hsub.trans Set.subset_union_left⟩
        · obtain ⟨U, hU, hne, hsub⟩ := ht.1 h
          exact ⟨U, hU, hne, hsub.trans Set.subset_union_right⟩
      · obtain ⟨U₁, hU₁, hne₁, h₁⟩ := hs.2 fun h' => h (Or.inl h')
        obtain ⟨U₂, hU₂, hne₂, h₂⟩ := ht.2 fun h' => h (Or.inr h')
        refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨η, hη _ hU₁ hne₁, hη _ hU₂ hne₂⟩, ?_⟩
        rw [Set.inter_union_distrib_left]
        exact Set.union_empty_iff.2
          ⟨Set.subset_empty_iff.1 (h₁ ▸ Set.inter_subset_inter_left _ Set.inter_subset_left),
            Set.subset_empty_iff.1 (h₂ ▸ Set.inter_subset_inter_left _ Set.inter_subset_right)⟩
    | compl s _ hs =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨U, hU, hne, hdis⟩ := hs.2 h
        exact ⟨U, hU, hne, fun x hx hxs => (Set.eq_empty_iff_forall_notMem.1 hdis x) ⟨hx, hxs⟩⟩
      · obtain ⟨U, hU, hne, hsub⟩ := hs.1 (not_not.1 h)
        exact ⟨U, hU, hne, Set.eq_empty_iff_forall_notMem.2 fun x hx => hx.2 (hsub hx.1)⟩
  by_contra h
  obtain ⟨U, hU, hne, hdis⟩ := (key T hT).2 h
  obtain ⟨x, hx⟩ := hd U hU hne
  exact (Set.eq_empty_iff_forall_notMem.1 hdis x) hx

/-- **A point over the generic point of a domain has a geometric point in any algebraically closed
field containing the domain.** -/
private theorem exists_ringHom_of_domain {R D K : Type} [CommRing R] [IsDomain R] [CommRing D]
    [IsDomain D] [Algebra R D] [Algebra.FiniteType R D] [Field K] [IsAlgClosed K]
    (φ : R →+* K) (hφ : Function.Injective φ)
    (hD : Function.Injective (algebraMap R D)) :
    ∃ χ : D →+* K, χ.comp (algebraMap R D) = φ := by
  classical
  let F := FractionRing R
  let M := Algebra.algebraMapSubmonoid D (nonZeroDivisors R)
  let DF := Localization M
  have hM : M ≤ nonZeroDivisors D := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero hr
      (hD (h.trans (map_zero _).symm))
  have : IsDomain DF := IsLocalization.isDomain_of_le_nonZeroDivisors DF hM
  let : Algebra F DF := localizationAlgebra (nonZeroDivisors R) D
  have : IsLocalization (Submonoid.map (algebraMap R D) (nonZeroDivisors R)) DF :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid D (nonZeroDivisors R)) DF)
  have : Algebra.FiniteType F DF := by
    have := RingHom.finiteType_localizationPreserves (algebraMap R D) (nonZeroDivisors R) F DF
      (RingHom.finiteType_algebraMap.mpr inferInstance)
    exact RingHom.finiteType_algebraMap.mp this
  obtain ⟨m, hm⟩ := Ideal.exists_maximal DF
  let L := DF ⧸ m
  let : Field L := Ideal.Quotient.field m
  have : Module.Finite F L := finite_of_finite_type_of_isJacobsonRing F L
  have : Algebra.IsAlgebraic F L := Algebra.IsIntegral.isAlgebraic
  let : Algebra F K := (IsFractionRing.lift hφ : F →+* K).toAlgebra
  have : Module.IsTorsionFree F L := ⟨fun r hr x y hxy => by
    simpa [smul_smul, inv_mul_cancel₀ hr.ne_zero] using congrArg (r⁻¹ • ·) hxy⟩
  let χL : L →ₐ[F] K := IsAlgClosed.lift
  refine ⟨(χL : L →+* K).comp ((Ideal.Quotient.mk m).comp (algebraMap D DF)), ?_⟩
  ext r
  have h1 : algebraMap D DF (algebraMap R D r) = algebraMap F DF (algebraMap R F r) :=
    (IsLocalization.map_eq (S := F) _ r).symm
  simp only [RingHom.comp_apply, h1]
  change χL (algebraMap F L (algebraMap R F r)) = φ r
  rw [AlgHom.commutes]
  exact IsFractionRing.lift_algebraMap hφ r

/-! ### The universal binary forms -/

section Universal

variable {R : Type} [CommRing R] {ι : Type} {N : ℕ} (G : ι → MvPolynomial (Fin (N + 1)) R)
  (e : ℕ)

/-- The coefficient ring `R[c_{k,a}]` of `N + 1` binary forms of degree `e`. -/
private abbrev CoeffRing (R : Type) [CommRing R] (N e : ℕ) : Type :=
  MvPolynomial (Fin (N + 1) × Fin (e + 1)) R

/-- The universal binary forms `∑_a c_{k,a} t^a`. -/
private noncomputable def univForm (k : Fin (N + 1)) : (CoeffRing R N e)[X] :=
  ∑ a : Fin (e + 1), Polynomial.monomial a (MvPolynomial.X (k, a))

/-- The ideal of the coefficients of the `G l` evaluated on the universal forms. -/
private noncomputable def univIdeal : Ideal (CoeffRing R N e) :=
  Ideal.span {x | ∃ l c, x = (MvPolynomial.aeval (univForm e) (G l)).coeff c}

/-- The minor `c_{k,a} c_{k',b} - c_{k,b} c_{k',a}`. -/
private noncomputable def univMinor (k k' : Fin (N + 1)) (a b : Fin (e + 1)) :
    CoeffRing R N e :=
  MvPolynomial.X (k, a) * MvPolynomial.X (k', b) - MvPolynomial.X (k, b) * MvPolynomial.X (k', a)

/-- The algebra of solutions of `G` in binary forms of degree `e` with the given minor
invertible. -/
private abbrev UnivAlg (k k' : Fin (N + 1)) (a b : Fin (e + 1)) : Type :=
  Localization.Away (Ideal.Quotient.mk (univIdeal G e) (univMinor e k k' a b))

variable {G e}

/-- The coefficients of the universal forms are the variables. -/
private theorem univForm_coeff (k : Fin (N + 1)) (a : Fin (e + 1)) :
    (univForm (R := R) e k).coeff a = MvPolynomial.X (k, a) := by
  rw [univForm, Polynomial.finsetSum_coeff, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [Polynomial.coeff_monomial, ite_eq_right]
    exact fun h => hb (Fin.ext h)
  · simp

/-- The universal forms, after any change of coefficients, have degree at most `e`. -/
private theorem natDegree_univForm_map {A : Type} [CommRing A] (χ : CoeffRing R N e →+* A)
    (k : Fin (N + 1)) : ((univForm e k).map χ).natDegree ≤ e := by
  refine (Polynomial.natDegree_map_le).trans ?_
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp a.2)

/-- Evaluation commutes with a change of coefficients. -/
private theorem map_aeval_univForm {A : Type} [CommRing A] (χ : CoeffRing R N e →+* A) (ψ : R →+* A)
    (hχ : χ.comp MvPolynomial.C = ψ) (g : MvPolynomial (Fin (N + 1)) R) :
    (MvPolynomial.aeval (univForm e) g).map χ =
      MvPolynomial.aeval (fun k => (univForm e k).map χ) (g.map ψ) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map,
    ← Polynomial.coe_mapRingHom, MvPolynomial.eval₂_comp_left]
  congr 1
  ext r
  simp [← hχ]

/-- **A point of the universal algebra is a solution.** -/
private theorem hasBinarySolution_of_ringHom {K : Type} [Field K] (φ : R →+* K) {k k' : Fin (N + 1)}
    {a b : Fin (e + 1)} (χ : UnivAlg G e k k' a b →+* K)
    (hχ : χ.comp (algebraMap R (UnivAlg G e k k' a b)) = φ) :
    HasBinarySolution K (fun l => (G l).map φ) e := by
  classical
  let χ' : CoeffRing R N e →+* K :=
    χ.comp ((algebraMap _ (UnivAlg G e k k' a b)).comp (Ideal.Quotient.mk (univIdeal G e)))
  have hχ' : χ'.comp MvPolynomial.C = φ := by
    rw [← hχ]
    rfl
  refine ⟨fun k => (univForm e k).map χ', fun k => natDegree_univForm_map χ' k, fun l => ?_,
    k, k', a, b, ?_⟩
  · rw [← map_aeval_univForm χ' φ hχ']
    ext c
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    change χ (algebraMap (CoeffRing R N e ⧸ univIdeal G e) _
      (Ideal.Quotient.mk (univIdeal G e) _)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem (I := univIdeal G e) |>.mpr
      (Ideal.subset_span ⟨l, c, rfl⟩), map_zero, map_zero]
  · simp only [Polynomial.coeff_map, univForm_coeff]
    have hu : IsUnit (χ' (univMinor e k k' a b)) :=
      (IsLocalization.Away.algebraMap_isUnit
        (Ideal.Quotient.mk (univIdeal G e) (univMinor e k k' a b))).map χ
    rw [← sub_ne_zero, ← map_mul, ← map_mul, ← map_sub]
    exact hu.ne_zero

/-- **A solution is a point of the universal algebra.** -/
private theorem exists_ringHom_of_hasBinarySolution {K : Type} [Field K] (ψ : R →+* K)
    (h : HasBinarySolution K (fun l => (G l).map ψ) e) :
    ∃ (k k' : Fin (N + 1)) (a b : Fin (e + 1)) (χ : UnivAlg G e k k' a b →+* K),
      χ.comp (algebraMap R (UnivAlg G e k k' a b)) = ψ := by
  classical
  obtain ⟨f, hdeg, hG, k, k', a, b, hab⟩ := h
  have hz : ∀ j c, e < c → (f j).coeff c = 0 := fun j _ hc =>
    Polynomial.coeff_eq_zero_of_natDegree_lt ((hdeg j).trans_lt hc)
  have ha : a < e + 1 := by
    by_contra ha
    simp [hz k a (by omega), hz k' a (by omega)] at hab
  have hb : b < e + 1 := by
    by_contra hb
    simp [hz k b (by omega), hz k' b (by omega)] at hab
  let ev : CoeffRing R N e →+* K := MvPolynomial.eval₂Hom ψ fun x => (f x.1).coeff x.2
  have hev : ev.comp MvPolynomial.C = ψ := by
    ext r
    simp [ev]
  have hform : ∀ k, (univForm e k).map ev = f k := by
    intro k
    rw [univForm, Polynomial.map_sum]
    simp only [Polynomial.map_monomial]
    conv_rhs => rw [(f k).as_sum_range' (e + 1) (Nat.lt_succ_of_le (hdeg k))]
    rw [← Fin.sum_univ_eq_sum_range]
    simp [ev]
  have hI : univIdeal G e ≤ RingHom.ker ev := by
    rw [univIdeal, Ideal.span_le]
    rintro _ ⟨l, c, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, ← Polynomial.coeff_map, map_aeval_univForm ev ψ hev]
    simp only [hform, hG l, Polynomial.coeff_zero]
  let ev' : (CoeffRing R N e ⧸ univIdeal G e) →+* K := Ideal.Quotient.lift _ ev hI
  have hu :
      IsUnit (ev' (Ideal.Quotient.mk (univIdeal G e) (univMinor e k k' ⟨a, ha⟩ ⟨b, hb⟩))) := by
    refine isUnit_iff_ne_zero.mpr ?_
    rw [show ev' (Ideal.Quotient.mk (univIdeal G e) (univMinor e k k' ⟨a, ha⟩ ⟨b, hb⟩)) =
      ev (univMinor e k k' ⟨a, ha⟩ ⟨b, hb⟩) from Ideal.Quotient.lift_mk _ _ _]
    simp only [univMinor, map_sub, map_mul, ev, MvPolynomial.eval₂Hom_X']
    exact sub_ne_zero.mpr hab
  refine ⟨k, k', ⟨a, ha⟩, ⟨b, hb⟩, IsLocalization.Away.lift _ hu, ?_⟩
  ext r
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply R (CoeffRing R N e ⧸ univIdeal G e),
    IsLocalization.Away.lift_eq]
  change ev' (Ideal.Quotient.mk _ (MvPolynomial.C r)) = ψ r
  simp only [ev']
  exact RingHom.congr_fun hev r

end Universal

/-- The universal algebra is of finite type over the coefficients. -/
private theorem finiteType_univAlg {R : Type} [CommRing R] {ι : Type} {N : ℕ}
    (G : ι → MvPolynomial (Fin (N + 1)) R) (e : ℕ) (k k' : Fin (N + 1)) (a b : Fin (e + 1)) :
    Algebra.FiniteType R (UnivAlg G e k k' a b) := by
  have : Algebra.FiniteType R (CoeffRing R N e ⧸ univIdeal G e) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R _)
      (Ideal.Quotient.mkₐ_surjective R _)
  have : Algebra.FiniteType (CoeffRing R N e ⧸ univIdeal G e) (UnivAlg G e k k' a b) :=
    IsLocalization.finiteType_of_monoid_fg
      (Submonoid.powers (Ideal.Quotient.mk (univIdeal G e) (univMinor e k k' a b))) _
  exact Algebra.FiniteType.trans (S := CoeffRing R N e ⧸ univIdeal G e) inferInstance
    inferInstance

/-- **Generisation of bounded binary solutions.** Let `R ⊆ K` be a finitely generated domain over
`ℤ` inside an algebraically closed field. If every nonempty open of `Spec R` contains a point over
which the equations `G` have a nonconstant solution in binary forms of degree at most `E`, then
they have one over `K`. -/
private theorem exists_hasBinarySolution_of_dense {R : Type} [CommRing R] [IsDomain R]
    [Algebra.FiniteType ℤ R] {K : Type} [Field K] [IsAlgClosed K] (φ : R →+* K)
    (hφ : Function.Injective φ) {ι : Type} [Finite ι] {N : ℕ}
    (G : ι → MvPolynomial (Fin (N + 1)) R) (E : ℕ)
    (h : ∀ O : Set (PrimeSpectrum R), IsOpen O → O.Nonempty →
      ∃ (k : Type) (_ : Field k) (ψ : R →+* k),
        (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ O ∧
        ∃ e ≤ E, HasBinarySolution k (fun l => (G l).map ψ) e) :
    ∃ e ≤ E, HasBinarySolution K (fun l => (G l).map φ) e := by
  classical
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let X := Σ e : Fin (E + 1), Fin (N + 1) × Fin (N + 1) × Fin (e + 1) × Fin (e + 1)
  let B : X → Type := fun x => UnivAlg G x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  have hfp : ∀ x, (algebraMap R (B x)).FinitePresentation := fun x => by
    have := finiteType_univAlg G x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
    exact RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp inferInstance)
  let T := ⋃ x, Set.range (PrimeSpectrum.comap (algebraMap R (B x)))
  have hT : IsConstructible T :=
    IsConstructible.iUnion fun x => PrimeSpectrum.isConstructible_range_comap (hfp x)
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : ∀ U : Set (PrimeSpectrum R), IsOpen U → U.Nonempty → η ∈ U := by
    rintro U hU ⟨P, hP⟩
    exact ((PrimeSpectrum.le_iff_specializes η P).mp bot_le).mem_open hU hP
  have hd : ∀ U : Set (PrimeSpectrum R), IsOpen U → U.Nonempty → (U ∩ T).Nonempty := by
    intro U hU hne
    obtain ⟨k, _, ψ, hψU, e, he, hsol⟩ := h U hU hne
    obtain ⟨k₁, k₂, a, b, χ, hχ⟩ := exists_ringHom_of_hasBinarySolution ψ hsol
    refine ⟨_, hψU, Set.mem_iUnion.2 ⟨⟨⟨e, by omega⟩, k₁, k₂, a, b⟩,
      ⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, ?_⟩⟩
    ext y
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.mem_ker]
    rw [← hχ]
    rfl
  obtain ⟨x, Q, hQ⟩ := Set.mem_iUnion.1 (mem_of_isConstructible η hη hT hd)
  have hQ' : Q.asIdeal.comap (algebraMap R (B x)) = ⊥ := congrArg PrimeSpectrum.asIdeal hQ
  have := finiteType_univAlg G x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  let D := B x ⧸ Q.asIdeal
  have : Q.asIdeal.IsPrime := Q.2
  have hinj : Function.Injective (algebraMap R D) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    have : r ∈ Q.asIdeal.comap (algebraMap R (B x)) := by
      rwa [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    rwa [hQ'] at this
  obtain ⟨χ, hχ⟩ := exists_ringHom_of_domain (D := D) φ hφ hinj
  refine ⟨x.1, by omega, hasBinarySolution_of_ringHom φ (χ.comp (Ideal.Quotient.mk _)) ?_⟩
  rw [← hχ]
  rfl

end Generisation

section P1Forms

open TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjTwistSections

universe u

variable {S : Type u} [CommRing S] {σ : Type u} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- `𝒪(d)` on `Proj S`, as a module on the scheme. -/
private noncomputable abbrev twistO (d : ℤ) : (AlgebraicGeometry.Proj 𝒮).Modules :=
  twistingSheaf 𝒮 d

/-- The global section of `𝒪(d)` of a homogeneous element of degree `d`. -/
private noncomputable abbrev degSec (d : ℕ) (p : S) (hp : p ∈ 𝒮 d) :
    Γ(twistO 𝒮 (d : ℤ), ⊤) :=
  degreeSection 𝒮 d ⟨p, hp⟩

/-- On `D₊(q)` the degree-`d` section of `p` is the fraction `p/q` times that of `q`. -/
private theorem degreeSection_res_eq {d : ℕ} {p q : S} (hp : p ∈ 𝒮 d) (hq : q ∈ 𝒮 d) :
    (twistO 𝒮 (d : ℤ)).presheaf.map
        (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
        (degreeSection 𝒮 d ⟨p, hp⟩) =
      (AlgebraicGeometry.Proj.awayToSection 𝒮 q).hom
          (Away.mk 𝒮 hq 1 p (by simpa using hp)) •
        (twistO 𝒮 (d : ℤ)).presheaf.map
          (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
          (degreeSection 𝒮 d ⟨q, hq⟩) := by
  refine Subtype.ext (funext fun x => ?_)
  have hL : ((twistO 𝒮 (d : ℤ)).presheaf.map
        (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
        (degreeSection 𝒮 d ⟨p, hp⟩)).1 x =
      LocalizedModule.mk p (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    degreeSection_apply 𝒮 d ⟨p, hp⟩ _
  have hR : ((AlgebraicGeometry.Proj.awayToSection 𝒮 q).hom
          (Away.mk 𝒮 hq 1 p (by simpa using hp)) •
        (twistO 𝒮 (d : ℤ)).presheaf.map
          (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
          (degreeSection 𝒮 d ⟨q, hq⟩)).1 x =
      HomogeneousLocalization.val
          (((AlgebraicGeometry.Proj.awayToSection 𝒮 q).hom
            (Away.mk 𝒮 hq 1 p (by simpa using hp))).1 x) *
        ((twistO 𝒮 (d : ℤ)).presheaf.map
          (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
          (degreeSection 𝒮 d ⟨q, hq⟩)).1 x := rfl
  have hval : HomogeneousLocalization.val
      (((AlgebraicGeometry.Proj.awayToSection 𝒮 q).hom
        (Away.mk 𝒮 hq 1 p (by simpa using hp))).1 x) =
      Localization.mk p ⟨q ^ 1, _⟩ := rfl
  have hLq : ((twistO 𝒮 (d : ℤ)).presheaf.map
        (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
        (degreeSection 𝒮 d ⟨q, hq⟩)).1 x =
      LocalizedModule.mk q (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    degreeSection_apply 𝒮 d ⟨q, hq⟩ _
  rw [hL, hR, hval, hLq]
  rw [show LocalizedModule.mk q (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) =
      Localization.mk q 1 from rfl,
    show LocalizedModule.mk p (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) =
      Localization.mk p 1 from rfl, Localization.mk_mul]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp; ring))

open Stacks.ProjectiveFromSections in
/-- **The ratio of two degree sections is the degree-zero fraction**: on any open inside both the
nonvanishing open of `s_i` and `D₊(H_i)`, the ratio `s_k / s_i` of the degree-`d` sections of
`H_k` and `H_i` is the fraction `H_k / H_i`. -/
private theorem resO_ratio_degreeSection {ι : Type*} {d : ℕ} (H : ι → S) (hH : ∀ k, H k ∈ 𝒮 d)
    [Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒮) (twistO 𝒮 (d : ℤ))]
    (i k : ι) {W : (AlgebraicGeometry.Proj 𝒮).Opens}
    (hi : W ≤ nvCover (L := twistO 𝒮 (d : ℤ)) (fun k => degSec 𝒮 d (H k) (hH k)) i)
    (hb : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒮 (H i)) :
    resO hi (ratio (L := twistO 𝒮 (d : ℤ)) (fun k => degSec 𝒮 d (H k) (hH k)) i k) =
      resO hb ((AlgebraicGeometry.Proj.awayToSection 𝒮 (H i)).hom
        (Away.mk 𝒮 (hH i) 1 (H k) (by simpa using hH k))) := by
  refine eq_of_smul_eq_smul (L := twistO 𝒮 (d : ℤ)) (degreeSection 𝒮 d ⟨H i, hH i⟩) hi ?_
  rw [resO_ratio_smul _ hi k]
  have h := congrArg (resM (L := twistO 𝒮 (d : ℤ)) hb) (degreeSection_res_eq 𝒮 (hH k) (hH i))
  rw [resM_smul] at h
  exact (resM_resT (L := twistO 𝒮 (d : ℤ)) hb _).symm.trans
    (h.trans (congrArg _ (resM_resT (L := twistO 𝒮 (d : ℤ)) hb _)))

section Coeff

open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.ProjectiveSpaceChartRatio (baseRingHom)
open Stacks.ProjectiveFromSections (resO)

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The coefficient ring maps into the degree-zero localization at a homogeneous element. -/
private noncomputable def coeffToAwayElem (f : MvPolynomial (Fin (n + 1)) R) :
    R →+* Away (polyGrading R n) f :=
  (algebraMap (polyGrading R n 0) (Away (polyGrading R n) f)).comp
    (algebraMap R (polyGrading R n 0))

/-- The structure morphism of `Proj R[T₀, …, Tₙ]` on the standard open of a homogeneous element
of positive degree. -/
private theorem awayι_comp_projToSpecCoeff_elem {d : ℕ} (hd : 0 < d)
    {f : MvPolynomial (Fin (n + 1)) R} (hf : f ∈ polyGrading R n d) :
    AlgebraicGeometry.Proj.awayι (polyGrading R n) f hf hd ≫ projToSpecCoeff R n =
      Spec.map (CommRingCat.ofHom (coeffToAwayElem R n f)) := by
  have hz : ∀ r : R, (GradedRing.projZeroRingHom' (polyGrading R n))
      (algebraMap R (MvPolynomial (Fin (n + 1)) R) r) = algebraMap R (polyGrading R n 0) r :=
    fun r => by
      have h := GradedRing.projZeroRingHom'_apply_coe (polyGrading R n)
        (algebraMap R (polyGrading R n 0) r)
      rwa [SetLike.GradeZero.coe_algebraMap] at h
  have key : (HomogeneousLocalization.fromZeroRingHom (polyGrading R n)
        (Submonoid.powers f)).comp
        ((GradedRing.projZeroRingHom' (polyGrading R n)).comp
          (algebraMap R (MvPolynomial (Fin (n + 1)) R))) = coeffToAwayElem R n f := by
    refine RingHom.ext fun r => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, hz r, coeffToAwayElem, RingHom.comp_apply]
    rfl
  rw [Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff, ← Category.assoc,
    AlgebraicGeometry.Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp, key]

/-- **The base ring structure on `D₊(f)`**: restricted to the standard open of a homogeneous `f`
of positive degree, the `R`-algebra structure of `Proj R[T]` is the coefficient inclusion into
the degree-zero localization. -/
private theorem resO_baseRingHom_projToSpecCoeff {d : ℕ} (hd : 0 < d)
    {f : MvPolynomial (Fin (n + 1)) R} (hf : f ∈ polyGrading R n d) (c : R) :
    resO (le_top : AlgebraicGeometry.Proj.basicOpen (polyGrading R n) f ≤ ⊤)
        (baseRingHom (projToSpecCoeff R n) c) =
      (AlgebraicGeometry.Proj.awayToSection (polyGrading R n) f).hom (coeffToAwayElem R n f c) := by
  set B := AlgebraicGeometry.Proj.basicOpen (polyGrading R n) f
  have hinj : Function.Injective B.topIso.inv.hom := fun a b h => by
    rw [← Iso.inv_hom_id_apply B.topIso a, ← Iso.inv_hom_id_apply B.topIso b]
    exact congrArg B.topIso.hom.hom h
  apply hinj
  rw [← Stacks.ProjectiveSpaceChartRatio.baseRingHom_ι]
  have h1 : B.ι ≫ projToSpecCoeff R n =
      (AlgebraicGeometry.Proj.basicOpenIsoSpec (polyGrading R n) f hf hd).hom ≫
        Spec.map (CommRingCat.ofHom (coeffToAwayElem R n f)) := by
    rw [← awayι_comp_projToSpecCoeff_elem R n hd hf,
      ← AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι (polyGrading R n) f hf hd,
      ← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h1, ← Stacks.ProjectiveSpaceChartRatio.baseRingHom_comp, RingHom.comp_apply]
  rw [AlgebraicGeometry.Proj.basicOpenIsoSpec_hom]
  change ((AlgebraicGeometry.Proj.basicOpenToSpec (polyGrading R n) f).app ⊤).hom
    (baseRingHom (Spec.map (CommRingCat.ofHom (coeffToAwayElem R n f))) c) = _
  rw [AlgebraicGeometry.Proj.basicOpenToSpec_app_top]
  have h2 : baseRingHom (Spec.map (CommRingCat.ofHom (coeffToAwayElem R n f))) c =
      (Scheme.ΓSpecIso _).inv.hom (coeffToAwayElem R n f c) := by
    rw [baseRingHom]
    exact (congrArg (fun φ => φ.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (coeffToAwayElem R n f)))).symm
  rw [h2]
  change B.topIso.inv.hom ((AlgebraicGeometry.Proj.awayToSection (polyGrading R n) f).hom
    ((Scheme.ΓSpecIso _).hom.hom ((Scheme.ΓSpecIso _).inv.hom (coeffToAwayElem R n f c)))) = _
  rw [Iso.inv_hom_id_apply]

/-- A homogeneous polynomial of degree `m` scales by `c ^ m`. -/
private theorem eval₂_mul_of_isHomogeneous {A B : Type*} [CommRing A] [CommRing B] {ι : Type*}
    [Finite ι] (g : A →+* B) (x : ι → B) (c : B) {F : MvPolynomial ι A} {m : ℕ}
    (hF : F.IsHomogeneous m) :
    MvPolynomial.eval₂ g (fun k => c * x k) F = c ^ m * MvPolynomial.eval₂ g x F := by
  have := Fintype.ofFinite ι
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = m := by
    have := hF (MvPolynomial.mem_support_iff.mp hd)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

variable {R} {N e : ℕ} (H : Fin (N + 1) → MvPolynomial (Fin 2) R)
  (hH : ∀ k, H k ∈ polyGrading R 1 e)

/-- Evaluation at the fractions `H_k / H_i` in the degree-zero localization at `H_i`. -/
private noncomputable def awayEval (i : Fin (N + 1)) :
    MvPolynomial (Fin (N + 1)) R →+* Away (polyGrading R 1) (H i) :=
  MvPolynomial.eval₂Hom (coeffToAwayElem R 1 (H i))
    (fun k => Away.mk (polyGrading R 1) (hH i) 1 (H k) (by simpa using hH k))

/-- **The evaluation at the fractions is the fraction of the evaluation**: for `F` homogeneous of
degree `m`, `F(H / H_i) · H_i ^ m = F(H)`. -/
private theorem val_awayEval_mul (i : Fin (N + 1)) {F : MvPolynomial (Fin (N + 1)) R} {m : ℕ}
    (hF : F.IsHomogeneous m) :
    (awayEval H hH i F).val * algebraMap _ (Localization.Away (H i)) (H i) ^ m =
      algebraMap _ (Localization.Away (H i)) (MvPolynomial.aeval H F) := by
  have hval : ∀ z : Away (polyGrading R 1) (H i), z.val =
      algebraMap (Away (polyGrading R 1) (H i)) (Localization.Away (H i)) z := fun z => rfl
  rw [hval, awayEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  set u : Localization.Away (H i) := Localization.mk 1 ⟨H i, 1, pow_one _⟩ with hu
  have hx : (algebraMap (Away (polyGrading R 1) (H i)) (Localization.Away (H i))) ∘
      (fun k => Away.mk (polyGrading R 1) (hH i) 1 (H k) (by simpa using hH k)) =
      fun k => u * algebraMap _ (Localization.Away (H i)) (H k) := by
    funext k
    simp only [Function.comp_apply, ← hval, Away.val_mk, u]
    rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    simp
  have hc : (algebraMap (Away (polyGrading R 1) (H i)) (Localization.Away (H i))).comp
      (coeffToAwayElem R 1 (H i)) =
      (algebraMap (MvPolynomial (Fin 2) R) (Localization.Away (H i))).comp MvPolynomial.C := by
    ext c
    simp only [RingHom.comp_apply, ← hval, coeffToAwayElem]
    rfl
  have hunit : u * algebraMap _ (Localization.Away (H i)) (H i) = 1 := by
    rw [hu, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    simp only [one_mul, mul_one]
    exact Localization.mk_self (⟨H i, 1, pow_one _⟩ : Submonoid.powers (H i))
  rw [hx, hc, eval₂_mul_of_isHomogeneous _ _ _ hF, mul_comm, ← mul_assoc, ← mul_pow,
    mul_comm _ u, hunit, one_pow, one_mul, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
  rfl

end Coeff

section Forms

open Polynomial

/-- **Removing the common factor of a nonconstant tuple of polynomials.** -/
private theorem exists_coprime_of_minor {K : Type*} [Field K] {N : ℕ} {ι : Type*}
    (G : ι → MvPolynomial (Fin (N + 1)) K) (hG : ∀ l, ∃ d, (G l).IsHomogeneous d) {e : ℕ}
    (f : Fin (N + 1) → K[X]) (hdeg : ∀ k, (f k).natDegree ≤ e)
    (hGf : ∀ l, MvPolynomial.aeval f (G l) = 0)
    (hmin : ∃ k k' a b, (f k).coeff a * (f k').coeff b ≠ (f k).coeff b * (f k').coeff a) :
    ∃ (e' : ℕ) (h : Fin (N + 1) → K[X]), 1 ≤ e' ∧ e' ≤ e ∧ (∀ k, (h k).natDegree ≤ e') ∧
      (∃ i, (h i).natDegree = e') ∧ Ideal.span (Set.range h) = ⊤ ∧
      ∀ l, MvPolynomial.aeval h (G l) = 0 := by
  classical
  obtain ⟨k₀, k₁, a, b, hab⟩ := hmin
  have hne : ∃ k, f k ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hab
    simp [hall k₀]
  have hs : (Finset.univ : Finset (Fin (N + 1))).Nonempty := Finset.univ_nonempty
  obtain ⟨h, hfh, hgcd⟩ := Finset.extract_gcd f hs
  set g := Finset.univ.gcd f with hg
  have hg0 : g ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := hne
    exact hk (Finset.gcd_eq_zero_iff.mp h0 k (Finset.mem_univ k))
  have hfh' : ∀ k, f k = g * h k := fun k => hfh k (Finset.mem_univ k)
  have hdegh : ∀ k, (h k).natDegree ≤ e := by
    intro k
    by_cases hk : f k = 0
    · have : h k = 0 := by
        have := hfh' k
        rw [hk] at this
        exact (mul_eq_zero.mp this.symm).resolve_left hg0
      simp [this]
    · have := hdeg k
      rw [hfh' k, natDegree_mul hg0 (fun h0 => hk (by rw [hfh' k, h0, mul_zero]))] at this
      omega
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun k => (h k).natDegree) hs
  set e' := (h i).natDegree
  have hspan : Ideal.span (Set.range h) = ⊤ := by
    obtain ⟨d, hd⟩ := (Submodule.IsPrincipal.principal (Ideal.span (Set.range h)))
    have hdvd : ∀ k, d ∣ h k := fun k => by
      have : h k ∈ Ideal.span (Set.range h) := Ideal.subset_span ⟨k, rfl⟩
      rw [hd] at this
      exact Ideal.mem_span_singleton.mp this
    have hunit : IsUnit d := by
      have : d ∣ Finset.univ.gcd h := Finset.dvd_gcd fun k _ => hdvd k
      rw [hgcd] at this
      exact isUnit_of_dvd_one this
    rw [hd]
    exact Ideal.span_singleton_eq_top.mpr hunit
  have he' : 1 ≤ e' := by
    by_contra h0
    push Not at h0
    have hc : ∀ k, h k = Polynomial.C ((h k).coeff 0) := fun k =>
      eq_C_of_natDegree_eq_zero (by have := hi k (Finset.mem_univ k); omega)
    apply hab
    rw [hfh' k₀, hfh' k₁, hc k₀, hc k₁]
    simp only [coeff_mul_C, mul_comm (g.coeff _)]
    ring
  refine ⟨e', h, he', (hdegh i), fun k => hi k (Finset.mem_univ k), ⟨i, rfl⟩, hspan, fun l => ?_⟩
  obtain ⟨d, hd⟩ := hG l
  have := hGf l
  rw [show f = fun k => g * h k from funext hfh', MvPolynomial.aeval_def,
    eval₂_mul_of_isHomogeneous _ _ _ hd, ← MvPolynomial.aeval_def] at this
  exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hg0)

/-- **Homogenised Bézout**: if `h` generates the unit ideal, a power of `X₁` lies in the span of
the homogenisations. -/
private theorem exists_X_one_pow_mem_span {K : Type*} [Field K] {ι : Type*} [Finite ι] {e : ℕ}
    (h : ι → K[X]) (hdeg : ∀ k, (h k).natDegree ≤ e) (hspan : Ideal.span (Set.range h) = ⊤) :
    ∃ M, (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ M ∈
      Ideal.span (Set.range fun k => (h k).homogenize e) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp (hspan ▸ Submodule.mem_top :
    (1 : K[X]) ∈ Ideal.span (Set.range h))
  set D := Finset.univ.sup fun k => (c k).natDegree
  refine ⟨D + e, ?_⟩
  rw [← homogenize_one, ← hc, homogenize_finsetSum]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [homogenize_mul _ _ (Finset.le_sup (f := fun k => (c k).natDegree) (Finset.mem_univ k))
    (hdeg k)]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

/-- At a prime containing `X₁`, the homogenisation of a polynomial of exact degree `e` lies in the
prime only if `X₀` does. -/
private theorem X_zero_mem_of_homogenize_mem {K : Type*} [Field K] {e : ℕ} (p : K[X])
    (hp : p.natDegree = e) (hp0 : p ≠ 0) (P : Ideal (MvPolynomial (Fin 2) K)) [P.IsPrime]
    (h1 : MvPolynomial.X 1 ∈ P) (hP : p.homogenize e ∈ P) : MvPolynomial.X 0 ∈ P := by
  rcases Nat.eq_zero_or_pos e with he | he
  · exfalso
    have : p = Polynomial.C (p.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    have hc : p.coeff 0 ≠ 0 := fun h0 => hp0 (by rw [this, h0, map_zero])
    rw [this, homogenize_C, he, pow_zero, mul_one] at hP
    exact (Ideal.IsPrime.ne_top ‹_›) (Ideal.eq_top_of_isUnit_mem _ hP
      ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C))
  have hsplit : p = p.eraseLead + Polynomial.C p.leadingCoeff * Polynomial.X ^ e := by
    rw [← hp, ← C_mul_X_pow_eq_monomial.symm, eraseLead_add_monomial_natDegree_leadingCoeff]
  have hlow : p.eraseLead.natDegree ≤ e - 1 := by
    have := eraseLead_natDegree_lt_or_eraseLead_eq_zero p
    rcases this with h | h
    · omega
    · rw [h]; simp
  have hH : p.homogenize e = p.eraseLead.homogenize (e - 1) * MvPolynomial.X 1 +
      MvPolynomial.C p.leadingCoeff * MvPolynomial.X 0 ^ e := by
    conv_lhs => rw [hsplit]
    rw [homogenize_add, homogenize_C_mul, homogenize_X_pow le_rfl, Nat.sub_self, pow_zero, mul_one]
    congr 1
    have := homogenize_mul p.eraseLead 1 hlow (by simp : (1 : K[X]).natDegree ≤ 1)
    rw [mul_one, Nat.sub_add_cancel he, homogenize_one, pow_one] at this
    exact this
  rw [hH] at hP
  have h2 : MvPolynomial.C p.leadingCoeff * MvPolynomial.X 0 ^ e ∈ P := by
    have := P.sub_mem hP (P.mul_mem_left (p.eraseLead.homogenize (e - 1)) h1)
    simpa using this
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  rcases (Ideal.IsPrime.mem_or_mem ‹_› h2) with h | h
  · exact absurd (Ideal.eq_top_of_isUnit_mem _ h
      ((isUnit_iff_ne_zero.mpr hlc).map MvPolynomial.C)) (Ideal.IsPrime.ne_top ‹_›)
  · exact Ideal.IsPrime.mem_of_pow_mem ‹_› e h

/-- Homogenisation keeps the equations: if the homogeneous `G` vanishes on the polynomials `h`,
it vanishes on their homogenisations. -/
private theorem aeval_homogenize_eq_zero {K : Type*} [Field K] {N : ℕ} {e : ℕ}
    (h : Fin (N + 1) → K[X]) (hdeg : ∀ k, (h k).natDegree ≤ e)
    {G : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hG : G.IsHomogeneous d)
    (hGh : MvPolynomial.aeval h G = 0) :
    MvPolynomial.aeval (fun k => (h k).homogenize e) G = 0 := by
  have hhom : (MvPolynomial.aeval (fun k => (h k).homogenize e) G).IsHomogeneous (e * d) :=
    hG.aeval _ fun k => isHomogeneous_homogenize _
  have hdeh : MvPolynomial.aeval (R := K) ![(Polynomial.X : K[X]), 1]
      (MvPolynomial.aeval (fun k => (h k).homogenize e) G) = 0 := by
    rw [MvPolynomial.comp_aeval_apply, ← hGh]
    congr 2
    funext k
    exact aeval_homogenize_X_one _ (hdeg k)
  rw [← homogenize_eq_of_isHomogeneous hhom hdeh, homogenize_zero]

end Forms

section ChartEval

open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.ProjectiveSpaceChartRatio (baseRingHom)
open Stacks.ProjectiveFromSections

variable {K : Type u} [Field K] {N e : ℕ} (H : Fin (N + 1) → MvPolynomial (Fin 2) K)
  (hH : ∀ k, H k ∈ polyGrading K 1 e)

/-- Restriction to the same open is the identity. -/
private theorem resO_self {X : Scheme.{u}} {W : X.Opens} (a : Γ(X, W)) :
    resO (le_refl W) a = a := by
  simp [resO]

/-- Restriction maps zero to zero. -/
private theorem resO_zero {X : Scheme.{u}} {W W' : X.Opens} (h : W' ≤ W) :
    resO h (0 : Γ(X, W)) = 0 := map_zero _

/-- Restriction is transitive. -/
private theorem resO_resO {X : Scheme.{u}} {W₁ W₂ W₃ : X.Opens} (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂)
    (a : Γ(X, W₁)) : resO h₂ (resO h₁ a) = resO (h₂.trans h₁) a := by
  simp only [resO, ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- **The chart evaluation of the morphism of a tuple of degree sections**: on the chart of `s_i`,
evaluating a polynomial at the ratios `s_k / s_i` is the image of its evaluation at the fractions
`H_k / H_i`. -/
private theorem chartEval_degreeSection (he : 0 < e) (i : Fin (N + 1))
    (hW : nvCover (L := twistO (polyGrading K 1) (e : ℤ))
        (fun k => degSec (polyGrading K 1) e (H k) (hH k)) i ≤
      AlgebraicGeometry.Proj.basicOpen (polyGrading K 1) (H i))
    (F : MvPolynomial (Fin (N + 1)) K) :
    MMP.Fourfold.chartEval (L := twistO (polyGrading K 1) (e : ℤ))
        (fun k => degSec (polyGrading K 1) e (H k) (hH k)) (projToSpecCoeff K 1) i F =
      (nvCover (L := twistO (polyGrading K 1) (e : ℤ))
          (fun k => degSec (polyGrading K 1) e (H k) (hH k)) i).topIso.inv.hom
        (resO hW ((AlgebraicGeometry.Proj.awayToSection (polyGrading K 1) (H i)).hom
          (awayEval H hH i F))) := by
  set W := nvCover (L := twistO (polyGrading K 1) (e : ℤ))
    (fun k => degSec (polyGrading K 1) e (H k) (hH k)) i
  let ρ : Away (polyGrading K 1) (H i) →+* Γ(W.toScheme, ⊤) :=
    W.topIso.inv.hom.comp (((AlgebraicGeometry.Proj (polyGrading K 1)).presheaf.map
      (homOfLE hW).op).hom.comp (AlgebraicGeometry.Proj.awayToSection (polyGrading K 1) (H i)).hom)
  have key : MMP.Fourfold.chartEval (L := twistO (polyGrading K 1) (e : ℤ))
      (fun k => degSec (polyGrading K 1) e (H k) (hH k)) (projToSpecCoeff K 1) i =
      ρ.comp (awayEval H hH i) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [MMP.Fourfold.chartEval, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, awayEval, ρ]
      rw [Stacks.ProjectiveSpaceChartRatio.baseRingHom_ι]
      congr 1
      rw [← resO_baseRingHom_projToSpecCoeff K 1 he (hH i)]
      exact (resO_resO _ hW _).symm
    · intro k
      simp only [MMP.Fourfold.chartEval, MvPolynomial.eval₂Hom_X', RingHom.comp_apply, awayEval, ρ]
      unfold chartRatio
      congr 1
      exact (resO_self _).symm.trans (resO_ratio_degreeSection (polyGrading K 1) H hH i k le_rfl hW)
  exact RingHom.congr_fun key F

/-- The nonvanishing locus of the degree section of a homogeneous `F` is `D₊(F)`. -/
private theorem nonvanishingLocus_degreeSection (K : Type u) [CommRing K] (N m : ℕ)
    (F : polyGrading K N m) :
    Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj (polyGrading K N))
        (twistingSheaf (polyGrading K N) (m : ℤ))
        (degreeSection (polyGrading K N) m F) =
      (AlgebraicGeometry.Proj.basicOpen (polyGrading K N) (F : MvPolynomial _ K) : Set _) := by
  have key : ∀ (k : ℕ) (hk : k = m * 1) (g : polyGrading K N k),
      Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj (polyGrading K N))
          (twistingSheaf (polyGrading K N) (k : ℤ)) (degreeSection (polyGrading K N) k g) =
        (AlgebraicGeometry.Proj.basicOpen (polyGrading K N) (g : MvPolynomial _ K) : Set _) := by
    intro k hk g
    subst hk
    exact
      Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nonvanishingLocus_degreeSection_eq_basicOpen
        (polyGrading K N) (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top _ _) one_pos m g
  exact key m (mul_one m).symm F

/-- The nonvanishing open of the degree-`e` section of `f` is `D₊(f)`. -/
private theorem nvOpen_degSec (f : MvPolynomial (Fin 2) K) (hf : f ∈ polyGrading K 1 e) :
    nvOpen (twistO (polyGrading K 1) (e : ℤ)) (degSec (polyGrading K 1) e f hf) =
      AlgebraicGeometry.Proj.basicOpen (polyGrading K 1) f :=
  TopologicalSpace.Opens.ext (nonvanishingLocus_degreeSection K 1 e ⟨f, hf⟩)

/-- For `H_i ≠ 0` and `F` homogeneous, `F(H / H_i) = 0` if and only if `F(H) = 0`. -/
private theorem awayEval_eq_zero_iff {i : Fin (N + 1)} {F : MvPolynomial (Fin (N + 1)) K} {m : ℕ}
    (hF : F.IsHomogeneous m) (hHi : H i ≠ 0) :
    awayEval H hH i F = 0 ↔ MvPolynomial.aeval H F = 0 := by
  have hu : IsUnit (algebraMap _ (Localization.Away (H i)) (H i) ^ m) :=
    (IsLocalization.Away.algebraMap_isUnit (H i)).pow m
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin 2) K) (Localization.Away (H i))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hHi)
  have key := val_awayEval_mul H hH i hF
  constructor
  · intro h
    rw [h, HomogeneousLocalization.val_zero, zero_mul] at key
    exact hinj (key.symm.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero] at key
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_zero]
    exact (hu.mul_left_eq_zero).mp key

/-- If the evaluation vanishes, so does every chart evaluation. -/
private theorem chartEval_eq_zero_of_aeval_eq_zero (he : 0 < e) (i : Fin (N + 1))
    {F : MvPolynomial (Fin (N + 1)) K} {m : ℕ} (hF : F.IsHomogeneous m)
    (h : MvPolynomial.aeval H F = 0) :
    MMP.Fourfold.chartEval (L := twistO (polyGrading K 1) (e : ℤ))
        (fun k => degSec (polyGrading K 1) e (H k) (hH k)) (projToSpecCoeff K 1) i F = 0 := by
  by_cases hHi : H i = 0
  · have hz : awayEval H hH i F = 0 := by
      apply HomogeneousLocalization.val_injective
      have hsub : (0 : MvPolynomial (Fin 2) K) ∈ Submonoid.powers (H i) := ⟨1, by simp [hHi]⟩
      have : Subsingleton (Localization.Away (H i)) :=
        IsLocalization.subsingleton (M := Submonoid.powers (H i)) hsub
      exact Subsingleton.elim _ _
    rw [chartEval_degreeSection H hH he i (le_of_eq (nvOpen_degSec _ _)) F, hz, map_zero,
      resO_zero, map_zero]
  · rw [chartEval_degreeSection H hH he i (le_of_eq (nvOpen_degSec _ _)) F,
      (awayEval_eq_zero_iff H hH hF hHi).mpr h, map_zero, resO_zero, map_zero]

/-- Conversely, a vanishing chart evaluation at a nonzero form forces the evaluation to vanish. -/
private theorem aeval_eq_zero_of_chartEval_eq_zero (he : 0 < e) {i : Fin (N + 1)} (hHi : H i ≠ 0)
    {F : MvPolynomial (Fin (N + 1)) K} {m : ℕ} (hF : F.IsHomogeneous m)
    (h : MMP.Fourfold.chartEval (L := twistO (polyGrading K 1) (e : ℤ))
        (fun k => degSec (polyGrading K 1) e (H k) (hH k)) (projToSpecCoeff K 1) i F = 0) :
    MvPolynomial.aeval H F = 0 := by
  have hWB := nvOpen_degSec (H i) (hH i)
  rw [chartEval_degreeSection H hH he i (le_of_eq hWB) F] at h
  have h1 : resO (le_of_eq hWB) ((AlgebraicGeometry.Proj.awayToSection (polyGrading K 1) (H i)).hom
      (awayEval H hH i F)) = 0 := by
    set W := nvCover (L := twistO (polyGrading K 1) (e : ℤ))
      (fun k => degSec (polyGrading K 1) e (H k) (hH k)) i
    have hinj : Function.Injective W.topIso.inv.hom := fun a b hab => by
      rw [← Iso.inv_hom_id_apply W.topIso a, ← Iso.inv_hom_id_apply W.topIso b]
      exact congrArg _ hab
    exact hinj (h.trans (map_zero _).symm)
  have h2 : (AlgebraicGeometry.Proj.awayToSection (polyGrading K 1) (H i)).hom
      (awayEval H hH i F) = 0 := by
    have := congrArg (resO (le_of_eq hWB.symm)) h1
    rwa [resO_resO, resO_self, resO_zero] at this
  have h3 : awayEval H hH i F = 0 := by
    let hiso := (AlgebraicGeometry.Proj.basicOpenIsoAway (polyGrading K 1) (H i) (hH i) he)
    have hinj : Function.Injective
        (AlgebraicGeometry.Proj.awayToSection (polyGrading K 1) (H i)).hom := fun a b hab => by
      have := congrArg hiso.inv.hom hab
      rwa [show (AlgebraicGeometry.Proj.awayToSection (polyGrading K 1) (H i)) = hiso.hom from rfl,
        Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at this
    exact hinj (h2.trans (map_zero _).symm)
  exact (awayEval_eq_zero_iff H hH hF hHi).mp h3

open Polynomial in
/-- **Homogenised forms without a common zero generate `𝒪(e)`.** -/
private theorem generatesStalks_homogenize (he : 0 < e) (h : Fin (N + 1) → K[X])
    (hdeg : ∀ k, (h k).natDegree ≤ e) (hspan : Ideal.span (Set.range h) = ⊤)
    (hmax : ∃ i, (h i).natDegree = e) :
    GeneratesStalks (L := twistO (polyGrading K 1) (e : ℤ))
      (fun k => degSec (polyGrading K 1) e ((h k).homogenize e)
        ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (isHomogeneous_homogenize _))) := by
  rw [Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem]
  intro x
  simp only [nvCover, nvOpen_degSec]
  by_contra hall
  push Not at hall
  have hmem : ∀ k, (h k).homogenize e ∈ x.asHomogeneousIdeal.toIdeal := fun k => by
    have := hall k
    rwa [AlgebraicGeometry.Proj.mem_basicOpen, not_not] at this
  have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have h1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ∈ x.asHomogeneousIdeal.toIdeal := by
    obtain ⟨M, hM⟩ := exists_X_one_pow_mem_span h hdeg hspan
    refine Ideal.IsPrime.mem_of_pow_mem ‹_› M ?_
    refine (Ideal.span_le.2 ?_) hM
    rintro _ ⟨k, rfl⟩
    exact hmem k
  obtain ⟨i, hi⟩ := hmax
  have hi0 : h i ≠ 0 := fun h0 => by rw [h0, natDegree_zero] at hi; omega
  have h0 := X_zero_mem_of_homogenize_mem (h i) hi hi0 _ h1 (hmem i)
  have hcov := Stacks.AlgebraicGeometry.ProjPolyChart.iSup_basicOpen_X_eq_top K 1
  have hx : x ∈ (⨆ j, AlgebraicGeometry.Proj.basicOpen (polyGrading K 1)
      (MvPolynomial.X j : MvPolynomial (Fin 2) K)) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  rw [AlgebraicGeometry.Proj.mem_basicOpen] at hj
  fin_cases j
  · exact hj h0
  · exact hj h1

end ChartEval

section Assembly

open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.ProjectiveFromSections
open CategoryTheory.Limits

/-- Transport of the degree along an equality of structure morphisms. -/
private theorem invertibleCurveDegree_congr_hom {k : Type u} [Field k] {X : Scheme.{u}}
    {f f' : X ⟶ Spec (.of k)} [IsProper f] [IsProper f'] (h : f = f')
    (hd : topologicalKrullDim X ≤ 1) (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    invertibleCurveDegree k f hd M = invertibleCurveDegree k f' hd M := by
  subst h; rfl

/-- **`ℙ¹_K` is a rational curve in itself**: the closed subscheme of `ℙ¹_K` given by the zero
ideal sheaf is a rational curve over `K`. -/
public theorem _root_.MMP.Mori.isRationalCurve_bot_projectiveLine (K : Type) [Field K] :
    MMP.Mori.IsRationalCurve (projectiveLine K ↘ Spec (.of K))
      (⊥ : (projectiveLine K).IdealSheafData) := by
  set ι₀ := (⊥ : (projectiveLine K).IdealSheafData).subschemeι
  have e : (⊥ : (projectiveLine K).IdealSheafData).subscheme ≅ projectiveLine K := asIso ι₀
  have hne : Nonempty (⊥ : (projectiveLine K).IdealSheafData).subscheme :=
    ⟨e.inv.base (Classical.arbitrary (projectiveLine K))⟩
  have hint : IsIntegral (⊥ : (projectiveLine K).IdealSheafData).subscheme :=
    isIntegral_of_isOpenImmersion ι₀
  have hdim : topologicalKrullDim (⊥ : (projectiveLine K).IdealSheafData).subscheme = 1 := by
    rw [← IsCurve.topologicalKrullDim_eq_one (k := K) (f := projectiveLine K ↘ Spec (.of K))]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph
  refine ⟨⟨hint, hdim⟩, inferInstance, ⟨inv ι₀, ?_, inferInstance,
    MMP.Mori.isBirationalMorphism_of_isIso _⟩⟩
  rw [IsIso.inv_hom_id_assoc]

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism' {Y Z : Scheme} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : MMP.Mori.IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
  let := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

section BinaryForms

open Polynomial

/-- The dehomogenisation of a form of degree `e` has degree at most `e`. -/
private theorem natDegree_aeval_X_one_le {K : Type*} [Field K] {e : ℕ} {q : MvPolynomial (Fin 2) K}
    (hq : q.IsHomogeneous e) :
    (MvPolynomial.aeval ![(Polynomial.X : K[X]), 1] q).natDegree ≤ e := by
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  have := hq (MvPolynomial.mem_support_iff.mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fin.sum_univ_two] at this
  simp at this
  omega

/-- The value of a homogenisation at `(1, 0)` is the top coefficient. -/
private theorem eval_one_zero_homogenize {K : Type*} [Field K] (p : K[X]) (n : ℕ) :
    MvPolynomial.eval ![1, 0] (p.homogenize n) = p.coeff n := by
  rw [homogenize, map_sum, Finset.sum_eq_single (n, 0)]
  · simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]
  · rintro ⟨a, b⟩ hab hne
    have hab' : a + b = n := by simpa using hab
    have hb : b ≠ 0 := by
      rintro rfl
      exact hne (by simp_all)
    simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two, hb]
  · intro h
    exact absurd (by simp) h

/-- **A nonconstant binary form over an algebraically closed field has a nontrivial zero.** -/
private theorem exists_eval_eq_zero_of_isHomogeneous {K : Type*} [Field K] [IsAlgClosed K] {e : ℕ}
    (he : 0 < e) {q : MvPolynomial (Fin 2) K} (hq : q.IsHomogeneous e) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ MvPolynomial.eval v q = 0 := by
  set f := MvPolynomial.aeval ![(Polynomial.X : K[X]), 1] q
  have hqf : f.homogenize e = q := Polynomial.homogenize_eq_of_isHomogeneous hq rfl
  have hdeg : f.natDegree ≤ e := natDegree_aeval_X_one_le hq
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · refine ⟨![1, 0], fun h => by simpa using congrFun h 0, ?_⟩
    rw [← hqf, eval_one_zero_homogenize, Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
  · obtain ⟨α, hα⟩ := IsAlgClosed.exists_root f (by
      rw [Polynomial.degree_eq_natDegree (fun h => by rw [h] at heq; simp at heq; omega), heq]
      exact_mod_cast he.ne')
    refine ⟨![α, 1], fun h => by simpa using congrFun h 1, ?_⟩
    rw [← hqf, Polynomial.eval_homogenize hdeg _ (by simp)]
    have : f.eval α = 0 := hα
    simp [this]

section ProjPoint

/-- Evaluation at `v` along the line `t ↦ t v`. -/
private noncomputable def lineEval {K : Type*} [Field K] (v : Fin 2 → K) :
    MvPolynomial (Fin 2) K →+* K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.X * Polynomial.C (v i))

/-- On a form of degree `d`, `lineEval v` is `t ^ d` times the value at `v`. -/
private theorem lineEval_of_isHomogeneous {K : Type*} [Field K] (v : Fin 2 → K)
    {F : MvPolynomial (Fin 2) K} {d : ℕ} (hF : F.IsHomogeneous d) :
    lineEval v F = Polynomial.X ^ d * Polynomial.C (MvPolynomial.eval v F) := by
  rw [lineEval, MvPolynomial.coe_eval₂Hom, eval₂_mul_of_isHomogeneous _ _ _ hF]
  congr 1
  rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  rfl

/-- **The point `[v] ∈ ℙ¹`**: for `v ≠ 0` there is a point of `Proj K[T₀, T₁]` whose ideal contains
every form vanishing at `v`. -/
private theorem exists_projPoint {K : Type*} [Field K] {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ x : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 2) K),
      ∀ (F : MvPolynomial (Fin 2) K) (d : ℕ), F.IsHomogeneous d → MvPolynomial.eval v F = 0 →
        F ∈ x.asHomogeneousIdeal := by
  classical
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) K
  let I : Ideal (MvPolynomial (Fin 2) K) := RingHom.ker (lineEval v)
  have hI : I.IsHomogeneous 𝒜 := by
    intro i r hr
    have hcomp : ∀ j, lineEval v (DirectSum.decompose 𝒜 r j : MvPolynomial (Fin 2) K) =
        Polynomial.X ^ j * Polynomial.C (MvPolynomial.eval v (DirectSum.decompose 𝒜 r j)) :=
      fun j => lineEval_of_isHomogeneous v
        ((MvPolynomial.mem_homogeneousSubmodule _ _).1 (SetLike.coe_mem _))
    have hr' : lineEval v r = 0 := hr
    rw [← DirectSum.sum_support_decompose 𝒜 r, map_sum] at hr'
    simp only [hcomp] at hr'
    have hcoeff := congrArg (fun p => Polynomial.coeff p i) hr'
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_zero, mul_comm (Polynomial.X ^ _),
      Polynomial.coeff_C_mul_X_pow] at hcoeff
    rw [Finset.sum_ite_eq] at hcoeff
    change lineEval v _ = 0
    rw [hcomp]
    split_ifs at hcoeff with hi
    · rw [hcoeff, map_zero, mul_zero]
    · rw [DFinsupp.notMem_support_iff.mp hi]; simp
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  refine ⟨⟨⟨I, hI⟩, RingHom.ker_isPrime _, fun hle => ?_⟩, fun F d hF hFv => ?_⟩
  · have hX : (MvPolynomial.X j : MvPolynomial (Fin 2) K) ∈ HomogeneousIdeal.irrelevant 𝒜 := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne 𝒜 (MvPolynomial.isHomogeneous_X K j) one_ne_zero]
    have := hle hX
    change lineEval v (MvPolynomial.X j) = 0 at this
    simp [lineEval, hj] at this
  · change lineEval v F = 0
    rw [lineEval_of_isHomogeneous v hF, hFv, map_zero, mul_zero]

end ProjPoint

/-- Vanishing `2 × 2` minors make the polynomials proportional to a nonzero one. -/
private theorem exists_eq_C_mul_of_minor_eq_zero {K : Type*} [Field K] {ι : Type*} (f : ι → K[X])
    (hmin : ∀ k k' a b, (f k).coeff a * (f k').coeff b = (f k).coeff b * (f k').coeff a)
    {j : ι} (hj : f j ≠ 0) (k : ι) : ∃ c : K, f k = Polynomial.C c * f j := by
  obtain ⟨b, hb⟩ : ∃ b, (f j).coeff b ≠ 0 := by
    by_contra h
    push Not at h
    exact hj (Polynomial.ext fun n => by simp [h n])
  refine ⟨(f k).coeff b / (f j).coeff b, Polynomial.ext fun a => ?_⟩
  rw [Polynomial.coeff_C_mul]
  have := hmin k j a b
  field_simp
  linear_combination this

end BinaryForms

end Assembly

end P1Forms

open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff) in
open Stacks.ProjectiveFromSections CategoryTheory.Limits Polynomial in
/-- **From binary forms to a rational curve.** Let `Z ⊆ ℙᴺ_K` be the closed subscheme cut out by
homogeneous `G`. A nonconstant solution of `G` in binary forms of degree at most `e` gives a
rational curve `L ⊆ Z` with `0 < deg_L 𝒪(1) ≤ e`. -/
public theorem exists_isRationalCurve_of_hasBinarySolution {K : Type} [Field K] [IsAlgClosed K]
    {N : ℕ} {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of K)) [IsProperVariety K sZ]
    (ι : Z ⟶ projectiveSpaceOverRing N (.of K)) [IsClosedImmersion ι]
    (hι : ι ≫ Limits.pullback.fst (Limits.terminal.from (Spec (.of K)))
      (Limits.terminal.from (projectiveSpaceAtUniverse.{0} N)) = sZ)
    {r : ℕ} (G : Fin r → MvPolynomial (Fin (N + 1)) K) (hG : ∀ l, ∃ d, (G l).IsHomogeneous d)
    (hspan : (MMP.Fourfold.closedSubschemeIdeal ι).toIdeal = Ideal.span (Set.range G))
    {e : ℕ} (h : HasBinarySolution K G e) :
    ∃ (L : Z.IdealSheafData) (hL : Mori.IsRationalCurve sZ L),
      haveI := hL.2.1
      0 < Mori.degreeOn K sZ L.subschemeι hL.1.2.le ((Scheme.Modules.pullback ι).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of K)))) ∧
        Mori.degreeOn K sZ L.subschemeι hL.1.2.le ((Scheme.Modules.pullback ι).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of K)))) ≤ e := by
  classical
  obtain ⟨f, hdeg, hGf, hmin⟩ := h
  obtain ⟨e', hh, he1, he'e, hdegh, hmax, hspanh, hGh⟩ :=
    exists_coprime_of_minor G hG f hdeg hGf hmin
  have he' : 0 < e' := he1
  set H : Fin (N + 1) → MvPolynomial (Fin 2) K := fun k => (hh k).homogenize e' with hHdef
  have hH : ∀ k, H k ∈ polyGrading K 1 e' := fun k =>
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (isHomogeneous_homogenize _)
  set s : Fin (N + 1) → Γ(twistO (polyGrading K 1) (e' : ℤ), ⊤) :=
    fun k => degSec (polyGrading K 1) e' (H k) (hH k) with hsdef
  have hs : GeneratesStalks s := generatesStalks_homogenize he' hh hdegh hspanh hmax
  set π := projToSpecCoeff K 1 with hπ
  set φ₀ := toProjectiveSpaceOver s hs π with hφ₀
  obtain ⟨g, hg⟩ : ∃ g, g ≫ ι = φ₀ := by
    refine (MMP.Fourfold.exists_lift_closedImmersion_iff s π ι hs).mpr ?_
    intro j F hF
    rw [hspan] at hF
    refine (Ideal.span_le (I := RingHom.ker (MMP.Fourfold.chartEval s π j))).2 ?_ hF
    rintro _ ⟨l, rfl⟩
    obtain ⟨d, hd⟩ := hG l
    exact chartEval_eq_zero_of_aeval_eq_zero H hH he' j hd
      (aeval_homogenize_eq_zero hh hdegh hd (hGh l))
  obtain ⟨p, hp, α, hαiso, hαs⟩ :=
    Stacks.TwistPullbackPinned.exists_hom_over_and_iso_pullback_twistingSheafAtUniverse s hs π
  have := hαiso
  have hpφ : p = φ₀ := by
    refine pullback.hom_ext ?_ ?_
    · rw [hp, hφ₀, toProjectiveSpaceOver_fst]
    · change p ≫ projectiveSpaceOver.toIntegralAtUniverse N _ =
        φ₀ ≫ projectiveSpaceOver.toIntegralAtUniverse N _
      rw [MMP.Fourfold.eq_toProjectiveSpaceAtUniverse_of_pinned s _ α hαs hs, hφ₀,
        toProjectiveSpaceOver_snd]
  set O := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of K)) with hO
  let eP : (Scheme.Modules.pullback φ₀).obj O ≅ twistO (polyGrading K 1) (e' : ℤ) :=
    (Scheme.Modules.pullbackComp φ₀ (projectiveSpaceOver.toIntegralAtUniverse N _)).app _ ≪≫
      (Scheme.Modules.pullbackCongr (by rw [hpφ])).app _ ≪≫ asIso α
  have hθ : (projectiveLineIsoProj K).hom ≫ π = projectiveLine K ↘ Spec (.of K) :=
    projectiveLineIsoProj_hom_comp_projToSpecCoeff K
  have : IsProper π := by
    have : π = (projectiveLineIsoProj K).inv ≫ (projectiveLine K ↘ Spec (.of K)) := by
      rw [← hθ, Iso.inv_hom_id_assoc]
    rw [this]; infer_instance
  have hdP : topologicalKrullDim (AlgebraicGeometry.Proj (polyGrading K 1)) ≤ 1 := by
    rw [← (IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (projectiveLineIsoProj K)).isHomeomorph),
      IsCurve.topologicalKrullDim_eq_one (k := K) (f := projectiveLine K ↘ Spec (.of K))]
  have hdegP : invertibleCurveDegree K π hdP ((Scheme.Modules.pullback φ₀).obj O) = e' := by
    rw [invertibleCurveDegree_eq_of_iso K π hdP eP]
    exact invertibleCurveDegree_twistingSheaf_projectiveLineProj K e'
  set θ := projectiveLineIsoProj K with hθdef
  set ν : projectiveLine K ⟶ Z := θ.hom ≫ g with hνdef
  have hν : ν ≫ sZ = projectiveLine K ↘ Spec (.of K) := by
    rw [hνdef, ← hι, Category.assoc, ← Category.assoc g, hg, hφ₀, toProjectiveSpaceOver_fst, hθ]
  set M := (Scheme.Modules.pullback ι).obj O with hM
  have hd1 : topologicalKrullDim (projectiveLine K) ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := K) (f := projectiveLine K ↘ Spec (.of K))).le
  let eν : (Scheme.Modules.pullback ν).obj M ≅
      (Scheme.Modules.pullback θ.hom).obj ((Scheme.Modules.pullback φ₀).obj O) :=
    ((Scheme.Modules.pullbackComp θ.hom g).app M).symm ≪≫ (Scheme.Modules.pullback θ.hom).mapIso
      ((Scheme.Modules.pullbackComp g ι).app O ≪≫ (Scheme.Modules.pullbackCongr hg).app O)
  have hdegν : invertibleCurveDegree K (projectiveLine K ↘ Spec (.of K)) hd1
      ((Scheme.Modules.pullback ν).obj M) = e' := by
    rw [invertibleCurveDegree_eq_of_iso K _ hd1 eν, ← hdegP,
      ← invertibleCurveDegree_pullback_of_isIso θ.hom π hd1 hdP]
    exact invertibleCurveDegree_congr_hom hθ.symm hd1 _
  have hncν : ∀ y : Z, ¬ ∀ x, ν.base x = y := by
    intro y hy
    have := AlgebraicGeometry.invertibleCurveDegree_pullback_eq_zero_of_forall_eq K
      (projectiveLine K ↘ Spec (.of K)) hd1 ν M y hy
    omega
  have hnc : ¬ (ν.base '' ((⊥ : (projectiveLine K).IdealSheafData).support :
      Set (projectiveLine K))).Subsingleton := by
    intro hsub
    obtain ⟨x₀⟩ := (inferInstance : Nonempty (projectiveLine K))
    exact hncν (ν.base x₀) fun x => hsub ⟨x, trivial, rfl⟩ ⟨x₀, trivial, rfl⟩
  have hL := MMP.Mori.IsRationalCurve.ker_subschemeι_comp hν
    (MMP.Mori.isRationalCurve_bot_projectiveLine K) hnc
  set L := ((⊥ : (projectiveLine K).IdealSheafData).subschemeι ≫ ν).ker with hLdef
  refine ⟨L, hL, ?_⟩
  have := hL.2.1
  have hvar : AlgebraicGeometry.IsVariety K sZ := inferInstance
  have hLC : AlgebraicGeometry.IsCurve K (L.subschemeι ≫ sZ) := by
    have := hL.1.1
    have : LocallyOfFiniteType sZ := hvar.toLocallyOfFiniteType
    have : IsSeparated sZ := hvar.toIsSeparated
    have : QuasiCompact sZ := hvar.toQuasiCompact
    have : AlgebraicGeometry.IsVariety K (L.subschemeι ≫ sZ) := {}
    exact { topologicalKrullDim_eq_one := hL.1.2 }
  set lam := inv (⊥ : (projectiveLine K).IdealSheafData).subschemeι ≫
    ((⊥ : (projectiveLine K).IdealSheafData).subschemeι ≫ ν).toImage with hlamdef
  have hlam : lam ≫ L.subschemeι = ν := by
    have h1 := Scheme.Hom.toImage_imageι ((⊥ : (projectiveLine K).IdealSheafData).subschemeι ≫ ν)
    change inv (⊥ : (projectiveLine K).IdealSheafData).subschemeι ≫
      (((⊥ : (projectiveLine K).IdealSheafData).subschemeι ≫ ν).toImage ≫
        ((⊥ : (projectiveLine K).IdealSheafData).subschemeι ≫ ν).imageι) = ν
    rw [h1, IsIso.inv_hom_id_assoc]
  have hlams : lam ≫ (L.subschemeι ≫ sZ) = projectiveLine K ↘ Spec (.of K) := by
    rw [← Category.assoc, hlam, hν]
  have hnclam : ¬ ∃ y, ∀ x, lam.base x = y := by
    rintro ⟨y, hy⟩
    apply hncν (L.subschemeι.base y)
    intro x
    rw [← hlam, Scheme.Hom.comp_apply, hy x]
  have key := AlgebraicGeometry.invertibleCurveDegree_pullback_eq_degreeOver_mul K
    (projectiveLine K ↘ Spec (.of K)) (L.subschemeι ≫ sZ) lam hlams hnclam
    ((Scheme.Modules.pullback L.subschemeι).obj M)
  have hpos := AlgebraicGeometry.degreeOver_pos_of_not_constant K
    (projectiveLine K ↘ Spec (.of K)) (L.subschemeι ≫ sZ) lam hlams hnclam
  have hlhs : invertibleCurveDegree K (projectiveLine K ↘ Spec (.of K)) hd1
      ((Scheme.Modules.pullback lam).obj ((Scheme.Modules.pullback L.subschemeι).obj M)) = e' := by
    rw [← hdegν]
    exact invertibleCurveDegree_eq_of_iso K _ _
      (((Scheme.Modules.pullbackComp lam L.subschemeι).app M) ≪≫
        (Scheme.Modules.pullbackCongr hlam).app M)
  change 0 < invertibleCurveDegree K (L.subschemeι ≫ sZ) _ _ ∧
    invertibleCurveDegree K (L.subschemeι ≫ sZ) _ _ ≤ e
  rw [hlhs] at key
  constructor
  · nlinarith
  · have : (e' : ℤ) ≤ e := by exact_mod_cast he'e
    nlinarith

open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff) in
open Stacks.ProjectiveFromSections CategoryTheory.Limits Polynomial in
/-- **From a rational curve to binary forms.** Let `Z ⊆ ℙᴺ_K` be a closed subscheme on which the
homogeneous `G` vanish. A rational curve `L ⊆ Z` with `deg_L 𝒪(1) = d > 0` gives a nonconstant
solution of `G` in binary forms of degree at most `d`. -/
public theorem hasBinarySolution_of_isRationalCurve {K : Type} [Field K] [IsAlgClosed K]
    {N : ℕ} {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of K))
    (ι : Z ⟶ projectiveSpaceOverRing N (.of K)) [IsClosedImmersion ι]
    (hι : ι ≫ Limits.pullback.fst (Limits.terminal.from (Spec (.of K)))
      (Limits.terminal.from (projectiveSpaceAtUniverse.{0} N)) = sZ)
    {r : ℕ} (G : Fin r → MvPolynomial (Fin (N + 1)) K) (hG : ∀ l, ∃ d, (G l).IsHomogeneous d)
    (L : Z.IdealSheafData) (hL : Mori.IsRationalCurve sZ L)
    (hmem : ∀ l, G l ∈ (MMP.Fourfold.closedSubschemeIdeal (L.subschemeι ≫ ι)).toIdeal)
    (hpos : haveI := hL.2.1
      0 < Mori.degreeOn K sZ L.subschemeι hL.1.2.le ((Scheme.Modules.pullback ι).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of K))))) :
    haveI := hL.2.1
    ∃ e ≤ (Mori.degreeOn K sZ L.subschemeι hL.1.2.le ((Scheme.Modules.pullback ι).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N
            (Spec (.of K))))).toNat, HasBinarySolution K G e := by
  classical
  have := hL.2.1
  obtain ⟨ν₀, hν₀, hfin, hbir⟩ := hL.2.2
  set π := projToSpecCoeff K 1 with hπ
  set θ := projectiveLineIsoProj K with hθdef
  have hθ : θ.hom ≫ π = projectiveLine K ↘ Spec (.of K) :=
    projectiveLineIsoProj_hom_comp_projToSpecCoeff K
  have : IsProper π := by
    have : π = θ.inv ≫ (projectiveLine K ↘ Spec (.of K)) := by rw [← hθ, Iso.inv_hom_id_assoc]
    rw [this]; infer_instance
  set φ' : AlgebraicGeometry.Proj (polyGrading K 1) ⟶ projectiveSpaceOverRing N (.of K) :=
    θ.inv ≫ ν₀ ≫ L.subschemeι ≫ ι with hφ'def
  have hφ'fst : φ' ≫ pullback.fst (terminal.from (Spec (.of K)))
      (terminal.from (projectiveSpaceAtUniverse.{0} N)) = π := by
    rw [hφ'def, Category.assoc, Category.assoc, Category.assoc, hι, hν₀, ← hθ,
      Iso.inv_hom_id_assoc]
  set g₀ := φ' ≫ projectiveSpaceOver.toIntegralAtUniverse N (Spec (.of K)) with hg₀
  set M := (Scheme.Modules.pullback g₀).obj
    (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse N) with hM
  have hσ := Stacks.ProjectiveSpaceModuli.taut_generates g₀
  -- the curve `L` and the degree `d`
  have hvarZ : LocallyOfFiniteType sZ ∧ IsSeparated sZ ∧ QuasiCompact sZ := by
    rw [← hι]; exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hLC : AlgebraicGeometry.IsCurve K (L.subschemeι ≫ sZ) := by
    have := hL.1.1
    have := hvarZ.1; have := hvarZ.2.1; have := hvarZ.2.2
    have : AlgebraicGeometry.IsVariety K (L.subschemeι ≫ sZ) := {}
    exact { topologicalKrullDim_eq_one := hL.1.2 }
  set O := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of K)) with hO
  set NL := (Scheme.Modules.pullback L.subschemeι).obj ((Scheme.Modules.pullback ι).obj O)
    with hNL
  have hν₀' : ν₀ ≫ (L.subschemeι ≫ sZ) = projectiveLine K ↘ Spec (.of K) := hν₀
  have : IsDominant ν₀ := hbir.isDominant
  have hncν₀ : ¬ ∃ y, ∀ x, ν₀.base x = y := by
    rintro ⟨y, hy⟩
    have hrange : Set.range ν₀.base = {y} := Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨Classical.arbitrary _, hy _⟩, fun z ⟨x, hx⟩ => hx ▸ hy x⟩
    have hcl : IsClosed (Set.range ν₀.base) := ν₀.isClosedMap.isClosed_range
    have hdense : Dense (Set.range ν₀.base) := ν₀.denseRange
    have huniv : (Set.univ : Set L.subscheme) = {y} := by
      rw [← hrange, ← hcl.closure_eq, hdense.closure_eq]
    have : Subsingleton L.subscheme := ⟨fun a b => by
      have ha : a ∈ ({y} : Set L.subscheme) := huniv ▸ Set.mem_univ a
      have hb : b ∈ ({y} : Set L.subscheme) := huniv ▸ Set.mem_univ b
      rw [Set.mem_singleton_iff] at ha hb; rw [ha, hb]⟩
    have := topologicalKrullDim_zero_of_discreteTopology L.subscheme
    rw [hL.1.2] at this
    exact absurd this (by decide)
  have hdeg1 := AlgebraicGeometry.invertibleCurveDegree_pullback_eq_degreeOver_mul K
    (projectiveLine K ↘ Spec (.of K)) (L.subschemeι ≫ sZ) ν₀ hν₀' hncν₀ NL
  rw [degreeOver_eq_one_of_isBirationalMorphism' ν₀ hbir, Nat.cast_one, one_mul] at hdeg1
  -- the Picard group of `ℙ¹`
  have hMinv : Stacks.Ample.IsInvertibleModule _ M :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback g₀ _
  obtain ⟨m, ⟨γ⟩⟩ := Stacks.PicardUFD.exists_iso_twistingSheaf K M inferInstance
  have hd1 : topologicalKrullDim (projectiveLine K) ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := K) (f := projectiveLine K ↘ Spec (.of K))).le
  have hdP : topologicalKrullDim (AlgebraicGeometry.Proj (polyGrading K 1)) ≤ 1 := by
    rw [← (IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (projectiveLineIsoProj K)).isHomeomorph)]
    exact hd1
  let tI := projectiveSpaceOver.toIntegralAtUniverse N (Spec (.of K))
  let eM : M ≅ (Scheme.Modules.pullback θ.inv).obj ((Scheme.Modules.pullback ν₀).obj NL) :=
    (Scheme.Modules.pullbackCongr (show g₀ = θ.inv ≫ (ν₀ ≫ (L.subschemeι ≫ (ι ≫ tI))) by
        simp [g₀, φ', tI])).app _ ≪≫
      ((Scheme.Modules.pullbackComp θ.inv (ν₀ ≫ (L.subschemeι ≫ (ι ≫ tI)))).app _).symm ≪≫
      (Scheme.Modules.pullback θ.inv).mapIso
        (((Scheme.Modules.pullbackComp ν₀ (L.subschemeι ≫ (ι ≫ tI))).app _).symm ≪≫
          (Scheme.Modules.pullback ν₀).mapIso
            (((Scheme.Modules.pullbackComp L.subschemeι (ι ≫ tI)).app _).symm ≪≫
              (Scheme.Modules.pullback L.subschemeι).mapIso
                ((Scheme.Modules.pullbackComp ι tI).app _).symm))
  have hπθ : π = θ.inv ≫ (projectiveLine K ↘ Spec (.of K)) := by
    rw [← hθ, Iso.inv_hom_id_assoc]
  have hdegM : invertibleCurveDegree K π hdP M =
      invertibleCurveDegree K (L.subschemeι ≫ sZ) hL.1.2.le NL := by
    rw [invertibleCurveDegree_eq_of_iso K π hdP eM, invertibleCurveDegree_congr_hom hπθ hdP,
      invertibleCurveDegree_pullback_of_isIso θ.inv _ hdP hd1, hdeg1]
  have hdegm : invertibleCurveDegree K π hdP M = m := by
    rw [invertibleCurveDegree_eq_of_iso K π hdP γ]
    exact invertibleCurveDegree_twistingSheaf_projectiveLineProj K m
  have hmd : m = invertibleCurveDegree K (L.subschemeι ≫ sZ) hL.1.2.le NL :=
    hdegm.symm.trans hdegM
  have hpos' : 0 < invertibleCurveDegree K (L.subschemeι ≫ sZ) hL.1.2.le NL := hpos
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, m = e := ⟨m.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have he : 0 < e := by omega
  -- the forms
  let σ := Stacks.TwistPullbackPinned.pullbackCoordSection g₀
  choose a ha using fun k => Stacks.ProjectiveSpace.Cohomology.exists_degreeSection_eq (A := K) 1 e
    (γ.hom.app ⊤ (σ k))
  set H : Fin (N + 1) → MvPolynomial (Fin 2) K := fun k => (a k : MvPolynomial (Fin 2) K)
    with hHdef
  have hH : ∀ k, H k ∈ polyGrading K 1 e := fun k => (a k).2
  set s' : Fin (N + 1) → Γ(twistO (polyGrading K 1) (e : ℤ), ⊤) :=
    fun k => degSec (polyGrading K 1) e (H k) (hH k) with hs'def
  have hs'σ : ∀ k, γ.hom.app ⊤ (σ k) = s' k := fun k => (ha k).symm
  have hs' : GeneratesStalks s' := by
    rw [Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem]
    intro x
    obtain ⟨k, hk⟩ := (Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem σ).mp
      hσ x
    refine ⟨k, ?_⟩
    change x ∈ Stacks.Ample.nonvanishingLocus _ (s' k)
    rw [← hs'σ k, Stacks.CokernelSupport.nonvanishingLocus_iso_app γ (σ k)]
    exact hk
  have hφ' : φ' = toProjectiveSpaceOver s' hs' π := by
    refine pullback.hom_ext ?_ ?_
    · rw [hφ'fst, toProjectiveSpaceOver_fst]
    · change g₀ = toProjectiveSpaceOver s' hs' π ≫ projectiveSpaceOver.toIntegralAtUniverse N _
      rw [toProjectiveSpaceOver_snd]
      exact MMP.Fourfold.eq_toProjectiveSpaceAtUniverse_of_pinned s' g₀ γ.hom hs'σ hs'
  have hfac : ∃ g : AlgebraicGeometry.Proj (polyGrading K 1) ⟶ L.subscheme,
      g ≫ (L.subschemeι ≫ ι) = toProjectiveSpaceOver s' hs' π :=
    ⟨θ.inv ≫ ν₀, by rw [← hφ']; simp [φ']⟩
  have hchart := (MMP.Fourfold.exists_lift_closedImmersion_iff s' π (L.subschemeι ≫ ι) hs').mp
    hfac
  obtain ⟨j, hj⟩ : ∃ j, H j ≠ 0 := by
    obtain ⟨x⟩ : Nonempty (AlgebraicGeometry.Proj (polyGrading K 1)) :=
      ⟨θ.hom.base (Classical.arbitrary _)⟩
    obtain ⟨k, hk⟩ := (Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem s').mp
      hs' x
    refine ⟨k, fun h0 => ?_⟩
    have : x ∈ AlgebraicGeometry.Proj.basicOpen (polyGrading K 1) (H k) := by
      rw [← nvOpen_degSec]; exact hk
    rw [AlgebraicGeometry.Proj.mem_basicOpen, h0] at this
    exact this (zero_mem _)
  have hGH : ∀ l, MvPolynomial.aeval H (G l) = 0 := fun l => by
    obtain ⟨d, hd⟩ := hG l
    exact aeval_eq_zero_of_chartEval_eq_zero H hH he hj hd (hchart j _ (hmem l))
  -- the dehomogenised forms
  have hHhom : ∀ k, (H k).IsHomogeneous e := fun k =>
    (MvPolynomial.mem_homogeneousSubmodule _ _).1 (hH k)
  set f : Fin (N + 1) → K[X] := fun k => MvPolynomial.aeval ![(Polynomial.X : K[X]), 1] (H k)
    with hfdef
  have hfH : ∀ k, (f k).homogenize e = H k := fun k =>
    Polynomial.homogenize_eq_of_isHomogeneous (hHhom k) rfl
  have hd' : MMP.Mori.degreeOn K sZ L.subschemeι hL.1.2.le ((Scheme.Modules.pullback ι).obj O) =
      (e : ℤ) := hmd.symm
  refine ⟨e, by rw [hd']; simp, f, fun k => natDegree_aeval_X_one_le (hHhom k), fun l => ?_, ?_⟩
  · have := congrArg (MvPolynomial.aeval ![(Polynomial.X : K[X]), 1]) (hGH l)
    rw [MvPolynomial.comp_aeval_apply, map_zero] at this
    exact this
  · by_contra hmin
    push Not at hmin
    have hfj : f j ≠ 0 := fun h0 => hj (by rw [← hfH j, h0, Polynomial.homogenize_zero])
    obtain ⟨v, hv, hvH⟩ := exists_eval_eq_zero_of_isHomogeneous he (hHhom j)
    obtain ⟨x, hx⟩ := exists_projPoint hv
    obtain ⟨k, hk⟩ := (Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem s').mp
      hs' x
    have hxk : x ∈ AlgebraicGeometry.Proj.basicOpen (polyGrading K 1) (H k) := by
      rw [← nvOpen_degSec]; exact hk
    obtain ⟨c, hc⟩ := exists_eq_C_mul_of_minor_eq_zero f hmin hfj k
    have hHk : H k = MvPolynomial.C c * H j := by
      rw [← hfH k, ← hfH j, hc, Polynomial.homogenize_C_mul]
    refine absurd (hx (H k) e (hHhom k) ?_) hxk
    rw [hHk, map_mul, hvH, mul_zero]

/-! ### Spreading out -/

section SpreadingOut

open CategoryTheory.Limits Topology

/-! ### Families `C ⊆ U ⊆ V ⊆ ℙᴺ_S` and their base change -/

/-- A closed subscheme `V ⊆ ℙᴺ_S`, an open `U ⊆ V` and a closed `C ⊆ U` proper over `S`. -/
private structure EmbeddedFamily (N : ℕ) (S : Scheme.{0}) where
  V : Scheme.{0}
  U : Scheme.{0}
  C : Scheme.{0}
  sV : V ⟶ S
  iU : U ⟶ V
  iC : C ⟶ U
  j : V ⟶ projectiveSpaceOver N S
  isOpenImmersion_iU : IsOpenImmersion iU
  isClosedImmersion_iC : IsClosedImmersion iC
  isClosedImmersion_j : IsClosedImmersion j
  isProper_C : IsProper (iC ≫ iU ≫ sV)
  j_fst : j ≫ pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{0} N)) = sV

namespace EmbeddedFamily

variable {N : ℕ} {S S' : Scheme.{0}} (F : EmbeddedFamily N S) (t : S' ⟶ S)

/-- The base change of a family along `t : S' ⟶ S`. -/
private noncomputable def baseChange : EmbeddedFamily N S' where
  V := pullback F.sV t
  U := pullback (F.iU ≫ F.sV) t
  C := pullback (F.iC ≫ F.iU ≫ F.sV) t
  sV := pullback.snd _ _
  iU := pullback.map _ _ _ _ F.iU (𝟙 _) (𝟙 _) (by simp) (by simp)
  iC := pullback.map _ _ _ _ F.iC (𝟙 _) (𝟙 _) (by simp) (by simp)
  j := pullback.lift (pullback.snd _ _)
    (pullback.fst _ _ ≫ F.j ≫ projectiveSpaceOver.toIntegralAtUniverse N _)
    (terminal.hom_ext _ _)
  isOpenImmersion_iU := by
    have := F.isOpenImmersion_iU
    have sq : IsPullback (pullback.fst (F.iU ≫ F.sV) t)
        (pullback.map _ _ _ _ F.iU (𝟙 _) (𝟙 _) (by simp) (by simp))
        F.iU (pullback.fst F.sV t) := by
      refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback F.sV t)
      simpa using IsPullback.of_hasPullback (F.iU ≫ F.sV) t
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq ‹_›
  isClosedImmersion_iC := by
    have := F.isClosedImmersion_iC
    have sq : IsPullback (pullback.fst (F.iC ≫ F.iU ≫ F.sV) t)
        (pullback.map _ _ _ _ F.iC (𝟙 _) (𝟙 _) (by simp) (by simp))
        F.iC (pullback.fst (F.iU ≫ F.sV) t) := by
      refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback (F.iU ≫ F.sV) t)
      simpa using IsPullback.of_hasPullback (F.iC ≫ F.iU ≫ F.sV) t
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq ‹_›
  isClosedImmersion_j := by
    have := F.isClosedImmersion_j
    have sq : IsPullback (pullback.fst F.sV t)
        (pullback.lift (pullback.snd _ _)
          (pullback.fst _ _ ≫ F.j ≫ projectiveSpaceOver.toIntegralAtUniverse N _)
          (terminal.hom_ext _ _)) F.j (projectiveSpaceOverMap N t) := by
      refine IsPullback.of_bot ?_ ?_ (isPullback_projectiveSpaceOverMap N t)
      · rw [pullback.lift_fst, F.j_fst]
        exact IsPullback.of_hasPullback F.sV t
      · refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, Category.assoc, projectiveSpaceOverMap_fst,
            ← Category.assoc (pullback.lift _ _ _), pullback.lift_fst, F.j_fst,
            pullback.condition]
        · rw [Category.assoc, Category.assoc, projectiveSpaceOverMap_snd, pullback.lift_snd]
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq ‹_›
  isProper_C := by
    have := F.isProper_C
    rw [show pullback.map _ _ _ _ F.iC (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      pullback.map _ _ _ _ F.iU (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.snd _ _ =
      pullback.snd (F.iC ≫ F.iU ≫ F.sV) t by simp]
    infer_instance
  j_fst := pullback.lift_fst _ _ _

/-- The projection of the base change of `V` to `V`. -/
private noncomputable abbrev qV : (F.baseChange t).V ⟶ F.V := pullback.fst F.sV t
/-- The projection of the base change of `U` to `U`. -/
private noncomputable abbrev qU : (F.baseChange t).U ⟶ F.U := pullback.fst (F.iU ≫ F.sV) t
/-- The projection of the base change of `C` to `C`. -/
private noncomputable abbrev qC : (F.baseChange t).C ⟶ F.C := pullback.fst (F.iC ≫ F.iU ≫ F.sV) t

/-- The base change of `V` is a pullback. -/
private theorem isPullback_qV : IsPullback (F.qV t) (F.baseChange t).sV F.sV t :=
  IsPullback.of_hasPullback _ _

/-- The base change of `U` is a pullback. -/
private theorem isPullback_qU : IsPullback (F.qU t) ((F.baseChange t).iU ≫ (F.baseChange t).sV)
    (F.iU ≫ F.sV) t := by
  rw [show (F.baseChange t).iU ≫ (F.baseChange t).sV = pullback.snd (F.iU ≫ F.sV) t by
    simp [baseChange]]
  exact IsPullback.of_hasPullback _ _

/-- The base change of `C` is a pullback. -/
private theorem isPullback_qC : IsPullback (F.qC t)
    ((F.baseChange t).iC ≫ (F.baseChange t).iU ≫ (F.baseChange t).sV)
    (F.iC ≫ F.iU ≫ F.sV) t := by
  rw [show (F.baseChange t).iC ≫ (F.baseChange t).iU ≫ (F.baseChange t).sV =
    pullback.snd (F.iC ≫ F.iU ≫ F.sV) t by simp [baseChange]]
  exact IsPullback.of_hasPullback _ _

/-- The projections commute with the open immersion of `U`. -/
private theorem qU_iU : F.qU t ≫ F.iU = (F.baseChange t).iU ≫ F.qV t := by
  simp [baseChange]

/-- The projections commute with the closed immersion of `C`. -/
private theorem qC_iC : F.qC t ≫ F.iC = (F.baseChange t).iC ≫ F.qU t := by
  simp [baseChange]

/-- The embedding of the base change is the base change of the embedding. -/
private theorem j_baseChange : (F.baseChange t).j ≫ projectiveSpaceOverMap N t = F.qV t ≫ F.j := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, projectiveSpaceOverMap_fst, ← Category.assoc, (F.baseChange t).j_fst,
      Category.assoc, F.j_fst]
    exact (pullback.condition).symm
  · rw [Category.assoc, projectiveSpaceOverMap_snd]
    exact pullback.lift_snd _ _ _

/-- The structure morphism of the base change of `U`. -/
private theorem iU_sV_baseChange :
    (F.baseChange t).iU ≫ (F.baseChange t).sV = pullback.snd (F.iU ≫ F.sV) t := by
  simp [baseChange]

/-- The structure morphism of the base change of `C`. -/
private theorem iC_iU_sV_baseChange :
    (F.baseChange t).iC ≫ (F.baseChange t).iU ≫ (F.baseChange t).sV =
    pullback.snd (F.iC ≫ F.iU ≫ F.sV) t := by
  simp [baseChange]

/-- A map into the base change of `V`. -/
private noncomputable def liftV {W : Scheme.{0}} (a : W ⟶ F.V) (b : W ⟶ S') (h : a ≫ F.sV = b ≫ t) :
    W ⟶ (F.baseChange t).V := pullback.lift a b h

/-- A map into the base change of `U`. -/
private noncomputable def liftU {W : Scheme.{0}} (a : W ⟶ F.U) (b : W ⟶ S')
    (h : a ≫ F.iU ≫ F.sV = b ≫ t) : W ⟶ (F.baseChange t).U := pullback.lift a b h

/-- A map into the base change of `C`. -/
private noncomputable def liftC {W : Scheme.{0}} (a : W ⟶ F.C) (b : W ⟶ S')
    (h : a ≫ F.iC ≫ F.iU ≫ F.sV = b ≫ t) : W ⟶ (F.baseChange t).C := pullback.lift a b h

variable {F t}

/-- The projection of `liftV`. -/
private theorem liftV_qV {W : Scheme.{0}} (a : W ⟶ F.V) (b : W ⟶ S') (h) :
    F.liftV t a b h ≫ F.qV t = a := pullback.lift_fst _ _ _
/-- The structure morphism of `liftV`. -/
private theorem liftV_sV {W : Scheme.{0}} (a : W ⟶ F.V) (b : W ⟶ S') (h) :
    F.liftV t a b h ≫ (F.baseChange t).sV = b := pullback.lift_snd _ _ _
/-- The projection of `liftU`. -/
private theorem liftU_qU {W : Scheme.{0}} (a : W ⟶ F.U) (b : W ⟶ S') (h) :
    F.liftU t a b h ≫ F.qU t = a := pullback.lift_fst _ _ _
/-- The structure morphism of `liftU`. -/
private theorem liftU_sV {W : Scheme.{0}} (a : W ⟶ F.U) (b : W ⟶ S') (h) :
    F.liftU t a b h ≫ (F.baseChange t).iU ≫ (F.baseChange t).sV = b := by
  rw [iU_sV_baseChange]; exact pullback.lift_snd _ _ _
/-- The projection of `liftC`. -/
private theorem liftC_qC {W : Scheme.{0}} (a : W ⟶ F.C) (b : W ⟶ S') (h) :
    F.liftC t a b h ≫ F.qC t = a := pullback.lift_fst _ _ _
/-- The structure morphism of `liftC`. -/
private theorem liftC_sV {W : Scheme.{0}} (a : W ⟶ F.C) (b : W ⟶ S') (h) :
    F.liftC t a b h ≫ (F.baseChange t).iC ≫ (F.baseChange t).iU ≫ (F.baseChange t).sV = b := by
  rw [iC_iU_sV_baseChange]; exact pullback.lift_snd _ _ _

/-- Maps into the base change of `V` are determined by their two components. -/
private theorem homV_ext {W : Scheme.{0}} {g g' : W ⟶ (F.baseChange t).V}
    (h₁ : g ≫ F.qV t = g' ≫ F.qV t)
    (h₂ : g ≫ (F.baseChange t).sV = g' ≫ (F.baseChange t).sV) : g = g' :=
  pullback.hom_ext h₁ h₂

/-- Maps into the base change of `U` are determined by their two components. -/
private theorem homU_ext {W : Scheme.{0}} {g g' : W ⟶ (F.baseChange t).U}
    (h₁ : g ≫ F.qU t = g' ≫ F.qU t)
    (h₂ : g ≫ (F.baseChange t).iU ≫ (F.baseChange t).sV =
      g' ≫ (F.baseChange t).iU ≫ (F.baseChange t).sV) : g = g' := by
  rw [iU_sV_baseChange] at h₂; exact pullback.hom_ext h₁ h₂

/-- The base change of the embedding, followed by the projection to the integral model. -/
private theorem j_toIntegral_baseChange :
    (F.baseChange t).j ≫ projectiveSpaceOver.toIntegralAtUniverse N _ =
    F.qV t ≫ F.j ≫ projectiveSpaceOver.toIntegralAtUniverse N _ := pullback.lift_snd _ _ _

end EmbeddedFamily

attribute [local simp] EmbeddedFamily.liftV_qV EmbeddedFamily.liftV_sV EmbeddedFamily.liftU_qU
  EmbeddedFamily.liftU_sV EmbeddedFamily.liftC_qC EmbeddedFamily.liftC_sV

/-- The curve of a family is projective over the base, through the embedding of `V`. -/
private theorem EmbeddedFamily.isProjectiveMorphism_C {N : ℕ} {S : Scheme.{0}}
    (F : EmbeddedFamily N S) : IsProjectiveMorphism (F.iC ≫ F.iU ≫ F.sV) := by
  have := F.isOpenImmersion_iU
  have := F.isClosedImmersion_iC
  have := F.isClosedImmersion_j
  have : IsProper ((F.iC ≫ F.iU) ≫ F.sV) := by rw [Category.assoc]; exact F.isProper_C
  have : IsSeparated F.sV := by rw [← F.j_fst]; infer_instance
  have : IsProper (F.iC ≫ F.iU) := IsProper.of_comp _ F.sV
  have : IsClosedImmersion (F.iC ≫ F.iU) :=
    IsClosedImmersion.of_isPreimmersion _ (F.iC ≫ F.iU).isClosedMap.isClosed_range
  have : IsClosedImmersion (F.iC ≫ F.iU ≫ F.j) := by rw [← Category.assoc]; infer_instance
  exact ⟨N, F.iC ≫ F.iU ≫ F.j, inferInstance, by
    rw [Category.assoc, Category.assoc]; exact congrArg (F.iC ≫ F.iU ≫ ·) F.j_fst⟩

/-- Over a Noetherian ring the schemes of a family are Noetherian. -/
private theorem EmbeddedFamily.isNoetherian {N : ℕ} {R : Type} [CommRing R] [IsNoetherianRing R]
    (F : EmbeddedFamily N (Spec (.of R))) :
    IsNoetherian F.V ∧ IsNoetherian F.U ∧ IsNoetherian F.C ∧ QuasiCompact (F.iU ≫ F.sV) ∧
      QuasiCompact F.sV := by
  have := F.isOpenImmersion_iU
  have := F.isClosedImmersion_iC
  have := F.isClosedImmersion_j
  have := F.isProper_C
  have : LocallyOfFiniteType F.sV := by rw [← F.j_fst]; infer_instance
  have : QuasiCompact F.sV := by rw [← F.j_fst]; infer_instance
  have : IsLocallyNoetherian F.V := LocallyOfFiniteType.isLocallyNoetherian F.sV
  have : CompactSpace F.V := QuasiCompact.compactSpace_of_compactSpace F.sV
  have : IsNoetherian F.V := ⟨⟩
  have : IsLocallyNoetherian F.U := LocallyOfFiniteType.isLocallyNoetherian (F.iU ≫ F.sV)
  have : CompactSpace F.U := QuasiCompact.compactSpace_of_compactSpace F.iU
  have : IsNoetherian F.U := ⟨⟩
  have : IsLocallyNoetherian F.C := LocallyOfFiniteType.isLocallyNoetherian (F.iC ≫ F.iU ≫ F.sV)
  have : CompactSpace F.C := QuasiCompact.compactSpace_of_compactSpace F.iC
  exact ⟨inferInstance, inferInstance, ⟨⟩, inferInstance, inferInstance⟩

/-! ### Models over finitely generated subrings of `ℂ` -/

/-- **A model of `C ⊆ U ⊆ V ⊆ ℙᴺ_ℂ` over a subring `R ⊆ ℂ`.** -/
private structure Model {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) (U : V.Opens) {C : Scheme.{0}}
    (i : C ⟶ U.toScheme) {N : ℕ} (j : V ⟶ projectiveSpaceOver N (Spec (.of ℂ)))
    (R : Subalgebra ℤ ℂ) where
  F : EmbeddedFamily N (Spec (.of R))
  pV : V ⟶ F.V
  pU : U.toScheme ⟶ F.U
  pC : C ⟶ F.C
  isPullback_V : IsPullback pV sV F.sV (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))
  isPullback_U : IsPullback pU (U.ι ≫ sV) (F.iU ≫ F.sV)
    (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))
  isPullback_C : IsPullback pC (i ≫ U.ι ≫ sV) (F.iC ≫ F.iU ≫ F.sV)
    (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))
  pU_iU : pU ≫ F.iU = U.ι ≫ pV
  pC_iC : pC ≫ F.iC = i ≫ pU
  pV_j : pV ≫ F.j ≫ projectiveSpaceOver.toIntegralAtUniverse N _ =
    j ≫ projectiveSpaceOver.toIntegralAtUniverse N _

/-- **A model of `C ⊆ U ⊆ V ⊆ ℙᴺ_ℂ` exists over a finitely generated subring of `ℂ`.** -/
private theorem exists_model {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) (U : V.Opens) {C : Scheme.{0}}
    (i : C ⟶ U.toScheme) [IsClosedImmersion i] [IsClosedImmersion (i ≫ U.ι)] {N : ℕ}
    (j : V ⟶ projectiveSpaceOver N (Spec (.of ℂ))) [IsClosedImmersion j]
    (hj : j ≫ pullback.fst (terminal.from (Spec (.of ℂ)))
      (terminal.from (projectiveSpaceAtUniverse.{0} N)) = sV) :
    ∃ R : Subalgebra ℤ ℂ, R.FG ∧ Nonempty (Model sV U i j R) := by
  classical
  let X : ComposableArrows (Over (Spec (.of ℂ))) 2 :=
    ComposableArrows.mk₂ (Over.homMk i : Over.mk (i ≫ U.ι ≫ sV) ⟶ Over.mk (U.ι ≫ sV))
      (Over.homMk U.ι : Over.mk (U.ι ≫ sV) ⟶ Over.mk sV)
  have h02 : (0 : Fin 3) ≤ 2 := by decide
  have h12 : (1 : Fin 3) ≤ 2 := by decide
  have h01 : (0 : Fin 3) ≤ 1 := by decide
  let ι : ∀ k : Fin 3, (X.obj k).left ⟶ projectiveSpaceOver N (Spec (.of ℂ)) :=
    fun k => (X.map (homOfLE (Fin.le_last k))).left ≫ j
  have hι : ∀ k, IsImmersion (ι k) := by
    intro k
    fin_cases k
    · change IsImmersion ((i ≫ U.ι) ≫ j); infer_instance
    · change IsImmersion (U.ι ≫ j); infer_instance
    · change IsImmersion (𝟙 V ≫ j); infer_instance
  have hιover : ∀ k, ι k ≫ (projectiveSpaceOver N (Spec (.of ℂ)) ↘ Spec (.of ℂ)) =
      (X.obj k).hom := by
    intro k
    rw [Category.assoc]
    change (X.map (homOfLE (Fin.le_last k))).left ≫ (j ≫ pullback.fst _ _) = _
    rw [hj]
    exact Over.w (X.map (homOfLE (Fin.le_last k)))
  obtain ⟨R, hR, Y, ιY, p, hp, -, -, -, -, hover, hpb, hcompat, hcl, hop, hclm, -⟩ :=
    MMP.exists_fg_subalgebra_model_of_finCategory ℤ ℂ X N ι hι hιover
      (Functor.empty (Fin 3)) (fun e => PEmpty.elim e.as) (fun e => PEmpty.elim e.as)
      (fun {e} => PEmpty.elim e.as) (fun e => PEmpty.elim e.as)
      (fun {e} => PEmpty.elim e.as)
  have hC : IsProper (Y.obj 0).hom := by
    have := hcl 0 (by change IsClosedImmersion ((i ≫ U.ι) ≫ j); infer_instance)
    rw [← hover 0]
    infer_instance
  refine ⟨R, hR, ⟨{
    F := {
      V := (Y.obj 2).left
      U := (Y.obj 1).left
      C := (Y.obj 0).left
      sV := (Y.obj 2).hom
      iU := (Y.map (homOfLE h12)).left
      iC := (Y.map (homOfLE h01)).left
      j := ιY 2
      isOpenImmersion_iU := hop (homOfLE h12) (by change IsOpenImmersion U.ι; infer_instance)
      isClosedImmersion_iC := hclm (homOfLE h01) (by change IsClosedImmersion i; infer_instance)
      isClosedImmersion_j := hcl 2 (by change IsClosedImmersion (𝟙 V ≫ j); infer_instance)
      isProper_C := by
        rwa [← Over.w (Y.map (homOfLE h01)), ← Over.w (Y.map (homOfLE h12))] at hC
      j_fst := hover 2 }
    pV := p 2
    pU := p 1
    pC := p 0
    isPullback_V := hpb 2
    isPullback_U := by
      have := hpb 1
      rwa [← Over.w (Y.map (homOfLE h12))] at this
    isPullback_C := by
      have := hpb 0
      rwa [← Over.w (Y.map (homOfLE h01)), ← Over.w (Y.map (homOfLE h12))] at this
    pU_iU := (hp (homOfLE h12)).symm
    pC_iC := (hp (homOfLE h01)).symm
    pV_j := by
      have := hcompat 2
      change (𝟙 V ≫ j) ≫ _ = _ at this
      rw [Category.id_comp] at this
      exact this.symm }⟩⟩

section BaseChange

variable {V : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)} {U : V.Opens} {C : Scheme.{0}}
  {i : C ⟶ U.toScheme} {N : ℕ} {j : V ⟶ projectiveSpaceOver N (Spec (.of ℂ))}

/-- The map `Spec R' ⟶ Spec R` of an inclusion of subrings of `ℂ`. -/
private noncomputable abbrev specIncl {R R' : Subalgebra ℤ ℂ} (h : R ≤ R') :
    Spec (.of R') ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

/-- The map of spectra of an inclusion is compatible with the maps from `Spec ℂ`. -/
private theorem specIncl_comm {R R' : Subalgebra ℤ ℂ} (h : R ≤ R') :
    Spec.map (CommRingCat.ofHom (algebraMap R' ℂ)) ≫ specIncl h =
      Spec.map (CommRingCat.ofHom (algebraMap R ℂ)) := by
  rw [← Spec.map_comp]; rfl

/-- **Base change of a model along an inclusion `R ≤ R'`.** -/
private noncomputable def Model.baseChange {R R' : Subalgebra ℤ ℂ} (M : Model sV U i j R)
    (h : R ≤ R') : Model sV U i j R' where
  F := M.F.baseChange (specIncl h)
  pV := M.F.liftV (specIncl h) M.pV (sV ≫ Spec.map (CommRingCat.ofHom (algebraMap R' ℂ)))
    (by rw [Category.assoc, specIncl_comm, M.isPullback_V.w])
  pU := M.F.liftU (specIncl h) M.pU (U.ι ≫ sV ≫ Spec.map (CommRingCat.ofHom (algebraMap R' ℂ)))
    (by simp only [Category.assoc, specIncl_comm]; simpa only [Category.assoc] using
      M.isPullback_U.w)
  pC := M.F.liftC (specIncl h) M.pC
    (i ≫ U.ι ≫ sV ≫ Spec.map (CommRingCat.ofHom (algebraMap R' ℂ)))
    (by simp only [Category.assoc, specIncl_comm]; simpa only [Category.assoc] using
      M.isPullback_C.w)
  isPullback_V := by
    refine IsPullback.of_right ?_ (EmbeddedFamily.liftV_sV _ _ _) (M.F.isPullback_qV (specIncl h))
    rw [EmbeddedFamily.liftV_qV, specIncl_comm]
    exact M.isPullback_V
  isPullback_U := by
    refine IsPullback.of_right ?_ (by simp) (M.F.isPullback_qU (specIncl h))
    rw [EmbeddedFamily.liftU_qU, specIncl_comm]
    exact M.isPullback_U
  isPullback_C := by
    refine IsPullback.of_right ?_ (by simp) (M.F.isPullback_qC (specIncl h))
    rw [EmbeddedFamily.liftC_qC, specIncl_comm]
    exact M.isPullback_C
  pU_iU := by
    refine EmbeddedFamily.homV_ext ?_ ?_
    · rw [Category.assoc, ← EmbeddedFamily.qU_iU, ← Category.assoc, EmbeddedFamily.liftU_qU,
        Category.assoc, EmbeddedFamily.liftV_qV, M.pU_iU]
    · rw [Category.assoc, EmbeddedFamily.liftU_sV, Category.assoc, EmbeddedFamily.liftV_sV]
  pC_iC := by
    refine EmbeddedFamily.homU_ext ?_ ?_
    · rw [Category.assoc, ← EmbeddedFamily.qC_iC, ← Category.assoc, EmbeddedFamily.liftC_qC,
        Category.assoc, EmbeddedFamily.liftU_qU, M.pC_iC]
    · rw [Category.assoc, EmbeddedFamily.liftC_sV, Category.assoc, EmbeddedFamily.liftU_sV]
  pV_j := by
    rw [EmbeddedFamily.j_toIntegral_baseChange, ← Category.assoc, EmbeddedFamily.liftV_qV]
    exact M.pV_j

end BaseChange

section Descent

open MMP.CoefficientModels

/-- **Smoothness descends to a finitely generated stage.** -/
private theorem exists_smooth_of_isPullback {R : Subalgebra ℤ ℂ} (hR : R.FG) {X₀ : Scheme.{0}}
    (f : X₀ ⟶ Spec (.of R)) [LocallyOfFinitePresentation f] [CompactSpace X₀]
    [QuasiSeparatedSpace X₀] {Xc : Scheme.{0}} (q : Xc ⟶ X₀) (fc : Xc ⟶ Spec (.of ℂ)) [Smooth fc]
    (hpb : IsPullback q fc f (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) :
    ∃ (R' : Subalgebra ℤ ℂ) (h : R ≤ R'), R'.FG ∧ Smooth (pullback.snd f (specIncl h)) := by
  classical
  let D := specDiagram ℤ ℂ
  let c := specCone ℤ ℂ
  have hc : IsLimit c := isLimitSpecCone ℤ ℂ
  let i₀ : (FGSub ℤ ℂ)ᵒᵖ := Opposite.op ⟨R, hR⟩
  have : MorphismProperty.RespectsIso (@Smooth.{0}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let X₀' : Over (D.obj i₀) := Over.mk f
  let Y₀ : Over (D.obj i₀) := Over.mk (𝟙 (D.obj i₀))
  let a : X₀' ⟶ Y₀ := Over.homMk f (Category.comp_id f)
  have : CompactSpace X₀'.left := inferInstanceAs (CompactSpace X₀)
  have : QuasiSeparatedSpace X₀'.left := inferInstanceAs (QuasiSeparatedSpace X₀)
  have : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj i₀))
  have : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i₀))
  have : LocallyOfFinitePresentation a.left := inferInstanceAs (LocallyOfFinitePresentation f)
  have hsm : Smooth ((Over.pullback (c.π.app i₀)).map a).left := by
    refine (smooth_overPullback_map_left_iff a (c.π.app i₀)).mpr ?_
    change Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
    rw [← MorphismProperty.cancel_left_of_respectsIso (@Smooth.{0}) hpb.isoPullback.hom,
      hpb.isoPullback_hom_snd]
    infer_instance
  obtain ⟨j, g, hj⟩ := exists_smooth_baseChange_of_smooth_limitBaseChange D c i₀ X₀' Y₀ a hc
  exact ⟨j.unop.1, leOfHom g.unop, j.unop.2, (smooth_overPullback_map_left_iff a (D.map g)).mp hj⟩

/-- Smoothness after base change to a stage persists at every later stage. -/
private theorem smooth_pullback_snd_of_le {R R₁ R₂ : Subalgebra ℤ ℂ} {X₀ : Scheme.{0}}
    (f : X₀ ⟶ Spec (.of R)) (h₁ : R ≤ R₁) (h₂ : R₁ ≤ R₂)
    (hs : Smooth (pullback.snd f (specIncl h₁))) :
    Smooth (pullback.snd f (specIncl (h₁.trans h₂))) := by
  have : MorphismProperty.RespectsIso (@Smooth.{0}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hcomp : specIncl (h₁.trans h₂) = specIncl h₂ ≫ specIncl h₁ := by
    rw [specIncl, specIncl, specIncl, ← Spec.map_comp]; rfl
  have sq : IsPullback (pullback.lift (pullback.fst f (specIncl (h₁.trans h₂)))
      (pullback.snd f (specIncl (h₁.trans h₂)) ≫ specIncl h₂)
      (by rw [pullback.condition, Category.assoc, hcomp]))
      (pullback.snd f (specIncl (h₁.trans h₂))) (pullback.snd f (specIncl h₁)) (specIncl h₂) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, ← hcomp]
    exact IsPullback.of_hasPullback _ _
  exact MorphismProperty.of_isPullback (P := @Smooth) sq hs

/-- A finitely generated subring of `ℂ` is Noetherian. -/
private theorem isNoetherianRing_of_fg {R : Subalgebra ℤ ℂ} (hR : R.FG) : IsNoetherianRing R := by
  have : Algebra.FiniteType ℤ R := (Subalgebra.fg_iff_finiteType R).mp hR
  exact Algebra.FiniteType.isNoetherianRing ℤ R

/-- **A smooth model containing given coefficients.** -/
private theorem exists_smooth_model {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) (U : V.Opens)
    {C : Scheme.{0}} (i : C ⟶ U.toScheme) [IsClosedImmersion i] [IsClosedImmersion (i ≫ U.ι)]
    [Smooth (U.ι ≫ sV)] [Smooth (i ≫ U.ι ≫ sV)] {N : ℕ}
    (j : V ⟶ projectiveSpaceOver N (Spec (.of ℂ))) [IsClosedImmersion j]
    (hj : j ≫ pullback.fst (terminal.from (Spec (.of ℂ)))
      (terminal.from (projectiveSpaceAtUniverse.{0} N)) = sV) (T : Finset ℂ) :
    ∃ R : Subalgebra ℤ ℂ, R.FG ∧ (T : Set ℂ) ⊆ R ∧ ∃ M : Model sV U i j R,
      Smooth (M.F.iU ≫ M.F.sV) ∧ Smooth (M.F.iC ≫ M.F.iU ≫ M.F.sV) := by
  classical
  obtain ⟨R₀, hR₀, ⟨M₀⟩⟩ := exists_model sV U i j hj
  have := isNoetherianRing_of_fg hR₀
  have := M₀.F.isOpenImmersion_iU
  have : LocallyOfFiniteType M₀.F.sV := by
    have := M₀.F.isClosedImmersion_j; rw [← M₀.F.j_fst]; infer_instance
  obtain ⟨-, hUn, hCn, -, -⟩ := M₀.F.isNoetherian
  have hUl := @IsNoetherian.toIsLocallyNoetherian _ hUn
  have hCl := @IsNoetherian.toIsLocallyNoetherian _ hCn
  haveI : CompactSpace M₀.F.U := @IsNoetherian.toCompactSpace _ hUn
  haveI : CompactSpace M₀.F.C := @IsNoetherian.toCompactSpace _ hCn
  haveI : QuasiSeparatedSpace M₀.F.U := @IsLocallyNoetherian.quasiSeparatedSpace _ hUl
  haveI : QuasiSeparatedSpace M₀.F.C := @IsLocallyNoetherian.quasiSeparatedSpace _ hCl
  haveI : IsLocallyNoetherian (Spec (.of R₀)) :=
    @IsNoetherian.toIsLocallyNoetherian _ inferInstance
  haveI : LocallyOfFiniteType (M₀.F.iU ≫ M₀.F.sV) := inferInstance
  haveI : LocallyOfFiniteType (M₀.F.iC ≫ M₀.F.iU ≫ M₀.F.sV) := by
    have := M₀.F.isClosedImmersion_iC; infer_instance
  haveI : LocallyOfFinitePresentation (M₀.F.iU ≫ M₀.F.sV) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  haveI : LocallyOfFinitePresentation (M₀.F.iC ≫ M₀.F.iU ≫ M₀.F.sV) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  obtain ⟨R₁, h₁, hR₁, hs₁⟩ := exists_smooth_of_isPullback hR₀ (M₀.F.iU ≫ M₀.F.sV) M₀.pU
    (U.ι ≫ sV) M₀.isPullback_U
  obtain ⟨R₂, h₂, hR₂, hs₂⟩ := exists_smooth_of_isPullback hR₀ (M₀.F.iC ≫ M₀.F.iU ≫ M₀.F.sV)
    M₀.pC (i ≫ U.ι ≫ sV) M₀.isPullback_C
  let R : Subalgebra ℤ ℂ := R₁ ⊔ R₂ ⊔ Algebra.adjoin ℤ (T : Set ℂ)
  have hR : R.FG := (hR₁.sup hR₂).sup (Subalgebra.fg_adjoin_finset T)
  have h₁' : R₁ ≤ R := le_sup_left.trans le_sup_left
  have h₂' : R₂ ≤ R := le_sup_right.trans le_sup_left
  refine ⟨R, hR, fun x hx => le_sup_right (α := Subalgebra ℤ ℂ) (Algebra.subset_adjoin hx),
    M₀.baseChange (h₁.trans h₁'), ?_, ?_⟩
  · change Smooth ((M₀.F.baseChange _).iU ≫ (M₀.F.baseChange _).sV)
    rw [EmbeddedFamily.iU_sV_baseChange]
    exact smooth_pullback_snd_of_le _ h₁ h₁' hs₁
  · change Smooth ((M₀.F.baseChange _).iC ≫ (M₀.F.baseChange _).iU ≫ (M₀.F.baseChange _).sV)
    rw [EmbeddedFamily.iC_iU_sV_baseChange]
    exact smooth_pullback_snd_of_le _ h₂ h₂' hs₂

end Descent

/-! ### Generic points -/

section Generic

open Topology

/-- The zero ideal lies in every nonempty open subset of the spectrum of a domain. -/
private theorem bot_mem_of_isOpen {R : Type*} [CommRing R] [IsDomain R] {O : Set (PrimeSpectrum R)}
    (hO : IsOpen O) (hne : O.Nonempty) : (⊥ : PrimeSpectrum R) ∈ O := by
  obtain ⟨x, hx⟩ := hne
  exact ((PrimeSpectrum.le_iff_specializes ⊥ x).mp bot_le).mem_open hO hx

/-- An open subset of a Noetherian space is constructible. -/
private theorem isConstructible_of_isOpen {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] {U : Set X} (hU : IsOpen U) : IsConstructible U :=
  IsRetrocompact.isConstructible hU fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _

/-- **Avoiding a constructible image.** If no point of a constructible `T ⊆ X` lies over the
generic point of `Spec R`, some nonempty open of `Spec R` receives no point of `T`. -/
private theorem exists_isOpen_forall_notMem {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation f] [QuasiCompact f] {T : Set X}
    (hT : IsConstructible T) (hη : ∀ x ∈ T, f.base x ≠ (⊥ : PrimeSpectrum R)) :
    ∃ O : Set (PrimeSpectrum R), IsOpen O ∧ O.Nonempty ∧ ∀ x ∈ T, f.base x ∉ O := by
  have hc : IsConstructible (f.base '' T) := f.isConstructible_image hT
  by_contra hcon
  push Not at hcon
  have : (⊥ : PrimeSpectrum R) ∈ f.base '' T := by
    refine mem_of_isConstructible (X := PrimeSpectrum R) ⊥
      (fun U hU hne => bot_mem_of_isOpen hU hne)
      hc fun U hU hne => ?_
    obtain ⟨x, hxT, hxU⟩ := hcon U hU hne
    exact ⟨_, hxU, x, hxT, rfl⟩
  obtain ⟨x, hxT, hx⟩ := this
  exact hη x hxT hx

/-- The point of `Spec K`, for a field `K` containing a domain `R`, lies over the zero ideal. -/
private theorem spec_algebraMap_apply_eq_bot {R K : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] (hinj : Function.Injective (algebraMap R K)) (x : Spec (.of K)) :
    (Spec.map (CommRingCat.ofHom (algebraMap R K))).base x = (⊥ : PrimeSpectrum R) := by
  refine PrimeSpectrum.ext (R := R) ?_
  change Ideal.comap (algebraMap R K) x.asIdeal = _
  have : x.asIdeal = ⊥ := @Ideal.eq_bot_of_prime K _ x.asIdeal (PrimeSpectrum.isPrime x)
  rw [PrimeSpectrum.asIdeal_bot, this, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).mp hinj]

/-- **Points over the generic point come from the generic geometric fibre.** -/
private theorem exists_preimage_of_isPullback {R K : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] (hinj : Function.Injective (algebraMap R K)) {X Xc : Scheme.{0}}
    {f : X ⟶ Spec (.of R)} {q : Xc ⟶ X} {fc : Xc ⟶ Spec (.of K)}
    (h : IsPullback q fc f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (x : X)
    (hx : f.base x = (⊥ : PrimeSpectrum R)) : ∃ x' : Xc, q.base x' = x := by
  obtain ⟨pt⟩ : Nonempty (Spec (.of K)) := inferInstance
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
    (g := Spec.map (CommRingCat.ofHom (algebraMap R K))) x pt
    (by rw [hx, spec_algebraMap_apply_eq_bot hinj])
  refine ⟨h.isoPullback.inv.base z, ?_⟩
  rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz]

end Generic

/-! ### Relative dimension -/

section RelDim

/-- Smoothness of relative dimension `n` is local on the source. -/
local instance (n : ℕ) : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} n) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} n)

/-- A smooth morphism is smooth of some relative dimension near every point. -/
private theorem exists_smoothOfRelativeDimension_nbhd {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f]
    (x : X) : ∃ V : X.Opens, x ∈ V ∧ ∃ n : ℕ, SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, hn⟩ : ∃ n, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n := by
    let := (f.appLE U V e).hom.toAlgebra
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.toAlgebra.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have hQi := (HasRingHomProperty.isLocal_ringHomProperty
    (@SmoothOfRelativeDimension n)).respectsIso
  have : (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hQi
  have h : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)))
      (arrowResLEAppIso f U V e)).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hn)
  refine ⟨V, hx, n, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]
  exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) _)

/-- A connected scheme smooth over a field is smooth of pure relative dimension. -/
private theorem exists_smoothOfRelativeDimension_of_connectedSpace {k : Type} [Field k]
    {X : Scheme.{0}} [ConnectedSpace X] (f : X ⟶ Spec (.of k)) [Smooth f] :
    ∃ d : ℕ, SmoothOfRelativeDimension d f := by
  obtain ⟨x₀⟩ := (ConnectedSpace.toNonempty : Nonempty X)
  choose V hxV n hn using exists_smoothOfRelativeDimension_nbhd f
  have key : ∀ x y, y ∈ V x → n y = n x := by
    intro x y hy
    let W : X.Opens := V x ⊓ V y
    have hyW : y ∈ W := ⟨hy, hxV y⟩
    have : Nonempty W := ⟨⟨y, hyW⟩⟩
    have h₁ : SmoothOfRelativeDimension (n x) (W.ι ≫ f) := by
      rw [← X.homOfLE_ι (inf_le_left : W ≤ V x), Category.assoc]
      exact IsZariskiLocalAtSource.comp (hn x) _
    have h₂ : SmoothOfRelativeDimension (n y) (W.ι ≫ f) := by
      rw [← X.homOfLE_ι (inf_le_right : W ≤ V y), Category.assoc]
      exact IsZariskiLocalAtSource.comp (hn y) _
    have e₁ := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field (n x) (W.ι ≫ f)
    have e₂ := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field (n y) (W.ι ≫ f)
    exact_mod_cast e₂.symm.trans e₁
  let S : Set X := {y | n y = n x₀}
  have hS : IsClopen S := by
    refine ⟨?_, ?_⟩
    · refine isOpen_compl_iff.1 (isOpen_iff_forall_mem_open.2 fun y hy => ?_)
      refine ⟨V y, fun z hz => ?_, (V y).2, hxV y⟩
      change n z ≠ n x₀
      rw [key y z hz]
      exact hy
    · refine isOpen_iff_forall_mem_open.2 fun y hy => ?_
      refine ⟨V y, fun z hz => ?_, (V y).2, hxV y⟩
      change n z = n x₀
      rw [key y z hz]
      exact hy
  have hall : ∀ y, n y = n x₀ := Set.eq_univ_iff_forall.1 (hS.eq_univ ⟨x₀, rfl⟩)
  exact ⟨n x₀, IsZariskiLocalAtSource.of_iSup_eq_top V
    (top_unique fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxV y⟩) fun i => hall i ▸ hn i⟩

/-- The points of `X` near which `f` is not smooth of relative dimension `n`. -/
private def badSet {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) : Set X :=
  {x | ¬ ∃ V : X.Opens, x ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f)}

/-- The bad set is closed. -/
private theorem isClosed_badSet {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) : IsClosed (badSet f n) := by
  refine isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr fun x hx => ?_)
  obtain ⟨V, hxV, hV⟩ := not_not.mp hx
  exact ⟨V, fun y hy => not_not.mpr ⟨V, hy, hV⟩, V.2, hxV⟩

/-- The base change of an open restriction. -/
private theorem isPullback_restrict {X Y X' Y' : Scheme.{0}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (h : IsPullback g' f' f g) (V : X.Opens) :
    IsPullback (g' ∣_ V) ((g' ⁻¹ᵁ V).ι ≫ f') (V.ι ≫ f) g :=
  (isPullback_morphismRestrict g' V).paste_vert h

/-- **Relative dimension on a fibre avoiding the bad set.** -/
private theorem smoothOfRelativeDimension_of_isPullback {X Y X' Y' : Scheme.{0}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (h : IsPullback g' f' f g) (n : ℕ)
    (hbad : ∀ x', g'.base x' ∉ badSet f n) : SmoothOfRelativeDimension n f' := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange n
  choose V hxV hV using fun x' => not_not.mp (hbad x')
  refine IsZariskiLocalAtSource.of_iSup_eq_top (fun x' => g' ⁻¹ᵁ V x')
    (top_unique fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxV y⟩) fun x' => ?_
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n)
    (isPullback_restrict h (V x')) (hV x')

/-- **The generic geometric fibre misses the bad set.** -/
private theorem notMem_badSet_of_isPullback {K : Type} [Field K] {X Y Xc : Scheme.{0}} {f : X ⟶ Y}
    [Smooth f] {g : Spec (.of K) ⟶ Y} {fc : Xc ⟶ Spec (.of K)} {q : Xc ⟶ X}
    (h : IsPullback q fc f g) (n : ℕ) [SmoothOfRelativeDimension n fc] (x' : Xc) :
    q.base x' ∉ badSet f n := by
  obtain ⟨V, hxV, m, hm⟩ := exists_smoothOfRelativeDimension_nbhd f (q.base x')
  refine not_not.mpr ⟨V, hxV, ?_⟩
  have := smoothOfRelativeDimension_isStableUnderBaseChange m
  have h₁ : SmoothOfRelativeDimension m ((q ⁻¹ᵁ V).ι ≫ fc) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension m) (isPullback_restrict h V) hm
  have h₂ : SmoothOfRelativeDimension n ((q ⁻¹ᵁ V).ι ≫ fc) := IsZariskiLocalAtSource.comp ‹_› _
  have : Nonempty (q ⁻¹ᵁ V) := ⟨⟨x', hxV⟩⟩
  have e₁ := AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field m
    ((q ⁻¹ᵁ V).ι ≫ fc)
  have e₂ := AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field n
    ((q ⁻¹ᵁ V).ι ≫ fc)
  have : m = n := by exact_mod_cast e₁.symm.trans e₂
  exact this ▸ hm

end RelDim

/-! ### Vanishing of forms -/

section Vanishing

open Stacks.AlgebraicGeometry.ProjPolyChart ProjectiveSpectrum.Proj

/-- The open `D₊(F) ⊆ ℙᴺ_A` of a polynomial `F`. -/
@[expose] public noncomputable def projBasicOpen (A : Type) [CommRing A] (N : ℕ)
    (F : MvPolynomial (Fin (N + 1)) A) : (projectiveSpaceOverRing N (.of A)).Opens :=
  (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso A N).hom ⁻¹ᵁ
    AlgebraicGeometry.Proj.basicOpen (polyGrading A N) F

/-- **`D₊(F)` is compatible with base change.** -/
public theorem preimage_projBasicOpen {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (N : ℕ)
    (F : MvPolynomial (Fin (N + 1)) A) :
    projectiveSpaceOverRingMap N (CommRingCat.ofHom φ) ⁻¹ᵁ projBasicOpen A N F =
      projBasicOpen B N (F.map φ) := by
  have key : projectiveSpaceOverRingMap N (CommRingCat.ofHom φ) ≫
      (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso A N).hom =
      (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso B N).hom ≫
        Stacks.ProjectiveCohomology.projModelMap N φ := by
    have h := Stacks.ProjectiveCohomology.projModelMap_comp_polynomialComparison_iso_inv A B N φ
    rw [← cancel_epi (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso B N).inv,
      ← cancel_mono (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso A N).inv]
    simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id]
    exact h.symm
  unfold projBasicOpen
  rw [← Scheme.Hom.comp_preimage, key, Scheme.Hom.comp_preimage,
    Stacks.ProjectiveCohomology.projModelMap, Proj.map_preimage_basicOpen]
  rfl

/-- **On a reduced closed subscheme, a homogeneous form vanishing at every point of it (i.e.
`D₊(F)` misses it) lies in its ideal.** -/
public theorem mem_closedSubschemeIdeal_of_preimage_eq_bot {K : Type} [Field K] {N : ℕ}
    {Z : Scheme.{0}} [IsReduced Z] (ι : Z ⟶ projectiveSpaceOverRing N (.of K))
    [IsClosedImmersion ι] {F : MvPolynomial (Fin (N + 1)) K} {m : ℕ} (hF : F.IsHomogeneous m)
    (h : ι ⁻¹ᵁ projBasicOpen K N F = ⊥) :
    F ∈ (MMP.Fourfold.closedSubschemeIdeal ι).toIdeal := by
  classical
  set i := ι ≫ (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso K N).hom
  have hFm : F ∈ polyGrading K N m := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hF
  refine Ideal.subset_span ⟨m, ⟨F, hFm⟩, rfl, ?_⟩
  by_contra hσ
  have : Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj (polyGrading K N))
      (twistingSheaf (polyGrading K N) m) :=
    AlgebraicGeometry.ProjectiveSpectrum.Proj.algebraicGeometry_isInvertible_twistingSheaf
      (polyGrading K N) (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top _ _) m
  have : Stacks.Ample.IsInvertibleModule Z
      ((Scheme.Modules.pullback i).obj (twistingSheaf (polyGrading K N) (m : ℤ))) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback i _
  obtain ⟨z, hz⟩ := nonempty_nonvanishingLocus_of_ne_zero _ _ hσ
  rw [nonvanishingLocus_sectionsOfTop_eq] at hz
  have h1 := Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections i
    (twistingSheaf (polyGrading K N) (m : ℤ)) (degreeSection (polyGrading K N) m ⟨F, hFm⟩)
  have hz2 : z ∈ i.base ⁻¹' Stacks.Ample.nonvanishingLocus
      (X := AlgebraicGeometry.Proj (polyGrading K N)) (twistingSheaf (polyGrading K N) (m : ℤ))
      (degreeSection (polyGrading K N) m ⟨F, hFm⟩) := by rw [h1]; exact hz
  rw [nonvanishingLocus_degreeSection] at hz2
  have hz' : z ∈ ι ⁻¹ᵁ projBasicOpen K N F := hz2
  rw [h] at hz'
  exact hz'

/-- **A homogeneous form in the ideal of a closed subscheme vanishes at every point of it**:
`D₊(F)` misses the subscheme. -/
public theorem preimage_eq_bot_of_mem_closedSubschemeIdeal {K : Type} [Field K] {N : ℕ}
    {Z : Scheme.{0}} (ι : Z ⟶ projectiveSpaceOverRing N (.of K))
    [IsClosedImmersion ι] {F : MvPolynomial (Fin (N + 1)) K} {m : ℕ} (hF : F.IsHomogeneous m)
    (h : F ∈ (MMP.Fourfold.closedSubschemeIdeal ι).toIdeal) :
    ι ⁻¹ᵁ projBasicOpen K N F = ⊥ := by
  classical
  set i := ι ≫ (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso K N).hom
  have hFm : F ∈ polyGrading K N m := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hF
  have h0 := (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.mem_idealOfClosedSubscheme_iff
    (polyGrading K N) i F).mp h m
  have hdec : (DirectSum.decompose (polyGrading K N) F) m = ⟨F, hFm⟩ :=
    Subtype.ext (DirectSum.decompose_of_mem_same _ hFm)
  rw [hdec] at h0
  have h1 := Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections i
    (twistingSheaf (polyGrading K N) (m : ℤ)) (degreeSection (polyGrading K N) m ⟨F, hFm⟩)
  rw [h0, Stacks.Ample.nonvanishingLocus_zero, nonvanishingLocus_degreeSection] at h1
  refine le_bot_iff.mp fun z hz => ?_
  have : i.base z ∈ (AlgebraicGeometry.Proj.basicOpen (polyGrading K N) F : Set _) := hz
  rw [← Set.mem_preimage, h1] at this
  exact absurd this (Set.notMem_empty z)

end Vanishing

/-! ### Cohomology of fibres -/

section Cohomology

open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-- An invertible module on a scheme flat over `S` is flat over `S`. -/
private theorem isFlatOver_of_isInvertibleModule {X S : Scheme.{0}} (π : X ⟶ S) [Flat π]
    (F : X.Modules) [Stacks.Ample.IsInvertibleModule X F] :
    IsFlatOver π.toLRSHom.toShHom F := by
  have h0 : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf _ _).mp ‹_›
  have : F.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule F
  have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0} F :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry F).mp
      (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ F h0)
  obtain ⟨-, hfree⟩ :=
    ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae F).out 4 2).mp hflf
  intro x
  let := (π.stalkMap x).hom.toAlgebra
  have : Module.Flat (S.presheaf.stalk (π x)) (X.presheaf.stalk x) := Flat.stalkMap π x
  have := hfree x
  let : Module (S.presheaf.stalk (π x)) (F.presheaf.stalk x) :=
    Module.compHom _ (π.stalkMap x).hom
  have : IsScalarTower (S.presheaf.stalk (π x)) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat (X.presheaf.stalk x) (F.presheaf.stalk x) := Module.Flat.of_free
  exact Module.Flat.trans (S.presheaf.stalk (π x)) (X.presheaf.stalk x) (F.presheaf.stalk x)

/-- **The Euler characteristic of an invertible module is the same on any two field-valued
fibres** of a flat proper family over a connected base. -/
private theorem eulerSum_eq_of_isPullback {X S : Scheme.{0}} (f : X ⟶ S) [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f] [ConnectedSpace S] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {K₁ K₂ : Type} [Field K₁] [Field K₂]
    {p₁ : Spec (.of K₁) ⟶ S} {p₂ : Spec (.of K₂) ⟶ S} {Y₁ Y₂ : Scheme.{0}}
    {q₁ : Y₁ ⟶ X} {g₁ : Y₁ ⟶ Spec (.of K₁)} {q₂ : Y₂ ⟶ X} {g₂ : Y₂ ⟶ Spec (.of K₂)}
    (h₁ : IsPullback q₁ g₁ f p₁) (h₂ : IsPullback q₂ g₂ f p₂) :
    eulerSum K₁ g₁ ((Scheme.Modules.pullback q₁).obj L) =
      eulerSum K₂ g₂ ((Scheme.Modules.pullback q₂).obj L) := by
  have hfp : FinitePresentation f :=
    ⟨inferInstance, inferInstanceAs (QuasiCompact f),
      @IsSeparated.instQuasiSeparated _ _ f IsProper.toIsSeparated⟩
  have hL : L.IsFinitePresentation :=
    @Stacks.Divisors.isFinitePresentation_of_isInvertible _ L
      ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        X.presheaf _ _).mp ‹_›)
  have hfl := isFlatOver_of_isInvertibleModule f L
  obtain ⟨pt₁⟩ : Nonempty (Spec (.of K₁)) := inferInstance
  obtain ⟨pt₂⟩ : Nonempty (Spec (.of K₂)) := inferInstance
  rw [← chiDerivedFibre_eq_eulerSum f hfp L hL hfl K₁ p₁ q₁ g₁ h₁ pt₁,
    ← chiDerivedFibre_eq_eulerSum f hfp L hL hfl K₂ p₂ q₂ g₂ h₂ pt₂]
  have hlc := isLocallyConstant_fibreEulerCharacteristic f hfp L hL hfl
  rw [fibreEulerCharacteristic_eq_chiDerivedFibre f hfp L hL hfl] at hlc
  exact hlc.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial

/-- **The degree of an invertible module is the same on any two field-valued fibres** of a flat
proper family of curves over a connected base. -/
private theorem invertibleCurveDegree_eq_of_isPullback {X S : Scheme.{0}} (f : X ⟶ S) [Flat f]
    [IsProper f] [LocallyOfFinitePresentation f] [ConnectedSpace S] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {K₁ K₂ : Type} [Field K₁] [Field K₂]
    {p₁ : Spec (.of K₁) ⟶ S} {p₂ : Spec (.of K₂) ⟶ S} {Y₁ Y₂ : Scheme.{0}}
    {q₁ : Y₁ ⟶ X} {g₁ : Y₁ ⟶ Spec (.of K₁)} {q₂ : Y₂ ⟶ X} {g₂ : Y₂ ⟶ Spec (.of K₂)}
    (h₁ : IsPullback q₁ g₁ f p₁) (h₂ : IsPullback q₂ g₂ f p₂) [IsProper g₁] [IsProper g₂]
    (hd₁ : topologicalKrullDim Y₁ ≤ 1) (hd₂ : topologicalKrullDim Y₂ ≤ 1)
    [SheafOfModules.IsInvertible Y₁.presheaf Y₁.ringCatSheaf.2 ((Scheme.Modules.pullback q₁).obj L)]
    [SheafOfModules.IsInvertible Y₂.presheaf Y₂.ringCatSheaf.2
      ((Scheme.Modules.pullback q₂).obj L)] :
    invertibleCurveDegree K₁ g₁ hd₁ ((Scheme.Modules.pullback q₁).obj L) =
      invertibleCurveDegree K₂ g₂ hd₂ ((Scheme.Modules.pullback q₂).obj L) := by
  have : Stacks.Ample.IsInvertibleModule X (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.Ample.isInvertibleModule_unit X
  have e : ∀ {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ X) (g : Y ⟶ Spec (.of K))
      [IsProper g] (hd : topologicalKrullDim Y ≤ 1)
      [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 ((Scheme.Modules.pullback q).obj L)],
      invertibleCurveDegree K g hd ((Scheme.Modules.pullback q).obj L) =
        eulerSum K g ((Scheme.Modules.pullback q).obj L) -
          eulerSum K g ((Scheme.Modules.pullback q).obj (SheafOfModules.unit X.ringCatSheaf)) := by
    intro K _ Y q g _ hd _
    exact congrArg (fun z => eulerSum K g ((Scheme.Modules.pullback q).obj L) - z)
      (eulerSum_congr K g (Scheme.Modules.pullbackUnitIso q)).symm
  rw [e, e, eulerSum_eq_of_isPullback f L h₁ h₂,
    eulerSum_eq_of_isPullback f (SheafOfModules.unit X.ringCatSheaf) h₁ h₂]

/-- **The cohomology of the structure sheaf of a field-valued fibre is that of the scheme
theoretic fibre**, in every degree. -/
private theorem finrank_cohomology_unit_eq_fiber {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f]
    {K : Type} [Field K] {p : Spec (.of K) ⟶ S} {Y : Scheme.{0}} {q : Y ⟶ X}
    {g : Y ⟶ Spec (.of K)} (h : IsPullback q g f p) (n : ℕ) :
    Module.finrank K (cohomologyOverField K g (SheafOfModules.unit Y.ringCatSheaf) n) =
      Module.finrank (S.residueField (p.base (IsLocalRing.closedPoint K)))
        (cohomologyOverField (S.residueField (p.base (IsLocalRing.closedPoint K)))
          (f.fiberToSpecResidueField (p.base (IsLocalRing.closedPoint K)))
          ((Scheme.Modules.pullback (f.fiberι (p.base (IsLocalRing.closedPoint K)))).obj
            (SheafOfModules.unit X.ringCatSheaf)) n) := by
  have hc := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S p
  exact Stacks.FibreCohomology.finrank_eq_of_isPullback f (SheafOfModules.unit X.ringCatSheaf)
    _ (Scheme.descResidueField (Scheme.stalkClosedPointTo p)) q g (by rw [hc]; exact h)
    (SheafOfModules.unit Y.ringCatSheaf) (Scheme.Modules.pullbackUnitIso q).symm n

/-- On an integral scheme over an algebraically closed field the global functions have dimension
at most one. -/
private theorem finrank_cohomology_unit_zero_le_one {K : Type} [Field K] [IsAlgClosed K]
    {X : Scheme.{0}}
    (f : X ⟶ Spec (.of K)) [IsIntegral X] :
    Module.finrank K (cohomologyOverField K f (SheafOfModules.unit X.ringCatSheaf) 0) ≤ 1 := by
  rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections K f]
  let : Algebra K Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  by_cases hfin : FiniteDimensional K Γ(X, ⊤)
  · have : Algebra.IsIntegral K Γ(X, ⊤) := Algebra.IsIntegral.of_finite K _
    have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := Γ(X, ⊤))
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K Γ(X, ⊤)) hb).finrank_eq,
      Module.finrank_self]
  · rw [Module.finrank_of_not_finite hfin]
    exact zero_le_one

/-- On a nonempty scheme proper over a field the global functions have dimension at least one. -/
private theorem one_le_finrank_cohomology_unit_zero {K : Type} [Field K] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of K)) [IsProper f] [Nonempty X] :
    1 ≤ Module.finrank K (cohomologyOverField K f (SheafOfModules.unit X.ringCatSheaf) 0) := by
  have : IsLocallyNoetherian X :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field K f
  have := forall_finiteDimensional_cohomologyOverField_of_isProper K f _
    (Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit X) 0
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have : Nontrivial (cohomologyOverField K f (SheafOfModules.unit X.ringCatSheaf) 0) :=
    @Equiv.nontrivial _ _ (cohomologyOverFieldZeroEquivSections K f _)
      (by change Nontrivial Γ(X, ⊤); exact (X.presheaf.Γgerm x).hom.domain_nontrivial)
  exact Module.finrank_pos

/-- Upper semicontinuous functions only grow under specialization. -/
private theorem le_of_specializes {X : Type*} [TopologicalSpace X] {f : X → ℕ}
    (hf : UpperSemicontinuous f) {x y : X} (h : x ⤳ y) : f x ≤ f y := by
  have := (hf y (f y + 1) (Nat.lt_succ_self _))
  have hx : f x < f y + 1 := (this.filter_mono h).self_of_nhds
  omega

end Cohomology

/-! ### Closed points -/

section ClosedPoints

/-- **A geometric point of positive characteristic over a closed point of any nonempty open.** -/
private theorem exists_geometricPoint {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
    {O : Set (PrimeSpectrum R)} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (p : ℕ) (_ : Fact p.Prime) (_ : CharP k p)
      (ψ : R →+* k), (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ O := by
  have : IsJacobsonRing ℤ := int_isJacobsonRing
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ)
  obtain ⟨s, hsO, hs⟩ := nonempty_inter_closedPoints hne hO.isLocallyClosed
  have hmax : s.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal s).mp hs
  obtain ⟨κ, _, ⟨e⟩⟩ : ∃ (κ : Type) (_ : Field κ), Nonempty ((R ⧸ s.asIdeal) ≃+* κ) :=
    ⟨R ⧸ s.asIdeal, Ideal.Quotient.field s.asIdeal, ⟨RingEquiv.refl _⟩⟩
  let ψ₀ : R →+* κ := e.toRingHom.comp (Ideal.Quotient.mk s.asIdeal)
  have hψ₀ : Function.Surjective ψ₀ := e.surjective.comp Ideal.Quotient.mk_surjective
  have hfin : Algebra.FiniteType ℤ κ := Algebra.FiniteType.of_surjective ψ₀.toIntAlgHom hψ₀
  obtain ⟨hfinite, hpos⟩ := MMP.Fourfold.finite_and_charPos_of_finiteType_int κ
  set p := ringChar κ
  have hpκ : CharP κ p := ringChar.charP κ
  have hp : p.Prime := CharP.char_is_prime κ p
  let k := AlgebraicClosure κ
  have hpk : CharP k p := charP_of_injective_algebraMap (algebraMap κ k).injective p
  refine ⟨k, inferInstance, inferInstance, p, ⟨hp⟩, hpk, (algebraMap κ k).comp ψ₀, ?_⟩
  have hker : RingHom.ker ((algebraMap κ k).comp ψ₀) = s.asIdeal := by
    rw [RingHom.ker_comp_of_injective _ (algebraMap κ k).injective, RingHom.ker_comp_of_injective _
      e.injective, Ideal.mk_ker]
  rw [show (⟨RingHom.ker ((algebraMap κ k).comp ψ₀), RingHom.ker_isPrime _⟩ : PrimeSpectrum R) = s
    from PrimeSpectrum.ext hker]
  exact hsO

end ClosedPoints

/-! ### Inverting an element -/

section Localization

/-- **Inverting a nonzero element of a finitely generated subring of `ℂ`.** -/
private theorem exists_le_isUnit {R : Subalgebra ℤ ℂ} (hR : R.FG) (a : R) (ha : a ≠ 0) :
    ∃ (R' : Subalgebra ℤ ℂ) (h : R ≤ R'), R'.FG ∧ IsUnit (Subalgebra.inclusion h a) := by
  let R' : Subalgebra ℤ ℂ := R ⊔ Algebra.adjoin ℤ {((a : ℂ))⁻¹}
  have hR' : R'.FG := hR.sup (by simpa using Subalgebra.fg_adjoin_finset ({((a : ℂ))⁻¹} : Finset ℂ))
  refine ⟨R', le_sup_left, hR', ?_⟩
  have hinv : ((a : ℂ))⁻¹ ∈ R' :=
    le_sup_right (α := Subalgebra ℤ ℂ) (Algebra.subset_adjoin (Set.mem_singleton _))
  have ha' : (a : ℂ) ≠ 0 := fun h => ha (Subtype.ext h)
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change (a : ℂ) * (a : ℂ)⁻¹ = 1
  exact mul_inv_cancel₀ ha'

/-- After inverting `a`, every point of the spectrum lies in `D(a)`. -/
private theorem specIncl_mem_basicOpen {R R' : Subalgebra ℤ ℂ} (h : R ≤ R') {a : R}
    (ha : IsUnit (Subalgebra.inclusion h a)) (x : Spec (.of R')) :
    (show PrimeSpectrum R from (specIncl h).base x) ∈
      (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)) := by
  change a ∉ ((specIncl h).base x).asIdeal
  intro hx
  have hx' : Subalgebra.inclusion h a ∈ x.asIdeal := hx
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx' ha)

/-- A nonempty open of the spectrum of a domain contains a basic open `D(a)` with `a ≠ 0`. -/
private theorem exists_basicOpen_subset {R : Type} [CommRing R] [IsDomain R]
    {O : Set (PrimeSpectrum R)}
    (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ a : R, a ≠ 0 ∧ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)) ⊆ O := by
  obtain ⟨_, ⟨a, rfl⟩, hbot, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (bot_mem_of_isOpen hO hne) hO
  refine ⟨a, fun h0 => ?_, hsub⟩
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.asIdeal_bot, h0] at hbot
  exact hbot (Ideal.zero_mem _)

end Localization

/-! ### A model with the right relative dimensions -/

section GoodModel

/-- **The points of the bad set lie over a proper closed subset of the base.** -/
private theorem exists_isOpen_forall_badSet {R : Subalgebra ℤ ℂ} {X Xc : Scheme.{0}}
    (f : X ⟶ Spec (.of R)) [Smooth f] [QuasiCompact f] [IsNoetherian X] {q : Xc ⟶ X}
    {fc : Xc ⟶ Spec (.of ℂ)} (h : IsPullback q fc f (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
    (n : ℕ) [SmoothOfRelativeDimension n fc] :
    ∃ O : Set (PrimeSpectrum R), IsOpen O ∧ O.Nonempty ∧ ∀ x ∈ badSet f n, f.base x ∉ O := by
  refine exists_isOpen_forall_notMem f
    (by simpa using (isConstructible_of_isOpen (isClosed_badSet f n).isOpen_compl).compl)
    fun x hx hx0 => ?_
  obtain ⟨x', rfl⟩ := exists_preimage_of_isPullback Subtype.val_injective h x hx0
  exact notMem_badSet_of_isPullback h n x' hx

/-- **A model over which `U` and `C` are smooth of relative dimension `n` and `1`.** -/
private theorem exists_good_model {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) (U : V.Opens)
    {C : Scheme.{0}} (i : C ⟶ U.toScheme) [IsClosedImmersion i] [IsClosedImmersion (i ≫ U.ι)]
    (n : ℕ) [SmoothOfRelativeDimension n (U.ι ≫ sV)] [SmoothOfRelativeDimension 1 (i ≫ U.ι ≫ sV)]
    {N : ℕ} (j : V ⟶ projectiveSpaceOver N (Spec (.of ℂ))) [IsClosedImmersion j]
    (hj : j ≫ pullback.fst (terminal.from (Spec (.of ℂ)))
      (terminal.from (projectiveSpaceAtUniverse.{0} N)) = sV) (T : Finset ℂ) :
    ∃ R : Subalgebra ℤ ℂ, R.FG ∧ (T : Set ℂ) ⊆ R ∧ ∃ M : Model sV U i j R,
      SmoothOfRelativeDimension n (M.F.iU ≫ M.F.sV) ∧
        SmoothOfRelativeDimension 1 (M.F.iC ≫ M.F.iU ≫ M.F.sV) := by
  have : Smooth (U.ι ≫ sV) := SmoothOfRelativeDimension.smooth n _
  have : Smooth (i ≫ U.ι ≫ sV) := SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨R₀, hR₀, hT, M₀, hsU, hsC⟩ := exists_smooth_model sV U i j hj T
  have := hsU
  have := hsC
  have := isNoetherianRing_of_fg hR₀
  have := M₀.F.isProper_C
  obtain ⟨-, hU, hC, hqU, -⟩ := M₀.F.isNoetherian
  obtain ⟨OU, hOU, hOUne, hOU'⟩ := exists_isOpen_forall_badSet (M₀.F.iU ≫ M₀.F.sV)
    M₀.isPullback_U n
  obtain ⟨OC, hOC, hOCne, hOC'⟩ := exists_isOpen_forall_badSet (M₀.F.iC ≫ M₀.F.iU ≫ M₀.F.sV)
    M₀.isPullback_C 1
  obtain ⟨a, ha0, hsub⟩ := exists_basicOpen_subset (hOU.inter hOC)
    ⟨⊥, bot_mem_of_isOpen hOU hOUne, bot_mem_of_isOpen hOC hOCne⟩
  obtain ⟨R, h, hR, hunit⟩ := exists_le_isUnit hR₀ a ha0
  refine ⟨R, hR, hT.trans h, M₀.baseChange h, ?_, ?_⟩
  · refine smoothOfRelativeDimension_of_isPullback (M₀.F.isPullback_qU (specIncl h)) n
      fun x' hbad => hOU' _ hbad ?_
    rw [← Scheme.Hom.comp_apply, (M₀.F.isPullback_qU (specIncl h)).w, Scheme.Hom.comp_apply]
    exact (hsub (specIncl_mem_basicOpen h hunit _)).1
  · refine smoothOfRelativeDimension_of_isPullback (M₀.F.isPullback_qC (specIncl h)) 1
      fun x' hbad => hOC' _ hbad ?_
    rw [← Scheme.Hom.comp_apply, (M₀.F.isPullback_qC (specIncl h)).w, Scheme.Hom.comp_apply]
    exact (hsub (specIncl_mem_basicOpen h hunit _)).2

end GoodModel

/-! ### Comparing invertible modules on the fibres -/

section ModuleComparison

/-- Pulling back differential forms along a cartesian square and then along a map that factors
through `C`. -/
private noncomputable def formsPullbackIso {S S' X W D Cr : Scheme.{0}} {πU : X ⟶ S} {t : S' ⟶ S}
    {r : W ⟶ X} {g : W ⟶ S'} (hsq : IsPullback r g πU t) (n : ℤ) (iC : Cr ⟶ X) (c : D ⟶ W)
    (q : D ⟶ Cr) (hcq : c ≫ r = q ≫ iC) :
    (Scheme.Modules.pullback c).obj (Scheme.Hom.relativeDifferentialForms g n) ≅
      (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback iC).obj
        (Scheme.Hom.relativeDifferentialForms πU n)) :=
  haveI := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback r πU g t hsq n
  (Scheme.Modules.pullback c).mapIso
      (asIso (Scheme.Hom.relativeDifferentialFormsMap r πU g t hsq.w n)).symm ≪≫
    (Scheme.Modules.pullbackComp c r).app _ ≪≫
    (Scheme.Modules.pullbackCongr hcq).app _ ≪≫
    ((Scheme.Modules.pullbackComp q iC).app _).symm

/-- Two iterated pullbacks along composites that agree. -/
private noncomputable def pullbackPullbackCongrIso {A B B' Z : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ Z)
    (a' : A ⟶ B') (b' : B' ⟶ Z) (h : a ≫ b = a' ≫ b') (M : Z.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ≅
      (Scheme.Modules.pullback a').obj ((Scheme.Modules.pullback b').obj M) :=
  (Scheme.Modules.pullbackComp a b).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M ≪≫
    ((Scheme.Modules.pullbackComp a' b').app M).symm

end ModuleComparison

end SpreadingOut

/-! ### Reduction modulo `p` -/

section ReductionModP

open CategoryTheory.Limits Topology

/-- **The closed fibres of a good model carry bounded rational curves.** Over a geometric point
`Spec k ⟶ Spec R` of positive characteristic at which the fibre of `C` is nonempty with
`h⁰(𝒪) ≤ 1` and `h¹(𝒪) ≥ g`, the fibre of `V` contains a rational curve whose `𝒪(1)`-degree obeys
the bound of `C` over `ℂ`. -/
private theorem exists_fibre_curve
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sV]
    (U : V.Opens) (n : ℕ) [SmoothOfRelativeDimension n (U.ι ≫ sV)]
    {C : Scheme.{0}} (i : C ⟶ U.toScheme) [IsClosedImmersion i]
    [AlgebraicGeometry.IsCurve ℂ (i ≫ U.ι ≫ sV)]
    [AlgebraicGeometry.IsProjectiveVariety ℂ (i ≫ U.ι ≫ sV)] [Smooth (i ≫ U.ι ≫ sV)]
    (hg : 1 ≤ genus (i ≫ U.ι ≫ sV))
    (hκ :
      haveI : Stacks.Ample.IsInvertibleModule U.toScheme
          (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
        Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
      MMP.Mori.degreeOn ℂ (U.ι ≫ sV) i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ U.ι ≫ sV)).le
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) < 0)
    {N : ℕ} (j : V ⟶ projectiveSpaceOverRing N (.of ℂ)) [IsClosedImmersion j]
    {R : Subalgebra ℤ ℂ} (M : Model sV U i j R)
    [hUn : SmoothOfRelativeDimension n (M.F.iU ≫ M.F.sV)]
    [hC1R : SmoothOfRelativeDimension 1 (M.F.iC ≫ M.F.iU ≫ M.F.sV)]
    {k : Type} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (ψ : R →+* k)
    (hne : (Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint k) ∈
      Set.range (M.F.iC ≫ M.F.iU ≫ M.F.sV).base)
    (hh0 : Module.finrank ((Spec (.of R)).residueField
        ((Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint k)))
      (cohomologyOverField ((Spec (.of R)).residueField
          ((Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint k)))
        ((M.F.iC ≫ M.F.iU ≫ M.F.sV).fiberToSpecResidueField
          ((Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint k)))
        ((Scheme.Modules.pullback ((M.F.iC ≫ M.F.iU ≫ M.F.sV).fiberι
          ((Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint k)))).obj
          (SheafOfModules.unit M.F.C.ringCatSheaf)) 0) ≤ 1)
    (hh1 : genus (i ≫ U.ι ≫ sV) ≤ Module.finrank ((Spec (.of R)).residueField
        ((Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint k)))
      (cohomologyOverField ((Spec (.of R)).residueField
          ((Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint k)))
        ((M.F.iC ≫ M.F.iU ≫ M.F.sV).fiberToSpecResidueField
          ((Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint k)))
        ((Scheme.Modules.pullback ((M.F.iC ≫ M.F.iU ≫ M.F.sV).fiberι
          ((Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint k)))).obj
          (SheafOfModules.unit M.F.C.ringCatSheaf)) 1)) :
    haveI : Stacks.Ample.IsInvertibleModule U.toScheme
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
      Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
    haveI : IsProper ((i ≫ U.ι) ≫ sV) := by rw [Category.assoc]; infer_instance
    ∃ (L : (M.F.baseChange (Spec.map (CommRingCat.ofHom ψ))).V.IdealSheafData)
      (hL : MMP.Mori.IsRationalCurve (M.F.baseChange (Spec.map (CommRingCat.ofHom ψ))).sV L),
      haveI := hL.2.1
      0 < MMP.Mori.degreeOn k (M.F.baseChange (Spec.map (CommRingCat.ofHom ψ))).sV L.subschemeι
          hL.1.2.le ((Scheme.Modules.pullback
          (M.F.baseChange (Spec.map (CommRingCat.ofHom ψ))).j).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k)))) ∧
        (MMP.Mori.degreeOn k (M.F.baseChange (Spec.map (CommRingCat.ofHom ψ))).sV L.subschemeι
          hL.1.2.le ((Scheme.Modules.pullback
          (M.F.baseChange (Spec.map (CommRingCat.ofHom ψ))).j).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k)))) : ℚ) ≤
          2 * n * MMP.Mori.degreeOn ℂ sV (i ≫ U.ι) (IsCurve.topologicalKrullDim_eq_one
            (f := i ≫ U.ι ≫ sV)).le ((Scheme.Modules.pullback j).obj
              (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of ℂ)))) /
            (-MMP.Mori.degreeOn ℂ (U.ι ≫ sV) i (IsCurve.topologicalKrullDim_eq_one
              (f := i ≫ U.ι ≫ sV)).le (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n)) := by
  classical
  have hΩ : Stacks.Ample.IsInvertibleModule U.toScheme
      (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
    Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
  have hCP : IsProper ((i ≫ U.ι) ≫ sV) := by rw [Category.assoc]; infer_instance
  set F := M.F with hF
  have := F.isOpenImmersion_iU
  have := F.isClosedImmersion_iC
  have := F.isClosedImmersion_j
  have := F.isProper_C
  set πC := F.iC ≫ F.iU ≫ F.sV with hπC
  set πU := F.iU ≫ F.sV with hπU
  set t : Spec (.of k) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom ψ) with ht
  -- the fibre over the geometric point
  set FK := F.baseChange t with hFK
  have := FK.isOpenImmersion_iU
  have := FK.isClosedImmersion_iC
  have := FK.isClosedImmersion_j
  have := FK.isProper_C
  set UK : FK.V.Opens := FK.iU.opensRange with hUK
  set eU : FK.U ≅ UK.toScheme := FK.iU.isoOpensRange with heU
  have heUι : eU.hom ≫ UK.ι = FK.iU := FK.iU.isoOpensRange_hom_ι
  set iK : FK.C ⟶ UK.toScheme := FK.iC ≫ eU.hom with hiKdef
  have hiK : iK ≫ UK.ι ≫ FK.sV = FK.iC ≫ FK.iU ≫ FK.sV := by
    rw [hiKdef, Category.assoc, ← Category.assoc eU.hom, heUι]
  have hUKs : UK.ι ≫ FK.sV = eU.inv ≫ FK.iU ≫ FK.sV := by
    rw [← heUι, Category.assoc, Iso.inv_hom_id_assoc]
  have := smoothOfRelativeDimension_isStableUnderBaseChange n
  have := smoothOfRelativeDimension_isStableUnderBaseChange 1
  have hri : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension n) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hUKn' : SmoothOfRelativeDimension n (FK.iU ≫ FK.sV) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n) (F.isPullback_qU t) hUn
  have hUKn : SmoothOfRelativeDimension n (UK.ι ≫ FK.sV) := by
    rw [hUKs]
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension n) eU.inv
      _).mpr hUKn'
  have hCK1 : SmoothOfRelativeDimension 1 (FK.iC ≫ FK.iU ≫ FK.sV) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) (F.isPullback_qC t) hC1R
  -- `C_k` is a smooth projective curve
  have hneCK : Nonempty FK.C := by
    obtain ⟨c, hc⟩ := hne
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := πC) (g := t) c
      (IsLocalRing.closedPoint k) (by rw [hc])
    exact ⟨z⟩
  have hh0K : Module.finrank k (cohomologyOverField k (FK.iC ≫ FK.iU ≫ FK.sV)
      (SheafOfModules.unit FK.C.ringCatSheaf) 0) = 1 := by
    refine le_antisymm ?_ (one_le_finrank_cohomology_unit_zero _)
    rw [finrank_cohomology_unit_eq_fiber πC (F.isPullback_qC t) 0]
    exact hh0
  have hcurveK : IsCurve k (FK.iC ≫ FK.iU ≫ FK.sV) := GenusOne.isCurve _ (by
    rw [(structureSheafCohomologyIsoCohomologyOverField k _ 0).toLinearEquiv.finrank_eq]
    exact hh0K)
  have hprojK : IsProjectiveVariety k (FK.iC ≫ FK.iU ≫ FK.sV) :=
    { isProjective := FK.isProjectiveMorphism_C }
  have : IsCurve k (iK ≫ UK.ι ≫ FK.sV) := by rw [hiK]; exact hcurveK
  have : IsProjectiveVariety k (iK ≫ UK.ι ≫ FK.sV) := by rw [hiK]; exact hprojK
  have : Smooth (iK ≫ UK.ι ≫ FK.sV) := by rw [hiK]; exact SmoothOfRelativeDimension.smooth 1 _
  -- the genus
  have hgK : 1 ≤ genus (iK ≫ UK.ι ≫ FK.sV) := by
    rw [hiK, genus_eq_finrank_structureSheafCohomology,
      (structureSheafCohomologyIsoCohomologyOverField k _ 1).toLinearEquiv.finrank_eq,
      finrank_cohomology_unit_eq_fiber πC (F.isPullback_qC t) 1]
    exact hg.trans hh1
  -- the degrees of `ω` and of `𝒪(1)` on the fibre are those over `ℂ`
  have : ConnectedSpace (Spec (.of R)) := inferInstance
  have hΩK : Stacks.Ample.IsInvertibleModule UK.toScheme
      (Scheme.Hom.relativeDifferentialForms (UK.ι ≫ FK.sV) n) :=
    Stacks.Discriminant.isInvertible_relativeDifferentialForms (UK.ι ≫ FK.sV) n
  have hΩR : Stacks.Ample.IsInvertibleModule F.U (Scheme.Hom.relativeDifferentialForms πU n) :=
    Stacks.Discriminant.isInvertible_relativeDifferentialForms πU n
  let Lω : F.C.Modules := (Scheme.Modules.pullback F.iC).obj
    (Scheme.Hom.relativeDifferentialForms πU n)
  have : Stacks.Ample.IsInvertibleModule F.C Lω :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback F.iC
      (Scheme.Hom.relativeDifferentialForms πU n)
  have hOR := Stacks.TwistInvertibleOverBase.isInvertibleModule_projectiveSpaceTwistingSheaf N
    (Spec (.of R))
  have hOk := Stacks.TwistInvertibleOverBase.isInvertibleModule_projectiveSpaceTwistingSheaf N
    (Spec (.of k))
  let LH : F.C.Modules := (Scheme.Modules.pullback (F.iC ≫ F.iU ≫ F.j)).obj
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of R)))
  have : Stacks.Ample.IsInvertibleModule F.C LH :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (F.iC ≫ F.iU ≫ F.j)
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of R)))
  have hsqK : IsPullback (eU.inv ≫ F.qU t) (UK.ι ≫ FK.sV) πU t := by
    have h1 : IsPullback eU.inv (UK.ι ≫ FK.sV) (FK.iU ≫ FK.sV) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hUKs, Category.comp_id]⟩
    simpa using h1.paste_horiz (F.isPullback_qU t)
  have hcK : iK ≫ (eU.inv ≫ F.qU t) = F.qC t ≫ F.iC := by
    rw [hiKdef, Category.assoc, Iso.hom_inv_id_assoc, F.qC_iC]
  have hdK := (IsCurve.topologicalKrullDim_eq_one (f := FK.iC ≫ FK.iU ≫ FK.sV)).le
  have hdC := (IsCurve.topologicalKrullDim_eq_one (f := i ≫ U.ι ≫ sV)).le
  have : IsProper (FK.iC ≫ FK.iU ≫ FK.sV) := FK.isProper_C
  have : Smooth πC := SmoothOfRelativeDimension.smooth 1 _
  have : Flat πC := inferInstance
  have : LocallyOfFinitePresentation πC :=
    AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth πC
  have : Stacks.Ample.IsInvertibleModule FK.C ((Scheme.Modules.pullback (F.qC t)).obj Lω) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (F.qC t) Lω
  have : Stacks.Ample.IsInvertibleModule C ((Scheme.Modules.pullback M.pC).obj Lω) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback M.pC Lω
  have : Stacks.Ample.IsInvertibleModule FK.C ((Scheme.Modules.pullback (F.qC t)).obj LH) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (F.qC t) LH
  have : Stacks.Ample.IsInvertibleModule C ((Scheme.Modules.pullback M.pC).obj LH) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback M.pC LH
  have : Stacks.Ample.IsInvertibleModule FK.C ((Scheme.Modules.pullback iK).obj
      (Scheme.Hom.relativeDifferentialForms (UK.ι ≫ FK.sV) n)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback iK
      (Scheme.Hom.relativeDifferentialForms (UK.ι ≫ FK.sV) n)
  have : Stacks.Ample.IsInvertibleModule C ((Scheme.Modules.pullback i).obj
      (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback i
      (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n)
  have hdegω : MMP.Mori.degreeOn k (UK.ι ≫ FK.sV) iK
      (IsCurve.topologicalKrullDim_eq_one (f := iK ≫ UK.ι ≫ FK.sV)).le
        (Scheme.Hom.relativeDifferentialForms (UK.ι ≫ FK.sV) n) =
      MMP.Mori.degreeOn ℂ (U.ι ≫ sV) i hdC (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) := by
    unfold MMP.Mori.degreeOn
    refine (invertibleCurveDegree_eq_of_iso _ _ _
      (formsPullbackIso hsqK n F.iC iK (F.qC t) hcK)).trans
      ((invertibleCurveDegree_congr_hom hiK _ _).trans
        ((invertibleCurveDegree_eq_of_isPullback πC Lω (F.isPullback_qC t) M.isPullback_C
          hdK hdC).trans ?_))
    exact (invertibleCurveDegree_eq_of_iso _ _ _
      (formsPullbackIso M.isPullback_U n F.iC i M.pC M.pC_iC.symm)).symm
  -- `𝒪(1)` on the fibre
  let Hk := (Scheme.Modules.pullback FK.j).obj
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k)))
  have hHkinv : Stacks.Ample.IsInvertibleModule FK.V Hk :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback FK.j
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k)))
  have hKρ : (iK ≫ UK.ι) ≫ FK.j ≫ projectiveSpaceOver.toIntegralAtUniverse N (Spec (.of k)) =
      F.qC t ≫ (F.iC ≫ F.iU ≫ F.j) ≫ projectiveSpaceOver.toIntegralAtUniverse N (Spec (.of R)) := by
    rw [EmbeddedFamily.j_toIntegral_baseChange, hiKdef]
    simp only [Category.assoc]
    rw [← Category.assoc eU.hom, heUι, ← Category.assoc FK.iU, ← F.qU_iU]
    simp only [Category.assoc]
    rw [← Category.assoc FK.iC (F.qU t), ← F.qC_iC]
    simp only [Category.assoc]
  have hCρ : (i ≫ U.ι) ≫ j ≫ projectiveSpaceOver.toIntegralAtUniverse N (Spec (.of ℂ)) =
      M.pC ≫ (F.iC ≫ F.iU ≫ F.j) ≫ projectiveSpaceOver.toIntegralAtUniverse N (Spec (.of R)) := by
    simp only [Category.assoc]
    rw [← Category.assoc M.pC, M.pC_iC, Category.assoc, ← Category.assoc M.pU, M.pU_iU,
      Category.assoc, M.pV_j]
  have eK : (Scheme.Modules.pullback (iK ≫ UK.ι)).obj Hk ≅
      (Scheme.Modules.pullback (F.qC t)).obj LH :=
    (Scheme.Modules.pullback (iK ≫ UK.ι)).mapIso ((Scheme.Modules.pullbackComp FK.j _).app _) ≪≫
      pullbackPullbackCongrIso _ _ _ _ hKρ _ ≪≫
      ((Scheme.Modules.pullback (F.qC t)).mapIso
        ((Scheme.Modules.pullbackComp (F.iC ≫ F.iU ≫ F.j) _).app _)).symm
  have eC : (Scheme.Modules.pullback (i ≫ U.ι)).obj ((Scheme.Modules.pullback j).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of ℂ)))) ≅
      (Scheme.Modules.pullback M.pC).obj LH :=
    (Scheme.Modules.pullback (i ≫ U.ι)).mapIso ((Scheme.Modules.pullbackComp j _).app _) ≪≫
      pullbackPullbackCongrIso _ _ _ _ hCρ _ ≪≫
      ((Scheme.Modules.pullback M.pC).mapIso
        ((Scheme.Modules.pullbackComp (F.iC ≫ F.iU ≫ F.j) _).app _)).symm
  have : Stacks.Ample.IsInvertibleModule FK.C ((Scheme.Modules.pullback (iK ≫ UK.ι)).obj Hk) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (iK ≫ UK.ι) Hk
  have : Stacks.Ample.IsInvertibleModule C ((Scheme.Modules.pullback (i ≫ U.ι)).obj
      ((Scheme.Modules.pullback j).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of ℂ))))) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (i ≫ U.ι)
      ((Scheme.Modules.pullback j).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of ℂ))))
  have : IsProper ((iK ≫ UK.ι) ≫ FK.sV) := by rw [Category.assoc]; infer_instance
  have hdegH : MMP.Mori.degreeOn k FK.sV (iK ≫ UK.ι)
      (IsCurve.topologicalKrullDim_eq_one (f := iK ≫ UK.ι ≫ FK.sV)).le Hk =
      MMP.Mori.degreeOn ℂ sV (i ≫ U.ι) hdC ((Scheme.Modules.pullback j).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of ℂ)))) := by
    unfold MMP.Mori.degreeOn
    refine (invertibleCurveDegree_eq_of_iso _ _ _ eK).trans
      ((invertibleCurveDegree_congr_hom (by rw [Category.assoc, hiK]) _ _).trans
        ((invertibleCurveDegree_eq_of_isPullback πC LH (F.isPullback_qC t) M.isPullback_C
          hdK hdC).trans ?_))
    exact ((invertibleCurveDegree_eq_of_iso _ _ _ eC).trans
      (invertibleCurveDegree_congr_hom (Category.assoc _ _ _) _ _)).symm
  have hVK : IsProjectiveMorphism FK.sV := ⟨N, FK.j, inferInstance, FK.j_fst⟩
  have hHamp : Stacks.Ample.IsAmple FK.V Hk :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
      (Scheme.Modules.isAmple_pullback_of_isClosedImmersion FK.j _
        ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mp
          (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf N (Spec (.of k)))))
  have hκK : MMP.Mori.degreeOn k (UK.ι ≫ FK.sV) iK
      (IsCurve.topologicalKrullDim_eq_one (f := iK ≫ UK.ι ≫ FK.sV)).le
        (Scheme.Hom.relativeDifferentialForms (UK.ι ≫ FK.sV) n) < 0 := hdegω ▸ hκ
  obtain ⟨L, hL, h0, hle⟩ := MMP.Fourfold.exists_isRationalCurve_degreeOn_le_of_charP p FK.sV hVK
    UK n iK hgK hκK Hk hHamp
  refine ⟨L, hL, h0, ?_⟩
  rw [hdegH, hdegω] at hle
  exact hle

/-- **Bounded rational curves on the closed fibres of a model.** -/
private theorem exists_model_fibre_curves
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sV]
    (U : V.Opens) (n : ℕ) [SmoothOfRelativeDimension n (U.ι ≫ sV)]
    {C : Scheme.{0}} (i : C ⟶ U.toScheme) [IsClosedImmersion i]
    [AlgebraicGeometry.IsCurve ℂ (i ≫ U.ι ≫ sV)]
    [AlgebraicGeometry.IsProjectiveVariety ℂ (i ≫ U.ι ≫ sV)] [Smooth (i ≫ U.ι ≫ sV)]
    (hg : 1 ≤ genus (i ≫ U.ι ≫ sV))
    (hκ :
      haveI : Stacks.Ample.IsInvertibleModule U.toScheme
          (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
        Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
      MMP.Mori.degreeOn ℂ (U.ι ≫ sV) i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ U.ι ≫ sV)).le
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) < 0)
    {N : ℕ} (j : V ⟶ projectiveSpaceOverRing N (.of ℂ)) [IsClosedImmersion j]
    (hj : j ≫ Limits.pullback.fst (Limits.terminal.from (Spec (.of ℂ)))
      (Limits.terminal.from (projectiveSpaceAtUniverse.{0} N)) = sV)
    {r : ℕ} (G : Fin r → MvPolynomial (Fin (N + 1)) ℂ) (hG : ∀ l, ∃ d, (G l).IsHomogeneous d)
    (hmem : ∀ l, G l ∈ (MMP.Fourfold.closedSubschemeIdeal j).toIdeal) :
    haveI : Stacks.Ample.IsInvertibleModule U.toScheme
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
      Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
    haveI : IsProper ((i ≫ U.ι) ≫ sV) := by rw [Category.assoc]; infer_instance
    ∃ (R : Subalgebra ℤ ℂ), R.FG ∧ ∃ GR : Fin r → MvPolynomial (Fin (N + 1)) R,
      (∀ l, (GR l).map (algebraMap R ℂ) = G l) ∧ (∀ l, ∃ d, (GR l).IsHomogeneous d) ∧
      ∀ O : Set (PrimeSpectrum R), IsOpen O → O.Nonempty →
        ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (ψ : R →+* k),
          (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ O ∧
          ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of k)) (ι : Z ⟶ projectiveSpaceOverRing N (.of k))
            (_ : IsClosedImmersion ι),
            ι ≫ Limits.pullback.fst (Limits.terminal.from (Spec (.of k)))
              (Limits.terminal.from (projectiveSpaceAtUniverse.{0} N)) = sZ ∧
            ∃ (L : Z.IdealSheafData) (hL : MMP.Mori.IsRationalCurve sZ L),
              (∀ l, (GR l).map ψ ∈
                (MMP.Fourfold.closedSubschemeIdeal (L.subschemeι ≫ ι)).toIdeal) ∧
              haveI := hL.2.1
              0 < MMP.Mori.degreeOn k sZ L.subschemeι hL.1.2.le ((Scheme.Modules.pullback ι).obj
                (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N
                  (Spec (.of k)))) ∧
              (MMP.Mori.degreeOn k sZ L.subschemeι hL.1.2.le ((Scheme.Modules.pullback ι).obj
                (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N
                  (Spec (.of k)))) : ℚ) ≤
                2 * n * MMP.Mori.degreeOn ℂ sV (i ≫ U.ι) (IsCurve.topologicalKrullDim_eq_one
                  (f := i ≫ U.ι ≫ sV)).le ((Scheme.Modules.pullback j).obj
                    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N
                      (Spec (.of ℂ)))) /
                  (-MMP.Mori.degreeOn ℂ (U.ι ≫ sV) i (IsCurve.topologicalKrullDim_eq_one
                    (f := i ≫ U.ι ≫ sV)).le
                      (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n)) := by
  classical
  have hΩ : Stacks.Ample.IsInvertibleModule U.toScheme
      (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
    Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
  have hCP : IsProper ((i ≫ U.ι) ≫ sV) := by rw [Category.assoc]; infer_instance
  -- `C` is closed in `V`, and smooth of relative dimension one
  have : IsProper (i ≫ U.ι) := IsProper.of_comp (i ≫ U.ι) sV
  have hCcl : IsClosedImmersion (i ≫ U.ι) :=
    IsClosedImmersion.of_isPreimmersion _ (i ≫ U.ι).isClosedMap.isClosed_range
  have hC1 : SmoothOfRelativeDimension 1 (i ≫ U.ι ≫ sV) := by
    have hvar : IsVariety ℂ (i ≫ U.ι ≫ sV) := inferInstance
    have : IsIntegral C := hvar.toIsIntegral
    have : IrreducibleSpace C := inferInstance
    have : ConnectedSpace C := inferInstance
    have : Nonempty C := IsIntegral.nonempty
    obtain ⟨d, hd⟩ := exists_smoothOfRelativeDimension_of_connectedSpace (i ≫ U.ι ≫ sV)
    have h1 := IsCurve.topologicalKrullDim_eq_one (f := i ≫ U.ι ≫ sV)
    have h2 := AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field d
      (i ≫ U.ι ≫ sV)
    have : d = 1 := by
      have := h2.symm.trans h1
      exact_mod_cast this
    exact this ▸ hd
  -- a model with the right relative dimensions, containing the coefficients of `G`
  obtain ⟨R, hR, hTR, M, hUn, hC1R⟩ := exists_good_model sV U i n j hj
    (Finset.univ.biUnion fun l => (G l).coeffs)
  have := hUn
  have := hC1R
  have hcoef : ∀ l, ((G l).coeffs : Set ℂ) ⊆ R := fun l x hx =>
    hTR (Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, hx⟩))
  choose GR hGR using fun l =>
    (MvPolynomial.mem_range_map_iff_coeffs_subset (f := algebraMap R ℂ)).mpr
      fun x hx => ⟨⟨x, hcoef l hx⟩, rfl⟩
  have hGRh : ∀ l, ∃ d, (GR l).IsHomogeneous d := fun l =>
    (hG l).imp fun d hd =>
      MvPolynomial.IsHomogeneous.of_map Subtype.val_injective ((hGR l).symm ▸ hd)
  refine ⟨R, hR, GR, hGR, hGRh, fun O hO hOne => ?_⟩
  -- notation and standing facts on the model
  set F := M.F with hF
  have := F.isOpenImmersion_iU
  have := F.isClosedImmersion_iC
  have := F.isClosedImmersion_j
  have := F.isProper_C
  have := isNoetherianRing_of_fg hR
  obtain ⟨hVn, hUnoeth, hCnoeth, hqU, hqV⟩ := F.isNoetherian
  set πC := F.iC ≫ F.iU ≫ F.sV with hπC
  set πU := F.iU ≫ F.sV with hπU
  have : Smooth πC := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth πU := SmoothOfRelativeDimension.smooth n _
  set ιℂ : Spec (.of ℂ) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R ℂ))
  set η := ιℂ.base (IsLocalRing.closedPoint ℂ) with hη
  have hηbot : η = (⊥ : PrimeSpectrum R) := spec_algebraMap_apply_eq_bot Subtype.val_injective _
  have : Stacks.Ample.IsInvertibleModule F.C (SheafOfModules.unit F.C.ringCatSheaf) :=
    Stacks.Ample.isInvertibleModule_unit F.C
  have : IsNoetherian F.C := hCnoeth
  have : IsLocallyNoetherian F.C := IsNoetherian.toIsLocallyNoetherian
  have : IsNoetherian (Spec (.of R)) := inferInstance
  have : (SheafOfModules.unit F.C.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit F.C
  have hflat := isFlatOver_of_isInvertibleModule πC (SheafOfModules.unit F.C.ringCatSheaf)
  have hsemi := fun m => MMP.upperSemicontinuous_finrank_cohomologyOverField_fiber πC
    F.isProjectiveMorphism_C.isProjective (SheafOfModules.unit F.C.ringCatSheaf) hflat m
  -- `O₃`: the equations of `V` vanish on the fibre
  set B : Set F.V := ⋃ l, ((F.j ⁻¹ᵁ projBasicOpen R N (GR l) : F.V.Opens) : Set F.V) with hBdef
  have hpj : M.pV ≫ F.j = j ≫ projectiveSpaceOverMap N ιℂ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, F.j_fst, Category.assoc, projectiveSpaceOverMap_fst, ← Category.assoc,
        hj, M.isPullback_V.w]
    · rw [Category.assoc, Category.assoc, projectiveSpaceOverMap_snd]
      exact M.pV_j
  have : LocallyOfFiniteType F.sV := by rw [← F.j_fst]; infer_instance
  have : LocallyOfFinitePresentation F.sV := inferInstance
  have := hVn
  obtain ⟨O₃, hO₃, hO₃ne, hO₃'⟩ := exists_isOpen_forall_notMem F.sV
    (isConstructible_of_isOpen (isOpen_iUnion fun l => (F.j ⁻¹ᵁ projBasicOpen R N (GR l)).2))
    (T := B) (by
      intro x hx hx0
      obtain ⟨x', rfl⟩ := exists_preimage_of_isPullback Subtype.val_injective M.isPullback_V x hx0
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hx
      obtain ⟨d, hd⟩ := hG l
      have h0 := preimage_eq_bot_of_mem_closedSubschemeIdeal j hd (hmem l)
      have hx' : x' ∈ (M.pV ≫ F.j) ⁻¹ᵁ projBasicOpen R N (GR l) := hl
      rw [hpj, Scheme.Hom.comp_preimage,
        show projectiveSpaceOverMap N ιℂ =
          projectiveSpaceOverRingMap N (CommRingCat.ofHom (algebraMap R ℂ)) from rfl,
        preimage_projBasicOpen, hGR l, h0] at hx'
      exact hx')
  -- `O₄`: the fibres of `C` have `h⁰ ≤ 1`
  have hh0η : Module.finrank ((Spec (.of R)).residueField η)
      (cohomologyOverField ((Spec (.of R)).residueField η) (πC.fiberToSpecResidueField η)
        ((Scheme.Modules.pullback (πC.fiberι η)).obj (SheafOfModules.unit F.C.ringCatSheaf)) 0)
        < 1 + 1 := by
    rw [← finrank_cohomology_unit_eq_fiber πC M.isPullback_C 0]
    exact Nat.lt_succ_of_le (finrank_cohomology_unit_zero_le_one (i ≫ U.ι ≫ sV))
  obtain ⟨O₄, hO₄sub, hO₄, hηO₄⟩ := mem_nhds_iff.mp (hsemi 0 η _ hh0η)
  -- `O₅`: the fibres of `C` are nonempty
  have : Flat πC := inferInstance
  have : LocallyOfFinitePresentation πC :=
    AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth πC
  have : UniversallyOpen πC := UniversallyOpen.of_flat (f := πC)
  have hO₅ : IsOpen (Set.range πC.base) := πC.isOpenMap.isOpen_range
  have hηO₅ : η ∈ Set.range πC.base := by
    obtain ⟨c⟩ : Nonempty C := inferInstance
    refine ⟨M.pC.base c, ?_⟩
    rw [← Scheme.Hom.comp_apply, M.isPullback_C.w, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  -- a geometric point in all of them
  have hO' : IsOpen (O ∩ O₃ ∩ O₄ ∩ Set.range πC.base) :=
    ((hO.inter hO₃).inter hO₄).inter hO₅
  have hηO : η ∈ O ∩ O₃ ∩ O₄ ∩ Set.range πC.base :=
    ⟨⟨⟨hηbot ▸ bot_mem_of_isOpen hO hOne, hηbot ▸ bot_mem_of_isOpen hO₃ hO₃ne⟩, hηO₄⟩, hηO₅⟩
  have : Algebra.FiniteType ℤ R := (Subalgebra.fg_iff_finiteType R).mp hR
  obtain ⟨k, _, _, p, _, _, ψ, hψ⟩ := exists_geometricPoint hO' ⟨η, hηO⟩
  refine ⟨k, inferInstance, inferInstance, ψ, hψ.1.1.1, ?_⟩
  set t : Spec (.of k) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom ψ) with ht
  set s := t.base (IsLocalRing.closedPoint k) with hsdef
  have hs : s = ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap ψ (IsLocalRing.maximalIdeal k) = _
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  have hsO : s ∈ O ∩ O₃ ∩ O₄ ∩ Set.range πC.base := hs ▸ hψ
  have hpt : ∀ z : Spec (.of k), t.base z = s := fun z => by
    rw [hsdef]; congr 1; exact Subsingleton.elim _ _
  -- the fibre carries a bounded rational curve
  have hsp : η ⤳ s := hηbot ▸ (PrimeSpectrum.le_iff_specializes ⊥ s).mp bot_le
  have hh1 : genus (i ≫ U.ι ≫ sV) ≤ Module.finrank ((Spec (.of R)).residueField s)
      (cohomologyOverField ((Spec (.of R)).residueField s) (πC.fiberToSpecResidueField s)
        ((Scheme.Modules.pullback (πC.fiberι s)).obj
          (SheafOfModules.unit F.C.ringCatSheaf)) 1) := by
    refine le_trans ?_ (le_of_specializes (hsemi 1) hsp)
    rw [← finrank_cohomology_unit_eq_fiber πC M.isPullback_C 1,
      ← (structureSheafCohomologyIsoCohomologyOverField ℂ _ 1).toLinearEquiv.finrank_eq,
      ← genus_eq_finrank_structureSheafCohomology]
  obtain ⟨L, hL, h0, hle⟩ := exists_fibre_curve sV U n i hg hκ j M p ψ hsO.2
    (Nat.lt_succ_iff.mp (hO₄sub hsO.1.2)) hh1
  have := (F.baseChange t).isClosedImmersion_j
  refine ⟨(F.baseChange t).V, (F.baseChange t).sV, (F.baseChange t).j,
    (F.baseChange t).isClosedImmersion_j, (F.baseChange t).j_fst, L, hL, fun l => ?_, h0, hle⟩
  -- the equations vanish on the reduced curve `L`
  have : IsIntegral L.subscheme := hL.1.1
  obtain ⟨d, hd⟩ := hGRh l
  refine mem_closedSubschemeIdeal_of_preimage_eq_bot (L.subschemeι ≫ (F.baseChange t).j)
    (hd.map ψ) ?_
  rw [Scheme.Hom.comp_preimage]
  suffices hK : (F.baseChange t).j ⁻¹ᵁ projBasicOpen k N ((GR l).map ψ) = ⊥ by
    rw [hK, Scheme.Hom.preimage_bot]
  rw [← preimage_projBasicOpen ψ N (GR l), ← Scheme.Hom.comp_preimage,
    show projectiveSpaceOverRingMap N (CommRingCat.ofHom ψ) = projectiveSpaceOverMap N t from rfl,
    F.j_baseChange t, Scheme.Hom.comp_preimage]
  refine le_bot_iff.mp fun z hz => absurd ?_ (hO₃' _ (Set.mem_iUnion.mpr ⟨l, hz⟩))
  rw [← Scheme.Hom.comp_apply, (F.isPullback_qV t).w, Scheme.Hom.comp_apply, hpt]
  exact hsO.1.1.2

end ReductionModP

/-- A homogeneous ideal of `K[T₀, …, T_N]` is generated by finitely many homogeneous
polynomials. -/
public theorem exists_homogeneous_generators {K : Type} [Field K] {N : ℕ}
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)) :
    ∃ (r : ℕ) (G : Fin r → MvPolynomial (Fin (N + 1)) K),
      (∀ l, ∃ d, (G l).IsHomogeneous d) ∧ J.toIdeal = Ideal.span (Set.range G) := by
  classical
  let S : Set (MvPolynomial (Fin (N + 1)) K) :=
    {x | x ∈ J.toIdeal ∧ ∃ d, x.IsHomogeneous d}
  have hJ : J.toIdeal = Ideal.span S := by
    apply le_antisymm
    · intro x hx
      rw [← DirectSum.sum_support_decompose (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) x]
      refine Ideal.sum_mem _ fun d _ => Ideal.subset_span ⟨J.2 d hx, d, ?_⟩
      exact (MvPolynomial.mem_homogeneousSubmodule _ _).1 (SetLike.coe_mem _)
    · exact Ideal.span_le.2 fun x hx => hx.1
  have hfg : (Ideal.span S).FG := IsNoetherian.noetherian _
  obtain ⟨T, hTS, hT⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).1 hfg
  refine ⟨T.card, fun l => (T.equivFin.symm l : _), fun l => (hTS (T.equivFin.symm l).2).2, ?_⟩
  rw [hJ]
  change Submodule.span _ S = Submodule.span _ _
  rw [hT]
  congr 1
  ext x
  simp only [Finset.mem_coe, Set.mem_range]
  exact ⟨fun hx => ⟨T.equivFin ⟨x, hx⟩, by simp⟩, fun ⟨l, hl⟩ => hl ▸ (T.equivFin.symm l).2⟩

/-- A positive integer bounded by a rational is bounded by its floor. -/
private theorem toNat_le_floor {x : ℤ} {E : ℚ} (hx : 0 < x) (h : (x : ℚ) ≤ E) :
    x.toNat ≤ ⌊E⌋₊ := by
  apply Nat.le_floor
  have : ((x.toNat : ℤ) : ℚ) = x := by rw [Int.toNat_of_nonneg hx.le]
  rw [← this] at h
  exact_mod_cast h

/-- The bound for the hyperplane sheaf of a projective embedding `V ⊆ ℙᴺ_ℂ`. -/
private theorem exists_isRationalCurve_degreeOn_twist_le
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sV]
    (U : V.Opens) (n : ℕ) [SmoothOfRelativeDimension n (U.ι ≫ sV)]
    {C : Scheme.{0}} (i : C ⟶ U.toScheme) [IsClosedImmersion i]
    [AlgebraicGeometry.IsCurve ℂ (i ≫ U.ι ≫ sV)]
    [AlgebraicGeometry.IsProjectiveVariety ℂ (i ≫ U.ι ≫ sV)] [Smooth (i ≫ U.ι ≫ sV)]
    (hg : 1 ≤ genus (i ≫ U.ι ≫ sV))
    (hκ :
      haveI : Stacks.Ample.IsInvertibleModule U.toScheme
          (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
        Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
      Mori.degreeOn ℂ (U.ι ≫ sV) i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ U.ι ≫ sV)).le
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) < 0)
    {N : ℕ} (j : V ⟶ projectiveSpaceOver N (Spec (.of ℂ))) [IsClosedImmersion j]
    (hj : j ≫ Limits.pullback.fst (Limits.terminal.from (Spec (.of ℂ)))
      (Limits.terminal.from (projectiveSpaceAtUniverse.{0} N)) = sV) :
    haveI : Stacks.Ample.IsInvertibleModule U.toScheme
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
      Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
    haveI : IsProper ((i ≫ U.ι) ≫ sV) := by rw [Category.assoc]; infer_instance
    ∃ (L : V.IdealSheafData) (hL : Mori.IsRationalCurve sV L),
      haveI := hL.2.1
      0 < Mori.degreeOn ℂ sV L.subschemeι hL.1.2.le ((Scheme.Modules.pullback j).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of ℂ)))) ∧
        (Mori.degreeOn ℂ sV L.subschemeι hL.1.2.le ((Scheme.Modules.pullback j).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of ℂ)))) : ℚ) ≤
          2 * n * Mori.degreeOn ℂ sV (i ≫ U.ι) (IsCurve.topologicalKrullDim_eq_one
            (f := i ≫ U.ι ≫ sV)).le ((Scheme.Modules.pullback j).obj
              (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of ℂ)))) /
            (-Mori.degreeOn ℂ (U.ι ≫ sV) i (IsCurve.topologicalKrullDim_eq_one
              (f := i ≫ U.ι ≫ sV)).le (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n)) := by
  obtain ⟨r, G, hG, hspan⟩ := exists_homogeneous_generators (MMP.Fourfold.closedSubschemeIdeal j)
  have hmem : ∀ l, G l ∈ (MMP.Fourfold.closedSubschemeIdeal j).toIdeal := fun l =>
    hspan ▸ Ideal.subset_span ⟨l, rfl⟩
  obtain ⟨R, hRfg, GR, hGR, hGRh, hfib⟩ := exists_model_fibre_curves sV U n i hg hκ j hj G hG hmem
  have : Algebra.FiniteType ℤ R := Subalgebra.fg_iff_finiteType R |>.mp hRfg
  have : Stacks.Ample.IsInvertibleModule U.toScheme
      (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
    Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
  have : IsProper ((i ≫ U.ι) ≫ sV) := by rw [Category.assoc]; infer_instance
  set E : ℚ := 2 * n * Mori.degreeOn ℂ sV (i ≫ U.ι) (IsCurve.topologicalKrullDim_eq_one
    (f := i ≫ U.ι ≫ sV)).le ((Scheme.Modules.pullback j).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of ℂ)))) /
    (-Mori.degreeOn ℂ (U.ι ≫ sV) i (IsCurve.topologicalKrullDim_eq_one
      (f := i ≫ U.ι ≫ sV)).le (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n)) with hE
  have h1 : ∀ O : Set (PrimeSpectrum R), IsOpen O → O.Nonempty →
      ∃ (k : Type) (_ : Field k) (ψ : R →+* k),
        (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ O ∧
        ∃ e ≤ ⌊E⌋₊, HasBinarySolution k (fun l => (GR l).map ψ) e := by
    intro O hO hne
    obtain ⟨k, _, _, ψ, hψ, Z, sZ, ι, _, hι, L, hL, hGZ, h0, hle⟩ := hfib O hO hne
    obtain ⟨e, he, hsol⟩ := hasBinarySolution_of_isRationalCurve sZ ι hι
      (fun l => (GR l).map ψ) (fun l => (hGRh l).imp fun d hd => hd.map ψ) L hL hGZ h0
    exact ⟨k, inferInstance, ψ, hψ, e, he.trans (toNat_le_floor h0 hle), hsol⟩
  obtain ⟨e, he, hsol⟩ := exists_hasBinarySolution_of_dense (algebraMap R ℂ)
    Subtype.val_injective GR ⌊E⌋₊ h1
  simp only [hGR] at hsol
  obtain ⟨L, hL, h0, hle⟩ := exists_isRationalCurve_of_hasBinarySolution sV j hj G hG hspan hsol
  refine ⟨L, hL, h0, ?_⟩
  have hE0 : 0 ≤ E := by
    by_contra hneg
    push Not at hneg
    rw [Nat.floor_eq_zero.mpr (hneg.trans one_pos)] at he
    omega
  calc _ ≤ (e : ℚ) := by exact_mod_cast hle
    _ ≤ ⌊E⌋₊ := by exact_mod_cast he
    _ ≤ E := Nat.floor_le hE0

/-- The degree of the `m`-th tensor power of an invertible sheaf along a curve is `m` times the
degree of the sheaf. -/
private theorem degreeOn_tensorPowModule_natCast {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (z : Z ⟶ X) [IsProper (z ≫ sX)] (hdim : topologicalKrullDim Z ≤ 1) (H : X.Modules)
    [Stacks.Ample.IsInvertibleModule X H] (m : ℕ) :
    Mori.degreeOn ℂ sX z hdim (Stacks.Ample.tensorPowModule X H (m : ℤ)) =
      m * Mori.degreeOn ℂ sX z hdim H := by
  have : Stacks.Ample.IsInvertibleModule Z ((Scheme.Modules.pullback z).obj H) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback z H
  rw [Mori.degreeOn_eq_invertibleCurveDegree, Mori.degreeOn_eq_invertibleCurveDegree,
    ← MMP.Fourfold.invertibleCurveDegree_tensorPowModule_natCast (z ≫ sX) hdim _ m]
  exact invertibleCurveDegree_eq_of_iso ℂ (z ≫ sX) hdim
    (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso z H m)

/-- The bound for an ample invertible sheaf on a projective complex variety. -/
private theorem exists_isRationalCurve_degreeOn_le
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sV]
    (U : V.Opens) (n : ℕ) [SmoothOfRelativeDimension n (U.ι ≫ sV)]
    {C : Scheme.{0}} (i : C ⟶ U.toScheme) [IsClosedImmersion i]
    [AlgebraicGeometry.IsCurve ℂ (i ≫ U.ι ≫ sV)]
    [AlgebraicGeometry.IsProjectiveVariety ℂ (i ≫ U.ι ≫ sV)] [Smooth (i ≫ U.ι ≫ sV)]
    (hg : 1 ≤ genus (i ≫ U.ι ≫ sV))
    (hκ :
      haveI : Stacks.Ample.IsInvertibleModule U.toScheme
          (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
        Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
      Mori.degreeOn ℂ (U.ι ≫ sV) i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ U.ι ≫ sV)).le
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) < 0)
    (H : V.Modules) [Stacks.Ample.IsInvertibleModule V H] (hH : Stacks.Ample.IsAmple V H) :
    haveI : Stacks.Ample.IsInvertibleModule U.toScheme
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
      Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
    haveI : IsProper ((i ≫ U.ι) ≫ sV) := by rw [Category.assoc]; infer_instance
    ∃ (L : V.IdealSheafData) (hL : Mori.IsRationalCurve sV L),
      haveI := hL.2.1
      0 < Mori.degreeOn ℂ sV L.subschemeι hL.1.2.le H ∧
        (Mori.degreeOn ℂ sV L.subschemeι hL.1.2.le H : ℚ) ≤
          2 * n * Mori.degreeOn ℂ sV (i ≫ U.ι) (IsCurve.topologicalKrullDim_eq_one
            (f := i ≫ U.ι ≫ sV)).le H /
            (-Mori.degreeOn ℂ (U.ι ≫ sV) i (IsCurve.topologicalKrullDim_eq_one
              (f := i ≫ U.ι ≫ sV)).le (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n)) := by
  obtain ⟨a, ha, h⟩ := ((Stacks.AmpleRelativeFiniteType.tfae_six sV H).out 1 6).1 hH
  obtain ⟨N, j, hj, hjs, ⟨e⟩⟩ := h a le_rfl
  have : IsImmersion j := hj
  have : IsProper j := by
    have : IsProper (j ≫ Limits.pullback.fst _ _) := by rw [hjs]; infer_instance
    exact IsProper.of_comp j (Limits.pullback.fst _ _)
  have : IsClosedImmersion j :=
    IsClosedImmersion.of_isPreimmersion _ j.isClosedMap.isClosed_range
  have hdeg : ∀ {Z : Scheme.{0}} (z : Z ⟶ V) [IsProper (z ≫ sV)]
      (hdim : topologicalKrullDim Z ≤ 1),
      Mori.degreeOn ℂ sV z hdim ((Scheme.Modules.pullback j).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of ℂ)))) =
        a * Mori.degreeOn ℂ sV z hdim H := fun z _ hdim => by
    rw [← degreeOn_tensorPowModule_natCast sV z hdim H a]
    exact Mori.degreeOn_eq_of_iso ℂ sV z hdim e.symm
  obtain ⟨L, hL, h0, hle⟩ := exists_isRationalCurve_degreeOn_twist_le sV U n i hg hκ j hjs
  refine ⟨L, hL, ?_, ?_⟩
  · rw [hdeg] at h0
    exact pos_of_mul_pos_right h0 (by positivity)
  · rw [hdeg, hdeg] at hle
    have ha' : (0 : ℚ) < a := by exact_mod_cast (show 0 < a by omega)
    push_cast at hle
    rw [← mul_le_mul_iff_of_pos_left ha']
    calc _ ≤ _ := hle
      _ = _ := by ring

end MMP.Fourfold.SmoothLocusSlopeBound

@[expose] public section

namespace MMP.Fourfold

/-- **A bounded rational curve from a negative curve in a smooth open of a normal complex
variety.** Let `V` be a normal projective variety over `ℂ`, `U ⊆ V` an open which is smooth of
relative dimension `n` over `ℂ`, and `i : C ⟶ U` a smooth projective curve of genus `≥ 1` with
`κ = -deg(Ωⁿ_{U/ℂ}|_C) > 0`. For an ample `ℚ`-Cartier `ℚ`-divisor `H` on `V` there is a rational
curve `L ⊆ V` with `0 < H · L ≤ 2n (H · C) / κ`. -/
@[mmp "lem_fourfold_normal_smooth_locus_slope_bound"]
public theorem exists_isRationalCurve_intersectionNumber_le
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sV] [IsNormal V]
    (U : V.Opens) (n : ℕ) [SmoothOfRelativeDimension n (U.ι ≫ sV)]
    {C : Scheme.{0}} (i : C ⟶ U.toScheme) [IsClosedImmersion i]
    [AlgebraicGeometry.IsCurve ℂ (i ≫ U.ι ≫ sV)]
    [AlgebraicGeometry.IsProjectiveVariety ℂ (i ≫ U.ι ≫ sV)] [Smooth (i ≫ U.ι ≫ sV)]
    (hg : 1 ≤ genus (i ≫ U.ι ≫ sV))
    (hκ :
      haveI : Stacks.Ample.IsInvertibleModule U.toScheme
          (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
        Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
      Mori.degreeOn ℂ (U.ι ≫ sV) i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ U.ι ≫ sV)).le
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) < 0)
    (H : Mori.QDivisor V)
    (hHq : haveI := LocallyOfFiniteType.isLocallyNoetherian sV; H.IsQCartier)
    (hH : haveI := LocallyOfFiniteType.isLocallyNoetherian sV
      haveI := QuasiCompact.compactSpace_of_compactSpace sV; H.IsAmple) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sV
    haveI : Stacks.Ample.IsInvertibleModule U.toScheme
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n) :=
      Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) n
    haveI : IsProper ((i ≫ U.ι) ≫ sV) := by rw [Category.assoc]; infer_instance
    ∃ (L : V.IdealSheafData) (hL : Mori.IsRationalCurve sV L),
      haveI := hL.2.1
      0 < H.intersectionNumber ℂ sV L.subschemeι hL.1.2.le hHq ∧
        H.intersectionNumber ℂ sV L.subschemeι hL.1.2.le hHq ≤
          2 * n * H.intersectionNumber ℂ sV (i ≫ U.ι)
            (IsCurve.topologicalKrullDim_eq_one (f := i ≫ U.ι ≫ sV)).le hHq /
            (-Mori.degreeOn ℂ (U.ι ≫ sV) i (IsCurve.topologicalKrullDim_eq_one
              (f := i ≫ U.ι ≫ sV)).le (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) n)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sV
  have := QuasiCompact.compactSpace_of_compactSpace sV
  obtain ⟨m, hm, D, hD, hDc, hDa⟩ := hH
  have := hDc.isInvertibleModule_divisorialSheaf
  have hDm : MMP.Mori.Divisor.toQDivisor D = (m : ℤ) • H := by
    rw [hD, ← Int.cast_smul_eq_zsmul ℚ]; simp
  have key : ∀ {Z : Scheme.{0}} (j : Z ⟶ V) [IsProper (j ≫ sV)]
      (hdim : topologicalKrullDim Z ≤ 1),
      H.intersectionNumber ℂ sV j hdim hHq =
        (Mori.degreeOn ℂ sV j hdim D.divisorialSheaf : ℚ) / m := fun j _ hdim =>
    MMP.Mori.QDivisor.intersectionNumber_eq_of_smul ℂ sV j hdim H hHq hm D hDc hDm
  obtain ⟨L, hL, h0, hle⟩ := SmoothLocusSlopeBound.exists_isRationalCurve_degreeOn_le sV U n i hg hκ
    D.divisorialSheaf hDa
  refine ⟨L, hL, ?_, ?_⟩
  · rw [key]; exact div_pos (by exact_mod_cast h0) (by exact_mod_cast hm)
  · rw [key, key]
    have hm' : (0 : ℚ) < m := by exact_mod_cast hm
    rw [div_le_iff₀ hm']
    calc _ ≤ _ := hle
      _ = _ := by field_simp

end MMP.Fourfold

end
