module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.Analysis.Complex.CauchyTransformRungeMontel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.Singularities.AdjointIdeal.ReducedSncBoundary
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.MMP.Fourfold.RestrictedSeries
public import MMP.AlgebraicGeometry.Singularities.DifferentFlatBaseChange
public import MMP.AlgebraicGeometry.Divisor.RationalFunctionGerm
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.IndexOneCover
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.Divisor.RestrictedSectionAlgebra
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorAdjunction
public import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueSmoothDivisor
public import MMP.AlgebraicGeometry.Singularities.Adjunction.TotalDiscrepancyInequality
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Positivity.SemiampleSectionModule
public import MMP.AlgebraicGeometry.Positivity.AsymptoticAdjointIdeal
public import MMP.AlgebraicGeometry.Singularities.AdjointIdeal.GeneralMember
public import MMP.AlgebraicGeometry.MMP.Flip.FixedMemberLifting
public import MMP.AlgebraicGeometry.Singularities.PltDifferentCoefficients
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison

/-!
# The lifting inequality of a prepared restricted algebra

For the prepared restricted algebra `R_S(X, q(K_X + Δ))` over a finitely generated normal complex
domain `A₀`, with `X` smooth of dimension at least three, `S` a smooth prime divisor,
`Δ = S + A + B`, `A = H/a` for an effective `π`-ample Cartier divisor `H` and `a ≥ 3`, reindexed
as the graded restricted series `V_m = W_{m/q}` (`W_j` the image series of `qK + ⌊qΔ⌋` on `S`),
the lifting theorem below the asymptotic restricted fixed divisor for a fixed ample member
(`MMP.Fourfold.exists_isRestrictionAlong_of_le_restrictedAsymptoticFixedPart_of_isPltPair_add`)
gives the lifting inequality of `MMP.Fourfold.HasRestrictedLiftingProperty`. The comparison
needs three facts: `εD + A` is relatively ample for some rational `0 < ε < 1` (openness of
ampleness at `A`); the asymptotic fixed part of the restricted systems `|mD|_S` is at most that
of `V` (they agree in the degrees divisible by `q`, and fixed parts decrease along multiples);
and `(S, (A + B)|_S + A|_S)` is a real canonical pair, by adjunction from `(X, Δ + A)` plt.

## Main results

* `MMP.Fourfold.exists_forall_mem_of_isPltPair_add`: the lifting inequality for the reindexed
  restricted algebra.

## Implementation notes

* The restricted system `|mD|_S`, the canonical section and the restriction map are those of
  the lifting theorem: sections of `𝒪_X(G)` are rational functions (`MMP.Fourfold.sectionsIn`),
  multiplication by a canonical section is the inclusion of section sets, and restriction is
  `MMP.Fourfold.IsRestrictionAlong`.

## References

* The fourfold source, *Section lifting* and *Prepared algebras*.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- The image series of `D` on `S` is graded: restricted sections of degrees `j` and `k`
multiply to a restricted section of degree `j + k`. -/
theorem mul_mem_imageSeries_add {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (D : Divisor X) (S : MMP.Mori.PrimeDivisor X) [IsIntegral S.idealSheaf.subscheme]
    {j k : ℕ} {h h' : S.idealSheaf.subscheme.functionField}
    (hh : h ∈ imageSeries D S j) (hh' : h' ∈ imageSeries D S k) :
    h * h' ∈ imageSeries D S (j + k) := by
  have gen : ∀ x ∈ {h | ∃ g ∈ sectionsIn ((j : ℤ) • D), IsRestrictionAlong S g h},
      ∀ y ∈ {h | ∃ g ∈ sectionsIn ((k : ℤ) • D), IsRestrictionAlong S g h},
      x * y ∈ imageSeries D S (j + k) := by
    rintro x ⟨g, hg, a, ha1, ha2⟩ y ⟨g', hg', a', ha1', ha2'⟩
    refine AddSubgroup.subset_closure ⟨g * g', fun P => ?_, a * a', ?_, ?_⟩
    · rw [map_mul]
      calc _ ≤ WithZero.exp (((j : ℤ) • D).coeff P) * WithZero.exp (((k : ℤ) • D).coeff P) :=
            mul_le_mul' (hg P) (hg' P)
        _ = _ := by
          rw [← WithZero.exp_add]
          congr 1
          simp only [DivisorWithCoeffs.coeff_smul, Nat.cast_add, add_smul,
            DivisorWithCoeffs.coeff_add]
    · rw [map_mul, ha1, ha1']
    · rw [map_mul, ha2, ha2']
  refine AddSubgroup.closure_induction (p := fun h _ => h * h' ∈ imageSeries D S (j + k))
    ?_ ?_ ?_ ?_ hh
  · intro x hx
    refine AddSubgroup.closure_induction (p := fun y _ => x * y ∈ imageSeries D S (j + k))
      (fun y hy => gen x hx y hy) ?_ ?_ ?_ hh'
    · simp
    · intro y z _ _ hy hz; rw [mul_add]; exact add_mem hy hz
    · intro y _ hy; rw [mul_neg]; exact neg_mem hy
  · simp
  · intro x y _ _ hx hy; rw [add_mul]; exact add_mem hx hy
  · intro x _ hx; rw [neg_mul]; exact neg_mem hx

/-- Every nonzero rational `1`-canonical form is a nonzero rational top form. -/
theorem exists_toPluriForms_eq {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) :
    ∃ ω : RationalTopForms sX n, ω ≠ 0 ∧ ω.toPluriForms sX = τ := by
  letI := functionFieldAlgebra sX
  have hω : RationalTopForms.toPluriForms sX (PiTensorProduct.subsingletonEquiv
      (R := X.functionField) (s := fun _ : Fin 1 => ⋀[X.functionField]^n Ω[X.functionField⁄k])
      0 τ : RationalTopForms sX n) = τ := by
    change PiTensorProduct.tprod X.functionField (fun _ : Fin 1 => PiTensorProduct.subsingletonEquiv
      (R := X.functionField) (s := fun _ : Fin 1 => ⋀[X.functionField]^n Ω[X.functionField⁄k])
      0 τ) = τ
    rw [← PiTensorProduct.subsingletonEquiv_symm_apply' (i₀ := (0 : Fin 1))]
    exact LinearEquiv.symm_apply_apply _ _
  refine ⟨_, fun h0 => hτ ?_, hω⟩
  rw [← hω, h0]
  change PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
    (0 : ⋀[X.functionField]^n Ω[X.functionField⁄k])) = 0
  exact MultilinearMap.map_coord_zero _ (0 : Fin 1) rfl

/-- **Adjunction for a smooth prime divisor.** On a smooth normal variety `X` with canonical
divisor `K` of coefficient `-1` along a prime divisor `S`, the restriction `(K + S)|_S` is a
canonical divisor of `S`: `K` is the divisor of a rational top form `σ` with a simple pole along
`S`, and `(K + S)|_S` is the divisor of its Poincaré residue. -/
theorem isCanonicalDivisor_restrictPrimeDivisor_add_single {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX (n + 1)) (S : MMP.Mori.PrimeDivisor X)
    [IsIntegral S.idealSheaf.subscheme] [IsLocallyNoetherian S.idealSheaf.subscheme]
    [IsNormal S.idealSheaf.subscheme] (hKS : K.coeff S = -1) :
    Divisor.IsCanonicalDivisor (S.idealSheaf.subschemeι ≫ sX) n
      ((K + Finsupp.single S 1).restrictPrimeDivisor S) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : CompactSpace S.idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace S.idealSheaf.subschemeι
  have : IsNoetherian X := {}
  have hdim : topologicalKrullDim X = n + 1 := by
    rw [hK.topologicalKrullDim_eq]; push_cast; rfl
  have h := adjunction_restrict_of_isCartierAt_coheight_eq_two sX hX hdim
    (J := Unit) (T := fun _ => S.idealSheaf.subscheme) (fun _ => S.idealSheaf.subschemeι)
    (fun _ => S) (fun _ => Scheme.IdealSheafData.range_subschemeι S.idealSheaf)
    (fun a b hab => (hab (Subsingleton.elim a b)).elim)
    (fun x _ _ => by
      obtain ⟨U, hxU, φ, hφ⟩ := isCartier_of_isSmoothScheme hsm _ x
      exact MMP.Flips.isCartierAt_of_isLocalEquation hxU hφ)
    0 (fun _ => rfl) K hK ?_
  obtain ⟨ω₀, hω₀, hord⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨σ, hσ0, hσ⟩ := exists_toPluriForms_eq hω₀
  have hdivσ : topFormDivisor sX σ = K :=
    Finsupp.ext fun P => by
      change (topFormDivisor sX σ).coeff P = K.coeff P
      rw [coeff_topFormDivisor, hσ, hord]
  obtain ⟨-, hres⟩ := h.2.2.1 σ hσ0 (fun _ => by rw [hσ, hord, hKS])
  obtain ⟨⟨ρ, hρ⟩, hρ'⟩ := hres ()
  obtain ⟨hcanρ, heq⟩ := hρ' ρ hρ
  have hKS0 : (K + Finsupp.single S 1).coeff S = 0 := by
    rw [DivisorWithCoeffs.coeff_add, hKS]
    change -1 + (Finsupp.single S (1 : ℤ)) S = 0
    rw [Finsupp.single_eq_same]; rfl
  have : (K + Finsupp.single S 1).restrictPrimeDivisor S = divisorOfForm ρ := by
    apply Divisor.toQDivisor_injective
    rw [← MMP.Mori.Divisor.restrictPrimeDivisor_toQDivisor _ _ hKS0, map_add]
    rw [hdivσ, add_zero, Fintype.sum_unique] at heq
    refine heq.trans ?_
    have h0 : DivisorWithCoeffs.restrict S.idealSheaf.subschemeι (0 : QDivisor X) = 0 := by
      unfold DivisorWithCoeffs.restrict
      split_ifs
      · ext Q
        change DivisorWithCoeffs.restrictCoeff S.idealSheaf.subschemeι 0 Q = 0
        simp [DivisorWithCoeffs.restrictCoeff]
      · rfl
    rw [h0, add_zero]
  · rw [this]
    exact hcanρ
  · exact ⟨1, one_ne_zero, ⟨K + ∑ _ : Unit, Finsupp.single S 1, by simp,
      isCartier_of_isSmoothScheme hsm _⟩⟩

/-- The valuation `v_E` on the factor of `K(X)` at the component of `E` is the inverse of the
divisorial valuation of the corresponding rational function. -/
theorem valuation_eq_inv_divisorialValuation' {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : MMP.Mori.PrimeDivisor X)
    (s : X.presheaf.stalk (componentGenericPoint X E.component)) :
    E.valuation s = (E.divisorialValuation
      ((X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial :
        genericPoint X ⤳ componentGenericPoint X E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

/-- A section of `𝒪_X(E)` in the function field is a section of `𝒪_X(E)` in `K(X)`. -/
theorem symm_mem_divisorialSections {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (E : Divisor X) {h : X.functionField} (hh : h ∈ sectionsIn E) :
    (rationalFunctionsEquivFunctionField X).symm h ∈ divisorialSections E := by
  by_cases h0 : h = 0
  · rw [h0, map_zero]; exact zero_mem _
  intro P hP
  change P.OrdGE (-E.coeff P) ((rationalFunctionsEquivFunctionField X).symm h P.component)
  right
  rw [valuation_eq_inv_divisorialValuation', MMP.Positivity.componentToFunctionField_symm_apply]
  have := hh P
  have hv0 : P.divisorialValuation h ≠ 0 := (_root_.map_ne_zero _).mpr h0
  rw [← WithZero.exp_log hv0] at this ⊢
  rw [WithZero.exp_le_exp] at this
  rw [← WithZero.exp_neg, WithZero.exp_le_exp]
  omega

/-- **Restricted sections are sections of the restricted divisor.** On a smooth `X`, the
restriction to a smooth prime divisor `S` of a section of `𝒪_X(D)`, `S` not a component of `D`,
is a section of `𝒪_S(D|_S)`: its order along `Q` is `∑_E length · ord_E`, which is at least
`-∑_E length · d_E`. -/
theorem mem_sectionsIn_restrictPrimeDivisor {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [Smooth sX] (S : MMP.Mori.PrimeDivisor X) [IsIntegral S.idealSheaf.subscheme]
    [IsLocallyNoetherian S.idealSheaf.subscheme] [IsNormal S.idealSheaf.subscheme]
    [Smooth (S.idealSheaf.subschemeι ≫ sX)] (D : Divisor X) (hDS : D.coeff S = 0)
    {g : X.functionField} (hg : g ∈ sectionsIn D) {h : S.idealSheaf.subscheme.functionField}
    (hres : IsRestrictionAlong S g h) : h ∈ sectionsIn (D.restrictPrimeDivisor S) := by
  classical
  haveI : IsNoetherian X := {}
  intro Q
  by_cases h0 : h = 0
  · rw [h0, map_zero]; exact zero_le'
  obtain ⟨a, ha1, ha2⟩ := hres
  have hunit : IsUnit a := by
    have : IsUnit ((S.idealSheaf.subschemeι.stalkMap
        (genericPoint S.idealSheaf.subscheme)).hom a) := by
      rw [ha2]; exact IsUnit.mk0 _ h0
    exact isUnit_of_map_unit _ _ this
  have hga : algebraMap _ X.functionField a = g := by
    change (X.presheaf.stalkSpecializes _).hom a = g
    exact ha1
  have hg0 : g ≠ 0 := by
    rw [← hga]; exact (hunit.map _).ne_zero
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero hg0
  set s := (MMP.Mori.principalDivisor φ).support ∪ D.support with hs
  have key := MMP.Mori.PrimeDivisor.ord_restrict_eq_sum_intersectionLength_mul_ord sX
    S.idealSheaf.subschemeι a hunit Q
    s (fun E hE => by
      rw [hga] at hE
      refine Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr ?_)
      change (MMP.Mori.principalDivisor φ).coeff E ≠ 0
      rw [MMP.Mori.coeff_principalDivisor, hφ]; exact hE)
  rw [ha2, hga] at key
  have hDs : ∑ E ∈ D.support, E.intersectionLength S.idealSheaf.subschemeι Q • D E =
      ∑ E ∈ s, E.intersectionLength S.idealSheaf.subschemeι Q • D E :=
    Finset.sum_subset Finset.subset_union_right
      (fun E _ hE => by rw [Finsupp.notMem_support_iff.mp hE, smul_zero])
  rw [Q.divisorialValuation_eq_exp_neg_ord h0, WithZero.exp_le_exp,
    DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ hDS, key, Finsupp.sum, hDs,
    neg_le_iff_add_nonneg, ← Finset.sum_add_distrib]
  refine Finset.sum_nonneg fun E _ => ?_
  have hE := hg E
  rw [E.divisorialValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp] at hE
  rw [nsmul_eq_mul, ← mul_add]
  exact mul_nonneg (Nat.cast_nonneg _) (by change 0 ≤ D.coeff E + _; omega)

/-- The round-down of an integral `ℚ`-divisor is the divisor. -/
theorem roundDown_toQDivisor' {X : Scheme.{0}} (D : Divisor X) :
    (Divisor.toQDivisor D).roundDown = D :=
  Finsupp.ext fun P => by
    change ((Divisor.toQDivisor D).roundDown).coeff P = D.coeff P
    rw [DivisorWithCoeffs.coeff_roundDown, Divisor.coeff_toQDivisor, Int.floor_intCast]

/-- If `qΔ` is integral and `m = jq`, then `(j(qK + ⌊qΔ⌋))|_S = m (K + S)|_S + ⌊m (A + B)|_S⌋`. -/
theorem restrictPrimeDivisor_smul_eq {X : Scheme.{0}} [IsLocallyNoetherian X] [CompactSpace X]
    (K : Divisor X) (S : MMP.Mori.PrimeDivisor X) (A B Δ : QDivisor X)
    (hΔ : Δ = Divisor.toQDivisor (Finsupp.single S 1) + A + B) (hKS : K.coeff S = -1)
    (hABS : (A + B).coeff S = 0) (q j m : ℕ) (hm : m = j * q) (D' : Divisor X)
    (hD' : Divisor.toQDivisor D' = (q : ℚ) • Δ) :
    ((j : ℤ) • ((q : ℤ) • K + ((q : ℚ) • Δ).roundDown)).restrictPrimeDivisor S =
      m • (K + Finsupp.single S 1).restrictPrimeDivisor S +
        ((m : ℚ) • (A + B).restrictPrimeDivisor S).roundDown := by
  set E' : Divisor X := D' - (q : ℤ) • Finsupp.single S 1 with hE'def
  have hE : Divisor.toQDivisor E' = (q : ℤ) • (A + B) := by
    refine Finsupp.ext fun P => ?_
    have := congrArg (fun G : QDivisor X => G.coeff P) hD'
    change ((DivisorWithCoeffs.coeff (D' - (q : ℤ) • Finsupp.single S (1 : ℤ)) P : ℤ) : ℚ) =
      DivisorWithCoeffs.coeff ((q : ℤ) • (A + B)) P
    simp only [Divisor.coeff_toQDivisor, hΔ, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub] at this ⊢
    push_cast
    rw [this]
    simp only [smul_eq_mul, zsmul_eq_mul, Int.cast_natCast]
    by_cases hPS : P = S
    · subst hPS
      simp [DivisorWithCoeffs.coeff_single_self]
      ring
    · simp [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hPS)]
  have hES : E'.coeff S = 0 := by
    have := congrArg (fun G : QDivisor X => G.coeff S) hE
    simp only [Divisor.coeff_toQDivisor] at this
    have h2 : ((q : ℤ) • (A + B)).coeff S = 0 := by
      change (q : ℤ) • (A + B).coeff S = 0
      rw [hABS, smul_zero]
    rw [h2] at this
    exact_mod_cast this
  have hKS0 : (K + Finsupp.single S 1).coeff S = 0 := by
    rw [DivisorWithCoeffs.coeff_add, hKS]
    change -1 + (Finsupp.single S (1 : ℤ)) S = 0
    rw [Finsupp.single_eq_same]; rfl
  have hround : ((q : ℚ) • Δ).roundDown = D' := by rw [← hD', roundDown_toQDivisor']
  have hsplit : (j : ℤ) • ((q : ℤ) • K + ((q : ℚ) • Δ).roundDown) =
      (m : ℤ) • (K + Finsupp.single S 1) + (j : ℤ) • E' := by
    rw [hround, hE'def, hm]
    push_cast
    module
  have hjE : ((j : ℤ) • E').coeff S = 0 := by
    rw [DivisorWithCoeffs.coeff_smul, hES, smul_zero]
  have hmK : ((m : ℤ) • (K + Finsupp.single S 1)).coeff S = 0 := by
    rw [DivisorWithCoeffs.coeff_smul, hKS0, smul_zero]
  rw [hsplit, MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor_add _ _ _ hmK hjE,
    MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor_zsmul _ _ hKS0,
    MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor_zsmul _ _ hES, natCast_zsmul]
  congr 1
  have hΩ : (m : ℚ) • (A + B).restrictPrimeDivisor S =
      Divisor.toQDivisor ((j : ℤ) • E'.restrictPrimeDivisor S) := by
    rw [map_zsmul, ← MMP.Mori.Divisor.restrictPrimeDivisor_toQDivisor _ _ hES, hE,
      MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor_zsmul _ _ hABS, smul_smul, hm,
      ← Int.cast_smul_eq_zsmul ℚ]
    congr 1
  rw [hΩ, roundDown_toQDivisor']

/-- A section of `𝒪_X(E)` in `K(X)`, read in the function field, is a section of `𝒪_X(E)`. -/
theorem mem_sectionsIn_of_mem_divisorialSections {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : Divisor X) {φ : RationalFunctions X}
    (hφ : φ ∈ divisorialSections E) :
    rationalFunctionsEquivFunctionField X φ ∈ sectionsIn E := by
  intro P
  set h := rationalFunctionsEquivFunctionField X φ with hh
  by_cases h0 : h = 0
  · rw [h0, map_zero]; exact zero_le'
  have hP := hφ P ⟨P.genericPoint, by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩
  change P.OrdGE (-E.coeff P) (φ P.component) at hP
  have hφh : φ = (rationalFunctionsEquivFunctionField X).symm h := by
    rw [hh, RingEquiv.symm_apply_apply]
  rcases hP with hz | hz
  · exfalso; apply h0
    rw [← MMP.Positivity.componentToFunctionField_symm_apply P.component h, ← hφh, hz, map_zero]
  · rw [valuation_eq_inv_divisorialValuation', hφh,
      MMP.Positivity.componentToFunctionField_symm_apply] at hz
    have hv0 : P.divisorialValuation h ≠ 0 := (_root_.map_ne_zero _).mpr h0
    rw [← WithZero.exp_log hv0] at hz ⊢
    rw [← WithZero.exp_neg, WithZero.exp_le_exp] at hz
    rw [WithZero.exp_le_exp]
    omega

/-! ### Relative ampleness of `εD + A` -/

open MMP.Flips.Internal.RelativeRealAmplePerturbation in
/-- **Openness of ampleness at `A = H/a`.** If `H` is a `π`-ample Cartier divisor, `a, q > 0`
and `qD` is an integral Cartier divisor, then `εD + H/a` has a `π`-ample Cartier multiple for
some rational `0 < ε < 1`. -/
private theorem exists_hasRelativelyAmpleMultiple_smul_add {X Z : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [CompactSpace Z] (π : X ⟶ Z)
    [QuasiCompact π] {H : Divisor X} (hH : MMP.Flips.IsRelativelyAmpleCartier π H) {a q : ℕ}
    (ha : 0 < a) (hq : 0 < q) {D : QDivisor X} {E : Divisor X} (hE : E.IsCartier)
    (hED : Divisor.toQDivisor E = (q : ℚ) • D) :
    ∃ ε : ℚ, 0 < ε ∧ ε < 1 ∧
      (ε • D + (a : ℚ)⁻¹ • Divisor.toQDivisor H).HasRelativelyAmpleMultiple π := by
  obtain ⟨m, hmA, hmq⟩ := ((eventually_isRelativelyAmpleCartier_nsmul_add π hH
    (hE.nsmul a)).and (Filter.eventually_gt_atTop q)).exists
  have hm0 : 0 < m := hq.trans hmq
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  refine ⟨(q : ℚ) / m, by positivity, (div_lt_one hmQ).mpr (by exact_mod_cast hmq), a * m,
    Nat.mul_pos ha hm0, m • H + a • E, hmA.1, ?_, ?_⟩
  · refine Finsupp.ext fun P => ?_
    have h1 := congrArg (fun G : QDivisor X => G.coeff P) hED
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h1
    change ((DivisorWithCoeffs.coeff (m • H + a • E) P : ℤ) : ℚ) =
      DivisorWithCoeffs.coeff (((a * m : ℕ) : ℤ) • (((q : ℚ) / m) • D +
        (a : ℚ)⁻¹ • Divisor.toQDivisor H)) P
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
      smul_eq_mul, nsmul_eq_mul, zsmul_eq_mul]
    push_cast
    rw [h1]
    field_simp
    ring
  · obtain ⟨hWc, hamp⟩ := hmA
    have := hWc.isInvertibleModule_divisorialSheaf
    intro y
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨V, hV, hyV, hamp V hV⟩

/-! ### Divisor arithmetic -/

/-- The round-down of an integral divisor plus a `ℚ`-divisor. -/
private theorem roundDown_toQDivisor_add {Y : Scheme.{0}} (E : Divisor Y) (G : QDivisor Y) :
    (Divisor.toQDivisor E + G).roundDown = E + G.roundDown :=
  Finsupp.ext fun P => by
    change ((Divisor.toQDivisor E + G).roundDown).coeff P = (E + G.roundDown).coeff P
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown,
      Int.floor_intCast_add]

/-- `(qj)(K + Δ)` is the integral divisor `j(qK + ⌊qΔ⌋)` when `qΔ` is integral. -/
private theorem toQDivisor_zsmul_eq {Y : Scheme.{0}} (K : Divisor Y) (Δ : QDivisor Y) (q j : ℕ)
    (D' : Divisor Y) (hD' : Divisor.toQDivisor D' = (q : ℚ) • Δ) :
    Divisor.toQDivisor ((j : ℤ) • ((q : ℤ) • K + D')) =
      ((q * j : ℕ) : ℚ) • (Divisor.toQDivisor K + Δ) := by
  refine Finsupp.ext fun P => ?_
  have h1 := congrArg (fun G : QDivisor Y => G.coeff P) hD'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h1
  change ((DivisorWithCoeffs.coeff ((j : ℤ) • ((q : ℤ) • K + D')) P : ℤ) : ℚ) =
    DivisorWithCoeffs.coeff (((q * j : ℕ) : ℚ) • (Divisor.toQDivisor K + Δ)) P
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
    smul_eq_mul]
  push_cast
  rw [h1]
  ring

/-- `⌊(qj)(K + Δ)⌋ = j(qK + ⌊qΔ⌋)` when `qΔ` is integral. -/
private theorem roundDown_natCast_smul_eq {Y : Scheme.{0}} (K : Divisor Y) (Δ : QDivisor Y)
    (q j : ℕ) (D' : Divisor Y) (hD' : Divisor.toQDivisor D' = (q : ℚ) • Δ) :
    (((q * j : ℕ) : ℚ) • (Divisor.toQDivisor K + Δ)).roundDown =
      (j : ℤ) • ((q : ℤ) • K + ((q : ℚ) • Δ).roundDown) := by
  have hround : ((q : ℚ) • Δ).roundDown = D' := by rw [← hD', roundDown_toQDivisor']
  rw [hround, ← toQDivisor_zsmul_eq K Δ q j D' hD', roundDown_toQDivisor']

/-- `⌊k(K + Ω - P)⌋ = kK + ⌊k(Ω - P)⌋`. -/
private theorem roundDown_smul_toQDivisor_add_sub {Y : Scheme.{0}} (K : Divisor Y)
    (Ω P : QDivisor Y) (k : ℕ) :
    ((k : ℚ) • (Divisor.toQDivisor K + Ω - P)).roundDown =
      k • K + ((k : ℚ) • (Ω - P)).roundDown := by
  have : (k : ℚ) • (Divisor.toQDivisor K + Ω - P) =
      Divisor.toQDivisor (k • K) + (k : ℚ) • (Ω - P) := by
    refine Finsupp.ext fun Q => ?_
    change DivisorWithCoeffs.coeff ((k : ℚ) • (Divisor.toQDivisor K + Ω - P)) Q =
      DivisorWithCoeffs.coeff (Divisor.toQDivisor (k • K) + (k : ℚ) • (Ω - P)) Q
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [this, roundDown_toQDivisor_add]

/-! ### The coefficientwise minimum is monotone -/

open scoped ENNReal in
private theorem coeffwiseMin_mono {Y : Scheme.{0}} (Ω : QDivisor Y)
    {F₁ F₂ : MMP.Mori.PrimeDivisor Y → ℝ≥0∞} (h : ∀ G, F₁ G ≤ F₂ G) :
    coeffwiseMin Ω F₁ ≤ coeffwiseMin Ω F₂ := fun G => by
  change (coeffwiseMin Ω F₁).coeff G ≤ (coeffwiseMin Ω F₂).coeff G
  rw [coeff_coeffwiseMin, coeff_coeffwiseMin]
  exact ENNReal.toReal_mono ((min_le_left _ _).trans_lt ENNReal.ofReal_lt_top).ne
    (min_le_min le_rfl (h G))

/-! ### The restricted systems of `D = K + Δ` and the image series of `qK + ⌊qΔ⌋` -/

/-- The restricted system `|mD|_S` at `m = qj`, as a subgroup of `K(S)`, is the image series of
`qK + ⌊qΔ⌋` in degree `j`, when `qΔ` is integral and `X` is smooth. -/
private theorem mem_closure_restrictedSystem_iff {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hsm : IsSmoothScheme sX) (K : Divisor X) (Δ : QDivisor X) (S : MMP.Mori.PrimeDivisor X)
    [IsIntegral S.idealSheaf.subscheme] (q j : ℕ) (D' : Divisor X)
    (hD' : Divisor.toQDivisor D' = (q : ℚ) • Δ) (s : RationalFunctions S.idealSheaf.subscheme) :
    s ∈ AddSubgroup.closure
        {h | (((q * j : ℕ) : ℚ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor ∧
          ∃ g ∈ sectionsIn
            (DivisorWithCoeffs.roundDown (((q * j : ℕ) : ℚ) • (Divisor.toQDivisor K + Δ))),
            IsRestrictionAlong S g (rationalFunctionsEquivFunctionField _ h)} ↔
      rationalFunctionsEquivFunctionField _ s ∈
        imageSeries ((q : ℤ) • K + ((q : ℚ) • Δ).roundDown) S j := by
  set e := rationalFunctionsEquivFunctionField S.idealSheaf.subscheme
  have hcart : (((q * j : ℕ) : ℚ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor :=
    ⟨(j : ℤ) • ((q : ℤ) • K + D'), toQDivisor_zsmul_eq K Δ q j D' hD',
      isCartier_of_isSmoothScheme hsm _⟩
  rw [roundDown_natCast_smul_eq K Δ q j D' hD']
  set X₀ : Set S.idealSheaf.subscheme.functionField :=
    {h | ∃ g ∈ sectionsIn ((j : ℤ) • ((q : ℤ) • K + ((q : ℚ) • Δ).roundDown)),
      IsRestrictionAlong S g h} with hX₀
  have hset : {h | (((q * j : ℕ) : ℚ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor ∧
      ∃ g ∈ sectionsIn ((j : ℤ) • ((q : ℤ) • K + ((q : ℚ) • Δ).roundDown)),
        IsRestrictionAlong S g (e h)} = e ⁻¹' X₀ := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hX₀, true_and, hcart]
  rw [hset]
  change _ ↔ e s ∈ AddSubgroup.closure X₀
  constructor
  · intro hs
    refine AddSubgroup.closure_induction (p := fun x _ => e x ∈ AddSubgroup.closure X₀)
      (fun x hx => AddSubgroup.subset_closure hx) ?_ ?_ ?_ hs
    · rw [map_zero]; exact zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
    · intro x _ hx; rw [map_neg]; exact neg_mem hx
  · intro hs
    rw [← e.symm_apply_apply s]
    refine AddSubgroup.closure_induction
      (p := fun x _ => e.symm x ∈ AddSubgroup.closure (e ⁻¹' X₀))
      (fun x hx => AddSubgroup.subset_closure (by
        change e (e.symm x) ∈ X₀
        rwa [RingEquiv.apply_symm_apply])) ?_ ?_ ?_ hs
    · rw [map_zero]; exact zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
    · intro x _ hx; rw [map_neg]; exact neg_mem hx

/-- The reindexed image series `V_m = e⁻¹ W_{m/q}` (for `q ∣ m`, and `0` otherwise) is graded. -/
private theorem mul_mem_of_mem_iff {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (D : Divisor X) (S : MMP.Mori.PrimeDivisor X) [IsIntegral S.idealSheaf.subscheme]
    {R : Type*} [Semiring R] [Module R (RationalFunctions S.idealSheaf.subscheme)]
    (V : ℕ → Submodule R (RationalFunctions S.idealSheaf.subscheme)) (q : ℕ)
    (hVmem : ∀ m s, s ∈ V m ↔ if q ∣ m then
      rationalFunctionsEquivFunctionField _ s ∈ imageSeries D S (m / q) else s = 0) :
    ∀ m n, ∀ s ∈ V m, ∀ t ∈ V n, s * t ∈ V (m + n) := by
  intro m n s hs t ht
  rw [hVmem] at hs ht ⊢
  by_cases hm : q ∣ m
  · by_cases hn : q ∣ n
    · rw [if_pos hm] at hs
      rw [if_pos hn] at ht
      rw [if_pos (dvd_add hm hn), map_mul, Nat.add_div_of_dvd_right hm]
      exact mul_mem_imageSeries_add D S hs ht
    · rw [if_neg hn] at ht
      split_ifs <;> simp [ht]
  · rw [if_neg hm] at hs
    split_ifs <;> simp [hs]

/-- `S` is not a component of `j(qK + ⌊qΔ⌋)`. -/
private theorem coeff_zsmul_qDivisor_eq_zero {X : Scheme.{0}} (K : Divisor X)
    (S : MMP.Mori.PrimeDivisor X) (A B Δ : QDivisor X)
    (hΔ : Δ = Divisor.toQDivisor (Finsupp.single S 1) + A + B) (hKS : K.coeff S = -1)
    (hABS : (A + B).coeff S = 0) (q : ℕ) (D' : Divisor X)
    (hD' : Divisor.toQDivisor D' = (q : ℚ) • Δ) (j : ℕ) :
    ((j : ℤ) • ((q : ℤ) • K + ((q : ℚ) • Δ).roundDown)).coeff S = 0 := by
  have hround : ((q : ℚ) • Δ).roundDown = D' := by rw [← hD', roundDown_toQDivisor']
  have h1 := congrArg (fun G : QDivisor X => G.coeff S) hD'
  simp only [Divisor.coeff_toQDivisor] at h1
  have h2 : ((q : ℚ) • Δ).coeff S = q := by
    change (q : ℚ) * Δ.coeff S = q
    rw [hΔ]
    change (q : ℚ) * (((Finsupp.single S (1 : ℤ)) S : ℚ) + A.coeff S + B.coeff S) = q
    have : A.coeff S + B.coeff S = 0 := hABS
    rw [Finsupp.single_eq_same, add_assoc, this]; push_cast; ring
  rw [h2] at h1
  have h3 : D'.coeff S = q := by exact_mod_cast h1
  rw [DivisorWithCoeffs.coeff_smul, hround, DivisorWithCoeffs.coeff_add,
    DivisorWithCoeffs.coeff_smul, hKS, h3]
  simp

/-- Restricted sections of `𝒪_X(j(qK + ⌊qΔ⌋))` are sections of `𝒪_S(qj(K_S + Ω))`. -/
private theorem symm_mem_divisorialSections_of_mem_imageSeries {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) (hsm : IsSmoothScheme sX) (K : Divisor X)
    (S : MMP.Mori.PrimeDivisor X) [IsIntegral S.idealSheaf.subscheme]
    [IsLocallyNoetherian S.idealSheaf.subscheme] [IsNormal S.idealSheaf.subscheme]
    (hSsm : IsSmoothScheme (S.idealSheaf.subschemeι ≫ sX)) (A B Δ : QDivisor X)
    (hΔ : Δ = Divisor.toQDivisor (Finsupp.single S 1) + A + B) (hKS : K.coeff S = -1)
    (hABS : (A + B).coeff S = 0) (q : ℕ) (D' : Divisor X)
    (hD' : Divisor.toQDivisor D' = (q : ℚ) • Δ) (j : ℕ) {h : S.idealSheaf.subscheme.functionField}
    (hh : h ∈ imageSeries ((q : ℤ) • K + ((q : ℚ) • Δ).roundDown) S j) :
    (rationalFunctionsEquivFunctionField _).symm h ∈ divisorialSections
      ((q * j) • (K + Finsupp.single S 1).restrictPrimeDivisor S +
        (((q * j : ℕ) : ℚ) • (A + B).restrictPrimeDivisor S).roundDown) := by
  have : Smooth sX := MMP.Mori.IsSmoothScheme.smooth hsm
  have : Smooth (S.idealSheaf.subschemeι ≫ sX) := MMP.Mori.IsSmoothScheme.smooth hSsm
  rw [← restrictPrimeDivisor_smul_eq K S A B Δ hΔ hKS hABS q j (q * j) (mul_comm _ _) D' hD']
  refine AddSubgroup.closure_induction
    (p := fun h _ => (rationalFunctionsEquivFunctionField _).symm h ∈ divisorialSections _)
    ?_ ?_ ?_ ?_ hh
  · rintro h ⟨g, hg, hres⟩
    exact symm_mem_divisorialSections _ (mem_sectionsIn_restrictPrimeDivisor sX S _
      (coeff_zsmul_qDivisor_eq_zero K S A B Δ hΔ hKS hABS q D' hD' j) hg hres)
  · rw [map_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro x _ hx; rw [map_neg]; exact neg_mem hx

/-! ### Fixed parts -/

open scoped ENNReal in
/-- **The two asymptotic fixed parts.** Let `V` be a graded series whose sections in degrees
divisible by `q` are sections of `m(K + Ω)` with `mΩ` integral, and let `W` be a family agreeing
with `V` in the degrees divisible by `q`. The factorial limit `F_W = inf_n F_{W, n!}` of `W` is
at most every normalized fixed part `F_{V, qN}`, `N > 0`, of `V`. -/
private theorem restrictedAsymptoticFixedPart_one_le {S : Scheme.{0}} [IsIntegral S]
    [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S] {R : Type*} [Semiring R]
    [Module R (RationalFunctions S)] (K : Divisor S) (Ω : QDivisor S) {q : ℕ} (hq : 0 < q)
    (V : ℕ → Submodule R (RationalFunctions S)) (W : ℕ → Submodule ℤ (RationalFunctions S))
    (hsame : ∀ m, q ∣ m → ∀ s, s ∈ W m ↔ s ∈ V m)
    (hmul : ∀ m n, ∀ s ∈ V m, ∀ t ∈ V n, s * t ∈ V (m + n))
    (hmem : ∀ m, q ∣ m → ∀ s ∈ V m, s ∈ divisorialSections (seriesDivisor K Ω m))
    (hint : ∀ m, q ∣ m → ∀ P : MMP.Mori.PrimeDivisor S, ∃ z : ℤ, (m : ℚ) * Ω.coeff P = z)
    {N : ℕ} (hN : 0 < N) (G : MMP.Mori.PrimeDivisor S) :
    restrictedAsymptoticFixedPart K Ω 1 W G ≤ restrictedNormalizedFixedPart K Ω V (q * N) G := by
  have hqN : 0 < q * N := Nat.mul_pos hq hN
  have hdvd : q ∣ (q * N).factorial := Nat.dvd_factorial hq (Nat.le_mul_of_pos_right q hN)
  have h1 : restrictedAsymptoticFixedPart K Ω 1 W G ≤
      restrictedNormalizedFixedPart K Ω W (1 * (q * N).factorial) G :=
    iInf_le_of_le (q * N) (iInf_le_of_le hqN le_rfl)
  rw [one_mul] at h1
  have h2 : restrictedNormalizedFixedPart K Ω W (q * N).factorial G =
      restrictedNormalizedFixedPart K Ω V (q * N).factorial G := by
    unfold restrictedNormalizedFixedPart restrictedFixedMultiplicity
    congr 2
    exact iInf_congr fun s => iInf_congr_Prop (hsame _ hdvd s) fun _ => rfl
  have h3 := restrictedNormalizedFixedPart_mul_le hmul (hmem _ (dvd_mul_right q N))
    (fun s hs => hmem _ (dvd_mul_of_dvd_right (dvd_mul_right q N) _) s hs)
    (hint _ (dvd_mul_right q N)) (Nat.factorial_pos (q * N - 1)) G
  rw [mul_comm, Nat.mul_factorial_pred hqN.ne'] at h3
  rw [h2] at h1
  exact h1.trans h3

/-- The fixed multiplicity along `G` of a series containing the section `h` is at most `k` when
`v_G(h) ≥ exp(c - k)`, `c` the coefficient of `G` in the divisor of the series. -/
private theorem restrictedFixedMultiplicity_le_of_le_divisorialValuation {S : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S] {R : Type*} [Semiring R]
    [Module R (RationalFunctions S)] {K : Divisor S} {Ω : QDivisor S}
    {V : ℕ → Submodule R (RationalFunctions S)} {m : ℕ} {h : S.functionField}
    (hV : (rationalFunctionsEquivFunctionField S).symm h ∈ V m)
    (hs : (rationalFunctionsEquivFunctionField S).symm h ∈
      divisorialSections (seriesDivisor K Ω m))
    (h0 : h ≠ 0) (G : MMP.Mori.PrimeDivisor S) (c k : ℤ)
    (hc : (seriesDivisor K Ω m).coeff G = c)
    (hval : WithZero.exp (c - k) ≤ G.divisorialValuation h) :
    restrictedFixedMultiplicity K Ω V m G ≤ (k.toNat : ℕ∞) := by
  have hs0 : (rationalFunctionsEquivFunctionField S).symm h ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (rationalFunctionsEquivFunctionField S).symm.injective]
  obtain ⟨χ, hχ, -⟩ := exists_unit_of_mem_divisorialSections hs hs0
  refine (restrictedFixedMultiplicity_le_toNat hV hs hs0 hχ G).trans ?_
  have hv : G.divisorialValuation h = (WithZero.exp (G.ord χ))⁻¹ := by
    have h1 := valuation_eq_inv_divisorialValuation' G ((χ : RationalFunctions S) G.component)
    rw [G.valuation_component, hχ, MMP.Positivity.componentToFunctionField_symm_apply] at h1
    rw [h1, inv_inv]
  rw [hv, ← WithZero.exp_neg, WithZero.exp_le_exp] at hval
  rw [hc]
  exact_mod_cast Int.toNat_le_toNat (by omega)

/-- A function whose restriction to `S` is nonzero is a unit at the generic point of `S`. -/
private theorem divisorialValuation_eq_one_of_isRestrictionAlong {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (S : MMP.Mori.PrimeDivisor X)
    [IsIntegral S.idealSheaf.subscheme] {g : X.functionField}
    {h : S.idealSheaf.subscheme.functionField} (hres : IsRestrictionAlong S g h) (h0 : h ≠ 0) :
    S.divisorialValuation g = 1 := by
  obtain ⟨a, ha1, ha2⟩ := hres
  have hunit : IsUnit a := by
    have : IsUnit ((S.idealSheaf.subschemeι.stalkMap
        (genericPoint S.idealSheaf.subscheme)).hom a) := by
      rw [ha2]; exact IsUnit.mk0 _ h0
    exact isUnit_of_map_unit _ _ this
  obtain ⟨u, rfl⟩ := hunit
  have hle : ∀ r : X.presheaf.stalk (S.idealSheaf.subschemeι
      (genericPoint S.idealSheaf.subscheme)),
      S.divisorialValuation (X.presheaf.stalkSpecializes (genericPoint_specializes _) r) ≤ 1 :=
    fun r => (MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff S _).mpr ⟨r, rfl⟩
  have hmul : S.divisorialValuation
      (X.presheaf.stalkSpecializes (genericPoint_specializes _) u.val) *
      S.divisorialValuation
        (X.presheaf.stalkSpecializes (genericPoint_specializes _) u⁻¹.val) =
        1 := by
    rw [← map_mul, ← map_mul, u.mul_inv, map_one, map_one]
  rw [← ha1]
  refine le_antisymm (hle u.val) ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hmul.symm
    _ ≤ _ := mul_le_of_le_one_right' (hle u⁻¹.val)

/-! ### The canonical hypothesis on `S` -/

/-- **The canonical hypothesis of the lifting theorem.** On a smooth `X` of dimension `d + 1`
with a smooth prime divisor `S`, `K_X` of coefficient `-1` along `S` and `A, B ≥ 0` not containing
`S`: if `(X, S + 2A + B)` is plt and `(S, (2A + B)|_S)` is canonical in the sense of
Kollár–Mori, then `(S, (A + B)|_S + A|_S)` is a real canonical pair with no coefficient one. The
coefficients are `< 1` by adjunction (KM 5.46, `(S, (2A + B)|_S)` has total discrepancy `> -1`). -/
private theorem isRealCanonicalPair_restrictPrimeDivisor {d : ℕ} {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    (hXn : IsNormalVariety ℂ sX) (hsm : IsSmoothScheme sX) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX (d + 1)) (S : MMP.Mori.PrimeDivisor X)
    [IsIntegral S.idealSheaf.subscheme] [IsLocallyNoetherian S.idealSheaf.subscheme]
    [IsNormal S.idealSheaf.subscheme] (hKS : K.coeff S = -1)
    (hSsm : IsSmoothScheme (S.idealSheaf.subschemeι ≫ sX))
    (hSn : IsNormalVariety ℂ (S.idealSheaf.subschemeι ≫ sX)) (A B : QDivisor X)
    (hA0 : ∀ P, 0 ≤ A.coeff P) (hB : 0 ≤ B) (hAS : A.coeff S = 0) (hBS : B.coeff S = 0)
    (hplt' : IsPltPair sX (d + 1) K
      (Divisor.toQDivisor (Finsupp.single S 1) + A + B + A))
    (hcan : ∃ KS : Divisor S.idealSheaf.subscheme,
      IsCanonicalPair (S.idealSheaf.subschemeι ≫ sX) d KS ((2 • A + B).restrictPrimeDivisor S)) :
    IsRealCanonicalPair (S.idealSheaf.subschemeι ≫ sX)
      (QDivisor.toRDivisor ((A + B).restrictPrimeDivisor S + A.restrictPrimeDivisor S)) := by
  have : CompactSpace S.idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace S.idealSheaf.subschemeι
  have : IsNoetherian X := {}
  have hABS : (A + B).coeff S = 0 := by
    rw [DivisorWithCoeffs.coeff_add, hAS, hBS, add_zero]
  have h2ABS : (2 • A + B).coeff S = 0 := by
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, hAS, hBS, smul_zero, add_zero]
  have hΘeq : (A + B).restrictPrimeDivisor S + A.restrictPrimeDivisor S =
      (2 • A + B).restrictPrimeDivisor S := by
    rw [← MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor_add _ _ _ hABS hAS]
    congr 1
    abel
  rw [hΘeq]
  set Θ := (2 • A + B).restrictPrimeDivisor S with hΘ
  obtain ⟨KS', hcan'⟩ := hcan
  have hKScan := isCanonicalDivisor_restrictPrimeDivisor_add_single hXn hsm hK S hKS
  set KS := (K + Finsupp.single S 1).restrictPrimeDivisor S
  -- `K_S + Θ` is `ℚ`-Cartier: `S` is smooth and `Θ` has an integral multiple.
  obtain ⟨M, hM, L, hL, -⟩ := hcan'.1.2.2
  have hL' : Divisor.toQDivisor (M • KS + L - M • KS') = M • (Divisor.toQDivisor KS + Θ) := by
    rw [map_sub, map_add, map_zsmul, map_zsmul, hL, smul_add, smul_add]
    abel
  have hqC : (Divisor.toQDivisor KS + Θ).IsQCartier :=
    ⟨M, hM, M • KS + L - M • KS', hL', isCartier_of_isSmoothScheme hSsm _⟩
  have hPS : MMP.Mori.IsPair (S.idealSheaf.subschemeι ≫ sX) Θ := ⟨hSn, d, KS, hKScan, hqC⟩
  -- Adjunction: `(S, Θ)` has total discrepancy `> -1`.
  have hsupp : (Finsupp.single S (1 : ℤ)).support = {S} :=
    Finsupp.support_single_ne_zero _ one_ne_zero
  let T : PairOnNormalDivisor sX :=
    { components := (Finsupp.single S (1 : ℤ)).support
      pairwise_disjoint := by
        rw [hsupp, Finset.coe_singleton]; exact Set.pairwise_singleton _ _
      isNormalVariety := fun E => by
        obtain ⟨E, hE⟩ := E
        rw [hsupp] at hE
        obtain hE' := (Finset.mem_singleton.mp hE).symm
        subst hE'
        exact hSn
      dim := d
      K := fun E => (K + Finsupp.single E.1 1).restrictPrimeDivisor E.1
      Θ := fun E => (2 • A + B).restrictPrimeDivisor E.1
      isCanonicalDivisor := fun E => by
        obtain ⟨E, hE⟩ := E
        rw [hsupp] at hE
        obtain hE' := (Finset.mem_singleton.mp hE).symm
        subst hE'
        exact hKScan
      isQCartier := fun E => by
        obtain ⟨E, hE⟩ := E
        rw [hsupp] at hE
        obtain hE' := (Finset.mem_singleton.mp hE).symm
        subst hE'
        exact hqC }
  have hSred : MMP.Intersection.IsReducedEffective (Finsupp.single S (1 : ℤ) : Divisor X) := by
    intro P
    by_cases hPS : P = S
    · subst hPS; right; exact Finsupp.single_eq_same
    · left; exact Finsupp.single_eq_of_ne' (Ne.symm hPS)
  have hSC : ∀ x ∈ DivisorWithCoeffs.supp (Finsupp.single S (1 : ℤ) : Divisor X),
      Order.coheight x = 2 → MMP.Flips.IsCartierAt (Finsupp.single S (1 : ℤ)) x := fun x _ _ => by
    obtain ⟨U, hxU, φ, hφ⟩ := isCartier_of_isSmoothScheme hsm _ x
    exact MMP.Flips.isCartierAt_of_isLocalEquation hxU hφ
  have hBsupp : ∀ P ∈ (Finsupp.single S (1 : ℤ)).support, (2 • A + B).coeff P = 0 := by
    intro P hP
    rw [hsupp, Finset.mem_singleton] at hP
    rw [hP]; exact h2ABS
  have hΔ'' : Divisor.toQDivisor (Finsupp.single S 1) + (2 • A + B) =
      Divisor.toQDivisor (Finsupp.single S 1) + A + B + A := by abel
  have hKSB : (Divisor.toQDivisor K + Divisor.toQDivisor (Finsupp.single S 1) +
      (2 • A + B)).IsQCartier := by
    have h := hplt'.1.2.2
    rwa [add_assoc, hΔ'']
  have hineq := MMP.Mori.discrepCenterIn_le_totalDiscrepCenterIn_of_components_eq hXn hK
    (Finsupp.single S 1) hSred hSC Set.univ hBsupp hKSB T rfl rfl (fun _ => rfl)
  rw [MMP.Mori.discrepCenterIn_univ, hΔ''] at hineq
  have hlt := hplt'.2.trans_le hineq
  have hE0 : S ∈ T.components := by
    change S ∈ (Finsupp.single S (1 : ℤ)).support
    rw [hsupp]; exact Finset.mem_singleton_self S
  unfold MMP.Mori.PairOnNormalDivisor.totalDiscrepCenterIn at hlt
  have hlt' := hlt.trans_le (iInf_le _ (⟨S, hE0⟩ : T.components))
  simp only [Set.preimage_univ, MMP.Mori.totalDiscrepCenterIn_univ] at hlt'
  -- The three clauses.
  refine ⟨hSn, fun P hP => ?_, ⟨d, KS, hKScan, ?_⟩, fun n E a hE ha => ?_⟩
  · rw [QDivisor.coeff_toRDivisor] at hP ⊢
    have h0 : 0 ≤ Θ.coeff P := by
      rw [hΘ, DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ h2ABS]
      refine Finset.sum_nonneg fun E _ => nsmul_nonneg ?_ _
      change 0 ≤ (2 • A + B).coeff E
      rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul]
      exact add_nonneg (nsmul_nonneg (hA0 E) _) (hB E)
    have hne : Θ.coeff P ≠ 0 := fun h => hP (by rw [h, Rat.cast_zero])
    refine ⟨by exact_mod_cast lt_of_le_of_ne h0 (Ne.symm hne), ?_⟩
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPS hKScan
      (DivisorOver.ofPrimeDivisor ℂ hSn P)
    have h1 := hlt'.trans_le (MMP.Mori.totalDiscrep_le_neg_coeff hSn ⟨c, hc⟩)
    have h2 : ((-1 : ℝ) : EReal) < ((-Θ.coeff P : ℚ) : ℝ) := by simpa using h1
    have h3 := EReal.coe_lt_coe_iff.mp h2
    push_cast at h3
    linarith
  · have hL'c := isCartier_of_isSmoothScheme hSsm (M • KS + L - M • KS')
    set L' := M • KS + L - M • KS'
    refine ⟨1, fun _ => ((M : ℚ) : ℝ)⁻¹, fun _ => L', fun _ => hL'c, fun Γ => ?_⟩
    have h1 := congrArg (fun G : QDivisor S.idealSheaf.subscheme => G.coeff Γ) hL'
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      zsmul_eq_mul] at h1
    have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast hM
    rw [Fin.sum_univ_one]
    change ((KS.coeff Γ : ℤ) : ℝ) + ((Θ.coeff Γ : ℚ) : ℝ) = ((M : ℚ) : ℝ)⁻¹ * ((L'.coeff Γ : ℤ) : ℝ)
    have h2 : ((KS.coeff Γ : ℤ) : ℚ) + Θ.coeff Γ = (M : ℚ)⁻¹ * ((L'.coeff Γ : ℤ) : ℚ) := by
      rw [h1]; field_simp
    have h3 := congrArg (fun x : ℚ => (x : ℝ)) h2
    push_cast at h3 ⊢
    exact h3
  · have hn : n = d := by
      have e := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
        hKScan.topologicalKrullDim_eq
      exact_mod_cast e
    subst hn
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hcan'.1.isPair hcan'.1.2.1 E
    obtain ⟨-, rfl⟩ := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc a).mp ha
    have h1 := hcan'.2.trans (MMP.Mori.discrep_le hE hc)
    have h2 : (0 : ℚ) ≤ c := by simpa using h1
    have h3 : (0 : ℝ) ≤ c := by exact_mod_cast h2
    linarith

/-! ### The lifting clause of the prepared restricted algebra -/

open scoped ENNReal in
/-- **The lifting clause for the prepared restricted algebra, from the fixed-member lifting
theorem.** Let `X → Spec A₀` be projective with `X` smooth of dimension `d + 1`, `S` a smooth prime
divisor, `K` a canonical divisor with coefficient `-1` along `S`, `H ≥ 0` a `π`-ample Cartier
divisor, `A = H/a` with `a ≥ 3`, `B ≥ 0` and `Δ = S + A + B` with `⌊Δ⌋ = S`, `(X, Δ)` and
`(X, Δ + A)` plt and `(S, (2A + B)|_S)` canonical. Let `q > 0` make `qΔ` integral with a nonzero
restricted section in degree one, and suppose no component of `H|_S` lies in the asymptotic fixed
part of the image series `W_j` of `qK + ⌊qΔ⌋` on `S`. Let `V_m = W_{m/q}` for `q ∣ m` and `0`
otherwise. Then the fixed-member lifting theorem gives the lifting inequality of `V`
(the second clause of `MMP.Fourfold.HasRestrictedLiftingProperty`): there is a rational
`0 < ε < 1` such that for every `k > 0` divisible by `q` and every `ℚ`-divisor `P` on `S` with `kP`
integral and `Ω ∧ (1 - ε/k)F ≤ P ≤ Ω`, `F` the asymptotic fixed part of `V` and
`Ω = (A + B)|_S`, every section of `𝒪_S(k(K_S + Ω - P))` lies in `V_k`. -/
theorem exists_forall_mem_of_isPltPair_add (d : ℕ) (hd : 2 ≤ d)
    {A₀ : Type} [CommRing A₀] [IsDomain A₀] [Algebra ℂ A₀] [Algebra.FiniteType ℂ A₀]
    [IsIntegrallyClosed A₀]
    (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (π : X ⟶ Spec (.of A₀))
    (hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A₀)) = sX)
    (hπp : IsProjectiveMorphism π) (hsm : IsSmoothScheme sX)
    (K : Divisor X) (hK : K.IsCanonicalDivisor sX (d + 1))
    (S : MMP.Mori.PrimeDivisor X) [IsIntegral S.idealSheaf.subscheme]
    [IsLocallyNoetherian S.idealSheaf.subscheme] [IsNormal S.idealSheaf.subscheme]
    [CompactSpace S.idealSheaf.subscheme]
    (hKS : K.coeff S = -1) (hSsm : IsSmoothScheme (S.idealSheaf.subschemeι ≫ sX))
    (H : Divisor X) (a : ℕ) (A B Δ : QDivisor X)
    (hH : 0 ≤ H) (hHa : MMP.Flips.IsRelativelyAmpleCartier π H) (ha : 3 ≤ a)
    (hA : A = (a : ℚ)⁻¹ • Divisor.toQDivisor H) (hB : 0 ≤ B)
    (hΔ : Δ = Divisor.toQDivisor (Finsupp.single S 1) + A + B)
    (hfloor : Δ.roundDown = Finsupp.single S 1)
    (hplt : IsPltPair sX (d + 1) K Δ) (hplt' : IsPltPair sX (d + 1) K (Δ + A))
    (hcan : ∃ KS : Divisor S.idealSheaf.subscheme,
      IsCanonicalPair (S.idealSheaf.subschemeι ≫ sX) d KS ((2 • A + B).restrictPrimeDivisor S))
    {T : Scheme.{0}} (g : T ⟶ Spec (.of A₀)) (f : S.idealSheaf.subscheme ⟶ T)
    (q : ℕ) (hq : 0 < q) (hqΔ : ((q : ℚ) • Δ).IsCartierDivisor)
    (hne : imageSeries ((q : ℤ) • K + ((q : ℚ) • Δ).roundDown) S 1 ≠ ⊥)
    (hgen : ∀ Q : MMP.Mori.PrimeDivisor S.idealSheaf.subscheme,
      (H.restrictPrimeDivisor S).coeff Q ≠ 0 → ∀ n : ℕ, 0 < n → ∃ j : ℕ, 0 < j ∧ ∃ k : ℤ,
        (n : ℤ) * k < j ∧ ∃ h ∈ imageSeries ((q : ℤ) • K + ((q : ℚ) • Δ).roundDown) S j,
          h ≠ 0 ∧ WithZero.exp ((j : ℤ) *
            (((q : ℤ) • K + ((q : ℚ) • Δ).roundDown).restrictPrimeDivisor S).coeff Q - k) ≤
              Q.divisorialValuation h)
    (V : ℕ → Submodule (restrictedSeriesBaseMap g f).range
      (RationalFunctions S.idealSheaf.subscheme))
    (hVmem : ∀ m s, s ∈ V m ↔ if q ∣ m then
      rationalFunctionsEquivFunctionField _ s ∈
        imageSeries ((q : ℤ) • K + ((q : ℚ) • Δ).roundDown) S (m / q) else s = 0) :
    ∃ ε : ℚ, 0 < ε ∧ ε < 1 ∧ ∀ k : ℕ, 0 < k → q ∣ k → ∀ P : QDivisor S.idealSheaf.subscheme,
      ((k : ℤ) • P).IsCartierDivisor →
      coeffwiseMin ((A + B).restrictPrimeDivisor S) (fun G => ENNReal.ofReal (1 - (ε : ℝ) / k) *
          restrictedAsymptoticFixedPart ((K + Finsupp.single S 1).restrictPrimeDivisor S)
            ((A + B).restrictPrimeDivisor S) q V G) ≤ QDivisor.toRDivisor P →
      P ≤ (A + B).restrictPrimeDivisor S →
      ∀ s ∈ divisorialSections (k • (K + Finsupp.single S 1).restrictPrimeDivisor S +
          DivisorWithCoeffs.roundDown ((k : ℚ) • ((A + B).restrictPrimeDivisor S - P))),
        s ∈ V k := by
  have : IsNoetherian X := {}
  have : IsNormal (Spec (.of A₀)) := isNormal_spec_of_isIntegrallyClosed _
  have : IsProper π := isProper_of_isProjectiveMorphism _ hπp
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ A₀))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hXn : IsNormalVariety ℂ sX := by
    subst hπ
    exact ⟨(isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
      inferInstance⟩
  have hSn : IsNormalVariety ℂ (S.idealSheaf.subschemeι ≫ sX) := by
    subst hπ
    exact ⟨(isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
      inferInstance⟩
  -- Coefficients along `S`.
  have hA0 : ∀ P, 0 ≤ A.coeff P := fun P => by
    rw [hA]
    change 0 ≤ (a : ℚ)⁻¹ * ((H.coeff P : ℤ) : ℚ)
    have h1 : (0 : ℤ) ≤ H.coeff P := hH P
    have h2 : (0 : ℚ) ≤ (H.coeff P : ℚ) := by exact_mod_cast h1
    positivity
  have hABS : (A + B).coeff S = 0 := by
    have h1 := hplt.isLcPair.coeff_le_one (by omega) S
    have h2 : Δ.coeff S = 1 + A.coeff S + B.coeff S := by
      rw [hΔ]
      change ((Finsupp.single S (1 : ℤ)) S : ℚ) + A.coeff S + B.coeff S = _
      rw [Finsupp.single_eq_same]; push_cast; rfl
    have h3 := hA0 S
    have h4 : 0 ≤ B.coeff S := hB S
    change A.coeff S + B.coeff S = 0
    linarith
  have hABS' : A.coeff S + B.coeff S = 0 := hABS
  have hA0S : 0 ≤ A.coeff S := hA0 S
  have hB0S : 0 ≤ B.coeff S := hB S
  have hAS : A.coeff S = 0 := by linarith
  have hBS : B.coeff S = 0 := by linarith
  have hHS : H.coeff S = 0 := by
    have h1 : A.coeff S = (a : ℚ)⁻¹ * ((H.coeff S : ℤ) : ℚ) := by rw [hA]; rfl
    have ha0 : (a : ℚ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (by omega : a ≠ 0))
    rw [hAS] at h1
    exact_mod_cast (mul_eq_zero.mp h1.symm).resolve_left ha0
  -- `qΔ`, `qD` and `qΩ` are integral.
  obtain ⟨D', hD', -⟩ := hqΔ
  have hDq : Divisor.toQDivisor ((q : ℤ) • K + D') = (q : ℚ) • (Divisor.toQDivisor K + Δ) := by
    have h := toQDivisor_zsmul_eq K Δ q 1 D' hD'
    rwa [Nat.cast_one, one_smul, Nat.mul_one] at h
  have hfl1 : ((q : ℚ) • (Divisor.toQDivisor K + Δ)).roundDown =
      (q : ℤ) • K + ((q : ℚ) • Δ).roundDown := by
    have h := roundDown_natCast_smul_eq K Δ q 1 D' hD'
    rwa [Nat.cast_one, one_smul, Nat.mul_one] at h
  have hDc0 : ((q : ℤ) • K + ((q : ℚ) • Δ).roundDown).coeff S = 0 := by
    have h := coeff_zsmul_qDivisor_eq_zero K S A B Δ hΔ hKS hABS q D' hD' 1
    rwa [Nat.cast_one, one_smul] at h
  have hqΩ : QDivisor.IsCartierDivisor ((q : ℤ) • (A + B).restrictPrimeDivisor S) := by
    have hE : Divisor.toQDivisor (D' - (q : ℤ) • Finsupp.single S 1) = (q : ℤ) • (A + B) := by
      refine Finsupp.ext fun P => ?_
      have := congrArg (fun G : QDivisor X => G.coeff P) hD'
      change ((DivisorWithCoeffs.coeff (D' - (q : ℤ) • Finsupp.single S (1 : ℤ)) P : ℤ) : ℚ) =
        DivisorWithCoeffs.coeff ((q : ℤ) • (A + B)) P
      simp only [Divisor.coeff_toQDivisor, hΔ, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub] at this ⊢
      push_cast
      rw [this]
      simp only [smul_eq_mul, zsmul_eq_mul, Int.cast_natCast]
      by_cases hPS : P = S
      · subst hPS
        simp [DivisorWithCoeffs.coeff_single_self]
        ring
      · simp [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hPS)]
    have hES : (D' - (q : ℤ) • Finsupp.single S 1).coeff S = 0 := by
      have := congrArg (fun G : QDivisor X => G.coeff S) hE
      simp only [Divisor.coeff_toQDivisor] at this
      have h2 : ((q : ℤ) • (A + B)).coeff S = 0 := by
        change (q : ℤ) • (A + B).coeff S = 0
        rw [hABS, smul_zero]
      rw [h2] at this
      exact_mod_cast this
    rw [← MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor_zsmul _ _ hABS, ← hE,
      MMP.Mori.Divisor.restrictPrimeDivisor_toQDivisor _ _ hES]
    exact QDivisor.isCartierDivisor_toQDivisor.mpr (isCartier_of_isSmoothScheme hSsm _)
  -- The rational number `ε`.
  obtain ⟨ε, hε0, hε1, hεA⟩ := exists_hasRelativelyAmpleMultiple_smul_add π hHa
    (by omega : 0 < a) hq (isCartier_of_isSmoothScheme hsm _) hDq
  rw [← hA] at hεA
  -- The restricted systems of the lifting theorem and their fixed part.
  set e := rationalFunctionsEquivFunctionField S.idealSheaf.subscheme
  set Dc := (q : ℤ) • K + ((q : ℚ) • Δ).roundDown
  set KS := (K + Finsupp.single S 1).restrictPrimeDivisor S
  set Ω := (A + B).restrictPrimeDivisor S
  let Vs : ℕ → Submodule ℤ (RationalFunctions S.idealSheaf.subscheme) := fun m =>
    AddSubgroup.toIntSubmodule <| AddSubgroup.closure
      {h | ((m : ℚ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor ∧
        ∃ g ∈ sectionsIn (DivisorWithCoeffs.roundDown ((m : ℚ) • (Divisor.toQDivisor K + Δ))),
          IsRestrictionAlong S g (rationalFunctionsEquivFunctionField _ h)}
  have hmulV := mul_mem_of_mem_iff Dc S V q hVmem
  have hmemV : ∀ m, q ∣ m → ∀ s ∈ V m, s ∈ divisorialSections (seriesDivisor KS Ω m) := by
    rintro m ⟨i, rfl⟩ s hs
    rw [hVmem, if_pos (dvd_mul_right q i), Nat.mul_div_cancel_left _ hq] at hs
    have := symm_mem_divisorialSections_of_mem_imageSeries sX hsm K S hSsm A B Δ hΔ hKS hABS q
      D' hD' i hs
    rwa [RingEquiv.symm_apply_apply] at this
  have hint : ∀ m, q ∣ m → ∀ P : MMP.Mori.PrimeDivisor S.idealSheaf.subscheme,
      ∃ z : ℤ, (m : ℚ) * Ω.coeff P = z :=
    fun m hm P => exists_int_eq_mul_coeff_of_isCartierDivisor hqΩ hm P
  have hsame : ∀ m, q ∣ m → ∀ s, s ∈ Vs m ↔ s ∈ V m := by
    rintro m ⟨i, rfl⟩ s
    rw [hVmem, if_pos (dvd_mul_right q i), Nat.mul_div_cancel_left _ hq]
    exact mem_closure_restrictedSystem_iff hsm K Δ S q i D' hD' s
  have hFN : ∀ N, 0 < N → ∀ G, restrictedAsymptoticFixedPart KS Ω 1 Vs G ≤
      restrictedNormalizedFixedPart KS Ω V (q * N) G :=
    fun N hN G => restrictedAsymptoticFixedPart_one_le KS Ω hq V Vs hsame hmulV hmemV hint hN G
  have hFle : ∀ G, restrictedAsymptoticFixedPart KS Ω 1 Vs G ≤
      restrictedAsymptoticFixedPart KS Ω q V G := fun G =>
    le_iInf₂ fun n _ => hFN n.factorial (Nat.factorial_pos n) G
  -- No component of `H|_S` lies in the fixed part.
  have hFzero : ∀ G, (H.restrictPrimeDivisor S).coeff G ≠ 0 →
      restrictedAsymptoticFixedPart KS Ω 1 Vs G = 0 := by
    intro G hG
    by_contra hF0
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hF0
    obtain ⟨i, hi, k', hnk, h, hh, h0, hval⟩ := hgen G hG (n + 1) n.succ_pos
    have hsV : e.symm h ∈ V (q * i) := by
      rw [hVmem, if_pos (dvd_mul_right q i), Nat.mul_div_cancel_left _ hq,
        RingEquiv.apply_symm_apply]
      exact hh
    have hsD := hmemV _ (dvd_mul_right q i) _ hsV
    have hc : (seriesDivisor KS Ω (q * i)).coeff G =
        (i : ℤ) * (Dc.restrictPrimeDivisor S).coeff G := by
      change ((q * i) • KS + (((q * i : ℕ) : ℚ) • Ω).roundDown).coeff G = _
      rw [← restrictPrimeDivisor_smul_eq K S A B Δ hΔ hKS hABS q i (q * i) (mul_comm _ _) D' hD',
        MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor_zsmul _ _ hDc0,
        DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    have hrfm := restrictedFixedMultiplicity_le_of_le_divisorialValuation hsV hsD h0 G _ k' hc
      hval
    have h1 : restrictedNormalizedFixedPart KS Ω V (q * i) G ≤
        ((k'.toNat : ℕ) : ℝ≥0∞) / ((q * i : ℕ) : ℝ≥0∞) := by
      unfold restrictedNormalizedFixedPart
      have := ENat.toENNReal_le.mpr hrfm
      simp only [ENat.toENNReal_coe] at this
      exact ENNReal.div_le_div_right this _
    have hnat : (n + 1) * k'.toNat ≤ q * i := by
      have hi' : i ≤ q * i := Nat.le_mul_of_pos_left i hq
      rcases le_or_gt k' 0 with hk0 | hk0
      · rw [Int.toNat_eq_zero.mpr hk0, mul_zero]; exact Nat.zero_le _
      · have h3 : ((n + 1 : ℕ) : ℤ) * (k'.toNat : ℤ) < i := by
          rwa [Int.toNat_of_nonneg hk0.le]
        have h4 : (n + 1) * k'.toNat < i := by exact_mod_cast h3
        omega
    have hqi : ((q * i : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos hq hi).ne'
    have h2 : ((k'.toNat : ℕ) : ℝ≥0∞) / ((q * i : ℕ) : ℝ≥0∞) ≤ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.div_le_iff hqi (ENNReal.natCast_ne_top _)]
      calc ((k'.toNat : ℕ) : ℝ≥0∞)
          = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * (((n + 1 : ℕ) : ℝ≥0∞) * ((k'.toNat : ℕ) : ℝ≥0∞)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _),
              one_mul]
        _ ≤ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ((q * i : ℕ) : ℝ≥0∞) := by
            gcongr
            exact_mod_cast hnat
    have h3 : ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_le_inv.mpr (by exact_mod_cast n.le_succ)
    exact absurd ((hFN i hi G).trans (h1.trans (h2.trans h3))) (not_le.mpr hn)
  -- A section of `qD` not vanishing along `S`.
  have hnv : ∃ m : ℕ, 0 < m ∧ ((m : ℚ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor ∧
      ∃ σ ∈ sectionsIn (DivisorWithCoeffs.roundDown ((m : ℚ) • (Divisor.toQDivisor K + Δ))),
        S.divisorialValuation σ = WithZero.exp
          ((DivisorWithCoeffs.roundDown ((m : ℚ) • (Divisor.toQDivisor K + Δ))).coeff S) := by
    have hex : ∃ h ∈ {h | ∃ g ∈ sectionsIn (((1 : ℕ) : ℤ) • Dc), IsRestrictionAlong S g h},
        h ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hne
      rw [eq_bot_iff]
      exact (AddSubgroup.closure_le _).mpr fun x hx => by
        rw [SetLike.mem_coe, AddSubgroup.mem_bot]; exact hcon x hx
    obtain ⟨h, ⟨g₁, hg₁, hres₁⟩, h0⟩ := hex
    rw [Nat.cast_one, one_smul] at hg₁
    refine ⟨q, hq, ⟨_, hDq, isCartier_of_isSmoothScheme hsm _⟩, g₁, ?_, ?_⟩
    · rw [hfl1]; exact hg₁
    · rw [hfl1, hDc0, WithZero.exp_zero]
      exact divisorialValuation_eq_one_of_isRestrictionAlong S hres₁ h0
  -- The canonical hypothesis.
  have hcanR := isRealCanonicalPair_restrictPrimeDivisor hXn hsm hK S hKS hSsm hSn A B hA0 hB hAS
    hBS (by rw [hΔ] at hplt'; exact hplt') hcan
  -- Apply the lifting theorem.
  refine ⟨ε, hε0, hε1, fun k hk hqk P hPc hlow hup s hs => ?_⟩
  obtain ⟨j, rfl⟩ := hqk
  have hkΔ : (((q * j : ℕ) : ℚ) • Δ).IsCartierDivisor := by
    refine ⟨(j : ℤ) • D', ?_, isCartier_of_isSmoothScheme hsm _⟩
    rw [map_zsmul, hD', ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    push_cast
    ring
  have hPc' : (((q * j : ℕ) : ℚ) • P).IsCartierDivisor := by
    rwa [Nat.cast_smul_eq_nsmul, ← natCast_zsmul]
  have hlow' : coeffwiseMin Ω (fun G => ENNReal.ofReal (1 - (ε : ℝ) / ((q * j : ℕ) : ℝ)) *
      restrictedAsymptoticFixedPart KS Ω 1 Vs G) ≤ QDivisor.toRDivisor P :=
    (coeffwiseMin_mono Ω fun G => by gcongr; exact hFle G).trans hlow
  have hs' : e s ∈ sectionsIn (DivisorWithCoeffs.roundDown
      (((q * j : ℕ) : ℚ) • (Divisor.toQDivisor KS + Ω - P))) := by
    rw [roundDown_smul_toQDivisor_add_sub]
    exact mem_sectionsIn_of_mem_divisorialSections _ hs
  subst hA hΔ
  obtain ⟨g₀, hg₀, hres⟩ :=
    exists_isRestrictionAlong_of_le_restrictedAsymptoticFixedPart_of_isPltPair_add sX hXn hsm π
      hπp (d + 1) (by omega) K hK S hKS hSsm B hB hBS H hH hHa a ha
    hHS hplt' hfloor hcanR hnv hFzero ε hε0 hε1 hεA (q * j) hk hkΔ P hPc' hlow' hup (e s) hs'
  rw [hVmem, if_pos (dvd_mul_right q j), Nat.mul_div_cancel_left _ hq]
  refine AddSubgroup.subset_closure ⟨g₀, ?_, hres⟩
  rwa [roundDown_natCast_smul_eq K _ q j D' hD'] at hg₀

end MMP.Fourfold
