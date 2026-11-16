module

public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainLabel
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# Junctions, lost divisors, boundary labels and vertical contractions

Four facts used in the construction of terminal chains over a stabilized small klt tail of
fourfolds.

* A crepant junction `(p, Θ)`, `p : Y ⟶ X`, of a projective klt fourfold pair `(X, B)` is
  crepant: `K_Y + Θ = p^*(K_X + B)`, for `K_X = div(ω)` and `K_Y = div(p^*ω)` with `ω` a nonzero
  rational top form on `X`. Take `m > 0` with `D = m(K_X + B)` Cartier and let `D' = p^*D`. For a
  prime divisor `P` of `Y` the log discrepancy of `(Y, p, P)` is
  `1 + ord_P(p^*ω) - m⁻¹ coeff_P D'`; it depends only on the valuation `ord_P`, which is either an
  extracted valuation `s`, of log discrepancy `a(s; X, B)`, or `ord_Q` for a prime divisor `Q` of
  `X` with `p⁻¹_* Q = P`, of log discrepancy `1 - coeff_Q B`. Either way
  `m⁻¹ coeff_P D' = coeff_P K_Y + coeff_P Θ`.
* In a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)`, a prime divisor `E` of `X⁻` whose valuation is
  exceptional over `X⁺` lies in the negative bad locus `W⁻ = (f⁻)⁻¹(Σ)`: were `f⁻(η_E)` in the
  common biregular locus, the centre of `ord_E` on `X⁺` would have coheight one.
* A label `S = p_0⁻¹_* Γ` of a terminal chain, `Γ` a component of `B_0`, has label coefficient
  `coeff_Γ B_0` at every model of the chain. The centre of `ord_S` is followed along the chain:
  the downstairs steps and the flips of the bridges are pairs of small morphisms, which carry a
  prime divisor to a prime divisor with the same valuation and the same coefficient in the strict
  transform, and on a junction the centre is not an extracted divisor.
* The contraction `g : U ⟶ V` of an extremal ray all of whose curves are contracted by a
  projective birational morphism `h : U ⟶ Z` is birational: `h = g ≫ h'`, and on a dense open
  `W` where `h` is an open immersion, the restriction of `g` is a surjective closed immersion
  onto a reduced scheme, hence an isomorphism.

## Main results

* `MMP.Fourfold.FourfoldCrepantJunction.isPullback_canonical_add_boundary`:
  `K_Y + Θ = p^*(K_X + B)`.
* `MMP.Fourfold.IsFourfoldStepDiagram.support_subset_badLocusMinus`: a lost divisor lies in
  `W⁻`.
* `TerminalChain.isLabelCoefficient_coeff_of_inverseTransformPrimeDivisor_eq_some`
  (in `MMP.Fourfold.StabilizedSmallKltTail`): `b_h^M = coeff_Γ B_0` for every model `M`.
* `MMP.Fourfold.isBirationalMorphism_of_isContractionOfRay`: the contraction is birational.

## Implementation notes

The canonical divisors of a junction are given by their coefficients, `coeff_Γ(K_X) = ord_Γ(ω)`
and `coeff_Γ(K_Y) = ord_Γ(p^*ω)`, as in `MMP.Intersection.IsLogDiscrepancy`; the pull-back is that
of a `ℚ`-Cartier `ℚ`-divisor, `MMP.Mori.QDivisor.IsPullback`, whose side condition (the generic
point of `Y` maps outside `Supp (K_X + B)`) is part of the conclusion.

The valuations of `k(X⁻)` and `k(X⁺)` in a step diagram are compared through `k(Z)`: a valuation
`ξ` of `k(X⁺)` corresponds to `ord_E` when the two have the same restriction to `k(Z)`, as in
`MMP.Fourfold.StepSequence.IsTransportedValuation`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Crepant junctions are crepant -/

section CrepantJunction

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
  {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- A dominant morphism from an irreducible scheme maps the generic point outside the support of
every divisor with coefficients. -/
private theorem map_componentGenericPoint_notMem_supp {R : Type*} [Zero R] {Y : Scheme.{0}}
    [IrreducibleSpace Y] (f : Y ⟶ X) [IsDominant f] (D : DivisorWithCoeffs R X)
    (Z : irreducibleComponents Y) : f (componentGenericPoint Y Z) ∉ D.supp := by
  intro h
  obtain ⟨E, -, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  have hfgen : closure {f (componentGenericPoint Y Z)} = Set.univ := by
    have hgen := isGenericPoint_componentGenericPoint Y Z
    rw [show (Z.1 : Set Y) = Set.univ by
      simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using Z.2] at hgen
    simpa only [Set.image_univ, f.denseRange.closure_range] using (hgen.image f.continuous).def
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem
  have hmax : IsMax E.genericPoint := fun y _ => specializes_iff_mem_closure.mpr <|
    closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure (hfgen ▸ trivial)
  have h0 := Order.coheight_eq_zero.mpr hmax
  rw [E.coheight_genericPoint] at h0
  exact one_ne_zero h0

/-- A prime divisor `Q` of the source `Y` of a junction, as the divisor `(Y, p, Q)` over `X`. -/
private def primeDivisorOver (J : FourfoldCrepantJunction sX B I) (Q : MMP.Mori.PrimeDivisor J.Y) :
    DivisorOver ℂ sX :=
  ⟨J.Y, J.p, J.isQFactorial.1, J.isBirationalMorphism, Q⟩

/-- A divisor over a normal variety is exceptional exactly when its centre has codimension at
least two. -/
private theorem isExceptional_iff_two_le_codimension_center {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY)
    (D : DivisorOver ℂ sY) : D.IsExceptional ↔ 2 ≤ codimension D.center := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sY := hY.1.toIsSeparated
  have hsep : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = sY ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set Y), D.center.isClosed⟩ := by
    refine Closeds.ext ?_
    rw [Closeds.coe_closure]
    exact D.coe_center.symm
  rw [hc]
  change 2 ≤ closedsCodimension (T := Y) ⟨(D.center : Set Y), D.center.isClosed⟩ ↔ _
  rw [closedsCodimension_coe]

/-- The image of a divisor under a map of prime divisors has coefficient zero at a prime divisor
that is not the image of any prime divisor. -/
private theorem coeff_mapPrimeDivisors_eq_zero {R : Type*} [AddCommMonoid R] {X' Y' : Scheme.{0}}
    (φ : MMP.Mori.PrimeDivisor X' → Option (MMP.Mori.PrimeDivisor Y'))
    (D : DivisorWithCoeffs R X') (Γ : MMP.Mori.PrimeDivisor Y') (h : ∀ P, φ P ≠ some Γ) :
    (DivisorWithCoeffs.mapPrimeDivisors φ D).coeff Γ = 0 := by
  classical
  induction D using Finsupp.induction_linear with
  | zero =>
    rw [map_zero]
    rfl
  | add D₁ D₂ h₁ h₂ =>
    have := congrArg₂ (· + ·) h₁ h₂
    simp only [add_zero] at this
    rw [map_add]
    exact this
  | single P r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    cases hφ : φ P with
    | none => rfl
    | some Q =>
      change (Finsupp.single Q r) Γ = 0
      exact Finsupp.single_eq_of_ne (fun hQ => h P (by rw [hφ, hQ]))

/-- The strict transform `p⁻¹_* B` does not contain the exceptional divisors `E_s`. -/
private theorem coeff_inverseTransformDivisor_E (J : FourfoldCrepantJunction sX B I) (s : I) :
    (inverseTransformDivisor J.p B).coeff (J.E s) = 0 := by
  have hX : IsNormalVariety ℂ sX := J.isKltPair.1.isPair.1
  refine coeff_mapPrimeDivisors_eq_zero _ _ _ fun P hP => ?_
  have hη := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hP).1
  have hE : (primeDivisorOver J (J.E s)).IsExceptional :=
    (J.isExceptional_iff _).mpr ⟨s, rfl⟩
  have h2 := (isExceptional_iff_two_le_codimension_center hX _).mp hE
  rw [MMP.Positivity.DivisorOver.codimension_center] at h2
  change 2 ≤ Order.coheight (J.p (J.E s).genericPoint) at h2
  rw [hη, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- The base of a junction is quasi-compact: it is projective over `ℂ`. -/
private theorem compactSpace_base (J : FourfoldCrepantJunction sX B I) : CompactSpace X := by
  have := isProper_of_isProjectiveMorphism _ J.isProjectiveVariety_base.isProjective
  exact QuasiCompact.compactSpace_of_compactSpace sX

/-- On the base of a junction, the divisor of a nonzero rational top form is canonical. -/
private theorem isCanonicalDivisor_of_coeff_eq_ordForm (J : FourfoldCrepantJunction sX B I)
    {ω : RationalPluriForms sX 4 1} (hω : ω ≠ 0) {KX : Divisor X}
    (hKX : ∀ Γ : MMP.Mori.PrimeDivisor X, KX.coeff Γ = Γ.ordForm ω) :
    KX.IsCanonicalDivisor sX 4 := by
  have hpair := J.isKltPair.1.isPair
  have hX : IsNormalVariety ℂ sX := hpair.1
  obtain ⟨n, K₀, hK₀, -⟩ := hpair.2
  have hn : n = 4 := by exact_mod_cast hK₀.topologicalKrullDim_eq.symm.trans J.dim_base
  subst hn
  have := compactSpace_base J
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hle := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK₀ hω
  have hKω : divisorOfForm ω = KX := by
    ext Γ
    exact (hKX Γ).symm
  rw [hKω, one_smul] at hle
  exact hK₀.of_linearlyEquivalent hle

/-- The log discrepancy of `(Y, p, P)`, computed with the form `ω` and the presentation
`K_X + B = m⁻¹ D` by a Cartier divisor `D = m(K_X + B)` with pull-back `D'`. -/
private theorem isLogDiscrepancy_primeDivisorOver (J : FourfoldCrepantJunction sX B I)
    {ω : RationalPluriForms sX 4 1} (hω : ω ≠ 0) {KX : Divisor X}
    (hKX : ∀ Γ : MMP.Mori.PrimeDivisor X, KX.coeff Γ = Γ.ordForm ω) {m : ℕ} (hm : 0 < m)
    {D : Divisor X} (hD : Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor KX + B))
    (hDc : D.IsCartier) {D' : Divisor J.Y} (hD' : ∃ hC, D.IsPullback J.p hC D')
    (P : MMP.Mori.PrimeDivisor J.Y) :
    MMP.Intersection.IsLogDiscrepancy sX 4 (QDivisor.toRDivisor B) (primeDivisorOver J P)
      (1 + ((primeDivisorOver J P).ordPullback ω : ℝ) - (m : ℝ)⁻¹ * (D'.coeff P : ℝ)) := by
  have hX : IsNormalVariety ℂ sX := J.isKltPair.1.isPair.1
  refine ⟨hX, isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism, ω, hω,
    ⟨KX, isCanonicalDivisor_of_coeff_eq_ordForm J hω hKX, hKX⟩, 1, fun _ => (m : ℝ)⁻¹,
    fun _ => D, fun _ => D', fun _ => hDc, fun Γ => ?_, fun _ => hD', ?_⟩
  · have h := congrArg (fun G : QDivisor X => G.coeff Γ) hD
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, zsmul_eq_mul, Int.cast_natCast] at h
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hR : (D.coeff Γ : ℝ) = m * (KX.coeff Γ + (B.coeff Γ : ℝ)) := by
      exact_mod_cast h
    simp only [Finset.univ_unique, Finset.sum_singleton, QDivisor.coeff_toRDivisor, ← hKX Γ, hR]
    field_simp
  · simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl

/-- A prime divisor of `X` is not contained in the complement of the biregular locus of `p`: that
complement has codimension at least two. -/
private theorem genericPoint_mem_biregularLocus (J : FourfoldCrepantJunction sX B I)
    (Q : MMP.Mori.PrimeDivisor X) : Q.genericPoint ∈ biregularLocus J.p := by
  have hX : IsNormalVariety ℂ sX := J.isKltPair.1.isPair.1
  have := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  have := hX.1
  have := J.isQFactorial.1.1
  have hc := MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sX J.p J.isBirationalMorphism
  by_contra hnot
  rw [le_closedsCodimension_iff] at hc
  have hsub : (IrreducibleCloseds.closureSingleton Q.genericPoint : Set X) ⊆
      ((biregularLocus J.p).compl : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr hnot) (biregularLocus J.p).compl.isClosed
  have h2 := hc _ hsub
  rw [Q.codimension_closure_genericPoint] at h2
  exact absurd h2 (by decide)

/-- The exceptional part `∑ₜ c_t E_t` of a junction has coefficient `c_s` at `E_s`. -/
private theorem coeff_sum_single_E (J : FourfoldCrepantJunction sX B I) (c : I → ℚ) (s : I) :
    DivisorWithCoeffs.coeff (∑ t : I, Finsupp.single (J.E t) (c t)) (J.E s) = c s := by
  classical
  change (∑ t : I, Finsupp.single (J.E t) (c t)) (J.E s) = c s
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply, J.injective.eq_iff]

/-- The exceptional part `∑ₜ c_t E_t` of a junction vanishes at a non-exceptional prime. -/
private theorem coeff_sum_single_eq_zero (J : FourfoldCrepantJunction sX B I) (c : I → ℚ)
    {P : MMP.Mori.PrimeDivisor J.Y} (hP : P ∉ Set.range J.E) :
    DivisorWithCoeffs.coeff (∑ t : I, Finsupp.single (J.E t) (c t)) P = 0 := by
  change (∑ t : I, Finsupp.single (J.E t) (c t)) P = 0
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun t _ => Finsupp.single_eq_of_ne fun h => hP ⟨t, h.symm⟩

/-- A non-exceptional prime divisor `P` of the source of a junction is the strict transform of a
prime divisor `Q` of `X`: their valuations agree and `coeff_P Θ = coeff_Q B`. -/
private theorem exists_valuation_eq_and_coeff_Θ (J : FourfoldCrepantJunction sX B I)
    {a : I → ℚ}
    (hΘ : J.Θ = inverseTransformDivisor J.p B + ∑ s : I, Finsupp.single (J.E s) (1 - a s))
    {P : MMP.Mori.PrimeDivisor J.Y} (hP : P ∉ Set.range J.E) :
    ∃ Q : MMP.Mori.PrimeDivisor X, (primeDivisorOver J P).valuation =
        (DivisorOver.ofPrimeDivisor ℂ J.isKltPair.1.isPair.1 Q).valuation ∧
      J.Θ.coeff P = B.coeff Q := by
  have hX : IsNormalVariety ℂ sX := J.isKltPair.1.isPair.1
  have h2 : ¬ 2 ≤ codimension (primeDivisorOver J P).center := fun h =>
    hP ((J.isExceptional_iff P).mp ((isExceptional_iff_two_le_codimension_center hX _).mpr h))
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX] at h2
  push Not at h2
  obtain ⟨Q, hv⟩ := h2
  have hη : J.p P.genericPoint = Q.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  refine ⟨Q, hv, ?_⟩
  rw [hΘ, DivisorWithCoeffs.coeff_add, coeff_sum_single_eq_zero J _ hP, add_zero]
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη
      (hη ▸ genericPoint_mem_biregularLocus J Q)) (fun Q' hQ' => ?_) B
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hQ').1.symm.trans hη)

/-- **The coefficient comparison.** With `D = m(K_X + B)` Cartier and `D' = p^*D`, at every prime
divisor `P` of `Y`, `m⁻¹ coeff_P D' = coeff_P K_Y + coeff_P Θ`. -/
private theorem coeff_pullback_eq (J : FourfoldCrepantJunction sX B I)
    {ω : RationalPluriForms sX 4 1} (hω : ω ≠ 0) {KX : Divisor X}
    (hKX : ∀ Γ : MMP.Mori.PrimeDivisor X, KX.coeff Γ = Γ.ordForm ω) {KY : Divisor J.Y}
    (hKY : ∀ Γ : MMP.Mori.PrimeDivisor J.Y,
      haveI := J.isBirationalMorphism.isDominant
      KY.coeff Γ = Γ.ordForm (pullbackRationalPluriForms sX J.p ω)) {m : ℕ} (hm : 0 < m)
    {D : Divisor X} (hD : Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor KX + B))
    (hDc : D.IsCartier) {D' : Divisor J.Y} (hD' : ∃ hC, D.IsPullback J.p hC D')
    (P : MMP.Mori.PrimeDivisor J.Y) :
    (m : ℝ)⁻¹ * (D'.coeff P : ℝ) = (KY.coeff P : ℝ) + (J.Θ.coeff P : ℝ) := by
  have hpair := J.isKltPair.1.isPair
  have hlog := isLogDiscrepancy_primeDivisorOver J hω hKX hm hD hDc hD' P
  rw [show ((primeDivisorOver J P).ordPullback ω : ℝ) = (KY.coeff P : ℝ) by rw [hKY P]; rfl]
    at hlog
  obtain ⟨a, ha, hΘ⟩ := J.Θ_eq
  by_cases hP : P ∈ Set.range J.E
  · obtain ⟨s, rfl⟩ := hP
    obtain ⟨_, _, -, hv, hlog₀⟩ := ha s
    have heq := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog hlog₀
      ((J.valuation_eq s).trans hv.symm)
    rw [hΘ, DivisorWithCoeffs.coeff_add, coeff_inverseTransformDivisor_E J s, zero_add,
      coeff_sum_single_E]
    push_cast
    linarith
  · obtain ⟨Q, hv, hΘP⟩ := exists_valuation_eq_and_coeff_Θ J hΘ hP
    obtain ⟨-, n, K₀, hK₀, -⟩ := id hpair
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair hK₀
      (DivisorOver.ofPrimeDivisor ℂ hpair.1 Q)
    have hlogQ := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
      (inferInstanceAs (IsProper (𝟙 X)))
    have heq := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog hlogQ hv
    rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hpair.1 hc] at heq
    rw [hΘP]
    push_cast at heq
    linarith

end CrepantJunction

/-- **Crepant junctions are crepant.** For a crepant junction `(p, Θ)`, `p : Y ⟶ X`, of a
projective klt fourfold pair `(X, B)` and a nonzero rational top form `ω` on `X`, with
`K_X = div(ω)` and `K_Y = div(p^*ω)`, the `ℚ`-divisor `K_Y + Θ` is the pull-back `p^*(K_X + B)`. -/
@[mmp "lem_oai4_c1_junction_crepant"]
public theorem FourfoldCrepantJunction.isPullback_canonical_add_boundary
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}
    (J : FourfoldCrepantJunction sX B I) (ω : RationalPluriForms sX 4 1) (hω : ω ≠ 0)
    (KX : Divisor X) (hKX : ∀ Γ : MMP.Mori.PrimeDivisor X, KX.coeff Γ = Γ.ordForm ω)
    (KY : Divisor J.Y) (hKY : ∀ Γ : MMP.Mori.PrimeDivisor J.Y,
      haveI := J.isBirationalMorphism.isDominant
      KY.coeff Γ = Γ.ordForm (pullbackRationalPluriForms sX J.p ω)) :
    ∃ hB, (Divisor.toQDivisor KX + B).IsPullback J.p hB (Divisor.toQDivisor KY + J.Θ) := by
  have := J.isBirationalMorphism.isDominant
  refine ⟨map_componentGenericPoint_notMem_supp J.p _, ?_⟩
  intro m hm D hD hDc
  have hBD : ∀ Z : irreducibleComponents J.Y, J.p (componentGenericPoint J.Y Z) ∉ D.supp :=
    map_componentGenericPoint_notMem_supp J.p D
  refine ⟨D.pullback hDc hBD, ?_, Divisor.isPullback_pullback hDc _⟩
  ext P
  have h := coeff_pullback_eq J hω hKX hKY hm hD hDc ⟨hBD, Divisor.isPullback_pullback hDc hBD⟩ P
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hR : ((D.pullback hDc hBD).coeff P : ℝ) = m * (KY.coeff P + (J.Θ.coeff P : ℝ)) := by
    rw [← h]
    field_simp
  change ((D.pullback hDc hBD).coeff P : ℚ) =
    ((m : ℤ) • (Divisor.toQDivisor KY + J.Θ)).coeff P
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
    Divisor.coeff_toQDivisor, zsmul_eq_mul, Int.cast_natCast]
  exact_mod_cast hR

/-! ### A lost divisor lies in the negative bad locus -/

section LostDivisor

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- If a valuation `u` of `k(Y)` dominates the local ring at `y`, then its restriction to
`k(X)` along a dominant morphism `f : Y ⟶ X` dominates the local ring at `f y`. -/
private lemma dominates_comap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] (u : Valuation Y.functionField (WithZero (Multiplicative ℤ))) (y : Y)
    (h1 : ∀ a : Y.presheaf.stalk y, u (algebraMap _ Y.functionField a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
      u (algebraMap _ Y.functionField a) < 1) :
    (∀ a : X.presheaf.stalk (f y),
      u.comap (functionFieldMap f) (algebraMap _ X.functionField a) ≤ 1) ∧
    (∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (f y)),
      u.comap (functionFieldMap f) (algebraMap _ X.functionField a) < 1) := by
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
    exact h1 _
  · rw [Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
    exact h2 _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu))

/-- The divisorial valuation `ord_E` dominates the local ring at the generic point of `E`. -/
private lemma dominates_divisorialValuation {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : MMP.Mori.PrimeDivisor X) :
    (∀ a : X.presheaf.stalk E.genericPoint,
      E.divisorialValuation (algebraMap _ X.functionField a) ≤ 1) ∧
    (∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint),
      E.divisorialValuation (algebraMap _ X.functionField a) < 1) :=
  ⟨fun a => (PrimeDivisor.divisorialValuation_le_one_iff _ _).2 ⟨a, rfl⟩,
    fun a ha => (E.divisorialValuation_algebraMap_lt_one_iff a).2 ha⟩

/-- The key step: if `f⁻(η_E)` lies in the common biregular locus, then the centre on `X⁺` of
the valuation `ξ` corresponding to `ord_E` has coheight one. -/
private lemma coheight_centre_eq_one {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm]
    [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral Z]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) [IsDominant fm] [IsDominant fp]
    (E : MMP.Mori.PrimeDivisor Xm)
    (ξ : Valuation Xp.functionField (WithZero (Multiplicative ℤ)))
    (hξ : ξ.comap (functionFieldMap fp) = E.divisorialValuation.comap (functionFieldMap fm))
    (D : DivisorOver ℂ sXp) (hξD : ξ = D.valuation)
    (hηU : fm E.genericPoint ∈ commonBiregularLocus fm fp) :
    Order.coheight (D.f D.E.genericPoint) = 1 := by
  set y := D.f D.E.genericPoint
  obtain ⟨hm1, hm2⟩ := dominates_comap fm _ _ (dominates_divisorialValuation E).1
    (dominates_divisorialValuation E).2
  obtain ⟨hp1, hp2⟩ := dominates_comap fp ξ y
    (fun a => hξD ▸ MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D y rfl a)
    (fun a ha => hξD ▸ MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D y rfl a ha)
  have : IsSeparated sZ := h.isNormalVariety_target.1.toIsSeparated
  have heq : fm E.genericPoint = fp y :=
    MMP.Positivity.DivisorOver.eq_of_dominates sZ _ hm1 hm2 (hξ ▸ hp1) (hξ ▸ hp2)
  rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp
      (le_biregularLocus (isBiregular_commonBiregularLocus_right fm fp) (heq ▸ hηU)), ← heq,
    MMP.Positivity.coheight_map_of_mem_biregularLocus fm
      (le_biregularLocus (isBiregular_commonBiregularLocus_left fm fp) hηU),
    E.coheight_genericPoint]

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsIntegral Z]

/-- In a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)`, a prime divisor `E` of `X⁻` whose valuation
`ord_E` corresponds to a valuation of `k(X⁺)` exceptional over `X⁺` lies in the negative-side
bad locus `W⁻ = (f⁻)⁻¹(Σ)`. -/
@[mmp "lem_oai4_c1_lost_divisor_in_bad_locus"]
public theorem IsFourfoldStepDiagram.support_subset_badLocusMinus
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (E : MMP.Mori.PrimeDivisor Xm)
    (hE : haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isBirationalMorphism_plus.isDominant
      ∃ ξ : Valuation Xp.functionField (WithZero (Multiplicative ℤ)),
      ξ.comap (functionFieldMap fp) = E.divisorialValuation.comap (functionFieldMap fm) ∧
        MMP.Intersection.IsExceptionalValuation ℂ sXp ξ) :
    (E.support : Set Xm) ⊆ (badLocusMinus fm fp : Set Xm) := by
  intro x hx
  have := h.isBirationalMorphism_minus.isDominant
  have := h.isBirationalMorphism_plus.isDominant
  obtain ⟨ξ, hξ, D, -, hξD, hcod⟩ := hE
  rw [coe_badLocusMinus, Set.mem_preimage, coe_badLocusBase, Set.mem_compl_iff]
  intro hxU
  have hspec : E.genericPoint ⤳ x := by
    rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
  rw [MMP.Positivity.DivisorOver.codimension_center, coheight_centre_eq_one h E ξ hξ D hξD
    ((hspec.map fm.continuous).mem_open (commonBiregularLocus fm fp).isOpen hxU)] at hcod
  exact absurd hcod (by decide)

end LostDivisor

/-! ### Labels coming from the boundary keep their coefficient -/

section Labels

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- `ord_E` regarded through a composite is the restriction of `ord_E` regarded through the
first morphism. -/
private lemma valuationOver_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsIntegral Z] (E : MMP.Mori.PrimeDivisor X) (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsDominant f] [IsDominant g] [IsDominant (f ≫ g)] :
    E.valuationOver (f ≫ g) = (E.valuationOver f).comap (functionFieldMap g) := by
  ext t
  simp only [PrimeDivisor.valuationOver_apply, Valuation.comap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- If a birational morphism `g` maps the generic point of `E` to that of `D`, then `ord_E`
regarded through `g` is `ord_D`. -/
private lemma valuationOver_eq_divisorialValuation {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (g : X ⟶ Y) [IsDominant g] (hg : Function.Surjective (functionFieldMap g))
    (E : MMP.Mori.PrimeDivisor X) (D : MMP.Mori.PrimeDivisor Y)
    (h : g E.genericPoint = D.genericPoint) : E.valuationOver g = D.divisorialValuation := by
  have key : ∀ z (hz : z = g E.genericPoint),
      (∀ a : Y.presheaf.stalk z, E.valuationOver g (algebraMap _ Y.functionField a) ≤ 1) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z),
        E.valuationOver g (algebraMap _ Y.functionField a) < 1) := by
    rintro z rfl
    refine ⟨fun a => ?_, fun a ha => ?_⟩
    · rw [PrimeDivisor.valuationOver_apply, functionFieldMap_algebraMap_stalk,
        PrimeDivisor.divisorialValuation_le_one_iff]
      exact ⟨_, rfl⟩
    · rw [PrimeDivisor.valuationOver_apply, functionFieldMap_algebraMap_stalk,
        PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff]
      exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)
  have := D.isDiscreteValuationRing_localRing
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨k1, k2⟩ := key D.genericPoint h.symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D.localRing
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  obtain ⟨t, ht⟩ := hg (algebraMap E.localRing X.functionField ϖ')
  refine MMP.Positivity.DivisorOver.valuation_eq_of_isDiscreteValuationRing (R := D.localRing)
    k1 k2 ⟨t, ?_⟩ (fun r => ?_) (fun r hr => ?_)
    ⟨_, D.divisorialValuation_algebraMap_of_irreducible hϖ⟩
  · rw [PrimeDivisor.valuationOver_apply, ht, E.divisorialValuation_algebraMap_of_irreducible hϖ']
  · rw [PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨r, rfl⟩
  · exact (D.divisorialValuation_algebraMap_lt_one_iff r).2 hr

/-- The coefficient at a prime divisor `Γ'` of an inverse transform `g⁻¹_* D` is the
coefficient of `D` at `Γ`, when `g⁻¹_* Γ = Γ'`. -/
private lemma inverseTransformDivisor_apply_of_eq_some {X Y : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] {g : Y ⟶ X} {Γ : MMP.Mori.PrimeDivisor X} {Γ' : MMP.Mori.PrimeDivisor Y}
    (h : inverseTransformPrimeDivisor g Γ = some Γ') (D : DivisorWithCoeffs R X) :
    inverseTransformDivisor g D Γ' = D Γ := by
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq h (fun E' hE' => ?_) D
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hE').1.symm.trans
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some h).1)

/-- A point of the base lying in the biregular locus of `g` is the image of a point. -/
private lemma exists_apply_eq_of_mem_biregularLocus {X Y : Scheme.{0}} (g : Y ⟶ X) {z : X}
    (hz : z ∈ biregularLocus g) : ∃ y, g y = z := by
  set V := biregularLocus g
  have : IsIso (g ∣_ V) := isBiregular_biregularLocus g
  let w : (V : Scheme) := ⟨z, hz⟩
  refine ⟨(g ⁻¹ᵁ V).ι (inv (g ∣_ V) w), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply,
    ← Scheme.Hom.comp_apply (inv (g ∣_ V)), IsIso.inv_hom_id]
  rfl

/-- **Small morphisms and prime divisors.** Let `X⁻ → Z ← X⁺` be small morphisms `f⁻`, `f⁺` of
normal complex varieties and `Γ` a prime divisor of `X⁻`. Both morphisms are isomorphisms over
the codimension one point `f⁻(η_Γ)`, so there is a prime divisor `Γ'` of `X⁺` with
`ord_{Γ'} = ord_Γ` on `k(Z)`, and the coefficient of the strict transform `(f⁺)⁻¹_* f⁻_* D` at `Γ'`
is the coefficient of `D` at `Γ`. -/
private lemma exists_valuationOver_eq_and_flipTransform_apply {Xm Xp Z : Scheme.{0}}
    [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral Z]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsDominant fm] [IsDominant fp]
    (hm : IsSmallMorphism sXm sZ fm) (hp : IsSmallMorphism sXp sZ fp)
    (Γ : MMP.Mori.PrimeDivisor Xm) :
    ∃ Γ' : MMP.Mori.PrimeDivisor Xp, Γ'.valuationOver fp = Γ.valuationOver fm ∧
      ∀ D : QDivisor Xm, flipTransform fm fp D Γ' = D Γ := by
  have hZ := hm.isNormalVariety_target
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := hm.isProper
  have := hp.isProper
  have hη : fm Γ.genericPoint ∈ biregularLocus fm := by
    by_contra h
    have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hm.two_le_codimension
      (mem_exceptionalSet.mpr h)
    rw [Γ.coheight_genericPoint] at this
    exact absurd this (by decide)
  set z := fm Γ.genericPoint
  have hz1 : Order.coheight z = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fm hη]
    exact Γ.coheight_genericPoint
  set ΓZ : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hz1
  have hΓZ : ΓZ.genericPoint = z := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hz1
  have hpbij := MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective hp.isBirationalMorphism
  have hmbij := MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective hm.isBirationalMorphism
  have hzV : z ∈ biregularLocus fp :=
    MMP.Positivity.mem_biregularLocus_of_coheight_le_one fp hpbij hp.two_le_codimension hz1.le
  obtain ⟨x', hx'⟩ := exists_apply_eq_of_mem_biregularLocus fp hzV
  have hx'1 : Order.coheight x' = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hx' ▸ hzV), hx', hz1]
  set Γ' : MMP.Mori.PrimeDivisor Xp := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x' hx'1
  have hΓ' : Γ'.genericPoint = x' :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hx'1
  refine ⟨Γ', ?_, fun D => ?_⟩
  · rw [valuationOver_eq_divisorialValuation fp hpbij.2 Γ' ΓZ (by rw [hΓ', hx', hΓZ]),
      valuationOver_eq_divisorialValuation fm hmbij.2 Γ ΓZ hΓZ.symm]
  · have hinv : inverseTransformPrimeDivisor fp ΓZ = some Γ' :=
      MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
        (by rw [hΓ', hx', hΓZ]) (by rw [hΓ', hx']; exact hzV)
    change inverseTransformDivisor fp (RationalMap.transformDivisor (X := Xm)
      fm.toRationalMap D) Γ' = D Γ
    rw [inverseTransformDivisor_apply_of_eq_some hinv]
    have hX : IsNormalVariety ℂ (fm ≫ sZ) := hm.comp_eq ▸ hm.isNormalVariety_source
    obtain ⟨E, hE, -, hcoeff⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
      hZ hX hm.isBirationalMorphism ΓZ
    rw [hcoeff D]
    have hEz : fm E.genericPoint = z := hE.trans hΓZ
    have h1 : E.genericPoint ⤳ Γ.genericPoint :=
      MMP.Threefold.Resolution.specializes_of_mem_biregularLocus fm (hEz ▸ hη) hη
        (by rw [hEz])
    have h2 : Γ.genericPoint ⤳ E.genericPoint :=
      MMP.Threefold.Resolution.specializes_of_mem_biregularLocus fm hη (hEz ▸ hη)
        (by rw [hEz])
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h1.antisymm h2).eq]

/-- `ord_E` regarded through equal morphisms is the same valuation. -/
private lemma valuationOver_congr {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] (E : MMP.Mori.PrimeDivisor X) {f f' : X ⟶ Y} (h : f = f')
    [IsDominant f] [IsDominant f'] : E.valuationOver f = E.valuationOver f' := by
  subst h
  rfl

section Junction

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
  {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

omit [CompactSpace X] in
/-- A prime divisor of the source of a crepant junction whose generic point maps to the generic
point of a prime divisor of the base is not one of the extracted divisors `E_s`. -/
private lemma notMem_range_E_of_map_genericPoint (hX : IsNormalVariety ℂ sX)
    (J : FourfoldCrepantJunction sX B I) {P : MMP.Mori.PrimeDivisor J.Y}
    {Γ : MMP.Mori.PrimeDivisor X} (h : J.p P.genericPoint = Γ.genericPoint) :
    P ∉ Set.range J.E := by
  intro hP
  have hexc := (J.isExceptional_iff P).mpr hP
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ Limits.terminal Scheme) := by
    rw [show (X ↘ Limits.terminal Scheme) = sX ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hdef : RationalMap.DefinedAt (X := J.Y) J.p.toRationalMap P.genericPoint := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have htr := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff J.p P Γ).mpr h
  have h2 := RationalMap.isExceptional_iff.mp hexc hdef
  have h3 := le_closedsCodimension_iff.mp h2
    (IrreducibleCloseds.closureSingleton Γ.genericPoint) (by
      rw [← RationalMap.support_transformPrimeDivisor htr]
      change closure {Γ.genericPoint} ⊆ (Γ.support : Set X)
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure])
  rw [Γ.codimension_closure_genericPoint] at h3
  exact absurd h3 (by decide)

omit [CompactSpace X] in
/-- Off the extracted divisors, a divisor `p⁻¹_* B + ∑_s c_s E_s` has the coefficients of
`p⁻¹_* B`. -/
private lemma apply_eq_of_notMem_range_E (J : FourfoldCrepantJunction sX B I)
    {P : MMP.Mori.PrimeDivisor J.Y} (hP : P ∉ Set.range J.E) (c : I → ℚ) :
    (inverseTransformDivisor J.p B + ∑ s : I, Finsupp.single (J.E s) (c s)) P =
      inverseTransformDivisor J.p B P := by
  rw [Finsupp.add_apply, Finsupp.finsetSum_apply, Finset.sum_eq_zero, add_zero]
  intro s _
  exact Finsupp.single_eq_of_ne (fun h => hP ⟨s, h.symm⟩)

omit [CompactSpace X] in
/-- The centre on `X` of `ord_P`, for a prime divisor `P` of the source of a crepant junction:
if `ord_P = ord_Γ` then `p(η_P) = η_Γ`. -/
private lemma map_genericPoint_of_valuationOver_eq (hX : IsNormalVariety ℂ sX)
    (J : FourfoldCrepantJunction sX B I) [IsDominant J.p] {P : MMP.Mori.PrimeDivisor J.Y}
    {Γ : MMP.Mori.PrimeDivisor X} (h : P.valuationOver J.p = Γ.divisorialValuation) :
    J.p P.genericPoint = Γ.genericPoint := by
  have hv : (primeDivisorOver J P).valuation = (DivisorOver.ofPrimeDivisor ℂ hX Γ).valuation := by
    change P.valuationOver J.p = _
    rw [h]
    ext g
    change _ = Γ.divisorialValuation (functionFieldMap (𝟙 X) g)
    rw [MMP.Mori.functionFieldMap_id_apply]
  exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv

omit [CompactSpace X] in
/-- If `ord_P = ord_Γ`, the coefficient at `P` of a divisor `p⁻¹_* B + ∑_s c_s E_s` is that of
`p⁻¹_* B`. -/
private lemma apply_eq_of_valuationOver_eq (hX : IsNormalVariety ℂ sX)
    (J : FourfoldCrepantJunction sX B I) [IsDominant J.p] {P : MMP.Mori.PrimeDivisor J.Y}
    {Γ : MMP.Mori.PrimeDivisor X} (h : P.valuationOver J.p = Γ.divisorialValuation)
    (c : I → ℚ) :
    (inverseTransformDivisor J.p B + ∑ s : I, Finsupp.single (J.E s) (c s)) P =
      inverseTransformDivisor J.p B P :=
  apply_eq_of_notMem_range_E J
    (notMem_range_E_of_map_genericPoint hX J (map_genericPoint_of_valuationOver_eq hX J h)) c

end Junction

section Chain

variable {T : StabilizedSmallKltTail} {C : StabilizedSmallKltTail.TerminalChain T}

/-- The junction morphisms `p_i` of a terminal chain are dominant. -/
private lemma isDominant_junction_p (i : ℕ) : IsDominant (C.junction i).p :=
  (C.junction i).isBirationalMorphism.isDominant

attribute [local instance] isDominant_junction_p

/-- Along the `i`-th bridge: if `P` on `Y_i` has `ord_P = ord_{Γ_i}` for a prime divisor `Γ_i` of
`X_i` and `coeff_P Θ_i = c`, then every model `V_k` of the bridge carries a prime divisor `Q` with
`ord_Q = ord_{Γ_i}` on `k(Z_i)` and `coeff_Q Θ_k = c`. -/
private lemma bridge_invariant (i : ℕ) {P : MMP.Mori.PrimeDivisor (C.junction i).Y}
    {Γi : MMP.Mori.PrimeDivisor (T.X i)}
    (hP : P.valuationOver (C.junction i).p = Γi.divisorialValuation) {c : ℚ}
    (hc : (C.junction i).Θ.coeff P = c) :
    ∀ k ≤ (C.bridge i).P.m, ∃ Q : MMP.Mori.PrimeDivisor ((C.bridge i).P.model k),
      ∃ _ : IsDominant ((C.bridge i).P.toBase k),
        Q.valuationOver ((C.bridge i).P.toBase k) =
          Γi.divisorialValuation.comap (functionFieldMap (T.f i)) ∧
        ((C.bridge i).P.boundary k).coeff Q = c := by
  have hX := (T.isFourfoldStepDiagram i).isNormalVariety_minus
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨P, inferInstanceAs (IsDominant ((C.junction i).p ≫ T.f i)), ?_, ?_⟩
    · change P.valuationOver ((C.junction i).p ≫ T.f i) = _
      rw [valuationOver_comp, hP]
    · change (C.bridge i).Θ' P = c
      obtain ⟨a', -, hΘ'⟩ := (C.bridge i).isDecreasedBoundary
      obtain ⟨a, -, hΘ⟩ := (C.junction i).Θ_eq
      rw [← hc, DivisorWithCoeffs.coeff_apply, hΘ', hΘ, apply_eq_of_valuationOver_eq hX _ hP,
        apply_eq_of_valuationOver_eq hX _ hP]
  | succ k ih =>
    intro hk
    obtain ⟨Q, hd, hQ, hQc⟩ := ih (Nat.le_of_succ_le hk)
    have hk' : k < (C.bridge i).P.m := hk
    have hsd := (C.bridge i).P.isFourfoldStepDiagram k hk'
    have : IsIntegral ((C.bridge i).P.T k) := hsd.isNormalVariety_target.1.toIsIntegral
    have : IsDominant ((C.bridge i).P.g k) := hsd.isBirationalMorphism_minus.isDominant
    have : IsDominant ((C.bridge i).P.gp k) :=
      hsd.isSmallMorphism_plus.isBirationalMorphism.isDominant
    obtain ⟨Q', hQ'v, hQ'c⟩ := exists_valuationOver_eq_and_flipTransform_apply
      ((C.bridge i).isSmallMorphism k hk') hsd.isSmallMorphism_plus Q
    have hgh : (C.bridge i).P.toBase k = (C.bridge i).P.g k ≫ (C.bridge i).P.h k :=
      (C.bridge i).P.modelMap_eq k hk'
    have : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k) := hgh ▸ hd
    have : IsDominant ((C.bridge i).P.h k) :=
      IsDominant.of_comp ((C.bridge i).P.g k) ((C.bridge i).P.h k)
    have hπ : (C.bridge i).P.πY k = (C.bridge i).P.gp k ≫ (C.bridge i).P.h k :=
      (C.bridge i).P.πY_eq k hk'
    have hd' : IsDominant ((C.bridge i).P.πY k) := by
      rw [hπ]
      infer_instance
    refine ⟨Q', hd', ?_, ?_⟩
    · change Q'.valuationOver ((C.bridge i).P.πY k) = _
      rw [valuationOver_congr Q' hπ, valuationOver_comp, hQ'v, ← valuationOver_comp,
        ← valuationOver_congr Q hgh, hQ]
    · rw [← hQc]
      change ((C.bridge i).P.ΘY k) Q' = ((C.bridge i).P.boundary k) Q
      rw [(C.bridge i).P.ΘY_eq k hk']
      exact hQ'c _

/-- Along the junctions: `Y_i` carries a prime divisor `P` with `ord_P = ord_{Γ_i}`, for a prime
divisor `Γ_i` of `X_i` with `ord_{Γ_i}` corresponding to `ord_S`, and `coeff_P Θ_i = c`. -/
private lemma junction_invariant (S : C.Label) {Γ : MMP.Mori.PrimeDivisor (T.X 0)}
    (hS : inverseTransformPrimeDivisor (C.junction 0).p Γ = some S.1) (i : ℕ) :
    ∃ P : MMP.Mori.PrimeDivisor (C.junction i).Y, ∃ Γi : MMP.Mori.PrimeDivisor (T.X i),
      T.Corresponds i (StabilizedSmallKltTail.TerminalChain.labelValuation S)
          Γi.divisorialValuation ∧
        P.valuationOver (C.junction i).p = Γi.divisorialValuation ∧
        (C.junction i).Θ.coeff P = (T.B 0).coeff Γ := by
  induction i with
  | zero =>
    have hX := (T.isFourfoldStepDiagram 0).isNormalVariety_minus
    have hη := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hS).1
    have hv : S.1.valuationOver (C.junction 0).p = Γ.divisorialValuation :=
      valuationOver_eq_divisorialValuation _
        (MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective
          (C.junction 0).isBirationalMorphism).2 _ _ hη
    refine ⟨S.1, Γ, hv.symm, hv, ?_⟩
    obtain ⟨a, -, hΘ⟩ := (C.junction 0).Θ_eq
    rw [DivisorWithCoeffs.coeff_apply, hΘ, apply_eq_of_valuationOver_eq hX _ hv,
      inverseTransformDivisor_apply_of_eq_some hS]
    rfl
  | succ i ih =>
    obtain ⟨P, Γi, hcorr, hP, hc⟩ := ih
    obtain ⟨Q, hd, hQ, hQc⟩ := bridge_invariant i hP hc _ le_rfl
    have hbir : biregularLocus (C.bridge i).e.hom = ⊤ :=
      top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff _).mpr inferInstance))
    have hV : (C.bridge i).e.hom Q.genericPoint ∈ biregularLocus (C.bridge i).e.hom := by
      rw [hbir]
      trivial
    have hx1 : Order.coheight ((C.bridge i).e.hom Q.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _ hV]
      exact Q.coheight_genericPoint
    obtain ⟨P', hP'⟩ : ∃ P' : MMP.Mori.PrimeDivisor (C.junction (i + 1)).Y,
        P'.genericPoint = (C.bridge i).e.hom Q.genericPoint :=
      ⟨_, AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hx1⟩
    have hinv : inverseTransformPrimeDivisor (C.bridge i).e.hom P' = some Q :=
      MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
        hP'.symm hV
    -- the valuation of `P'` on `k(Z_i)`
    have he := valuationOver_eq_divisorialValuation (C.bridge i).e.hom
      (MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective
        (isBirationalMorphism_of_isIso (C.bridge i).e.hom)).2 Q P' hP'.symm
    have hQ' : (P'.valuationOver (C.junction (i + 1)).p).comap (functionFieldMap (T.fp i)) =
        Γi.divisorialValuation.comap (functionFieldMap (T.f i)) := by
      rw [← hQ, valuationOver_congr Q (C.bridge i).toBase_end_eq, valuationOver_comp, he,
        ← valuationOver_comp]
      rfl
    -- the transport of `Γ_i` to `X_{i+1}`
    obtain ⟨Γi', hΓi'v, -⟩ := exists_valuationOver_eq_and_flipTransform_apply
      (T.isStabilizedSmallKltTail.isSmallFrom_zero i (Nat.zero_le i))
      (T.toStepSequence.isSmallMorphism_fp i) Γi
    have hw : P'.valuationOver (C.junction (i + 1)).p = Γi'.divisorialValuation := by
      refine Valuation.ext fun t => ?_
      obtain ⟨u, rfl⟩ := (MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective
        (T.isFourfoldStepDiagram i).isBirationalMorphism_plus).2 t
      exact congrArg (fun v => v u) (hQ'.trans hΓi'v.symm)
    refine ⟨P', Γi', ⟨Γi.divisorialValuation, hcorr, hΓi'v⟩, hw, ?_⟩
    rw [← hQc]
    change (C.junction (i + 1)).Θ P' = (C.bridge i).P.endBoundary Q
    rw [(C.bridge i).endBoundary_eq, inverseTransformDivisor_apply_of_eq_some hinv]

end Chain

namespace StabilizedSmallKltTail

namespace TerminalChain

/-- A label `S_h` of a terminal chain that is the strict transform `p_0⁻¹_* Γ` of a prime divisor
`Γ` of `X_0` that is a component of `B_0` has label coefficient `b_h^M = coeff_Γ B_0` at every
model `M` of the chain. -/
@[mmp "lem_oai4_c1_original_labels_fixed"]
public theorem isLabelCoefficient_coeff_of_inverseTransformPrimeDivisor_eq_some
    {T : StabilizedSmallKltTail} {C : TerminalChain T} (S : C.Label)
    {Γ : MMP.Mori.PrimeDivisor (T.X 0)} (_hΓ : (T.B 0).coeff Γ ≠ 0)
    (hS : inverseTransformPrimeDivisor (C.junction 0).p Γ = some S.1) (x : C.ModelIndex) :
    C.IsLabelCoefficient S x ((T.B 0).coeff Γ) := by
  obtain ⟨i, y⟩ := x
  obtain ⟨P, Γi, hcorr, hP, hc⟩ := junction_invariant S hS i
  rcases y with _ | k
  · exact Or.inl ⟨P, ⟨_, hcorr, hP⟩, hc⟩
  · obtain ⟨Q, hd, hQ, hQc⟩ := bridge_invariant i hP hc k.1 k.2.le
    exact Or.inl ⟨Q, ⟨_, hcorr, hd, hQ⟩, hQc⟩

end TerminalChain

end StabilizedSmallKltTail

end Labels

/-! ### A vertical contraction of a birational morphism is birational -/

/-- If `g` is surjective and `W` is dense, a restriction `W ⟶ V` of `g` that is a closed
immersion is surjective: its range is closed and contains the dense set `V ∩ g(W)`. -/
private lemma surjective_resLE_of_dense {X Y : Scheme} (g : X ⟶ Y) (hg : Function.Surjective g)
    {W : X.Opens} (hW : Dense (W : Set X)) {V : Y.Opens} (hle : W ≤ g ⁻¹ᵁ V)
    [IsClosedImmersion (g.resLE V W hle)] : Surjective (g.resLE V W hle) := by
  refine ⟨Set.range_eq_univ.mp <|
    (g.resLE V W hle).isClosedEmbedding.isClosed_range.closure_eq.symm.trans <|
      Dense.closure_eq <| ((hg.denseRange.dense_image g.continuous hW).preimage
        V.ι.isOpenEmbedding.isOpenMap).mono ?_⟩
  rintro y ⟨x, hx, hxy⟩
  refine ⟨⟨x, hx⟩, V.ι.isOpenEmbedding.injective ?_⟩
  rw [← hxy]
  change (g.resLE V W hle ≫ V.ι) ⟨x, hx⟩ = g x
  rw [Scheme.Hom.resLE_comp_ι]
  rfl

/-- **A vertical contraction of a birational morphism is birational.** If `U` is a projective
`k`-variety, `h : U ⟶ Z` is a projective birational morphism of `k`-schemes, `R` an extremal
ray of `NE̅(U)` all of whose curves are contracted by `h`, and `g : U ⟶ V` is the contraction of
`R`, then `g` is a birational morphism. -/
@[mmp "lem_oai4_vertical_ray_c"]
public theorem isBirationalMorphism_of_isContractionOfRay {k : Type u} [Field k]
    {U V Z : Scheme.{u}} {sU : U ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} (hU : MMP.Mori.IsProjectiveVariety k sU)
    {h : U ⟶ Z} (hh : IsProjectiveMorphism h)
    (hhb : IsBirationalMorphism h) (hZ : h ≫ sZ = sU)
    {R : Set (NumericalCurveClasses sU)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sU : Set (NumericalCurveClasses sU)) R)
    (hRh : ∀ C : ProperCurve sU, OneCycle.numericalClass sU (C.cycle ℝ) ∈ R → C.IsContractedBy h)
    {g : U ⟶ V} (hg : IsContractionOfRay sU sV R g) :
    IsBirationalMorphism g := by
  obtain ⟨h', hh', -⟩ := existsUnique_comp_eq_of_isContractionOfRay hU hh hZ hR hRh hg
  obtain ⟨hVv, -⟩ := hg.isNormalVariety_target
  obtain ⟨hUv, -⟩ := hg.isNormalVariety_source
  have := hUv.toIsIntegral
  have := hVv.toIsIntegral
  have : IsSeparated sV := hVv.toIsSeparated
  have : V.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from sV]
    infer_instance⟩
  obtain ⟨W, hW, _⟩ := hhb.exists_isOpenImmersion
  -- `g` restricts to `φ : W ⟶ V' = h'⁻¹(h(W))`, and `φ ≫ h'|_{V'}` is `W ≅ h(W)`
  let O : Z.Opens := (W.ι ≫ h).opensRange
  have hle : W ≤ g ⁻¹ᵁ (h' ⁻¹ᵁ O) := fun x hx ↦
    show h' (g x) ∈ O by
      rw [← Scheme.Hom.comp_apply, hh']
      exact ⟨⟨x, hx⟩, rfl⟩
  let φ := g.resLE (h' ⁻¹ᵁ O) W hle
  have : IsIso (φ ≫ h'.resLE O _ le_rfl) := by
    rw [show φ ≫ h'.resLE O _ le_rfl = (W.ι ≫ h).isoOpensRange.hom by
      rw [← cancel_mono O.ι, Scheme.Hom.isoOpensRange_hom_ι]
      simp [φ, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, hh']]
    infer_instance
  have : IsClosedImmersion φ := .of_comp φ (h'.resLE O _ le_rfl)
  have := surjective_resLE_of_dense g hg.surjective (W.isOpen.dense hW) hle
  have : IsIso φ := isIso_of_isClosedImmersion_of_surjective φ
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE g W _ hW
    ⟨g hW.some, hle hW.some_mem⟩ hle this

end MMP.Fourfold
