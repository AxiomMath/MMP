module

public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
public import MMP.AlgebraicGeometry.MMP.Contraction.RelativeContraction
public import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
public import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial

/-!
# Cartier indices persist through klt-negative null steps

Let `(X, B)` be a projective klt pair with a `ℚ`-boundary and canonical divisor `K`, with `X`
`ℚ`-factorial, let `R` be a `(K + B)`-negative extremal ray of `NE̅(X)` and `f : X ⟶ V` its
contraction. Let `Bᵢ` be klt `ℚ`-boundaries such that, for one integer `m > 0`, every
`m (K + Bᵢ)` is a Cartier divisor, and every adjoint `Dᵢ = K + Bᵢ` is numerically trivial on `R`.
Let `f⁺ : X' ⟶ V` be the next model: an isomorphism when `f` is divisorial, and a flip of `f`
for some adjoint, with `X'` normal and `ℚ`-factorial, when `f` is small. Then, with
`D'ᵢ = K' + B'ᵢ` the birational transforms `(f⁺)⁻¹_* f_*`, every `m D'ᵢ` is Cartier, every
`(X', B'ᵢ)` is klt, and `Dᵢ`, `D'ᵢ` are the pull-backs of one `ℚ`-Cartier `ℚ`-divisor on `V`;
in particular the step is crepant for every adjoint `Dᵢ`.

## Main results

* `MMP.Fourfold.IsKltPair.isKltPair_flipTransform_of_isContractionOfRay`.

## Implementation notes

The source works over `ℂ`; the statement is made over any field `k`, the klt condition
`MMP.Fourfold.IsKltPair` already forcing `k` to be algebraically closed of characteristic zero.
The index set of the adjoints is an arbitrary type. The divisorial case `X' = V` is the case
where `f⁺` is an isomorphism, so that both cases are stated with the one transform
`MMP.Mori.flipTransform f f⁺`, which is `f_*` followed by the identification along `f⁺`.
Crepancy is stated in its descended form: `Dᵢ = f^* Mᵢ` and `D'ᵢ = (f⁺)^* Mᵢ` for a
`ℚ`-Cartier `Mᵢ` on `V` (`MMP.Mori.QDivisor.IsPullback`), which gives the equality of the
pull-backs of `Dᵢ` and `D'ᵢ` to every common resolution.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][OAI4]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-! ### Klt across a crepant diagram -/

section Klt

/-- **Klt crosses a crepant diagram.** Let `f : X ⟶ V ⟵ X' : f'` be proper birational morphisms
of normal varieties, with canonical divisors `K`, `K'`, `K_V` of dimension `n` such that
`f_* K = K_V = f'_* K'`. If `K + B = f^*(K_V + B_V)` and `K' + B' = f'^*(K_V + B_V)` for one
`ℚ`-Cartier `K_V + B_V`, then `(X', B')` is klt as soon as `(X, B)` is and `B' ≥ 0`: a divisor
over `X'` is a divisor over `V`, which is realized over `X` with the same valuation, and the
three discrepancies agree by crepant invariance. -/
private theorem isKltPair_of_isPullback {k : Type} [Field k] {X X' V : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of k)} (hV : IsNormalVariety k sV)
    {f : X ⟶ V} {fp : X' ⟶ V} [IsProper f] [IsProper fp]
    (hX : IsNormalVariety k (f ≫ sV)) (hX' : IsNormalVariety k (fp ≫ sV))
    (hfb : IsBirationalMorphism f) (hfpb : IsBirationalMorphism fp)
    {n : ℕ} {K : Divisor X} {K' : Divisor X'} {KV : Divisor V}
    (hK : K.IsCanonicalDivisor (f ≫ sV) n) (hK' : K'.IsCanonicalDivisor (fp ≫ sV) n)
    (hKV : KV.IsCanonicalDivisor sV n)
    (hfK : RationalMap.transformDivisor (X := X) f.toRationalMap K = KV)
    (hfpK : RationalMap.transformDivisor (X := X') fp.toRationalMap K' = KV)
    {B : QDivisor X} {B' : QDivisor X'} {BV : QDivisor V}
    (hBV : (Divisor.toQDivisor KV + BV).IsQCartier)
    (hf : ∃ h, (Divisor.toQDivisor KV + BV).IsPullback f h (Divisor.toQDivisor K + B))
    (hfp : ∃ h, (Divisor.toQDivisor KV + BV).IsPullback fp h (Divisor.toQDivisor K' + B'))
    (hB : IsKltPair (f ≫ sV) B) (hB' : ∀ P, 0 ≤ B'.coeff P) :
    IsKltPair (fp ≫ sV) B' := by
  have := hB.1.isAlgClosed
  have := hB.1.charZero
  have hPV : MMP.Mori.IsPair sV BV := ⟨hV, n, KV, hKV, hBV⟩
  obtain ⟨hP', hcr'⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hPV fp hX' hfpb hKV hK'
    (Or.inr ⟨inferInstance, hfpK, hfp⟩)
  obtain ⟨-, hcr⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hPV f hX hfb hKV hK
    (Or.inr ⟨inferInstance, hfK, hf⟩)
  refine ⟨⟨‹_›, ‹_›, hP', hB'⟩, fun n' D b hb => ?_⟩
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hb).symm.trans
      hK'.topologicalKrullDim_eq
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP' hK' D
  obtain ⟨hDp, rfl⟩ := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy ha b).mp hb
  set EV := MMP.Mori.compDivisorOver fp hX' hfpb D
  have hEV := (hcr' D EV (MMP.Mori.valuation_compDivisorOver fp hX' hfpb D) a).mp ha
  have hEVp : IsProper EV.f := by change IsProper (D.f ≫ fp); infer_instance
  obtain ⟨D₁, hD₁, -⟩ := MMP.Flips.ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq
    hV.1 f hX.1 hfb ⟨EV, hEVp⟩
  have h1 := (hcr D₁.toDivisorOver EV hD₁.symm a).mpr hEV
  exact hB.2 _ _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy h1 D₁.isProper)

end Klt

/-! ### Prime divisors across the two maps -/

section PrimeDivisors

/-- **Prime divisors across two small maps.** Let `f : X ⟶ V ⟵ X' : f'` with `f` proper
birational, `V` a normal variety and `f'` small. Every prime divisor `P'` of `X'` has a prime
divisor `P` of `X` whose coefficient in any `D` is that of `P'` in the strict transform
`(f')⁻¹_* f_* D`, and at which the pull-backs of any Cartier divisor `G` of `V` along `f` and
along `f'` have the same coefficient: both lie over the same prime divisor of `V`, with
isomorphic local rings. -/
private theorem exists_primeDivisor_flipTransform_apply {k : Type} [Field k]
    {X V X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {f : X ⟶ V} {fp : X' ⟶ V}
    (hV : IsNormalVariety k sV) [IsProper f] (hfb : IsBirationalMorphism f)
    (hfp : IsSmallMorphism sX' sV fp) (P' : MMP.Mori.PrimeDivisor X') :
    ∃ P : MMP.Mori.PrimeDivisor X,
      (∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X), flipTransform f fp D P' = D P) ∧
      ∀ {G : Divisor V} {hG : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G.supp}
        {hG' : ∀ W : irreducibleComponents X', fp (componentGenericPoint X' W) ∉ G.supp}
        {G₁ : Divisor X} {G₂ : Divisor X'}, G.IsCartier → G.IsPullback f hG G₁ →
          G.IsPullback fp hG' G₂ → G₁.coeff P = G₂.coeff P' := by
  have := hfb.isDominant
  have := hfp.isBirationalMorphism.isDominant
  obtain ⟨P, Q, -, hPQ, hP'Q⟩ :=
    exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hV hfb hfp P'
  have hP := map_genericPoint_eq_of_image_eq P Q hPQ
  have hP' := map_genericPoint_eq_of_image_eq P' Q hP'Q
  obtain ⟨P₀, hP₀, htr⟩ :=
    exists_eq_genericPoint_flipTransform_apply hfb hfp P' P.genericPoint (hP.trans hP'.symm)
  obtain rfl : P₀ = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hP₀.symm
  have := isIso_stalkMap_of_map_eq_genericPoint hfb hP
  have := isIso_stalkMap_of_map_eq_genericPoint hfp.isBirationalMorphism hP'
  refine ⟨P₀, htr, fun hGc h₁ h₂ => ?_⟩
  rw [MMP.Positivity.coeff_eq_of_isPullback P₀ Q hP hGc h₁,
    MMP.Positivity.coeff_eq_of_isPullback P' Q hP' hGc h₂]

/-- **Push-forward of a strict transform.** For `f : X ⟶ V ⟵ X' : f'` with `f` proper
birational and `f'` small, `f'_* (f')⁻¹_* f_* D = f_* D`. -/
private theorem transformDivisor_flipTransform {k : Type} [Field k] {X X' V : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of k)} (hV : IsNormalVariety k sV) {f : X ⟶ V} {fp : X' ⟶ V} [IsProper f]
    (hX : IsNormalVariety k (f ≫ sV)) (hfb : IsBirationalMorphism f)
    (hfp : IsSmallMorphism (fp ≫ sV) sV fp) {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor (X := X') fp.toRationalMap (flipTransform f fp D) =
      RationalMap.transformDivisor (X := X) f.toRationalMap D := by
  haveI : IsProper fp := hfp.isProper
  refine Finsupp.ext fun Q => ?_
  obtain ⟨P, hP, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hV hX hfb Q
  obtain ⟨P', hP', -, htr'⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
    hV hfp.isNormalVariety_source hfp.isBirationalMorphism Q
  obtain ⟨P₀, hP₀, hft⟩ :=
    exists_eq_genericPoint_flipTransform_apply hfb hfp P' P.genericPoint (hP.trans hP'.symm)
  obtain rfl : P₀ = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hP₀.symm
  rw [htr', htr, hft]

/-- **Push-forward along a small morphism.** If `f' : X' ⟶ V` is small onto a normal variety,
every prime divisor `P'` of `X'` maps onto a prime divisor `Q` of `V`, and the coefficient of
`Q` in `f'_* D` is the coefficient of `P'` in `D`. -/
private theorem exists_primeDivisor_transformDivisor_apply {k : Type} [Field k] {X' V : Scheme.{0}}
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of k)} (hV : IsNormalVariety k sV) {fp : X' ⟶ V}
    (hfp : IsSmallMorphism (fp ≫ sV) sV fp) (P' : MMP.Mori.PrimeDivisor X') :
    ∃ Q : MMP.Mori.PrimeDivisor V, ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X'),
      RationalMap.transformDivisor (X := X') fp.toRationalMap D Q = D P' := by
  haveI : IsProper fp := hfp.isProper
  have hfpb := hfp.isBirationalMorphism
  haveI := hfpb.isDominant
  obtain ⟨-, Q, -, -, hP'Q⟩ := exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hV
    (isBirationalMorphism_of_isIso (𝟙 V)) hfp P'
  have hQ := map_genericPoint_eq_of_image_eq P' Q hP'Q
  obtain ⟨E, hE, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hV hfp.isNormalVariety_source
      hfpb Q
  haveI := isIso_stalkMap_of_map_eq_genericPoint hfpb hQ
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (V.presheaf.stalk (fp E.genericPoint)) := by rw [hE]; infer_instance
  have hEP : E = P' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.eq_of_isIso_stalkMap fp hfpb.functionFieldMap_bijective (hQ.trans hE.symm))
  exact ⟨Q, fun D => by rw [htr, hEP]⟩

/-- Push-forward along a small morphism onto a normal variety is injective on divisors. -/
private theorem transformDivisor_injective_of_isSmallMorphism {k : Type} [Field k]
    {X' V : Scheme.{0}} [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of k)} (hV : IsNormalVariety k sV) {fp : X' ⟶ V}
    (hfp : IsSmallMorphism (fp ≫ sV) sV fp) {R : Type} [AddCommMonoid R] :
    Function.Injective
      (RationalMap.transformDivisor (X := X') fp.toRationalMap : DivisorWithCoeffs R X' → _) := by
  intro D₁ D₂ h
  refine Finsupp.ext fun P' => ?_
  obtain ⟨Q, hQ⟩ := exists_primeDivisor_transformDivisor_apply hV hfp P'
  rw [← hQ D₁, ← hQ D₂, h]

/-- An isomorphism onto a normal variety is a small morphism. -/
private theorem isSmallMorphism_of_isIso {k : Type} [Field k] {X V : Scheme.{0}} [IsIntegral X]
    [IsNormal X] {sV : V ⟶ Spec (.of k)} (hV : IsNormalVariety k sV) (f : X ⟶ V) [IsIso f] :
    IsSmallMorphism (f ≫ sV) sV f where
  isNormalVariety_source := by
    haveI : AlgebraicGeometry.IsVariety k sV := hV.1
    exact ⟨(MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance,
      inferInstance⟩, inferInstance⟩
  isNormalVariety_target := hV
  comp_eq := rfl
  isProper := inferInstance
  isBirationalMorphism := isBirationalMorphism_of_isIso f
  two_le_codimension := by
    rw [(exceptionalSet_eq_bot_iff f).mpr inferInstance, le_closedsCodimension_iff]
    intro W hW
    obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
    exact absurd (hW hx) (by simp)

/-- **Pull-backs along a small map are strict transforms.** Along `f : X ⟶ V ⟵ X' : f'`, with `f`
proper birational and `f'` small, the pull-back along `f'` of a Cartier divisor `G` of `V` is the
strict transform `(f')⁻¹_* f_* (f^* G)`. -/
private theorem pullback_eq_flipTransform {k : Type} [Field k]
    {X V X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {f : X ⟶ V} {fp : X' ⟶ V}
    (hV : IsNormalVariety k sV) [IsProper f] (hfb : IsBirationalMorphism f)
    (hfp : IsSmallMorphism sX' sV fp) {G : Divisor V} (hGc : G.IsCartier)
    {hG : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G.supp}
    (hG' : ∀ W : irreducibleComponents X', fp (componentGenericPoint X' W) ∉ G.supp)
    {L : Divisor X} (hGL : G.IsPullback f hG L) :
    G.pullback hGc hG' = flipTransform f fp L := by
  refine Finsupp.ext fun P' => ?_
  obtain ⟨P, htr, hcoeff⟩ := exists_primeDivisor_flipTransform_apply hV hfb hfp P'
  rw [htr]
  exact (hcoeff hGc hGL (Divisor.isPullback_pullback hGc hG')).symm

/-- The strict transform across `f : X ⟶ V ⟵ X' : f'` preserves a relation `L = m (K + B)`
between a divisor, a divisor and a `ℚ`-divisor. -/
private theorem toQDivisor_flipTransform_eq_zsmul {k : Type} [Field k]
    {X V X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {f : X ⟶ V} {fp : X' ⟶ V}
    (hV : IsNormalVariety k sV) [IsProper f] (hfb : IsBirationalMorphism f)
    (hfp : IsSmallMorphism sX' sV fp) {L K : Divisor X} {B : QDivisor X} {m : ℤ}
    (hL : Divisor.toQDivisor L = m • (Divisor.toQDivisor K + B)) :
    Divisor.toQDivisor (flipTransform f fp L) =
      m • (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B) := by
  refine Finsupp.ext fun P' => ?_
  obtain ⟨P, htr, -⟩ := exists_primeDivisor_flipTransform_apply hV hfb hfp P'
  change ((flipTransform f fp L P' : ℤ) : ℚ) =
    m • (((flipTransform f fp K P' : ℤ) : ℚ) + flipTransform f fp B P')
  rw [htr, htr, htr]
  exact congrArg (fun H : QDivisor X => H P) hL

end PrimeDivisors

/-! ### Canonical divisors across the two maps -/

section Canonical

/-- The push-forward of a canonical divisor along a proper birational morphism of normal varieties
over a perfect field is a canonical divisor. -/
private theorem isCanonicalDivisor_transformDivisor {k : Type} [Field k] [PerfectField k]
    {X V : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of k)} (hV : IsNormalVariety k sV) {f : X ⟶ V} [IsProper f]
    (hX : IsNormalVariety k (f ≫ sV)) (hfb : IsBirationalMorphism f) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor (f ≫ sV) n) :
    Divisor.IsCanonicalDivisor sV n (RationalMap.transformDivisor (X := X) f.toRationalMap K) := by
  haveI : AlgebraicGeometry.IsVariety k sV := hV.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sV) := hX.1
  haveI := hfb.isDominant
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor sV hV
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV (f ≫ sV) hfb).trans
      hK.topologicalKrullDim_eq)
  exact MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hV hX hfb hK₀ hK

/-- **The strict transform of a canonical divisor is canonical.** Across `f : X ⟶ V ⟵ X' : f'`,
with `f` proper birational and `f'` small, `(f')⁻¹_* f_* K` is a canonical divisor of `X'` for
every canonical divisor `K` of `X`: some canonical divisor of `X'` pushes forward to `f_* K`, and
push-forward along `f'` is injective. -/
private theorem isCanonicalDivisor_flipTransform {k : Type} [Field k] [PerfectField k]
    {X X' V : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of k)} (hV : IsNormalVariety k sV) {f : X ⟶ V} {fp : X' ⟶ V} [IsProper f]
    (hX : IsNormalVariety k (f ≫ sV)) (hfb : IsBirationalMorphism f)
    (hfp : IsSmallMorphism (fp ≫ sV) sV fp) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor (f ≫ sV) n) :
    Divisor.IsCanonicalDivisor (fp ≫ sV) n (flipTransform f fp K) := by
  have hX' := hfp.isNormalVariety_source
  have hfpb := hfp.isBirationalMorphism
  haveI : AlgebraicGeometry.IsVariety k sV := hV.1
  haveI : AlgebraicGeometry.IsVariety k (fp ≫ sV) := hX'.1
  haveI : IsProper fp := hfp.isProper
  haveI := hfpb.isDominant
  have hKV := isCanonicalDivisor_transformDivisor hV hX hfb hK
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor (fp ≫ sV) hX'
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV (fp ≫ sV)
      hfpb).symm.trans hKV.topologicalKrullDim_eq)
  obtain ⟨K', hK', hK'V⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hV hX' hfpb hKV hK₀
  rwa [transformDivisor_injective_of_isSmallMorphism hV hfp
    ((transformDivisor_flipTransform hV hX hfb hfp K).trans hK'V.symm)]

end Canonical

/-! ### Rational multiples of pull-backs -/

section Pullback

/-- If `G = mM` is Cartier and `L = mD` its pull-back along `g`, then `D` is the pull-back of
the `ℚ`-divisor `M`. -/
private theorem isPullback_of_zsmul_eq {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y] {g : X ⟶ Y} {G : Divisor Y}
    (hGc : G.IsCartier) {hG : ∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ G.supp}
    {L : Divisor X} (hGL : G.IsPullback g hG L) {m : ℕ} (hm : 0 < m) {M : QDivisor Y}
    (hM : Divisor.toQDivisor G = (m : ℤ) • M) {D : QDivisor X}
    (hD : Divisor.toQDivisor L = (m : ℤ) • D)
    (hMs : ∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ M.supp) :
    M.IsPullback g hMs D := by
  intro m' hm' D' hD' hD'c
  have hm₀ : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm₁ : (m' : ℤ) ≠ 0 := by exact_mod_cast hm'.ne'
  have hD's : ∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ D'.supp :=
    fun Z hZ => hMs Z (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hm₁ hD'] at hZ)
  refine ⟨D'.pullback hD'c hD's, ?_, Divisor.isPullback_pullback hD'c hD's⟩
  have key : (m : ℤ) • D' = (m' : ℤ) • G := by
    apply Divisor.toQDivisor_injective
    rw [map_zsmul, map_zsmul, hD', hM, smul_smul, smul_smul, mul_comm]
  have hsupp : ∀ (n : ℤ) (H : Divisor Y), n ≠ 0 →
      (∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ H.supp) →
      ∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ (n • H).supp := by
    intro n H hn hH Z hZ
    refine hH Z ?_
    rwa [← Divisor.supp_toQDivisor, map_zsmul, QDivisor.supp_zsmul hn,
      Divisor.supp_toQDivisor] at hZ
  have h1 := (Divisor.isPullback_pullback hD'c hD's).zsmul hD'c (m : ℤ) (hsupp _ _ hm₀ hD's)
  have h2 := (hGL.zsmul hGc (m' : ℤ) (hsupp _ _ hm₁ hG)).of_eq key.symm
    (hB₂ := hsupp _ _ hm₀ hD's)
  have h3 : (m : ℤ) • D'.pullback hD'c hD's = (m' : ℤ) • L := h1.eq (hD'c.zsmul _) h2
  have h4 := congrArg Divisor.toQDivisor h3
  rw [map_zsmul, map_zsmul, hD, smul_smul, mul_comm, ← smul_smul] at h4
  ext E
  have := congrArg (fun H : QDivisor X => H.coeff E) h4
  simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this ⊢
  exact mul_left_cancel₀ (by exact_mod_cast hm.ne') this

end Pullback

/-! ### Cartier descent along the contraction -/

section Descent

/-- **Cartier descent along a klt-negative ray contraction** (Kollár–Mori 3.7(4)). Let `(X, B)`
be a projective klt pair, `f : X ⟶ V` the birational contraction, onto a projective variety, of
a `(K + B)`-negative extremal ray `R`. A Cartier divisor `L` of degree zero on every curve with
class in `R` is the pull-back `f^* G` of a Cartier divisor `G` on `V`. -/
private theorem exists_isPullback_of_isContractionOfRay {k : Type} [Field k] {X V : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian V] [IsNormal V]
    {sX : X ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} {K : Divisor X} {B : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ V}
    (hB : IsKltPair sX B) (hXp : MMP.Mori.IsProjectiveVariety k sX)
    (hVp : MMP.Mori.IsProjectiveVariety k sV) (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hf : IsContractionOfRay sX sV R f) (hfb : IsBirationalMorphism f)
    {L : Divisor X} (hLc : L.IsCartier)
    (hL0 : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ R →
      L.degreeOn k sX C.ι C.dim_le hLc = 0) :
    ∃ (G : Divisor V) (_ : G.IsCartier)
      (hG : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G.supp),
      G.IsPullback f hG L := by
  obtain ⟨n, hKn⟩ := hK
  have hP := hB.1
  have := hP.isAlgClosed
  have := hP.charZero
  have : AlgebraicGeometry.IsProjectiveVariety k sX := hXp
  have : AlgebraicGeometry.IsProjectiveVariety k sV := hVp
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : IsIntegral V := hf.isNormalVariety_target.1.toIsIntegral
  have := hfb.isDominant
  have hklt : MMP.Mori.IsKltPair sX n K B := (isKltPair_iff_mori_isKltPair sX hKn hP).mp hB
  obtain ⟨hq, hRay, hneg⟩ := hR
  have hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + B) hklt.1.2.2) R :=
    ⟨hRay.1, hRay.1.2.2.1, hneg⟩
  have hg : IsContractionOfFace k sX sV R f :=
    ⟨hXp, hVp, hf.comp_eq, hRay.1, hf.isContractedBy_iff, hf.isIso_app⟩
  have := hLc.isInvertibleModule_divisorialSheaf
  obtain ⟨LV, hLV, ⟨e⟩⟩ := exists_isInvertible_iso_pullback_of_isContractionOfFace hklt
    hP.nonneg hF hg L.divisorialSheaf hL0
  obtain ⟨E, hEc, ⟨e'⟩⟩ := MMP.Mori.exists_isCartier_divisorialSheaf_iso LV
  have hfE := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f E
  obtain ⟨e''⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (f := f) hEc hfE
  obtain ⟨u, hu⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e ≪≫ (Scheme.Modules.pullback f).mapIso e'.symm ≪≫ e''.symm)
  obtain ⟨uV, huV, rfl⟩ := exists_pullbackRationalFunction_eq hfb u
  have hG := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f
    (E + principalDivisor uV)
  refine ⟨E + principalDivisor uV, hEc.add (Divisor.isCartier_principalDivisor uV), hG, ?_⟩
  have hL : L = E.pullback hEc hfE + principalDivisor (pullbackRationalFunction f uV huV) := by
    rw [← hu, add_sub_cancel]
  rw [hL]
  exact (Divisor.isPullback_pullback hEc hfE).add hEc (Divisor.isCartier_principalDivisor uV) hG
    (Divisor.isPullback_principalDivisor uV huV)

end Descent

/-! ### The target of the contraction is projective -/

section Target

variable {X Z : Scheme.{0}} (ψ : X ⟶ Z) (hψ : ∀ V : Z.Opens, IsIso (ψ.app V))

include hψ

/-- If every `ψ.app V` is an isomorphism, nonempty opens have nonempty preimages. -/
private theorem nonempty_preimage_of_isIso_app (V : Z.Opens) [Nonempty V] :
    Nonempty (ψ ⁻¹ᵁ V) := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have hbot : ψ ⁻¹ᵁ V = ⊥ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => hne.false ⟨x, hx⟩
  haveI := Scheme.component_nontrivial Z V
  haveI := hψ V
  haveI : Subsingleton Γ(X, ψ ⁻¹ᵁ V) := by rw [hbot]; infer_instance
  obtain ⟨a, b, hab⟩ := exists_pair_ne Γ(Z, V)
  exact hab ((ConcreteCategory.bijective_of_isIso (ψ.app V)).1 (Subsingleton.elim _ _))

/-- The target of a morphism from an integral scheme with `ψ_* 𝒪_X = 𝒪_Z` is integral. -/
private theorem isIntegral_of_isIso_app [IsIntegral X] : IsIntegral Z where
  nonempty := ⟨ψ (Nonempty.some inferInstance)⟩
  component_integral V _ := by
    haveI := nonempty_preimage_of_isIso_app ψ hψ V
    haveI := hψ V
    exact Function.Injective.isDomain (ψ.app V).hom
      (ConcreteCategory.bijective_of_isIso (ψ.app V)).1

/-- A morphism with `ψ_* 𝒪_X = 𝒪_Z` is dominant. -/
private theorem isDominant_of_isIso_app : IsDominant ψ := by
  refine ⟨dense_iff_inter_open.mpr fun V hV ⟨z, hz⟩ => ?_⟩
  haveI : Nonempty (⟨V, hV⟩ : Z.Opens) := ⟨⟨z, hz⟩⟩
  obtain ⟨⟨x, hx⟩⟩ := nonempty_preimage_of_isIso_app ψ hψ ⟨V, hV⟩
  exact ⟨ψ x, hx, x, rfl⟩

omit hψ

variable {k : Type} [Field k]

/-- Every proper curve is contracted by the structure morphism. -/
private theorem isContractedBy_structure (sX : X ⟶ Spec (.of k)) (C : ProperCurve sX) :
    C.IsContractedBy sX :=
  fun _ _ => Subsingleton.elim _ _

/-- Over the base point, the natural map `N₁(X / Spec k) → N₁(X)` is bijective. -/
private theorem relativeToAbsolute_bijective (sX : X ⟶ Spec (.of k)) :
    Function.Bijective (relativeToAbsolute sX sX) := by
  refine ⟨?_, fun z => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX sX z
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (mem_relativeNumericallyTrivial.mpr ((Submodule.Quotient.mk_eq_zero _).mp hz))
  · obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    have hZ : Z ∈ relativeOneCycles sX sX :=
      (Finsupp.mem_supported ℝ Z).mpr fun C _ => isContractedBy_structure sX C
    exact ⟨relativeNumericalClass sX sX ⟨Z, hZ⟩,
      isNaturalRelativeMap_relativeToAbsolute sX sX ⟨Z, hZ⟩⟩

/-- Two contractions of the same extremal ray of `NE̅(X)` agree up to an isomorphism of their
targets over `k`. -/
private theorem exists_isIso_comp_eq_of_isContractionOfRay {Z' : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsProjectiveVariety k sX)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {sZ : Z ⟶ Spec (.of k)} {sZ' : Z' ⟶ Spec (.of k)} {f : X ⟶ Z} {f' : X ⟶ Z'}
    (hf : IsContractionOfRay sX sZ R f) (hf' : IsContractionOfRay sX sZ' R f') :
    ∃ φ : Z ⟶ Z', IsIso φ ∧ f ≫ φ = f' ∧ φ ≫ sZ' = sZ := by
  have factor {W W' : Scheme.{0}} {sW : W ⟶ Spec (.of k)} {sW' : W' ⟶ Spec (.of k)} {g : X ⟶ W}
      {g' : X ⟶ W'} (hg : IsContractionOfRay sX sW R g) (hg' : IsContractionOfRay sX sW' R g') :
      ∃! h : W ⟶ W', g ≫ h = g' :=
    existsUnique_comp_eq_of_isContractionOfRay hX hg'.isProjectiveMorphism hg'.comp_eq hR
      (fun C hC => (hg'.isContractedBy_iff C).mpr hC) hg
  obtain ⟨φ, hφ, -⟩ := factor hf hf'
  obtain ⟨ψ, hψ, -⟩ := factor hf' hf
  have hφi : IsIso φ :=
    ⟨ψ, (factor hf hf).unique (by rw [← Category.assoc, hφ, hψ]) (Category.comp_id f),
      (factor hf' hf').unique (by rw [← Category.assoc, hψ, hφ]) (Category.comp_id f')⟩
  have : IsProper f := isProper_of_isProjectiveMorphism _ hf.isProjectiveMorphism
  have : IsIso f.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ f.c fun U => hf.isIso_app U.unop
  refine ⟨φ, hφi, hφ, (MMP.existsUnique_comp_eq_of_isIso_c f sX fun _ _ _ =>
    Subsingleton.elim (α := PrimeSpectrum k) _ _).unique ?_ hf.comp_eq⟩
  rw [← Category.assoc, hφ, hf'.comp_eq]

/-- **The target of the contraction of a negative extremal ray is projective.** Let `(X, B)` be
a projective klt pair and `f : X ⟶ W` the contraction of a `(K + B)`-negative extremal ray `R`.
Then `W` is projective: the contraction theorem over the base point contracts `R` onto a
projective variety, which is `W` up to isomorphism. -/
private theorem isProjectiveVariety_of_isContractionOfRay {W : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)}
    {f : X ⟶ W} (hB : IsKltPair sX B) (hXp : MMP.Mori.IsProjectiveVariety k sX)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hf : IsContractionOfRay sX sW R f) : MMP.Mori.IsProjectiveVariety k sW := by
  obtain ⟨n, hKn⟩ := hK
  have hP := hB.1
  have := hP.isAlgClosed
  have := hP.charZero
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hXp
  have hklt : MMP.Mori.IsKltPair sX n K B := (isKltPair_iff_mori_isKltPair sX hKn hP).mp hB
  have hS : MMP.Mori.IsProjectiveVariety k (𝟙 (Spec (.of k))) :=
    (AlgebraicGeometry.isProjectiveVariety_iff k _).mpr
      ⟨(MMP.Mori.isVariety_iff k _).mpr
        ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
        MMP.isProjectiveMorphism_of_isClosedImmersion _⟩
  haveI : AlgebraicGeometry.IsProjectiveVariety k (𝟙 (Spec (.of k))) := hS
  have hbij := relativeToAbsolute_bijective sX
  set e := LinearEquiv.ofBijective (relativeToAbsolute sX sX) hbij with hedef
  have hNimg : e '' (relativeClosedConeOfCurves sX sX : Set _) =
      (closedConeOfCurves sX : Set _) := by
    have := image_relativeClosedConeOfCurves_eq_inter_range sX (𝟙 (Spec (.of k))) sX
      (Category.comp_id sX)
    rw [hbij.2.range_eq, Set.inter_univ] at this
    exact this
  have hNpre : e.symm '' (closedConeOfCurves sX : Set _) =
      (relativeClosedConeOfCurves sX sX : Set _) := by
    rw [← hNimg, ← Set.image_comp]; simp
  obtain ⟨hq, hRay, hneg⟩ := hR
  have hFray : IsExtremalRay ℝ (relativeClosedConeOfCurves sX sX : Set _) (e ⁻¹' R) := by
    rw [← e.image_symm_eq_preimage, ← hNpre]
    exact MMP.ProgramBaseChange.isExtremalRay_image e.symm hRay
  have hset : IsProjectiveSetting k sX (𝟙 (Spec (.of k))) sX :=
    ⟨‹_›, ‹_›, hXp, hS, Category.comp_id sX⟩
  obtain ⟨Z, ψ, g, hψ⟩ := exists_isRelativeContractionOfFace_of_isNegativeExtremalFace hset hklt
    hP.nonneg ⟨hFray.1, hFray.1.2.2.1, fun z hz hz0 =>
      hneg (e z) hz fun h => hz0 (e.injective (by rw [h, map_zero]))⟩
  have happ := hψ.isIso_app
  haveI : IsIntegral Z := isIntegral_of_isIso_app ψ happ
  have hgp := hψ.isProjectiveMorphism
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hgp
  have hZv : MMP.Mori.IsVariety k g := (MMP.Mori.isVariety_iff k g).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hZp : MMP.Mori.IsProjectiveVariety k g :=
    (AlgebraicGeometry.isProjectiveVariety_iff k g).mpr ⟨hZv, hgp⟩
  haveI : IsDominant ψ := isDominant_of_isIso_app ψ happ
  haveI : IsIso ψ.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ ψ.c fun U => happ U.unop
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hXp.isProjective
  haveI : IsProper (ψ ≫ g) := by rw [hψ.comp_eq]; infer_instance
  haveI : IsProper ψ := IsProper.of_comp ψ g
  have hsurj : Function.Surjective ψ := by
    intro z
    have h1 : closure (Set.range ψ) = Set.univ := ψ.denseRange.closure_range
    rw [ψ.isClosedMap.isClosed_range.closure_eq] at h1
    exact Set.range_eq_univ.mp h1 z
  haveI : AlgebraicGeometry.IsProjectiveVariety k g := hZp
  haveI := IsProjectiveVariety.isQuasiProjectiveVariety k sX
  have hψR : IsContractionOfRay sX g R ψ :=
    { isNormalVariety_source := hf.isNormalVariety_source
      isNormalVariety_target := ⟨hZv, MMP.Mori.isNormal_of_isIso_c g ψ hZv
        (by rw [hψ.comp_eq]; exact hXp.toIsVariety)⟩
      comp_eq := hψ.comp_eq
      isProjectiveMorphism :=
        MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety sX g ψ hψ.comp_eq
      surjective := hsurj
      isIso_app := happ
      isContractedBy_iff := fun C => by
        rw [hψ.isContractedBy_iff C (isContractedBy_structure sX C)]
        change e (C.relativeClass sX _) ∈ R ↔ _
        rw [show e (C.relativeClass sX _) = OneCycle.numericalClass sX (C.cycle ℝ) from
          isNaturalRelativeMap_relativeToAbsolute sX sX _] }
  obtain ⟨φ, _, -, hφg⟩ := exists_isIso_comp_eq_of_isContractionOfRay hXp hRay hf hψR
  obtain ⟨N, i, hi, hic⟩ := hgp
  exact (AlgebraicGeometry.isProjectiveVariety_iff k sW).mpr
    ⟨hf.isNormalVariety_target.1, N, φ ≫ i, inferInstance, by rw [Category.assoc, hic, hφg]⟩

end Target

/-- **Cartier indices persist through klt-negative null steps.** Let `(X, B)` be a projective
`ℚ`-factorial klt pair with canonical divisor `K`, `R` a `(K + B)`-negative extremal ray of
`NE̅(X)` and `f : X ⟶ V` its contraction. Let `Bᵢ` be klt `ℚ`-boundaries such that each
`m (K + Bᵢ)` is Cartier and `K + Bᵢ` is numerically trivial on `R`. Let `f⁺ : X' ⟶ V` be
either an isomorphism, when `f` is divisorial, or, with `X'` `ℚ`-factorial, a `(K + Γ)`-flip of
`f` (`MMP.Fourfold.IsFlipOf`). Then for the transforms `K' = flipTransform f f⁺ K` and
`B'ᵢ = flipTransform f f⁺ Bᵢ`, every `m (K' + B'ᵢ)` is Cartier, every `(X', B'ᵢ)` is klt, and
`K + Bᵢ` and `K' + B'ᵢ` are the pull-backs along `f` and `f⁺` of one `ℚ`-Cartier `ℚ`-divisor
`Mᵢ` on `V`. -/
@[mmp "lem_fourfold_null_step_preserves_indices"]
public theorem IsKltPair.isKltPair_flipTransform_of_isContractionOfRay {k : Type} [Field k]
    {X V X' : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian V] [IsNormal V]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ V}
    (hB : IsKltPair sX B) (hXp : MMP.Mori.IsProjectiveVariety k sX) (hXQ : IsQFactorial sX)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hf : IsContractionOfRay sX sV R f)
    {ι : Type*} {Bi : ι → QDivisor X} {m : ℕ} (hBi : ∀ i, IsKltPair sX (Bi i)) (hm : 0 < m)
    (hmD : ∀ i, ∃ L : Divisor X, L.IsCartier ∧
      Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor K + Bi i))
    (hnull : ∀ i, ∃ h : (Divisor.toQDivisor K + Bi i).IsQCartier,
      ∀ u ∈ R, QDivisor.curveForm sX (Divisor.toQDivisor K + Bi i) h u = 0)
    {fp : X' ⟶ V}
    (hstep : (IsBirationalMorphism f ∧
        (∃ E : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = E.support) ∧
        IsIso fp ∧ fp ≫ sV = sX') ∨
      (IsQFactorial sX' ∧
        ∃ Γ : QDivisor X, IsFlipOf sX sV sX' (Divisor.toQDivisor K + Γ) f fp)) :
    ∀ i, (∃ L : Divisor X', L.IsCartier ∧ Divisor.toQDivisor L =
        (m : ℤ) • (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp (Bi i))) ∧
      IsKltPair sX' (flipTransform f fp (Bi i)) ∧
      ∃ (M : QDivisor V) (_ : M.IsQCartier)
        (hMf : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ M.supp)
        (hMfp : ∀ Z : irreducibleComponents X', fp (componentGenericPoint X' Z) ∉ M.supp),
        M.IsPullback f hMf (Divisor.toQDivisor K + Bi i) ∧
          M.IsPullback fp hMfp
            (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp (Bi i)) := by
  intro i
  have hV := hf.isNormalVariety_target
  haveI : IsIntegral V := hV.1.toIsIntegral
  haveI : LocallyOfFiniteType sV := hV.1.toLocallyOfFiniteType
  haveI : QuasiCompact sV := hV.1.toQuasiCompact
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hf.isProjectiveMorphism
  obtain ⟨hfb, hfpS⟩ : IsBirationalMorphism f ∧ IsSmallMorphism sX' sV fp := by
    rcases hstep with ⟨hfb, -, hiso, hcomp⟩ | ⟨-, Γ, hflip⟩
    · subst hcomp
      exact ⟨hfb, isSmallMorphism_of_isIso hV fp⟩
    · exact ⟨hflip.isSmallMorphism.isBirationalMorphism, hflip.isSmallMorphism_flip⟩
  have hVp := isProjectiveVariety_of_isContractionOfRay hB hXp hK hR hf
  obtain ⟨L, hLc, hL⟩ := hmD i
  obtain ⟨hq, hq0⟩ := hnull i
  have hL0 : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ R →
      L.degreeOn k sX C.ι C.dim_le hLc = 0 := by
    intro C hC
    have h := hq0 _ hC
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le _ hq hm L hLc hL] at h
    simpa [hm.ne'] using h
  obtain ⟨G, hGc, hG, hGL⟩ :=
    exists_isPullback_of_isContractionOfRay hB hXp hVp hK hR hf hfb hLc hL0
  obtain ⟨n, hKn⟩ := hK
  have hBi' := hBi i
  have hfs := hf.comp_eq
  have hfps := hfpS.comp_eq
  subst hfs hfps
  have hX := hf.isNormalVariety_source
  have hX' := hfpS.isNormalVariety_source
  have hfpb := hfpS.isBirationalMorphism
  haveI : IsProper fp := hfpS.isProper
  haveI := hfb.isDominant
  haveI := hfpb.isDominant
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  set M : QDivisor V := (m : ℚ)⁻¹ • Divisor.toQDivisor G with hMdef
  have hmM : Divisor.toQDivisor G = (m : ℤ) • M := by
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [hMdef, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    simp [hmq]
  have hM : M.IsQCartier := ⟨m, hm', G, hmM, hGc⟩
  have hMf := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f M
  have hMfp := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp M
  have hG' := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp G
  have key : Divisor.toQDivisor (G.pullback hGc hG') =
      (m : ℤ) • (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp (Bi i)) := by
    rw [pullback_eq_flipTransform hV hfb hfpS hGc hG' hGL]
    exact toQDivisor_flipTransform_eq_zsmul hV hfb hfpS hL
  have hpb := isPullback_of_zsmul_eq hGc hGL hm hmM hL hMf
  have hpb' := isPullback_of_zsmul_eq hGc (Divisor.isPullback_pullback hGc hG') hm hmM key hMfp
  refine ⟨⟨_, hGc.isCartier_pullback fp hG', key⟩, ?_, M, hM, hMf, hMfp, hpb, hpb'⟩
  haveI := hBi'.1.isAlgClosed
  have hfpK := transformDivisor_flipTransform hV hX hfb hfpS K
  have hMeq : Divisor.toQDivisor (RationalMap.transformDivisor (X := X) f.toRationalMap K) +
      RationalMap.transformDivisor (X := X) f.toRationalMap (Bi i) = M := by
    rw [← MMP.Positivity.transformDivisor_of_isPullback hV hX hfb hM hMf hpb, map_add,
      MMP.Flips.transformDivisor_toQDivisor f.toRationalMap]
  refine isKltPair_of_isPullback hV hX hX' hfb hfpb hKn
    (isCanonicalDivisor_flipTransform hV hX hfb hfpS hKn)
    (isCanonicalDivisor_transformDivisor hV hX hfb hKn) rfl hfpK (hMeq ▸ hM)
    (by rw [hMeq]; exact ⟨hMf, hpb⟩) (by rw [hMeq]; exact ⟨hMfp, hpb'⟩) hBi' fun P' => ?_
  obtain ⟨P, htr, -⟩ := exists_primeDivisor_flipTransform_apply hV hfb hfpS P'
  rw [DivisorWithCoeffs.coeff_apply, htr]
  exact hBi'.1.nonneg P

end MMP.Fourfold
