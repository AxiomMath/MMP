module

public import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ContractedDegree

/-!
# A crepant dlt lift is not nef over the base of a permitted step

Let `(X, B) → Z ← (X⁺, B⁺)` be a permitted step, with `f : X ⟶ Z` the contraction of a
`(K_X + B)`-negative extremal ray, and let `p : (U, Δ) ⟶ (X, B)` be a crepant dlt lift. Then
`K_U + Δ` is not nef over `Z` for `p ≫ f`.

The contraction `f` contracts some curve `C ⊆ X`: otherwise `f` is quasi-finite, hence finite,
hence (birational onto the normal `Z`) an isomorphism, and `ρ(X/Z) = 0`. Then `(K_X + B) · C < 0`
because `-(K_X + B)` is `f`-ample. Since `p` is proper and surjective, a curve `C̃ ⊆ U` maps onto
`C`; it is contracted by `p ≫ f`. Write `K_X = div(ω)` for a rational top form `ω`; crepancy says
exactly that `div(p^*ω) + Δ` is the pull-back `p^*(K_X + B)`, and `K_U ∼ div(p^*ω)`, so the
projection formula gives `(K_U + Δ) · C̃ = deg(C̃/C) (K_X + B) · C < 0`.

## Main results

* `MMP.Fourfold.IsPermittedStep.not_isRelativelyNef_of_isCrepantDltLift`: for a crepant dlt lift
  `p : (U, Δ) ⟶ (X, B)` of a permitted step, `K_U + Δ` is not nef over `Z`.
* `MMP.Mori.exists_properCurve_isContractedBy_of_not_locallyQuasiFinite`: a proper morphism
  that is not locally quasi-finite contracts a proper curve.

## Implementation notes

The canonical divisor `K_U` of `U` is any canonical divisor of `U` (over `k` by `p ≫ s_X`); over
a perfect field all canonical divisors are linearly equivalent, so relative nefness of
`K_U + Δ` does not depend on the choice.

The canonical divisor `K_X` is realized as `div(ω)` over the perfect base field; the crepancy of
`Δ` is compared with the discrepancies computed from the local generator `ω^{⊗m} / φ` of
`𝒪_X(m(K_X + B))`, where `φ` is a local equation of the Cartier divisor `m(K_X + B)`, through the
uniqueness of discrepancies. The image of `C̃` in `X` is the scheme-theoretic image, identified
with `C` since both are the reduced structure on the closure of the generic point of `C`.

## References

* [oai4] the fourfold source, the dlt bridge.
-/

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

section Crepancy

/-- The order of `c ^ m * g⁻¹` along a point, for nonzero rational functions `c` and `g`. -/
private theorem ord_zpow_mul_inv {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y)
    {c g : Y.functionField} (hc : c ≠ 0) (hg : g ≠ 0) (m : ℤ) :
    Y.ord (c ^ m * g⁻¹) z = m * Y.ord c z - Y.ord g z := by
  rw [Scheme.ord_mul (zpow_ne_zero _ hc) (inv_ne_zero hg), MMP.Mori.ord_zpow _ hc,
    ← zpow_neg_one, MMP.Mori.ord_zpow _ hg]
  ring

variable {k : Type u} [Field k] [PerfectField k] {X U : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]

omit [PerfectField k] in
/-- A form `τ` with `ord_Γ τ = m ord_Γ c - ord_Γ g + m N_Γ`, where `K_Γ = ord_Γ c + N_Γ` and
`ord_Γ g = E_Γ` on `V` for `E = m (K + B)`, generates `𝒪_X(m(K + B))` on `V`. -/
private theorem generatesOn_of_ordForm_eq {sX : X ⟶ Spec (.of k)} {n m : ℕ} {K E : Divisor X}
    {B : QDivisor X} (hE : Divisor.toQDivisor E = (m : ℤ) • (Divisor.toQDivisor K + B))
    {V : X.Opens} {τ : RationalPluriForms sX n m} (hτ0 : τ ≠ 0) {c g : X.functionField}
    (hK : ∀ Γ : MMP.Mori.PrimeDivisor X, ∃ NΓ : ℤ,
      (K.coeff Γ : ℤ) = X.ord c Γ.genericPoint + NΓ ∧
      (Γ.ordForm τ : ℤ) = m * X.ord c Γ.genericPoint - X.ord g Γ.genericPoint + m * NΓ)
    (hg : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ V).Nonempty →
      X.ord g Γ.genericPoint = E.coeff Γ) :
    GeneratesOn B m V τ := by
  refine ⟨hτ0, fun Γ hΓ => ?_⟩
  obtain ⟨NΓ, h₁, h₂⟩ := hK Γ
  have hCq : (E.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by
    rw [mul_add]
    simpa [zsmul_eq_mul] using congrArg (fun D : QDivisor X => D.coeff Γ) hE
  have h₁' : (K.coeff Γ : ℚ) = X.ord c Γ.genericPoint + NΓ := by exact_mod_cast h₁
  have h₂' : (Γ.ordForm τ : ℚ) = m * X.ord c Γ.genericPoint - X.ord g Γ.genericPoint
      + m * NΓ := by exact_mod_cast h₂
  have h₃ : (X.ord g Γ.genericPoint : ℚ) = E.coeff Γ := by exact_mod_cast hg Γ hΓ
  linear_combination h₂' - hCq - h₃ - (m : ℚ) * h₁'

/-- Coefficientwise crepancy: along a prime divisor `F` of `U`, the pull-back of a Cartier
multiple `E = m (K + B)` has coefficient `m (ord_F div(p^*ω) + Δ_F)` when `K = div(ω)`. -/
private theorem coeff_pullback_eq {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {p : U ⟶ X}
    [IsDominant p] [LocallyOfFiniteType (p ≫ sX)]
    (hY : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {n n' : ℕ} {K : Divisor X}
    (hK' : K.IsCanonicalDivisor sX n') {B : QDivisor X} {Δ : QDivisor U}
    (hcrep : IsCrepantBoundary sX n K B p hY hp Δ) {m : ℕ} (hm0 : 0 < m) {E : Divisor X}
    (hE : Divisor.toQDivisor E = (m : ℤ) • (Divisor.toQDivisor K + B)) (hEc : E.IsCartier)
    {hB : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉ E.supp}
    {Dp : Divisor U} (hDp : E.IsPullback p hB Dp) {ω : RationalPluriForms sX n' 1}
    (hω0 : ω ≠ 0) (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ)
    (F : MMP.Mori.PrimeDivisor U) :
    (Dp.coeff F : ℚ) =
      m * ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F + Δ.coeff F) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hK := (hcrep F).2.1
  obtain rfl : n = n' := by exact_mod_cast hK.1.symm.trans hK'.1
  have hn := hK.topologicalKrullDim_eq
  set D : DivisorOver k sX := ⟨U, p, hY, hp, F⟩ with hD
  obtain ⟨b, N', hb0⟩ := D.exists_ordPullback_eq hX hn
  have hb : ∀ (m : ℤ) (τ : RationalPluriForms sX n m), τ ≠ 0 → D.ordPullback τ =
      U.ord (functionFieldMap p ((ZTensorPower.basis b m).repr τ ())) F.genericPoint + m * N' :=
    hb0
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨V, hxV, φ, hφ⟩ := hEc (p F.genericPoint)
  let Z0 : irreducibleComponents X := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]
    simp⟩
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X) with hg_def
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  set c'' : X.functionField := c ^ (m : ℤ) * g⁻¹ with hc''_def
  have hc'' : c'' ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg)
  let τ : RationalPluriForms sX n m := c'' • ZTensorPower.basis b (m : ℤ) ()
  have hτr : (ZTensorPower.basis b (m : ℤ)).repr τ () = c'' := by simp [τ]
  have hτ0 : τ ≠ 0 := smul_ne_zero hc'' ((ZTensorPower.basis b (m : ℤ)).ne_zero ())
  have hKcoeff : ∀ Γ : MMP.Mori.PrimeDivisor X, ∃ NΓ : ℤ,
      (K.coeff Γ : ℤ) = X.ord c Γ.genericPoint + NΓ ∧
      (Γ.ordForm τ : ℤ) = m * X.ord c Γ.genericPoint - X.ord g Γ.genericPoint + m * NΓ := by
    intro Γ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    refine ⟨NΓ, ?_, ?_⟩
    · rw [← hωK Γ, hNΓ 1 ω hω0]
      simp [hc_def]
    · rw [hNΓ _ τ hτ0, hτr, hc''_def, ord_zpow_mul_inv _ hc hg]
  have hgord : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ V).Nonempty →
      X.ord g Γ.genericPoint = E.coeff Γ := by
    intro Γ hΓ
    rw [hφ Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
      Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents)
        Γ.component Z0]
  have hKY : (divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F =
      U.ord (functionFieldMap p c) F.genericPoint + N' := by
    have e : D.ordPullback ω = (divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F := by
      rw [coeff_divisorOfForm]
      rfl
    rw [← e, hb 1 ω hω0]
    simp [hc_def]
  have hcoeff : Dp.coeff F = U.ord (functionFieldMap p g) F.genericPoint :=
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hDp hφ F hxV Z0
  have hgY : functionFieldMap p g ≠ 0 := (map_ne_zero _).mpr hg
  have hcY : functionFieldMap p c ≠ 0 := (map_ne_zero _).mpr hc
  have hordτ : D.ordPullback τ = m * U.ord (functionFieldMap p c) F.genericPoint
      - U.ord (functionFieldMap p g) F.genericPoint + m * N' := by
    rw [hb _ τ hτ0, hτr, hc''_def, map_mul, map_zpow₀, map_inv₀, ord_zpow_mul_inv _ hcY hgY]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hdisc : IsDiscrepancy sX n K B D
      ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F - Dp.coeff F / m) := by
    refine ⟨hX, hK, m, hm0, ⟨E, hE, hEc⟩, V, hxV, τ,
      generatesOn_of_ordForm_eq hE hτ0 hKcoeff hgord, ?_⟩
    have e1 : (D.ordPullback τ : ℚ) = m * U.ord (functionFieldMap p c) F.genericPoint
        - U.ord (functionFieldMap p g) F.genericPoint + m * N' := by exact_mod_cast hordτ
    have e2 : ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F : ℚ) =
        U.ord (functionFieldMap p c) F.genericPoint + N' := by exact_mod_cast hKY
    have e3 : (Dp.coeff F : ℚ) = U.ord (functionFieldMap p g) F.genericPoint := by
      exact_mod_cast hcoeff
    rw [e1, e2, e3]
    field_simp
    ring
  have heq := IsDiscrepancy.eq (hcrep F) hdisc
  field_simp at heq
  linear_combination heq

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX)
    {p : U ⟶ X} [IsDominant p] (hp : IsBirationalMorphism p) {n : ℕ}
    (hn : topologicalKrullDim X = n) {m : ℤ} {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX p τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := hp.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX p hbij hd
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := pullbackForms_eq hω m τ ▸ h0
  have h1 : algebraMap X.functionField U.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- **Crepancy as a pull-back.** If `Δ` is the crepant boundary of `(X, B)` on `U` and
`K = div(ω)`, then `div(p^*ω) + Δ = p^*(K + B)`. -/
private theorem isPullback_divisorOfForm_add {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {p : U ⟶ X} [IsDominant p] [LocallyOfFiniteType (p ≫ sX)]
    (hY : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {n n' : ℕ} {K : Divisor X}
    (hK' : K.IsCanonicalDivisor sX n') {B : QDivisor X} {Δ : QDivisor U}
    (hcrep : IsCrepantBoundary sX n K B p hY hp Δ) {ω : RationalPluriForms sX n' 1}
    (hω0 : ω ≠ 0) (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ)
    (hLB : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉
      (Divisor.toQDivisor K + B).supp) :
    (Divisor.toQDivisor K + B).IsPullback p hLB
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX p ω)) + Δ) := by
  intro m hm D hD hDc
  have hB' : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉ D.supp :=
    fun Z hZ => hLB Z (by
      rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD] at hZ)
  refine ⟨D.pullback hDc hB', ?_, Divisor.isPullback_pullback hDc hB'⟩
  ext F
  simpa only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor, Int.cast_natCast] using
    coeff_pullback_eq hX hY hp hK' hcrep hm hD hDc (Divisor.isPullback_pullback hDc hB') hω0 hωK F

end Crepancy

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Intersection numbers of `K + Δ` along a curve depend on `K` only up to linear equivalence. -/
private theorem intersectionNumber_add_eq_of_linearlyEquivalent [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
    {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    {K₁ K₂ : Divisor X} (h : K₁.LinearlyEquivalent K₂) (Δ : QDivisor X)
    (h₁ : (Divisor.toQDivisor K₁ + Δ).IsQCartier) (h₂ : (Divisor.toQDivisor K₂ + Δ).IsQCartier) :
    (Divisor.toQDivisor K₁ + Δ).intersectionNumber k sX i hdim h₁ =
      (Divisor.toQDivisor K₂ + Δ).intersectionNumber k sX i hdim h₂ := by
  obtain ⟨D', hD', hD'c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul h₂
  set m := (Divisor.toQDivisor K₂ + Δ).cartierIndex h₂
  have hm := QDivisor.cartierIndex_pos h₂
  obtain ⟨φ, hφ⟩ := h
  set a : Additive (RationalFunctions X)ˣ := (m : ℤ) • Additive.ofMul φ with ha
  set G := D' + principalDivisorHom a with hG_def
  have hGc : G.IsCartier := hD'c.add (Divisor.isCartier_principalDivisor _)
  have hG : Divisor.toQDivisor G = (m : ℤ) • (Divisor.toQDivisor K₁ + Δ) := by
    have e : principalDivisorHom a = (m : ℤ) • (K₁ - K₂) := by
      rw [ha, map_zsmul, principalDivisorHom_apply, toMul_ofMul, hφ]
    rw [hG_def, e, map_add, hD', map_zsmul, map_sub, ← smul_add]
    congr 1
    abel
  have hGD : G.LinearlyEquivalent D' := ⟨a.toMul, by
    rw [hG_def, add_sub_cancel_left, principalDivisorHom_apply]⟩
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ h₁ hm G hGc hG,
    QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ h₂ hm D' hD'c hD']
  congr 2
  haveI := hGc.isInvertibleModule_divisorialSheaf
  haveI := hD'c.isInvertibleModule_divisorialSheaf
  exact degreeOn_eq_of_iso k sX i hdim hGD.divisorialSheafIso

/-- Intersection numbers are unchanged by an isomorphism of curves over `X`. -/
private theorem intersectionNumber_eq_of_iso_comp [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] {C C' : Scheme.{u}} (i : C ⟶ X) (i' : C' ⟶ X)
    [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (e : C ≅ C') (he : e.hom ≫ i' = i) (D : QDivisor X)
    (hD : D.IsQCartier) :
    D.intersectionNumber k sX i hdim hD = D.intersectionNumber k sX i' hdim' hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  unfold QDivisor.intersectionNumber Divisor.degreeOn
  haveI := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i i' hdim hdim' e he]

/-- Two closed subschemes cut out by equal ideal sheaves are isomorphic over `X`. -/
private theorem exists_iso_subscheme_of_eq {I J : X.IdealSheafData} (h : I = J) :
    ∃ e : I.subscheme ≅ J.subscheme, e.hom ≫ J.subschemeι = I.subschemeι := by
  subst h
  exact ⟨Iso.refl _, by simp⟩

end Curves

section Main

variable {k : Type u} [Field k] [PerfectField k] {X U : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]

omit [PerfectField k] in
/-- If a proper curve `C' ⊆ U` maps onto a proper curve `C ⊆ X`, then the intersection number of
a pull-back `p^*D` with `C'` is a positive multiple of `D · C`. -/
private theorem exists_pos_intersectionNumber_pullback_eq_mul {sX : X ⟶ Spec (.of k)}
    {p : U ⟶ X} [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k (p ≫ sX)]
    [IsProper sX] [IsProper p] (C : ProperCurve sX) (C' : ProperCurve (p ≫ sX))
    (hp : p C'.point = C.point) {D : QDivisor X} (hD : D.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉ D.supp}
    {D' : QDivisor U} (hpb : D.IsPullback p hLB D') (hD' : D'.IsQCartier) :
    ∃ d : ℚ, 0 < d ∧ D'.intersectionNumber k (p ≫ sX) C'.ι C'.dim_le hD' =
      d * D.intersectionNumber k sX C.ι C.dim_le hD := by
  haveI := C'.isCurve
  haveI := C.isCurve
  set φ := C'.ι ≫ p with hφ
  have hrange : closure (Set.range φ) = closure ({C.point} : Set X) := by
    rw [hφ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, C'.range_ι,
      closure_image_closure p.continuous, Set.image_singleton, hp]
  have hker : φ.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({C.point} : Set X)) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    ext1
    simpa only [TopologicalSpace.Closeds.coe_closure] using hrange
  obtain ⟨e, he⟩ := exists_iso_subscheme_of_eq hker
  have hnc : ¬ ∃ x : X, Set.range φ = {x} := by
    intro hpt
    have := subsingleton_image sX φ hpt
    have h0 : topologicalKrullDim φ.image ≤ 0 := topologicalKrullDim_zero_of_discreteTopology _
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph,
      C.dim_eq] at h0
    norm_num at h0
  haveI : AlgebraicGeometry.IsCurve k (φ ≫ sX) := by
    rw [hφ, Category.assoc]
    infer_instance
  haveI : IsProper (φ ≫ sX) := by
    rw [hφ, Category.assoc]
    infer_instance
  have hcurve := isCurve_imageι_comp sX φ hnc
  rw [intersectionNumber_pullback_eq_degreeOver_mul k (p ≫ sX) sX p rfl C'.ι hD hpb hcurve]
  refine ⟨(degreeOver φ.toImage : ℚ), ?_, by
    rw [intersectionNumber_eq_of_iso_comp sX φ.imageι C.ι _ C.dim_le e he _ hD]⟩
  haveI : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sX) := hcurve
  haveI : IsProper φ := IsProper.of_comp φ sX
  haveI : IsProper (φ.imageι ≫ sX) := isProper_imageι_comp φ sX
  exact_mod_cast degreeOver_pos_of_not_constant k (φ ≫ sX) (φ.imageι ≫ sX) φ.toImage
    (by simp) (not_exists_toImage_eq φ hnc)

/-- **Crepancy and the projection formula.** For a crepant dlt lift `p : (U, Δ) ⟶ (X, B)`, a
canonical divisor `K_U`, and a curve `C̃ ⊆ U` mapping onto a curve `C ⊆ X`,
there is `d > 0` (the degree of `C̃ → C`) with `(K_U + Δ) · C̃ = d (K + B) · C`. -/
private theorem exists_pos_intersectionNumber_add_eq_mul_of_isCrepantDltLift
    {sX : X ⟶ Spec (.of k)} {K : Divisor X} {B : QDivisor X} {p : U ⟶ X} {Δ : QDivisor U}
    (hlift : IsCrepantDltLift sX K B p Δ) {KU : Divisor U}
    (hKU : ∃ n : ℕ, KU.IsCanonicalDivisor (p ≫ sX) n) (hD : (Divisor.toQDivisor K + B).IsQCartier)
    (C : ProperCurve sX) (C' : ProperCurve (p ≫ sX)) (hp : p C'.point = C.point)
    (hD' : (Divisor.toQDivisor KU + Δ).IsQCartier) :
    ∃ d : ℚ, 0 < d ∧
      (Divisor.toQDivisor KU + Δ).intersectionNumber k (p ≫ sX) C'.ι C'.dim_le hD' =
        d * (Divisor.toQDivisor K + B).intersectionNumber k sX C.ι C.dim_le hD := by
  obtain ⟨n, hcrep⟩ := hlift.isCrepantBoundary
  obtain ⟨n', hK'⟩ := hlift.isCanonicalDivisor
  obtain ⟨n'', hKU'⟩ := hKU
  have hPV := hlift.isProjectiveVariety
  have hXv : IsNormalVariety k sX := ⟨hPV.toIsVariety, ‹IsNormal X›⟩
  have hY : IsNormalVariety k (p ≫ sX) := hlift.isQFactorial.1
  have hb := hlift.isBirationalMorphism
  haveI : IsDominant p := hb.isDominant
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (p ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety k sX := hXv.1
  haveI : AlgebraicGeometry.IsVariety k (p ≫ sX) := hY.1
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hPV.isProjective
  haveI : IsProper p := isProper_of_isProjectiveMorphism _ hlift.isProjectiveMorphism
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXv hK'
  have hLB : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉
      (Divisor.toQDivisor K + B).supp := fun Z => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  have hpb := isPullback_divisorOfForm_add hXv hY hb hK' hcrep hω0 hωK hLB
  obtain rfl : n'' = n' := by
    have h1 := hKU'.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hb,
      hK'.1] at h1
    exact_mod_cast h1.symm
  have hne := pullbackRationalPluriForms_ne_zero hXv hb hK'.1 hω0
  have hlin := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hKU' hne
  rw [one_smul] at hlin
  have hq' := hpb.isQCartier hD
  rw [intersectionNumber_add_eq_of_linearlyEquivalent (p ≫ sX) C'.ι C'.dim_le hlin.symm Δ hD' hq']
  exact exists_pos_intersectionNumber_pullback_eq_mul C C' hp hD hpb hq'

end Main

section Lift

variable {k : Type u} [Field k] {X U : Scheme.{u}}

/-- On a proper curve `C ⊆ X` with generic point `c`, a point `a` with `c ⤳ a ⤳ b` and `a ≠ b`
is `c` itself. -/
private theorem eq_point_of_specializes {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) {a b : X}
    (h1 : C.point ⤳ a) (h2 : a ⤳ b) (hab : a ≠ b) : a = C.point := by
  by_contra hne
  have hmem : ∀ x : X, C.point ⤳ x → x ∈ Set.range C.ι := fun x hx => by
    rw [C.range_ι]
    exact specializes_iff_mem_closure.mp hx
  obtain ⟨x₀, hx₀⟩ := hmem _ specializes_rfl
  obtain ⟨x₁, hx₁⟩ := hmem _ h1
  obtain ⟨x₂, hx₂⟩ := hmem _ (h1.trans h2)
  have hind := C.ι.isClosedEmbedding.isInducing
  have h01 : x₀ ⤳ x₁ := hind.specializes_iff.mp (by rwa [hx₀, hx₁])
  have h12 : x₁ ⤳ x₂ := hind.specializes_iff.mp (by rwa [hx₁, hx₂])
  have n01 : x₀ ≠ x₁ := fun h => hne (by rw [← hx₁, ← h, hx₀])
  have n12 : x₁ ≠ x₂ := fun h => hab (by rw [← hx₁, ← hx₂, h])
  let c : C.scheme → TopologicalSpace.IrreducibleCloseds C.scheme := fun a =>
    ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hlt : ∀ {a b : C.scheme}, a ⤳ b → a ≠ b → c b < c a := by
    intro a b hab hne
    refine lt_of_le_of_ne (specializes_iff_closure_subset.mp hab) fun hEq ↦ hne ?_
    exact (t0Space_iff_inseparable C.scheme).mp inferInstance a b
      (inseparable_iff_closure_eq.mpr
        (congrArg TopologicalSpace.IrreducibleCloseds.carrier hEq).symm)
  let l : LTSeries (TopologicalSpace.IrreducibleCloseds C.scheme) :=
    { length := 2, toFun := ![c x₂, c x₁, c x₀],
      step := fun i => by
        fin_cases i
        · exact hlt h12 n12
        · exact hlt h01 n01 }
  have h2le : ((2 : ℕ) : WithBot ℕ∞) ≤
      Order.krullDim (TopologicalSpace.IrreducibleCloseds C.scheme) :=
    Order.le_krullDim_iff.mpr ⟨l, rfl⟩
  have hd : topologicalKrullDim C.scheme = 1 := C.dim_eq
  rw [topologicalKrullDim] at hd
  rw [hd] at h2le
  exact absurd h2le (by decide)

end Lift

section Picard

variable {k : Type u} [Field k] {X Z : Scheme.{u}}

/-- For an isomorphism `f`, `f^* N¹(Z)_ℝ` is all of `N¹(X)_ℝ`. -/
private theorem pullbackNumericalClasses_eq_top (sX : X ⟶ Spec (.of k)) (f : X ⟶ Z) [IsIso f] :
    pullbackNumericalClasses sX f = ⊤ := by
  refine eq_top_iff.mpr fun d _ => ?_
  obtain ⟨D, rfl⟩ := Submodule.mkQ_surjective _ d
  change numericalDivisorClass sX D ∈ _
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ =>
    rw [map_add]
    exact Submodule.add_mem _ (h₁ Submodule.mem_top) (h₂ Submodule.mem_top)
  | single E c =>
    have e : (Finsupp.single E c : KCartierDivisor ℝ X) = c • KCartierDivisor.ofCartier ℝ E := by
      simp [KCartierDivisor.ofCartier]
    rw [e, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨E, (Scheme.Modules.pullback (inv f)).obj (MMP.CartierDivisor.sheaf E),
      inferInstance, ⟨?_⟩, rfl⟩
    exact ((Scheme.Modules.pullbackId X).app _).symm ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.hom_inv_id f)).symm.app _ ≪≫
      ((Scheme.Modules.pullbackComp f (inv f)).app _).symm

end Picard

section Contracted

variable {k : Type u} [Field k] {X Z : Scheme.{u}}

/-- A morphism of finite type from a locally Noetherian scheme is quasi-finite at `x` when the
fibre through `x` has dimension at most zero. -/
private theorem quasiFiniteAt_of_topologicalKrullDim_preimage_le_zero [IsLocallyNoetherian X]
    {f : X ⟶ Z} [LocallyOfFiniteType f] (x : X)
    (hle : topologicalKrullDim (f ⁻¹' {f x}) ≤ 0) : f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have h' : topologicalKrullDim (f.fiber (f x)) ≤ 0 := by
    rwa [IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo (f x)).isHomeomorph]
  have : IsLocallyNoetherian
      (CategoryTheory.Limits.pullback f (Z.fromSpecResidueField (f x))) := inferInstance
  have : IsLocallyNoetherian (f.fiber (f x)) := this
  have : IsLocallyArtinian (f.fiber (f x)) := IsLocallyArtinian.of_topologicalKrullDim_le_zero h'
  have : DiscreteTopology (f.fiber (f x)) :=
    (IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.mp inferInstance).2
  exact isOpen_discrete _

/-- A proper morphism out of a proper, locally Noetherian `k`-scheme which is not locally
quasi-finite contracts some proper curve. -/
public theorem _root_.MMP.Mori.exists_properCurve_isContractedBy_of_not_locallyQuasiFinite
    {sX : X ⟶ Spec (.of k)} [IsProper sX] [IsLocallyNoetherian X] {f : X ⟶ Z} [IsProper f]
    (h : ¬ LocallyQuasiFinite f) : ∃ C : ProperCurve sX, C.IsContractedBy f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff] at h
  have hne : ((f.quasiFiniteLocus : Set X)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro h'
    exact h (SetLike.coe_injective (h'.trans TopologicalSpace.Opens.coe_top.symm))
  obtain ⟨x, hx, hxc⟩ := f.quasiFiniteLocus.isOpen.isClosed_compl.exists_closed_singleton hne
  have hy : IsClosed ({f x} : Set Z) := by
    simpa [Set.image_singleton] using f.isClosedMap _ hxc
  have hF : IsClosed (f ⁻¹' {f x}) := hy.preimage f.continuous
  have hdim : 0 < topologicalKrullDim (f ⁻¹' {f x}) := by
    by_contra! hle
    exact hx (quasiFiniteAt_of_topologicalKrullDim_preimage_le_zero x hle)
  rw [topologicalKrullDim, Order.krullDim_pos_iff] at hdim
  obtain ⟨A, B, hAB⟩ := hdim
  have hBirr : IsIrreducible (Subtype.val '' (B : Set (f ⁻¹' {f x}))) :=
    B.isIrreducible.image _ continuous_subtype_val.continuousOn
  set η := hBirr.genericPoint
  have hη : closure ({η} : Set X) = closure (Subtype.val '' (B : Set (f ⁻¹' {f x}))) :=
    hBirr.isGenericPoint_genericPoint_closure
  have hBF : closure (Subtype.val '' (B : Set (f ⁻¹' {f x}))) ⊆ f ⁻¹' {f x} :=
    closure_minimal (by rintro _ ⟨z, -, rfl⟩; exact z.2) hF
  have hAcl : IsClosed (Subtype.val '' (A : Set (f ⁻¹' {f x}))) :=
    hF.isClosedEmbedding_subtypeVal.isClosedMap _ A.isClosed
  have hAne : (Subtype.val '' (A : Set (f ⁻¹' {f x}))).Nonempty :=
    A.isIrreducible.nonempty.image _
  obtain ⟨x₀, hx₀A, hx₀⟩ := hAcl.exists_closed_singleton hAne
  have hx₀B : x₀ ∈ closure (Subtype.val '' (B : Set (f ⁻¹' {f x}))) :=
    subset_closure (Set.image_mono hAB.le hx₀A)
  have hηx₀ : η ⤳ x₀ := specializes_iff_mem_closure.mpr (hη ▸ hx₀B)
  have hηne : η ∉ ({x₀} : Set X) := by
    intro hη₀
    rw [Set.mem_singleton_iff] at hη₀
    apply hAB.not_ge
    intro z hz
    have hz' : z.1 ∈ closure ({η} : Set X) := hη ▸ subset_closure ⟨z, hz, rfl⟩
    rw [hη₀, hx₀.closure_eq, Set.mem_singleton_iff] at hz'
    obtain ⟨a, ha, ha'⟩ := hx₀A
    have : z = a := Subtype.ext (hz'.trans ha'.symm)
    exact this ▸ ha
  obtain ⟨y', hηy', -, -, hcurve⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sX hηx₀ hx₀
    hx₀ (Set.mem_singleton _) hηne
  have hsub : closure ({y'} : Set X) ⊆ f ⁻¹' {f x} := by
    refine (closure_minimal (Set.singleton_subset_iff.mpr ?_) isClosed_closure).trans hBF
    exact hη ▸ specializes_iff_mem_closure.mp hηy'
  refine ⟨⟨y', hcurve⟩, fun z hz => ?_⟩
  have h1 : f z = f x := hsub hz
  have h2 : f y' = f x := hsub (subset_closure rfl)
  rw [h1, h2]

end Contracted

section Helpers

variable {k : Type u} [Field k] {X Z U : Scheme.{u}}

/-- A curve whose generic point maps to the generic point of a curve contracted by `f` is
contracted by `p ≫ f`. -/
private theorem isContractedBy_comp_of_map_point {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z}
    {p : U ⟶ X} (C : ProperCurve sX) (hC : C.IsContractedBy f) (C' : ProperCurve (p ≫ sX))
    (hp : p C'.point = C.point) : C'.IsContractedBy (p ≫ f) := by
  intro x hx
  have hx' : p x ∈ closure ({C.point} : Set X) := by
    rw [← hp, ← Set.image_singleton]
    exact image_closure_subset_closure_image p.continuous ⟨x, hx, rfl⟩
  simp only [Scheme.Hom.comp_apply]
  rw [hC _ hx', hp]

end Helpers

section Obligations

variable {k : Type u} [Field k] {X Z X' U : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)}
    {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- `(K_X + B) · C < 0` for every proper curve `C` contracted by the contraction `f` of a
permitted step. -/
private theorem intersectionNumber_neg_of_isContractedBy
    (hstep : IsPermittedStep sX sZ sX' K B R f fp) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) (hD : (Divisor.toQDivisor K + B).IsQCartier) :
    (Divisor.toQDivisor K + B).intersectionNumber k sX C.ι C.dim_le hD < 0 := by
  obtain ⟨m, hm, L, hL, hLeq, hamp⟩ := hstep.hasRelativelyAmpleMultiple
  have hpos : 0 < L.degreeOn k sX C.ι C.dim_le hL := by
    haveI := hL.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hamp C hC
  have e : Divisor.toQDivisor L = (-(m : ℚ)) • (Divisor.toQDivisor K + B) := by
    rw [hLeq, smul_neg, neg_smul, ← Int.cast_smul_eq_zsmul ℚ]
    rfl
  have hq : ((-(m : ℚ)) • (Divisor.toQDivisor K + B)).IsQCartier :=
    e ▸ QDivisor.isQCartier_toQDivisor hL
  have h1 := QDivisor.intersectionNumber_toQDivisor k sX C.ι C.dim_le L hL
    (QDivisor.isQCartier_toQDivisor hL)
  rw [MMP.Fourfold.intersectionNumber_congr sX C.ι C.dim_le _ hq e,
    MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le _ hD _ hq] at h1
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hpos' : (0 : ℚ) < (L.degreeOn k sX C.ι C.dim_le hL : ℚ) := by exact_mod_cast hpos
  nlinarith

/-- The contraction `f` of a permitted step contracts some proper curve. -/
private theorem exists_properCurve_isContractedBy
    (hstep : IsPermittedStep sX sZ sX' K B R f fp) :
    ∃ C : ProperCurve sX, C.IsContractedBy f := by
  by_contra hno
  have hc := hstep.isContractionOfRay.toIsContraction
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hstep.isProjectiveVariety.isProjective
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  haveI : LocallyQuasiFinite f :=
    of_not_not fun h => hno (exists_properCurve_isContractedBy_of_not_locallyQuasiFinite h)
  haveI : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  have hZ := hc.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : IsIso f := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hstep.isBirationalMorphism)).2
      inferInstance
  have h1 := hstep.relativePicardNumber_eq_one
  rw [relativePicardNumberN1, pullbackNumericalClasses_eq_top] at h1
  simp at h1

/-- For a crepant dlt lift `p : U ⟶ X`, every proper curve `C ⊆ X` is the image of a proper
curve `C̃ ⊆ U`, in the sense that the generic point of `C̃` maps to that of `C`. -/
private theorem exists_properCurve_map_point {p : U ⟶ X} {Δ : QDivisor U}
    (hlift : IsCrepantDltLift sX K B p Δ) (C : ProperCurve sX) :
    ∃ C' : ProperCurve (p ≫ sX), p C'.point = C.point := by
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hlift.isProjectiveVariety.isProjective
  haveI : IsProper p := isProper_of_isProjectiveMorphism _ hlift.isProjectiveMorphism
  haveI : IsDominant p := hlift.isBirationalMorphism.isDominant
  set c := C.point
  obtain ⟨y, hy⟩ := p.surjective c
  obtain ⟨q, hqc, hq⟩ :=
    (isClosed_closure : IsClosed (closure ({c} : Set X))).exists_closed_singleton
    ⟨c, subset_closure rfl⟩
  have hqne : q ≠ c := by
    intro hqc'
    have hr : Set.range C.ι = {q} := by
      rw [C.range_ι]
      change closure {c} = {q}
      rw [← hqc', hq.closure_eq]
    have : Subsingleton C.scheme := ⟨fun a b => C.ι.isClosedEmbedding.injective (by
      have ha : C.ι a ∈ Set.range C.ι := ⟨a, rfl⟩
      have hb : C.ι b ∈ Set.range C.ι := ⟨b, rfl⟩
      rw [hr] at ha hb
      exact ha.trans hb.symm)⟩
    have h0 : topologicalKrullDim C.scheme ≤ 0 := topologicalKrullDim_zero_of_discreteTopology _
    rw [C.dim_eq] at h0
    norm_num at h0
  have hcl : IsClosed (p '' closure ({y} : Set U)) := p.isClosedMap _ isClosed_closure
  have hqimg : q ∈ p '' closure ({y} : Set U) :=
    closure_minimal (by rintro _ rfl; exact ⟨y, subset_closure rfl, hy⟩) hcl hqc
  obtain ⟨w, hw, hwq⟩ := hqimg
  obtain ⟨q', hq'w, hq'⟩ :=
    (isClosed_closure : IsClosed (closure ({w} : Set U))).exists_closed_singleton
      ⟨w, subset_closure rfl⟩
  have hpq' : p q' = q := by
    have h := image_closure_subset_closure_image p.continuous ⟨q', hq'w, rfl⟩
    rwa [Set.image_singleton, hwq, hq.closure_eq] at h
  have hyq' : y ⤳ q' := specializes_iff_mem_closure.mpr
    (closure_minimal (Set.singleton_subset_iff.mpr hw) isClosed_closure hq'w)
  have hZ : IsClosed (p ⁻¹' {q}) := hq.preimage p.continuous
  obtain ⟨y', hyy', hy'q', hy'Z, hcurve⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes
    (p ≫ sX) hyq' hq' hZ (by simp [hpq']) (by simp [hy, hqne.symm])
  refine ⟨⟨y', hcurve⟩, ?_⟩
  have h1 : c ⤳ p y' := hy ▸ hyy'.map p.continuous
  have h2 : p y' ⤳ q := hpq' ▸ hy'q'.map p.continuous
  have h3 : p y' ≠ q := fun h => hy'Z (by simp [h])
  exact eq_point_of_specializes C h1 h2 h3

end Obligations

/-- For a permitted step `(X, B) → Z ← (X⁺, B⁺)` with contraction `f : X ⟶ Z` and a crepant
dlt lift `p : (U, Δ) ⟶ (X, B)`, the divisor `K_U + Δ` is not nef over `Z` for `p ≫ f`, for any
canonical divisor `K_U` of `U`. -/
@[mmp "lem_oai4_c3_dlt_bridge_nonempty"]
public theorem IsPermittedStep.not_isRelativelyNef_of_isCrepantDltLift
    {k : Type u} [Field k] [PerfectField k] {X Z X' U : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)}
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hstep : IsPermittedStep sX sZ sX' K B R f fp)
    {p : U ⟶ X} {Δ : QDivisor U} (hlift : IsCrepantDltLift sX K B p Δ)
    {KU : Divisor U} (hKU : ∃ n : ℕ, KU.IsCanonicalDivisor (p ≫ sX) n) :
    ¬ (Divisor.toQDivisor KU + Δ).IsRelativelyNef (p ≫ sX) (p ≫ f) := by
  intro hnef
  obtain ⟨hD, -⟩ := hstep.isNegativeExtremalRayOf
  obtain ⟨C, hC⟩ := exists_properCurve_isContractedBy hstep
  obtain ⟨C', hp⟩ := exists_properCurve_map_point hlift C
  have hD' := hnef.1
  obtain ⟨d, hd, heq⟩ :=
    exists_pos_intersectionNumber_add_eq_mul_of_isCrepantDltLift hlift hKU hD C C' hp hD'
  have h0 := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg _ hnef hD' C'
    (isContractedBy_comp_of_map_point C hC C' hp)
  have hneg := intersectionNumber_neg_of_isContractedBy hstep C hC hD
  rw [heq] at h0
  nlinarith

end MMP.Fourfold
