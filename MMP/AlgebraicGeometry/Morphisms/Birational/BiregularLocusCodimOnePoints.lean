module

public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison

/-!
# Codimension-one points of the biregular locus, and discrepancies as coefficients

Two results on birational morphisms of varieties over a field `k`.

Let `f : Y ⟶ X` be a proper birational morphism with `X` normal, and let `V_f` be the union of
the opens of `X` over which `f` is an isomorphism. Every point `x ∈ X` of codimension at most
one, i.e. with `dim 𝒪_{X,x} ≤ 1`, lies in `V_f`; in particular every prime divisor of `X` meets
`V_f`. The local ring at such a point is a field or a discrete valuation ring, so by the
valuative criterion there is `y ∈ Y` over `x` with `𝒪_{X,x} ≅ 𝒪_{Y,y}`. Then `f` is an open
immersion near `y`, and its inverse on the image `W` is a section of the separated morphism
`f⁻¹(W) ⟶ W`, hence an open and closed immersion into the irreducible `f⁻¹(W)`, hence an
isomorphism.

Let `ω ≠ 0` be a rational top form on a normal variety `X` with `K_X = div_X(ω)` canonical, `Δ`
a `ℚ`-divisor with `K_X + Δ` `ℚ`-Cartier, and `f : Y ⟶ X` a birational morphism from a normal
variety, with `K_Y = div_Y(f^*ω)`. Then for every prime divisor `E` of `Y` the discrepancy
`a(E, X, Δ)` is the coefficient of `E` in `K_Y - f^*(K_X + Δ)`. Choosing `m > 0` and a local
equation `φ` of `m(K_X + Δ)` near `f(η_E)`, and writing `ω = c · b` for a basis `b` of
`Ω^n_{k(X)/k}`, the form `τ = c^m φ⁻¹ · b^{⊗m}` generates `𝒪_X(m(K_X + Δ))` near `f(η_E)`, and
`ord_E(f^*τ) = m · ord_E(f^*ω) - v_E(f^*φ)`.

## Main results

* `MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one`: a point of codimension at most
  one lies in the biregular locus `MMP.Mori.biregularLocus f`.
* `MMP.Mori.isDiscrepancy_coeff_divisorOfForm_sub_pullback`: the coefficient of `E` in
  `div_Y(f^*ω) - f^*(div_X(ω) + Δ)` is the discrepancy `a(E, X, Δ)`.

## Implementation notes

The codimension of a point `x` is the Krull dimension of its local ring `𝒪_{X,x}`.

"`(X, Δ)` is a pair" is spelled out for the chosen canonical divisor `K_X = div_X(ω)`:
`X` is a normal variety, `div_X(ω)` is a canonical divisor of dimension `n`
(`MMP.Mori.Divisor.IsCanonicalDivisor`), and `div_X(ω) + Δ` is `ℚ`-Cartier. The last condition
is what makes the pull-back `MMP.Mori.QDivisor.pullback` defined. The discrepancy is the relation
`MMP.Mori.IsDiscrepancy`, and the statement says that the coefficient *is* the discrepancy of the
divisor `(Y, f, E)` over `X`.

The source works in characteristic `0`; here the base field `k` is only assumed perfect. Some such
hypothesis is needed: over an imperfect field a normal variety can have nowhere-cyclic Kähler
differentials (e.g. the affine line over `k(t^{1/p})`, viewed over `k = 𝔽_p(t)`), every order of a
form vanishes, and no discrepancy exists for a boundary with a non-zero coefficient.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.25,
  2.62–2.63
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

/-! ### The biregular locus contains every point of codimension at most one -/

/-- A morphism that is both an open and a closed immersion, from a nonempty scheme to an
irreducible one, is an isomorphism: its range is a nonempty clopen subset. -/
private theorem isIso_of_isOpenImmersion_of_isClosedImmersion {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] [IsClosedImmersion f] [Nonempty X] [IrreducibleSpace Y] : IsIso f :=
  haveI := IrreducibleSpace.connectedSpace Y
  (isIso_iff_isOpenImmersion_and_surjective f).mpr ⟨inferInstance, ⟨Set.range_eq_univ.mp <|
    (isClopen_iff.mp ⟨f.isClosedEmbedding.isClosed_range, f.isOpenEmbedding.isOpen_range⟩
      ).resolve_left (Set.range_nonempty f).ne_empty⟩⟩

/-- If `f` is separated and an open immersion on a nonempty open `U` of an irreducible scheme
`Y`, then `f` is an isomorphism over the image `W` of `U`: the inverse of `f` on `W` is a
section of `f⁻¹(W) ⟶ W`, hence a closed immersion, and also an open immersion, into the
irreducible `f⁻¹(W)`. -/
private theorem isBiregular_opensRange {X Y : Scheme} [IrreducibleSpace Y] (f : Y ⟶ X)
    [IsSeparated f] (U : Y.Opens) [Nonempty U] [IsOpenImmersion (U.ι ≫ f)] :
    IsBiregular f (U.ι ≫ f).opensRange := by
  set W := (U.ι ≫ f).opensRange
  let τ0 : (W : Scheme) ⟶ Y := (U.ι ≫ f).isoOpensRange.inv ≫ U.ι
  have hτ0 : τ0 ≫ f = W.ι := by
    simp only [τ0, Category.assoc, ← (U.ι ≫ f).isoOpensRange_hom_ι, Iso.inv_hom_id_assoc]
    rfl
  let τ : (W : Scheme) ⟶ f ⁻¹ᵁ W := IsOpenImmersion.lift (f ⁻¹ᵁ W).ι τ0 <| by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (τ0 w) ∈ W
    rw [← Scheme.Hom.comp_apply, hτ0]
    exact w.2
  have hτ : τ ≫ (f ⁻¹ᵁ W).ι = τ0 := IsOpenImmersion.lift_fac _ _ _
  have hsec : τ ≫ (f ∣_ W) = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hτ, hτ0,
      Category.id_comp]
  haveI : IsOpenImmersion τ := by
    haveI : IsOpenImmersion (τ ≫ (f ⁻¹ᵁ W).ι) := by
      rw [hτ]
      dsimp [τ0]
      infer_instance
    exact IsOpenImmersion.of_comp τ (f ⁻¹ᵁ W).ι
  haveI : IsClosedImmersion τ := by
    haveI : IsClosedImmersion (τ ≫ (f ∣_ W)) := by
      rw [hsec]
      infer_instance
    exact IsClosedImmersion.of_comp τ (f ∣_ W)
  haveI : Nonempty W := ⟨(U.ι ≫ f).isoOpensRange.hom (Classical.arbitrary U)⟩
  obtain ⟨y⟩ : Nonempty (f ⁻¹ᵁ W) := ⟨τ (Classical.arbitrary W)⟩
  haveI : IrreducibleSpace (f ⁻¹ᵁ W) := Subtype.irreducibleSpace ⟨⟨y.1, y.2⟩,
    (IrreducibleSpace.isIrreducible_univ Y).2.open_subset (f ⁻¹ᵁ W).2 (Set.subset_univ _)⟩
  haveI := isIso_of_isOpenImmersion_of_isClosedImmersion τ
  change IsIso (f ∣_ W)
  rw [show f ∣_ W = inv τ by rw [← cancel_epi τ, hsec, IsIso.hom_inv_id]]
  infer_instance

/-- Let `f : Y ⟶ X` be a proper birational morphism of `k`-varieties with `X` normal. Every
point of `X` of codimension at most one lies in the biregular locus `biregularLocus f`, the
union of the opens over which `f` is an isomorphism. -/
@[mmp "lem_km2c_biregular_locus_codim_two"]
public theorem mem_biregularLocus_of_ringKrullDim_stalk_le_one {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {x : X}
    (hx : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    x ∈ biregularLocus f := by
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : IsNormal X := hX.2
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY
  haveI : IsDominant f := hf.isDominant
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hco : Order.coheight x ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight] at hx
    exact_mod_cast hx
  haveI : ValuationRing (X.presheaf.stalk x) := by
    rcases lt_or_eq_of_le hco with h0 | h1
    · have hmax : IsMax x := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h0)
      obtain rfl : x = genericPoint X :=
        (Specializes.antisymm (hmax (genericPoint_specializes x))
          (genericPoint_specializes x)).eq
      change ValuationRing X.functionField
      infer_instance
    · haveI := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk h1
      infer_instance
  obtain ⟨y, hyx, hiso⟩ := MMP.Intersection.exists_isIso_stalkMap_of_valuationRing f
    hf.functionFieldMap_bijective x
  obtain ⟨U, hyU, hU⟩ := exists_isOpenImmersion_res_of_isIso_stalkMap f y
    (by rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _) hiso
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  exact le_biregularLocus (isBiregular_opensRange f U) ⟨⟨y, hyU⟩, hyx⟩

/-! ### The discrepancy as a coefficient of `K_Y - f^*(K_X + Δ)` -/

section Discrepancy

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} [IsDominant f]

/-- The coefficient of a pull-back is the order of the pulled-back local equation: if `φ` is a
local equation of the Cartier divisor `C` near `f(η_E)`, then `coeff_E(f^*C) = v_E(f^*φ)`. -/
private theorem coeff_isPullback_eq_ord_evalFF {C : MMP.Mori.Divisor X}
    {hC : ∀ Z : irreducibleComponents Y, f (MMP.Mori.componentGenericPoint Y Z) ∉ C.supp}
    {C' : MMP.Mori.Divisor Y} (h : C.IsPullback f hC C') {U : X.Opens}
    {φ : (MMP.Mori.RationalFunctions X)ˣ} (hφ : C.IsLocalEquation U φ) (E : MMP.Mori.PrimeDivisor Y)
    (hU : f E.genericPoint ∈ U) (Z : irreducibleComponents X) :
    C'.coeff E = Y.ord (functionFieldMap f
      (MMP.Threefold.Mori.Helpers.evalFF Z (φ : MMP.Mori.RationalFunctions X))) E.genericPoint := by
  classical
  have hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp hU
  rw [h U φ hφ E hE]
  have hZp := E.map_componentGenericPoint_mem f hE
  have hW := MMP.Mori.mem_pointComponent (f (MMP.Mori.componentGenericPoint Y E.component))
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZp (hC _) hW
  rw [MMP.Mori.pullbackComponent_eq hC hφ hZp hW a ha]
  set u := Units.map (f.stalkMap (MMP.Mori.componentGenericPoint Y E.component)).hom.toMonoidHom a
  let ψ : (MMP.Mori.RationalFunctions Y)ˣ :=
    (MMP.Mori.RationalFunctions.unitsEquiv Y).symm (Function.update 1 E.component u)
  have hψZ : (ψ : MMP.Mori.RationalFunctions Y) E.component = u := by
    simp [ψ, MMP.Mori.RationalFunctions.unitsEquiv]
  have h1 : E.ordUnit u = E.ord ψ := by
    rw [MMP.Mori.PrimeDivisor.ord_eq_ordUnit]
    congr 1
    exact (Units.ext hψZ).symm
  rw [h1, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  congr 1
  obtain rfl : Z = MMP.Mori.pointComponent (f (MMP.Mori.componentGenericPoint Y E.component)) :=
    Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
  change (Y.presheaf.stalkSpecializes _).hom ((ψ : MMP.Mori.RationalFunctions Y) E.component) =
    functionFieldMap f ((X.presheaf.stalkSpecializes _).hom
      ((φ : MMP.Mori.RationalFunctions X) _))
  rw [hψZ, ← ha]
  change _ = functionFieldMap f ((MMP.Mori.stalkToRationalFunctions X hW ≫
    X.presheaf.stalkSpecializes _).hom a)
  rw [MMP.Mori.stalkToRationalFunctions, TopCat.Presheaf.stalkSpecializes_comp]
  exact (MMP.Mori.functionFieldMap_algebraMap_stalk f
    (MMP.Mori.componentGenericPoint Y E.component) a.val).symm

/-- `v(c^m g⁻¹) = m v(c) - v(g)`. -/
private theorem ord_zpow_mul_inv {c g : Y.functionField} (hc : c ≠ 0) (hg : g ≠ 0) (m : ℤ)
    (x : Y) : Y.ord (c ^ m * g⁻¹) x = m * Y.ord c x - Y.ord g x := by
  rw [← zpow_neg_one, Scheme.ord_mul (zpow_ne_zero _ hc) (zpow_ne_zero _ hg),
    MMP.Mori.ord_zpow _ hc, MMP.Mori.ord_zpow _ hg]
  ring

end

/-- **The local generator of `𝒪_X(m(K_X + Δ))`.** Let `K_X = div_X(ω)` with `ω = c · b` for a
basis `b` of `Ω^n_{k(X)/k}`, and let `φ` be a local equation on `U` of a Cartier divisor `C` with
`C = m(K_X + Δ)`. Then the form `τ = c^m φ⁻¹ · b^{⊗m}` generates `𝒪_X(m(K_X + Δ))` on `U`. -/
private theorem generatesOn_zpow_mul_inv_basis {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]))
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0) {Δ : QDivisor X} {m : ℕ} {C : Divisor X}
    (hC : Divisor.toQDivisor C = (m : ℤ) • (Divisor.toQDivisor (divisorOfForm ω) + Δ))
    {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : C.IsLocalEquation U φ)
    (Z : irreducibleComponents X) {τ : RationalPluriForms sX n m}
    (hτ : letI := functionFieldAlgebra sX
      (ZTensorPower.basis b m).repr τ () = (ZTensorPower.basis b 1).repr ω () ^ (m : ℤ) *
        (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X))⁻¹) :
    GeneratesOn Δ m U τ := by
  letI := functionFieldAlgebra sX
  have hc : (ZTensorPower.basis b 1).repr ω () ≠ 0 := repr_ne_zero_of_ne_zero b hω
  have hg : MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X) ≠ 0 :=
    (φ.isUnit.map _).ne_zero
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    refine mul_ne_zero (zpow_ne_zero (m : ℤ) hc) (inv_ne_zero hg) ?_
    rw [← hτ]
    exact DFunLike.congr_fun (map_zero (ZTensorPower.basis b (m : ℤ)).repr) ()
  refine ⟨hτ0, fun Γ hΓ => ?_⟩
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have hK : (divisorOfForm ω).coeff Γ = X.ord ((ZTensorPower.basis b 1).repr ω ()) Γ.genericPoint
      + N := by
    rw [coeff_divisorOfForm, hN 1 ω hω, one_mul]
  have hCΓ : (C.coeff Γ : ℚ) = m * ((divisorOfForm ω).coeff Γ + Δ.coeff Γ) := by
    simpa [zsmul_eq_mul, mul_add] using congrArg (fun D : QDivisor X => D.coeff Γ) hC
  have hgΓ : X.ord (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X))
      Γ.genericPoint = C.coeff Γ := by
    rw [hφ Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
      Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents)
        Γ.component Z]
  rw [hN _ _ hτ0, hτ, ord_zpow_mul_inv hc hg]
  push_cast [hK, ← hgΓ] at hCΓ ⊢
  linear_combination -hCΓ

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- **The discrepancy as a coefficient** (Kollár–Mori 2.25 in terms of a top form). Let `X` be a
normal variety, `ω ≠ 0` a rational `n`-form on `X` with `K_X = div_X(ω)` a canonical divisor of
dimension `n`, `Δ` a `ℚ`-divisor with `K_X + Δ` `ℚ`-Cartier, and `f : Y ⟶ X` a birational
morphism from a normal variety `Y`; put `K_Y = div_Y(f^*ω)`. Then for every prime divisor `E` of
`Y`, the coefficient of `E` in `K_Y - f^*(K_X + Δ)` is the discrepancy `a(E, X, Δ)`. -/
@[mmp "lem_km5d_discrepancy_as_coefficient"]
public theorem isDiscrepancy_coeff_divisorOfForm_sub_pullback (hX : IsNormalVariety k sX)
    {n : ℕ} (ω : RationalPluriForms sX n 1) (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n) (Δ : QDivisor X)
    (hQ : (Divisor.toQDivisor (divisorOfForm ω) + Δ).IsQCartier)
    {Y : Scheme.{u}} (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [LocallyOfFiniteType (f ≫ sX)] (E : PrimeDivisor Y) :
    haveI : IsDominant f := hf.isDominant
    IsDiscrepancy sX n (divisorOfForm ω) Δ ⟨Y, f, hY, hf, E⟩
      ((Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) -
          QDivisor.pullback (f := f) (Divisor.toQDivisor (divisorOfForm ω) + Δ) hQ
            (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier f hQ)).coeff E) := by
  haveI : IsDominant f := hf.isDominant
  let := functionFieldAlgebra sX
  have hn := hK.topologicalKrullDim_eq
  obtain ⟨m, hm0, C, hC, hCart⟩ := hQ.exists_pos
  obtain ⟨Dp, hDp, hCp⟩ := QDivisor.isPullback_pullback (f := f) hQ
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier f hQ) m hm0 C hC hCart
  obtain ⟨b, N, hb⟩ := (⟨Y, f, hY, hf, E⟩ : DivisorOver k sX).exists_ordPullback_eq hX hn
  obtain ⟨U, hxU, φ, hφ⟩ := hCart (f E.genericPoint)
  let Z : irreducibleComponents X := ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; simp⟩
  let τ : RationalPluriForms sX n m := ((ZTensorPower.basis b 1).repr ω () ^ (m : ℤ) *
    (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X))⁻¹) •
      ZTensorPower.basis b (m : ℤ) ()
  have hτ : (ZTensorPower.basis b m).repr τ () = (ZTensorPower.basis b 1).repr ω () ^ (m : ℤ) *
      (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X))⁻¹ := by
    simp [τ]
  have hgen := generatesOn_zpow_mul_inv_basis
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn) b hω hC hφ Z hτ
  refine ⟨hX, hK, m, hm0, ⟨C, hC, hCart⟩, U, hxU, τ, hgen, ?_⟩
  have hc : functionFieldMap f ((ZTensorPower.basis b 1).repr ω ()) ≠ 0 :=
    (map_ne_zero _).mpr (repr_ne_zero_of_ne_zero b hω)
  have hg : functionFieldMap f (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X))
      ≠ 0 := (map_ne_zero _).mpr (φ.isUnit.map _).ne_zero
  rw [hb _ _ hgen.1, hτ, map_mul (functionFieldMap f), map_zpow₀ (functionFieldMap f),
    map_inv₀ (functionFieldMap f), ord_zpow_mul_inv hc hg]
  have hDpE := congrArg (fun D : QDivisor Y => D.coeff E) hDp
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    coeff_isPullback_eq_ord_evalFF hCp hφ E hxU Z] at hDpE
  simp only [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor, coeff_divisorOfForm]
  rw [show E.ordForm (pullbackRationalPluriForms sX f ω) =
    DivisorOver.ordPullback (⟨Y, f, hY, hf, E⟩ : DivisorOver k sX) ω from rfl, hb 1 ω hω]
  push_cast at hDpE ⊢
  linear_combination hDpE

end Discrepancy

end MMP.Mori
