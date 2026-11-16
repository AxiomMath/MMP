module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentExistence
public import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueSmoothDivisor
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary

/-!
# Lifting a floor stratum along a crepant birational morphism of snc pairs

Let `h : (Y, C) ⟶ (X, B)` be a projective birational morphism of smooth projective varieties
carrying snc subboundaries (`ℚ`-divisors with simple normal crossing support and all
coefficients at most one), with `K_Y + C = h^*(K_X + B)`, that is, `C` is the crepant boundary of
`(X, B)` on `Y`. A *floor stratum* of `(X, B)` is an
snc stratum of the reduced coefficient-one part `B^{=1}`: an irreducible component of an
intersection of components of `B^{=1}` (the empty intersection giving `X` itself). Every floor
stratum `Z ⊆ X` is the final stratum of a flag of iterated adjunction of `(X, B)`, and for every
such flag, with adjunction pair `(S, B_S)`, there are a flag of iterated adjunction of `(Y, C)`
whose final stratum `S' ⊆ Y` is a floor stratum of `(Y, C)`, with adjunction pair
`(S', C_{S'})`, and a birational morphism `g : S' ⟶ S` lying under `h`, which is crepant:
`K_{S'} + C_{S'} = g^*(K_S + B_S)`.

## Main results

* `MMP.Fourfold.IsSNCSubboundaryPair.exists_stratumAdjunctionData_isBirationalMorphism`: the
  birational crepant lift of a floor stratum.

## Implementation notes

* The adjunction pair of a stratum is that of a flag of iterated adjunction
  (`MMP.Fourfold.StratumAdjunctionData`); for an snc subboundary it depends only on the stratum,
  and the lift is asserted for every flag reaching `Z`.
* The equality `K_Y + C = h^*(K_X + B)` on `Y` is stated coefficientwise, as
  `MMP.Mori.IsCrepantBoundary`: `-coeff_F C = a(F, X, B)` for every prime divisor `F` of `Y`.
  An equality of divisors `K_Y + C = h^*(K_X + B)` for independently chosen canonical divisors
  would determine `C` only up to a principal divisor, since a canonical divisor is determined
  only up to linear equivalence; the source's convention is `h_* K_Y = K_X`, which the
  discrepancy formulation builds in.
* Crepancy of `g` is `K_{S'} + C_{S'} = g^*(K_S + B_S)` via `MMP.Mori.QDivisor.IsPullback` for
  canonical divisors of the strata of the same dimension; there the boundaries are already pinned
  by the flags, and the canonical divisors are asserted to exist.
* The base field is an algebraically closed field of characteristic zero, the setting of the
  source (which works over `ℂ`): over an imperfect field the strata of an snc divisor are regular
  but need not be smooth, and the residues identifying the boundaries of the strata are undefined
  on strata with inseparable function field.
-/

@[expose] public section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.CrepantSncStratumBirationalLift

open MMP.Mori MMP.Flips MMP.Fourfold

/-! ### Existence of adjunction steps on locally factorial varieties -/

section AdjunctionStepExistence

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- The section `φ|_U` of `K(X)` over `U` of a rational function. -/
private def secOf (U : X.Opens) (φ : RationalFunctions X) :
    ToType ((rationalFunctionsPresheaf X).obj (op U)) := fun Z => φ Z.1

private theorem secOf_mem_sheaf {D : Divisor X} {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) :
    secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) ∈
      (Divisor.toWeilDivisor D).sheaf.sections U := by
  rw [sheaf_toWeilDivisor_sections]
  intro E hE
  refine Or.inr ?_
  change WithZero.exp _ ≤ E.valuation (((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)
    E.component)
  rw [PrimeDivisor.valuation_component, PrimeDivisor.ord_inv, hφ E hE]

/-- On a Cartier divisor with local equation `φ` on `U`, the stalk of `𝒪_X(D)` at `x ∈ U` is
`φ⁻¹ 𝒪_{X,x}`. -/
private theorem stalkSet_sheaf_of_isLocalEquation {D : Divisor X} {U : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ) {x : X} (hx : x ∈ U) :
    (Divisor.toWeilDivisor D).sheaf.stalkSet x = Set.range fun a : X.presheaf.stalk x =>
      (rationalFunctionsPresheaf X).germ U x hx
          (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)) *
        (structureStalkToRationalFunctionsStalk X x).hom a := by
  have hsub := MMP.Flips.subsingleton_irreducibleComponents (X := X)
  obtain ⟨Z⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  ext g
  constructor
  · rintro ⟨W, hxW, s, hs, rfl⟩
    have hZW : componentGenericPoint X Z ∈ W := componentGenericPoint_mem_of_nonempty Z ⟨x, hxW⟩
    by_cases h0 : s ⟨Z, hZW⟩ = 0
    · refine ⟨0, ?_⟩
      apply rationalFunctionsStalkEval_injective x Z
      simp only [map_mul, map_zero, mul_zero]
      rw [rationalFunctionsStalkEval_germ]
      exact h0.symm
    obtain ⟨χ, hχ⟩ := exists_units_eq_of_ne_zero ⟨x, hxW⟩ s fun Z' => by
      obtain ⟨Z', h'⟩ := Z'
      obtain rfl : Z' = Z := Subsingleton.elim _ _
      exact h0
    have hxZ : x ∈ Z.1 := by rw [irreducibleComponents_val_eq_univ Z]; trivial
    obtain ⟨r, hr⟩ := exists_stalk_eq_of_forall_zero_le_ord hxZ (χ * φ) fun E hxE => by
      rw [PrimeDivisor.ord_mul, ← hφ E ⟨x, hxE, hx⟩]
      have hsE := (sheaf_toWeilDivisor_sections D W ▸ hs) E ⟨x, hxE, hxW⟩
      obtain rfl : E.component = Z := Subsingleton.elim _ _
      rcases hsE with h | h
      · exact absurd h h0
      · rw [← hχ, PrimeDivisor.valuation_component, WithZero.exp_le_exp] at h
        omega
    refine ⟨r, ?_⟩
    apply rationalFunctionsStalkEval_injective x Z
    rw [map_mul, rationalFunctionsStalkEval_germ, rationalFunctionsStalkEval_structure,
      rationalFunctionsStalkEval_germ]
    change ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z *
      (stalkToRationalFunctions X hxZ).hom r = _
    have key : ((φ⁻¹ * (χ * φ) : (RationalFunctions X)ˣ) : RationalFunctions X) = χ := by
      rw [mul_comm χ φ, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hr, ← hχ Z hZW, ← key]
    rfl
  · rintro ⟨a, rfl⟩
    obtain ⟨W, hxW, a', rfl⟩ := X.presheaf.exists_germ_eq a
    have hx' : x ∈ U ⊓ W := ⟨hx, hxW⟩
    refine ⟨U ⊓ W, hx', X.presheaf.map (homOfLE inf_le_right).op a' •
      (rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op
        (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)),
      Submodule.smul_mem _ _ ((Divisor.toWeilDivisor D).sheaf.map_mem _ (secOf_mem_sheaf hφ)), ?_⟩
    rw [germ_smul_rationalFunctions, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply, mul_comm]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
/-- `i^w_C 𝓕` is saturated: its stalk conditions are imposed at the points of codimension at most
one only. -/
private theorem isSaturated_weilRestrictionCartier {T : Scheme.{u}} (j : T ⟶ X)
    (F : RationalFunctionsSubmodule X) : (weilRestrictionCartier j F).IsSaturated := by
  refine RationalFunctionsSubmodule.ext fun V =>
    le_antisymm ((weilRestrictionCartier j F).sections_le_saturation V) fun s hs => ?_
  intro P hP hc
  obtain ⟨W, hPW, t, ht, hts⟩ := hs P hP hc
  rw [← hts]
  exact ht P hPW hc

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
private theorem secOf_mul (U : X.Opens) (φ ψ : RationalFunctions X) :
    secOf U (φ * ψ) = secOf U φ * secOf U ψ := rfl

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
private theorem secOf_one (U : X.Opens) : secOf U (1 : RationalFunctions X) = 1 := rfl

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
private theorem map_secOf {U V : X.Opens} (i : V ⟶ U) (φ : RationalFunctions X) :
    (rationalFunctionsPresheaf X).map i.op (secOf U φ) = secOf V φ := rfl

/-- The germ at `x ∈ U` of a unit `φ` of `K(X)`, as a unit of `K(X)_x`. -/
private noncomputable def germUnit {U : X.Opens} {x : X} (hx : x ∈ U) (φ : (RationalFunctions X)ˣ) :
    ((rationalFunctionsPresheaf X).stalk x)ˣ where
  val := (rationalFunctionsPresheaf X).germ U x hx (secOf U (φ : RationalFunctions X))
  inv := (rationalFunctionsPresheaf X).germ U x hx (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) :
    RationalFunctions X))
  val_inv := by
    rw [← map_mul, ← secOf_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, secOf_one,
      map_one]
  inv_val := by
    rw [← map_mul, ← secOf_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, secOf_one,
      map_one]

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
private theorem val_germUnit {U : X.Opens} {x : X} (hx : x ∈ U) (φ : (RationalFunctions X)ˣ) :
    (germUnit hx φ : (rationalFunctionsPresheaf X).stalk x) =
      (rationalFunctionsPresheaf X).germ U x hx (secOf U (φ : RationalFunctions X)) := rfl

attribute [local simp] val_germUnit

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
private theorem germUnit_mul {U V : X.Opens} {x : X} (hU : x ∈ U) (hV : x ∈ V)
    (φ ψ : (RationalFunctions X)ˣ) :
    germUnit hU φ * germUnit hV ψ = germUnit (show x ∈ U ⊓ V from ⟨hU, hV⟩) (φ * ψ) := by
  ext
  simp only [Units.val_mul, val_germUnit]
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_left : U ⊓ V ⟶ U) x ⟨hU, hV⟩,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_right : U ⊓ V ⟶ V) x ⟨hU, hV⟩,
    ← map_mul, map_secOf, map_secOf, ← secOf_mul]

section SheafAlgebra

variable {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {d : ℕ}
  (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)

include sX hd

/-- **`𝒪_X(D₁) · 𝒪_X(D₂) = 𝒪_X(D₁ + D₂)`** for Cartier divisors. -/
private theorem sheaf_mul_sheaf {D₁ D₂ : Divisor X} (h₁ : D₁.IsCartier) (h₂ : D₂.IsCartier) :
    (Divisor.toWeilDivisor D₁).sheaf.mul (Divisor.toWeilDivisor D₂).sheaf =
      (Divisor.toWeilDivisor (D₁ + D₂)).sheaf := by
  haveI : IsNoetherian X := {}
  obtain ⟨L₁, hL₁⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf sX hd
    (Divisor.toWeilDivisor D₁)
  obtain ⟨L₂, hL₂⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf sX hd
    (Divisor.toWeilDivisor D₂)
  rw [← hL₁, ← hL₂]
  refine RationalFunctionsSubmodule.eq_of_stalkSet_eq
    (RationalFunctionsSubmodule.isSaturated_saturation _) (WeilDivisor.isSaturated_sheaf _)
    fun η hη => ?_
  obtain ⟨U₁, hU₁, φ₁, hφ₁⟩ := h₁ η
  obtain ⟨U₂, hU₂, φ₂, hφ₂⟩ := h₂ η
  have e₁ : L₁.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      ((germUnit hU₁ φ₁⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) :
        (rationalFunctionsPresheaf X).stalk η) *
        (structureStalkToRationalFunctionsStalk X η).hom a := by
    change L₁.toRationalFunctionsSubmodule.stalkSet η = _
    rw [hL₁]
    exact stalkSet_sheaf_of_isLocalEquation hφ₁ hU₁
  have e₂ : L₂.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      ((germUnit hU₂ φ₂⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) :
        (rationalFunctionsPresheaf X).stalk η) *
        (structureStalkToRationalFunctionsStalk X η).hom a := by
    change L₂.toRationalFunctionsSubmodule.stalkSet η = _
    rw [hL₂]
    exact stalkSet_sheaf_of_isLocalEquation hφ₂ hU₂
  rw [(L₁.stalkSet_mul_inv_unit L₂ η hη _ _ e₁ e₂).1, germUnit_mul,
    stalkSet_sheaf_of_isLocalEquation ((hφ₁.mono inf_le_left).add (hφ₂.mono inf_le_right))
      (show η ∈ U₁ ⊓ U₂ from ⟨hU₁, hU₂⟩), mul_inv]
  rfl

/-- `𝒪_X(D)^[n] = 𝒪_X(nD)` for `n ≥ 1`. -/
private theorem sheaf_reflexivePowNat (D : Divisor X) {n : ℕ} (hn : 1 ≤ n) :
    (Divisor.toWeilDivisor D).sheaf.reflexivePowNat n =
      (Divisor.toWeilDivisor ((n : ℤ) • D)).sheaf := by
  haveI : IsNoetherian X := {}
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Divisor.reflexivePowNat_sheaf_toWeilDivisor sX hd D m, natCast_zsmul]

end SheafAlgebra

section Restriction

variable {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]

open Classical in
/-- The pull-back `j^*φ ∈ K(T)^×` of a local equation `φ` of `D` on `U`, for `T` integral meeting
`j⁻¹ U`. -/
private noncomputable def pullbackLocalUnit (j : T ⟶ X) {D : Divisor X}
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp)
    {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ) :
    (RationalFunctions T)ˣ :=
  (RationalFunctions.unitsEquiv T).symm fun Z =>
    if hZ : j (componentGenericPoint T Z) ∈ U then pullbackComponent j hB hφ Z hZ else 1

open Classical in
private theorem isLocalEquation_pullbackLocalUnit (j : T ⟶ X) {D : Divisor X} (hDc : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp)
    {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ) :
    (D.pullback hDc hB).IsLocalEquation (j ⁻¹ᵁ U) (pullbackLocalUnit j hB hφ) := by
  intro E hE
  rw [Divisor.isPullback_pullback hDc hB U φ hφ E hE, PrimeDivisor.ord_eq_ordUnit]
  congr 1
  ext
  change _ = (if hZ : j (componentGenericPoint T E.component) ∈ U then
    pullbackComponent j hB hφ E.component hZ else 1).val
  rw [dif_pos (E.map_componentGenericPoint_mem j hE)]

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
/-- If `φ_ξ` is the image of a unit `a` of `𝒪_{X,ξ}`, then the germ of `φ⁻¹|_U` at `ξ` is the
image of `a⁻¹`. -/
private theorem structure_inv_eq_germ_secOf_inv {U : X.Opens} {φ : (RationalFunctions X)ˣ} {ξ : X}
    (hξU : ξ ∈ U) {ZX : irreducibleComponents X} (hξ : ξ ∈ ZX.1) (a : (X.presheaf.stalk ξ)ˣ)
    (ha : (stalkToRationalFunctions X hξ).hom a = (φ : RationalFunctions X) ZX) :
    (structureStalkToRationalFunctionsStalk X ξ).hom ((a⁻¹ : (X.presheaf.stalk ξ)ˣ) :
        X.presheaf.stalk ξ) =
      (rationalFunctionsPresheaf X).germ U ξ hξU
        (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)) := by
  apply rationalFunctionsStalkEval_injective _ ZX
  rw [rationalFunctionsStalkEval_structure, rationalFunctionsStalkEval_germ]
  change (stalkToRationalFunctions X hξ).hom _ = ((φ⁻¹ : (RationalFunctions X)ˣ) :
    RationalFunctions X) ZX
  have h1 : (stalkToRationalFunctions X hξ).hom ((a⁻¹ : (X.presheaf.stalk ξ)ˣ) :
      X.presheaf.stalk ξ) * (stalkToRationalFunctions X hξ).hom (a : X.presheaf.stalk ξ) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : ((φ : (RationalFunctions X)ˣ) : RationalFunctions X) ZX *
      ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) ZX = 1 := by
    rw [← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Pi.one_apply]
  rw [ha] at h1
  exact left_inv_eq_right_inv h1 h2

/-- `φ⁻¹|_U` is regular along `j` when `j` maps the generic point of `T` into `U` off `Supp D`. -/
private theorem isRegularAlong_secOf_inv (j : T ⟶ X) {D : Divisor X}
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp)
    {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ) :
    IsRegularAlong j (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)) := by
  obtain ⟨ZX⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  intro Z hZU
  have hξ : j (componentGenericPoint T Z) ∈ ZX.1 := by
    rw [irreducibleComponents_val_eq_univ ZX]; trivial
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZU (hB Z) hξ
  exact ⟨_, structure_inv_eq_germ_secOf_inv hZU hξ a ha⟩

open Classical in
/-- The restriction of `φ⁻¹|_U` along `j` is `(j^*φ)⁻¹|_{j⁻¹U}`. -/
private theorem restrictAlong_secOf_inv (j : T ⟶ X) {D : Divisor X}
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp)
    {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ)
    (hf : IsRegularAlong j (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X))) :
    restrictAlong j (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)) hf =
      secOf (j ⁻¹ᵁ U) (((pullbackLocalUnit j hB hφ)⁻¹ : (RationalFunctions T)ˣ) :
        RationalFunctions T) := by
  obtain ⟨ZX⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  funext Z
  have hZU : j (componentGenericPoint T Z.1) ∈ U := Z.2
  have hξ : j (componentGenericPoint T Z.1) ∈ ZX.1 := by
    rw [irreducibleComponents_val_eq_univ ZX]; trivial
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZU (hB Z.1) hξ
  rw [restrictAlong_apply_of_germ_eq j hf Z _ (structure_inv_eq_germ_secOf_inv hZU hξ a ha)]
  change _ = (((RationalFunctions.unitsEquiv T).symm fun Z =>
    if hZ : j (componentGenericPoint T Z) ∈ U then pullbackComponent j hB hφ Z hZ else 1)⁻¹ :
      (RationalFunctions T)ˣ).val Z.1
  rw [← map_inv]
  change _ = ((fun Z => if hZ : j (componentGenericPoint T Z) ∈ U then
    pullbackComponent j hB hφ Z hZ else 1)⁻¹ Z.1).val
  rw [Pi.inv_apply, dif_pos hZU, pullbackComponent_eq hB hφ hZU hξ a ha, ← map_inv]
  rfl

/-- **The restriction `i^w_C 𝒪_X(D)` of a Cartier divisor is `𝒪_T(j^*D)`.** -/
private theorem weilRestrictionCartier_sheaf_toWeilDivisor (j : T ⟶ X) {D : Divisor X}
    (hDc : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp) :
    weilRestrictionCartier j (Divisor.toWeilDivisor D).sheaf =
      (Divisor.toWeilDivisor (D.pullback hDc hB)).sheaf := by
  refine RationalFunctionsSubmodule.eq_of_stalkSet_eq (isSaturated_weilRestrictionCartier j _)
    (WeilDivisor.isSaturated_sheaf _) fun P hc => ?_
  obtain ⟨U, hU, φ, hφ⟩ := hDc (j P)
  have hf := isRegularAlong_secOf_inv j hB hφ
  let f₀ : ((rationalFunctionsPresheaf X).stalk (j P))ˣ :=
    ⟨(rationalFunctionsPresheaf X).germ U (j P) hU
        (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)),
      (rationalFunctionsPresheaf X).germ U (j P) hU
        (secOf U ((φ : (RationalFunctions X)ˣ) : RationalFunctions X)),
      by rw [← map_mul]; convert map_one ((rationalFunctionsPresheaf X).germ U (j P) hU).hom
         using 2; funext Z; exact congrFun (congrArg Units.val (inv_mul_cancel φ)) Z.1,
      by rw [← map_mul]; convert map_one ((rationalFunctionsPresheaf X).germ U (j P) hU).hom
         using 2; funext Z; exact congrFun (congrArg Units.val (mul_inv_cancel φ)) Z.1⟩
  have hP : j P ∈ U := hU
  rw [stalkSet_weilRestrictionCartier j (secOf_mem_sheaf hφ) hf hP hc f₀ rfl
      (stalkSet_sheaf_of_isLocalEquation hφ hU),
    stalkSet_sheaf_of_isLocalEquation (isLocalEquation_pullbackLocalUnit j hDc hB hφ)
      (show P ∈ j ⁻¹ᵁ U from hU), restrictAlong_secOf_inv j hB hφ hf]

/-- The stalk of the image `ε(i^*𝒪_X(D))` at a point `P` of `T`, for a Cartier divisor `D` with
local equation `φ` near `j(P)`: the restrictions are spanned by `(φ⁻¹|_U)|_T`. -/
private theorem stalkSet_restrictionImage_sheaf (j : T ⟶ X) {D : Divisor X}
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp)
    {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ) {P : T}
    (hP : P ∈ j ⁻¹ᵁ U) :
    (restrictionImage j (Divisor.toWeilDivisor D).sheaf).stalkSet P =
      Set.range fun a : T.presheaf.stalk P =>
        (rationalFunctionsPresheaf T).germ (j ⁻¹ᵁ U) P hP
            (restrictAlong j (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X))
              (isRegularAlong_secOf_inv j hB hφ)) *
          (structureStalkToRationalFunctionsStalk T P).hom a := by
  have hf := isRegularAlong_secOf_inv j hB hφ
  refine subset_antisymm (stalkSet_restrictionImage_subset j ⟨0, by simp⟩ ?_ ?_ ?_) ?_
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp only [map_add, mul_add]⟩
  · rintro c _ ⟨a, rfl⟩
    exact ⟨c * a, by simp only [map_mul]; ring⟩
  · intro W hPW l hlL hl
    have hmem : (rationalFunctionsPresheaf X).germ W _ hPW l ∈
        (Divisor.toWeilDivisor D).sheaf.stalkSet (j P) := ⟨W, hPW, l, hlL, rfl⟩
    rw [stalkSet_sheaf_of_isLocalEquation hφ hP] at hmem
    obtain ⟨b, hb⟩ := hmem
    exact ⟨(j.stalkMap P).hom b, (germ_restrictAlong_eq_mul j hl hf hPW hP b hb.symm).symm⟩
  · rintro _ ⟨a, rfl⟩
    exact germ_restrictAlong_mul_mem_stalkSet_restrictionImage j (secOf_mem_sheaf hφ) hf hP a

/-- **The embedded dualizing sheaf of `𝒪_X(D)` along `T` is `𝒪_T(j^*D)`**, for `D` Cartier with
`T ⊄ Supp D`. -/
private theorem embeddedDualizingSheaf_eq_sheaf_pullback (j : T ⟶ X) {D : Divisor X}
    (hDc : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp)
    {L : WeilDivisorialSubsheaf X} (hL : L.toRationalFunctionsSubmodule =
      (Divisor.toWeilDivisor D).sheaf) :
    embeddedDualizingSheaf j L = (Divisor.toWeilDivisor (D.pullback hDc hB)).sheaf := by
  refine RationalFunctionsSubmodule.eq_of_stalkSet_eq
    (RationalFunctionsSubmodule.isSaturated_saturation _)
    (WeilDivisor.isSaturated_sheaf _) fun P hc => ?_
  obtain ⟨U, hU, φ, hφ⟩ := hDc (j P)
  have h1 : (embeddedDualizingSheaf j L).stalkSet P =
      (restrictionImage j L.toRationalFunctionsSubmodule).stalkSet P :=
    congrArg SetLike.coe (RationalFunctionsSubmodule.stalk_saturation
      (restrictionImage j L.toRationalFunctionsSubmodule) hc)
  rw [h1]
  change (restrictionImage j L.toRationalFunctionsSubmodule).stalkSet P = _
  rw [hL, stalkSet_restrictionImage_sheaf j hB hφ (show P ∈ j ⁻¹ᵁ U from hU),
    stalkSet_sheaf_of_isLocalEquation (isLocalEquation_pullbackLocalUnit j hDc hB hφ)
      (show P ∈ j ⁻¹ᵁ U from hU), restrictAlong_secOf_inv j hB hφ]

/-- The pull-back of a Cartier divisor is Cartier. -/
private theorem isCartier_pullback (j : T ⟶ X) {D : Divisor X} (hDc : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp) :
    (D.pullback hDc hB).IsCartier := fun x => by
  obtain ⟨U, hU, φ, hφ⟩ := hDc (j x)
  exact ⟨j ⁻¹ᵁ U, hU, _, isLocalEquation_pullbackLocalUnit j hDc hB hφ⟩

end Restriction

section Dualizing

/-- **A dualizing sheaf `𝒪_X(K) ⊆ K(X)` with a prescribed coefficient.** On a proper normal
scheme over `k` of pure dimension `d`, Gorenstein in codimension at most one, the dualizing sheaf
embeds into `K(X)` as `𝒪_X(K)` for a divisor `K`, and `K` can be chosen with any coefficient `c`
along a given prime divisor `P`: moving `K` by a principal divisor gives an isomorphic sheaf. -/
private theorem exists_isDualizingSheaf_sheaf {k : Type u} [Field k] (sV : X ⟶ Spec (.of k))
    [IsProper sV] [LocallyOfFiniteType sV] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (hgor : ∀ η : X, Order.coheight η ≤ 1 → ∃ _ : IsNoetherianRing (X.presheaf.stalk η),
      Dualizing.IsGorensteinLocalRing (X.presheaf.stalk η))
    (P : MMP.Mori.PrimeDivisor X) (c : ℤ) :
    ∃ (ω : WeilDivisorialSubsheaf X) (K : Divisor X), IsDualizingSheaf sV d ω.toModules ∧
      ω.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor K).sheaf ∧ K.coeff P = c := by
  haveI : IsNoetherian X := {}
  let ω₀ := (Scheme.Modules.restrictFunctor (𝟙 X)).obj
    (Stacks.Duality.dualizingModuleOverField sV d)
  have h0 : IsDualizingSheaf sV d ω₀ :=
    ⟨hd, X, 𝟙 X, inferInstance, sV, inferInstance, Category.id_comp _, ⟨Iso.refl _⟩⟩
  obtain ⟨-, φ, hφ⟩ := h0.isCoherent_exists_injective
  obtain ⟨L0, hL0⟩ := (h0.exists_weilDivisorialSubsheaf_iff φ hφ).mpr hgor
  have h1 : IsDualizingSheaf sV d L0.toModules :=
    h0.of_iso (isoImageSubmodule φ hφ ≪≫ eqToIso (by rw [hL0]))
  obtain ⟨K0, hK0⟩ := WeilDivisorialSubsheaf.exists_eq_sheaf_toWeilDivisor sV hd L0
  obtain ⟨t, ht⟩ := MMP.Positivity.PrimeDivisor.exists_ord_eq_one P
  set K := K0 - principalDivisor (t ^ (K0.coeff P - c)) with hK
  obtain ⟨L, hL⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf sV hd (Divisor.toWeilDivisor K)
  have hlin : K0.LinearlyEquivalent K := ⟨t ^ (K0.coeff P - c), by rw [hK, sub_sub_cancel]⟩
  refine ⟨L, K, h1.of_iso (eqToIso (by rw [hK0, toModules_sheaf_toWeilDivisor]) ≪≫
    hlin.divisorialSheafIso ≪≫ eqToIso (by rw [hL, toModules_sheaf_toWeilDivisor])), hL, ?_⟩
  rw [hK, DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, PrimeDivisor.ord_zpow, ht,
    smul_eq_mul, mul_one]
  ring

end Dualizing

section Steps

variable {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]

/-- A Cartier divisor `D` has `𝒪_X(D)` invertible at every point. -/
private theorem isInvertibleAt_sheaf {D : Divisor X} (hDc : D.IsCartier) (x : X) :
    (Divisor.toWeilDivisor D).sheaf.IsInvertibleAt x := by
  obtain ⟨U, hU, φ, hφ⟩ := hDc x
  exact ⟨germUnit hU φ⁻¹, stalkSet_sheaf_of_isLocalEquation hφ hU⟩

omit [CompactSpace X] in
/-- The generic point of `T` maps outside `Supp D` when `D` has coefficient zero along the prime
divisor `P` it maps to. -/
private theorem notMem_supp_of_coeff_eq_zero {R : Type*} [Zero R] {D : DivisorWithCoeffs R X}
    {P : MMP.Mori.PrimeDivisor X}
    (hP : D.coeff P = 0) : P.genericPoint ∉ D.supp := by
  intro h
  obtain ⟨E, hE, hPE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  obtain rfl := eq_of_genericPoint_mem_primeDivisor_support hPE
  exact hE hP

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
/-- A closed immersion onto a prime divisor `P` maps a generic point to the generic point
of `P`. -/
private theorem map_eq_genericPoint_of_range_eq {T : Scheme.{u}} (j : T ⟶ X) [IsClosedImmersion j]
    (P : MMP.Mori.PrimeDivisor X) (hj : Set.range j.base = (P.support : Set X)) {x : T}
    (hx : IsGenericPoint x (Set.univ : Set T)) : j x = P.genericPoint := by
  have h := hx.image j.base.hom.continuous
  rw [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq, hj] at h
  exact h.eq (by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isGenericPoint_closure)

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
/-- Removing a component `P` of coefficient one leaves coefficient zero along `P`, in both the
positive and the negative part. -/
private theorem coeff_parts_sub_single_eq_zero {D : QDivisor X} {P : MMP.Mori.PrimeDivisor X}
    (hP : D.coeff P = 1) : (D - Finsupp.single P 1).coeff P = 0 ∧
      ((D - Finsupp.single P 1)⁺).coeff P = 0 ∧ ((D - Finsupp.single P 1)⁻).coeff P = 0 := by
  have h : (D - Finsupp.single P 1).coeff P = 0 := by
    rw [DivisorWithCoeffs.coeff_sub, hP, DivisorWithCoeffs.coeff_single_self, sub_self]
  refine ⟨h, ?_, ?_⟩ <;> generalize D - Finsupp.single P 1 = Δ at h ⊢ <;> change Δ P = 0 at h
  · change (Δ P)⁺ = 0; rw [h, posPart_zero]
  · change (Δ P)⁻ = 0; rw [h, negPart_zero]

/-- **`𝒪_X(D)` has good support along `T`** for `D` Cartier with `T ⊄ Supp D`. -/
private theorem mem_goodSupportSubsheaves_of_sheaf {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] {d : ℕ} (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (j : T ⟶ X) [IsClosedImmersion j] {D : Divisor X} (hDc : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp)
    (hcod : ∀ Z : irreducibleComponents T, Order.coheight (j (componentGenericPoint T Z)) ≤ 1)
    {L : WeilDivisorialSubsheaf X} (hL : L.toRationalFunctionsSubmodule =
      (Divisor.toWeilDivisor D).sheaf) :
    L ∈ goodSupportSubsheaves (closedRange j) := by
  obtain ⟨ZT⟩ : Nonempty (irreducibleComponents T) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  obtain ⟨ZX⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  refine ⟨fun P _ => ⟨1, le_rfl, ?_⟩, fun ξ hξ hsupp => hsupp ?_⟩
  · rw [RationalFunctionsSubmodule.reflexivePow_natCast, hL, sheaf_reflexivePowNat sX hd D le_rfl,
      Nat.cast_one, one_smul]
    exact isInvertibleAt_sheaf hDc P.1
  · -- `ξ` is the image of the generic point of `T`
    have hgen : IsGenericPoint (j (componentGenericPoint T ZT)) (closedRange j : Set X) := by
      have h := (isGenericPoint_componentGenericPoint T ZT).image j.base.hom.continuous
      rw [irreducibleComponents_val_eq_univ ZT, Set.image_univ,
        j.isClosedEmbedding.isClosed_range.closure_eq] at h
      exact h
    have hcl : IsGenericPoint ξ (closedRange j : Set X) :=
      hξ.eq_of_subset ⟨le_rfl, hgen.isIrreducible⟩ hξ.prop.1
    have hξj : ξ = j (componentGenericPoint T ZT) := hcl.eq hgen
    subst hξj
    obtain ⟨U, hU, φ, hφ⟩ := hDc (j (componentGenericPoint T ZT))
    have hξ' : j (componentGenericPoint T ZT) ∈ ZX.1 := by
      rw [irreducibleComponents_val_eq_univ ZX]; trivial
    obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hU (hB ZT) hξ'
    change L.toRationalFunctionsSubmodule.stalkSet _ = _
    rw [hL, stalkSet_sheaf_of_isLocalEquation hφ hU,
      ← structure_inv_eq_germ_secOf_inv hU hξ' a ha, RationalFunctionsSubmodule.stalkSet_saturation
        (hcod ZT), RationalFunctionsSubmodule.stalkSet_unit]
    ext g
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨((a⁻¹ : (X.presheaf.stalk _)ˣ) : X.presheaf.stalk _) * b, ?_⟩
      simp only [map_mul]
    · rintro ⟨b, rfl⟩
      refine ⟨(a : X.presheaf.stalk _) * b, ?_⟩
      simp only
      rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]

/-- **Sums of classes of `𝒪(D)`.** If `n₃ (n₂ D₁ + n₁ D₂) = n₁ n₂ D₃` for Cartier divisors, then
`(1/n₁)𝒪(D₁) + (1/n₂)𝒪(D₂) = (1/n₃)𝒪(D₃)` in `WSh(X)_ℚ`. -/
private theorem isSum_divNat_of_sheaf {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] {d : ℕ} (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    {L₁ L₂ L₃ : WeilDivisorialSubsheaf X} {D₁ D₂ D₃ : Divisor X} (h₁ : D₁.IsCartier)
    (h₂ : D₂.IsCartier)
    (hL₁ : L₁.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor D₁).sheaf)
    (hL₂ : L₂.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor D₂).sheaf)
    (hL₃ : L₃.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor D₃).sheaf) {n₁ n₂ n₃ : ℕ+}
    (h : ((n₃ : ℕ) : ℤ) • (((n₂ : ℕ) : ℤ) • D₁ + ((n₁ : ℕ) : ℤ) • D₂) =
      (((n₁ : ℕ) * (n₂ : ℕ) : ℕ) : ℤ) • D₃) :
    QWeilDivisorialSheaf.IsSum (L₁.divNat n₁) (L₂.divNat n₂) (L₃.divNat n₃) := by
  refine ⟨L₁, L₂, L₃, n₁, n₂, n₃, rfl, rfl, rfl, 1, le_rfl, ?_⟩
  simp only [one_mul, RationalFunctionsSubmodule.reflexivePow_natCast]
  rw [hL₁, hL₂, hL₃, sheaf_reflexivePowNat sX hd D₁ n₂.pos, sheaf_reflexivePowNat sX hd D₂ n₁.pos,
    sheaf_mul_sheaf sX hd (h₁.zsmul _) (h₂.zsmul _), sheaf_reflexivePowNat sX hd _ n₃.pos,
    sheaf_reflexivePowNat sX hd D₃ (Nat.mul_pos n₁.pos n₂.pos), h]

/-- **The different on a locally factorial variety.** Let `V` be a proper normal variety over
`k`, Gorenstein in codimension at most one, on which every divisor is Cartier, `B_V` a `ℚ`-divisor
with coefficients at most one, and `j : T ⟶ V` a closed immersion of a normal variety onto a
prime divisor `P` with coefficient one in `B_V`. Then the different `Diff_T((B_V - P)⁺)` of FA 16.6
is defined and equals the pull-back `j^*(B_V - P)⁺`: the dualizing sheaf `𝒪_V(K)` (with
`coeff_P K = -1`) twisted by `P` is invertible along `T`. -/
private theorem exists_isDifferentDivisor_pullback {k : Type u} [Field k] (sV : X ⟶ Spec (.of k))
    (hV : IsNormalVariety k sV) [IsProper sV] [LocallyOfFiniteType sV] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) {dT : ℕ}
    (hdT : ∀ Z ∈ irreducibleComponents T, topologicalKrullDim Z = dT)
    (hcart : ∀ D : Divisor X, D.IsCartier)
    (hgor : ∀ η : X, Order.coheight η ≤ 1 → ∃ _ : IsNoetherianRing (X.presheaf.stalk η),
      Dualizing.IsGorensteinLocalRing (X.presheaf.stalk η))
    {BV : QDivisor X} (hle : ∀ Q, BV.coeff Q ≤ 1) (P : MMP.Mori.PrimeDivisor X)
    (hP : BV.coeff P = 1) (j : T ⟶ X) [IsClosedImmersion j]
    (hj : Set.range j.base = (P.support : Set X)) (hT : IsNormalVariety k (j ≫ sV)) :
    ∃ (hBp : ∀ Z : irreducibleComponents T,
        j (componentGenericPoint T Z) ∉ ((BV - Finsupp.single P 1)⁺).supp)
      (hBn : ∀ Z : irreducibleComponents T,
        j (componentGenericPoint T Z) ∉ ((BV - Finsupp.single P 1)⁻).supp)
      (hqp : ((BV - Finsupp.single P 1)⁺).IsQCartier)
      (hqn : ((BV - Finsupp.single P 1)⁻).IsQCartier) (d' : ℕ)
      (ω ωXS : MMP.Flips.WeilDivisorialSubsheaf X) (DS : MMP.Flips.WeilDivisor X),
      MMP.Flips.IsDifferentDivisor j sV d' ω ωXS DS
        (QDivisor.toQWeilDivisor (BV - Finsupp.single P 1)⁺)
        (QDivisor.toQWeilDivisor (((BV - Finsupp.single P 1)⁺).pullback hqp hBp)) := by
  classical
  haveI : IsNoetherian X := {}
  haveI : IsNoetherian T := {}
  haveI : LocallyOfFiniteType (j ≫ sV) := hT.1.toLocallyOfFiniteType
  have hqall : ∀ D : QDivisor X, D.IsQCartier := fun D => by
    obtain ⟨N, hN, G, hG⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor D
    exact ⟨N, by exact_mod_cast hN.ne', G, hG, hcart G⟩
  obtain ⟨-, hΔpP, hΔnP⟩ := coeff_parts_sub_single_eq_zero hP
  set Δ := BV - Finsupp.single P (1 : ℚ) with hΔ
  have hΔle : ∀ Q, Δ.coeff Q ≤ 1 := fun Q => by
    rw [hΔ, DivisorWithCoeffs.coeff_sub]
    have : 0 ≤ DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℚ) : QDivisor X) Q := by
      change 0 ≤ (Finsupp.single P (1 : ℚ)) Q
      rw [Finsupp.single_apply]; split_ifs <;> norm_num
    linarith [hle Q]
  -- the generic point of `T` is that of `P`
  have hjη : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) = P.genericPoint :=
    fun Z => map_eq_genericPoint_of_range_eq j P hj
      (irreducibleComponents_val_eq_univ Z ▸ isGenericPoint_componentGenericPoint T Z)
  have hcod : ∀ Z : irreducibleComponents T, Order.coheight (j (componentGenericPoint T Z)) = 1 :=
    fun Z => by rw [hjη]; exact P.coheight_genericPoint
  have hBΔ : ∀ (D : DivisorWithCoeffs ℚ X), D.coeff P = 0 →
      ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp :=
    fun D hD Z => by rw [hjη]; exact notMem_supp_of_coeff_eq_zero hD
  have hBp := hBΔ _ hΔpP
  have hBn := hBΔ _ hΔnP
  refine ⟨hBp, hBn, hqall _, hqall _, ?_⟩
  -- the dualizing sheaf `ω = 𝒪_X(K)` with `coeff_P K = -1`, and `ω(P) = 𝒪_X(K + P)`
  obtain ⟨ω, K, hω, hωK, hKP⟩ := exists_isDualizingSheaf_sheaf sV hd hgor P (-1)
  set KP : Divisor X := K + Finsupp.single P 1 with hKPdef
  have hKPP : KP.coeff P = 0 := by
    rw [hKPdef, DivisorWithCoeffs.coeff_add, hKP, DivisorWithCoeffs.coeff_single_self]; norm_num
  have hBKP : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ KP.supp :=
    fun Z => by rw [hjη]; exact notMem_supp_of_coeff_eq_zero hKPP
  obtain ⟨ωXS, hωXS⟩ :=
    WeilDivisor.exists_weilDivisorialSubsheaf_sheaf sV hd (Divisor.toWeilDivisor KP)
  set DS : MMP.Flips.WeilDivisor X := Divisor.toWeilDivisor (Finsupp.single P 1) with hDS
  -- the class of `Δ⁺`
  obtain ⟨m, hm, E, hE, hEc⟩ := (hqall (Δ⁺)).exists_pos
  have hEP : E.coeff P = 0 := by
    have := congrArg (fun D : QDivisor X => D.coeff P) hE
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, hΔpP, smul_zero] at this
    exact_mod_cast this
  have hBE : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ E.supp :=
    fun Z => by rw [hjη]; exact notMem_supp_of_coeff_eq_zero hEP
  obtain ⟨LE, hLE⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf sV hd
    (Divisor.toWeilDivisor E)
  set mp : ℕ+ := ⟨m, hm⟩
  set ET : Divisor T := E.pullback hEc hBE with hET
  obtain ⟨N, hN⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf (j ≫ sV) hdT
    (Divisor.toWeilDivisor ET)
  set KT : Divisor T := KP.pullback (hcart KP) hBKP with hKT
  obtain ⟨Ω, hΩ⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf (j ≫ sV) hdT
    (Divisor.toWeilDivisor KT)
  obtain ⟨O₀, hO₀⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf (j ≫ sV) hdT
    (Divisor.toWeilDivisor (0 : Divisor T))
  set BT' := (Δ⁺).pullback (hqall _) hBp with hBT'
  -- `m B_T' = j^*E`
  have hBT'E : Divisor.toQDivisor ET = (m : ℤ) • BT' := by
    obtain ⟨D', hD', hpD'⟩ := QDivisor.isPullback_pullback (hqall (Δ⁺)) hBp m hm E hE hEc
    rw [← hD', hET]
    congr 1
    exact (Divisor.isPullback_pullback hEc hBE).eq hEc hpD'
  have hgoodω : ωXS ∈ goodSupportSubsheaves (closedRange j) :=
    mem_goodSupportSubsheaves_of_sheaf sV hd j (hcart KP) hBKP (fun Z => (hcod Z).le) hωXS
  have hgoodE : LE ∈ goodSupportSubsheaves (closedRange j) :=
    mem_goodSupportSubsheaves_of_sheaf sV hd j hEc hBE (fun Z => (hcod Z).le) hLE
  have hpow1 : ∀ {L : WeilDivisorialSubsheaf X} {D : Divisor X},
      L.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor D).sheaf →
      L.toRationalFunctionsSubmodule.reflexivePow (((1 : ℕ+) : ℕ) : ℤ) =
        (Divisor.toWeilDivisor D).sheaf := fun {L D} hL => by
    rw [PNat.one_coe, RationalFunctionsSubmodule.reflexivePow_natCast, hL,
      sheaf_reflexivePowNat sV hd D le_rfl, Nat.cast_one, one_smul]
  have hinv : ∀ {L : WeilDivisorialSubsheaf X} {D : Divisor X},
      L.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor D).sheaf →
      ∀ P' : T, Order.coheight P' ≤ 1 →
        (L.toRationalFunctionsSubmodule.reflexivePow (((1 : ℕ+) : ℕ) : ℤ)).IsInvertibleAt
          (j.base P') := fun {L D} hL P' _ => by
    rw [hpow1 hL]; exact isInvertibleAt_sheaf (hcart D) _
  have hdiff : MMP.Flips.IsDifferentDivisor j sV d ω ωXS DS (QDivisor.toQWeilDivisor (Δ⁺))
      (QDivisor.toQWeilDivisor BT') := by
    refine ⟨⟨hV, inferInstance, hcod, fun Z => ⟨⟨P, inferInstance,
        P.isDiscreteValuationRing_localRing⟩, (hjη Z).symm⟩, fun Γ => ?_, fun Γ => ?_,
        fun Γ => ?_, fun Γ hΓ hmem => ?_, hω, ?_, hgoodω⟩, LE.divNat mp,
        ⟨mp, Divisor.toWeilDivisor E, LE, fun Γ => ?_, hLE, rfl⟩, mp, Divisor.toWeilDivisor ET, N,
        fun Γ => ?_, hN, ⟨LE, mp, hgoodE, rfl⟩, O₀.divNat 1, N.divNat mp,
        ⟨Ω, Ω.divNat 1, ?_, ⟨hgoodω, 1, hinv hωXS, Ω, ?_, rfl⟩, ?_⟩,
        ⟨LE, mp, hgoodE, rfl, N, 1, ⟨hgoodE, 1, hinv hLE, N, ?_, rfl⟩, by rw [mul_one]⟩, ?_⟩
    · -- `DS` is the reduced divisor `P`
      obtain ⟨ZT⟩ : Nonempty (irreducibleComponents T) :=
        ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
      rw [hDS, Divisor.toWeilDivisor_apply]
      by_cases hΓP : Γ.1 = P
      · rw [hΓP, DivisorWithCoeffs.coeff_single_self, if_pos ⟨ZT, by rw [hjη]⟩]
      · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hΓP), if_neg]
        rintro ⟨Z, hZ⟩
        rw [hjη] at hZ
        exact hΓP (AlgebraicGeometry.PrimeDivisor.genericPoint_injective hZ)
    · exact posPart_nonneg _
    · rw [QDivisor.toQWeilDivisor_apply]
      change (Δ Γ.1)⁺ ≤ 1
      rw [posPart_def]
      exact sup_le (hΔle Γ.1) zero_le_one
    · rw [hj] at hmem
      obtain rfl := eq_of_genericPoint_mem_primeDivisor_support hmem
      exact hΓ hΔpP
    · -- `ω(P) = ω · 𝒪_X(P)`
      rw [hωXS, WeilDivisorialSubsheaf.twist, hωK, hDS,
        sheaf_mul_sheaf sV hd (hcart K) (hcart _)]
    · have := congrArg (fun D : QDivisor X => D.coeff Γ.1) hE
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
      rw [Divisor.toWeilDivisor_apply, QDivisor.toQWeilDivisor_apply]
      exact this.symm
    · have := congrArg (fun D : QDivisor T => D.coeff Γ.1) hBT'E
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
      rw [Divisor.toWeilDivisor_apply, QDivisor.toQWeilDivisor_apply, this]
      change BT'.coeff Γ.1 = (m : ℚ) * BT'.coeff Γ.1 / (m : ℚ)
      field_simp
    · rw [hΩ, hKT]
      exact (embeddedDualizingSheaf_eq_sheaf_pullback j (hcart KP) hBKP hωXS).symm
    · rw [hΩ, hpow1 hωXS, weilRestrictionCartier_sheaf_toWeilDivisor j (hcart KP) hBKP]
    · refine isSum_divNat_of_sheaf (j ≫ sV) hdT (isCartier_pullback j (hcart KP) hBKP)
        Divisor.isCartier_zero hΩ hO₀ hΩ ?_
      simp [hKT]
    · rw [hN, hpow1 hLE, weilRestrictionCartier_sheaf_toWeilDivisor j hEc hBE]
    · refine isSum_divNat_of_sheaf (j ≫ sV) hdT Divisor.isCartier_zero
        (isCartier_pullback j hEc hBE) hO₀ hN hN ?_
      simp [hET]
  exact ⟨d, ω, ωXS, DS, hdiff⟩

end Steps

end AdjunctionStepExistence

/-! ### Crepancy of a birational morphism of strata -/

/-- `g : S' ⟶ S` is *crepant* from `(S, B_S)` to `(S', C_{S'})`: for every nonzero rational top
form `τ` on `S`, `div τ + B_S` is `ℚ`-Cartier and `div g^*τ + C_{S'} = g^*(div τ + B_S)`. -/
private def Crep {k : Type} [Field k] {S S' : Scheme.{0}} (sS : S ⟶ Spec (.of k)) (g : S' ⟶ S)
    (BS : QDivisor S) (CS' : QDivisor S') : Prop :=
  ∀ [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] [LocallyOfFiniteType sS]
    [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S'] [CompactSpace S']
    [LocallyOfFiniteType (g ≫ sS)] [IsDominant g],
  ∀ (d : ℕ), topologicalKrullDim S = d → ∀ τ : RationalPluriForms sS d 1, τ ≠ 0 →
    (Divisor.toQDivisor (divisorOfForm τ) + BS).IsQCartier ∧
    ∃ hgen : ∀ W : irreducibleComponents S',
        g (componentGenericPoint S' W) ∉ (Divisor.toQDivisor (divisorOfForm τ) + BS).supp,
      (Divisor.toQDivisor (divisorOfForm τ) + BS).IsPullback g hgen
        (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sS g τ)) + CS')

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

/-! ### Generalities on normal varieties -/

/-- An snc subboundary pair `(X, B)` is a pair: `X` is a smooth, hence normal, variety, and every
`ℚ`-divisor on it is `ℚ`-Cartier. -/
private theorem isPair_of_isSNCSubboundaryPair {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {B : QDivisor X}
    (hB : IsSNCSubboundaryPair sX B) : MMP.Mori.IsPair sX B := by
  have hV : MMP.Mori.IsVariety k sX := hB.isProjectiveVariety.toIsVariety
  haveI : LocallyOfFiniteType sX := hV.toLocallyOfFiniteType
  haveI : CompactSpace X := by
    haveI := hV
    exact QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hB.isSmoothScheme
    (topologicalKrullDim_eq_toNat_trdeg sX)
  exact ⟨⟨hV, inferInstance⟩, _, K, hK, isQCartier_of_isSmoothScheme hB.isSmoothScheme _⟩

/-- The whole of an irreducible scheme is a stratum of every divisor (the empty intersection). -/
private theorem isSNCStratum_univ {S : Scheme.{0}} [IrreducibleSpace S] {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R S) : IsSNCStratum D Set.univ := by
  refine ⟨∅, Finset.empty_subset _, ⟨IrreducibleSpace.isIrreducible_univ _, by simp⟩,
    fun T _ _ => Set.subset_univ T⟩

/-- A normal variety carries a nonzero rational top form. -/
private theorem exists_ne_zero_form {S : Scheme.{0}} [IsIntegral S] {sS : S ⟶ Spec (.of k)}
    (hS : IsNormalVariety k sS) {d : ℕ} (hd : topologicalKrullDim S = d) :
    ∃ τ : RationalPluriForms sS d 1, τ ≠ 0 := by
  letI := functionFieldAlgebra sS
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hS hd
  exact ⟨(ZTensorPower.basis b 1) (), (ZTensorPower.basis b 1).ne_zero ()⟩

/-- The divisor of a nonzero rational top form on a normal variety is a canonical divisor. -/
private theorem isCanonicalDivisor_divisorOfForm' {S : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] {sS : S ⟶ Spec (.of k)}
    [LocallyOfFiniteType sS] (hS : IsNormalVariety k sS) {d : ℕ}
    (hd : topologicalKrullDim S = d) {τ : RationalPluriForms sS d 1} (hτ : τ ≠ 0) :
    (divisorOfForm τ).IsCanonicalDivisor sS d := by
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sS hS hd
  exact hK.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hS hK hτ

/-! ### Restricting an snc subboundary to a component -/

section SNCRestriction

variable {V : Scheme.{0}} {sV : V ⟶ Spec (.of k)}

/-- The pull-back of a divisor along the inclusion of a smooth prime divisor `F` not among its
components is its restriction `B|_F`. -/
private theorem isPullback_restrictPrimeDivisor_int [AlgebraicGeometry.IsVariety k sV]
    [IsLocallyNoetherian V] [IsNormal V] [Smooth sV] (P : MMP.Mori.PrimeDivisor V)
    [IsLocallyNoetherian P.idealSheaf.subscheme] [IsNormal P.idealSheaf.subscheme]
    [Smooth (P.idealSheaf.subschemeι ≫ sV)]
    (B : Divisor V) (hBP : B.coeff P = 0)
    (hB : ∀ Z : irreducibleComponents P.idealSheaf.subscheme,
      P.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉ B.supp) :
    B.IsPullback P.idealSheaf.subschemeι hB (B.restrictPrimeDivisor P) := by
  haveI : IsSmoothVariety k sV := (isSmoothVariety_iff k sV).mpr ⟨inferInstance, inferInstance⟩
  exact (MMP.Mori.Divisor.isPullback_restrictPrimeDivisor k sV P B hBP).snd

/-- The basic facts on an snc subboundary pair `(V, D)` and a component `P` of `D`. -/
private structure Setting (sV : V ⟶ Spec (.of k)) (D : QDivisor V) (P : MMP.Mori.PrimeDivisor V) :
    Prop where
  isVariety : AlgebraicGeometry.IsVariety k sV
  smooth : Smooth sV
  isNormal : IsNormal V
  mem : P ∈ D.support
  smoothP : Smooth (P.idealSheaf.subschemeι ≫ sV)

private theorem setting {D : QDivisor V} (hD : IsSNCSubboundaryPair sV D)
    (P : MMP.Mori.PrimeDivisor V) (hP : D.coeff P ≠ 0) : Setting sV D P := by
  have hv : AlgebraicGeometry.IsVariety k sV := hD.isProjectiveVariety.toIsVariety
  haveI := hv
  haveI hs : Smooth sV := (isSmoothScheme_iff sV).mp hD.isSmoothScheme
  have hPD : P ∈ D.support := Finsupp.mem_support_iff.mpr hP
  have hsm := hD.isSNC.1 P hPD
  haveI : LocallyOfFiniteType (P.idealSheaf.subschemeι ≫ sV) := inferInstance
  exact ⟨hv, hs, isNormal_of_smooth_over_field sV, hPD, (isSmoothScheme_iff _).mp hsm⟩

/-- Local coordinates on a component `P` of an snc divisor adapted to the other components. -/
private theorem exists_coordinates {D : QDivisor V} (hD : IsSNCSubboundaryPair sV D)
    {P : MMP.Mori.PrimeDivisor V} (hS : Setting sV D P) (y : P.idealSheaf.subscheme) :
    ∃ (m : ℕ) (w : Fin m → P.idealSheaf.subscheme.presheaf.stalk y)
      (c : {i : {E : MMP.Mori.PrimeDivisor V // E ∈ D.support ∧ E ≠ P} //
        y ∈ ((i.1.idealSheaf).comap P.idealSheaf.subschemeι).support} → Fin m),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk ((i.1.1.idealSheaf).comap P.idealSheaf.subschemeι) y =
          Ideal.span {w (c i)}) ∧ Function.Injective c := by
  haveI := hS.isVariety
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have hZ : MMP.Resolution.HasSNCWith
      (fun i : {E : MMP.Mori.PrimeDivisor V // E ∈ D.support ∧ E ≠ P} => i.1.idealSheaf)
      P.idealSheaf := by
    intro x hx
    obtain ⟨n, z, jj, hz, hjj, hI⟩ := hD.isSNC.2 x
    refine ⟨n, z, fun i => jj ⟨i.1.1, i.1.2.1, i.2⟩, {jj ⟨P, hS.mem, hx⟩}, hz,
      fun i => hI ⟨i.1.1, i.1.2.1, i.2⟩, fun a b hab => ?_, ?_⟩
    · have h1 := hjj hab
      simp only [Subtype.mk.injEq] at h1
      exact Subtype.ext (Subtype.ext h1)
    · rw [Finset.coe_singleton, Set.image_singleton]
      exact hI ⟨P, hS.mem, hx⟩
  have hcomp : ∀ i : {E : MMP.Mori.PrimeDivisor V // E ∈ D.support ∧ E ≠ P},
      ∀ W ∈ MMP.Resolution.componentsOf (P.idealSheaf.support : Set V),
        ¬ W ⊆ (i.1.idealSheaf).support := by
    intro i W hW hWE
    have hPirr : IsIrreducible (P.idealSheaf.support : Set V) := by
      rw [show (P.idealSheaf.support : Set V) = P.support from rfl,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
    have hWP : (P.idealSheaf.support : Set V) ⊆ W := hW.2 ⟨hPirr, le_rfl⟩ hW.1.2
    have hmem : P.genericPoint ∈ i.1.support := by
      refine hWE (hWP ?_)
      rw [show (P.idealSheaf.support : Set V) = P.support from rfl,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have := i.1.eq_genericPoint_of_mem_support hmem P.coheight_genericPoint
    exact i.2.2 (AlgebraicGeometry.PrimeDivisor.genericPoint_injective this).symm
  exact MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith hZ hcomp y

/-- On an snc component `P`, every connected component of the trace `P ∩ E` of another component
`E` is a prime divisor of `P`. -/
private theorem exists_primeDivisor_eq_connectedComponentIn {D : QDivisor V}
    (hD : IsSNCSubboundaryPair sV D) {P : MMP.Mori.PrimeDivisor V} (hS : Setting sV D P)
    {E : MMP.Mori.PrimeDivisor V} (hE : E ∈ D.support) (hEP : E ≠ P)
    {y : P.idealSheaf.subscheme} (hy : P.idealSheaf.subschemeι y ∈ E.support) :
    ∃ Q : MMP.Mori.PrimeDivisor P.idealSheaf.subscheme,
      Q.support = connectedComponentIn (P.idealSheaf.subschemeι ⁻¹' E.support) y := by
  haveI := hS.isVariety
  haveI := hS.smoothP
  haveI : IsLocallyNoetherian P.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (P.idealSheaf.subschemeι ≫ sV)
  haveI : CompactSpace P.idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (P.idealSheaf.subschemeι ≫ sV)
  haveI : IsNoetherian P.idealSheaf.subscheme := {}
  have hsupp : ((E.idealSheaf.comap P.idealSheaf.subschemeι).support : Set _) =
      P.idealSheaf.subschemeι ⁻¹' E.support := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hloc : ∀ z ∈ (E.idealSheaf.comap P.idealSheaf.subschemeι).support,
      ∃ (m : ℕ) (w : Fin m → P.idealSheaf.subscheme.presheaf.stalk z) (j : Fin m),
        IsRegularSystemOfParameters w ∧
          IdealSheafData.stalk (E.idealSheaf.comap P.idealSheaf.subschemeι) z =
            Ideal.span {w j} := by
    intro z hz
    obtain ⟨m, w, c, hw, hst, -⟩ := exists_coordinates hD hS z
    exact ⟨m, w, c ⟨⟨E, hE, hEP⟩, hz⟩, hw, hst ⟨⟨E, hE, hEP⟩, hz⟩⟩
  have hy' : y ∈ ((E.idealSheaf.comap P.idealSheaf.subschemeι).support : Set _) := by
    rwa [hsupp]
  obtain ⟨Q, hQ⟩ := MMP.Mori.exists_primeDivisor_support_eq_connectedComponentIn _ hloc hy'
  exact ⟨Q, by rw [hQ, hsupp]⟩

/-- The local intersection length of another component `E` of an snc divisor along a prime
divisor `Q` of the component `P` through whose generic point `E` passes is one. -/
private theorem intersectionLength_eq_one {D : QDivisor V} (hD : IsSNCSubboundaryPair sV D)
    {P : MMP.Mori.PrimeDivisor V} (hS : Setting sV D P) {E : MMP.Mori.PrimeDivisor V}
    (hE : E ∈ D.support) (hEP : E ≠ P) (Q : MMP.Mori.PrimeDivisor P.idealSheaf.subscheme)
    (hy : P.idealSheaf.subschemeι Q.genericPoint ∈ E.support) :
    E.intersectionLength P.idealSheaf.subschemeι Q = 1 := by
  obtain ⟨m, w, c, hw, hst, -⟩ := exists_coordinates hD hS Q.genericPoint
  have hz : Q.genericPoint ∈ (E.idealSheaf.comap P.idealSheaf.subschemeι).support := by
    rwa [MMP.Resolution.mem_support_comap_iff]
  set i : {i : {E : MMP.Mori.PrimeDivisor V // E ∈ D.support ∧ E ≠ P} //
      Q.genericPoint ∈ ((i.1.idealSheaf).comap P.idealSheaf.subschemeι).support} :=
    ⟨⟨E, hE, hEP⟩, hz⟩
  have hm : m = 1 := by
    have h1 := hw.2
    rw [ringKrullDim_stalk_eq_coheight, Q.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  subst hm
  have hmax : IdealSheafData.stalk (E.idealSheaf.comap P.idealSheaf.subschemeι) Q.genericPoint =
      IsLocalRing.maximalIdeal _ := by
    rw [hst i, ← hw.1]
    congr 1
    ext a
    simp only [Set.mem_singleton_iff, Set.mem_range]
    exact ⟨fun h => ⟨c i, h.symm⟩, fun ⟨b, hb⟩ => by rw [← hb, Subsingleton.elim b (c i)]⟩
  rw [MMP.Mori.PrimeDivisor.intersectionLength, Scheme.IdealSheafData.stalkIdeal_eq_stalk,
    ← AlgebraicGeometry.IdealSheafData.stalk_comap, hmax]
  have hl : Module.length (P.idealSheaf.subscheme.presheaf.stalk Q.genericPoint)
      (P.idealSheaf.subscheme.presheaf.stalk Q.genericPoint ⧸
        IsLocalRing.maximalIdeal (P.idealSheaf.subscheme.presheaf.stalk Q.genericPoint)) = 1 := by
    rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
    exact IsLocalRing.maximalIdeal.isMaximal _
  rw [hl]
  rfl

/-- Two components `E₁, E₂ ≠ P` of an snc divisor both through the generic point of a prime
divisor of `P` are equal. -/
private theorem eq_of_mem_support {D : QDivisor V} (hD : IsSNCSubboundaryPair sV D)
    {P : MMP.Mori.PrimeDivisor V} (hS : Setting sV D P) {E₁ E₂ : MMP.Mori.PrimeDivisor V}
    (hE₁ : E₁ ∈ D.support) (hE₁P : E₁ ≠ P) (hE₂ : E₂ ∈ D.support) (hE₂P : E₂ ≠ P)
    (Q : MMP.Mori.PrimeDivisor P.idealSheaf.subscheme)
    (h₁ : P.idealSheaf.subschemeι Q.genericPoint ∈ E₁.support)
    (h₂ : P.idealSheaf.subschemeι Q.genericPoint ∈ E₂.support) : E₁ = E₂ := by
  obtain ⟨m, w, c, hw, -, hinj⟩ := exists_coordinates hD hS Q.genericPoint
  have hm : m = 1 := by
    have h1 := hw.2
    rw [ringKrullDim_stalk_eq_coheight, Q.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  subst hm
  have hz₁ : Q.genericPoint ∈ (E₁.idealSheaf.comap P.idealSheaf.subschemeι).support := by
    rwa [MMP.Resolution.mem_support_comap_iff]
  have hz₂ : Q.genericPoint ∈ (E₂.idealSheaf.comap P.idealSheaf.subschemeι).support := by
    rwa [MMP.Resolution.mem_support_comap_iff]
  have := hinj (a₁ := ⟨⟨E₁, hE₁, hE₁P⟩, hz₁⟩) (a₂ := ⟨⟨E₂, hE₂, hE₂P⟩, hz₂⟩)
    (Subsingleton.elim _ _)
  simpa only [Subtype.mk.injEq] using this

/-- The coefficients of the restriction `(D - P)|_P` of an snc subboundary to a component. -/
private theorem coeff_restrict {D : QDivisor V} (hD : IsSNCSubboundaryPair sV D)
    {P : MMP.Mori.PrimeDivisor V} (hS : Setting sV D P) (hP : D.coeff P = 1)
    (Q : MMP.Mori.PrimeDivisor P.idealSheaf.subscheme) :
    ((∀ E ∈ D.support, E ≠ P → P.idealSheaf.subschemeι Q.genericPoint ∉ E.support) →
        ((D - Finsupp.single P 1).restrictPrimeDivisor P).coeff Q = 0) ∧
      ∀ E ∈ D.support, E ≠ P → P.idealSheaf.subschemeι Q.genericPoint ∈ E.support →
        ((D - Finsupp.single P 1).restrictPrimeDivisor P).coeff Q = D.coeff E := by
  classical
  haveI := hS.isVariety
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : IsNoetherian V := {}
  have h0 := (coeff_parts_sub_single_eq_zero hP).1
  have hcoeff : ∀ E, E ≠ P → (D - Finsupp.single P 1).coeff E = D.coeff E := fun E hE => by
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hE), sub_zero]
  have hsupp : ∀ E ∈ (D - Finsupp.single P 1).support, E ∈ D.support ∧ E ≠ P := by
    intro E hE
    have hne : (D - Finsupp.single P 1).coeff E ≠ 0 := Finsupp.mem_support_iff.mp hE
    have hEP : E ≠ P := fun h => hne (h ▸ h0)
    refine ⟨Finsupp.mem_support_iff.mpr ?_, hEP⟩
    change D.coeff E ≠ 0
    rwa [← hcoeff E hEP]
  rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ h0]
  refine ⟨fun h => ?_, fun E hE hEP hy => ?_⟩
  · refine Finset.sum_eq_zero fun E hE => ?_
    obtain ⟨hE', hEP⟩ := hsupp E hE
    simp only [MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem _ E (h E hE' hEP),
      zero_smul]
  · have hEs : E ∈ (D - Finsupp.single P 1).support := by
      refine Finsupp.mem_support_iff.mpr ?_
      change (D - Finsupp.single P 1).coeff E ≠ 0
      rw [hcoeff E hEP]; exact Finsupp.mem_support_iff.mp hE
    rw [Finsupp.sum, Finset.sum_eq_single E]
    · simp only [intersectionLength_eq_one hD hS hE hEP Q hy, one_smul]
      exact hcoeff E hEP
    · intro E' hE' hE'E
      obtain ⟨hE'', hE'P⟩ := hsupp E' hE'
      by_cases hy' : P.idealSheaf.subschemeι Q.genericPoint ∈ E'.support
      · exact absurd (eq_of_mem_support hD hS hE'' hE'P hE hEP Q hy' hy) hE'E
      · simp only [MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem _ E' hy',
          zero_smul]
    · exact fun h => absurd hEs h

/-- The restriction to a prime divisor is additive. -/
private theorem restrictPrimeDivisor_sub [NoetherianSpace V] (A A' : QDivisor V)
    (P : MMP.Mori.PrimeDivisor V) (hA : A.coeff P = 0) (hA' : A'.coeff P = 0) :
    (A - A').restrictPrimeDivisor P = A.restrictPrimeDivisor P - A'.restrictPrimeDivisor P := by
  have h0 : (A - A').coeff P = 0 := by rw [DivisorWithCoeffs.coeff_sub, hA, hA', sub_self]
  ext Q
  rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ h0,
    DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ hA,
    DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ hA']
  exact Finsupp.sum_sub_index fun E a b => smul_sub _ a b

/-- The restriction of `ℚ`-divisors to a smooth prime divisor is their pull-back. -/
private theorem pullback_eq_restrictPrimeDivisor [AlgebraicGeometry.IsVariety k sV]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [Smooth sV]
    (P : MMP.Mori.PrimeDivisor V)
    [IsIntegral P.idealSheaf.subscheme] [IsLocallyNoetherian P.idealSheaf.subscheme]
    [IsNormal P.idealSheaf.subscheme] [CompactSpace P.idealSheaf.subscheme]
    [Smooth (P.idealSheaf.subschemeι ≫ sV)]
    (A : QDivisor V) (hAP : A.coeff P = 0) (hq : A.IsQCartier)
    (hA : ∀ Z : irreducibleComponents P.idealSheaf.subscheme,
      P.idealSheaf.subschemeι (componentGenericPoint _ Z) ∉ A.supp) :
    A.pullback hq hA = A.restrictPrimeDivisor P := by
  haveI : IsNoetherian V := {}
  refine QDivisor.IsPullback.pullback_eq (f := P.idealSheaf.subschemeι) hq ?_
  intro m hm D hD hDc
  have hDP : D.coeff P = 0 := by
    have := congrArg (fun G : QDivisor V => G.coeff P) hD
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, hAP, smul_zero] at this
    exact_mod_cast this
  refine ⟨D.restrictPrimeDivisor P, ?_, isPullback_restrictPrimeDivisor_int (sV := sV) P D hDP _⟩
  ext Q
  rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ hDP,
    DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ hAP]
  have hDA : ∀ E, (D E : ℚ) = (m : ℚ) * A E := fun E => by
    have := congrArg (fun G : QDivisor V => G.coeff E) hD
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at this
    exact this
  classical
  rw [Finsupp.sum_of_support_subset D (Finset.subset_union_left (s₂ := A.support))
      (fun E d => E.intersectionLength P.idealSheaf.subschemeι Q • d) (fun _ _ => smul_zero _),
    Finsupp.sum_of_support_subset A (Finset.subset_union_right (s₁ := D.support))
      (fun E d => E.intersectionLength P.idealSheaf.subschemeι Q • d) (fun _ _ => smul_zero _),
    Int.cast_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  rw [hDA E]
  ring

/-- The components of `B^{=1}` are the prime divisors with coefficient one in `B`. -/
private theorem mem_coeffOnePart_support {X : Scheme.{0}} {B : QDivisor X}
    {E : MMP.Mori.PrimeDivisor X} : E ∈ (coeffOnePart B).support ↔ B.coeff E = 1 := by
  rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, coeff_coeffOnePart]
  split_ifs with h <;> simp [h]

/-- A prime divisor `Q` of a component `P` lying on another component `E` of an snc divisor is a
connected component of `P ∩ E`. -/
private theorem support_eq_connectedComponentIn {D : QDivisor V}
    (hD : IsSNCSubboundaryPair sV D) {P : MMP.Mori.PrimeDivisor V} (hS : Setting sV D P)
    {E : MMP.Mori.PrimeDivisor V} (hE : E ∈ D.support) (hEP : E ≠ P)
    (Q : MMP.Mori.PrimeDivisor P.idealSheaf.subscheme)
    (hy : P.idealSheaf.subschemeι Q.genericPoint ∈ E.support) :
    Q.support = connectedComponentIn (P.idealSheaf.subschemeι ⁻¹' E.support) Q.genericPoint := by
  obtain ⟨Q', hQ'⟩ := exists_primeDivisor_eq_connectedComponentIn hD hS hE hEP hy
  have hmem : Q.genericPoint ∈ Q'.support := by
    rw [hQ']; exact mem_connectedComponentIn hy
  have := Q'.eq_genericPoint_of_mem_support hmem Q.coheight_genericPoint
  rw [← hQ', AlgebraicGeometry.PrimeDivisor.genericPoint_injective this]

end SNCRestriction

/-! ### Pull-backs of `ℚ`-divisors -/

section QPullback

/-- Pull-back of `ℚ`-divisors along a composite `e = g ≫ f`. -/
private theorem qIsPullback_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {e : Z ⟶ X} (he : g ≫ f = e)
    {M : QDivisor X} {MY : QDivisor Y} {MZ : QDivisor Z}
    {hM : ∀ C : irreducibleComponents Y, f (componentGenericPoint Y C) ∉ M.supp}
    {hMY : ∀ C : irreducibleComponents Z, g (componentGenericPoint Z C) ∉ MY.supp}
    (h₁ : M.IsPullback f hM MY) (h₂ : MY.IsPullback g hMY MZ)
    (hM' : ∀ C : irreducibleComponents Z, e (componentGenericPoint Z C) ∉ M.supp) :
    M.IsPullback e hM' MZ := fun m hm D hD hDc => by
  obtain ⟨D', hD', hpb⟩ := h₁ m hm D hD hDc
  obtain ⟨D'', hD'', hpb'⟩ := h₂ m hm D' hD' (hpb.isCartier hDc)
  exact ⟨D'', hD'', MMP.ProgramBaseChange.divisor_isPullback_comp he hpb hpb' _⟩

/-- The divisor of a form does not depend on the presentation of the structure morphism. -/
private theorem divisorOfForm_cast {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X] {s₁ s₂ : X ⟶ Spec (.of k)} (e : s₁ = s₂)
    [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂] {d : ℕ} {m : ℤ}
    (h : RationalPluriForms s₁ d m = RationalPluriForms s₂ d m) (x : RationalPluriForms s₁ d m) :
    divisorOfForm (cast h x) = divisorOfForm x := by
  subst e
  rfl

/-- A scheme of dimension zero has no prime divisor. -/
private theorem isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero {X : Scheme.{0}}
    (h : topologicalKrullDim X = 0) : IsEmpty (MMP.Mori.PrimeDivisor X) := by
  refine ⟨fun Q => ?_⟩
  let _ : PartialOrder X := specializationOrder X
  have hk : Order.krullDim X = 0 := by
    rw [← h]
    exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).symm
  have h1 : Order.coheight Q.genericPoint = 1 := Q.coheight_genericPoint
  have h2 := Order.coheight_le_krullDim Q.genericPoint
  rw [h1, hk] at h2
  exact absurd h2 (by decide)

end QPullback

/-! ### The main induction -/

/-- The base of the induction: `h` is crepant from `(X, B)` to `(Y, C)`. -/
private theorem crep_base {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} {C : QDivisor Y}
    {h : Y ⟶ X} {n : ℕ} {KX : Divisor X}
    (hB : IsSNCSubboundaryPair sX B) (hbir : IsBirationalMorphism h)
    (hKX : KX.IsCanonicalDivisor sX n)
    (hcrep : ∃ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C) :
    Crep sX h B C := by
  intro _ _ _ _ _ _ _ _ _ _ _ d hd τ hτ
  obtain ⟨hY, hcb⟩ := hcrep
  have hsm := hB.isSmoothScheme
  have hnd : n = d := by
    have := hKX.topologicalKrullDim_eq
    rw [hd] at this
    exact_mod_cast this.symm
  subst hnd
  have hXv : IsNormalVariety k sX := ⟨hB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hK := isCanonicalDivisor_divisorOfForm' hXv hd hτ
  have hdY : topologicalKrullDim Y = n := by
    haveI := hXv.1
    haveI := hY.1
    rw [← hd]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (h ≫ sX) hbir).symm
  have hτ' : pullbackRationalPluriForms sX h τ ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' h
      hbir.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hd) hτ
  have hKY := isCanonicalDivisor_divisorOfForm' hY hdY hτ'
  have hcb' : IsCrepantBoundary sX n (divisorOfForm τ) B h hY hbir C := fun F => by
    obtain ⟨hX, -, m, hm, ⟨D, hD, -⟩, U, hU, σ, hσ, ha⟩ := hcb F
    refine ⟨hX, hK, m, hm, ⟨D + (m : ℤ) • (divisorOfForm τ - KX), ?_,
      MMP.Fourfold.isCartier_of_isSmoothScheme hsm _⟩, U, hU, σ, hσ, ha⟩
    rw [map_add, hD, map_zsmul, map_sub, ← smul_add]
    congr 1
    abel
  refine ⟨isQCartier_of_isSmoothScheme hsm _, ?_⟩
  exact (MMP.Mori.IsPair.isPullback_of_isCrepantBoundary (isPair_of_isSNCSubboundaryPair hB) h hY
    hbir hK hKY (Or.inl ⟨τ, hτ, rfl, rfl⟩) hcb').2.2

/-- The adjunction step to a floor component of an snc subboundary. -/
private theorem snc_step {V : Scheme.{0}} {sV : V ⟶ Spec (.of k)} {D : QDivisor V}
    (hD : IsSNCSubboundaryPair sV D) (P : MMP.Mori.PrimeDivisor V) (hP : D.coeff P = 1) :
    IsSNCSubboundaryPair (P.idealSheaf.subschemeι ≫ sV)
        ((D - Finsupp.single P 1).restrictPrimeDivisor P) ∧
      IsAdjunctionStep sV D P.idealSheaf.subschemeι
        ((D - Finsupp.single P 1).restrictPrimeDivisor P) ∧
      (∀ Q : MMP.Mori.PrimeDivisor P.idealSheaf.subscheme,
        ((D - Finsupp.single P 1).restrictPrimeDivisor P).coeff Q = 1 →
          ∃ E : MMP.Mori.PrimeDivisor V, E ≠ P ∧ D.coeff E = 1 ∧
            P.idealSheaf.subschemeι Q.genericPoint ∈ E.support) ∧
      (∀ E : MMP.Mori.PrimeDivisor V, E ≠ P → D.coeff E = 1 →
        ∀ Q : MMP.Mori.PrimeDivisor P.idealSheaf.subscheme,
          P.idealSheaf.subschemeι Q.genericPoint ∈ E.support →
            ((D - Finsupp.single P 1).restrictPrimeDivisor P).coeff Q = 1) := by
  classical
  have hS := setting hD P (by rw [hP]; exact one_ne_zero)
  haveI := hS.isVariety
  haveI := hS.smooth
  haveI := hS.isNormal
  haveI := hS.smoothP
  haveI : IsIntegral V := hS.isVariety.toIsIntegral
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : IsNoetherian V := {}
  haveI := P.integral
  haveI : IsLocallyNoetherian P.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (P.idealSheaf.subschemeι ≫ sV)
  haveI : IsNormal P.idealSheaf.subscheme :=
    isNormal_of_smooth_over_field (P.idealSheaf.subschemeι ≫ sV)
  haveI : CompactSpace P.idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (P.idealSheaf.subschemeι ≫ sV)
  haveI : IsNoetherian P.idealSheaf.subscheme := {}
  set j := P.idealSheaf.subschemeι with hjdef
  set DT := (D - Finsupp.single P 1).restrictPrimeDivisor P with hDT
  have hcoef := coeff_restrict hD hS hP
  have hle : ∀ Q, DT.coeff Q ≤ 1 := fun Q => by
    by_cases h : ∃ E ∈ D.support, E ≠ P ∧ j Q.genericPoint ∈ E.support
    · obtain ⟨E, hE, hEP, hy⟩ := h
      rw [(hcoef Q).2 E hE hEP hy]
      exact hD.coeff_le_one E
    · push Not at h
      rw [(hcoef Q).1 h]
      norm_num
  have hA3 : ∀ Q, DT.coeff Q = 1 → ∃ E : MMP.Mori.PrimeDivisor V, E ≠ P ∧ D.coeff E = 1 ∧
      j Q.genericPoint ∈ E.support := fun Q hQ => by
    by_contra h
    have h' : ∀ E ∈ D.support, E ≠ P → j Q.genericPoint ∉ E.support := by
      intro E hE hEP hy
      exact h ⟨E, hEP, by rw [← (hcoef Q).2 E hE hEP hy, hQ], hy⟩
    rw [(hcoef Q).1 h'] at hQ
    exact zero_ne_one hQ
  have hA4 : ∀ E : MMP.Mori.PrimeDivisor V, E ≠ P → D.coeff E = 1 → ∀ Q,
      j Q.genericPoint ∈ E.support → DT.coeff Q = 1 := fun E hEP hE1 Q hy => by
    have hE : E ∈ D.support := Finsupp.mem_support_iff.mpr (by
      change D.coeff E ≠ 0; rw [hE1]; exact one_ne_zero)
    rw [(hcoef Q).2 E hE hEP hy, hE1]
  -- the snc condition on `P`
  have hsncR := MMP.Mori.DivisorWithCoeffs.isSNC_restrictPrimeDivisor_sum_single sV P
    (D.support.erase P) (Finset.notMem_erase P _) (hD.isSNC.of_support_subset (by
      intro E hE
      by_contra hE'
      have hEP : E ≠ P := fun h => hE' (h ▸ hS.mem)
      have : (Finsupp.single P (1 : ℤ) + ∑ E ∈ D.support.erase P, Finsupp.single E (1 : ℤ)) E
          = 0 := by
        rw [Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.single_apply, if_neg (Ne.symm hEP)]
        refine (zero_add _).trans (Finset.sum_eq_zero fun E' hE'' => ?_)
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hE' (Finset.mem_of_mem_erase hE'')
      exact (Finsupp.mem_support_iff.mp hE) this))
  have hsnc : DivisorWithCoeffs.IsSNC (j ≫ sV) DT := by
    refine hsncR.1.of_support_subset fun Q hQ => ?_
    have hne : DT.coeff Q ≠ 0 := Finsupp.mem_support_iff.mp hQ
    have hex : ∃ E ∈ D.support, E ≠ P ∧ j Q.genericPoint ∈ E.support := by
      by_contra h
      push Not at h
      exact hne ((hcoef Q).1 h)
    obtain ⟨E, hE, hEP, hy⟩ := hex
    refine Finsupp.mem_support_iff.mpr ?_
    have h0 : (∑ E ∈ D.support.erase P, Finsupp.single E (1 : ℤ) : Divisor V).coeff P = 0 := by
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
      refine Finset.sum_eq_zero fun E' hE' => ?_
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact Finset.notMem_erase _ _ hE'
    change DivisorWithCoeffs.coeff _ Q ≠ 0
    rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ h0,
      Finsupp.sum_of_support_subset _ (s := D.support.erase P)
        (Finsupp.support_finset_sum.trans ?_)
        (fun (E : MMP.Mori.PrimeDivisor V) (d : ℤ) => E.intersectionLength j Q • d)
        (fun _ _ => smul_zero _)]
    · have hEm : E ∈ D.support.erase P := Finset.mem_erase.mpr ⟨hEP, hE⟩
      have hpos : ∀ E' ∈ D.support.erase P, 0 ≤ E'.intersectionLength j Q •
          (∑ E ∈ D.support.erase P, Finsupp.single E (1 : ℤ)) E' := fun E' _ =>
        smul_nonneg (Nat.zero_le _) (by
          rw [Finsupp.finset_sum_apply]
          exact Finset.sum_nonneg fun _ _ => by rw [Finsupp.single_apply]; split_ifs <;> norm_num)
      have hterm : E.intersectionLength j Q •
          (∑ E ∈ D.support.erase P, Finsupp.single E (1 : ℤ)) E = 1 := by
        rw [intersectionLength_eq_one hD hS hE hEP Q hy, one_smul, Finsupp.finset_sum_apply,
          Finset.sum_eq_single E (fun E' _ hE'E => by rw [Finsupp.single_apply, if_neg hE'E])
            (fun h => absurd hEm h), Finsupp.single_eq_same]
      have := Finset.single_le_sum hpos hEm
      rw [hterm] at this
      omega
    · intro E' hE'
      simp only [Finset.mem_biUnion] at hE'
      obtain ⟨E'', hE'', hE'⟩ := hE'
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hE'
      exact hE' ▸ hE''
  -- the adjunction step
  have hstep : IsAdjunctionStep sV D j DT := by
    have hTv : IsNormalVariety k (j ≫ sV) := by
      refine ⟨?_, inferInstance⟩
      constructor <;> infer_instance
    have hVv : IsNormalVariety k sV := ⟨hS.isVariety, inferInstance⟩
    haveI : IsProper sV := isProper_of_isProjectiveMorphism sV hD.isProjectiveVariety.isProjective
    have hdim : ∀ {Y : Scheme.{0}} [IsIntegral Y] (sY : Y ⟶ Spec (.of k))
        [LocallyOfFiniteType sY], ∀ Z ∈ irreducibleComponents Y, topologicalKrullDim Z =
          ((letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat : ℕ) :
            WithBot ℕ∞) := by
      intro Y _ sY _ Z hZ
      rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
      subst hZ
      rw [(Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq]
      exact topologicalKrullDim_eq_toNat_trdeg sY
    have hcart : ∀ G : Divisor V, G.IsCartier :=
      MMP.Fourfold.isCartier_of_isSmoothScheme hD.isSmoothScheme
    have hgor : ∀ η : V, Order.coheight η ≤ 1 → ∃ _ : IsNoetherianRing (V.presheaf.stalk η),
        Dualizing.IsGorensteinLocalRing (V.presheaf.stalk η) := fun η _ => by
      haveI := isRegularLocalRing_stalk_of_smooth_over_field sV η
      exact ⟨inferInstance, Dualizing.IsRegularLocalRing.isGorensteinLocalRing _⟩
    have hjr : Set.range j.base = (P.support : Set V) := by
      rw [hjdef, P.idealSheaf.range_subschemeι]
    obtain ⟨hBp, hBn, hqp, hqn, d', ω, ωXS, DS, hst⟩ := exists_isDifferentDivisor_pullback sV hVv
      (hdim sV) (hdim (j ≫ sV)) hcart hgor hD.coeff_le_one P hP j hjr hTv
    obtain ⟨-, hΔp, hΔn⟩ := coeff_parts_sub_single_eq_zero hP
    have hDT : DT = ((D - Finsupp.single P 1)⁺).pullback hqp hBp -
        ((D - Finsupp.single P 1)⁻).pullback hqn hBn := by
      rw [pullback_eq_restrictPrimeDivisor (sV := sV) P _ hΔp hqp hBp,
        pullback_eq_restrictPrimeDivisor (sV := sV) P _ hΔn hqn hBn,
        ← restrictPrimeDivisor_sub _ _ P hΔp hΔn, posPart_sub_negPart]
    -- a form with a simple pole along `P`, and its residue
    obtain ⟨n, hdV⟩ := MMP.Fourfold.exists_topologicalKrullDim_eq_add_one sV P
    obtain ⟨τ, hτ0, hτP, ρ, hρ, -⟩ :=
      MMP.Fourfold.exists_ordForm_eq_neg_one_isPoincareResidue_of_charZero sV hdV j P hjr
    have hqall : ∀ G : QDivisor V, G.IsQCartier := fun G => by
      obtain ⟨N, hN, G', hG'⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor G
      exact ⟨N, by exact_mod_cast hN.ne', G', hG', hcart G'⟩
    refine MMP.Fourfold.isAdjunctionStep_of_isDifferentDivisor hTv hdV P hP.ge hjr hst hBn hqn
      ?_ τ hτ0 hτP ρ hρ (hqall _)
    rw [hDT, sub_sub_cancel]
    exact QDivisor.isPullback_pullback _ _
  refine ⟨⟨?_, hD.isSNC.1 P hS.mem, hsnc, hle⟩, hstep, hA3, hA4⟩
  refine (AlgebraicGeometry.isProjectiveVariety_iff k _).mpr ⟨?_, ?_⟩
  · constructor <;> infer_instance
  · exact (MMP.isProjectiveMorphism_of_isClosedImmersion _).comp
      hD.isProjectiveVariety.isProjective

/-- Floor strata of the restricted boundary are floor strata of the boundary. -/
private theorem isSNCStratum_image {V : Scheme.{0}} {sV : V ⟶ Spec (.of k)} {D : QDivisor V}
    (hD : IsSNCSubboundaryPair sV D) (P : MMP.Mori.PrimeDivisor V) (hP : D.coeff P = 1)
    {W : Set P.idealSheaf.subscheme}
    (hW : IsSNCStratum (coeffOnePart ((D - Finsupp.single P 1).restrictPrimeDivisor P)) W) :
    IsSNCStratum (coeffOnePart D) (P.idealSheaf.subschemeι.base '' W) := by
  classical
  have hS := setting hD P (by rw [hP]; exact one_ne_zero)
  obtain ⟨-, -, hA3, -⟩ := snc_step hD P hP
  set j := P.idealSheaf.subschemeι with hjdef
  have hjc : Continuous j := j.continuous
  have hjemb := j.isClosedEmbedding
  obtain ⟨J, hJ, hmax⟩ := hW
  have hJ1 : ∀ Q ∈ J, ((D - Finsupp.single P 1).restrictPrimeDivisor P).coeff Q = 1 :=
    fun Q hQ => mem_coeffOnePart_support.mp (hJ hQ)
  haveI : Nonempty (MMP.Mori.PrimeDivisor V) := ⟨P⟩
  choose! Ef hEf using fun Q (hQ : Q ∈ J) => hA3 Q (hJ1 Q hQ)
  have hEfD : ∀ Q ∈ J, Ef Q ∈ D.support := fun Q hQ =>
    Finsupp.mem_support_iff.mpr (by
      change D.coeff (Ef Q) ≠ 0; rw [(hEf Q hQ).2.1]; exact one_ne_zero)
  have hrange : Set.range j = P.support := P.idealSheaf.range_subschemeι
  -- a closed irreducible subset of `T` maps into `E_Q` iff its generic point does
  have hsub : ∀ Q ∈ J, j '' Q.support ⊆ (Ef Q).support := by
    intro Q hQ x ⟨w, hw, hwx⟩
    rw [← hwx]
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hw
    exact ((specializes_iff_mem_closure.mpr hw).map hjc).mem_closed
      (Ef Q).idealSheaf.support.isClosed (hEf Q hQ).2.2
  refine ⟨insert P (J.image Ef), ?_, ⟨hmax.1.1.image j hjc.continuousOn, ?_⟩, ?_⟩
  · intro E hE
    rw [Finset.mem_insert, Finset.mem_image] at hE
    rcases hE with rfl | ⟨Q, hQ, rfl⟩
    · exact mem_coeffOnePart_support.mpr hP
    · exact mem_coeffOnePart_support.mpr (hEf Q hQ).2.1
  · rintro x ⟨w, hw, rfl⟩
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_image]
    rintro E (rfl | ⟨Q, hQ, rfl⟩)
    · rw [← hrange]; exact ⟨w, rfl⟩
    · have hwQ : w ∈ Q.support := by
        have := hmax.1.2 hw
        simp only [Set.mem_iInter] at this
        exact this Q hQ
      exact hsub Q hQ ⟨w, hwQ, rfl⟩
  · rintro W' ⟨hW'irr, hW'sub⟩ hle
    have hW'P : W' ⊆ P.support := fun x hx => by
      have := hW'sub hx
      simp only [Set.mem_iInter, Finset.mem_insert] at this
      exact this P (Or.inl rfl)
    -- the generic point of the closure of `W'` lies on `P`
    set ξ := hW'irr.genericPoint
    have hξ := hW'irr.isGenericPoint_genericPoint_closure
    have hclP : closure W' ⊆ P.support :=
      (P.idealSheaf.support.isClosed.closure_subset_iff).mpr hW'P
    have hξP : ξ ∈ P.support := hclP (hξ.mem)
    obtain ⟨ξ₀, hξ₀⟩ : ξ ∈ Set.range j := hrange ▸ hξP
    set W₀ := closure ({ξ₀} : Set P.idealSheaf.subscheme)
    have hW₀img : j '' W₀ = closure W' := by
      rw [← hjemb.isClosedMap.closure_image_eq_of_continuous hjc, Set.image_singleton, hξ₀]
      exact hξ.def
    have hWW₀ : W ⊆ W₀ := by
      intro w hw
      have : j w ∈ j '' W₀ := hW₀img ▸ subset_closure (hle ⟨w, hw, rfl⟩)
      obtain ⟨w', hw', hww'⟩ := this
      exact hjemb.injective hww' ▸ hw'
    have hW₀Q : ∀ Q ∈ J, W₀ ⊆ Q.support := by
      intro Q hQ
      have hcc := support_eq_connectedComponentIn hD hS (hEfD Q hQ) (hEf Q hQ).1 Q
        (hEf Q hQ).2.2
      have hW₀E : W₀ ⊆ j ⁻¹' (Ef Q).support := by
        intro z hz
        have : j z ∈ closure W' := hW₀img ▸ ⟨z, hz, rfl⟩
        have hcl : closure W' ⊆ (Ef Q).support :=
          ((Ef Q).idealSheaf.support.isClosed.closure_subset_iff).mpr fun x hx => by
            have := hW'sub hx
            simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_image] at this
            exact this (Ef Q) (Or.inr ⟨Q, hQ, rfl⟩)
        exact hcl this
      obtain ⟨w, hw⟩ := hmax.1.1.nonempty
      have hwQ : w ∈ Q.support := by
        have := hmax.1.2 hw
        simp only [Set.mem_iInter] at this
        exact this Q hQ
      rw [hcc] at hwQ ⊢
      rw [connectedComponentIn_eq hwQ]
      exact (IsIrreducible.isConnected isIrreducible_singleton.closure).isPreconnected
        |>.subset_connectedComponentIn (hWW₀ hw) hW₀E
    calc W' ⊆ closure W' := subset_closure
      _ = j '' W₀ := hW₀img.symm
      _ ⊆ j '' W := Set.image_mono <| hmax.2 ⟨isIrreducible_singleton.closure, fun z hz => by
          simp only [Set.mem_iInter]
          exact fun Q hQ => hW₀Q Q hQ hz⟩ hWW₀

/-- The induction behind `exists_flag`, on the number of components cutting out the stratum. -/
private theorem exists_flag_aux {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} (n : ℕ) :
    ∀ {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (_ : StratumAdjunctionData sX B ι BS)
      (_ : IsSNCSubboundaryPair (ι ≫ sX) BS) (J : Finset (MMP.Mori.PrimeDivisor S))
      (_ : J ⊆ (coeffOnePart BS).support) {Z : Set S}
      (_ : Maximal (fun T : Set S => IsIrreducible T ∧ T ⊆ ⋂ E ∈ J, (E.support : Set S)) Z),
      J.card = n →
      ∃ (S₁ : Scheme.{0}) (ι₁ : S₁ ⟶ X) (B₁ : QDivisor S₁),
        Nonempty (StratumAdjunctionData sX B ι₁ B₁) ∧ Set.range ι₁.base = ι.base '' Z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S ι BS F hS J hJ Z hmax hn
  classical
  haveI := F.isIntegral_stratum
  rcases J.eq_empty_or_nonempty with rfl | ⟨P, hPJ⟩
  · have hZ : Z = Set.univ := Set.eq_univ_of_univ_subset
      (hmax.2 ⟨IrreducibleSpace.isIrreducible_univ _, by simp⟩ (Set.subset_univ Z))
    exact ⟨S, ι, BS, ⟨F⟩, by rw [hZ, Set.image_univ]⟩
  have hP1 : BS.coeff P = 1 := mem_coeffOnePart_support.mp (hJ hPJ)
  obtain ⟨hS₁, hstep, -, hA4⟩ := snc_step hS P hP1
  have hSet := setting hS P (by rw [hP1]; exact one_ne_zero)
  set j := P.idealSheaf.subschemeι with hjdef
  have hjc : Continuous j := j.continuous
  have hjemb := j.isClosedEmbedding
  have hrange : Set.range j = P.support := P.idealSheaf.range_subschemeι
  have F₁ := F.step j _ hstep
  have hS₁' : IsSNCSubboundaryPair ((j ≫ ι) ≫ sX)
      ((BS - Finsupp.single P 1).restrictPrimeDivisor P) := by rwa [Category.assoc]
  have hZsub : Z ⊆ ⋂ E ∈ J, (E.support : Set S) := hmax.1.2
  have hZE : ∀ E ∈ J, Z ⊆ E.support := fun E hE z hz => by
    have := hZsub hz
    simp only [Set.mem_iInter] at this
    exact this E hE
  have hclosed : IsClosed (⋂ E ∈ J, (E.support : Set S)) :=
    isClosed_biInter fun E _ => E.idealSheaf.support.isClosed
  have hZcl : closure Z = Z := subset_antisymm
    (hmax.2 ⟨hmax.1.1.closure, hclosed.closure_subset_iff.mpr hZsub⟩ subset_closure) subset_closure
  set ζ := hmax.1.1.genericPoint
  have hζ : closure ({ζ} : Set S) = Z := by
    rw [← hZcl]; exact hmax.1.1.isGenericPoint_genericPoint_closure.def
  have hζZ : ζ ∈ Z := hζ ▸ subset_closure rfl
  obtain ⟨ζ₁, hζ₁⟩ : ζ ∈ Set.range j := hrange ▸ hZE P hPJ hζZ
  have hEmem : ∀ E ∈ J.erase P, E ∈ BS.support ∧ E ≠ P := fun E hE => by
    obtain ⟨hEP, hEJ⟩ := Finset.mem_erase.mp hE
    exact ⟨Finsupp.mem_support_iff.mpr (by
      change BS.coeff E ≠ 0; rw [mem_coeffOnePart_support.mp (hJ hEJ)]; exact one_ne_zero), hEP⟩
  have hζE : ∀ E ∈ J.erase P, j ζ₁ ∈ E.support := fun E hE => by
    rw [hζ₁]; exact hZE E (Finset.mem_of_mem_erase hE) hζZ
  choose QE hQE using fun E (hE : E ∈ J.erase P) =>
    exists_primeDivisor_eq_connectedComponentIn hS hSet (hEmem E hE).1 (hEmem E hE).2
      (hζE E hE)
  set J₁ := (J.erase P).attach.image fun E => QE E.1 E.2 with hJ₁def
  have hcard : J₁.card < n := by
    refine (Finset.card_image_le).trans_lt ?_
    rw [Finset.card_attach, Finset.card_erase_of_mem hPJ, ← hn]
    exact Nat.sub_lt (Finset.card_pos.mpr ⟨P, hPJ⟩) one_pos
  have hQEsub : ∀ E (hE : E ∈ J.erase P), (QE E hE).support ⊆ j ⁻¹' E.support :=
    fun E hE => (hQE E hE).trans_subset (connectedComponentIn_subset _ _)
  have hζ₁Q : ∀ E (hE : E ∈ J.erase P), ζ₁ ∈ (QE E hE).support := fun E hE => by
    rw [hQE E hE]; exact mem_connectedComponentIn (hζE E hE)
  have hJ₁ : J₁ ⊆ (coeffOnePart ((BS - Finsupp.single P 1).restrictPrimeDivisor P)).support := by
    intro Q hQ
    obtain ⟨⟨E, hE⟩, -, rfl⟩ := Finset.mem_image.mp hQ
    refine mem_coeffOnePart_support.mpr (hA4 E (hEmem E hE).2
      (mem_coeffOnePart_support.mp (hJ (Finset.mem_of_mem_erase hE))) _ ?_)
    exact hQEsub E hE (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  have hZ₁ : j ⁻¹' Z = closure ({ζ₁} : Set P.idealSheaf.subscheme) := by
    rw [hjemb.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hζ₁, hζ]
  have hmax₁ : Maximal (fun T : Set P.idealSheaf.subscheme =>
      IsIrreducible T ∧ T ⊆ ⋂ Q ∈ J₁, (Q.support : Set _)) (j ⁻¹' Z) := by
    refine ⟨⟨hZ₁ ▸ isIrreducible_singleton.closure, ?_⟩, ?_⟩
    · intro z hz
      simp only [Set.mem_iInter]
      intro Q hQ
      obtain ⟨⟨E, hE⟩, -, rfl⟩ := Finset.mem_image.mp hQ
      rw [hZ₁] at hz
      exact ((QE E hE).idealSheaf.support.isClosed.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr (hζ₁Q E hE))) hz
    · rintro W ⟨hWirr, hWsub⟩ hle
      have hjW : j '' W ⊆ ⋂ E ∈ J, (E.support : Set S) := by
        rintro x ⟨w, hw, rfl⟩
        simp only [Set.mem_iInter]
        intro E hEJ
        by_cases hEP : E = P
        · subst hEP; rw [← hrange]; exact ⟨w, rfl⟩
        · have hE : E ∈ J.erase P := Finset.mem_erase.mpr ⟨hEP, hEJ⟩
          have := hWsub hw
          simp only [Set.mem_iInter] at this
          exact hQEsub E hE (this _ (Finset.mem_image.mpr ⟨⟨E, hE⟩, Finset.mem_attach _ _, rfl⟩))
      have hZj : Z ⊆ j '' W := by
        intro z hz
        obtain ⟨z₁, rfl⟩ : z ∈ Set.range j := hrange ▸ hZE P hPJ hz
        exact ⟨z₁, hle hz, rfl⟩
      have := hmax.2 ⟨hWirr.image j hjc.continuousOn, hjW⟩ hZj
      intro w hw
      exact this ⟨w, hw, rfl⟩
  obtain ⟨S₂, ι₂, B₂, hF₂, hr⟩ := ih J₁.card hcard F₁ hS₁' J₁ hJ₁ hmax₁ rfl
  refine ⟨S₂, ι₂, B₂, hF₂, ?_⟩
  rw [hr, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp,
    Set.image_preimage_eq_of_subset (hrange ▸ hZE P hPJ)]

/-- A floor stratum of an snc subboundary on the final stratum of a flag is the final stratum
of an extension of the flag. -/
private theorem exists_flag {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S}
    (F : StratumAdjunctionData sX B ι BS) (hS : IsSNCSubboundaryPair (ι ≫ sX) BS)
    {Z : Set S} (hZ : IsSNCStratum (coeffOnePart BS) Z) :
    ∃ (S₁ : Scheme.{0}) (ι₁ : S₁ ⟶ X) (B₁ : QDivisor S₁),
      Nonempty (StratumAdjunctionData sX B ι₁ B₁) ∧ Set.range ι₁.base = ι.base '' Z := by
  obtain ⟨J, hJ, hmax⟩ := hZ
  exact exists_flag_aux _ F hS J hJ hmax rfl

/-- One step of the induction. -/
private theorem crep_step {S S' T : Scheme.{0}} {sS : S ⟶ Spec (.of k)} {g : S' ⟶ S}
    {BS : QDivisor S} {CS' : QDivisor S'} (hS : IsNormalVariety k sS)
    (hCS' : IsSNCSubboundaryPair (g ≫ sS) CS') (hg : IsBirationalMorphism g) [IsProper g]
    (hcrep : Crep sS g BS CS') {j : T ⟶ S} {BT : QDivisor T}
    (hstep : IsAdjunctionStep sS BS j BT) :
    ∃ (P' : MMP.Mori.PrimeDivisor S') (g' : P'.idealSheaf.subscheme ⟶ T),
      CS'.coeff P' = 1 ∧ g' ≫ j = P'.idealSheaf.subschemeι ≫ g ∧ IsBirationalMorphism g' ∧
        IsProper g' ∧
        Crep (j ≫ sS) g' BT ((CS' - Finsupp.single P' 1).restrictPrimeDivisor P') := by
  classical
  -- instances on `S` and `S'`
  haveI : IsIntegral S := hS.1.toIsIntegral
  haveI : IsNormal S := hS.2
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  haveI : CompactSpace S := by
    haveI := hS.1; exact QuasiCompact.compactSpace_of_compactSpace sS
  have hS'v : AlgebraicGeometry.IsVariety k (g ≫ sS) := hCS'.isProjectiveVariety.toIsVariety
  haveI := hS'v
  haveI : IsIntegral S' := hS'v.toIsIntegral
  haveI : Smooth (g ≫ sS) := (isSmoothScheme_iff _).mp hCS'.isSmoothScheme
  haveI : IsNormal S' := isNormal_of_smooth_over_field (g ≫ sS)
  haveI : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sS)
  haveI : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace (g ≫ sS)
  haveI : IsDominant g := hg.isDominant
  have hS'n : IsNormalVariety k (g ≫ sS) := ⟨hS'v, inferInstance⟩
  -- the step on `S`
  obtain ⟨hT, P, hP1, hrange, hci, -⟩ := id hstep
  haveI := hci
  haveI : IsIntegral T := hT.1.toIsIntegral
  haveI : IsNormal T := hT.2
  haveI : LocallyOfFiniteType (j ≫ sS) := hT.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (j ≫ sS)
  haveI : CompactSpace T := by
    haveI := hT.1; exact QuasiCompact.compactSpace_of_compactSpace (j ≫ sS)
  have hjT : j (genericPoint T) = P.genericPoint :=
    map_eq_genericPoint_of_range_eq j P hrange (genericPoint_spec T)
  -- the strict transform `P'` of `P`
  obtain ⟨P', hP'g, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hS hS'n hg P
  -- dimensions
  obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim S = d :=
    ⟨_, topologicalKrullDim_eq_toNat_trdeg sS⟩
  have hd' : topologicalKrullDim S' = d := by
    haveI := hS.1
    rw [← hd]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sS (g ≫ sS) hg).symm
  have htd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hd
  -- `P'` has coefficient one in `C_{S'}`
  have hcoef : CS'.coeff P' = 1 ∧ BS.coeff P = 1 := by
    obtain ⟨τ₀, hτ₀⟩ := exists_ne_zero_form hS hd
    obtain ⟨hq, hgen, hpb⟩ := hcrep d hd τ₀ hτ₀
    have h1 := MMP.Positivity.transformDivisor_of_isPullback hS hS'n hg hq hgen hpb
    have h2 := congrArg (fun D : QDivisor S => D P) h1
    rw [htr] at h2
    have h3 := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso g
      hg.functionFieldMap_bijective htd P' P hP'g τ₀
    have h4 : CS'.coeff P' = BS.coeff P := by
      have e2 : (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sS g τ₀)) + CS')
          P' = (Divisor.toQDivisor (divisorOfForm τ₀) + BS) P := h2
      simp only [Finsupp.add_apply] at e2
      change ((divisorOfForm (pullbackRationalPluriForms sS g τ₀)).coeff P' : ℚ) + CS'.coeff P' =
        ((divisorOfForm τ₀).coeff P : ℚ) + BS.coeff P at e2
      rw [coeff_divisorOfForm, coeff_divisorOfForm, h3] at e2
      linarith
    have h5 := hCS'.coeff_le_one P'
    constructor <;> linarith
  obtain ⟨hcoefP', hcoefP⟩ := hcoef
  -- the step on `S'` to the strict transform
  obtain ⟨hsncT', hstepY, -, -⟩ := snc_step hCS' P' hcoefP'
  have hSet := setting hCS' P' (by rw [hcoefP']; exact one_ne_zero)
  haveI := P'.integral
  haveI := hSet.smoothP
  haveI : IsLocallyNoetherian P'.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (P'.idealSheaf.subschemeι ≫ g ≫ sS)
  haveI : IsNormal P'.idealSheaf.subscheme :=
    isNormal_of_smooth_over_field (P'.idealSheaf.subschemeι ≫ g ≫ sS)
  haveI : CompactSpace P'.idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (P'.idealSheaf.subschemeι ≫ g ≫ sS)
  have hrange'' : Set.range P'.idealSheaf.subschemeι = P'.support := P'.idealSheaf.range_subschemeι
  have hj'T : P'.idealSheaf.subschemeι (genericPoint P'.idealSheaf.subscheme) =
      P'.genericPoint :=
    map_eq_genericPoint_of_range_eq _ P' hrange'' (genericPoint_spec _)
  -- the morphism `g' : P'.idealSheaf.subscheme ⟶ T`
  have hrange' : Set.range (P'.idealSheaf.subschemeι ≫ g).base ⊆ P.support := by
    rintro _ ⟨t, rfl⟩
    have ht : P'.idealSheaf.subschemeι t ∈ P'.support := hrange'' ▸ ⟨t, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at ht
    have hP : P.genericPoint ∈ P.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    have := ((specializes_iff_mem_closure.mpr ht).map g.continuous).mem_closed
      P.idealSheaf.support.isClosed (hP'g ▸ hP)
    exact this
  have hker : j.ker ≤ (P'.idealSheaf.subschemeι ≫ g).ker := by
    have h1 : j.ker ≤ Scheme.IdealSheafData.vanishingIdeal
        ⟨P.support, P.idealSheaf.support.isClosed⟩ := by
      rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
      intro x hx
      change x ∈ (j.ker.support : Set S)
      rw [Scheme.Hom.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq, hrange]
      exact hx
    have h2 : (P'.idealSheaf.subschemeι ≫ g).ker = Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ((P'.idealSheaf.subschemeι ≫ g).base ''
          (⊤ : Closeds P'.idealSheaf.subscheme))) := by
      rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
        ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
    rw [h2]
    refine h1.trans (Scheme.IdealSheafData.vanishingIdeal_antimono ?_)
    change closure _ ⊆ P.support
    refine (P.idealSheaf.support.isClosed.closure_subset_iff).mpr ?_
    rintro _ ⟨t, -, rfl⟩
    exact hrange' ⟨t, rfl⟩
  set g' : P'.idealSheaf.subscheme ⟶ T :=
    IsClosedImmersion.lift j (P'.idealSheaf.subschemeι ≫ g) hker with hg'def
  have hcomm : g' ≫ j = P'.idealSheaf.subschemeι ≫ g := IsClosedImmersion.lift_fac _ _ _
  -- properness
  haveI : IsProper (P'.idealSheaf.subschemeι ≫ g) := inferInstance
  haveI : IsProper (g' ≫ j) := by rw [hcomm]; infer_instance
  haveI : IsProper g' := IsProper.of_comp g' j
  -- `g'` maps the generic point to the generic point
  have hg'η : g' (genericPoint P'.idealSheaf.subscheme) = genericPoint T := by
    apply j.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply, hj'T, hP'g, hjT]
  -- `g'` is birational: it is an isomorphism at the generic point
  set η' := genericPoint P'.idealSheaf.subscheme with hη'
  haveI : IsIso (g.stalkMap (P'.idealSheaf.subschemeι η')) := by rw [hj'T]; exact hiso
  have hsurj : Function.Surjective (g'.stalkMap η').hom := by
    intro y
    obtain ⟨a, rfl⟩ := P'.idealSheaf.subschemeι.stalkMap_surjective η' y
    obtain ⟨b, rfl⟩ :=
      (ConcreteCategory.bijective_of_isIso (g.stalkMap (P'.idealSheaf.subschemeι η'))).2 a
    have e2 := Scheme.Hom.stalkMap_congr_hom (P'.idealSheaf.subschemeι ≫ g) (g' ≫ j) hcomm.symm η'
    have e3 := congrArg (fun φ => φ.hom b) e2
    simp only [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, RingHom.comp_apply] at e3
    exact ⟨_, e3.symm⟩
  have hinj : Function.Injective (g'.stalkMap η').hom := by
    have hfield : IsField (T.presheaf.stalk (g' η')) := by
      have e := (T.presheaf.stalkCongr (Inseparable.of_eq hg'η)).commRingCatIsoToRingEquiv
      exact MulEquiv.isField (Field.toIsField T.functionField) e.toMulEquiv
    letI := hfield.toField
    exact RingHom.injective _
  haveI : IsIso (g'.stalkMap η') :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  haveI : LocallyOfFiniteType (P'.idealSheaf.subschemeι ≫ g) :=
    LocallyOfFiniteType.of_comp (g := sS) (by rw [Category.assoc]; infer_instance)
  haveI : LocallyOfFiniteType (g' ≫ j) := by rw [hcomm]; infer_instance
  haveI : LocallyOfFiniteType g' := LocallyOfFiniteType.of_comp (g := j) inferInstance
  obtain ⟨U, hU, hUo⟩ := AlgebraicGeometry.exists_isOpenImmersion_res_of_isIso_stalkMap g' η'
    (by rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _) inferInstance
  have hg'bir : IsBirationalMorphism g' :=
    MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' g' U ⟨η', hU⟩
  haveI : IsDominant g' := hg'bir.isDominant
  refine ⟨P', g', hcoefP', hcomm, hg'bir, inferInstance, ?_⟩
  -- the dimension of `T`
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim T = e :=
    ⟨_, topologicalKrullDim_eq_toNat_trdeg (j ≫ sS)⟩
  have hde : d = e + 1 := by
    have h1 := MMP.Fourfold.trdeg_add_one_of_eq_genericPoint (sY := sS) (j := j) P hjT
    have h2 := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := j ≫ sS) he
    omega
  subst hde
  have he' : topologicalKrullDim P'.idealSheaf.subscheme = e := by
    haveI := hT.1
    haveI : AlgebraicGeometry.IsVariety k (g' ≫ j ≫ sS) := by
      rw [← Category.assoc, hcomm, Category.assoc]; exact hsncT'.isProjectiveVariety.toIsVariety
    rw [← he]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (j ≫ sS)
      (g' ≫ j ≫ sS) hg'bir).symm
  intro _ _ _ _ _ _ _ _ _ _ _ e₁ he₁ σ hσ
  have hee : e₁ = e := by rw [he] at he₁; exact_mod_cast he₁.symm
  subst e₁
  by_cases he0 : e = 0
  · -- dimension zero: there are no prime divisors
    subst he0
    have hT0 := isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero he
    have hT'0 := isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero he'
    have hsub : ∀ {Z : Scheme.{0}}, IsEmpty (MMP.Mori.PrimeDivisor Z) →
        ∀ D D' : QDivisor Z, D = D' := fun hZ _ _ => Finsupp.ext hZ.elim
    have hq : (Divisor.toQDivisor (divisorOfForm σ) + BT).IsQCartier := by
      rw [hsub hT0 (Divisor.toQDivisor (divisorOfForm σ) + BT) 0]
      exact ⟨1, one_ne_zero, 0, by simp, Divisor.isCartier_zero⟩
    have hgen := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g'
      (Divisor.toQDivisor (divisorOfForm σ) + BT)
    refine ⟨hq, hgen, ?_⟩
    have := QDivisor.isPullback_pullback hq hgen
    rwa [hsub hT'0 (QDivisor.pullback _ hq hgen) _] at this
  · -- positive dimension
    obtain ⟨Q⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq he he0
    have hdS : topologicalKrullDim S = (e + 1 : ℕ) := hd
    obtain ⟨σ₁, hσ₁0, hσ₁P, -, ρ₁, hρ₁, hρ₁0, -⟩ :=
      MMP.Fourfold.exists_form_of_residue_order sS hS (by rw [hdS]; push_cast; rfl) j hT P hrange Q
    -- `σ = c ρ₁` for a unit `c` of `k(T)`
    letI := functionFieldAlgebra (j ≫ sS)
    obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hT he
    set B1 := ZTensorPower.basis b 1
    have hρ₁r : B1.repr ρ₁ () ≠ 0 := by
      intro h0; apply hρ₁0
      have : B1.repr ρ₁ = 0 := Finsupp.ext fun u => by cases u; simpa using h0
      exact B1.repr.map_eq_zero_iff.mp this
    set c : T.functionField := B1.repr σ () / B1.repr ρ₁ ()
    have hσc : σ = c • ρ₁ := by
      have h1 : B1.repr (c • ρ₁) = c • B1.repr ρ₁ := B1.repr.map_smul c ρ₁
      apply B1.repr.injective
      refine Finsupp.ext fun u => ?_
      cases u
      rw [h1, Finsupp.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hρ₁r]
    have hc0 : c ≠ 0 := by
      intro h0; apply hσ; rw [hσc, h0, zero_smul]
    -- lift `c` to a unit `u` of the local ring of `S` along `P`
    obtain ⟨u, hu⟩ := j.stalkMap_surjective (genericPoint T) c
    letI := functionFieldAlgebra sS
    have huK : algebraMap _ S.functionField u ≠ 0 := by
      intro h0
      have : u = 0 := (IsFractionRing.injective _ S.functionField) (by rw [h0, map_zero])
      apply hc0
      rw [← hu, this, map_zero]
    set τ := algebraMap _ S.functionField u • σ₁ with hτdef
    have hτ0 : τ ≠ 0 := smul_ne_zero huK hσ₁0
    have htd1 := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hdS
    have huU : IsUnit u := by
      refine isUnit_of_map_unit (j.stalkMap (genericPoint T)).hom u ?_
      rw [hu]; exact hc0.isUnit
    have huP : S.ord (algebraMap _ S.functionField u) P.genericPoint = 0 := by
      have key : ∀ (x : S) (hx : x = P.genericPoint) (v : S.presheaf.stalk x), IsUnit v →
          S.ord (algebraMap _ S.functionField v) P.genericPoint = 0 := by
        rintro x rfl v hv
        exact P.ord_algebraMap_of_isUnit hv
      exact key _ hjT u huU
    have hτP : P.ordForm τ = -1 := by
      rw [hτdef, P.ordForm_smul (sX := sS) htd1 huK hσ₁0, huP, hσ₁P, zero_add]
    have hρ : IsPoincareResidue sS j e 1 τ σ := by
      have := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ₁ u
      rwa [hu, ← hσc] at this
    -- adjunction on `S`
    obtain ⟨hq, hgen, hpbg⟩ := hcrep (e + 1) hdS τ hτ0
    obtain ⟨hgX, hpbX⟩ := hstep.isPullback_divisorOfForm_add_of_isPoincareResidue
      (by exact_mod_cast hdS) P hrange τ hτ0 hτP σ hρ hq
    -- adjunction on `S'`
    have hρ' := MMP.Fourfold.IsPoincareResidue.pullback (by exact_mod_cast hdS) P hjT hρ g
      P'.idealSheaf.subschemeι g' hcomm
    have hτ'0 : pullbackRationalPluriForms sS g τ ≠ 0 :=
      MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' g
        hg.functionFieldMap_bijective htd1 hτ0
    have hτ'P : P'.ordForm (pullbackRationalPluriForms sS g τ) = -1 := by
      rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso g
        hg.functionFieldMap_bijective htd1 P' P hP'g τ, hτP]
    have hqY : (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sS g τ)) +
        CS').IsQCartier := isQCartier_of_isSmoothScheme hCS'.isSmoothScheme _
    have hdS' : topologicalKrullDim S' = (e + 1 : ℕ) := hd'
    obtain ⟨hgY, hpbY⟩ := hstepY.isPullback_divisorOfForm_add_of_isPoincareResidue
      (by exact_mod_cast hdS') P' hrange'' _ hτ'0 hτ'P _ hρ' hqY
    rw [divisorOfForm_cast (by rw [← Category.assoc, hcomm, Category.assoc])] at hpbY
    -- compose and compare
    have hq' := hpbX.isQCartier hq
    have hgen' := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g'
      (Divisor.toQDivisor (divisorOfForm σ) + BT)
    have hM' : ∀ C : irreducibleComponents P'.idealSheaf.subscheme,
        (P'.idealSheaf.subschemeι ≫ g) (componentGenericPoint _ C) ∉
          (Divisor.toQDivisor (divisorOfForm τ) + BS).supp := by
      intro C hC
      have hCη : componentGenericPoint _ C = genericPoint P'.idealSheaf.subscheme := by
        have h1 := isGenericPoint_componentGenericPoint _ C
        have h2 : (C : Set P'.idealSheaf.subscheme) = Set.univ :=
          Set.eq_univ_of_univ_subset (C.2.2 (IrreducibleSpace.isIrreducible_univ _)
            (Set.subset_univ _))
        rw [h2] at h1
        exact h1.eq (genericPoint_spec _)
      rw [Scheme.Hom.comp_apply, hCη, hj'T, hP'g] at hC
      obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp hC
      obtain rfl : P = E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (E.eq_genericPoint_of_mem_support hmem P.coheight_genericPoint)
      apply hE
      rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτP,
        hcoefP]
      norm_num
    have h1 := qIsPullback_comp hcomm hpbX (QDivisor.isPullback_pullback hq' hgen') hM'
    have h2 := qIsPullback_comp rfl hpbg hpbY hM'
    have hu' := (hq.existsUnique_isPullback hM').unique h1 h2
    refine ⟨hq', hgen', ?_⟩
    rw [← hu']
    exact QDivisor.isPullback_pullback hq' hgen'

/-- The lift of a flag of `(X, B)` to a flag of `(Y, C)`. -/
private theorem lift_flag {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {B : QDivisor X} {C : QDivisor Y}
    {h : Y ⟶ X} (hB : IsSNCSubboundaryPair sX B) (hC : IsSNCSubboundaryPair sY C)
    (hh : h ≫ sX = sY) (hproj : IsProjectiveMorphism h) (hbir : IsBirationalMorphism h)
    (hbase : Crep sX h B C)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    ∃ (S' : Scheme.{0}) (ι' : S' ⟶ Y) (CS' : QDivisor S')
      (_ : StratumAdjunctionData sY C ι' CS') (g : S' ⟶ S),
      g ≫ ι = ι' ≫ h ∧ IsBirationalMorphism g ∧ IsProper g ∧
        IsSNCSubboundaryPair (ι' ≫ sY) CS' ∧
        (∀ W : Set S', IsSNCStratum (coeffOnePart CS') W →
          IsSNCStratum (coeffOnePart C) (ι'.base '' W)) ∧
        Crep (ι ≫ sX) g BS CS' := by
  induction F with
  | refl hp =>
    haveI : IsProper h := isProper_of_isProjectiveMorphism h hproj
    refine ⟨Y, 𝟙 Y, C, .refl (isPair_of_isSNCSubboundaryPair hC), h, by simp, hbir,
      inferInstance, by rwa [Category.id_comp], fun W hW => by simpa using hW, ?_⟩
    rw [Category.id_comp]
    exact hbase
  | @step S T ι BS F j BT hstep ih =>
    obtain ⟨S', ι', CS', F', g, hcomm, hgbir, hgprop, hCS', hstr, hcr⟩ := ih
    have he : g ≫ ι ≫ sX = ι' ≫ sY := by rw [← Category.assoc, hcomm, Category.assoc, hh]
    have hCS'' : IsSNCSubboundaryPair (g ≫ ι ≫ sX) CS' := he ▸ hCS'
    obtain ⟨P', g', hP'1, hcomm', hg'bir, hg'prop, hcr'⟩ :=
      crep_step F.isNormalVariety hCS'' hgbir hcr hstep
    obtain ⟨hsnc', hstep', -, -⟩ := snc_step hCS' P' hP'1
    refine ⟨_, P'.idealSheaf.subschemeι ≫ ι', _, F'.step _ _ hstep', g', ?_, hg'bir, hg'prop,
      by rwa [Category.assoc], fun W hW => ?_, by rw [Category.assoc]; exact hcr'⟩
    · rw [← Category.assoc, hcomm', Category.assoc, hcomm, Category.assoc]
    · have := hstr _ (isSNCStratum_image hCS' P' hP'1 hW)
      simpa [Set.image_image] using this

end MMP.CrepantSncStratumBirationalLift

namespace MMP.Fourfold

open MMP.Mori MMP.Flips MMP.CrepantSncStratumBirationalLift

/-- **A floor stratum lifts birationally and crepantly along a crepant morphism of snc
subboundary pairs.** Let `(X, B)` and `(Y, C)` be smooth projective varieties over an
algebraically closed field `k` of characteristic zero with snc subboundaries
(`MMP.Fourfold.IsSNCSubboundaryPair`), and `h : Y ⟶ X` a projective birational morphism over `k`
with `K_Y + C = h^*(K_X + B)`, i.e. `C` is the crepant boundary of `(X, B)` on `Y`
(`MMP.Mori.IsCrepantBoundary`). Let `Z ⊆ X` be a floor stratum, an snc stratum of `B^{=1}`
(`MMP.Fourfold.IsSNCStratum`, `MMP.Fourfold.coeffOnePart`). Then `Z` is the final stratum of a
flag of iterated adjunction of `(X, B)` (`MMP.Fourfold.StratumAdjunctionData`), and for every
such flag, with adjunction pair `(S, B_S)` and inclusion `ι : S ⟶ X`, there are a flag of
iterated adjunction of `(Y, C)` with adjunction pair `(S', C_{S'})` and inclusion `ι' : S' ⟶ Y`
whose image is a floor stratum of `(Y, C)`, and a birational morphism `g : S' ⟶ S` with
`g ≫ ι = ι' ≫ h` such that `K_{S'} + C_{S'} = g^*(K_S + B_S)` for suitable canonical divisors of
`S` and `S'`. -/
@[mmp "lem_fourfold_crepant_snc_stratum_birational_lift"]
public theorem IsSNCSubboundaryPair.exists_stratumAdjunctionData_isBirationalMorphism
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {B : QDivisor X} {C : QDivisor Y}
    {h : Y ⟶ X} {n : ℕ} {KX : Divisor X}
    (hB : IsSNCSubboundaryPair sX B) (hC : IsSNCSubboundaryPair sY C) (hh : h ≫ sX = sY)
    (hproj : IsProjectiveMorphism h) (hbir : IsBirationalMorphism h)
    (hKX : KX.IsCanonicalDivisor sX n)
    (hcrep : ∃ hY : IsNormalVariety k (h ≫ sX), IsCrepantBoundary sX n KX B h hY hbir C)
    {Z : Set X} (hZ : IsSNCStratum (coeffOnePart B) Z) :
    (∃ (S : Scheme.{0}) (ι : S ⟶ X) (BS : QDivisor S),
        Nonempty (StratumAdjunctionData sX B ι BS) ∧ Set.range ι.base = Z) ∧
      ∀ {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS),
        Set.range ι.base = Z →
        ∃ (S' : Scheme.{0}) (ι' : S' ⟶ Y) (CS' : QDivisor S')
          (F' : StratumAdjunctionData sY C ι' CS') (g : S' ⟶ S),
          IsSNCStratum (coeffOnePart C) (Set.range ι'.base) ∧ g ≫ ι = ι' ≫ h ∧
            IsBirationalMorphism g ∧
            haveI := F.isLocallyNoetherian_stratum
            haveI := F.isNormal_stratum
            haveI := F'.isIntegral_stratum
            haveI := F'.isLocallyNoetherian_stratum
            haveI := F'.isNormal_stratum
            ∃ (d : ℕ) (KS : Divisor S) (KS' : Divisor S'),
              KS.IsCanonicalDivisor (ι ≫ sX) d ∧ KS'.IsCanonicalDivisor (ι' ≫ sY) d ∧
              ∃ hgen : ∀ W : irreducibleComponents S',
                  g (componentGenericPoint S' W) ∉ (Divisor.toQDivisor KS + BS).supp,
                (Divisor.toQDivisor KS + BS).IsPullback g hgen (Divisor.toQDivisor KS' + CS') := by
  refine ⟨?_, fun {S ι BS} F hZS => ?_⟩
  · obtain ⟨S₁, ι₁, B₁, hF, hr⟩ :=
      exists_flag (StratumAdjunctionData.refl (isPair_of_isSNCSubboundaryPair hB))
        (by rwa [Category.id_comp]) hZ
    exact ⟨S₁, ι₁, B₁, hF, by rw [hr]; simp⟩
  · obtain ⟨S', ι', CS', F', g, hcomm, hgbir, -, -, hstr, hcr⟩ :=
      lift_flag hB hC hh hproj hbir (crep_base hB hbir hKX hcrep) F
    refine ⟨S', ι', CS', F', g, ?_, hcomm, hgbir, ?_⟩
    · haveI := F'.isIntegral_stratum
      have h1 := hstr Set.univ (isSNCStratum_univ _)
      rwa [Set.image_univ] at h1
    · haveI := F.isIntegral_stratum
      haveI := F.isLocallyNoetherian_stratum
      haveI := F.isNormal_stratum
      haveI := F'.isIntegral_stratum
      haveI := F'.isLocallyNoetherian_stratum
      haveI := F'.isNormal_stratum
      have hSv := F.isNormalVariety
      have he : g ≫ ι ≫ sX = ι' ≫ sY := by rw [← Category.assoc, hcomm, Category.assoc, hh]
      have hS'v : IsNormalVariety k (g ≫ ι ≫ sX) := he ▸ F'.isNormalVariety
      haveI : LocallyOfFiniteType (ι ≫ sX) := hSv.1.toLocallyOfFiniteType
      haveI : LocallyOfFiniteType (g ≫ ι ≫ sX) := hS'v.1.toLocallyOfFiniteType
      haveI : CompactSpace S := by
        haveI := hSv.1
        exact QuasiCompact.compactSpace_of_compactSpace (ι ≫ sX)
      haveI : CompactSpace S' := by
        haveI := hS'v.1
        exact QuasiCompact.compactSpace_of_compactSpace (g ≫ ι ≫ sX)
      haveI : IsDominant g := hgbir.isDominant
      obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim S = d :=
        ⟨_, topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX)⟩
      have hd' : topologicalKrullDim S' = d := by
        haveI := hSv.1
        haveI := hS'v.1
        rw [← hd]
        exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ι ≫ sX)
          (g ≫ ι ≫ sX) hgbir).symm
      obtain ⟨τ, hτ⟩ := exists_ne_zero_form hSv hd
      obtain ⟨-, hgen, hpb⟩ := hcr d hd τ hτ
      have hτ' : pullbackRationalPluriForms (ι ≫ sX) g τ ≠ 0 :=
        MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' g
          hgbir.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hd)
          hτ
      have hK' := isCanonicalDivisor_divisorOfForm' hS'v hd' hτ'
      refine ⟨d, divisorOfForm τ, divisorOfForm (pullbackRationalPluriForms (ι ≫ sX) g τ),
        isCanonicalDivisor_divisorOfForm' hSv hd hτ, ?_, hgen, hpb⟩
      generalize divisorOfForm (pullbackRationalPluriForms (ι ≫ sX) g τ) = D at hK' ⊢
      rw [he] at hK'
      exact hK'

end MMP.Fourfold
