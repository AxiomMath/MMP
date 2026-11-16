module
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift

/-!
# Effectivity of the residue different at a codimension-one point

Let `X` be a normal variety of dimension `n + 1` over a field `k` of characteristic zero, `S ⊂ X` a
normal prime divisor and `B ≥ 0` a `ℚ`-divisor not containing `S`, such that `D = K_X + S + B` is
`ℚ`-Cartier. Fix `K_X = div(τ)` for a rational top form `τ` with a simple pole along `S`, and
`K_S = div(ρ)` for its Poincaré residue `ρ`. If `B_S` is the `ℚ`-divisor on `S` with
`K_S + B_S = D|_S`, then the coefficient of `B_S` at every codimension-one point of `S` is
nonnegative.

## Main results

* `MMP.Fourfold.coeff_nonneg_of_isPullback_divisorOfForm_isPoincareResidue_of_charZero`: the
  coefficients of `B_S` are nonnegative, over a field of characteristic zero.
* `MMP.Fourfold.coeff_nonneg_of_isPullback_divisorOfForm_isPoincareResidue`: the same over `ℂ`.

## Implementation notes

Restriction of the `ℚ`-Cartier divisor `D` to `S` is its pull-back along the closed immersion
`S ⟶ X` (`MMP.Mori.QDivisor.IsPullback`): for every `m > 0` with `mD` Cartier, `m(K_S + B_S)` is
the Cartier restriction of `mD`. A codimension-one point of `S` is a prime divisor of `S`.

The coefficient of `B_S` at `Q` is checked through `x = j(η_Q)` and a local equation `φ` of a
Cartier multiple `mD` near `x`. By the surjectivity of the residue `ω_X(P)_x → ω_{T,Q}`
(`MMP.Fourfold.exists_isPoincareResidue_of_le_ordForm_of_charZero`), a local generator of `ω_{T,Q}`
is the residue of a form `b τ` with `b` a unit along `P`, `b τ` without pole through `x` off `P`,
and `b̄ ρ` without zero at `Q`. Since `B ≥ 0`, `b^m φ` is regular at `x` (algebraic Hartogs), and
restricting it to `T` gives `m · coeff_Q(D|_T) ≥ m · ord_Q ρ`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 16
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

universe u

/-- An irreducible space has a single irreducible component. -/
private theorem subsingleton_irreducibleComponents (X : Scheme.{u}) [IrreducibleSpace X]
    (Z Z' : irreducibleComponents X) : Z = Z' := by
  have h := Z.2
  have h' := Z'.2
  simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h h'
  exact Subtype.ext (h.trans h'.symm)

/-- On an integral scheme, the order `v_Q` of a unit of the factor `K(X)` is the order of
vanishing of its image in the function field. -/
private theorem ordUnit_eq_ord {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (Q : Mori.PrimeDivisor X) (v : (X.presheaf.stalk (componentGenericPoint X Q.component))ˣ) :
    Q.ordUnit v = X.ord ((MMP.Positivity.componentToFunctionField Q.component).hom v.val)
      Q.genericPoint := by
  classical
  let φ : (RationalFunctions X)ˣ :=
    (RationalFunctions.unitsEquiv X).symm (Pi.mulSingle Q.component v)
  have hφ : Units.map (RationalFunctions.component X Q.component).toMonoidHom φ = v := by
    ext
    change ((RationalFunctions.unitsEquiv X φ) Q.component).val = v.val
    simp [φ]
  have := MMP.Positivity.ord_eq_ord_componentToFunctionField Q φ
  rw [PrimeDivisor.ord_eq_ordUnit, hφ] at this
  rw [this]
  congr 2
  exact congrArg Units.val hφ

/-- Generization to the generic point commutes with generization between stalks. -/
theorem algebraMap_stalkSpecializes' (X : Scheme.{u}) [IsIntegral X] {x x' : X} (h : x ⤳ x')
    (z : X.presheaf.stalk x') :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.stalkSpecializes h z) =
      algebraMap (X.presheaf.stalk x') X.functionField z := by
  change (X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes _).hom z = _
  rw [TopCat.Presheaf.stalkSpecializes_comp]
  rfl

/-- Generization from a stalk to a component, then to the function field, is generization to the
function field. -/
private theorem componentToFunctionField_stalkSpecializes (X : Scheme.{u}) [IsIntegral X]
    (Z : irreducibleComponents X) {x : X} (h : componentGenericPoint X Z ⤳ x)
    (z : X.presheaf.stalk x) :
    (MMP.Positivity.componentToFunctionField Z).hom (X.presheaf.stalkSpecializes h z) =
      algebraMap (X.presheaf.stalk x) X.functionField z := by
  change (X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes _).hom z = _
  rw [TopCat.Presheaf.stalkSpecializes_comp]
  rfl

/-- On an irreducible scheme the generic point of every component is the generic point. -/
private theorem componentGenericPoint_eq_genericPoint (T : Scheme.{u}) [IrreducibleSpace T]
    (Z : irreducibleComponents T) : componentGenericPoint T Z = genericPoint T :=
  (isGenericPoint_componentGenericPoint T Z).eq (by
    have h := Z.2
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h
    exact h ▸ genericPoint_spec T)

/-- A closed immersion of an irreducible scheme onto the support of a prime divisor maps the
generic point to the generic point of the divisor. -/
private theorem map_genericPoint_eq {X T : Scheme.{u}} (j : T ⟶ X) [IsClosedImmersion j]
    [IrreducibleSpace T] (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X)) :
    j (genericPoint T) = P.genericPoint := by
  have h1 : IsGenericPoint (j (genericPoint T)) (P.support : Set X) := by
    have := (genericPoint_spec T).image j.base.hom.continuous
    rwa [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq, hP] at this
  have h2 : IsGenericPoint P.genericPoint (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isGenericPoint_closure
  exact h1.eq h2

/-- An element of the local ring at a prime divisor has nonnegative order. -/
private theorem ord_algebraMap_nonneg {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (P : Mori.PrimeDivisor Y) (a : Y.presheaf.stalk P.genericPoint) :
    0 ≤ Y.ord (algebraMap _ Y.functionField a) P.genericPoint := by
  by_cases ha : algebraMap _ Y.functionField a = 0
  · rw [ha, Scheme.ord_zero]
    rfl
  have h := (P.divisorialValuation_le_one_iff _).mpr ⟨a, rfl⟩
  rw [P.divisorialValuation_eq_exp_neg_ord ha, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

/-- `ord 1 = 0`. -/
theorem ord_one' {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y) :
    Y.ord (1 : Y.functionField) z = 0 := by
  have := Scheme.ord_mul (x := z) (one_ne_zero (α := Y.functionField)) one_ne_zero
  rw [mul_one] at this
  omega

/-- `ord (f ^ k) = k ord f`. -/
theorem ord_pow' {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {f : Y.functionField} (hf : f ≠ 0) (k : ℕ) (z : Y) : Y.ord (f ^ k) z = k * Y.ord f z := by
  induction k with
  | zero => simp [ord_one']
  | succ k ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ hf) hf, ih]
    push_cast
    ring

/-- A unit of the local ring at a prime divisor has order zero. -/
private theorem ord_algebraMap_eq_zero_of_isUnit {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (P : Mori.PrimeDivisor Y) {x : Y} (hx : x = P.genericPoint)
    {b : Y.presheaf.stalk x} (hb : IsUnit b) :
    Y.ord (algebraMap _ Y.functionField b) P.genericPoint = 0 := by
  subst hx
  exact P.ord_algebraMap_of_isUnit hb

/-! ### Poincaré residues along a prime divisor -/

section ResidueAlongPrimeDivisor

variable {k : Type u} [Field k] {Y T : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsIntegral T] {j : T ⟶ Y}

/-- The residue of `b τ`, for `b` in the local ring at the generic point of `T`, is `b̄ Res τ`. -/
private theorem IsPoincareResidue.algebraMap_smul {n m : ℕ} {τ : RationalPluriForms sY (n + 1) m}
    {ρ : RationalPluriForms (j ≫ sY) n m} (h : IsPoincareResidue sY j n m τ ρ)
    (b : Y.presheaf.stalk (j (genericPoint T))) :
    IsPoincareResidue sY j n m (algebraMap _ Y.functionField b • τ)
      ((j.stalkMap (genericPoint T)).hom b • ρ) := by
  obtain ⟨t, g, x, ht, hτ, hρ⟩ := h
  refine ⟨t, b * g, x, ht, ?_, ?_⟩
  · subst hτ
    rw [map_mul, mul_smul]
    rfl
  · subst hρ
    rw [map_mul, mul_smul]
    rfl

end ResidueAlongPrimeDivisor

/-- A nonzero rational function of order `≥ 0` along a prime divisor `P` comes from the stalk at
the generic point of `P`. -/
theorem exists_algebraMap_eq_of_ord_nonneg {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y) {f : Y.functionField}
    (hf : f ≠ 0) (h : 0 ≤ Y.ord f P.genericPoint) :
    ∃ a : Y.presheaf.stalk P.genericPoint, algebraMap _ Y.functionField a = f := by
  have h1 : P.divisorialValuation f ≤ 1 := by
    rw [P.divisorialValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  exact (P.divisorialValuation_le_one_iff f).mp h1

/-- The algebra map from the stalk at the generic point to the function field is the identity. -/
private theorem algebraMap_stalk_genericPoint (T : Scheme.{u}) [IsIntegral T]
    (z : T.presheaf.stalk (genericPoint T)) :
    @algebraMap (T.presheaf.stalk (genericPoint T)) T.functionField _ _
      (stalkFunctionFieldAlgebra T (genericPoint T)) z = z := by
  change (T.presheaf.stalkSpecializes _).hom z = z
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- Along a prime divisor of an integral normal scheme there is a rational function of order
one. -/
private theorem exists_ord_eq_one {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (P : Mori.PrimeDivisor Y) :
    ∃ f : Y.functionField, f ≠ 0 ∧ Y.ord f P.genericPoint = 1 := by
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
  have hne : algebraMap P.localRing Y.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  refine ⟨_, hne, ?_⟩
  rw [Scheme.ord_eq_iff P.coheight_genericPoint hne]
  exact Ring.ordFrac_irreducible (R := Y.presheaf.stalk P.genericPoint) hϖ

/-- Along a prime divisor of an integral normal scheme every integer is the order of a nonzero
rational function. -/
private theorem exists_ord_eq {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (P : Mori.PrimeDivisor Y) (k : ℤ) :
    ∃ g : Y.functionField, g ≠ 0 ∧ Y.ord g P.genericPoint = k := by
  obtain ⟨f, hf0, hf⟩ := exists_ord_eq_one P
  have hinv : Y.ord f⁻¹ P.genericPoint = -1 := by
    have := Scheme.ord_mul (x := P.genericPoint) hf0 (inv_ne_zero hf0)
    rw [mul_inv_cancel₀ hf0, ord_one', hf] at this
    omega
  refine ⟨f ^ k.toNat * f⁻¹ ^ (-k).toNat,
    mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ (inv_ne_zero hf0)), ?_⟩
  rw [Scheme.ord_mul (pow_ne_zero _ hf0) (pow_ne_zero _ (inv_ne_zero hf0)), ord_pow' hf0,
    ord_pow' (inv_ne_zero hf0), hf, hinv]
  omega

/-- If `K(Y)` has transcendence degree `d` over a field `k` of characteristic zero, the rational
one-pluriforms of degree `d` form a line over `K(Y)`. -/
theorem finrank_rationalPluriForms_eq_one {k : Type} [Field k] [CharZero k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d) :
    Module.finrank Y.functionField (RationalPluriForms sY d 1) = 1 := by
  let := functionFieldAlgebra sY
  have := essFiniteType_functionField (sX := sY)
  have hK : Module.finrank Y.functionField Ω[Y.functionField⁄k] = d :=
    (finrank_kaehlerDifferential_eq_trdeg k Y.functionField).trans hd
  have : FiniteDimensional Y.functionField Ω[Y.functionField⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k Y.functionField).1
  have h1 : Module.finrank Y.functionField (⋀[Y.functionField]^d Ω[Y.functionField⁄k]) = 1 := by
    rw [exteriorPower.finrank_eq, hK, Nat.choose_self]
  let c₀ := (Module.finBasisOfFinrankEq _ _ h1).reindex (Equiv.ofUnique (Fin 1) Unit)
  let bb : Module.Basis Unit Y.functionField (RationalPluriForms sY d 1) :=
    ZTensorPower.basis c₀ 1
  rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]

/-- Along a prime divisor `Q` of a normal integral scheme of finite type over a field of
characteristic zero, there is a nonzero rational top form of order zero. -/
theorem exists_ne_zero_ordForm_eq_zero {k : Type} [Field k] [CharZero k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [LocallyOfFiniteType sY] {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d)
    (Q : Mori.PrimeDivisor Y) :
    ∃ ρ : RationalPluriForms sY d 1, ρ ≠ 0 ∧ Q.ordForm ρ = 0 := by
  let := functionFieldAlgebra sY
  have : Nontrivial (RationalPluriForms sY d 1) :=
    Module.nontrivial_of_finrank_pos (R := Y.functionField)
      (by simp [finrank_rationalPluriForms_eq_one sY hd])
  obtain ⟨ρ₀, hρ₀⟩ := exists_ne (0 : RationalPluriForms sY d 1)
  obtain ⟨g, hg0, hg⟩ := exists_ord_eq Q (-Q.ordForm ρ₀)
  refine ⟨g • ρ₀, smul_ne_zero hg0 hρ₀, ?_⟩
  rw [Q.ordForm_smul (sX := sY) hd hg0 hρ₀, hg]
  ring

/-- **The residue lift at a codimension-one point.** For `Q` a prime divisor of `T`, there is a
`b` in the local ring along `P`, a unit there, such that `b τ` has no pole along any other prime
divisor through `j(η_Q)` and its residue `b̄ ρ` has no zero at `Q`. -/
private theorem exists_residue_lift
    {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (Q : Mori.PrimeDivisor T) :
    ∃ b : X.presheaf.stalk (j (componentGenericPoint T Q.component)), IsUnit b ∧
      (∀ E : Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support → E ≠ P →
        0 ≤ X.ord (algebraMap _ X.functionField b) E.genericPoint + E.ordForm τ) ∧
      T.ord ((MMP.Positivity.componentToFunctionField Q.component).hom
        ((j.stalkMap (componentGenericPoint T Q.component)).hom b)) Q.genericPoint +
        Q.ordForm ρ ≤ 0 := by
  classical
  have : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  have hjT := map_genericPoint_eq j P hP
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (j ≫ sX)
  have hd : (Algebra.trdeg k X.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hdT : (Algebra.trdeg k T.functionField).toNat = n := by
    have := trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    omega
  obtain ⟨ρ₁, hρ₁0, hρ₁Q⟩ := exists_ne_zero_ordForm_eq_zero (j ≫ sX) hdT Q
  obtain ⟨σ, hσP, hσE, hσres⟩ :=
    exists_isPoincareResidue_of_le_ordForm_of_charZero sX hX hdim j hT P hP Q ρ₁ hρ₁Q.ge
  obtain ⟨f, hf⟩ :=
    (finrank_eq_one_iff_of_nonzero' τ hτ0).mp (finrank_rationalPluriForms_eq_one sX hd) σ
  have hspP : j (genericPoint T) ⤳ P.genericPoint := specializes_of_eq hjT
  obtain ⟨a, haf⟩ : ∃ a : X.presheaf.stalk P.genericPoint,
      algebraMap _ X.functionField a = f := by
    by_cases hf0 : f = 0
    · exact ⟨0, by rw [map_zero, hf0]⟩
    refine exists_algebraMap_eq_of_ord_nonneg P hf0 ?_
    have := P.ordForm_smul (sX := sX) hd hf0 hτ0
    rw [hf, hτ] at this
    omega
  set b₁ := X.presheaf.stalkSpecializes hspP a with hb₁
  have hb₁f : algebraMap _ X.functionField b₁ = f := by
    rw [hb₁, algebraMap_stalkSpecializes', haf]
  have hres := IsPoincareResidue.algebraMap_smul hρ b₁
  rw [hb₁f, hf] at hres
  have hρσeq := IsPoincareResidue.unique_of_isClosedImmersion (sY := sX) P hjT hσres hres
  obtain ⟨hb0, hρ0⟩ := smul_ne_zero_iff.mp (hρσeq ▸ hρ₁0 :
    (j.stalkMap (genericPoint T)).hom b₁ • ρ ≠ 0)
  have hb₁u : IsUnit b₁ :=
    isUnit_of_map_unit (j.stalkMap (genericPoint T)).hom b₁
      ((isUnit_iff_ne_zero (G₀ := T.functionField)).mpr hb0)
  have hf0 : f ≠ 0 := hb₁f ▸ (hb₁u.map _).ne_zero
  have hcg := componentGenericPoint_eq_genericPoint T Q.component
  have h' : componentGenericPoint T Q.component ⤳ genericPoint T := specializes_of_eq hcg
  refine ⟨X.presheaf.stalkSpecializes (j.base.hom.map_specializes h') b₁, hb₁u.map _,
    fun E hE hEP => ?_, ?_⟩
  · rw [algebraMap_stalkSpecializes', hb₁f, ← E.ordForm_smul (sX := sX) hd hf0 hτ0, hf]
    exact hσE E hE hEP
  · rw [Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ h',
      componentToFunctionField_stalkSpecializes T _ h', algebraMap_stalk_genericPoint T]
    have := Q.ordForm_smul (sX := j ≫ sX) hdT hb0 hρ0
    rw [← hρσeq, hρ₁Q] at this
    exact this.ge

/-- Generization between stalks commutes with the maps to the rational functions. -/
theorem stalkToRationalFunctions_stalkSpecializes (X : Scheme.{u}) [IsIntegral X]
    {Z : irreducibleComponents X} {x x' : X} (hx : x ∈ Z.1) (hx' : x' ∈ Z.1) (h : x ⤳ x')
    (c : X.presheaf.stalk x') :
    (stalkToRationalFunctions X hx).hom (X.presheaf.stalkSpecializes h c) =
      (stalkToRationalFunctions X hx').hom c := by
  change (X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes _).hom c = _
  rw [TopCat.Presheaf.stalkSpecializes_comp]
  rfl

/-- On an integral normal scheme, a unit `b` of the stalk at `x` defines a unit of `K(X)` whose
germ at `x` is `b` and whose order along every prime divisor `E` is `ord_E b`. -/
theorem exists_units_rationalFunctions_of_isUnit (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {x : X} {b : X.presheaf.stalk x} (hb : IsUnit b) :
    ∃ G : (RationalFunctions X)ˣ, (G : RationalFunctions X) (pointComponent x) =
        (stalkToRationalFunctions X (mem_pointComponent x)).hom b ∧
      ∀ E : Mori.PrimeDivisor X,
        E.ord G = X.ord (algebraMap _ X.functionField b) E.genericPoint := by
  have hmemZ : ∀ Z : irreducibleComponents X, x ∈ Z.1 := fun Z => by
    rw [subsingleton_irreducibleComponents X Z (pointComponent x)]
    exact mem_pointComponent _
  refine ⟨(RationalFunctions.unitsEquiv X).symm fun Z =>
    Units.map (stalkToRationalFunctions X (hmemZ Z)).hom.toMonoidHom hb.unit, rfl, fun E => ?_⟩
  rw [MMP.Positivity.ord_eq_ord_componentToFunctionField]
  change X.ord ((MMP.Positivity.componentToFunctionField E.component).hom
    ((stalkToRationalFunctions X (hmemZ E.component)).hom b)) _ = _
  exact congrArg (X.ord · _) (componentToFunctionField_stalkSpecializes X _ _ b)

/-- If `Dm = m (div τ + P + B)` with `B ≥ 0`, `coeff_P B = 0` and `ord_P τ = -1`, then
`m v + coeff_E Dm ≥ 0` for every `v` that vanishes when `E = P` and with `v + ord_E τ ≥ 0`
otherwise. -/
theorem zero_le_nsmul_add_coeff {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [LocallyOfFiniteType sX] {n : ℕ} {P : Mori.PrimeDivisor X} {B : QDivisor X}
    (hB : B.IsEffective) (hBP : B.coeff P = 0)
    {τ : RationalPluriForms sX (n + 1) 1} (hτ : P.ordForm τ = -1) {m : ℕ} {Dm : Divisor X}
    (hDm : Divisor.toQDivisor Dm =
      (m : ℤ) • (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B))
    (E : Mori.PrimeDivisor X) {v : ℤ} (hvP : E = P → v = 0)
    (hvE : E ≠ P → 0 ≤ v + E.ordForm τ) :
    0 ≤ m • v + Dm.coeff E := by
  have hc := congrArg (fun G : QDivisor X => G.coeff E) hDm
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
    coeff_divisorOfForm, zsmul_eq_mul] at hc
  by_cases hEP : E = P
  · subst hEP
    rw [hτ, DivisorWithCoeffs.coeff_single_self, hBP] at hc
    have hD0 : Dm.coeff E = 0 := by
      exact_mod_cast (show (Dm.coeff E : ℚ) = 0 by rw [hc]; push_cast; ring)
    simp [hvP rfl, hD0]
  · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hEP)] at hc
    have h1 : (0 : ℚ) ≤ (v : ℚ) + E.ordForm τ := by exact_mod_cast hvE hEP
    rw [nsmul_eq_mul]
    exact_mod_cast (show (0 : ℚ) ≤ (m : ℚ) * v + Dm.coeff E by
      rw [hc]
      push_cast
      nlinarith [hB E])

/-- If the germ `b^m a` at `j(η_Q)` of two units extends over `j(Q)`, and
`ord_Q b̄ + r ≤ 0`, then `m r ≤ ord_Q ā`. -/
private theorem mul_le_ord_of_stalkSpecializes_eq {X T : Scheme.{u}} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] (j : T ⟶ X) (Q : Mori.PrimeDivisor T)
    {c : X.presheaf.stalk (j Q.genericPoint)}
    {b a : X.presheaf.stalk (j (componentGenericPoint T Q.component))} (hb : IsUnit b)
    (ha : IsUnit a) {m : ℕ} {r : ℤ}
    (hspc : X.presheaf.stalkSpecializes (j.base.hom.map_specializes Q.specializes_genericPoint) c =
      b ^ m * a)
    (hbQ : T.ord ((MMP.Positivity.componentToFunctionField Q.component).hom
      ((j.stalkMap (componentGenericPoint T Q.component)).hom b)) Q.genericPoint + r ≤ 0) :
    (m : ℤ) * r ≤ T.ord ((MMP.Positivity.componentToFunctionField Q.component).hom
      ((j.stalkMap (componentGenericPoint T Q.component)).hom a)) Q.genericPoint := by
  have key := ord_algebraMap_nonneg Q ((j.stalkMap Q.genericPoint).hom c)
  rw [← componentToFunctionField_stalkSpecializes T Q.component Q.specializes_genericPoint,
    ← Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ Q.specializes_genericPoint c, hspc,
    map_mul, map_mul, map_pow, map_pow] at key
  have hb0 : (MMP.Positivity.componentToFunctionField Q.component).hom
      ((j.stalkMap (componentGenericPoint T Q.component)).hom b) ≠ 0 := ((hb.map _).map _).ne_zero
  have ha0 : (MMP.Positivity.componentToFunctionField Q.component).hom
      ((j.stalkMap (componentGenericPoint T Q.component)).hom a) ≠ 0 := ((ha.map _).map _).ne_zero
  rw [Scheme.ord_mul (pow_ne_zero _ hb0) ha0, ord_pow' hb0] at key
  have := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg m) hbQ
  linarith

/-- Effectivity of the different: if `R₀ = D|_T` for `D = div τ + P + B`, then `R₀ - div ρ` is
effective. -/
private theorem isEffective_isPullback_sub_divisorOfForm
    {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (B : QDivisor X) (hB : B.IsEffective) (hBP : B.coeff P = 0)
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (hD : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsQCartier)
    (hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).supp)
    (R₀ : QDivisor T)
    (hR₀ : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsPullback j hgen R₀) :
    (R₀ - Divisor.toQDivisor (divisorOfForm ρ)).IsEffective := by
  classical
  obtain ⟨m, hm, Dm, hDm, hDmc⟩ := hD.exists_pos
  obtain ⟨Dm', hDm', hp⟩ := hR₀ m hm Dm hDm hDmc
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  intro Q
  rw [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor, coeff_divisorOfForm, sub_nonneg]
  have hR₀Q : ((Dm'.coeff Q : ℤ) : ℚ) = (m : ℚ) * R₀.coeff Q := by
    simpa [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor] using
      congrArg (fun G : QDivisor T => G.coeff Q) hDm'
  set η := componentGenericPoint T Q.component with hηdef
  have hsp : j η ⤳ j Q.genericPoint := j.base.hom.map_specializes Q.specializes_genericPoint
  obtain ⟨U, hxU, φ, hφ⟩ := hDmc (j Q.genericPoint)
  have hQU : (Q.support ∩ j ⁻¹ᵁ U).Nonempty := (Q.genericPoint_mem_iff _).mp hxU
  have hjηU : j η ∈ U := hsp.mem_open U.isOpen hxU
  have hm' : ((m : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hgenm : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ Dm.supp :=
    fun Z hZ => hgen Z (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hDm] at hZ)
  rw [hp U φ hφ Q hQU] at hR₀Q
  set W := pointComponent (j η)
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hjηU (hgenm Q.component) (mem_pointComponent _)
  rw [pullbackComponent_eq _ hφ _ (mem_pointComponent _) a ha, ordUnit_eq_ord] at hR₀Q
  obtain ⟨b, hb, hbE, hbQ⟩ := exists_residue_lift sX hX hdim j hT P hP τ hτ0 hτ ρ hρ Q
  obtain ⟨Gu, hGW, hGord⟩ := exists_units_rationalFunctions_of_isUnit X (x := j η) hb
  have hxW : j Q.genericPoint ∈ W.1 :=
    hsp.mem_closed (isClosed_of_mem_irreducibleComponents _ W.2) (mem_pointComponent _)
  have hψ : ∀ E : Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support → 0 ≤ E.ord (Gu ^ m * φ) := by
    intro E hE
    rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_pow, hGord, ← hφ E ⟨_, hE, hxU⟩]
    refine zero_le_nsmul_add_coeff hB hBP hτ hDm E (fun hEP => ?_) (hbE E hE)
    subst hEP
    exact ord_algebraMap_eq_zero_of_isUnit E (by
      rw [hηdef, componentGenericPoint_eq_genericPoint]
      exact map_genericPoint_eq j E hP) hb
  obtain ⟨c, hc⟩ := exists_stalk_eq_of_forall_zero_le_ord hxW (Gu ^ m * φ) hψ
  have hspc : X.presheaf.stalkSpecializes hsp c = b ^ m * a.val := by
    apply stalkToRationalFunctions_injective (mem_pointComponent (j η))
    rw [map_mul, map_pow, ← hGW, ha,
      stalkToRationalFunctions_stalkSpecializes X (mem_pointComponent (j η)) hxW hsp, hc,
      Units.val_mul, Units.val_pow_eq_pow_val, Pi.mul_apply, Pi.pow_apply]
  rw [Units.coe_map] at hR₀Q
  change ((T.ord ((MMP.Positivity.componentToFunctionField Q.component).hom
      ((j.stalkMap η).hom a.val)) Q.genericPoint : ℤ) : ℚ) = _ at hR₀Q
  refine le_of_mul_le_mul_left ?_ hmQ
  rw [← hR₀Q]
  exact_mod_cast mul_le_ord_of_stalkSpecializes_eq j Q hb a.isUnit hspc hbQ

/-- **Effectivity of the residue different at a codimension-one point**, over a field `k` of
characteristic zero. Let `X` be a normal variety over `k` of dimension `n + 1`, `j : T ⟶ X` the
inclusion of a normal prime divisor `P`, and `B` an effective `ℚ`-divisor with `coeff_P B = 0`.
Let `τ` be a rational top form with `ord_P τ = -1` and `ρ` its Poincaré residue along `T`, and
suppose `D = div(τ) + P + B` is `ℚ`-Cartier. If `B_S` is a `ℚ`-divisor on `T` with
`div(ρ) + B_S = D|_T`, then `coeff_Q B_S ≥ 0` for every prime divisor `Q` of `T`. -/
public theorem coeff_nonneg_of_isPullback_divisorOfForm_isPoincareResidue_of_charZero
    {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (B : QDivisor X) (hB : B.IsEffective) (hBP : B.coeff P = 0)
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (hD : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsQCartier)
    (BS : QDivisor T)
    (hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).supp)
    (hBS : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsPullback j hgen
      (Divisor.toQDivisor (divisorOfForm ρ) + BS))
    (Q : Mori.PrimeDivisor T) :
    0 ≤ BS.coeff Q := by
  have h := isEffective_isPullback_sub_divisorOfForm sX hX hdim j hT P hP B hB hBP τ hτ0 hτ ρ hρ
    hD hgen _ hBS Q
  rwa [add_sub_cancel_left] at h

/-- **Effectivity of the residue different at a codimension-one point.** Let `X` be a normal
complex variety of dimension `n + 1`, `j : T ⟶ X` the inclusion of a normal prime divisor `P`,
and `B` an effective `ℚ`-divisor with `coeff_P B = 0`. Let `τ` be a rational top form with
`ord_P τ = -1` and `ρ` its Poincaré residue along `T` (`MMP.Fourfold.IsPoincareResidue`), and
suppose `D = div(τ) + P + B` is `ℚ`-Cartier. If `B_S` is a `ℚ`-divisor on `T` with
`div(ρ) + B_S = D|_T` (`MMP.Mori.QDivisor.IsPullback` along `j`), then `coeff_Q B_S ≥ 0` for every
prime divisor `Q` of `T`. -/
@[mmp "lem_fourfold_normal_prime_residue_effective_at_point"]
public theorem coeff_nonneg_of_isPullback_divisorOfForm_isPoincareResidue
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety ℂ (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (B : QDivisor X) (hB : B.IsEffective) (hBP : B.coeff P = 0)
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (hD : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsQCartier)
    (BS : QDivisor T)
    (hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).supp)
    (hBS : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsPullback j hgen
      (Divisor.toQDivisor (divisorOfForm ρ) + BS))
    (Q : Mori.PrimeDivisor T) :
    0 ≤ BS.coeff Q :=
  coeff_nonneg_of_isPullback_divisorOfForm_isPoincareResidue_of_charZero sX hX hdim j hT P hP B hB
    hBP τ hτ0 hτ ρ hρ hD BS hgen hBS Q

end MMP.Fourfold

end
