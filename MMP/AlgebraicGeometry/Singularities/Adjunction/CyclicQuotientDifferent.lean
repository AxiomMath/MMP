module

public import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
public import MMP.AlgebraicGeometry.Singularities.CyclicQuotientClassGroup
public import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
public import MMP.Analysis.Complex.CauchyTransformRungeMontel

/-!
# Residues, local equations and the local input at a cyclic quotient point

Auxiliary results for the different of `K_X + S` on a normal prime divisor `S` of a normal
variety `X` over a field `k`, at a codimension-one point `P` of `S` whose completed strict
henselization is the cyclic quotient `K[[x, y]]^{μ_m}`. Powers of rational forms and their
Poincaré residues along a prime divisor are compared, and the residue of a local generator of
`m(K_X + S + B)` is shown to be nonzero. The global restriction step reads the coefficient of the
residue different from local equations: restriction of units is multiplicative, and a Cartier
multiple of `K_X + S + B` has the local equation `φ₀^{M/m} ∏ h_i^{M b_i/m}` near `P`. Each `m B_i`
is principal at `P`, and the local equation `φ₀` of `m(K_X + S)` restricts to `S` with order
`m · ord_P(Res τ) + (m - 1)`, given the frame computation at the cyclic cover.

## Main results

* `MMP.CyclicChartDifferent.exists_isLocalEquation_nsmul_single`: `m B_i` is principal at `P`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6
-/

@[expose] public section

namespace MMP.CyclicChartDifferent

/-! ### Canonical divisors, powers of forms and residues of local generators -/

section AuxPort

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori

open MMP MMP.Fourfold

namespace Aux

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- On an integral scheme, the order `v_Q` of a unit of the factor `K(X)` is the order of
vanishing of its image in the function field. -/
theorem ordUnit_eq_ord {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
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
theorem componentToFunctionField_stalkSpecializes (X : Scheme.{u}) [IsIntegral X]
    (Z : irreducibleComponents X) {x : X} (h : componentGenericPoint X Z ⤳ x)
    (z : X.presheaf.stalk x) :
    (MMP.Positivity.componentToFunctionField Z).hom (X.presheaf.stalkSpecializes h z) =
      algebraMap (X.presheaf.stalk x) X.functionField z := by
  change (X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes _).hom z = _
  rw [TopCat.Presheaf.stalkSpecializes_comp]
  rfl

/-- `componentToFunctionField_stalkSpecializes` for `stalkToRationalFunctions`. -/
theorem componentToFunctionField_stalkToRationalFunctions (X : Scheme.{u}) [IsIntegral X]
    {Z : irreducibleComponents X} {x : X} (hx : x ∈ Z.1) (z : X.presheaf.stalk x) :
    (MMP.Positivity.componentToFunctionField Z).hom ((stalkToRationalFunctions X hx).hom z) =
      algebraMap (X.presheaf.stalk x) X.functionField z :=
  componentToFunctionField_stalkSpecializes X Z _ z

/-- A closed immersion of an irreducible scheme onto the support of a prime divisor maps the
generic point to the generic point of the divisor. -/
theorem map_genericPoint_eq {X T : Scheme.{u}} (j : T ⟶ X) [IsClosedImmersion j]
    [IrreducibleSpace T] (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X)) :
    j (genericPoint T) = P.genericPoint := by
  have h1 : IsGenericPoint (j (genericPoint T)) (P.support : Set X) := by
    have := (genericPoint_spec T).image j.base.hom.continuous
    rwa [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq, hP] at this
  have h2 : IsGenericPoint P.genericPoint (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isGenericPoint_closure
  exact h1.eq h2

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
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ hf) hf, ih]; push_cast; ring

/-! ### Poincaré residues along a prime divisor -/

section ResidueAlongPrimeDivisor

variable {k : Type u} [Field k] {Y T : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] {j : T ⟶ Y}

omit [IsNormal Y] in
/-- The residue of `b τ`, for `b` in the local ring at the generic point of `T`, is `b̄ Res τ`. -/
theorem IsPoincareResidue.algebraMap_smul {n m : ℕ} {τ : RationalPluriForms sY (n + 1) m}
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

/-- **Transcendence degree of a prime divisor**: `trdeg_k k(T) + 1 = trdeg_k k(Y)` for a closed
integral `T ⊂ Y` whose generic point is that of a prime divisor `P` of the normal variety `Y`. -/
theorem trdeg_add_one_of_eq_genericPoint {k : Type u} [Field k] [PerfectField k]
    {Y T : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral T] {j : T ⟶ Y} [LocallyOfFiniteType sY] [IsClosedImmersion j]
    [LocallyOfFiniteType (j ≫ sY)] (P : Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) :
    (letI := functionFieldAlgebra (j ≫ sY); (Algebra.trdeg k T.functionField).toNat) + 1 =
      (letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat) := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  obtain ⟨hdvr, hfree, hfin, hsm, -, hrank⟩ := MMP.Fourfold.stalk_facts (sY := sY) hP
  obtain ⟨htow, hsurj⟩ := MMP.Fourfold.stalkMap_facts (sY := sY) (j := j)
  obtain ⟨ϖ, r, -, -, hker, hϖ2, -⟩ := MMP.Fourfold.exists_uniformizer (sY := sY) hP
  have := essFiniteType_functionField (sX := j ≫ sY)
  have h := finrank_kaehlerDifferential_add_one (k := k) hsurj hker hϖ2
  rw [hrank, finrank_kaehlerDifferential_eq_trdeg] at h
  exact h

/-- An element of order `≥ 0` along a prime divisor lies in its local ring. -/
theorem exists_algebraMap_eq_of_ord_nonneg {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y) {f : Y.functionField}
    (hf : f ≠ 0) (h : 0 ≤ Y.ord f P.genericPoint) :
    ∃ a : Y.presheaf.stalk P.genericPoint, algebraMap _ Y.functionField a = f := by
  have h1 : P.divisorialValuation f ≤ 1 := by
    rw [P.divisorialValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  exact (P.divisorialValuation_le_one_iff f).mp h1

/-- The algebra map from the stalk at the generic point to the function field is the identity. -/
theorem algebraMap_stalk_genericPoint (T : Scheme.{u}) [IsIntegral T]
    (z : T.presheaf.stalk (genericPoint T)) :
    @algebraMap (T.presheaf.stalk (genericPoint T)) T.functionField _ _
      (stalkFunctionFieldAlgebra T (genericPoint T)) z = z := by
  change (T.presheaf.stalkSpecializes _).hom z = z
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- Along a prime divisor of an integral normal scheme there is a rational function of order
one. -/
theorem exists_ord_eq_one {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
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
theorem exists_ord_eq {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
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

/-! ### Powers of a rational form and their residues -/

section Pow

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]

/-- The power `τ^{⊗(M+1)}` of a rational top form, as a rational `(M+1)`-canonical form. -/
noncomputable def pluriPow {d : ℕ} (τ : RationalPluriForms sX d 1) :
    (M : ℕ) → RationalPluriForms sX d ((M + 1 : ℕ) : ℤ)
  | 0 => τ
  | M + 1 => RationalPluriForms.mul sX d (M + 1) 1 (pluriPow τ M) τ

/-- `τ^{⊗(M+2)} = τ^{⊗(M+1)} ⊗ τ`. -/
theorem pluriPow_succ {d : ℕ} (τ : RationalPluriForms sX d 1) (M : ℕ) :
    pluriPow τ (M + 1) = RationalPluriForms.mul sX d (M + 1) 1 (pluriPow τ M) τ := rfl

/-- On a scheme of dimension `d` over a perfect field, every power `τ^{⊗(M+1)}` of a nonzero
rational top form is nonzero. -/
theorem pluriPow_ne_zero [PerfectField k] [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) {τ : RationalPluriForms sX d 1} (hτ : τ ≠ 0) :
    ∀ M, pluriPow τ M ≠ 0
  | 0 => hτ
  | M + 1 => RationalPluriForms.mul_ne_zero (a := M + 1) (b := 1) hd (pluriPow_ne_zero hd hτ M) hτ

/-- The order of `τ^{⊗(M+1)}` along a prime divisor `Γ` is `(M + 1) ord_Γ τ`. -/
theorem ordForm_pluriPow [IsLocallyNoetherian X] [PerfectField k] [LocallyOfFiniteType sX]
    {d : ℕ} (hd : topologicalKrullDim X = d) {τ : RationalPluriForms sX d 1} (hτ : τ ≠ 0)
    (Γ : MMP.Mori.PrimeDivisor X) :
    ∀ M : ℕ, Γ.ordForm (pluriPow τ M) = ((M + 1 : ℕ) : ℤ) * Γ.ordForm τ
  | 0 => by simp only [zero_add, Nat.cast_one, one_mul]; rfl
  | M + 1 => by
    rw [pluriPow_succ, ordForm_mul (a := M + 1) (b := 1) Γ (pluriPow_ne_zero hd hτ M) hτ,
      ordForm_pluriPow hd hτ Γ M]
    push_cast; ring

end Pow

section ResiduePow

variable {k : Type u} [Field k] {Y T : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] {j : T ⟶ Y}

/-- **Multiplicativity of the Poincaré residue** along a closed integral `T ⊆ Y` whose generic
point is that of a prime divisor. -/
theorem isPoincareResidue_mul [PerfectField k] [LocallyOfFiniteType sY]
    [IsClosedImmersion j] [LocallyOfFiniteType (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    {n a b : ℕ} (hY : topologicalKrullDim Y = n + 1)
    {τ₁ : RationalPluriForms sY (n + 1) a} {τ₂ : RationalPluriForms sY (n + 1) b}
    {ρ₁ : RationalPluriForms (j ≫ sY) n a} {ρ₂ : RationalPluriForms (j ≫ sY) n b}
    (h₁ : IsPoincareResidue sY j n a τ₁ ρ₁) (h₂ : IsPoincareResidue sY j n b τ₂ ρ₂) :
    IsPoincareResidue sY j n (a + b) (RationalPluriForms.mul sY (n + 1) a b τ₁ τ₂)
      (RationalPluriForms.mul (j ≫ sY) n a b ρ₁ ρ₂) := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨hdvr, hfree, -, -, -, -⟩ := MMP.Fourfold.stalk_facts (sY := sY) hP
  obtain ⟨htow, hsurj⟩ := MMP.Fourfold.stalkMap_facts (sY := sY) (j := j)
  obtain ⟨ϖ, r, hϖ0, hr, -, -, hunif⟩ := MMP.Fourfold.exists_uniformizer (sY := sY) hP
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := sY) (by exact_mod_cast hY)
  have hline : Module.finrank Y.functionField (⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k]) =
      1 := by rw [Module.finrank_eq_card_basis b₀, Fintype.card_unit]
  obtain ⟨t₁, g₁, x₁, ht₁, hτ₁, rfl⟩ := h₁
  obtain ⟨t₂, g₂, x₂, ht₂, hτ₂, rfl⟩ := h₂
  obtain ⟨u₁, hu₁, rfl⟩ := hunif t₁ ht₁
  obtain ⟨u₂, hu₂, rfl⟩ := hunif t₂ ht₂
  obtain ⟨g, u, x, hu, hK, hL⟩ := exists_logPluriForm_mul (a := a) (b := b) hline hsurj hϖ0 hr
    g₁ g₂ hu₁ hu₂ x₁ x₂
  refine ⟨u * ϖ, g, x, ?_, ?_, hL.symm ▸ rfl⟩
  · rcases hu with rfl | rfl
    · exact ht₁
    · exact ht₂
  · rw [hτ₁, hτ₂]
    exact hK

/-- The residue of `τ^{⊗(M+1)}` is `ρ^{⊗(M+1)}`. -/
theorem isPoincareResidue_pluriPow [PerfectField k] [LocallyOfFiniteType sY]
    [IsClosedImmersion j] [LocallyOfFiniteType (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    {n : ℕ} (hY : topologicalKrullDim Y = n + 1)
    {τ : RationalPluriForms sY (n + 1) 1} {ρ : RationalPluriForms (j ≫ sY) n 1}
    (hρ : IsPoincareResidue sY j n 1 τ ρ) :
    ∀ M : ℕ, IsPoincareResidue sY j n (M + 1) (pluriPow τ M) (pluriPow ρ M)
  | 0 => hρ
  | M + 1 => isPoincareResidue_mul P hP hY (isPoincareResidue_pluriPow P hP hY hρ M) hρ

end ResiduePow

/-! ### The residue is nonzero -/

/-- The Poincaré residue of a form with a simple pole along a normal prime divisor is nonzero:
some nonzero form on `T` lifts to a multiple `f τ`, `f` regular along `P`, and its residue is
`f̄ ρ`. -/
theorem isPoincareResidue_ne_zero
    {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (Q : Mori.PrimeDivisor T) : ρ ≠ 0 := by
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
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := sX) (d := n + 1) (by rw [hdim]; norm_cast)
  have hrank : Module.finrank X.functionField (RationalPluriForms sX (n + 1) 1) = 1 := by
    let bb : Module.Basis Unit X.functionField (RationalPluriForms sX (n + 1) 1) :=
      ZTensorPower.basis b₀ 1
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  have hrankT : Module.finrank T.functionField (RationalPluriForms (j ≫ sX) n 1) = 1 := by
    have := essFiniteType_functionField (sX := j ≫ sX)
    have hK : Module.finrank T.functionField Ω[T.functionField⁄k] = n :=
      (finrank_kaehlerDifferential_eq_trdeg k T.functionField).trans hdT
    have : FiniteDimensional T.functionField Ω[T.functionField⁄k] :=
      (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k T.functionField).1
    have h1 : Module.finrank T.functionField (⋀[T.functionField]^n Ω[T.functionField⁄k]) = 1 := by
      rw [exteriorPower.finrank_eq, hK, Nat.choose_self]
    let c₀ := (Module.finBasisOfFinrankEq _ _ h1).reindex (Equiv.ofUnique (Fin 1) Unit)
    let bb : Module.Basis Unit T.functionField (RationalPluriForms (j ≫ sX) n 1) :=
      ZTensorPower.basis c₀ 1
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  have : Nontrivial (RationalPluriForms (j ≫ sX) n 1) :=
    Module.nontrivial_of_finrank_pos (R := T.functionField) (by omega)
  obtain ⟨ρ₀, hρ₀⟩ := exists_ne (0 : RationalPluriForms (j ≫ sX) n 1)
  obtain ⟨g, hg0, hg⟩ := exists_ord_eq Q (-Q.ordForm ρ₀)
  set ρ₁ := g • ρ₀ with hρ₁def
  have hρ₁0 : ρ₁ ≠ 0 := smul_ne_zero hg0 hρ₀
  have hρ₁Q : Q.ordForm ρ₁ = 0 := by
    rw [hρ₁def, Q.ordForm_smul (sX := j ≫ sX) hdT hg0 hρ₀, hg]
    ring
  obtain ⟨σ, hσP, -, hσres⟩ :=
    exists_isPoincareResidue_of_le_ordForm_of_charZero sX hX hdim j hT P hP Q ρ₁ hρ₁Q.ge
  obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' τ hτ0).mp hrank σ
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
  have hρσeq := MMP.Fourfold.isPoincareResidue_unique (sY := sX) hjT hσres hres
  exact (smul_ne_zero_iff.mp (hρσeq ▸ hρ₁0 :
    (j.stalkMap (genericPoint T)).hom b₁ • ρ ≠ 0)).2

/-! ### Local generators of `m(K_X + S + B)` and their residues -/

/-- The order of a unit of `K(X)` along a prime divisor, read off a stalk element representing
it. -/
theorem ord_eq_ord_algebraMap_of_stalk {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (φ : (RationalFunctions X)ˣ) {y : X}
    (W : irreducibleComponents X) (hy : y ∈ W.1) (a : X.presheaf.stalk y)
    (ha : (stalkToRationalFunctions X hy).hom a = (φ : RationalFunctions X) W)
    (Γ : Mori.PrimeDivisor X) :
    Γ.ord φ = X.ord (algebraMap _ X.functionField a) Γ.genericPoint := by
  obtain rfl : W = Γ.component :=
    (MMP.Fourfold.subsingleton_irreducibleComponents (X := X)).elim _ _
  rw [MMP.Positivity.ord_eq_ord_componentToFunctionField, ← ha,
    componentToFunctionField_stalkToRationalFunctions]

/-- **Local generators of `m(K_X + S + B)` with residues generating `m(K_S + B_S)`.** If `M D` is
Cartier, `D = K_X + S + B`, and `K_S + B_S = D|_S`, then near every point of `S` a unit multiple
`τ' = f τ^{⊗M}` of a power of `τ` generates `𝒪_X(M(K_X + S + B))`, and its residue
`f̄ ρ^{⊗M}` generates `𝒪_S(M(K_S + B_S))`: `f` is the inverse of a local equation of `M D`. -/
theorem exists_generatesOn_isPoincareResidue
    {k : Type} [Field k] [PerfectField k] {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX)) (hdimT : topologicalKrullDim T = n)
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (B : QDivisor X)
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ) (hρ0 : ρ ≠ 0)
    (BS : QDivisor T)
    (hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).supp)
    (hBS : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsPullback j hgen
      (Divisor.toQDivisor (divisorOfForm ρ) + BS))
    (M : ℕ) (DM : Divisor X)
    (hDM : Divisor.toQDivisor DM = ((M + 1 : ℕ) : ℤ) •
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B))
    (hDMc : DM.IsCartier) (x : T) :
    ∃ U : X.Opens, j x ∈ U ∧ ∃ τ' : RationalPluriForms sX (n + 1) ((M + 1 : ℕ) : ℤ),
      GeneratesOn (Finsupp.single P 1 + B) (M + 1) U τ' ∧
      ∃ ρ' : RationalPluriForms (j ≫ sX) n ((M + 1 : ℕ) : ℤ),
        IsPoincareResidue sX j n (M + 1) τ' ρ' ∧ GeneratesOn BS (M + 1) (j ⁻¹ᵁ U) ρ' := by
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
  have hdim' : topologicalKrullDim X = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; norm_cast
  have hM : 0 < M + 1 := Nat.succ_pos M
  obtain ⟨DT, hDT, hp⟩ := hBS (M + 1) hM DM hDM hDMc
  obtain ⟨U, hxU, φ, hφ⟩ := hDMc (j x)
  have hm' : (((M + 1 : ℕ)) : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hgenM : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ DM.supp :=
    fun Z hZ => hgen Z (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hDM] at hZ)
  let Z₀ : irreducibleComponents T := ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩
  have hgx : genericPoint T ⤳ x := (genericPoint_spec T).specializes trivial
  have hgU : j (genericPoint T) ∈ U := (hgx.map j.base.hom.continuous).mem_open U.isOpen hxU
  have hgs : j (genericPoint T) ∉ DM.supp := by
    have := hgenM Z₀
    rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at this
  obtain ⟨a₀, ha₀⟩ := hφ.exists_unit_stalk hgU hgs (mem_pointComponent _)
  have hordX : ∀ Γ : Mori.PrimeDivisor X, (Γ.support ∩ U).Nonempty →
      DM.coeff Γ = X.ord (algebraMap _ X.functionField a₀.val) Γ.genericPoint := fun Γ hΓ => by
    rw [hφ Γ hΓ]
    exact ord_eq_ord_algebraMap_of_stalk φ _ _ _ ha₀ Γ
  have hordT : ∀ Γ' : Mori.PrimeDivisor T, (Γ'.support ∩ j ⁻¹ᵁ U).Nonempty →
      DT.coeff Γ' = T.ord ((j.stalkMap (genericPoint T)).hom a₀.val) Γ'.genericPoint := by
    intro Γ' hΓ'
    rw [hp U φ hφ Γ' hΓ']
    have hc := MMP.Fourfold.componentGenericPoint_eq_genericPoint (X := T) Γ'.component
    have h₀ : componentGenericPoint T Γ'.component ⤳ genericPoint T := specializes_of_eq hc
    have h₁ : j (componentGenericPoint T Γ'.component) ⤳ j (genericPoint T) :=
      j.base.hom.map_specializes h₀
    have hW : j (componentGenericPoint T Γ'.component) ∈
        (pointComponent (j (genericPoint T))).1 := by
      rw [hc]
      exact mem_pointComponent _
    let a' : (X.presheaf.stalk (j (componentGenericPoint T Γ'.component)))ˣ :=
      Units.map (X.presheaf.stalkSpecializes h₁).hom.toMonoidHom a₀
    have ha' : (stalkToRationalFunctions X hW).hom a' =
        (φ : RationalFunctions X) (pointComponent (j (genericPoint T))) := by
      rw [← ha₀]
      change (X.presheaf.stalkSpecializes h₁ ≫ X.presheaf.stalkSpecializes _).hom a₀.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    rw [pullbackComponent_eq hgenM hφ _ hW a' ha', ordUnit_eq_ord, Units.coe_map]
    change T.ord ((MMP.Positivity.componentToFunctionField Γ'.component).hom
      ((j.stalkMap _).hom ((X.presheaf.stalkSpecializes h₁).hom a₀.val))) _ = _
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ h₀,
      componentToFunctionField_stalkSpecializes T _ h₀, algebraMap_stalk_genericPoint T]
  have hXa : algebraMap _ X.functionField a₀.val ≠ 0 := (a₀.isUnit.map _).ne_zero
  have hXb : algebraMap _ X.functionField (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T))) ≠ 0 :=
    ((a₀⁻¹).isUnit.map _).ne_zero
  have hXab : ∀ z : X, X.ord (algebraMap _ X.functionField
      (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T)))) z =
        -X.ord (algebraMap _ X.functionField a₀.val) z := fun z => by
    have h := Scheme.ord_mul (x := z) hXa hXb
    rw [← map_mul, Units.mul_inv, map_one, ord_one'] at h
    omega
  have hTa : ((j.stalkMap (genericPoint T)).hom a₀.val : T.functionField) ≠ 0 :=
    ((a₀.isUnit.map (j.stalkMap (genericPoint T)).hom)).ne_zero
  have hTb : ((j.stalkMap (genericPoint T)).hom
      (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T))) : T.functionField) ≠ 0 :=
    (((a₀⁻¹).isUnit.map (j.stalkMap (genericPoint T)).hom)).ne_zero
  have hTab : ∀ z : T, T.ord ((j.stalkMap (genericPoint T)).hom
      (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T))) : T.functionField) z =
        -T.ord ((j.stalkMap (genericPoint T)).hom a₀.val : T.functionField) z := fun z => by
    have h := Scheme.ord_mul (x := z) hTa hTb
    have e : ((j.stalkMap (genericPoint T)).hom a₀.val : T.functionField) *
        (j.stalkMap (genericPoint T)).hom (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T))) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [e, ord_one'] at h
    omega
  have hτM := pluriPow_ne_zero hdim' hτ0 M
  have hρM := pluriPow_ne_zero hdimT hρ0 M
  refine ⟨U, hxU, algebraMap _ X.functionField (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T))) •
      pluriPow τ M, ⟨smul_ne_zero hXb hτM, fun Γ hΓ => ?_⟩,
    ((j.stalkMap (genericPoint T)).hom (↑a₀⁻¹ : X.presheaf.stalk (j (genericPoint T))) :
      T.functionField) • pluriPow ρ M,
    IsPoincareResidue.algebraMap_smul (isPoincareResidue_pluriPow P hjT hdim hρ M) _,
    ⟨smul_ne_zero hTb hρM, fun Γ' hΓ' => ?_⟩⟩
  · rw [Γ.ordForm_smul (sX := sX) hd hXb hτM, ordForm_pluriPow hdim' hτ0 Γ M, hXab,
      ← hordX Γ hΓ]
    have hc := congrArg (fun G : QDivisor X => G.coeff Γ) hDM
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, coeff_divisorOfForm, zsmul_eq_mul] at hc
    simp only [DivisorWithCoeffs.coeff_add]
    push_cast at hc ⊢
    linear_combination -hc
  · rw [Γ'.ordForm_smul (sX := j ≫ sX) hdT hTb hρM, ordForm_pluriPow hdimT hρ0 Γ' M, hTab,
      ← hordT Γ' hΓ']
    have hc := congrArg (fun G : QDivisor T => G.coeff Γ') hDT
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, coeff_divisorOfForm, zsmul_eq_mul] at hc
    push_cast at hc ⊢
    linear_combination -hc

/-- **The different of a plt pair has coefficients `< 1`.** -/
theorem coeff_lt_one_of_isPltPair'
    {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX)) (hdimT : topologicalKrullDim T = n)
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (Q : MMP.Mori.PrimeDivisor T) (B : QDivisor X) (hB : B.IsEffective) (hBP : B.coeff P = 0)
    (hplt : IsPltPair sX (n + 1) (divisorOfForm τ) (Finsupp.single P 1 + B))
    (BS : QDivisor T)
    (hBS : ∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
        (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).supp,
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsPullback j hgen
        (Divisor.toQDivisor (divisorOfForm ρ) + BS))
    (KS : Divisor T) (hKS : KS.IsCanonicalDivisor (j ≫ sX) n)
    (hCart : ∀ {m : ℕ}, (∀ w : T, ∃ U : T.Opens, w ∈ U ∧
        ∃ σ : RationalPluriForms (j ≫ sX) n m, GeneratesOn BS m U σ) →
      ((m : ℤ) • (Divisor.toQDivisor KS + BS)).IsCartierDivisor)
    (hFA : ∀ (K : Divisor X), K.IsCanonicalDivisor sX (n + 1) →
      ∀ (KS : Divisor T), KS.IsCanonicalDivisor (j ≫ sX) n →
      ∀ (B : QDivisor X), 0 ≤ B → B.coeff P = 0 →
      (∃ m : ℕ, 0 < m ∧
        ((m : ℤ) • (Divisor.toQDivisor K + (Finsupp.single P 1 + B))).IsCartierDivisor) →
      ∀ (BS : QDivisor T), (∃ m : ℕ, 0 < m ∧ ∀ x : T, ∃ U : X.Opens, j.base x ∈ U ∧
        ∃ τ : RationalPluriForms sX (n + 1) m, GeneratesOn (Finsupp.single P 1 + B) m U τ ∧
          ∃ ρ : RationalPluriForms (j ≫ sX) n m,
            IsPoincareResidue sX j n m τ ρ ∧ GeneratesOn BS m (j ⁻¹ᵁ U) ρ) →
      ∀ (F : DivisorOver k (j ≫ sX)), ∃ E : DivisorOver k sX, E.IsExceptional ∧
        j.base (F.f.base F.E.genericPoint) = E.f.base E.E.genericPoint ∧
        ∀ a : ℚ, IsDiscrepancy (j ≫ sX) n KS BS F a ↔
          IsDiscrepancy sX (n + 1) K (Finsupp.single P 1 + B) E a) :
    BS.coeff Q < 1 := by
  classical
  obtain ⟨⟨-, hK, hQC⟩, hdisc⟩ := hplt
  obtain ⟨hgen, hpb⟩ := hBS
  have hρ0 := isPoincareResidue_ne_zero sX hX hdim j hT P hP τ hτ0 hτ ρ hρ Q
  obtain ⟨M₀, hM₀, hC⟩ := hQC.exists_pos
  obtain ⟨M, rfl⟩ : ∃ M, M₀ = M + 1 := ⟨M₀ - 1, by omega⟩
  obtain ⟨DM, hDM, hDMc⟩ := id hC
  have hDM' : Divisor.toQDivisor DM = ((M + 1 : ℕ) : ℤ) •
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B) := by
    rw [hDM, add_assoc]
  have hgens := exists_generatesOn_isPoincareResidue sX hdim j hT hdimT P hP B τ hτ0 ρ hρ hρ0 BS
    hgen hpb M DM hDM' hDMc
  have hB0 : 0 ≤ B := DivisorWithCoeffs.isEffective_iff_nonneg.mp hB
  set F : DivisorOver k (j ≫ sX) := DivisorOver.ofPrimeDivisor k hT Q with hFdef
  obtain ⟨E, hE, -, hiff⟩ := hFA (divisorOfForm τ) hK KS hKS B hB0 hBP ⟨M + 1, hM₀, hC⟩ BS
    ⟨M + 1, hM₀, hgens⟩ F
  have hFdisc : IsDiscrepancy (j ≫ sX) n KS BS F (-BS.coeff Q) := by
    obtain ⟨U, hU, -, -, ρ', -, hρ'⟩ := hgens Q.genericPoint
    refine ⟨hT, hKS, M + 1, hM₀, hCart fun w => ?_, j ⁻¹ᵁ U, hU, ρ', hρ', ?_⟩
    · obtain ⟨U', hU', -, -, σ, -, hσ⟩ := hgens w
      exact ⟨j ⁻¹ᵁ U', hU', σ, hσ⟩
    · rw [hFdef, DivisorOver.ordPullback_ofPrimeDivisor hT hdimT Q ρ']
      have hQU : (Q.support ∩ j ⁻¹ᵁ U).Nonempty := (Q.genericPoint_mem_iff _).mp hU
      have e := hρ'.2 Q hQU
      push_cast at e ⊢
      linear_combination -e
  have hEd := (hiff _).mp hFdisc
  have h := lt_of_lt_of_le hdisc (discrep_le hE hEd)
  rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by rw [EReal.coe_neg, EReal.coe_one]] at h
  have h2 : (-1 : ℝ) < ((-BS.coeff Q : ℚ) : ℝ) := EReal.coe_lt_coe_iff.mp h
  have h3 : (-1 : ℚ) < -BS.coeff Q := by exact_mod_cast h2
  linarith

end

end Aux

end AuxPort

end MMP.CyclicChartDifferent

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace MMP.CyclicChartDifferent

open MMP MMP.Mori MMP.Flips MMP.Fourfold

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

/-! ### The global restriction step -/

/-- The coefficient of the restriction of a `ℚ`-Cartier divisor
`D = G + ∑ b_i B_i` along `j` at a prime divisor `Q` of `T`, from local equations near
`j(η_Q)` of `m G` and of the `m B_i`. -/
theorem mul_coeff_isPullback_eq {X T : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian T] [IsNormal T] (j : T ⟶ X) (Q : Mori.PrimeDivisor T)
    (G : Divisor X) {ι : Type*} [Fintype ι] (Bi : ι → Mori.PrimeDivisor X) (b : ι → ℚ)
    {m : ℕ} (hm : 0 < m) {U : X.Opens} (hU : j Q.genericPoint ∈ U)
    {φ₀ : (RationalFunctions X)ˣ} (hφ₀ : ((m : ℤ) • G).IsLocalEquation U φ₀)
    {h : ι → (RationalFunctions X)ˣ}
    (hh : ∀ i, Divisor.IsLocalEquation ((m : ℤ) • Finsupp.single (Bi i) (1 : ℤ)) U (h i))
    (hG : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ ((m : ℤ) • G).supp)
    (hB : ∀ i, ∀ Z : irreducibleComponents T,
      j (componentGenericPoint T Z) ∉
        DivisorWithCoeffs.supp ((m : ℤ) • Finsupp.single (Bi i) (1 : ℤ)))
    (hQU : j (componentGenericPoint T Q.component) ∈ U) {D : QDivisor X}
    (hDG : D = Divisor.toQDivisor G + ∑ i, b i • Finsupp.single (Bi i) 1) (hDq : D.IsQCartier)
    {hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp}
    {BS : QDivisor T} (hBS : D.IsPullback j hgen BS) :
    (m : ℚ) * BS.coeff Q = (Q.ordUnit (pullbackComponent j hG hφ₀ Q.component hQU) : ℚ) +
      ∑ i, b i * (Q.ordUnit (pullbackComponent j (hB i) (hh i) Q.component hQU) : ℚ) := by
  classical
  subst hDG
  obtain ⟨N, hN, D₀, hD₀, hD₀c⟩ := hDq.exists_pos
  set L : ℕ := ∏ i, (b i).den with hLdef
  have hL : 0 < L := Finset.prod_pos fun i _ => (b i).den_pos
  have hc : ∀ i, ∃ c : ℤ, (c : ℚ) = N * L * b i := by
    intro i
    obtain ⟨k, hk⟩ : (b i).den ∣ L := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    refine ⟨N * k * (b i).num, ?_⟩
    have h1 := Rat.mul_den_eq_num (b i)
    rw [hk]
    push_cast
    linear_combination (-(N : ℚ) * k) * h1
  choose c hc using hc
  set M : ℕ := N * m * L with hMdef
  have hM : 0 < M := Nat.mul_pos (Nat.mul_pos hN hm) hL
  set DM : Divisor X := ((m * L : ℕ) : ℤ) • D₀ with hDMdef
  have hDM : Divisor.toQDivisor DM =
      (M : ℤ) • (Divisor.toQDivisor G + ∑ i, b i • Finsupp.single (Bi i) 1) := by
    rw [hDMdef, map_zsmul, hD₀, smul_smul]
    congr 1
    rw [hMdef]
    push_cast
    ring
  obtain ⟨D', hD', hpb⟩ := hBS M hM DM hDM (hD₀c.zsmul _)
  set n : ℤ := ((N * L : ℕ) : ℤ) with hn
  set ψ : (RationalFunctions X)ˣ := φ₀ ^ n * ∏ i, h i ^ c i with hψdef
  have hψ : DM.IsLocalEquation U ψ := by
    intro E hE
    apply Int.cast_injective (α := ℚ)
    have h1 := congrArg (fun F : QDivisor X => F.coeff E) hDM
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      smul_eq_mul] at h1
    rw [h1, hψdef, PrimeDivisor.ord_mul, PrimeDivisor.ord_zpow, smul_eq_mul]
    have h2 := hφ₀ E hE
    have h3 : ∀ i, E.ord (h i) =
        (m : ℤ) * DivisorWithCoeffs.coeff (Finsupp.single (Bi i) (1 : ℤ)) E :=
      fun i => by rw [← hh i E hE, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h2
    have hprod : E.ord (∏ i, h i ^ c i) = ∑ i, c i * E.ord (h i) := by
      simp only [PrimeDivisor.ord, map_prod, toAdd_prod, map_zpow, toAdd_zpow, smul_eq_mul]
    rw [hprod, ← h2]
    have hsum : DivisorWithCoeffs.coeff (∑ i, b i • Finsupp.single (Bi i) (1 : ℚ)) E =
        ∑ i, b i * (DivisorWithCoeffs.coeff (Finsupp.single (Bi i) (1 : ℤ)) E : ℚ) := by
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.smul_apply, smul_eq_mul, DivisorWithCoeffs.coeff_apply]
      by_cases hi : Bi i = E <;> simp [Finsupp.single_apply, hi]
    rw [hsum]
    push_cast
    simp only [h3, hn, Int.cast_mul, Int.cast_natCast, hc, Finset.mul_sum]
    rw [zsmul_eq_mul, hMdef]
    push_cast
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
      split_ifs <;> simp; ring
  have hQ : (Q.support ∩ j ⁻¹ᵁ U).Nonempty := (Q.genericPoint_mem_iff (j ⁻¹ᵁ U)).mp hU
  have hcoef := hpb U ψ hψ Q hQ
  set W := pointComponent (j (componentGenericPoint T Q.component))
  have hW : j (componentGenericPoint T Q.component) ∈ W.1 := mem_pointComponent _
  obtain ⟨a₀, ha₀⟩ := hφ₀.exists_unit_stalk hQU (hG _) hW
  have ha : ∀ i, ∃ a : (X.presheaf.stalk (j (componentGenericPoint T Q.component)))ˣ,
      (stalkToRationalFunctions X hW).hom a = (h i : RationalFunctions X) W :=
    fun i => (hh i).exists_unit_stalk hQU (hB i _) hW
  choose a ha using ha
  have hkey : Units.map (stalkToRationalFunctions X hW).hom.toMonoidHom
        (a₀ ^ n * ∏ i, a i ^ c i) =
      Units.map (RationalFunctions.component X W).toMonoidHom ψ := by
    have e₀ : Units.map (stalkToRationalFunctions X hW).hom.toMonoidHom a₀ =
        Units.map (RationalFunctions.component X W).toMonoidHom φ₀ := Units.ext ha₀
    have e : ∀ i, Units.map (stalkToRationalFunctions X hW).hom.toMonoidHom (a i) =
        Units.map (RationalFunctions.component X W).toMonoidHom (h i) := fun i => Units.ext (ha i)
    simp only [hψdef, map_mul, map_zpow, map_prod, e₀, e]
  rw [pullbackComponent_eq _ hψ hQU hW _ (congrArg Units.val hkey)] at hcoef
  rw [pullbackComponent_eq hG hφ₀ hQU hW a₀ ha₀]
  simp_rw [pullbackComponent_eq (hB _) (hh _) hQU hW (a _) (ha _)]
  have hprodU : ∀ (u : ι → (X.presheaf.stalk (j (componentGenericPoint T Q.component)))ˣ),
      Q.ordUnit (Units.map (j.stalkMap (componentGenericPoint T Q.component)).hom.toMonoidHom
        (∏ i, u i ^ c i)) = ∑ i, c i * Q.ordUnit
          (Units.map (j.stalkMap (componentGenericPoint T Q.component)).hom.toMonoidHom (u i)) := by
    intro u
    simp only [PrimeDivisor.ordUnit, map_prod, map_zpow, toAdd_prod, toAdd_zpow, smul_eq_mul]
  rw [map_mul, PrimeDivisor.ordUnit_mul, map_zpow, PrimeDivisor.ordUnit_zpow, hprodU] at hcoef
  have hD'Q := congrArg (fun F : QDivisor T => F.coeff Q) hD'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hD'Q
  rw [hcoef] at hD'Q
  push_cast at hD'Q
  simp only [hc, hn] at hD'Q
  have hNL : ((N : ℚ) * L) ≠ 0 := by positivity
  apply mul_left_cancel₀ hNL
  rw [zsmul_eq_mul, hMdef] at hD'Q
  push_cast at hD'Q
  have hs : ∀ o : ι → ℚ, ∑ x, (N : ℚ) * L * b x * o x = N * L * ∑ x, b x * o x := fun o => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hs] at hD'Q
  linear_combination hD'Q.symm

/-! ### Points, supports and restriction of units -/

/-- The generic point of a prime divisor `P` lies off the support of a divisor in which `P` has
coefficient zero. -/
theorem genericPoint_notMem_supp_of_coeff_eq_zero {R : Type*} [Zero R] {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X]
    {G : DivisorWithCoeffs R X} {P : MMP.Mori.PrimeDivisor X} (hG : G.coeff P = 0) :
    P.genericPoint ∉ G.supp := by
  intro h
  obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  obtain rfl := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hmem
  exact hE hG

/-- The generic point of a component of `T` maps off the support of a divisor of `X` whose
coefficient along the image `P` of `T` vanishes. -/
theorem map_componentGenericPoint_notMem_supp {R : Type*} [Zero R] {X T : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T]
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    {G : DivisorWithCoeffs R X} (hG : G.coeff P = 0) (Z : irreducibleComponents T) :
    j (componentGenericPoint T Z) ∉ G.supp := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint,
    Aux.map_genericPoint_eq j P hP]
  exact genericPoint_notMem_supp_of_coeff_eq_zero hG

/-- The point `j(η_T)` specializes to `j(η_Q)`, so it lies in every open containing `j(η_Q)`. -/
theorem map_specializes_genericPoint {X T : Scheme.{u}} (j : T ⟶ X)
    (Q : MMP.Mori.PrimeDivisor T) :
    j (componentGenericPoint T Q.component) ⤳ j Q.genericPoint :=
  Q.specializes_genericPoint.map j.base.hom.continuous

/-- The restriction of a local equation of an effective divisor near `j(η_Q)` has nonnegative
order along `Q`: by algebraic Hartogs the equation is regular at `j(η_Q)`, and its restriction
lies in `𝒪_{T,Q}`. -/
theorem ordUnit_pullbackComponent_nonneg {X T : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian T] [IsNormal T] (j : T ⟶ X) (Q : MMP.Mori.PrimeDivisor T)
    {Dv : Divisor X} (hDv : ∀ E, 0 ≤ Dv.coeff E) {U : X.Opens} (hU : j Q.genericPoint ∈ U)
    {h : (RationalFunctions X)ˣ} (hh : Dv.IsLocalEquation U h)
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ Dv.supp)
    (hQU : j (componentGenericPoint T Q.component) ∈ U) :
    0 ≤ Q.ordUnit (pullbackComponent j hB hh Q.component hQU) := by
  have hsp := map_specializes_genericPoint j Q
  set W := pointComponent (j (componentGenericPoint T Q.component))
  have hW : j (componentGenericPoint T Q.component) ∈ W.1 := mem_pointComponent _
  have hxW : j Q.genericPoint ∈ W.1 :=
    hsp.mem_closed (isClosed_of_mem_irreducibleComponents _ W.2) hW
  obtain ⟨r, hr⟩ := exists_stalk_eq_of_forall_zero_le_ord hxW h fun E hE => by
    rw [← hh E ⟨_, hE, hU⟩]; exact hDv E
  obtain ⟨a, ha⟩ := hh.exists_unit_stalk hQU (hB _) hW
  have har : a.val = (X.presheaf.stalkSpecializes hsp).hom r := by
    apply stalkToRationalFunctions_injective hW
    rw [ha, ← hr]
    change _ = (X.presheaf.stalkSpecializes hsp ≫ X.presheaf.stalkSpecializes _).hom r
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  rw [pullbackComponent_eq hB hh hQU hW a ha]
  set u := Units.map (j.stalkMap (componentGenericPoint T Q.component)).hom.toMonoidHom a
  have hu : u.val = Q.toComponent.hom ((j.stalkMap Q.genericPoint).hom r) := by
    change (j.stalkMap _).hom a.val = _
    rw [har, Scheme.Hom.stalkSpecializes_stalkMap_apply]
    rfl
  have hne : (j.stalkMap Q.genericPoint).hom r ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu
    exact u.ne_zero hu
  have h1 := Q.one_le_valuation_toComponent hne
  rw [← hu, PrimeDivisor.valuation_eq_exp_ordUnit, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h1
  exact h1

/-- Away from `B`, the divisor `m B` has the local equation `1`. -/
theorem isLocalEquation_one_compl {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (m : ℤ) (B : MMP.Mori.PrimeDivisor X) :
    Divisor.IsLocalEquation (m • Finsupp.single B (1 : ℤ))
      ⟨(B.support : Set X)ᶜ, by
        rw [isOpen_compl_iff, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isClosed_closure⟩ 1 := by
  intro E hE
  have hEB : B ≠ E := by
    rintro rfl
    obtain ⟨x, hx, hx'⟩ := hE
    exact hx' hx
  rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_single_of_ne hEB, smul_zero,
    PrimeDivisor.ord_one]

/-- The restriction of the unit `1` has order zero. -/
theorem ordUnit_pullbackComponent_one {X T : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian T] [IsNormal T] (j : T ⟶ X) (Q : MMP.Mori.PrimeDivisor T)
    {Dv : Divisor X} {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ1 : φ = 1)
    (hh : Dv.IsLocalEquation U φ)
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ Dv.supp)
    (hQU : j (componentGenericPoint T Q.component) ∈ U) :
    Q.ordUnit (pullbackComponent j hB hh Q.component hQU) = 0 := by
  subst hφ1
  rw [pullbackComponent_eq hB hh hQU (mem_pointComponent _) 1 (by simp), map_one,
    PrimeDivisor.ordUnit_one]

/-- **Spreading out a local equation.** If `φ` is a local equation of `D` at `x`, in the sense
that `D` and `div φ` agree at every prime divisor through `x`, then `φ` is a local equation of
`D` on the open complement of `Supp (D - div φ)`. -/
theorem exists_isLocalEquation_of_forall_mem_support {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (D : Divisor X)
    (φ : (RationalFunctions X)ˣ) (x : X)
    (h : ∀ E : MMP.Mori.PrimeDivisor X, x ∈ E.support → D.coeff E = E.ord φ) :
    ∃ U : X.Opens, x ∈ U ∧ D.IsLocalEquation U φ := by
  set F : Divisor X := D - principalDivisor φ
  have hF : ∀ E : MMP.Mori.PrimeDivisor X, F.coeff E = D.coeff E - E.ord φ := fun E => by
    rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor]
  refine ⟨⟨(F.supp : Set X)ᶜ, F.isClosed_supp.isOpen_compl⟩, fun hx => ?_, fun E hE => ?_⟩
  · obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    exact hE (by rw [hF, h E hxE, sub_self])
  · by_contra hne
    obtain ⟨y, hyE, hyU⟩ := hE
    exact hyU (DivisorWithCoeffs.support_subset_supp (by rw [hF]; exact sub_ne_zero.mpr hne) hyE)

/-! ### Principality of `m B` at a cyclic quotient point -/

/-- If the extension of an ideal `J` along a faithfully flat map to a local ring is principal,
then `J` is generated by one of its own elements. -/
theorem exists_eq_span_of_map_eq_span {A R : Type*} [CommRing A] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing A] [Algebra A R] [Module.FaithfullyFlat A R] (J : Ideal A) {c : R}
    (h : J.map (algebraMap A R) = Ideal.span {c}) :
    ∃ a ∈ J, J = Ideal.span {a} := by
  classical
  have hdesc : ∀ a ∈ J, Ideal.span {algebraMap A R a} = Ideal.span {c} → J = Ideal.span {a} := by
    intro a haJ ha
    refine le_antisymm ?_ (Ideal.span_le.2 (by simpa using haJ))
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (Ideal.span {a}) (B := R), Ideal.map_span,
      Set.image_singleton, ha, ← h]
    exact Ideal.le_comap_map
  by_cases hc : c = 0
  · subst hc
    refine ⟨0, J.zero_mem, hdesc 0 J.zero_mem (by simp)⟩
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian J : J.FG)
  have hcmem : c ∈ Ideal.span ((algebraMap A R) '' (s : Set A)) := by
    rw [← Ideal.map_span, Ideal.span, hs, h]; exact Ideal.mem_span_singleton_self c
  rw [← Finset.coe_image, Ideal.span, Submodule.mem_span_finset] at hcmem
  obtain ⟨r, -, hr⟩ := hcmem
  simp only [smul_eq_mul] at hr
  have ht : ∀ b ∈ s.image (algebraMap A R), ∃ t, b = t * c := by
    intro b hb
    obtain ⟨a, has, rfl⟩ := Finset.mem_image.1 hb
    have : algebraMap A R a ∈ Ideal.span {c} := by
      rw [← h]; exact Ideal.mem_map_of_mem _ (hs ▸ Ideal.subset_span has)
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨t, ht.symm⟩
  choose! t ht using ht
  have hsum : (∑ b ∈ s.image (algebraMap A R), r b * t b) * c = c := by
    conv_rhs => rw [← hr]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [mul_assoc, ← ht b hb]
  have hunit : IsUnit (∑ b ∈ s.image (algebraMap A R), r b * t b) := by
    by_contra hnu
    have h1 : IsUnit (1 - ∑ b ∈ s.image (algebraMap A R), r b * t b) := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (∑ b ∈ s.image (algebraMap A R), r b * t b)
        with h | h
      · exact absurd h hnu
      · exact h
    apply hc
    have : (1 - ∑ b ∈ s.image (algebraMap A R), r b * t b) * c = 0 := by
      rw [sub_mul, one_mul, hsum, sub_self]
    exact (h1.mul_right_eq_zero).1 this
  obtain ⟨b, hb, hbu⟩ : ∃ b ∈ s.image (algebraMap A R), IsUnit (t b) := by
    by_contra hno
    push Not at hno
    have hm : (∑ b ∈ s.image (algebraMap A R), r b * t b) ∈ IsLocalRing.maximalIdeal R :=
      Ideal.sum_mem _ fun b hb =>
        Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hno b hb))
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hunit
  obtain ⟨a, has, rfl⟩ := Finset.mem_image.1 hb
  refine ⟨a, hs ▸ Ideal.subset_span has, hdesc a (hs ▸ Ideal.subset_span has) ?_⟩
  rw [ht _ hb, Ideal.span_singleton_mul_left_unit hbu]

/-- An element `s` regular modulo `J` stays regular modulo `J R` after a flat base change. -/
theorem mem_map_of_algebraMap_mul_mem_map {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Module.Flat A R] (J : Ideal A) {s : A} (hs : ∀ a, s * a ∈ J → a ∈ J) {c : R}
    (h : algebraMap A R s * c ∈ J.map (algebraMap A R)) : c ∈ J.map (algebraMap A R) := by
  set e := Ideal.qoutMapEquivTensorQout R (I := J)
  have hinj : Function.Injective (LinearMap.lsmul A (A ⧸ J) s) := by
    intro x y hxy
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    induction y using Submodule.Quotient.induction_on with | H b => ?_
    simp only [LinearMap.lsmul_apply] at hxy
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq] at hxy
    rw [Submodule.Quotient.eq]
    exact hs _ (by rw [mul_sub]; simpa [smul_eq_mul] using hxy)
  have hinj' := Module.Flat.lTensor_preserves_injective_linearMap (M := R) _ hinj
  have hcomm : ∀ y : R ⧸ J.map (algebraMap A R),
      e (algebraMap A R s • y) = (LinearMap.lTensor R (LinearMap.lsmul A (A ⧸ J) s)) (e y) := by
    intro y
    rw [map_smul]
    induction e y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [LinearMap.lTensor_tmul, LinearMap.lsmul_apply, ← TensorProduct.smul_tmul,
        TensorProduct.smul_tmul', algebraMap_smul]
    | add x y hx hy => rw [smul_add, map_add, hx, hy]
  have h0 : e (Ideal.Quotient.mk _ c) = 0 := by
    apply hinj'
    rw [← hcomm, map_zero, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact e.injective (h0.trans e.map_zero.symm)

/-- **Membership in the extension of a symbolic power.** In the setting of the valuation-theoretic
class group argument: `A → R` with `R` a domain whose height-one valuations `ord_Z` satisfy
Hartogs, `v_B` a discrete valuation on `A` with uniformizer `π` and factorizations
`s a = π^{v_B a} b`, and `J = {a | v_B a ≥ c}`. If `z ∈ R` has `ord_Z z ≥ c · ord_Z π` along every
component `Z` lying over `B`, then `z ∈ J R`. -/
theorem mem_map_of_ord_le {A R K ι : Type*} [CommRing A] [IsDomain A] [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Algebra A R]
    (ord : ι → K → ℤ)
    (hmul : ∀ Z (x y : K), x ≠ 0 → y ≠ 0 → ord Z (x * y) = ord Z x + ord Z y)
    (hnn : ∀ Z (r : R), r ≠ 0 → 0 ≤ ord Z (algebraMap R K r))
    (hH : ∀ z : K, z ≠ 0 → (∀ Z, 0 ≤ ord Z z) → ∃ r : R, algebraMap R K r = z)
    (hfin : ∀ y : R, y ≠ 0 → Set.Finite {Z | ord Z (algebraMap R K y) ≠ 0})
    (hinj : ∀ a : A, a ≠ 0 → algebraMap A R a ≠ 0)
    (vB : A → ℕ) (hvBmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → vB (a * b) = vB a + vB b)
    (π : A) (hπ : π ≠ 0) (hvBπ : vB π = 1)
    (hfact : ∀ a : A, a ≠ 0 → ∃ s b : A, s ≠ 0 ∧ b ≠ 0 ∧ vB s = 0 ∧ vB b = 0 ∧
      s * a = π ^ vB a * b)
    (hcancel : ∀ (J : Ideal A) (s : A), (∀ a, s * a ∈ J → a ∈ J) → ∀ c : R,
      algebraMap A R s * c ∈ J.map (algebraMap A R) → c ∈ J.map (algebraMap A R))
    (c : ℕ) (J : Ideal A) (hJ : ∀ a, a ∈ J ↔ a = 0 ∨ c ≤ vB a) (z : R) (hz0 : z ≠ 0)
    (hz : ∀ Z, (∀ a : A, a ≠ 0 →
        (0 < ord Z (algebraMap R K (algebraMap A R a)) ↔ 0 < vB a)) →
      (c : ℤ) * ord Z (algebraMap R K (algebraMap A R π)) ≤ ord Z (algebraMap R K z)) :
    z ∈ J.map (algebraMap A R) := by
  classical
  set φ := algebraMap A R
  set κ := algebraMap R K
  have hκ : ∀ r : R, r ≠ 0 → κ r ≠ 0 := fun r hr =>
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hr
  have hφκ : ∀ a : A, a ≠ 0 → κ (φ a) ≠ 0 := fun a ha => hκ _ (hinj a ha)
  have hpow : ∀ Z (x : K), x ≠ 0 → ∀ n : ℕ, ord Z (x ^ n) = n * ord Z x := by
    intro Z x hx n
    induction n with
    | zero =>
      have h1 := hmul Z 1 1 one_ne_zero one_ne_zero
      simp only [mul_one] at h1
      simp; omega
    | succ n ih =>
      rw [pow_succ, hmul Z _ _ (pow_ne_zero _ hx) hx, ih]; push_cast; ring
  have hord1 : ∀ Z, ord Z 1 = 0 := fun Z => by
    have h1 := hmul Z 1 1 one_ne_zero one_ne_zero
    simp only [mul_one] at h1; omega
  have hinv : ∀ Z (x : K), x ≠ 0 → ord Z x⁻¹ = - ord Z x := fun Z x hx => by
    have := hmul Z x x⁻¹ hx (inv_ne_zero hx)
    rw [mul_inv_cancel₀ hx, hord1] at this
    omega
  have hφmul : ∀ Z (a b : A), a ≠ 0 → b ≠ 0 →
      ord Z (κ (φ (a * b))) = ord Z (κ (φ a)) + ord Z (κ (φ b)) := fun Z a b ha hb => by
    rw [map_mul, map_mul]
    exact hmul Z _ _ (hφκ a ha) (hφκ b hb)
  have hφnn : ∀ Z (a : A), a ≠ 0 → 0 ≤ ord Z (κ (φ a)) := fun Z a ha => hnn Z _ (hinj a ha)
  have hφpow : ∀ Z (a : A), a ≠ 0 → ∀ n : ℕ, ord Z (κ (φ (a ^ n))) = n * ord Z (κ (φ a)) := by
    intro Z a ha n
    rw [map_pow, map_pow]
    exact hpow Z _ (hφκ a ha) n
  let Over : ι → Prop := fun Z => ∀ a : A, a ≠ 0 → (0 < ord Z (κ (φ a)) ↔ 0 < vB a)
  set F := (hfin _ (hinj π hπ)).toFinset.filter fun Z => ¬ Over Z
  have hsZ : ∀ Z ∈ F, ∃ s : A, s ≠ 0 ∧ vB s = 0 ∧ 0 < ord Z (κ (φ s)) := by
    intro Z hZ
    simp only [F, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hZ
    obtain ⟨hπZ, hnO⟩ := hZ
    simp only [Over, not_forall] at hnO
    obtain ⟨a, ha, hiff⟩ := hnO
    by_cases hva : vB a = 0
    · refine ⟨a, ha, hva, ?_⟩
      by_contra hle
      exact hiff ⟨fun h => absurd h hle, fun h => by omega⟩
    · obtain ⟨s, b, hs, hb, hvs, hvb, hsab⟩ := hfact a ha
      refine ⟨s, hs, hvs, ?_⟩
      have e := congrArg (fun t => ord Z (κ (φ t))) hsab
      rw [hφmul Z _ _ hs ha, hφmul Z _ _ (pow_ne_zero _ hπ) hb, hφpow Z _ hπ] at e
      have h0 : ord Z (κ (φ a)) = 0 := by
        have := hφnn Z a ha
        by_contra hne
        exact hiff ⟨fun _ => by omega, fun _ => by omega⟩
      have h1 := hφnn Z π hπ
      have h2 := hφnn Z b hb
      have h3 : (1 : ℤ) ≤ vB a := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hva
      have h4 : (1 : ℤ) ≤ ord Z (κ (φ π)) := by omega
      have h5 : (1 : ℤ) ≤ (vB a : ℤ) * ord Z (κ (φ π)) := by nlinarith
      omega
  choose! s' hs'0 hs'v hs'ord using hsZ
  have hprod : ∀ (T : Finset ι) (f : ι → A), (∀ i ∈ T, f i ≠ 0) →
      (∏ i ∈ T, f i) ≠ 0 ∧ vB (∏ i ∈ T, f i) = ∑ i ∈ T, vB (f i) ∧
      ∀ Z, ord Z (κ (φ (∏ i ∈ T, f i))) = ∑ i ∈ T, ord Z (κ (φ (f i))) := by
    intro T f hf
    induction T using Finset.induction_on with
    | empty =>
      refine ⟨one_ne_zero, ?_, fun Z => ?_⟩
      · have := hvBmul 1 1 one_ne_zero one_ne_zero
        simp only [mul_one] at this
        simp
        omega
      · simp [hord1]
    | insert i T hi ih =>
      obtain ⟨h0, h1, h2⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hfi := hf i (Finset.mem_insert_self i T)
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      refine ⟨mul_ne_zero hfi h0, by rw [hvBmul _ _ hfi h0, h1], fun Z => ?_⟩
      rw [Finset.sum_insert hi, hφmul Z _ _ hfi h0, h2]
  have hvBpow : ∀ a : A, a ≠ 0 → ∀ n : ℕ, vB (a ^ n) = n * vB a := by
    intro a ha n
    induction n with
    | zero =>
      have := hvBmul 1 1 one_ne_zero one_ne_zero
      simp only [mul_one] at this; simp; omega
    | succ n ih => rw [pow_succ, hvBmul _ _ (pow_ne_zero _ ha) ha, ih]; ring
  set N : ι → ℕ := fun Z => c * (ord Z (κ (φ π))).toNat
  set s : A := ∏ Z ∈ F, s' Z ^ N Z
  obtain ⟨hs0, hvs, hords⟩ := hprod F (fun Z => s' Z ^ N Z) fun Z hZ => pow_ne_zero _ (hs'0 Z hZ)
  have hvs0 : vB s = 0 := by
    rw [hvs]; exact Finset.sum_eq_zero fun Z hZ => by rw [hvBpow _ (hs'0 Z hZ), hs'v Z hZ, mul_zero]
  have hordsZ : ∀ Z, 0 ≤ ord Z (κ (φ s)) := fun Z => hφnn Z s hs0
  have hordsF : ∀ Z ∈ F, (c : ℤ) * ord Z (κ (φ π)) ≤ ord Z (κ (φ s)) := by
    intro Z hZ
    rw [hords Z]
    have hterm : ∀ Z' ∈ F, 0 ≤ ord Z (κ (φ (s' Z' ^ N Z'))) := fun Z' hZ' =>
      hφnn Z _ (pow_ne_zero _ (hs'0 Z' hZ'))
    refine le_trans ?_ (Finset.single_le_sum hterm hZ)
    rw [hφpow Z _ (hs'0 Z hZ)]
    have h1 := hs'ord Z hZ
    have h2 := hφnn Z π hπ
    simp only [N]
    push_cast
    rw [Int.toNat_of_nonneg h2]
    have h3 : (0 : ℤ) ≤ c * ord Z (κ (φ π)) := mul_nonneg (Nat.cast_nonneg c) h2
    nlinarith
  have hOver0 : ∀ Z, Over Z → ∀ a : A, a ≠ 0 → vB a = 0 → ord Z (κ (φ a)) = 0 := by
    intro Z hO a ha hva
    have := hφnn Z a ha
    by_contra hne
    have := (hO a ha).1 (by omega)
    omega
  have hπc : π ^ c ∈ J := (hJ _).2 (Or.inr (by rw [hvBpow _ hπ, hvBπ, mul_one]))
  have hzK : κ z ≠ 0 := hκ z hz0
  have hw0 : κ (φ s) * κ z * (κ (φ π) ^ c)⁻¹ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hφκ s hs0) hzK) (inv_ne_zero (pow_ne_zero _ (hφκ π hπ)))
  obtain ⟨r, hr⟩ := hH _ hw0 fun Z => by
    rw [hmul Z _ _ (mul_ne_zero (hφκ s hs0) hzK) (inv_ne_zero (pow_ne_zero _ (hφκ π hπ))),
      hmul Z _ _ (hφκ s hs0) hzK, hinv Z _ (pow_ne_zero _ (hφκ π hπ)), hpow Z _ (hφκ π hπ)]
    have hzZ := hnn Z z hz0
    by_cases hO : Over Z
    · have := hz Z hO
      rw [hOver0 Z hO s hs0 hvs0]; linarith
    · by_cases hπZ : ord Z (κ (φ π)) = 0
      · rw [hπZ]; have := hordsZ Z; linarith
      · have hZF : Z ∈ F := by
          simp only [F, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
          exact ⟨hπZ, hO⟩
        have := hordsF Z hZF; linarith
  have hsz : φ s * z = φ (π ^ c) * r := by
    apply IsFractionRing.injective R K
    have hne := pow_ne_zero c (hφκ π hπ)
    rw [map_mul, map_mul, hr]
    change κ (φ s) * κ z = κ (φ (π ^ c)) * _
    rw [map_pow, map_pow, mul_comm (κ (φ π) ^ c), inv_mul_cancel_right₀ hne]
  refine hcancel J s (fun a ha => ?_) z ?_
  · rcases (hJ _).1 ha with h | h
    · exact (hJ a).2 (Or.inl ((mul_eq_zero.1 h).resolve_left hs0))
    · by_cases ha0 : a = 0
      · exact (hJ a).2 (Or.inl ha0)
      · rw [hvBmul _ _ hs0 ha0, hvs0, zero_add] at h
        exact (hJ a).2 (Or.inr h)
  · rw [hsz]; exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπc)

/-- **Principality of the extended symbolic power.** Let `A → R` be a ring map into a domain
`R` whose height-one valuations `ord_Z` satisfy Hartogs and kill every divisor class by `m`.
If `v_B` is a discrete valuation on `A` with uniformizer `π` and factorizations
`s a = π^{v_B a} b`, then the extension of `J = {a | v_B a ≥ m}` to `R` is principal. -/
theorem exists_map_eq_span_of_ord {A R K ι : Type*} [CommRing A] [IsDomain A] [CommRing R]
    [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Algebra A R]
    (ord : ι → K → ℤ)
    (hmul : ∀ Z (x y : K), x ≠ 0 → y ≠ 0 → ord Z (x * y) = ord Z x + ord Z y)
    (hnn : ∀ Z (r : R), r ≠ 0 → 0 ≤ ord Z (algebraMap R K r))
    (hH : ∀ z : K, z ≠ 0 → (∀ Z, 0 ≤ ord Z z) → ∃ r : R, algebraMap R K r = z)
    (hfin : ∀ y : R, y ≠ 0 → Set.Finite {Z | ord Z (algebraMap R K y) ≠ 0})
    (m : ℕ)
    (hcl : ∀ y : R, y ≠ 0 → ∀ W : ι → ℤ, (∀ Z, W Z ≠ 0 → ord Z (algebraMap R K y) ≠ 0) →
      ∃ c : K, c ≠ 0 ∧ ∀ Z, ord Z c = m * W Z)
    (hinj : ∀ a : A, a ≠ 0 → algebraMap A R a ≠ 0)
    (vB : A → ℕ) (hvBmul : ∀ a b : A, a ≠ 0 → b ≠ 0 → vB (a * b) = vB a + vB b)
    (π : A) (hπ : π ≠ 0) (hvBπ : vB π = 1)
    (hfact : ∀ a : A, a ≠ 0 → ∃ s b : A, s ≠ 0 ∧ b ≠ 0 ∧ vB s = 0 ∧ vB b = 0 ∧
      s * a = π ^ vB a * b)
    (hcancel : ∀ (J : Ideal A) (s : A), (∀ a, s * a ∈ J → a ∈ J) → ∀ c : R,
      algebraMap A R s * c ∈ J.map (algebraMap A R) → c ∈ J.map (algebraMap A R))
    (J : Ideal A) (hJ : ∀ a, a ∈ J ↔ a = 0 ∨ m ≤ vB a) :
    ∃ c : R, J.map (algebraMap A R) = Ideal.span {c} := by
  classical
  set φ := algebraMap A R
  set κ := algebraMap R K
  have hκ : ∀ r : R, r ≠ 0 → κ r ≠ 0 := fun r hr =>
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hr
  have hφκ : ∀ a : A, a ≠ 0 → κ (φ a) ≠ 0 := fun a ha => hκ _ (hinj a ha)
  have hpow : ∀ Z (x : K), x ≠ 0 → ∀ n : ℕ, ord Z (x ^ n) = n * ord Z x := by
    intro Z x hx n
    induction n with
    | zero =>
      have h1 := hmul Z 1 1 one_ne_zero one_ne_zero
      simp only [mul_one] at h1
      simp; omega
    | succ n ih =>
      rw [pow_succ, hmul Z _ _ (pow_ne_zero _ hx) hx, ih]; push_cast; ring
  have hord1 : ∀ Z, ord Z 1 = 0 := fun Z => by
    have h1 := hmul Z 1 1 one_ne_zero one_ne_zero
    simp only [mul_one] at h1; omega
  have hinv : ∀ Z (x : K), x ≠ 0 → ord Z x⁻¹ = - ord Z x := fun Z x hx => by
    have := hmul Z x x⁻¹ hx (inv_ne_zero hx)
    rw [mul_inv_cancel₀ hx, hord1] at this
    omega
  have hφmul : ∀ Z (a b : A), a ≠ 0 → b ≠ 0 →
      ord Z (κ (φ (a * b))) = ord Z (κ (φ a)) + ord Z (κ (φ b)) := fun Z a b ha hb => by
    rw [map_mul, map_mul]
    exact hmul Z _ _ (hφκ a ha) (hφκ b hb)
  have hφnn : ∀ Z (a : A), a ≠ 0 → 0 ≤ ord Z (κ (φ a)) := fun Z a ha => hnn Z _ (hinj a ha)
  have hφpow : ∀ Z (a : A), a ≠ 0 → ∀ n : ℕ, ord Z (κ (φ (a ^ n))) = n * ord Z (κ (φ a)) := by
    intro Z a ha n
    rw [map_pow, map_pow]
    exact hpow Z _ (hφκ a ha) n
  let Over : ι → Prop := fun Z => ∀ a : A, a ≠ 0 → (0 < ord Z (κ (φ a)) ↔ 0 < vB a)
  let W : ι → ℤ := fun Z => if Over Z then ord Z (κ (φ π)) else 0
  have hW : ∀ Z, W Z ≠ 0 → ord Z (κ (φ π)) ≠ 0 := fun Z hZ => by
    simp only [W] at hZ; split_ifs at hZ; exacts [hZ, absurd rfl hZ]
  obtain ⟨c0, hc0, hc0ord⟩ := hcl (φ π) (hinj π hπ) W hW
  have hOver0 : ∀ Z, Over Z → ∀ a : A, a ≠ 0 → vB a = 0 → ord Z (κ (φ a)) = 0 := by
    intro Z hO a ha hva
    have := hφnn Z a ha
    by_contra hne
    have := (hO a ha).1 (by omega)
    omega
  have hJord : ∀ a : A, a ≠ 0 → m ≤ vB a → ∀ Z, (m : ℤ) * W Z ≤ ord Z (κ (φ a)) := by
    intro a ha hma Z
    simp only [W]
    split_ifs with hO
    · obtain ⟨t, b, ht, hb, hvt, hvb, htab⟩ := hfact a ha
      have e := congrArg (fun x => ord Z (κ (φ x))) htab
      rw [hφmul Z _ _ ht ha, hφmul Z _ _ (pow_ne_zero _ hπ) hb, hφpow Z _ hπ,
        hOver0 Z hO t ht hvt] at e
      have h1 := hφnn Z π hπ
      have h2 := hφnn Z b hb
      have h3 : (m : ℤ) ≤ vB a := by exact_mod_cast hma
      nlinarith
    · rw [mul_zero]; exact hφnn Z a ha
  have hW0 : ∀ Z, 0 ≤ W Z := fun Z => by
    simp only [W]; split_ifs
    · exact hφnn Z π hπ
    · exact le_rfl
  obtain ⟨c, hc⟩ := hH c0 hc0 fun Z => by rw [hc0ord]; exact mul_nonneg (by positivity) (hW0 Z)
  have hcne : c ≠ 0 := by rintro rfl; exact hc0 (by rw [← hc, map_zero])
  refine ⟨c, le_antisymm ?_ ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    rcases (hJ a).1 ha with rfl | hma
    · rw [map_zero]; exact zero_mem _
    by_cases ha0 : a = 0
    · rw [ha0, map_zero]; exact zero_mem _
    obtain ⟨t, ht⟩ := hH (κ (φ a) * c0⁻¹) (mul_ne_zero (hφκ a ha0) (inv_ne_zero hc0))
      fun Z => by
        rw [hmul Z _ _ (hφκ a ha0) (inv_ne_zero hc0), hinv Z _ hc0, hc0ord]
        have := hJord a ha0 hma Z; omega
    refine Ideal.mem_span_singleton'.2 ⟨t, IsFractionRing.injective R K ?_⟩
    rw [map_mul, ht, hc, inv_mul_cancel_right₀ hc0]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    refine mem_map_of_ord_le ord hmul hnn hH hfin hinj vB hvBmul π hπ hvBπ hfact hcancel m J hJ c
      hcne fun Z hO => ?_
    change (m : ℤ) * ord Z (κ (φ π)) ≤ ord Z (κ c)
    rw [hc, hc0ord]
    simp only [W]
    split_ifs with h
    · exact le_rfl
    · exact absurd hO h

universe v

section

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- An element of the stalk at a point of a prime divisor has nonnegative order along it. -/
theorem ord_nonneg_of_mem_support (Z : MMP.Mori.PrimeDivisor Y) {x : Y}
    (hx : x ∈ Z.support) (r : Y.presheaf.stalk x) :
    0 ≤ Y.ord (algebraMap _ Y.functionField r) Z.genericPoint := by
  have hsp : Z.genericPoint ⤳ x := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
    exact specializes_iff_mem_closure.2 hx
  rw [← MMP.Mori.algebraMap_stalkSpecializes hsp r]
  set a := (Y.presheaf.stalkSpecializes hsp).hom r
  by_cases ha : algebraMap _ Y.functionField a = 0
  · rw [ha, Scheme.ord_zero]; rfl
  have h := (MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff Z _).mpr ⟨a, rfl⟩
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord Z ha, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h
  omega

/-- On a quasi-compact scheme a rational function has nonzero order along finitely many prime
divisors. -/
theorem finite_ord_ne_zero [CompactSpace Y] {g : Y.functionField} :
    Set.Finite {Z : MMP.Mori.PrimeDivisor Y | Y.ord g Z.genericPoint ≠ 0} := by
  have h := (AlgebraicGeometry.mem_weilDivisor_iff _).1 (AlgebraicGeometry.ord_mem_weilDivisor Y g)
  refine (h.finite_nonempty_of_compact).subset fun Z hZ => ?_
  simp only [Set.mem_setOf_eq] at hZ ⊢
  rw [if_neg hZ]
  exact ⟨Z.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support Z⟩

/-- If the class group is killed by `m`, then `m W` is the divisor of a rational function for
every Weil divisor `W` supported in the support of `div g`. -/
theorem exists_ord_eq_mul_of_nsmul_eq_zero (m : ℕ)
    (htor : ∀ D : AlgebraicGeometry.WeilDivisor Y, m • (D : weilDivisorClassGroup Y) = 0)
    (g : Y.functionField) (W : MMP.Mori.PrimeDivisor Y → ℤ)
    (hW : ∀ Z, W Z ≠ 0 → Y.ord g Z.genericPoint ≠ 0) :
    ∃ c : Y.functionField, c ≠ 0 ∧ ∀ Z : MMP.Mori.PrimeDivisor Y,
      Y.ord c Z.genericPoint = m * W Z := by
  have hWmem : W ∈ AlgebraicGeometry.WeilDivisor Y := by
    rw [AlgebraicGeometry.mem_weilDivisor_iff]
    have h :=
      (AlgebraicGeometry.mem_weilDivisor_iff _).1 (AlgebraicGeometry.ord_mem_weilDivisor Y g)
    refine h.subset fun Z => ?_
    by_cases hZ : W Z = 0
    · simp [hZ]
    · have := hW Z hZ
      simp only [hZ, if_false]
      rw [if_neg this]
  obtain ⟨f, hf⟩ := (AlgebraicGeometry.mk_eq_zero_iff Y _).1
    (show ((m • (⟨W, hWmem⟩ : AlgebraicGeometry.WeilDivisor Y) : AlgebraicGeometry.WeilDivisor Y) :
      weilDivisorClassGroup Y) = 0 by rw [QuotientAddGroup.mk_nsmul]; exact htor _)
  refine ⟨(Stacks.Chow.rationalFunctionsEquivFunctionField Y).1 f, ?_, fun Z => ?_⟩
  · exact (f.isUnit.map (Stacks.Chow.rationalFunctionsEquivFunctionField Y).1).ne_zero
  · have := congrArg (fun D : AlgebraicGeometry.WeilDivisor Y => (D : _ → ℤ) Z) hf
    simp only [AlgebraicGeometry.principalDivisor_apply] at this
    rw [this]
    simp

end

/-- A cyclic group generated by an element of order `m` is killed by `m`. -/
theorem nsmul_eq_zero_of_zmultiples_eq_top {G : Type*} [AddCommGroup G] {D : G} {m : ℕ}
    (hD : addOrderOf D = m) (htop : AddSubgroup.zmultiples D = ⊤) (x : G) : m • x = 0 := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (htop ▸ AddSubgroup.mem_top x)
  rw [smul_comm, ← hD, addOrderOf_nsmul_eq_zero, smul_zero]

section ASide

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {x : X} (B : MMP.Mori.PrimeDivisor X) (hxB : x ∈ B.support)

include hxB in
/-- A rational function regular along `B` is `b / s` with `b, s ∈ 𝒪_{X,x}` and `s` a unit
along `B`. -/
theorem exists_mul_eq_of_ord_nonneg {z : X.functionField} (hz : z ≠ 0)
    (h : 0 ≤ X.ord z B.genericPoint) :
    ∃ b s : X.presheaf.stalk x, s ≠ 0 ∧
      X.ord (algebraMap _ X.functionField s) B.genericPoint = 0 ∧
      algebraMap _ X.functionField b = z * algebraMap _ X.functionField s := by
  have hsp : B.genericPoint ⤳ x := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxB
    exact specializes_iff_mem_closure.2 hxB
  have hv : B.divisorialValuation z ≤ 1 := by
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord B hz, ← WithZero.exp_zero,
      WithZero.exp_le_exp]; omega
  obtain ⟨w, hw⟩ := (MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff B z).1 hv
  letI := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have hloc := MMP.Intersection.isLocalization_stalkSpecializes hsp
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk B.genericPoint)).comap
      (X.presheaf.stalkSpecializes hsp).hom).primeCompl w
  have hsu : IsUnit ((X.presheaf.stalkSpecializes hsp).hom (s : X.presheaf.stalk x)) := by
    by_contra hn
    exact s.2 ((IsLocalRing.mem_maximalIdeal _).2 hn)
  refine ⟨b, s, fun h0 => ?_, ?_, ?_⟩
  · rw [h0, map_zero] at hsu; exact not_isUnit_zero hsu
  · rw [← MMP.Mori.algebraMap_stalkSpecializes hsp]
    exact B.ord_algebraMap_of_isUnit hsu
  · rw [← hw, ← MMP.Mori.algebraMap_stalkSpecializes hsp (s : X.presheaf.stalk x),
      ← MMP.Mori.algebraMap_stalkSpecializes hsp b]
    change _ = algebraMap (X.presheaf.stalk B.genericPoint) X.functionField _ * _
    rw [← map_mul]
    congr 1
    exact (IsLocalization.mk'_spec _ b s).symm

include hxB in
/-- The stalk at a point of `B` contains an element of order one along `B`. -/
theorem exists_ord_eq_one_stalk :
    ∃ π : X.presheaf.stalk x, π ≠ 0 ∧
      X.ord (algebraMap _ X.functionField π) B.genericPoint = 1 := by
  have := B.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B.localRing
  have hne : algebraMap B.localRing X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  have h1 : X.ord (algebraMap B.localRing X.functionField ϖ) B.genericPoint = 1 := by
    rw [Scheme.ord_eq_iff B.coheight_genericPoint hne]
    exact Ring.ordFrac_irreducible (R := X.presheaf.stalk B.genericPoint) hϖ
  obtain ⟨b, s, hs, hs0, hb⟩ := exists_mul_eq_of_ord_nonneg B hxB hne (by omega)
  have hsK : algebraMap _ X.functionField s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hs
  refine ⟨b, fun h0 => ?_, ?_⟩
  · rw [h0, map_zero] at hb
    exact mul_ne_zero hne hsK hb.symm
  · rw [hb, Scheme.ord_mul hne hsK, h1, hs0, add_zero]

include hxB in
/-- Factorization along `B` in `𝒪_{X,x}`: `s a = π^{ord_B a} b` with `s, b` units along `B`. -/
theorem exists_mul_eq_pow_mul {π a : X.presheaf.stalk x} (hπ : π ≠ 0)
    (hπ1 : X.ord (algebraMap _ X.functionField π) B.genericPoint = 1) (ha : a ≠ 0) :
    ∃ s b : X.presheaf.stalk x, s ≠ 0 ∧ b ≠ 0 ∧
      X.ord (algebraMap _ X.functionField s) B.genericPoint = 0 ∧
      X.ord (algebraMap _ X.functionField b) B.genericPoint = 0 ∧
      s * a = π ^ (X.ord (algebraMap _ X.functionField a) B.genericPoint).toNat * b := by
  set n := (X.ord (algebraMap _ X.functionField a) B.genericPoint).toNat
  have hn : (n : ℤ) = X.ord (algebraMap _ X.functionField a) B.genericPoint :=
    Int.toNat_of_nonneg (ord_nonneg_of_mem_support B hxB a)
  have inj := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  have haK : algebraMap _ X.functionField a ≠ 0 := (map_ne_zero_iff _ inj).mpr ha
  have hπK : algebraMap _ X.functionField π ≠ 0 := (map_ne_zero_iff _ inj).mpr hπ
  have hpK : algebraMap _ X.functionField π ^ n ≠ 0 := pow_ne_zero _ hπK
  have hz : algebraMap _ X.functionField a * (algebraMap _ X.functionField π ^ n)⁻¹ ≠ 0 :=
    mul_ne_zero haK (inv_ne_zero hpK)
  have hpow : X.ord (algebraMap _ X.functionField π ^ n) B.genericPoint = n := by
    rw [← zpow_natCast, MMP.Mori.ord_zpow _ hπK, hπ1, mul_one]
  have hzord : X.ord (algebraMap _ X.functionField a * (algebraMap _ X.functionField π ^ n)⁻¹)
      B.genericPoint = 0 := by
    have := Scheme.ord_mul (x := B.genericPoint) hpK (inv_ne_zero hpK)
    rw [mul_inv_cancel₀ hpK, Aux.ord_one'] at this
    rw [Scheme.ord_mul haK (inv_ne_zero hpK)]
    omega
  obtain ⟨b, s, hs, hs0, hb⟩ := exists_mul_eq_of_ord_nonneg B hxB hz hzord.ge
  have hsK : algebraMap _ X.functionField s ≠ 0 := (map_ne_zero_iff _ inj).mpr hs
  have hbK : algebraMap _ X.functionField b ≠ 0 := by
    rw [hb]
    exact mul_ne_zero hz hsK
  refine ⟨s, b, hs, fun h0 => hbK (by rw [h0, map_zero]), hs0, ?_, inj ?_⟩
  · rw [hb, Scheme.ord_mul hz hsK, hzord, hs0, add_zero]
  · rw [map_mul, map_mul, map_pow, hb]
    field_simp

/-- The `B`-adic ideal `{a | ord_B a ≥ m}` of `𝒪_{X,x}`. -/
noncomputable def ordIdeal (m : ℕ) (hxB : x ∈ B.support) : Ideal (X.presheaf.stalk x) where
  carrier := {a | B.divisorialValuation (algebraMap _ X.functionField a) ≤ WithZero.exp (-(m : ℤ))}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (Valuation.map_add _ _ _).trans (max_le ha hb)
  smul_mem' r a ha := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
    have hr : B.divisorialValuation (algebraMap _ X.functionField r) ≤ 1 := by
      by_cases h0 : algebraMap _ X.functionField r = 0
      · rw [h0, map_zero]
        exact zero_le_one' _
      · rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord B h0, ← WithZero.exp_zero,
          WithZero.exp_le_exp]
        have := ord_nonneg_of_mem_support B hxB r
        omega
    exact (mul_le_of_le_one_left' hr).trans ha

include hxB in
/-- Membership in the `B`-adic ideal is the order condition `ord_B a ≥ m`. -/
theorem mem_ordIdeal_iff (m : ℕ) (a : X.presheaf.stalk x) :
    a ∈ ordIdeal B m hxB ↔
      a = 0 ∨ m ≤ (X.ord (algebraMap _ X.functionField a) B.genericPoint).toNat := by
  change B.divisorialValuation (algebraMap _ X.functionField a) ≤ _ ↔ _
  have inj := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  by_cases ha : a = 0
  · simp [ha]
  have haK : algebraMap _ X.functionField a ≠ 0 := (map_ne_zero_iff _ inj).mpr ha
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord B haK, WithZero.exp_le_exp]
  have := ord_nonneg_of_mem_support B hxB a
  simp only [ha, false_or]
  omega

end ASide

section Assembly

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **`m B` is principal at `x`.** If `𝒪_{X,x}` maps flatly and locally to a Noetherian normal
local domain whose class group is killed by `m`, then some `a ∈ 𝒪_{X,x}` has order `m` along
`B` and order zero along every other prime divisor through `x`. -/
theorem exists_ord_eq_of_flat (x : X) (R' : Type v) [CommRing R'] [IsDomain R'] [IsLocalRing R']
    [IsNoetherianRing R'] [IsIntegrallyClosed R'] (φ : X.presheaf.stalk x →+* R') (hφ : φ.Flat)
    [IsLocalHom φ] (m : ℕ)
    (htor : ∀ D : AlgebraicGeometry.WeilDivisor (Spec (.of R')),
      m • (D : weilDivisorClassGroup (Spec (.of R'))) = 0)
    (B : MMP.Mori.PrimeDivisor X) (hxB : x ∈ B.support) :
    ∃ a : X.presheaf.stalk x, a ≠ 0 ∧
      X.ord (algebraMap _ X.functionField a) B.genericPoint = m ∧
      ∀ E : MMP.Mori.PrimeDivisor X, x ∈ E.support → E ≠ B →
        X.ord (algebraMap _ X.functionField a) E.genericPoint = 0 := by
  classical
  set Y := Spec (CommRingCat.of R')
  haveI : IsNormal Y := isNormal_spec_of_isIntegrallyClosed R'
  set y0 : Y := IsLocalRing.closedPoint R'
  have hy0 : ∀ Z : MMP.Mori.PrimeDivisor Y, y0 ∈ Z.support := fun Z =>
    (IsLocalRing.specializes_closedPoint (R := R') Z.genericPoint).mem_closed
      (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure)
      (MMP.Flips.primeDivisor_genericPoint_mem_support Z)
  letI : Algebra R' (Y.presheaf.stalk y0) := StructureSheaf.stalkAlgebra R' y0
  haveI hloc : IsLocalization.AtPrime (Y.presheaf.stalk y0) (IsLocalRing.maximalIdeal R') :=
    StructureSheaf.IsLocalization.to_stalk R' y0
  have hflat2 : (algebraMap R' (Y.presheaf.stalk y0)).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat _ (IsLocalRing.maximalIdeal R').primeCompl
  haveI hlh2 : IsLocalHom (algebraMap R' (Y.presheaf.stalk y0)) := by
    refine ⟨fun r hr => ?_⟩
    have := (IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y0)
      (IsLocalRing.maximalIdeal R') r).1 hr
    by_contra hn
    exact this ((IsLocalRing.mem_maximalIdeal _).2 hn)
  set ψ : X.presheaf.stalk x →+* Y.presheaf.stalk y0 :=
    (algebraMap R' (Y.presheaf.stalk y0)).comp φ
  letI : Algebra (X.presheaf.stalk x) (Y.presheaf.stalk y0) := ψ.toAlgebra
  haveI : Module.Flat (X.presheaf.stalk x) (Y.presheaf.stalk y0) := by
    have : ψ.Flat := hφ.comp hflat2
    exact this
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk x) (Y.presheaf.stalk y0)) := by
    change IsLocalHom ((algebraMap R' (Y.presheaf.stalk y0)).comp φ)
    infer_instance
  haveI : Module.FaithfullyFlat (X.presheaf.stalk x) (Y.presheaf.stalk y0) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinjA : Function.Injective (algebraMap (X.presheaf.stalk x) (Y.presheaf.stalk y0)) :=
    FaithfulSMul.algebraMap_injective _ _
  have injA := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  obtain ⟨π, hπ, hπ1⟩ := exists_ord_eq_one_stalk B hxB
  set vB : X.presheaf.stalk x → ℕ :=
    fun a => (X.ord (algebraMap _ X.functionField a) B.genericPoint).toNat
  have hvBmul : ∀ a b : X.presheaf.stalk x, a ≠ 0 → b ≠ 0 → vB (a * b) = vB a + vB b := by
    intro a b ha hb
    simp only [vB]
    rw [map_mul, Scheme.ord_mul ((map_ne_zero_iff _ injA).2 ha) ((map_ne_zero_iff _ injA).2 hb)]
    exact Int.toNat_add (ord_nonneg_of_mem_support B hxB a) (ord_nonneg_of_mem_support B hxB b)
  have hvBπ : vB π = 1 := by simp only [vB, hπ1]; rfl
  have hfact : ∀ a : X.presheaf.stalk x, a ≠ 0 → ∃ s b : X.presheaf.stalk x, s ≠ 0 ∧ b ≠ 0 ∧
      vB s = 0 ∧ vB b = 0 ∧ s * a = π ^ vB a * b := by
    intro a ha
    obtain ⟨s, b, hs, hb, hs0, hb0, h⟩ := exists_mul_eq_pow_mul B hxB hπ hπ1 ha
    exact ⟨s, b, hs, hb, by simp [vB, hs0], by simp [vB, hb0], h⟩
  set J := ordIdeal B m hxB
  have hJ : ∀ a, a ∈ J ↔ a = 0 ∨ m ≤ vB a := mem_ordIdeal_iff B hxB m
  have hYfin : ∀ y : Y.presheaf.stalk y0, y ≠ 0 →
      Set.Finite {Z : MMP.Mori.PrimeDivisor Y |
        Y.ord (algebraMap _ Y.functionField y) Z.genericPoint ≠ 0} := fun _ _ => finite_ord_ne_zero
  obtain ⟨c, hc⟩ := exists_map_eq_span_of_ord (A := X.presheaf.stalk x)
    (R := Y.presheaf.stalk y0) (K := Y.functionField)
    (fun (Z : MMP.Mori.PrimeDivisor Y) z => Y.ord z Z.genericPoint)
    (fun Z _ _ hx hy => Scheme.ord_mul hx hy)
    (fun Z r _ => ord_nonneg_of_mem_support Z (hy0 Z) r)
    (fun z hz h => MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg y0 hz
      fun Γ _ => h Γ)
    hYfin m
    (fun y _ W hW => exists_ord_eq_mul_of_nsmul_eq_zero m htor _ W hW)
    (fun a ha h0 => ha (hinjA (h0.trans (map_zero _).symm)))
    vB hvBmul π hπ hvBπ hfact
    (fun J s hs c hc => mem_map_of_algebraMap_mul_mem_map J hs hc) J hJ
  obtain ⟨a, haJ, hJa⟩ := exists_eq_span_of_map_eq_span J hc
  have hvBpow : ∀ b : X.presheaf.stalk x, b ≠ 0 → ∀ n : ℕ, vB (b ^ n) = n * vB b := by
    intro b hb n
    induction n with
    | zero => simp [vB, Scheme.ord_one]
    | succ n ih => rw [pow_succ, hvBmul _ _ (pow_ne_zero _ hb) hb, ih]; ring
  have hπm : π ^ m ∈ J := (hJ _).2 (Or.inr (by rw [hvBpow _ hπ, hvBπ, mul_one]))
  rw [hJa] at hπm
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hπm
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ht
    exact pow_ne_zero m hπ ht.symm
  have ht0 : t ≠ 0 := by rintro rfl; rw [zero_mul] at ht; exact pow_ne_zero m hπ ht.symm
  have haK : algebraMap _ X.functionField a ≠ 0 := (map_ne_zero_iff _ injA).2 ha0
  refine ⟨a, ha0, ?_, fun E hxE hEB => ?_⟩
  · have h1 := ((hJ a).1 haJ).resolve_left ha0
    have h2 := congrArg vB ht
    rw [hvBmul _ _ ht0 ha0, hvBpow _ hπ, hvBπ, mul_one] at h2
    have h3 : vB a = m := by omega
    have := ord_nonneg_of_mem_support B hxB a
    simp only [vB] at h3
    omega
  · -- an element of `𝔭_B` off `𝔭_E`
    have hsB : B.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxB
      exact specializes_iff_mem_closure.2 hxB
    have hsE : E.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
      exact specializes_iff_mem_closure.2 hxE
    have hnle : ¬ MMP.Intersection.primeOfSpecializes hsB ≤
        MMP.Intersection.primeOfSpecializes hsE := by
      intro hle
      have hBE := MMP.Intersection.specializes_of_primeOfSpecializes_le hsB hsE hle
      refine hEB (MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support ?_).symm
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact specializes_iff_mem_closure.1 hBE
    obtain ⟨s, hsP, hsQ⟩ := Set.not_subset.1 hnle
    have hs0 : s ≠ 0 := by rintro rfl; exact hsQ (zero_mem _)
    have hsK : algebraMap _ X.functionField s ≠ 0 := (map_ne_zero_iff _ injA).2 hs0
    have hsE0 : X.ord (algebraMap _ X.functionField s) E.genericPoint = 0 := by
      rw [← MMP.Mori.algebraMap_stalkSpecializes hsE s]
      refine E.ord_algebraMap_of_isUnit ?_
      by_contra hn
      exact hsQ ((IsLocalRing.mem_maximalIdeal _).2 hn)
    have hsBpos : 0 < X.ord (algebraMap _ X.functionField s) B.genericPoint := by
      have hlt := (MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff B
        ((X.presheaf.stalkSpecializes hsB).hom s)).2 hsP
      rw [MMP.Mori.algebraMap_stalkSpecializes hsB s,
        MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord B hsK, ← WithZero.exp_zero,
        WithZero.exp_lt_exp] at hlt
      omega
    have hsm : s ^ m ∈ J := (hJ _).2 (Or.inr (by
      rw [hvBpow _ hs0]
      have : 1 ≤ vB s := by simp only [vB]; omega
      nlinarith))
    rw [hJa] at hsm
    obtain ⟨t', ht'⟩ := Ideal.mem_span_singleton'.1 hsm
    have ht'0 : t' ≠ 0 := by
      rintro rfl; rw [zero_mul] at ht'; exact pow_ne_zero m hs0 ht'.symm
    have ht'K : algebraMap _ X.functionField t' ≠ 0 := (map_ne_zero_iff _ injA).2 ht'0
    have e := congrArg (fun z => X.ord (algebraMap _ X.functionField z) E.genericPoint) ht'
    simp only [map_mul, map_pow] at e
    rw [Scheme.ord_mul ht'K haK, ← zpow_natCast, MMP.Mori.ord_zpow _ hsK, hsE0, mul_zero] at e
    have h1 := ord_nonneg_of_mem_support E hxE t'
    have h2 := ord_nonneg_of_mem_support E hxE a
    omega

end Assembly

section Final

open IsLocalRing MMP.Mori

/-- The stalks of a scheme locally of finite type over `k` are essentially of finite type. -/
theorem essFiniteType_stalk' {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (x : X) :
    letI := MMP.Mori.stalkAlgebra sX x
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  obtain ⟨W, hW, hpW, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.stalkAlgebra sX x
  let : Algebra Γ(X, W) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hpW⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hpW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hpW⟩
  have : IsScalarTower k Γ(X, W) (X.presheaf.stalk x) :=
    MMP.Mori.isScalarTower_section_stalk sX W ⟨x, hpW⟩
  have : Algebra.FiniteType k Γ(X, W) := MMP.Mori.finiteType_sectionAlgebra sX hW
  have : Algebra.EssFiniteType Γ(X, W) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization _ (hW.primeIdealOf ⟨x, hpW⟩).asIdeal.primeCompl
  exact Algebra.EssFiniteType.comp k Γ(X, W) _

/-- **`m B` is principal at a cyclic quotient point.** If the completed strict henselization of
`𝒪_{X,x}` is `K[[x, y]]^{μ_m}`, then `m B` has a local equation in `𝒪_{X,x}`, for every prime
divisor `B` through `x`. -/
theorem exists_stalk_ord_eq_of_cyclicInvariants {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [LocallyOfFiniteType sX] (x : X)
    (κsep : Type) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk x)) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk x)) κsep]
    (H : Type) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk x) H]
    [IsHenselization (X.presheaf.stalk x) κsep H]
    {K : Type*} [Field K] {m : ℕ} {q : ℤ} (hK : MMP.Flips.IsCyclicQuotientSetting K m q)
    (e : AdicCompletion (maximalIdeal H) H ≃+* MMP.Flips.cyclicInvariants K m q)
    (B : MMP.Mori.PrimeDivisor X) (hxB : x ∈ B.support) :
    ∃ a : X.presheaf.stalk x, a ≠ 0 ∧
      X.ord (algebraMap _ X.functionField a) B.genericPoint = m ∧
      ∀ E : MMP.Mori.PrimeDivisor X, x ∈ E.support → E ≠ B →
        X.ord (algebraMap _ X.functionField a) E.genericPoint = 0 := by
  letI := MMP.Mori.stalkAlgebra sX x
  haveI := essFiniteType_stalk' sX x
  haveI : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  obtain ⟨-, ⟨hlocAH, hffAH, -⟩, hlocR, -, ⟨hlocHR, hffHR, -⟩, -⟩ :=
    MMP.Foundations.isNoetherianRing_strictHenselization_adicCompletion k (X.presheaf.stalk x)
      κsep H
  obtain ⟨hR, hloc, hdom, hic, -, -, -, C, D, -, -, -, hord, htop⟩ :=
    MMP.Flips.exists_addEquiv_weilDivisorClassGroup_cyclicQuotientModel hK
  set φ : X.presheaf.stalk x →+* MMP.Flips.cyclicInvariants K m q :=
    e.toRingHom.comp ((algebraMap H (AdicCompletion (maximalIdeal H) H)).comp
      (algebraMap (X.presheaf.stalk x) H))
  have hφ : φ.Flat := by
    refine RingHom.Flat.comp (RingHom.Flat.comp ?_ ?_) (RingHom.Flat.of_bijective e.bijective)
    · rw [RingHom.flat_algebraMap_iff]; infer_instance
    · rw [RingHom.flat_algebraMap_iff]; infer_instance
  haveI : IsLocalHom e.toRingHom := ⟨fun a ha => by
    have := ha.map e.symm.toRingHom
    simpa using this⟩
  haveI : IsLocalHom ((algebraMap H (AdicCompletion (maximalIdeal H) H)).comp
      (algebraMap (X.presheaf.stalk x) H)) := @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ hlocHR hlocAH
  haveI : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  exact exists_ord_eq_of_flat x (MMP.Flips.cyclicInvariants K m q) φ hφ m
    (fun D' => nsmul_eq_zero_of_zmultiples_eq_top hord htop _) B hxB

end Final

/-! ### The local input at `P` -/

/-- The class-group descent at a point of `B`: with `𝔭 ⊂ 𝒪_{X,x}` the prime of `B`, the symbolic
power `𝔭^{(m)}` is principal, because its extension to the completed strict henselization `R` is
the divisorial ideal of `m D_R`, principal as `Cl(R) = ℤ/m`, and principality descends along the
faithfully flat local map `𝒪_{X,x} → R`. -/
theorem exists_forall_mem_support_coeff_eq_ord_of_mem {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [LocallyOfFiniteType sX] (x : X)
    (κsep : Type) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk x)) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk x)) κsep]
    (H : Type) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk x) H]
    [IsHenselization (X.presheaf.stalk x) κsep H]
    {K : Type*} [Field K] {m : ℕ} {q : ℤ} (hK : IsCyclicQuotientSetting K m q)
    (e : AdicCompletion (maximalIdeal H) H ≃+* cyclicInvariants K m q)
    (B : MMP.Mori.PrimeDivisor X) (hxB : x ∈ B.support) :
    ∃ φ : (RationalFunctions X)ˣ, ∀ E : MMP.Mori.PrimeDivisor X, x ∈ E.support →
      DivisorWithCoeffs.coeff ((m : ℤ) • Finsupp.single B (1 : ℤ)) E = E.ord φ := by
  classical
  obtain ⟨a, ha0, haB, haE⟩ :=
    exists_stalk_ord_eq_of_cyclicInvariants sX x κsep H hK e B hxB
  have hsp : ∀ Z : irreducibleComponents X, componentGenericPoint X Z ⤳ x := fun Z => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
    exact (genericPoint_spec X).specializes trivial
  have haK : algebraMap _ X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)).2 ha0
  set v : RationalFunctions X := fun Z => (X.presheaf.stalkSpecializes (hsp Z)).hom a
  have hvK : ∀ Z, (MMP.Positivity.componentToFunctionField Z).hom (v Z) =
      algebraMap _ X.functionField a := fun Z =>
    Aux.componentToFunctionField_stalkSpecializes X Z (hsp Z) a
  have hv : IsUnit v := by
    refine Pi.isUnit_iff.2 fun Z => ?_
    have hfield := RationalFunctions.isField_stalk X Z
    letI := hfield.toField
    refine isUnit_iff_ne_zero.2 fun h0 => haK ?_
    rw [← hvK Z]
    change (MMP.Positivity.componentToFunctionField Z).hom (v Z) = 0
    rw [show v Z = 0 from h0, map_zero]
  refine ⟨hv.unit, fun E hxE => ?_⟩
  rw [MMP.Positivity.ord_eq_ord_componentToFunctionField, IsUnit.unit_spec, hvK,
    DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  by_cases hEB : E = B
  · subst hEB
    rw [DivisorWithCoeffs.coeff_single_self, mul_one, haB]
  · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hEB), mul_zero, haE E hxE hEB]

/-- **Local Cartier index, pointwise.** At the point `x` whose completed strict henselization is
the cyclic quotient `K[[x, y]]^{μ_m}`, for every prime divisor `B` there is a rational function
whose order along each prime divisor through `x` is that of `m B`: the class group of the formal
cyclic quotient is `ℤ/m`, and `Cl(𝒪_{X,x}) → Cl(R)` is injective. -/
theorem exists_forall_mem_support_coeff_eq_ord {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [LocallyOfFiniteType sX] (x : X)
    (κsep : Type) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk x)) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk x)) κsep]
    (H : Type) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk x) H]
    [IsHenselization (X.presheaf.stalk x) κsep H]
    {K : Type*} [Field K] {m : ℕ} {q : ℤ} (hK : IsCyclicQuotientSetting K m q)
    (e : AdicCompletion (maximalIdeal H) H ≃+* cyclicInvariants K m q)
    (B : MMP.Mori.PrimeDivisor X) :
    ∃ φ : (RationalFunctions X)ˣ, ∀ E : MMP.Mori.PrimeDivisor X, x ∈ E.support →
      DivisorWithCoeffs.coeff ((m : ℤ) • Finsupp.single B (1 : ℤ)) E = E.ord φ := by
  by_cases hxB : x ∈ B.support
  · exact exists_forall_mem_support_coeff_eq_ord_of_mem sX x κsep H hK e B hxB
  · refine ⟨1, fun E hxE => ?_⟩
    have hEB : B ≠ E := by rintro rfl; exact hxB hxE
    rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_single_of_ne hEB, smul_zero,
      PrimeDivisor.ord_one]

/-- **`m D` is Cartier at a cyclic quotient point**, for every divisor `D`: the product of the
local equations of the `m E`, `E` a component of `D`. -/
theorem exists_forall_mem_support_coeff_nsmul_eq_ord {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [LocallyOfFiniteType sX] (x : X)
    (κsep : Type) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk x)) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk x)) κsep]
    (H : Type) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk x) H]
    [IsHenselization (X.presheaf.stalk x) κsep H]
    {K : Type*} [Field K] {m : ℕ} {q : ℤ} (hK : IsCyclicQuotientSetting K m q)
    (e : AdicCompletion (maximalIdeal H) H ≃+* cyclicInvariants K m q) (D : Divisor X) :
    ∃ φ : (RationalFunctions X)ˣ, ∀ E : MMP.Mori.PrimeDivisor X, x ∈ E.support →
      DivisorWithCoeffs.coeff ((m : ℤ) • D) E = E.ord φ := by
  classical
  choose ψ hψ using fun B : MMP.Mori.PrimeDivisor X =>
    exists_forall_mem_support_coeff_eq_ord sX x κsep H hK e B
  refine ⟨∏ B ∈ D.support, ψ B ^ D B, fun E hxE => ?_⟩
  have hord : E.ord (∏ B ∈ D.support, ψ B ^ D B) = ∑ B ∈ D.support, D B * E.ord (ψ B) := by
    simp only [PrimeDivisor.ord, map_prod, map_zpow, toAdd_prod, toAdd_zpow, smul_eq_mul]
  rw [hord]
  have hterm : ∀ B ∈ D.support, D B * E.ord (ψ B) = (m : ℤ) * (if B = E then D B else 0) := by
    intro B _
    rw [← hψ B E hxE, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    by_cases hBE : B = E
    · subst hBE; rw [DivisorWithCoeffs.coeff_single_self, if_pos rfl]; ring
    · rw [DivisorWithCoeffs.coeff_single_of_ne hBE, if_neg hBE]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_ite_eq' D.support E,
    DivisorWithCoeffs.coeff_smul, smul_eq_mul, DivisorWithCoeffs.coeff_apply]
  split_ifs with hE
  · rfl
  · rw [Finsupp.notMem_support_iff.1 hE]

/-- **Local Cartier index.** At such a point `m B` is Cartier, for every prime divisor `B`. -/
theorem exists_isLocalEquation_nsmul_single {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X]
    [LocallyOfFiniteType sX] (x : X)
    (κsep : Type) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk x)) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk x)) κsep]
    (H : Type) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk x) H]
    [IsHenselization (X.presheaf.stalk x) κsep H]
    {K : Type*} [Field K] {m : ℕ} {q : ℤ} (hK : IsCyclicQuotientSetting K m q)
    (e : AdicCompletion (maximalIdeal H) H ≃+* cyclicInvariants K m q)
    (B : MMP.Mori.PrimeDivisor X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ h : (RationalFunctions X)ˣ,
      Divisor.IsLocalEquation ((m : ℤ) • Finsupp.single B (1 : ℤ)) U h := by
  obtain ⟨φ, hφ⟩ := exists_forall_mem_support_coeff_eq_ord sX x κsep H hK e B
  obtain ⟨U, hxU, hU⟩ := exists_isLocalEquation_of_forall_mem_support _ φ x hφ
  exact ⟨U, hxU, φ, hU⟩

/-- In `⋀^{d+1} M`, `(a v + ∑ bᵢ wᵢ) ∧ w₁ ∧ ⋯ ∧ w_d = a (v ∧ w₁ ∧ ⋯ ∧ w_d)`. -/
theorem ιMulti_cons_add_sum {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {d : ℕ}
    (v : M) (w : Fin d → M) (a : R) (b : Fin d → R) :
    exteriorPower.ιMulti R (d + 1) (Fin.cons (a • v + ∑ i, b i • w i) w : Fin (d + 1) → M) =
      a • exteriorPower.ιMulti R (d + 1) (Fin.cons v w : Fin (d + 1) → M) := by
  set f := (exteriorPower.ιMulti R (d + 1) (M := M)).toMultilinearMap
  have h1 : ∀ y : M, exteriorPower.ιMulti R (d + 1) (Fin.cons y w : Fin (d + 1) → M) =
      f (Fin.cons y w) := fun y => rfl
  have hz : ∀ i, f (Fin.cons (w i) w) = 0 := fun i =>
    (exteriorPower.ιMulti R (d + 1) (M := M)).map_eq_zero_of_eq (i := 0) (j := i.succ) _
      (by simp) (Fin.succ_ne_zero i).symm
  rw [h1, h1, f.cons_add, f.cons_smul]
  have hs : ∀ s : Finset (Fin d), f (Fin.cons (∑ i ∈ s, b i • w i) w) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using f.map_coord_zero (m := Fin.cons 0 w) 0 rfl
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, f.cons_add, f.cons_smul, hz, ih, smul_zero, add_zero]
  rw [hs, add_zero]

/-- If `dϖ', dx'₁, …, dx'_d` span `Ω_{C'/k}`, then
`d(u ϖ'^{e+1}) ∧ dx' = ϖ'^e ((e + 1) u + ϖ' a) · dϖ' ∧ dx'` for some `a`. -/
theorem exists_ιMulti_cons_D_mul_pow {k C' : Type*} [Field k] [CommRing C'] [Algebra k C']
    {d : ℕ} {ϖ' : C'} {x' : Fin d → C'}
    (hspan : Submodule.span C' (Set.range (Fin.cons (KaehlerDifferential.D k C' ϖ')
      fun i => KaehlerDifferential.D k C' (x' i) : Fin (d + 1) → Ω[C'⁄k])) = ⊤)
    (u : C') (e : ℕ) :
    ∃ a : C', exteriorPower.ιMulti C' (d + 1)
        (Fin.cons (KaehlerDifferential.D k C' (u * ϖ' ^ (e + 1)))
          fun i => KaehlerDifferential.D k C' (x' i) : Fin (d + 1) → Ω[C'⁄k]) =
      (ϖ' ^ e * ((e + 1 : ℕ) * u + ϖ' * a)) •
        exteriorPower.ιMulti C' (d + 1) (Fin.cons (KaehlerDifferential.D k C' ϖ')
          fun i => KaehlerDifferential.D k C' (x' i) : Fin (d + 1) → Ω[C'⁄k]) := by
  have hu : KaehlerDifferential.D k C' u ∈ Submodule.span C' (Set.range (Fin.cons
      (KaehlerDifferential.D k C' ϖ') fun i => KaehlerDifferential.D k C' (x' i) :
        Fin (d + 1) → Ω[C'⁄k])) := hspan ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C').mp hu
  rw [Fin.sum_univ_succ] at hc
  simp only [Fin.cons_zero, Fin.cons_succ] at hc
  refine ⟨c 0, ?_⟩
  have hD : KaehlerDifferential.D k C' (u * ϖ' ^ (e + 1)) =
      (ϖ' ^ e * ((e + 1 : ℕ) * u + ϖ' * c 0)) • KaehlerDifferential.D k C' ϖ' +
        ∑ i, (ϖ' ^ (e + 1) * c i.succ) • KaehlerDifferential.D k C' (x' i) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, ← hc]
    have hs : ∑ i : Fin d, (ϖ' ^ (e + 1) * c i.succ) • KaehlerDifferential.D k C' (x' i) =
        ϖ' ^ (e + 1) • ∑ i : Fin d, c i.succ • KaehlerDifferential.D k C' (x' i) := by
      rw [Finset.smul_sum]; simp only [smul_smul]
    rw [hs]
    generalize (∑ i : Fin d, c i.succ • KaehlerDifferential.D k C' (x' i)) = s
    simp only [Nat.add_sub_cancel]
    push_cast
    module
  rw [hD, ιMulti_cons_add_sum]

/-- If the pull-back of a generator `σ` of `Ω^n_{C/k}` is `w` times a generator `σ'` of
`Ω^n_{C'/k}`, the order along `C'` of the pull-back of `ω` is `v'(ω / σ^{⊗m}) + m v'(w)`. -/
theorem ordAt_pullbackForms_eq_of_topFormsMap_eq {k : Type*} [Field k] {C C' F F' : Type*}
    [CommRing C] [CommRing C']
    [Field F] [Field F'] [Algebra k C] [Algebra k C'] [Algebra k F] [Algebra k F']
    [Algebra C F] [IsFractionRing C F] [IsScalarTower k C F]
    [Algebra C' F'] [IsFractionRing C' F'] [IsScalarTower k C' F']
    [Algebra F F'] [IsScalarTower k F F'] {n : ℕ}
    {σ : ⋀[C]^n Ω[C⁄k]} (hσ : Submodule.span C {σ} = ⊤) (h0 : topFormsMap k C F n σ ≠ 0)
    {σ' : ⋀[C']^n Ω[C'⁄k]} (hσ' : Submodule.span C' {σ'} = ⊤)
    (h0' : topFormsMap k C' F' n σ' ≠ 0) {w : F'} (hw : w ≠ 0)
    (hrel : topFormsMap k F F' n (topFormsMap k C F n σ) = w • topFormsMap k C' F' n σ')
    {v' : F' → ℤ} (hmul : ∀ x y : F', x ≠ 0 → y ≠ 0 → v' (x * y) = v' x + v' y)
    (hunit : ∀ a : C', IsUnit a → v' (algebraMap C' F' a) = 0)
    (m : ℕ) (ω : PluriForms k F n m) (hω : ω ≠ 0) :
    ordAt C' v' (pullbackForms (K' := F') (m : ℤ) ω) =
      v' (algebraMap F F' (formCoeff C hσ h0 ω)) + m * v' w := by
  have hpow : ∀ l : ℕ, v' (w ^ l) = l * v' w := by
    intro l
    induction l with
    | zero =>
      have := hmul 1 1 one_ne_zero one_ne_zero
      simp at this ⊢; omega
    | succ l ih => rw [pow_succ, hmul _ _ (pow_ne_zero _ hw) hw, ih]; push_cast; ring
  have hgen : IsPullbackGenerator F' (topFormsMap k C F n σ) := by
    refine ⟨span_singleton_topFormsMap (nonZeroDivisors C) hσ, ?_, ?_⟩
    · rw [hrel]
      have hs := span_singleton_topFormsMap (K := F') (nonZeroDivisors C') hσ'
      rw [Submodule.span_singleton_smul_eq (IsUnit.mk0 w hw)]
      exact hs
    · rw [hrel]; exact smul_ne_zero hw h0'
  set c := formCoeff C hσ h0 ω with hc
  have hωe : ω = c • formPow (topFormsMap k C F n σ) m := by
    have := formCoeff_smul_basis hσ h0 ω
    rw [ZTensorPower.basis_natCast, topFormsBasis_apply] at this
    exact this.symm
  have hc0 : c ≠ 0 := by rwa [hc, Ne, formCoeff_eq_zero_iff]
  have h1 : formCoeff C' hσ' h0' (ZTensorPower.basis (topFormsBasis C' hσ' h0') (m : ℤ) () :
      PluriForms k F' n m) = 1 := by simp [formCoeff]
  rw [hωe, pullbackForms_smul_formPow hgen, hrel, formPow_smul, smul_smul,
    ordAt_eq hmul hunit hσ' h0', ← topFormsBasis_apply (A := C') hσ' h0' (),
    ← ZTensorPower.basis_natCast, formCoeff_smul, h1, mul_one,
    hmul _ _ ((map_ne_zero _).mpr hc0) (pow_ne_zero _ hw), hpow]

/-- **Hurwitz's formula for `m`-canonical forms.** Let `C → C'` be a map of local rings with
fraction fields `F ⊆ F'`, `dϖ, dx` a frame of `Ω_{C/k}` whose images `dϖ', dx'` (with `ϖ'` the
new uniformizer) frame `Ω_{C'/k}`, and `ϖ = u ϖ'^{e+1}`, `u` a unit, in characteristic zero.
Then `ord_{C'}(u^*ω) = (e + 1) ord_C(ω) + m e` for every nonzero `m`-canonical form `ω`. -/
theorem ordAt_pullbackForms_eq_of_ramification {k : Type*} [Field k] {C C' F F' : Type*}
    [CommRing C] [CommRing C']
    [Field F] [Field F'] [Algebra k C] [Algebra k C'] [Algebra k F] [Algebra k F']
    [Algebra C F] [IsFractionRing C F] [IsScalarTower k C F]
    [Algebra C' F'] [IsFractionRing C' F'] [IsScalarTower k C' F']
    [Algebra F F'] [IsScalarTower k F F']
    [CharZero k] [IsLocalRing C'] [Algebra C C']
    [IsScalarTower k C C']
    (hcomp : ∀ c : C, algebraMap F F' (algebraMap C F c) = algebraMap C' F' (algebraMap C C' c))
    {d : ℕ} [Nontrivial (⋀[F]^(d + 1) Ω[F⁄k])] [Nontrivial (⋀[F']^(d + 1) Ω[F'⁄k])]
    {ϖ : C} {x : Fin d → C}
    (hx : Submodule.span C (Set.range (Fin.cons (KaehlerDifferential.D k C ϖ)
      fun i => KaehlerDifferential.D k C (x i) : Fin (d + 1) → Ω[C⁄k])) = ⊤)
    {ϖ' : C'} (hx' : Submodule.span C' (Set.range (Fin.cons (KaehlerDifferential.D k C' ϖ')
      fun i => KaehlerDifferential.D k C' (algebraMap C C' (x i)) : Fin (d + 1) → Ω[C'⁄k])) = ⊤)
    (hϖ' : ϖ' ∈ IsLocalRing.maximalIdeal C') (hϖ'ne : ϖ' ≠ 0) {u : C'} (hu : IsUnit u) {e : ℕ}
    (hram : algebraMap C C' ϖ = u * ϖ' ^ (e + 1))
    {v : F → ℤ} {v' : F' → ℤ} (hmul : ∀ x y : F, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : C, IsUnit a → v (algebraMap C F a) = 0)
    (hmul' : ∀ x y : F', x ≠ 0 → y ≠ 0 → v' (x * y) = v' x + v' y)
    (hunit' : ∀ a : C', IsUnit a → v' (algebraMap C' F' a) = 0)
    (hvϖ' : v' (algebraMap C' F' ϖ') = 1)
    (hvv : ∀ f : F, f ≠ 0 → v' (algebraMap F F' f) = (e + 1) * v f)
    (m : ℕ) (ω : PluriForms k F (d + 1) m) (hω : ω ≠ 0) :
    ordAt C' v' (pullbackForms (K' := F') (m : ℤ) ω) = (e + 1) * ordAt C v ω + m * e := by
  have hσ := MMP.Fourfold.span_singleton_ιMulti_eq_top _ hx
  have hσ' := MMP.Fourfold.span_singleton_ιMulti_eq_top _ hx'
  have h0 := topFormsMap_ne_zero_of_span_eq_top (K := F) hσ
  have h0' := topFormsMap_ne_zero_of_span_eq_top (K := F') hσ'
  obtain ⟨a, ha⟩ := exists_ιMulti_cons_D_mul_pow hx' u e
  have hϖ'0 : algebraMap C' F' ϖ' ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective C' F')).mpr hϖ'ne
  have he1 : IsUnit ((e + 1 : ℕ) : C') := by
    have h : ((e + 1 : ℕ) : C') = algebraMap k C' ((e + 1 : ℕ) : k) := by simp
    rw [h]
    exact (IsUnit.mk0 _ (by exact_mod_cast Nat.succ_ne_zero e)).map _
  have hU : IsUnit ((e + 1 : ℕ) * u + ϖ' * a) := by
    by_contra hn
    have h1 : (e + 1 : ℕ) * u + ϖ' * a ∈ IsLocalRing.maximalIdeal C' :=
      (IsLocalRing.mem_maximalIdeal _).mpr hn
    have h2 : (e + 1 : ℕ) * u ∈ IsLocalRing.maximalIdeal C' := by
      have := sub_mem h1 (Ideal.mul_mem_right a _ hϖ')
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 (he1.mul hu)
  set w := algebraMap C' F' (ϖ' ^ e * ((e + 1 : ℕ) * u + ϖ' * a)) with hw
  have hUF : algebraMap C' F' ((e + 1 : ℕ) * u + ϖ' * a) ≠ 0 := (hU.map _).ne_zero
  have hw0 : w ≠ 0 := by
    rw [hw, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hϖ'0) hUF
  have hpow : ∀ l : ℕ, v' (algebraMap C' F' ϖ' ^ l) = l := by
    intro l
    induction l with
    | zero =>
      have := hmul' 1 1 one_ne_zero one_ne_zero
      simp at this ⊢; omega
    | succ l ih => rw [pow_succ, hmul' _ _ (pow_ne_zero _ hϖ'0) hϖ'0, ih, hvϖ']; push_cast; ring
  have hvw : v' w = e := by
    rw [hw, map_mul, map_pow, hmul' _ _ (pow_ne_zero _ hϖ'0) hUF, hpow, hunit' _ hU, add_zero]
  have hrel : topFormsMap k F F' (d + 1) (topFormsMap k C F (d + 1)
      (exteriorPower.ιMulti C (d + 1) (Fin.cons (KaehlerDifferential.D k C ϖ)
        fun i => KaehlerDifferential.D k C (x i) : Fin (d + 1) → Ω[C⁄k]))) =
      w • topFormsMap k C' F' (d + 1) (exteriorPower.ιMulti C' (d + 1)
        (Fin.cons (KaehlerDifferential.D k C' ϖ')
          fun i => KaehlerDifferential.D k C' (algebraMap C C' (x i)) :
            Fin (d + 1) → Ω[C'⁄k])) := by
    rw [hw, algebraMap_smul, ← map_smul, ← ha, topFormsMap_ιMulti, topFormsMap_ιMulti,
      topFormsMap_ιMulti]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero, KaehlerDifferential.map_D, hcomp, hram]
    · simp only [Fin.cons_succ, KaehlerDifferential.map_D, hcomp]
  rw [ordAt_pullbackForms_eq_of_topFormsMap_eq hσ h0 hσ' h0' hw0 hrel hmul' hunit' m ω hω, hvw,
    ordAt_eq hmul hunit hσ h0, hvv _ (by rwa [Ne, formCoeff_eq_zero_iff])]

end

end MMP.CyclicChartDifferent

end
