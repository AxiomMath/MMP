module

public import MMP.AlgebraicGeometry.MMP.Fourfold.AmpleModel
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.ProjectiveSpectrum.ConeAlgebraGeneration

/-!
# The divisorial section algebra of a Weil divisor

Let `X` be a locally Noetherian normal scheme and `D` a Weil divisor on `X`. The divisorial
sheaves `𝒪_X(nD) ⊆ 𝒦_X`, `n ≥ 0`, form a sheaf of commutative graded `𝒪_X`-algebras
`⨁_{n ≥ 0} 𝒪_X(nD)`, multiplication being the product of rational functions. Each piece is
quasi-coherent, so this is a relative `Proj` datum over `X`.

## Main definitions

* `MMP.Mori.Divisor.sectionAlgebraPiece`: the degree-`n` piece, `𝒪_X(nD)` for `n ≥ 0` and zero
  for `n < 0`.
* `MMP.Mori.Divisor.sectionAlgebraMul`: the multiplication `𝒪_X(iD) × 𝒪_X(jD) → 𝒪_X((i+j)D)`.
* `MMP.Mori.Divisor.sectionGradedAlgebra`: the sheaf of graded algebras `⨁_{n ≥ 0} 𝒪_X(nD)`.
* `MMP.Mori.Divisor.divisorialSectionAlgebra`: the same algebra as a
  `MMP.Fourfold.DivisorialSectionAlgebra` along the identity of `X`.

## Main results

* `MMP.Mori.Divisor.isConeAlgebra_divisorialSectionAlgebra`: the algebra satisfies Fulton's
  conditions on the graded algebra of a cone (`MMP.Intersection.Scheme.IsConeAlgebra`), when
  `𝒪_X(D)` is coherent and `𝒪_X(nD)` is spanned by products of `n` sections of `𝒪_X(D)` over
  every affine open.
* `MMP.Mori.Divisor.isLocallyDegreeOneGenerated_divisorialSectionAlgebra`: degree-one generation
  of `⨁_n 𝒪_X(nD)` from `𝒪_X(nD)(V) ⊆ 𝒪_X(D)(V)ⁿ` on affine opens.
* `MMP.Mori.Divisor.divisorialSubmodule_le_pow_of_adjoin_eq`: if the Veronese ring
  `R(X, B)^{(e)}(U)` is generated in degrees `0` and `e`, then `𝒪_X(neB)(U) ⊆ 𝒪_X(eB)(U)ⁿ`.
* `MMP.Mori.Divisor.finiteType_divisorialAlgebraSections_of_le_pow`: finite generation of
  `R(X, D)(U)` from degree-one generation and finiteness of `𝒪_X(D)(U)`.
* `MMP.Fourfold.DivisorialSectionAlgebra.isDomain_sectionRing`: on an integral scheme the rings
  of sections are domains.

## Implementation notes

The pieces are indexed by `ℤ`, as relative `Proj` asks; a piece is defined by cases on the
integer, so that in degree `Int.ofNat k` it is literally `𝒪_X(Int.ofNat k • D)` and the degree
of a product of two nonnegative degrees reduces to the sum. The algebra laws are checked through
the embedding of each piece into the rational functions `𝒦_X(U)`, which is injective in
nonnegative degrees.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], §6.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace MMP.Mori.Divisor

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X)

/-- The degree-`n` piece of `⨁_{n ≥ 0} 𝒪_X(nD)`: the divisorial sheaf `𝒪_X(nD)` for `n ≥ 0`
and the zero sheaf for `n < 0`. -/
def sectionAlgebraPiece : ℤ → X.Modules
  | .ofNat k => ((Int.ofNat k) • D).divisorialSheaf
  | .negSucc _ => SheafOfModules.free (R := X.ringCatSheaf) PEmpty

/-- The pieces of `⨁_{n ≥ 0} 𝒪_X(nD)` in negative degrees are zero. -/
theorem isZero_sectionAlgebraPiece_of_neg (n : ℤ) (hn : n < 0) :
    Limits.IsZero (sectionAlgebraPiece D n) := by
  cases n with
  | ofNat k => exact absurd hn (not_lt.mpr (Int.natCast_nonneg k))
  | negSucc k =>
    change Limits.IsZero (SheafOfModules.free (R := X.ringCatSheaf) PEmpty)
    rw [Limits.IsZero.iff_id_eq_zero]
    exact Limits.Sigma.hom_ext _ _ fun i => i.elim

/-- Every section of a piece of negative degree is zero. -/
theorem sectionAlgebraPiece_eq_zero_of_neg {n : ℤ} (hn : n < 0) {U : X.Opens}
    (x : (sectionAlgebraPiece D n).val.obj (op U)) : x = 0 := by
  let E := Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)
  exact (ModuleCat.subsingleton_of_isZero
    (E.map_isZero (isZero_sectionAlgebraPiece_of_neg D n hn))).elim _ _

/-- Every piece of `⨁_{n ≥ 0} 𝒪_X(nD)` is quasi-coherent. -/
instance sectionAlgebraPiece_isQuasicoherent [CompactSpace X] (n : ℤ) :
    (sectionAlgebraPiece D n).IsQuasicoherent := by
  cases n with
  | ofNat k => exact isQuasicoherent_divisorialSheaf _
  | negSucc k =>
    exact (inferInstance : (SheafOfModules.free (R := X.ringCatSheaf) PEmpty).IsQuasicoherent)

/-- The rational function underlying a homogeneous section, taken to be `0` in negative degrees. -/
def sectionAlgebraAmbient (n : ℤ) (U : X.Opens) (x : (sectionAlgebraPiece D n).val.obj (op U)) :
    (rationalFunctionsPresheaf X).obj (op U) :=
  match n, x with
  | .ofNat _, x => (x : (Int.ofNat _ • D).divisorialSubmodule U).1
  | .negSucc _, _ => 0

/-- The rational function underlying the zero section is `0`. -/
@[simp]
theorem sectionAlgebraAmbient_zero (n : ℤ) (U : X.Opens) :
    sectionAlgebraAmbient D n U 0 = 0 := by
  cases n <;> rfl

/-- Two homogeneous sections of equal degrees with the same underlying rational function are
equal. -/
theorem heq_of_sectionAlgebraAmbient_eq {n m : ℤ} (h : n = m) {U : X.Opens}
    (x : (sectionAlgebraPiece D n).val.obj (op U)) (y : (sectionAlgebraPiece D m).val.obj (op U))
    (hxy : sectionAlgebraAmbient D n U x = sectionAlgebraAmbient D m U y) : HEq x y := by
  subst h
  refine heq_of_eq ?_
  cases n with
  | ofNat k => exact Subtype.ext hxy
  | negSucc k =>
    exact (sectionAlgebraPiece_eq_zero_of_neg D (Int.negSucc_lt_zero k) x).trans
      (sectionAlgebraPiece_eq_zero_of_neg D (Int.negSucc_lt_zero k) y).symm

/-- The product `𝒪_X(aD)(U) × 𝒪_X(bD)(U) → 𝒪_X((a + b)D)(U)` of rational functions. -/
def divisorialSubmoduleMul (a b : ℤ) (U : X.Opens) :
    (a • D).divisorialSubmodule U →+ (b • D).divisorialSubmodule U →+
      ((a + b) • D).divisorialSubmodule U :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => ⟨x.1 * y.1, by
      rw [add_smul]; exact IsDivisorialSection.mul x.2 y.2⟩)
    fun y y' => Subtype.ext (mul_add _ _ _))
    fun x x' => AddMonoidHom.ext fun y => Subtype.ext (add_mul _ _ _)

/-- The product of two divisorial sections is the product of their rational functions. -/
@[simp]
theorem coe_divisorialSubmoduleMul (a b : ℤ) (U : X.Opens) (x : (a • D).divisorialSubmodule U)
    (y : (b • D).divisorialSubmodule U) :
    (divisorialSubmoduleMul D a b U x y).1 = x.1 * y.1 := rfl

/-- The zero bilinear map. -/
def sectionAlgebraZeroMul (M N P : X.Modules) : SheafOfModules.BilinearMap M N P where
  app _ := 0
  map_smul_left _ _ _ _ := by simp
  map_smul_right _ _ _ _ := by simp
  naturality f _ _ := by
    change ConcreteCategory.hom (P.val.map f) 0 = 0
    exact map_zero _

/-- The multiplication `𝒪_X(iD) × 𝒪_X(jD) → 𝒪_X((i + j)D)` of `⨁_{n ≥ 0} 𝒪_X(nD)`, the product
of rational functions in nonnegative degrees and zero otherwise. -/
def sectionAlgebraMul (i j : ℤ) :
    SheafOfModules.BilinearMap (sectionAlgebraPiece D i) (sectionAlgebraPiece D j)
      (sectionAlgebraPiece D (i + j)) := by
  cases i with
  | ofNat k =>
    cases j with
    | ofNat m =>
      exact
        { app U := divisorialSubmoduleMul D (Int.ofNat k) (Int.ofNat m) U.unop
          map_smul_left U r x y := Subtype.ext (smul_mul_assoc _ _ _)
          map_smul_right U r x y := Subtype.ext (mul_smul_comm _ _ _)
          naturality f x y := Subtype.ext (map_mul ((rationalFunctionsPresheaf X).map f).hom _ _) }
    | negSucc m => exact sectionAlgebraZeroMul _ _ _
  | negSucc k => exact sectionAlgebraZeroMul _ _ _

/-- The rational function underlying a product of homogeneous sections is the product of the
underlying rational functions. -/
@[simp]
theorem sectionAlgebraAmbient_mul (i j : ℤ) (U : X.Opens)
    (x : (sectionAlgebraPiece D i).val.obj (op U)) (y : (sectionAlgebraPiece D j).val.obj (op U)) :
    sectionAlgebraAmbient D (i + j) U ((sectionAlgebraMul D i j).app (op U) x y) =
      sectionAlgebraAmbient D i U x * sectionAlgebraAmbient D j U y := by
  cases i with
  | ofNat k =>
    cases j with
    | ofNat m => rfl
    | negSucc m =>
      exact (sectionAlgebraAmbient_zero D _ U).trans (mul_zero _).symm
  | negSucc k =>
    exact (sectionAlgebraAmbient_zero D _ U).trans (zero_mul _).symm

/-- The unit `1 ∈ 𝒪_X(0 • D)`. -/
def sectionAlgebraOne : (sectionAlgebraPiece D 0).sections :=
  divisorialSheafOneSection (D := Int.ofNat 0 • D) (le_of_eq (zero_smul ℤ D).symm)

/-- The rational function underlying the unit of `⨁_{n ≥ 0} 𝒪_X(nD)` is `1`. -/
@[simp]
theorem sectionAlgebraAmbient_one (U : X.Opens) :
    sectionAlgebraAmbient D 0 U ((sectionAlgebraOne D).eval (op U)) = 1 := rfl

/-- The sheaf of graded `𝒪_X`-algebras `⨁_{n ≥ 0} 𝒪_X(nD)`. -/
def sectionGradedAlgebra : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf where
  piece := sectionAlgebraPiece D
  mul := sectionAlgebraMul D
  one := sectionAlgebraOne D
  mul_assoc i j k U x y z := heq_of_sectionAlgebraAmbient_eq D (add_assoc i j k) _ _ (by
    rw [sectionAlgebraAmbient_mul, sectionAlgebraAmbient_mul, sectionAlgebraAmbient_mul,
      sectionAlgebraAmbient_mul, mul_assoc])
  one_mul i U x := heq_of_sectionAlgebraAmbient_eq D (zero_add i) _ _ (by
    rw [sectionAlgebraAmbient_mul, sectionAlgebraAmbient_one, one_mul])
  mul_one i U x := heq_of_sectionAlgebraAmbient_eq D (add_zero i) _ _ (by
    rw [sectionAlgebraAmbient_mul, sectionAlgebraAmbient_one, mul_one])

/-- The multiplication of `sectionGradedAlgebra D` is commutative. -/
theorem sectionGradedAlgebra_mul_comm (i j : ℤ) (U : X.Opensᵒᵖ)
    (a : ((sectionGradedAlgebra D).piece i).val.obj U)
    (b : ((sectionGradedAlgebra D).piece j).val.obj U) :
    HEq (((sectionGradedAlgebra D).mul i j).app U a b)
      (((sectionGradedAlgebra D).mul j i).app U b a) :=
  heq_of_sectionAlgebraAmbient_eq D (U := U.unop) (add_comm i j) _ _
    ((sectionAlgebraAmbient_mul D i j U.unop a b).trans
      ((mul_comm _ _).trans (sectionAlgebraAmbient_mul D j i U.unop b a).symm))

/-- Equal divisors have equal divisorial sheaves, as an isomorphism of inclusions. -/
def divisorialSheafIsoOfEq {D₁ D₂ : Divisor X} (h : D₁ = D₂) :
    D₁.divisorialSheaf ≅ D₂.divisorialSheaf where
  hom := divisorialSheafInclusion (le_of_eq h)
  inv := divisorialSheafInclusion (le_of_eq h.symm)
  hom_inv_id := divisorialSheaf_hom_ext fun _ _ => rfl
  inv_hom_id := divisorialSheaf_hom_ext fun _ _ => rfl

/-- The degree-zero piece `𝒪_X(0 • D)` of `⨁_{n ≥ 0} 𝒪_X(nD)` is the structure sheaf. -/
def sectionAlgebraDegreeZeroIso :
    (sectionGradedAlgebra D).piece 0 ≅ SheafOfModules.unit X.ringCatSheaf :=
  divisorialSheafIsoOfEq (zero_smul ℤ D : Int.ofNat 0 • D = 0) ≪≫ divisorialSheafZeroIso

/-- The degree-zero identification sends the unit to `1`. -/
theorem sectionAlgebraDegreeZeroIso_one (U : X.Opensᵒᵖ) :
    (sectionAlgebraDegreeZeroIso D).hom.val.app U ((sectionAlgebraOne D).eval U) =
      (1 : X.ringCatSheaf.obj.obj U) := by
  have h1 : (divisorialSheafZeroIso (X := X)).inv.val.app U (1 : X.ringCatSheaf.obj.obj U) =
      (divisorialSheafIsoOfEq (zero_smul ℤ D : Int.ofNat 0 • D = 0)).hom.val.app U
        ((sectionAlgebraOne D).eval U) :=
    Subtype.ext ((coe_structureSheafToDivisorialSheaf_app _ U.unop 1).trans (map_one _))
  change divisorialSheafZeroIso.hom.val.app U
    ((divisorialSheafIsoOfEq (zero_smul ℤ D : Int.ofNat 0 • D = 0)).hom.val.app U
      ((sectionAlgebraOne D).eval U)) = _
  rw [← h1]
  exact congrArg (fun f => f.val.app U (1 : X.ringCatSheaf.obj.obj U))
    (divisorialSheafZeroIso (X := X)).inv_hom_id

/-- The identification of the degree-`i` sections of `⨁_{n ≥ 0} 𝒪_X(nD)` with
`𝒪_X(iD)(U)`, for `i ≥ 0`. -/
def sectionAlgebraEquiv (i : ℤ) (hi : 0 ≤ i) (U : X.Opens) :
    (sectionAlgebraPiece D i).val.obj (op U) ≃+ (i • D).divisorialSubmodule ((𝟙 X) ⁻¹ᵁ U) :=
  match i, hi with
  | .ofNat _, _ => AddEquiv.refl _

/-- The identification `sectionAlgebraEquiv` preserves the underlying rational function. -/
@[simp]
theorem coe_sectionAlgebraEquiv (i : ℤ) (hi : 0 ≤ i) (U : X.Opens)
    (x : (sectionAlgebraPiece D i).val.obj (op U)) :
    (sectionAlgebraEquiv D i hi U x).1 = sectionAlgebraAmbient D i U x :=
  match i, hi with
  | .ofNat _, _ => rfl

variable [CompactSpace X]

/-- The divisorial algebra `⨁_{n ≥ 0} 𝒪_X(nD)` of a Weil divisor `D`, as a divisorial section
algebra along the identity of `X`. -/
def divisorialSectionAlgebra : MMP.Fourfold.DivisorialSectionAlgebra (𝟙 X) D where
  algebra := sectionGradedAlgebra D
  mul_comm := sectionGradedAlgebra_mul_comm D
  negative_isZero := isZero_sectionAlgebraPiece_of_neg D
  isQuasicoherent := sectionAlgebraPiece_isQuasicoherent D
  sectionEquiv := sectionAlgebraEquiv D
  sectionEquiv_restrict i hi U V h a := by
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rfl
  sectionEquiv_smul i hi U r a := by
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rfl
  sectionEquiv_mul i j hi hj U a b := by
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rfl
  sectionEquiv_one U := rfl

end MMP.Mori.Divisor

namespace MMP.Fourfold.DivisorialSectionAlgebra

open MMP.Mori Polynomial

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y}
  (A : DivisorialSectionAlgebra (𝟙 Y) D)

/-- Heterogeneously equal sections of equal nonnegative degrees have the same image under
`sectionEquiv` as rational functions. -/
theorem sectionEquiv_heq {i j : ℤ} (h : i = j) (hi : 0 ≤ i) (hj : 0 ≤ j) (U : Y.Opens)
    (a : (A.algebra.piece i).val.obj (op U)) (b : (A.algebra.piece j).val.obj (op U))
    (hab : HEq a b) :
    ((A.sectionEquiv i hi U a : _) : (rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ U))) =
      A.sectionEquiv j hj U b := by
  subst h; cases hab; rfl

/-- The degree-`n` sections of the section ring, as rational functions. -/
def pieceToRationalFunctions (W : Y.Opens) (n : ℕ) :
    A.situation.sectionPieces W n →+ (rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)) :=
  (((n : ℤ) • D).divisorialSubmodule ((𝟙 Y) ⁻¹ᵁ W)).subtype.toAddMonoidHom.comp
    (A.sectionEquiv n (Int.natCast_nonneg n) W).toAddMonoidHom

/-- `pieceToRationalFunctions` is the rational function underlying `sectionEquiv`. -/
theorem pieceToRationalFunctions_apply (W : Y.Opens) (n : ℕ)
    (a : A.situation.sectionPieces W n) :
    A.pieceToRationalFunctions W n a = (A.sectionEquiv n (Int.natCast_nonneg n) W a : _) := rfl

/-- The section ring `⨁_n 𝒪_Y(nD)(W)` over an open `W`, embedded in the polynomial ring
`𝒦_Y(W)[t]` by `∑ aₙ ↦ ∑ aₙ tⁿ`. -/
def toPolynomial (W : Y.Opens) :
    A.situation.sectionRing W →+* ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)))[X] :=
  DirectSum.toSemiring (fun n => (monomial n).toAddMonoidHom.comp (A.pieceToRationalFunctions W n))
    (by
      have h1 := (A.situation.sectionRingStructure).one_homogeneous W
      have h2 := A.sectionEquiv_one W
      change monomial 0 (A.pieceToRationalFunctions W 0 _) = 1
      rw [pieceToRationalFunctions_apply]
      exact (congrArg (monomial 0) ((A.sectionEquiv_heq (i := ((0 : ℕ) : ℤ)) (j := 0) rfl _
        le_rfl W _ _ (heq_of_eq h1)).trans h2)).trans monomial_zero_one)
    (by
      intro i j a b
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, monomial_mul_monomial]
      congr 1
      rw [pieceToRationalFunctions_apply, pieceToRationalFunctions_apply,
        pieceToRationalFunctions_apply,
        A.sectionEquiv_heq (j := (i : ℤ) + j) (by push_cast; rfl) _
          (add_nonneg (Int.natCast_nonneg i) (Int.natCast_nonneg j)) W _ _
          ((A.situation.sectionRingStructure).mul_homogeneous W i j a b)]
      exact A.sectionEquiv_mul i j _ _ W a b)

/-- `toPolynomial` sends a homogeneous section `a` of degree `n` to the monomial `a tⁿ`. -/
@[simp]
theorem toPolynomial_of (W : Y.Opens) (n : ℕ) (a : A.situation.sectionPieces W n) :
    A.toPolynomial W (DirectSum.of _ n a) = monomial n (A.pieceToRationalFunctions W n a) :=
  DirectSum.toSemiring_of _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The `m`-th coefficient of `toPolynomial W r` is the rational function underlying the
degree-`m` component of `r`. -/
@[simp]
theorem coeff_toPolynomial (W : Y.Opens) (r : A.situation.sectionRing W) (m : ℕ) :
    (A.toPolynomial W r).coeff m = A.pieceToRationalFunctions W m (r m) := by
  induction r using DirectSum.induction_on with
  | zero => rw [map_zero, coeff_zero, DirectSum.zero_apply, map_zero]
  | of n a =>
    rw [toPolynomial_of, coeff_monomial]
    by_cases h : n = m
    · subst h; simp
    · have h0 : (DirectSum.of (A.situation.sectionPieces W) n a) m = 0 :=
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)
      rw [if_neg h, h0, map_zero]
  | add x y hx hy => rw [map_add, coeff_add, hx, hy, DirectSum.add_apply, map_add]

/-- The `m`-th coefficient of `toPolynomial W r` lies in `𝒪_Y(mD)(W)`. -/
theorem coeff_toPolynomial_mem (W : Y.Opens) (r : A.situation.sectionRing W) (m : ℕ) :
    (A.toPolynomial W r).coeff m ∈ ((m : ℤ) • D).divisorialSubmodule ((𝟙 Y) ⁻¹ᵁ W) := by
  rw [coeff_toPolynomial]
  exact (A.sectionEquiv m (Int.natCast_nonneg m) W (r m)).2

/-- The embedding `toPolynomial W` of the section ring in `𝒦_Y(W)[t]` is injective. -/
theorem toPolynomial_injective (W : Y.Opens) : Function.Injective (A.toPolynomial W) := by
  intro r r' h
  ext m
  have := congrArg (fun g => g.coeff m) h
  simp only [coeff_toPolynomial, pieceToRationalFunctions_apply] at this
  exact (A.sectionEquiv m (Int.natCast_nonneg m) W).injective (Subtype.ext this)

/-- A polynomial over `𝒦_Y(W)` whose `m`-th coefficient lies in `𝒪_Y(mD)(W)` for every `m` is in
the image of `toPolynomial W`. -/
theorem exists_toPolynomial_eq (W : Y.Opens)
    (g : ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)))[X])
    (hg : ∀ m : ℕ, g.coeff m ∈ ((m : ℤ) • D).divisorialSubmodule ((𝟙 Y) ⁻¹ᵁ W)) :
    ∃ r, A.toPolynomial W r = g := by
  refine ⟨∑ m ∈ g.support, DirectSum.of _ m
    ((A.sectionEquiv m (Int.natCast_nonneg m) W).symm ⟨g.coeff m, hg m⟩), ?_⟩
  rw [map_sum]
  conv_rhs => rw [g.as_sum_support]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [toPolynomial_of, pieceToRationalFunctions_apply, AddEquiv.apply_symm_apply]

/-- `toPolynomial` sends the image of a regular function `r` in the section ring to the constant
polynomial `r`. -/
theorem toPolynomial_sectionRingBaseMap (W : Y.Opens) (r : Γ(Y, W)) :
    A.toPolynomial W (A.situation.sectionRingBaseMap W r) =
      C (algebraMap Γ(Y, (𝟙 Y) ⁻¹ᵁ W) _ (Scheme.Hom.app (𝟙 Y) W r)) := by
  change A.toPolynomial W ((A.situation.sectionRingStructure).baseMap W r) = _
  rw [(A.situation.sectionRingStructure).baseMap_apply W r, toPolynomial_of,
    pieceToRationalFunctions_apply, monomial_zero_left]
  congr 1
  refine (congrArg Subtype.val
    (A.sectionEquiv_smul 0 le_rfl W r (A.algebra.one.eval (op W)))).trans ?_
  change Scheme.Hom.app (𝟙 Y) W r • ((A.sectionEquiv 0 le_rfl W (A.algebra.one.eval (op W)) : _) :
    (rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W))) = _
  rw [A.sectionEquiv_one W, Algebra.algebraMap_eq_smul_one]

/-- The polynomial `toPolynomial W r` lies in the divisorial algebra `R(Y, D)(W)`. -/
theorem toPolynomial_mem_divisorialAlgebraSections (W : Y.Opens) (r : A.situation.sectionRing W) :
    A.toPolynomial W r ∈ D.divisorialAlgebraSections W := fun m => by
  have := A.coeff_toPolynomial_mem W r m
  rwa [natCast_zsmul] at this

/-- The section ring of a divisorial section algebra along the identity over an open `W` is the
divisorial algebra `R(Y, D)(W) ⊆ 𝒦_Y(W)[t]`. -/
def sectionRingEquiv (W : Y.Opens) :
    A.situation.sectionRing W ≃+* D.divisorialAlgebraSections W :=
  RingEquiv.ofBijective
    ((A.toPolynomial W).codRestrict (D.divisorialAlgebraSections W)
      (A.toPolynomial_mem_divisorialAlgebraSections W))
    ⟨fun r r' h => A.toPolynomial_injective W (congrArg Subtype.val h), fun p => by
      obtain ⟨r, hr⟩ := A.exists_toPolynomial_eq W p.1 fun m => by
        have := p.2 m
        rwa [← natCast_zsmul] at this
      exact ⟨r, Subtype.ext hr⟩⟩

/-- The polynomial underlying `sectionRingEquiv W r` is `toPolynomial W r`. -/
@[simp]
theorem coe_sectionRingEquiv (W : Y.Opens) (r : A.situation.sectionRing W) :
    (A.sectionRingEquiv W r : ((rationalFunctionsPresheaf Y).obj (op W))[X]) =
      A.toPolynomial W r := rfl

/-- Under `sectionRingEquiv W`, the structure map of the section ring is the algebra map of
`R(Y, D)(W)`. -/
theorem sectionRingBaseMap_eq (W : Y.Opens) :
    (show Γ(Y, W) →+* A.situation.sectionRing W from A.situation.sectionRingBaseMap W) =
      (A.sectionRingEquiv W).symm.toRingHom.comp
        (algebraMap Γ(Y, W) (D.divisorialAlgebraSections W)) := by
  refine RingHom.ext fun r => ?_
  apply (A.sectionRingEquiv W).injective
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_sectionRingEquiv]
  exact (A.toPolynomial_sectionRingBaseMap W r).trans rfl

/-- If the divisorial algebra `R(Y, D)(W)` is a finitely generated `Γ(Y, W)`-algebra, so is the
section ring of any divisorial section algebra of `D` along the identity. -/
theorem finiteType_sectionRingBaseMap (W : Y.Opens)
    (h : Algebra.FiniteType Γ(Y, W) (D.divisorialAlgebraSections W)) :
    (A.situation.sectionRingBaseMap W).FiniteType := by
  change (show Γ(Y, W) →+* A.situation.sectionRing W from
    A.situation.sectionRingBaseMap W).FiniteType
  rw [sectionRingBaseMap_eq]
  exact RingHom.FiniteType.comp_surjective (RingHom.finiteType_algebraMap.mpr h)
    (A.sectionRingEquiv W).symm.surjective

end MMP.Fourfold.DivisorialSectionAlgebra

/-! ### Localization of the divisorial algebra -/

namespace MMP.Mori.Divisor

open Polynomial Stacks.AlgebraicGeometry.QuasicoherentBaseChange

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] (B : Divisor X)

/-- Restriction `R(X, B)(U) → R(X, B)(V)` of the divisorial algebra along `V ≤ U`. -/
def divisorialAlgebraSectionsRestrict {U V : X.Opens} (h : V ≤ U) :
    B.divisorialAlgebraSections U →+* B.divisorialAlgebraSections V :=
  (B.divisorialAlgebra.map (homOfLE h).op).hom

/-- Restriction of the divisorial algebra restricts each coefficient of the underlying
polynomial. -/
theorem coe_divisorialAlgebraSectionsRestrict {U V : X.Opens} (h : V ≤ U)
    (p : B.divisorialAlgebraSections U) :
    (B.divisorialAlgebraSectionsRestrict h p).1 =
      p.1.map ((rationalFunctionsPresheaf X).map (homOfLE h).op).hom := rfl

/-- Restriction of the divisorial algebra commutes with the algebra maps from regular functions. -/
theorem divisorialAlgebraSectionsRestrict_algebraMap {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U)) :
    B.divisorialAlgebraSectionsRestrict h (algebraMap Γ(X, U) _ r) =
      algebraMap Γ(X, V) _ (X.presheaf.map (homOfLE h).op r) := by
  apply Subtype.ext
  rw [coe_divisorialAlgebraSectionsRestrict]
  change (algebraMap Γ(X, U) (Polynomial _) r).map _ = algebraMap Γ(X, V) (Polynomial _) _
  rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, Polynomial.map_C]
  exact congrArg C (MMP.Flips.rationalFunctionsPresheaf_map_algebraMap (homOfLE h) r)

/-- The monomial `c tᵐ` lies in `R(X, B)(U)` whenever `c ∈ 𝒪_X(mB)(U)`. -/
theorem monomial_mem_divisorialAlgebraSections {U : X.Opens} (m : ℕ)
    {c : (rationalFunctionsPresheaf X).obj (op U)} (hc : c ∈ (m • B).divisorialSubmodule U) :
    monomial m c ∈ B.divisorialAlgebraSections U := fun k => by
  rw [coeff_monomial]
  split_ifs with h
  · exact h ▸ hc
  · exact zero_mem _

variable [CompactSpace X]

/-- Over `X_a ⊆ U`, every truncation `∑_{m ∈ S} z_m tᵐ` of a section of `R(X, B)(X_a)` becomes,
after multiplying by a power of `a`, the restriction of a section of `R(X, B)(U)`. -/
theorem exists_C_pow_mul_sum_monomial_eq_map {U : X.Opens} (a : Γ(X, U))
    (z : B.divisorialAlgebraSections (X.basicOpen a)) (S : Finset ℕ) :
    ∃ (n : ℕ) (q : B.divisorialAlgebraSections U),
      C (algebraMap Γ(X, X.basicOpen a) ((rationalFunctionsPresheaf X).obj (op (X.basicOpen a)))
        (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a)) ^ n *
        ∑ m ∈ S, monomial m (z.1.coeff m) =
      q.1.map ((rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le a)).op).hom := by
  have hVU : X.basicOpen a ≤ U := X.basicOpen_le a
  set ρ := ((rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le a)).op).hom
  set ra : Γ(X, (X.basicOpen a)) := X.presheaf.map (homOfLE (X.basicOpen_le a)).op a
  set r : (rationalFunctionsPresheaf X).obj (op (X.basicOpen a)) :=
    algebraMap Γ(X, (X.basicOpen a)) _ ra
  have hρa : ρ (algebraMap Γ(X, U) _ a) = r :=
    MMP.Flips.rationalFunctionsPresheaf_map_algebraMap (homOfLE hVU) a
  have hapow : ∀ n : ℕ, ((algebraMap Γ(X, U) (B.divisorialAlgebraSections U) a) ^ n).1 =
      C (algebraMap Γ(X, U) _ a) ^ n := fun n => by
    rw [SubmonoidClass.coe_pow]
    rfl
  have L (m : ℕ) := isLocalizedModule_divisorialSheaf_restrictₗ (m • B) a
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp⟩
  | insert m S hm ih =>
    obtain ⟨n, q, hq⟩ := ih
    letI := moduleOfLE (m • B).divisorialSheaf hVU
    obtain ⟨⟨x, ⟨_, k, rfl⟩⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers a)
      (restrictₗ (m • B).divisorialSheaf hVU)
      (show Γ((m • B).divisorialSheaf, (X.basicOpen a)) from ⟨z.1.coeff m, z.2 m⟩)
    have hx1 : r ^ k * z.1.coeff m = ρ (x : (m • B).divisorialSubmodule U).1 := by
      have := congrArg (fun y : Γ((m • B).divisorialSheaf, (X.basicOpen a)) =>
        (y : (m • B).divisorialSubmodule (X.basicOpen a)).1) hx
      simp only at this
      refine Eq.trans ?_ this
      change _ = (X.presheaf.map (homOfLE hVU).op (a ^ k)) • z.1.coeff m
      rw [Algebra.smul_def, map_pow, map_pow]
    refine ⟨n + k, (algebraMap Γ(X, U) _ a) ^ k * q + (algebraMap Γ(X, U) _ a) ^ n *
      ⟨monomial m (x : (m • B).divisorialSubmodule U).1,
        monomial_mem_divisorialAlgebraSections B m (x : (m • B).divisorialSubmodule U).2⟩,
      ?_⟩
    rw [Finset.sum_insert hm]
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, hapow, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_monomial, hρa]
    rw [← hx1, ← hq, ← C_mul_monomial, C_pow]
    ring

/-- If a section of `R(X, B)(U)` restricts to zero on `X_a`, each of its coefficients is killed by
a power of `a`. -/
theorem exists_pow_mul_coeff_eq_zero_of_map_eq_zero {U : X.Opens} (a : Γ(X, U))
    (w : B.divisorialAlgebraSections U)
    (hw : w.1.map ((rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le a)).op).hom = 0)
    (m : ℕ) : ∃ k : ℕ, (algebraMap Γ(X, U) _ a) ^ k * w.1.coeff m = 0 := by
  have hVU : X.basicOpen a ≤ U := X.basicOpen_le a
  set ρ := ((rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le a)).op).hom
  have L (j : ℕ) := isLocalizedModule_divisorialSheaf_restrictₗ (j • B) a
  letI := moduleOfLE (m • B).divisorialSheaf hVU
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers a)
    (f := restrictₗ (m • B).divisorialSheaf hVU)
    (x₁ := (show Γ((m • B).divisorialSheaf, U) from ⟨w.1.coeff m, w.2 m⟩)) (x₂ := 0) (by
      rw [map_zero]
      apply Subtype.ext
      change ρ (w.1.coeff m) = 0
      rw [← Polynomial.coeff_map, hw, coeff_zero])
  refine ⟨k, ?_⟩
  have := congrArg (fun y : Γ((m • B).divisorialSheaf, U) =>
    (y : (m • B).divisorialSubmodule U).1) hk
  simp only [smul_zero] at this
  refine Eq.trans ?_ this
  change _ = a ^ k • w.1.coeff m
  rw [Algebra.smul_def, map_pow]

/-- For `a ∈ Γ(X, U)`, the restriction `R(X, B)(U) → R(X, B)(X_a)` is the localization away
from `a`; this is the algebraic content of quasi-coherence of the divisorial algebra. -/
theorem isLocalization_divisorialAlgebraSections_basicOpen {U : X.Opens} (a : Γ(X, U)) :
    letI := (B.divisorialAlgebraSectionsRestrict (X.basicOpen_le a)).toAlgebra
    IsLocalization.Away (algebraMap Γ(X, U) (B.divisorialAlgebraSections U) a)
      (B.divisorialAlgebraSections (X.basicOpen a)) := by
  letI := (B.divisorialAlgebraSectionsRestrict (X.basicOpen_le a)).toAlgebra
  have hVU : X.basicOpen a ≤ U := X.basicOpen_le a
  set ρ := ((rationalFunctionsPresheaf X).map (homOfLE hVU).op).hom
  set ra : Γ(X, (X.basicOpen a)) := X.presheaf.map (homOfLE hVU).op a
  set r : (rationalFunctionsPresheaf X).obj (op (X.basicOpen a)) :=
    algebraMap Γ(X, (X.basicOpen a)) _ ra
  have hρa : ρ (algebraMap Γ(X, U) _ a) = r :=
    MMP.Flips.rationalFunctionsPresheaf_map_algebraMap (homOfLE hVU) a
  have hres : ∀ w : B.divisorialAlgebraSections U,
      (algebraMap (B.divisorialAlgebraSections U)
        (B.divisorialAlgebraSections (X.basicOpen a)) w).1 =
        w.1.map ρ := fun w => B.coe_divisorialAlgebraSectionsRestrict hVU w
  have hapow : ∀ n : ℕ, ((algebraMap Γ(X, U) (B.divisorialAlgebraSections U) a) ^ n).1 =
      C (algebraMap Γ(X, U) _ a) ^ n := fun n => by
    rw [SubmonoidClass.coe_pow]
    rfl
  change IsLocalization (Submonoid.powers _) _
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow n ?_
    change IsUnit (B.divisorialAlgebraSectionsRestrict hVU (algebraMap Γ(X, U) _ a))
    rw [divisorialAlgebraSectionsRestrict_algebraMap]
    exact (X.toRingedSpace.isUnit_res_basicOpen a).map _
  · intro z
    obtain ⟨n, q, hq⟩ := B.exists_C_pow_mul_sum_monomial_eq_map a z z.1.support
    refine ⟨(q, ⟨_, n, rfl⟩), Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, hres, hres, hapow, Polynomial.map_pow, Polynomial.map_C, hρa,
      ← hq, ← z.1.as_sum_support, mul_comm]
  · intro x y hxy
    set w := x - y
    have hw : w.1.map ρ = 0 := by
      rw [← hres, map_sub, hxy, sub_self]; rfl
    choose k hk using B.exists_pow_mul_coeff_eq_zero_of_map_eq_zero a w hw
    set N := ∑ m ∈ w.1.support, k m
    refine ⟨⟨_, N, rfl⟩, ?_⟩
    rw [← sub_eq_zero, ← mul_sub]
    apply Subtype.ext
    rw [Subalgebra.coe_mul, hapow, ZeroMemClass.coe_zero, ← C_pow]
    ext m
    rw [coeff_C_mul, coeff_zero]
    by_cases hm : m ∈ w.1.support
    · have hle : k m ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm
      rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
      exact (congrArg _ (hk m)).trans (mul_zero _)
    · rw [Polynomial.notMem_support_iff.mp hm, mul_zero]

/-- Over a basic open, finite generation of the divisorial algebra is inherited from the
ambient affine open, and with the structure maps in the form the local properties of ring maps
ask for. -/
theorem finiteType_algebraMap_divisorialAlgebraSections_basicOpen {U : X.Opens}
    (hU : IsAffineOpen U) (a : Γ(X, U))
    (h : (algebraMap Γ(X, U) (B.divisorialAlgebraSections U)).FiniteType) :
    (algebraMap Γ(X, X.basicOpen a) (B.divisorialAlgebraSections (X.basicOpen a))).FiniteType := by
  letI := (B.divisorialAlgebraSectionsRestrict (X.basicOpen_le a)).toAlgebra
  haveI := B.isLocalization_divisorialAlgebraSections_basicOpen a
  haveI := hU.isLocalization_basicOpen a
  have key := RingHom.finiteType_isLocal.localizationAwayPreserves
    (algebraMap Γ(X, U) (B.divisorialAlgebraSections U)) a Γ(X, X.basicOpen a)
    (B.divisorialAlgebraSections (X.basicOpen a)) h
  convert key using 1
  refine IsLocalization.ringHom_ext (Submonoid.powers a) (RingHom.ext fun r => ?_)
  rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.Away.map, IsLocalization.map_eq]
  exact (B.divisorialAlgebraSectionsRestrict_algebraMap (X.basicOpen_le a) r).symm

/-- **Finite generation of the divisorial algebra is local.** If every point has an affine open
neighbourhood `U` on which `R(X, B)(U)` is a finitely generated `Γ(X, U)`-algebra, then
`R(X, B)(V)` is a finitely generated `Γ(X, V)`-algebra for every affine open `V`. -/
theorem finiteType_divisorialAlgebraSections_of_forall_exists
    (hR : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Algebra.FiniteType Γ(X, U) (B.divisorialAlgebraSections U))
    {V : X.Opens} (hV : IsAffineOpen V) :
    Algebra.FiniteType Γ(X, V) (B.divisorialAlgebraSections V) := by
  choose U hU hxU hUR using hR
  rw [← RingHom.finiteType_algebraMap]
  refine of_affine_open_cover (P := fun W : X.affineOpens =>
      (algebraMap Γ(X, W.1) (B.divisorialAlgebraSections W.1)).FiniteType)
    (fun x => ⟨U x, hU x⟩)
    (eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) ⟨V, hV⟩
    (fun W a hW => B.finiteType_algebraMap_divisorialAlgebraSections_basicOpen W.2 a hW)
    (fun W s hs hW => ?_) (fun x => RingHom.finiteType_algebraMap.mpr (hUR x))
  refine RingHom.finiteType_ofLocalizationSpan.ofIsLocalization
    RingHom.finiteType_respectsIso _ s hs fun a => ?_
  letI := (B.divisorialAlgebraSectionsRestrict (X.basicOpen_le a.1)).toAlgebra
  haveI := B.isLocalization_divisorialAlgebraSections_basicOpen a.1
  haveI := W.2.isLocalization_basicOpen a.1
  refine ⟨Γ(X, X.basicOpen a.1), B.divisorialAlgebraSections (X.basicOpen a.1), inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    algebraMap _ _, RingHom.ext fun r => ?_, hW a⟩
  exact (B.divisorialAlgebraSectionsRestrict_algebraMap (X.basicOpen_le a.1) r).symm

end MMP.Mori.Divisor

/-! ### Generation in degree one, and the cone algebra -/

namespace MMP.Mori.Divisor

open Stacks.RelativeProj Polynomial

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- On a normal scheme, every section of `𝒪_X(0)` over `U` is a regular function. -/
theorem divisorialSubmodule_zero_le_one (U : X.Opens) :
    (0 : Divisor X).divisorialSubmodule U ≤ 1 := by
  intro φ hφ
  obtain ⟨s, rfl⟩ := IsDivisorialSection.exists_eq hφ
  rw [Submodule.one_eq_range]
  exact ⟨s, rfl⟩

/-- A monomial of degree `n` whose coefficient lies in `(span R s) ^ n` lies in the subalgebra
generated by the degree-one monomials with coefficients in `s`. -/
theorem monomial_mem_adjoin_image_monomial_one_of_mem_span_pow {R A : Type*} [CommSemiring R]
    [CommSemiring A] [Algebra R A] {s : Set A} {n : ℕ} {c : A}
    (hc : c ∈ Submodule.span R s ^ n) :
    monomial n c ∈ Algebra.adjoin R (monomial 1 '' s) := by
  induction n generalizing c with
  | zero =>
    rw [pow_zero, Submodule.one_eq_range] at hc
    obtain ⟨r, rfl⟩ := hc
    rw [Algebra.linearMap_apply, monomial_zero_left, ← Polynomial.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ r
  | succ n ih =>
    rw [pow_succ] at hc
    refine Submodule.mul_induction_on hc (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · rw [← monomial_mul_monomial]
      refine mul_mem (ih ha) ?_
      induction hb using Submodule.span_induction with
      | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
      | zero =>
        rw [map_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        rw [map_add]
        exact add_mem hx hy
      | smul r x _ hx =>
        rw [← smul_monomial]
        exact Subalgebra.smul_mem _ hx r
    · rw [map_add]
      exact add_mem hx hy

/-- **Finite generation from degree-one generation.** If `𝒪_X(D)(U)` is a finite
`Γ(X, U)`-module and every section of `𝒪_X(nD)` over `U` is a sum of products of `n` sections of
`𝒪_X(D)`, then `R(X, D)(U)` is a finitely generated `Γ(X, U)`-algebra. -/
theorem finiteType_divisorialAlgebraSections_of_le_pow (D : Divisor X) {U : X.Opens}
    (hfin : Module.Finite Γ(X, U) (((1 : ℤ) • D).divisorialSubmodule U))
    (hgen : ∀ n : ℕ, ((n : ℤ) • D).divisorialSubmodule U ≤
      (((1 : ℤ) • D).divisorialSubmodule U) ^ n) :
    Algebra.FiniteType Γ(X, U) (D.divisorialAlgebraSections U) := by
  classical
  set M := ((1 : ℤ) • D).divisorialSubmodule U
  obtain ⟨S, hS⟩ : M.FG := (Module.Finite.iff_fg (N := M)).mp hfin
  have hM1 : ∀ c ∈ M, monomial 1 c ∈ D.divisorialAlgebraSections U := fun c hc =>
    monomial_mem_divisorialAlgebraSections D 1 (by rwa [one_smul, ← one_zsmul D])
  let G := S.image (monomial 1)
  have hGR : Algebra.adjoin Γ(X, U) (G : Set ((rationalFunctionsPresheaf X).obj (op U))[X]) ≤
      D.divisorialAlgebraSections U := by
    rw [Algebra.adjoin_le_iff]
    intro p hp
    rw [Finset.coe_image] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    exact hM1 c (hS ▸ Submodule.subset_span hc)
  have heq : D.divisorialAlgebraSections U = Algebra.adjoin Γ(X, U)
      (G : Set ((rationalFunctionsPresheaf X).obj (op U))[X]) := by
    refine le_antisymm (fun p hp => ?_) hGR
    rw [p.as_sum_support]
    refine Subalgebra.sum_mem _ fun n _ => ?_
    rw [Finset.coe_image]
    refine monomial_mem_adjoin_image_monomial_one_of_mem_span_pow ?_
    rw [hS]
    exact hgen n (by rw [natCast_zsmul]; exact hp n)
  rw [← Subalgebra.fg_iff_finiteType, heq]
  exact Subalgebra.fg_adjoin_finset G

variable [CompactSpace X] (D : Divisor X)

/-- The degree-`n` sections of `⨁ 𝒪_X(mD)` over `V` as rational functions, a linear map. -/
def sectionAlgebraAmbientₗ (n : ℕ) (V : X.Opens) :
    Γ((divisorialSectionAlgebra D).situation.pieceModules (n : ℤ), V) →ₗ[Γ(X, V)]
      (rationalFunctionsPresheaf X).obj (op V) :=
  (((n : ℤ) • D).divisorialSubmodule V).subtype

/-- The map `sectionAlgebraAmbientₗ D n V` is injective. -/
theorem sectionAlgebraAmbientₗ_injective (n : ℕ) (V : X.Opens) :
    Function.Injective (sectionAlgebraAmbientₗ D n V) :=
  Subtype.val_injective

/-- The rational function underlying `homogeneousPow V n z` is the product of the rational
functions underlying the `z i`. -/
theorem sectionAlgebraAmbientₗ_homogeneousPow (V : X.Opens) :
    ∀ (n : ℕ) (z : Fin n → Γ((divisorialSectionAlgebra D).situation.pieceModules (1 : ℤ), V)),
      sectionAlgebraAmbientₗ D n V ((divisorialSectionAlgebra D).situation.homogeneousPow V n z) =
        ∏ i, sectionAlgebraAmbientₗ D 1 V (z i)
  | 0, z => by rw [Fin.prod_univ_zero]; rfl
  | n + 1, z => by
    rw [Fin.prod_univ_castSucc, ← sectionAlgebraAmbientₗ_homogeneousPow V n]
    rfl

/-- The rational function underlying `pieceMul n 1 V a b` is the product of the rational functions
underlying `a` and `b`. -/
theorem sectionAlgebraAmbientₗ_pieceMul (n : ℕ) (V : X.Opens)
    (a : Γ((divisorialSectionAlgebra D).situation.pieceModules (n : ℤ), V))
    (b : Γ((divisorialSectionAlgebra D).situation.pieceModules (1 : ℤ), V)) :
    sectionAlgebraAmbientₗ D (n + 1) V ((divisorialSectionAlgebra D).situation.pieceMul n 1 V a b) =
      sectionAlgebraAmbientₗ D n V a * sectionAlgebraAmbientₗ D 1 V b := rfl

/-- `𝒪_X(D)(V)ⁿ` is contained in the image of the span of the products `homogeneousPow V n z`. -/
theorem pow_le_map_span_homogeneousPow (V : X.Opens) (n : ℕ) :
    (((1 : ℤ) • D).divisorialSubmodule V) ^ n ≤
      (Submodule.span Γ(X, V) (Set.range fun z =>
        (divisorialSectionAlgebra D).situation.homogeneousPow V n z)).map
        (sectionAlgebraAmbientₗ D n V) := by
  induction n with
  | zero =>
    rw [pow_zero, Submodule.one_eq_range]
    rintro _ ⟨r, rfl⟩
    refine ⟨r • (divisorialSectionAlgebra D).situation.homogeneousPow V 0 Fin.elim0,
      Submodule.smul_mem _ r (Submodule.subset_span ⟨_, rfl⟩), ?_⟩
    rw [map_smul, sectionAlgebraAmbientₗ_homogeneousPow, Fin.prod_univ_zero,
      Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    rw [pow_succ, Submodule.mul_le]
    intro φ hφ ψ hψ
    obtain ⟨a, ha, rfl⟩ := ih hφ
    let b : Γ((divisorialSectionAlgebra D).situation.pieceModules (1 : ℤ), V) :=
      (⟨ψ, hψ⟩ : ((1 : ℤ) • D).divisorialSubmodule V)
    exact ⟨_, MMP.RelativeProjSituation.pieceMul_mem_span_homogeneousPow
      (divisorialSectionAlgebra D).situation V n ha b, sectionAlgebraAmbientₗ_pieceMul D n V a b⟩

/-- **Degree-one generation of `⨁ 𝒪_X(nD)`.** If on every affine open `V` every section of
`𝒪_X(nD)` is a sum of products of `n` sections of `𝒪_X(D)`, the algebra is locally generated in
degree one. -/
theorem isLocallyDegreeOneGenerated_divisorialSectionAlgebra
    (h : ∀ V : X.Opens, IsAffineOpen V → ∀ n : ℕ,
      ((n : ℤ) • D).divisorialSubmodule V ≤ (((1 : ℤ) • D).divisorialSubmodule V) ^ n)
    (U : X.Opens) : (divisorialSectionAlgebra D).situation.IsLocallyDegreeOneGenerated U := by
  intro n a x hx
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  refine ⟨V, hVU, hxV, ?_⟩
  obtain ⟨b, hb, hba⟩ := pow_le_map_span_homogeneousPow D V n (h V hV n
    ((divisorialSectionAlgebra D).situation.pieceRestrict (n : ℤ) hVU a :
      ((n : ℤ) • D).divisorialSubmodule V).2)
  exact sectionAlgebraAmbientₗ_injective D n V (a₁ := b)
    (a₂ := (divisorialSectionAlgebra D).situation.pieceRestrict (n : ℤ) hVU a) hba ▸ hb

variable (B : Divisor X)

/-- If in every degree `m` the coefficients of `p` and `q` lie in `M ^ (m / e)` when `e ∣ m` and
vanish otherwise, the same holds for `p * q`. -/
theorem coeff_mul_mem_ite_pow {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (M : Submodule R A) {e : ℕ} (he : 0 < e) {p q : A[X]}
    (hp : ∀ m, p.coeff m ∈ if e ∣ m then M ^ (m / e) else ⊥)
    (hq : ∀ m, q.coeff m ∈ if e ∣ m then M ^ (m / e) else ⊥) (m : ℕ) :
    (p * q).coeff m ∈ if e ∣ m then M ^ (m / e) else ⊥ := by
  have hk {r : A[X]} (hr : ∀ m, r.coeff m ∈ if e ∣ m then M ^ (m / e) else ⊥) (k : ℕ) :
      r.coeff (e * k) ∈ M ^ k := by
    simpa only [dvd_mul_right, if_true, Nat.mul_div_cancel_left _ he] using hr (e * k)
  rw [coeff_mul]
  refine Submodule.sum_mem _ fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hi : e ∣ ij.1
  · by_cases hj : e ∣ ij.2
    · obtain ⟨i', hi'⟩ := hi
      obtain ⟨j', hj'⟩ := hj
      rw [← hij, hi', hj', ← mul_add]
      simp only [dvd_mul_right, if_true, Nat.mul_div_cancel_left _ he, pow_add]
      exact Submodule.mul_mem_mul (hk hp i') (hk hq j')
    · have hzj := hq ij.2
      simp only [if_neg hj, Submodule.mem_bot] at hzj
      rw [hzj, mul_zero]
      exact zero_mem _
  · have hyi := hp ij.1
    simp only [if_neg hi, Submodule.mem_bot] at hyi
    rw [hyi, zero_mul]
    exact zero_mem _

set_option backward.isDefEq.respectTransparency false in
/-- Every element of the subalgebra of `R(X, B)(U)` generated by the pieces of degrees `0` and `e`
has its degree-`m` coefficient in `𝒪_X(eB)(U) ^ (m / e)` when `e ∣ m`, and zero otherwise. -/
theorem coeff_toPolynomial_mem_of_mem_adjoin {e : ℕ} (he : 0 < e) {U : X.Opens}
    [Algebra Γ(X, U) ((divisorialSectionAlgebra B).situation.sectionRing U)]
    (hA : ∀ r : Γ(X, U),
      algebraMap Γ(X, U) ((divisorialSectionAlgebra B).situation.sectionRing U) r =
      (divisorialSectionAlgebra B).situation.sectionRingBaseMap U r) :
    ∀ y ∈ Algebra.adjoin Γ(X, U)
      (((divisorialSectionAlgebra B).situation.sectionRingGrading U 0 :
          Set ((divisorialSectionAlgebra B).situation.sectionRing U)) ∪
        ((divisorialSectionAlgebra B).situation.sectionRingGrading U e :
          Set ((divisorialSectionAlgebra B).situation.sectionRing U))),
      ∀ m, ((divisorialSectionAlgebra B).toPolynomial U y).coeff m ∈
        if e ∣ m then (((1 : ℤ) • (e • B)).divisorialSubmodule U) ^ (m / e) else ⊥ := by
  set M := ((1 : ℤ) • (e • B)).divisorialSubmodule U
  have hMe : ((e : ℕ) : ℤ) • B = (1 : ℤ) • (e • B) := by rw [one_smul, natCast_zsmul]
  let P : (divisorialSectionAlgebra B).situation.sectionRing U →+*
      ((rationalFunctionsPresheaf X).obj (op U))[X] :=
    (divisorialSectionAlgebra B).toPolynomial U
  have hP (m : ℕ) (c : (divisorialSectionAlgebra B).situation.sectionPieces U m) :
      P (DirectSum.of _ m c) = @monomial ((rationalFunctionsPresheaf X).obj (op U)) _ m
        ((divisorialSectionAlgebra B).pieceToRationalFunctions U m c) :=
    Fourfold.DivisorialSectionAlgebra.toPolynomial_of (divisorialSectionAlgebra B) U m c
  have hPmem (m : ℕ) (c : (divisorialSectionAlgebra B).situation.sectionPieces U m) :
      ((divisorialSectionAlgebra B).pieceToRationalFunctions U m c :
        (rationalFunctionsPresheaf X).obj (op U)) ∈ ((m : ℤ) • B).divisorialSubmodule U :=
    ((divisorialSectionAlgebra B).sectionEquiv _ (Int.natCast_nonneg m) U c).2
  let T : ℕ → Submodule Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)) := fun m =>
    if e ∣ m then M ^ (m / e) else ⊥
  show ∀ y ∈ _, ∀ m, (P y).coeff m ∈ T m
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    intro m
    rcases hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · rw [hP, coeff_monomial]
      split_ifs with hm
      · subst hm
        simp only [T, dvd_zero, if_true, Nat.zero_div, pow_zero]
        exact divisorialSubmodule_zero_le_one U ((zero_smul ℤ B) ▸ hPmem 0 c)
      · exact zero_mem _
    · rw [hP, coeff_monomial]
      split_ifs with hm
      · subst hm
        simp only [T, dvd_refl, if_true, Nat.div_self he, pow_one]
        exact (hMe ▸ hPmem e c : _ ∈ ((1 : ℤ) • (e • B)).divisorialSubmodule U)
      · exact zero_mem _
  | algebraMap r =>
    intro m
    have h0 : P (algebraMap Γ(X, U) _ r) = C (algebraMap Γ(X, U) _ r) := hA r ▸
      Fourfold.DivisorialSectionAlgebra.toPolynomial_sectionRingBaseMap
        (divisorialSectionAlgebra B) U r
    rw [h0, coeff_C]
    split_ifs with hm
    · subst hm
      simp only [T, dvd_zero, if_true, Nat.zero_div, pow_zero]
      exact Submodule.algebraMap_mem r
    · exact zero_mem _
  | add y z _ _ hy hz =>
    rw [map_add]
    exact fun m => (coeff_add (P y) (P z) m) ▸ add_mem (hy m) (hz m)
  | mul y z _ _ hy hz =>
    rw [map_mul]
    exact coeff_mul_mem_ite_pow M he hy hz

set_option backward.isDefEq.respectTransparency false in
/-- **Veronese generation, transported.** If over an open `U` the Veronese subring
`R(X, B)^{(e)}(U)` is generated by the pieces of degrees `0` and `e`, then every section of
`𝒪_X(n e B)` over `U` is a sum of products of `n` sections of `𝒪_X(eB)`. -/
theorem divisorialSubmodule_le_pow_of_adjoin_eq {e : ℕ} (he : 0 < e) {U : X.Opens}
    [Algebra Γ(X, U) ((divisorialSectionAlgebra B).situation.sectionRing U)]
    (hA : ∀ r : Γ(X, U),
      algebraMap Γ(X, U) ((divisorialSectionAlgebra B).situation.sectionRing U) r =
      (divisorialSectionAlgebra B).situation.sectionRingBaseMap U r)
    (h : Algebra.adjoin Γ(X, U)
          (((divisorialSectionAlgebra B).situation.sectionRingGrading U 0 :
              Set ((divisorialSectionAlgebra B).situation.sectionRing U)) ∪
            ((divisorialSectionAlgebra B).situation.sectionRingGrading U e :
              Set ((divisorialSectionAlgebra B).situation.sectionRing U))) =
        Algebra.adjoin Γ(X, U)
          {x : (divisorialSectionAlgebra B).situation.sectionRing U | ∀ n, ¬ e ∣ n →
            (DirectSum.decompose ((divisorialSectionAlgebra B).situation.sectionRingGrading U) x n :
              (divisorialSectionAlgebra B).situation.sectionRing U) = 0})
    (n : ℕ) :
    ((n : ℤ) • (e • B)).divisorialSubmodule U ≤
      (((1 : ℤ) • (e • B)).divisorialSubmodule U) ^ n := by
  set M := ((1 : ℤ) • (e • B)).divisorialSubmodule U
  let P : (divisorialSectionAlgebra B).situation.sectionRing U →+*
      ((rationalFunctionsPresheaf X).obj (op U))[X] :=
    (divisorialSectionAlgebra B).toPolynomial U
  intro a ha
  have hmem : a ∈ (((n * e : ℕ) : ℤ) • B).divisorialSubmodule U := by
    rwa [Nat.cast_mul, mul_smul, natCast_zsmul]
  let c : (divisorialSectionAlgebra B).situation.sectionPieces U (n * e) :=
    ((divisorialSectionAlgebra B).sectionEquiv _ (Int.natCast_nonneg _) U).symm ⟨a, hmem⟩
  have hx : P (DirectSum.of _ (n * e) c) = monomial (n * e) a := by
    change (divisorialSectionAlgebra B).toPolynomial U (DirectSum.of _ (n * e) c) = _
    rw [Fourfold.DivisorialSectionAlgebra.toPolynomial_of,
      Fourfold.DivisorialSectionAlgebra.pieceToRationalFunctions_apply, AddEquiv.apply_symm_apply]
    rfl
  have hxv : DirectSum.of _ (n * e) c ∈ Algebra.adjoin Γ(X, U)
      (((divisorialSectionAlgebra B).situation.sectionRingGrading U 0 :
          Set ((divisorialSectionAlgebra B).situation.sectionRing U)) ∪
        ((divisorialSectionAlgebra B).situation.sectionRingGrading U e :
          Set ((divisorialSectionAlgebra B).situation.sectionRing U))) := by
    rw [h]
    refine Algebra.subset_adjoin fun m hm => ?_
    exact DirectSum.decompose_of_mem_ne _ ⟨c, rfl⟩ fun h' => hm (h' ▸ dvd_mul_left e n)
  have : (P (DirectSum.of _ (n * e) c)).coeff (n * e) ∈
      if e ∣ n * e then M ^ (n * e / e) else ⊥ :=
    coeff_toPolynomial_mem_of_mem_adjoin B he hA _ hxv (n * e)
  rw [hx, coeff_monomial, if_pos rfl] at this
  simpa only [dvd_mul_left, if_true, Nat.mul_div_cancel _ he] using this

/-- **The divisorial algebra is the graded algebra of a cone.** If `𝒪_X(D)` is coherent and on
every affine open every section of `𝒪_X(nD)` is a sum of products of `n` sections of `𝒪_X(D)`,
then `⨁_{n ≥ 0} 𝒪_X(nD)` satisfies Fulton's hypotheses on the graded algebra of a cone
(`MMP.Intersection.Scheme.IsConeAlgebra`): its degree-zero piece is `𝒪_X`, its degree-one piece
is coherent, and it is generated in degree one over every affine open. -/
theorem isConeAlgebra_divisorialSectionAlgebra
    (hcoh : Stacks.SheafOfModules.IsCoherent ((sectionGradedAlgebra D).piece 1))
    (hgen : ∀ V : X.Opens, IsAffineOpen V → ∀ n : ℕ,
      ((n : ℤ) • D).divisorialSubmodule V ≤ (((1 : ℤ) • D).divisorialSubmodule V) ^ n) :
    MMP.Intersection.Scheme.IsConeAlgebra (divisorialSectionAlgebra D).situation where
  bijective_smul_one U := (divisorialSectionAlgebra D).situation.bijective_smul_one_of_isoUnit
    (sectionAlgebraDegreeZeroIso D) (sectionAlgebraDegreeZeroIso_one D) U
  isCoherent_one := hcoh
  locally_generatedInDegreeOne x := by
    obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ (⊤ : X.Opens) from trivial)
    refine ⟨V, hxV, hV,
      MMP.RelativeProjSituation.isGeneratedInDegreeOne_of_mem_span_homogeneousPow
        (divisorialSectionAlgebra D).situation V fun n a => ?_⟩
    obtain ⟨b, hb, hba⟩ := pow_le_map_span_homogeneousPow D V n (hgen V hV n
      (a : ((n : ℤ) • D).divisorialSubmodule V).2)
    exact sectionAlgebraAmbientₗ_injective D n V (a₁ := b) (a₂ := a) hba ▸ hb

end MMP.Mori.Divisor

namespace MMP.Fourfold.DivisorialSectionAlgebra

open MMP.Mori Polynomial

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y}

/-- Over a nonempty open of an integral scheme, the ring of sections of a divisorial section
algebra along the identity is a domain: it embeds in `K(Y)[t]`. -/
theorem isDomain_sectionRing [IsIntegral Y] (A : DivisorialSectionAlgebra (𝟙 Y) D) (U : Y.Opens)
    (hU : (U : Set Y).Nonempty) : IsDomain (A.situation.sectionRing U) := by
  have hcomp : irreducibleComponents Y = {Set.univ} := irreducibleComponents_eq_singleton
  let Z : irreducibleComponents Y := ⟨Set.univ, hcomp ▸ rfl⟩
  have hZ : componentGenericPoint Y Z ∈ (𝟙 Y) ⁻¹ᵁ U :=
    ((isGenericPoint_componentGenericPoint Y Z).mem_open_set_iff U.isOpen).2 (by simpa [Z] using hU)
  have : Subsingleton (irreducibleComponents Y) := by
    rw [hcomp]
    infer_instance
  letI : Unique {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ (𝟙 Y) ⁻¹ᵁ U} :=
    uniqueOfSubsingleton ⟨Z, hZ⟩
  letI : Field (Y.presheaf.stalk (componentGenericPoint Y Z)) :=
    (RationalFunctions.isField_stalk Y Z).toField
  let e : (rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ U)) ≃+*
      Y.presheaf.stalk (componentGenericPoint Y Z) :=
    RingEquiv.piUnique (fun Z' : {Z : irreducibleComponents Y //
      componentGenericPoint Y Z ∈ (𝟙 Y) ⁻¹ᵁ U} => Y.presheaf.stalk (componentGenericPoint Y Z'.1))
  have : IsDomain ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ U)))[X] :=
    MulEquiv.isDomain _ (Polynomial.mapEquiv e).toMulEquiv
  exact Function.Injective.isDomain (A.toPolynomial U) (A.toPolynomial_injective U)

end MMP.Fourfold.DivisorialSectionAlgebra
