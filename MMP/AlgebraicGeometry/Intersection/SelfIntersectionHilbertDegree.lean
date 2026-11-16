module
public import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
public import MMP.AlgebraicGeometry.Intersection.CurveCartierLocal
public import MMP.AlgebraicGeometry.Cohomology.ProperCoherentSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Curves.SingularGenusZero
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.LocalDimension

/-!
# Intersection numbers, arithmetic genus and projective morphisms

This file collects foundational facts on intersection numbers and curves.

* For a proper scheme `X` over a field `k`, an invertible sheaf `L` on `X` and a closed
  subscheme `Z ⊆ X` of dimension `d`, the self-intersection number `(L^d · Z)` equals the degree
  `deg_L Z`, the `d`-th difference of the Hilbert polynomial `t ↦ χ(Z, L|_Z^{⊗ t})`. For a
  closed subscheme `X ⊆ ℙᴺ_k` and `L = 𝒪_X(1)` this says that the repeated hyperplane
  intersection `(H^d · Z)` is the projective degree `deg Z`. Writing `M = L|_Z`, both sides are
  alternating sums of Euler characteristics on `Z`; by Snapper's theorem the first is the mixed
  difference of `n ↦ χ(Z, M^{⊗ n_1} ⊗ ⋯ ⊗ M^{⊗ n_d})` at the indicator vectors, where the
  twist by `1_T` is `M^{⊗ |T|}`, and grouping the subsets `T` by cardinality gives the second.
* For varieties over `k`: finite morphisms are projective, projective morphisms compose,
  projectivity and properness are preserved by restriction to a closed subvariety of the source
  and cancel against a morphism of varieties, and properness is local on the target.
* On a smooth surface `Y` over an algebraically closed field `k` of characteristic zero, let `C`
  be a proper curve and `D` an effective divisor not containing `C`. Then `C ∩ Supp D` is finite
  and `(D · C) = ∑_{q ∈ C ∩ Supp D} i_q(D, C)`. Every divisor on `Y` is Cartier; the pull-back to
  `C` of the canonical section of `𝒪_Y(D)` has a finite zero scheme `Z` supported on
  `C ∩ Supp D`, and `(D · C) = dim_k Γ(Z, 𝒪_Z)` is the sum of the dimensions of the local rings
  `𝒪_{Y,q} / (I_{C,q} + I_{D,q})`.
* For an integral scheme `C` proper over an algebraically closed field `k` with `dim C ≤ 1`, the
  constants `k → Γ(C, 𝒪_C)` are bijective and `p_a(C) = 1 - χ(𝒪_C) = dim_k H¹(C, 𝒪_C) ≥ 0`. If
  `C` is a curve, `p_a(C) = 0` exactly when `C ≅ ℙ¹_k` over `k`: a singular point would make
  the normalization a projective line over a nontrivial finite extension of `k`
  [Stacks, Tag 0DJB], so `C` is regular, carries an invertible sheaf of degree one at a closed
  point, and is `ℙ¹_k` by [Stacks, Tag 0C6U].

## Main results

* `MMP.Mori.sheafSelfIntersectionNumber_eq_hilbertDegree`: `(L^d · Z) = deg_L Z`.
* `MMP.Foundations.projective_proper_operations_of_isVariety`: operations on projective and
  proper morphisms of varieties, as one conjunction.
* `MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber`: `C ∩ Supp D` is finite and
  `(D · C) = ∑_{q ∈ C ∩ Supp D} i_q(D, C)`.
* `MMP.Mori.arithmeticGenus_eq_finrank_cohomologyOverField_one`: `Γ(C, 𝒪_C) = k`,
  `p_a(C) = dim_k H¹(C, 𝒪_C)` and `0 ≤ p_a(C)`.
* `MMP.Mori.arithmeticGenus_nonneg_and_eq_zero_iff`: `0 ≤ p_a(C)`, and `p_a(C) = 0` if and only
  if `C ≅ ℙ¹_k` over `k`.

## Implementation notes

The degree statement is made for an arbitrary proper `k`-scheme `X` and invertible sheaf `L`, of
which a closed subscheme of `ℙᴺ_k` with `𝒪_X(1)` is the case of the source. A closed subvariety
of the source of a morphism is a closed immersion `i : Z ⟶ X` of varieties, and the restriction
is `i ≫ f`. A curve on the smooth surface `Y` is a prime divisor `C`, its intersection number
with `D` is `MMP.Mori.IsIntersectionNumber` for `Divisor.toQDivisor D`, and the sum is a
`finsum` over `C ∩ Supp D`. `H⁰(C, 𝒪_C) = k` is bijectivity of `f.appTop`, and the projective
line is the glued model `AlgebraicGeometry.projectiveLine k`, with the isomorphism commuting with
the structure morphisms to `Spec k`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.33–1.36, 4
* [R. Hartshorne, *Algebraic Geometry*][Hartshorne], I Thm. 3.4, III Ex. 5.3
* [The Stacks Project][stacks-project], Tags 01W8, 0DJB, 0C6U
-/

universe u

open CategoryTheory AlgebraicGeometry

/-! ### Hyperplane intersections and the degree -/

namespace MMP.Mori

/-- Twisting the constant family `(L|_Z, …, L|_Z)` by the indicator vector of `T` gives the
`|T|`-th tensor power of `L|_Z`, so its Euler characteristic is the Hilbert function at `|T|`. -/
private lemma eulerCharacteristic_twistedSheaf_indicator (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    {d : ℕ} (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (T : Finset (Fin d)) :
    @eulerCharacteristic k _ Z (i ≫ f) inferInstance
        (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun _ => (Scheme.Modules.pullback i).obj L) (fun j => if j ∈ T then 1 else 0))
        (isCoherent_twistedSheafUnitPullback k f i (fun _ => L)
          fun j => if j ∈ T then 1 else 0) =
      MMP.Mori.subschemeHilbertFunction k f i L T.card := by
  have hs : (∑ j : Fin d, if j ∈ T then (1 : ℤ) else 0) = ∑ _j : Fin 1, (T.card : ℤ) := by
    simp [Finset.sum_boole]
  exact @eulerCharacteristic_eq_of_iso k _ Z (i ≫ f) _ _ _
    (isCoherent_twistedSheafUnitPullback k f i (fun _ => L) _)
    (isCoherent_twistedSheafUnitPullback k f i (fun _ : Fin 1 => L) _)
    (MMP.Mori.Twist.twistedSheafUnitIsoTensorPower _ _ (fun _ => Iso.refl _) _ ≪≫
      eqToIso (congrArg (Stacks.SheafOfModules.Invertible.tensorPower Z.presheaf
        Z.ringCatSheaf.2 ((Scheme.Modules.pullback i).obj L)) hs) ≪≫
      (MMP.Mori.Twist.twistedSheafUnitIsoTensorPower _ _ (fun _ => Iso.refl _) _).symm)

/-- **The self-intersection of `L` with `Z` is the `L`-degree of `Z` (KM 1.36).** For a proper
`k`-scheme `X`, an invertible sheaf `L` on `X` and a closed subscheme `i : Z ⟶ X` of dimension
`d`, the intersection number `(L^d · Z)` equals the degree `deg_L Z`, the `d`-th difference of
`t ↦ χ(Z, L|_Z^{⊗ t})`. For `X ⊆ ℙᴺ_k` and `L = 𝒪_X(1)` this is `(H^d · Z) = deg Z`. -/
@[mmp "lem_mmp_foundation_km_hyperplane_intersection_degree"]
public theorem sheafSelfIntersectionNumber_eq_hilbertDegree (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z = d) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    sheafSelfIntersectionNumber k f i d hd.le L = hilbertDegree k f i d hd L := by
  classical
  rw [MMP.Mori.sheafSelfIntersectionNumber,
    MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    intersectionNumber_eq_sum_eulerCharacteristic, MMP.Mori.hilbertDegree]
  simp_rw [eulerCharacteristic_twistedSheaf_indicator]
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card
    (fun m => (-1 : ℤ) ^ (d - m) * MMP.Mori.subschemeHilbertFunction k f i L m)]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by push_cast; ring

end MMP.Mori

/-! ### Projective and proper morphisms of varieties -/

namespace MMP.Foundations

/-- For varieties over a field `k`: finite morphisms are projective; composites of projective
morphisms are projective; the restriction `i ≫ f` of a projective (resp. proper) morphism `f`
to a closed subvariety `i : Z ⟶ X` is projective (resp. proper); if `u ≫ g` is proper
(resp. projective) then so is `u`; and properness of a morphism of schemes is local on the
target. -/
@[mmp "lem_mmp_foundation_km_projective_proper_operations"]
public theorem projective_proper_operations_of_isVariety (k : Type u) [Field k] :
    -- finite morphisms of varieties are projective
    (∀ {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)),
      IsVariety k sX → IsVariety k sY → ∀ (f : X ⟶ Y), f ≫ sY = sX →
        IsFinite f → IsProjective f) ∧
    -- a composite of projective morphisms of varieties is projective
    (∀ {X Y Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
      (sZ : Z ⟶ Spec (.of k)), IsVariety k sX → IsVariety k sY → IsVariety k sZ →
        ∀ (f : X ⟶ Y) (g : Y ⟶ Z), f ≫ sY = sX → g ≫ sZ = sY →
          IsProjective f → IsProjective g → IsProjective (f ≫ g)) ∧
    -- restriction to a closed subvariety of the source
    (∀ {Z X Y : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
      (sY : Y ⟶ Spec (.of k)), IsVariety k sZ → IsVariety k sX → IsVariety k sY →
        ∀ (i : Z ⟶ X) (f : X ⟶ Y), IsClosedImmersion i → i ≫ sX = sZ → f ≫ sY = sX →
          (IsProjective f → IsProjective (i ≫ f)) ∧ (IsProper f → IsProper (i ≫ f))) ∧
    -- cancellation
    (∀ {X Y S : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
      (sS : S ⟶ Spec (.of k)), IsVariety k sX → IsVariety k sY → IsVariety k sS →
        ∀ (u : X ⟶ Y) (g : Y ⟶ S), u ≫ sY = sX → g ≫ sS = sY →
          (IsProper (u ≫ g) → IsProper u) ∧ (IsProjective (u ≫ g) → IsProjective u)) ∧
    -- properness is local on the target
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens), (⨆ i, U i) = ⊤ →
      (IsProper f ↔ ∀ i, IsProper (f ∣_ U i))) := by
  refine ⟨fun _ _ _ _ f _ _ => Stacks.FiniteMorphismProjective.isProjective_of_isFinite f, ?_, ?_,
      ?_,
    fun f _ U hU => IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsProper) (f := f) U hU⟩
  · intro X Y Z sX sY sZ _ _ hZ f g _ _ hf hg
    have := QuasiCompact.compactSpace_of_compactSpace sZ
    have := quasiSeparatedSpace_of_quasiSeparated sZ
    exact hf.comp hg
  · intro Z X Y sZ sX sY _ _ hY i f _ _ _
    have := QuasiCompact.compactSpace_of_compactSpace sY
    have := quasiSeparatedSpace_of_quasiSeparated sY
    exact ⟨(Stacks.FiniteMorphismProjective.isProjective_of_isFinite i).comp, fun _ =>
        inferInstance⟩
  · intro X Y S sX sY sS _ _ _ u g _ hg
    have : IsSeparated (g ≫ sS) := hg ▸ inferInstance
    have : IsSeparated g := .of_comp g sS
    exact ⟨fun _ => IsProper.of_comp u g, IsProjective.of_comp u g⟩

end MMP.Foundations

/-! ### Local intersection numbers on a smooth surface -/

namespace MMP.Mori

section LocalIntersection

open Opposite TopologicalSpace

section Local

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- A regular function whose germs are non-zero-divisors on `W` defines a rational function. -/
private theorem exists_units_eq_germ (W : Y.Opens) (f : Γ(Y, W))
    (hnzd : ∀ y (hy : y ∈ W), (Y.presheaf.germ W y hy).hom f ∈
      nonZeroDivisors (Y.presheaf.stalk y)) :
    ∃ φ : (RationalFunctions Y)ˣ, ∀ (Z : irreducibleComponents Y)
      (hZ : componentGenericPoint Y Z ∈ W),
        (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom f := by
  classical
  let u : ∀ Z : irreducibleComponents Y, (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ :=
    fun Z => if h : componentGenericPoint Y Z ∈ W then
      (by
        letI := (RationalFunctions.isField_stalk Y Z).toField
        exact (isUnit_iff_ne_zero.2 (nonZeroDivisors.ne_zero (hnzd _ h))).unit)
      else 1
  refine ⟨(RationalFunctions.unitsEquiv Y).symm u, fun Z hZW => ?_⟩
  change ((u Z : (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ) :
    Y.presheaf.stalk (componentGenericPoint Y Z)) = _
  simp only [u]
  rw [dif_pos hZW]
  rfl

/-- Near any point `q`, a prime divisor `P` on a smooth scheme has a local equation `φ` which is a
regular function `f` on an open `W ∋ q` and whose germ at `q` generates the ideal of `P`. -/
private theorem exists_localEquation_single (hsm : IsSmoothScheme sY) (P : Mori.PrimeDivisor Y)
    (q : Y) :
    ∃ (W : Y.Opens) (hq : q ∈ W) (f : Γ(Y, W)) (φ : (RationalFunctions Y)ˣ),
      Divisor.IsLocalEquation (Finsupp.single P 1 : Divisor Y) W φ ∧
      (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ W),
        (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom f) ∧
      IdealSheafData.stalk P.idealSheaf q = Ideal.span {(Y.presheaf.germ W q hq).hom f} := by
  classical
  haveI := P.integral
  obtain ⟨W, hW, hxW, f, hf, hspan⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
      P.idealSheaf
        (Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P) q
  have hgerm : ∀ y (hy : y ∈ W), IdealSheafData.stalk P.idealSheaf y =
      Ideal.span {(Y.presheaf.germ W y hy).hom f} := fun y hy => by
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf y ⟨W, hW⟩ hy, hspan,
      Ideal.map_span, Set.image_singleton]
  have hnzd : ∀ y (hy : y ∈ W), (Y.presheaf.germ W y hy).hom f ∈
      nonZeroDivisors (Y.presheaf.stalk y) := fun y hy =>
    Stacks.Divisors.germ_mem_nonZeroDivisors hW hf y hy
  obtain ⟨φ, hφ⟩ := exists_units_eq_germ W f hnzd
  refine ⟨W, hxW, f, φ, ?_, hφ, hgerm q hxW⟩
  rintro E ⟨y, hyE, hyW⟩
  have hηW : E.genericPoint ∈ W := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
    exact (specializes_iff_mem_closure.mpr hyE).mem_open W.isOpen hyW
  have key : E.toComponent.hom ((Y.presheaf.germ W _ hηW).hom f) =
      (φ : RationalFunctions Y) E.component := by
    rw [hφ _ (E.specializes_genericPoint.mem_open W.isOpen hηW)]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  by_cases hEP : P = E
  · subst hEP
    rw [DivisorWithCoeffs.coeff_single_self]
    have hmem : P.genericPoint ∈ P.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have hprime : Prime ((Y.presheaf.germ W _ hηW).hom f) := by
      rw [← Ideal.span_singleton_prime (nonZeroDivisors.ne_zero (hnzd _ hηW)), ← hgerm _ hηW]
      obtain ⟨y', hy'⟩ : P.genericPoint ∈ Set.range P.idealSheaf.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact hmem
      rw [← hy', ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
      exact RingHom.ker_isPrime _
    exact (P.ord_eq_one_of_irreducible hprime.irreducible key).symm
  · rw [DivisorWithCoeffs.coeff_single_of_ne hEP]
    have hnm : E.genericPoint ∉ P.support := fun h =>
      hEP (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support P E h)
    have htop := (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support
      P.idealSheaf _).2 hnm
    rw [hgerm _ hηW, Ideal.span_singleton_eq_top] at htop
    exact (E.ord_eq_zero_of_isUnit htop key).symm

private theorem ord_prod {s : Finset (Mori.PrimeDivisor Y)} (E : Mori.PrimeDivisor Y)
    (φ : Mori.PrimeDivisor Y → (RationalFunctions Y)ˣ) :
    E.ord (∏ P ∈ s, φ P) = ∑ P ∈ s, E.ord (φ P) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, PrimeDivisor.ord_mul, ih]

/-- Near any point `q`, an effective divisor `D` on a smooth scheme has a local equation `φ` which
is a regular function `f` on an affine open `W ∋ q` and whose germ at `q` generates the ideal
`I_{D,q} = ∏_E I_{E,q}^{d_E}`. -/
private theorem exists_localEquation_span_eq_localIdeal (hsm : IsSmoothScheme sY) (D : Divisor Y)
    (hD : 0 ≤ D) (q : Y) :
    ∃ (W : Y.affineOpens) (hq : q ∈ (W : Y.Opens)) (f : Γ(Y, (W : Y.Opens)))
      (φ : (RationalFunctions Y)ˣ), D.IsLocalEquation W φ ∧
      (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (W : Y.Opens)),
        (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom f) ∧
      Ideal.span {(Y.presheaf.germ W q hq).hom f} = localIdeal q D := by
  classical
  choose W' hq' f' φ' hloc' hφ' hst' using fun P => exists_localEquation_single hsm P q
  set U : Y.Opens := D.support.inf W' with hU
  have hqU : q ∈ U := by
    rw [← SetLike.mem_coe, hU, Opens.coe_finset_inf, Finset.inf_eq_iInf]
    simp only [Function.comp_apply, Set.iInf_eq_iInter, Set.mem_iInter, SetLike.mem_coe]
    exact fun P _ => hq' P
  obtain ⟨_, ⟨V, hV, rfl⟩, hqV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hqU U.isOpen
  have hle : ∀ P ∈ D.support, V ≤ W' P := fun P hP => (Set.Subset.trans hVU
    (Finset.inf_le (f := W') hP : U ≤ W' P))
  let n : Mori.PrimeDivisor Y → ℕ := fun P => (D P).toNat
  let g : D.support → Γ(Y, V) := fun P => Y.presheaf.map (homOfLE (hle P.1 P.2)).op (f' P.1)
  have hgerm : ∀ (P : D.support) (y : Y) (hy : y ∈ V),
      (Y.presheaf.germ V y hy).hom (g P) =
        (Y.presheaf.germ (W' P.1) y (hle P.1 P.2 hy)).hom (f' P.1) :=
    fun P y hy => Y.presheaf.germ_res_apply _ _ _ _
  refine ⟨⟨V, hV⟩, hqV, ∏ P ∈ D.support.attach, g P ^ n P, ∏ P ∈ D.support, φ' P ^ n P,
    ?_, ?_, ?_⟩
  · rintro E ⟨y, hyE, hyV⟩
    rw [ord_prod]
    simp only [PrimeDivisor.ord_pow]
    have hE : ∀ P ∈ D.support, E.ord (φ' P) = if P = E then 1 else 0 := by
      intro P hP
      rw [← hloc' P E ⟨y, hyE, hle P hP hyV⟩]
      by_cases h : P = E
      · subst h; simp [DivisorWithCoeffs.coeff_single_self]
      · rw [if_neg h, DivisorWithCoeffs.coeff_single_of_ne h]
    rw [Finset.sum_congr rfl fun P hP => by rw [hE P hP]]
    simp only [nsmul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
    rw [DivisorWithCoeffs.coeff_apply]
    split_ifs with h
    · exact (Int.toNat_of_nonneg (hD E)).symm
    · exact Finsupp.notMem_support_iff.1 h
  · intro Z hZ
    rw [Units.coe_prod, Finset.prod_apply, map_prod, ← Finset.prod_attach]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [Units.val_pow_eq_pow_val, Pi.pow_apply, map_pow, hgerm, hφ']
  · rw [map_prod, ← Ideal.prod_span_singleton, localIdeal,
      ← Finset.prod_attach D.support (fun E => IdealSheafData.stalk E.idealSheaf q ^ (D E).toNat)]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [map_pow, ← Ideal.span_singleton_pow, hgerm, hst']

/-- The stalk at `q` of the zero scheme of the canonical section of `𝒪_Y(D)`, for an effective
divisor `D` on a smooth scheme, is `I_{D,q}`. -/
private theorem stalk_zeroScheme_oneSection [CompactSpace Y] (hsm : IsSmoothScheme sY)
    (D : Divisor Y) (hD : 0 ≤ D) (hcart : D.IsCartier) (q : Y) :
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      D.divisorialSheaf := hcart.isInvertibleModule_divisorialSheaf
    IdealSheafData.stalk (zeroScheme Y D.divisorialSheaf (MMP.Threefold.Mori.oneSection hD)) q =
      localIdeal q D := by
  haveI := hcart.isInvertibleModule_divisorialSheaf
  obtain ⟨W, hq, f, φ, hloc, hφ, hspan⟩ := exists_localEquation_span_eq_localIdeal hsm D hD q
  obtain ⟨V, hqV, hVW, ⟨b⟩⟩ :=
    AlgebraicGeometry.exists_affineOpen_dualBasisOne_of_isInvertible D.divisorialSheaf q hq
  have hone : MMP.Threefold.Mori.oneSection hD =
      (Divisor.divisorialSheafOneSection hD).eval (op ⊤) :=
    Subtype.ext ((Divisor.coe_structureSheafToDivisorialSheaf_app hD ⊤ 1).trans (map_one _))
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ q V hqV, hone]
  erw [AlgebraicGeometry.zeroScheme_ideal_eq_span_evalAt D.divisorialSheaf _ V b]
  rw [MMP.Threefold.Resolution.span_evalAt_eq_span_of_isLocalEquation_of_nonneg D hD (V : Y.Opens) b
      (Y.presheaf.map (homOfLE hVW).op f) φ (hloc.mono hVW) fun Z hZ => by
        rw [hφ Z (hVW hZ)]
        exact (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hVW) _ hZ f).symm,
    Ideal.map_span, Set.image_singleton, ← hspan]
  congr 2
  exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hVW) _ hqV f

end Local

section Global

variable {k : Type u} [Field k]

/-- On a smooth scheme every divisor is Cartier. -/
private theorem isCartier_of_isSmoothScheme {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    [IsLocallyNoetherian Y] [IsNormal Y] (hsm : IsSmoothScheme sY) (D : Divisor Y) :
    D.IsCartier := by
  induction D using Finsupp.induction_linear with
  | zero => exact Divisor.isCartier_zero
  | add f g hf hg => exact hf.add hg
  | single E n =>
    have := (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm E).zsmul n
    simpa [Finsupp.smul_single] using this

/-- On an integral scheme of dimension at most one, proper over a field, a closed subset which is
not everything is finite. -/
private theorem finite_of_isClosed {C : Scheme.{u}} (g : C ⟶ Spec (.of k)) [IsProper g]
    [IsIntegral C] (hdim : topologicalKrullDim C ≤ 1) {S : Set C} (hS : IsClosed S)
    (hne : ∃ c, c ∉ S) : S.Finite := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace C := (quasiCompact_iff_compactSpace g).1 inferInstance
  have : IsNoetherian C := ⟨⟩
  have hg : genericPoint C ∉ S := by
    intro h
    obtain ⟨c, hc⟩ := hne
    exact hc (hS.closure_subset_iff.2 (Set.singleton_subset_iff.2 h)
      ((genericPoint_spec C).specializes (Set.mem_univ c)).mem_closure)
  have := Stacks.CurveProjectiveCompletion.finite_compl_of_genericPoints_subset (Z := C)
    hS.isOpen_compl hdim (by
      intro x hx
      rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
      exact hx ▸ hg)
  have h2 : S.Finite ∧ ∀ z ∈ S, IsClosed ({z} : Set C) := by simpa using this
  exact h2.1

/-- If a morphism of `k`-schemes is surjective on the stalk at `a`, the local ring at `a` is,
as a `k`-vector space, the quotient of the local ring at the image by the kernel. -/
private theorem finrank_stalk_eq_finrank_quotient_ker {A B : Scheme.{u}} (sB : B ⟶ Spec (.of k))
    (j : A ⟶ B) (a : A) (hj : Function.Surjective (j.stalkMap a)) :
    letI := stalkAlgebra (j ≫ sB) a
    letI := stalkAlgebra sB (j a)
    Module.finrank k (A.presheaf.stalk a) =
      Module.finrank k (B.presheaf.stalk (j a) ⧸ RingHom.ker (j.stalkMap a).hom) := by
  letI := stalkAlgebra (j ≫ sB) a
  letI := stalkAlgebra sB (j a)
  let ψ : B.presheaf.stalk (j a) →ₐ[k] A.presheaf.stalk a :=
    { (j.stalkMap a).hom with
      commutes' := fun c => MMP.Threefold.Resolution.stalkMap_algebraMap (sX := sB) j a c }
  exact (Ideal.quotientKerAlgEquivOfSurjective (f := ψ) hj).toLinearEquiv.finrank_eq.symm

/-- The ideal `I_{D,q}` of the divisor `1 · C` is the stalk of the ideal sheaf of `C`. -/
private theorem localIdeal_single_one {Y : Scheme.{u}} (C : Mori.PrimeDivisor Y) (q : Y) :
    localIdeal q (Finsupp.single C 1) = IdealSheafData.stalk C.idealSheaf q := by
  rw [localIdeal, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.prod_singleton,
    Finsupp.single_eq_same]
  simp

/-- Let `s` be the pull-back to a prime divisor `C` of the canonical section of `𝒪_Y(D)`, `D`
effective on a smooth scheme. At a point `z` of the zero scheme of `s` lying over `q`, the local
ring is `𝒪_{Y,q} / (I_{D,q} + I_{C,q})`, so its `k`-dimension is `i_q(D, C)`. -/
private theorem finrank_stalk_zeroScheme_eq_localIntersectionNumber {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (hsm : IsSmoothScheme sY) (C : Mori.PrimeDivisor Y) {D : Divisor Y} (heff : 0 ≤ D)
    (hcart : D.IsCartier)
    [SheafOfModules.IsInvertible C.idealSheaf.subscheme.sheaf.obj
      C.idealSheaf.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj D.divisorialSheaf)]
    {s : Γ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj D.divisorialSheaf, ⊤)}
    (hs : s = pullbackGlobalSections C.idealSheaf.subschemeι D.divisorialSheaf
      (MMP.Threefold.Mori.oneSection heff))
    {Z : C.idealSheaf.subscheme.IdealSheafData} (hZ : Z = zeroScheme C.idealSheaf.subscheme _ s)
    (z : Z.subscheme) :
    letI := stalkAlgebra (Z.subschemeι ≫ C.idealSheaf.subschemeι ≫ sY) z
    Module.finrank k (Z.subscheme.presheaf.stalk z) =
      localIntersectionNumber sY (C.idealSheaf.subschemeι (Z.subschemeι z)) D
        (Finsupp.single C 1) := by
  have hcomp : ((Z.subschemeι ≫ C.idealSheaf.subschemeι).stalkMap z).hom =
      (Z.subschemeι.stalkMap z).hom.comp
        (C.idealSheaf.subschemeι.stalkMap (Z.subschemeι z)).hom := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  have hj : Function.Surjective ((Z.subschemeι ≫ C.idealSheaf.subschemeι).stalkMap z) := by
    change Function.Surjective ((Z.subschemeι ≫ C.idealSheaf.subschemeι).stalkMap z).hom
    rw [hcomp]
    exact (Z.subschemeι.stalkMap_surjective z).comp (C.idealSheaf.subschemeι.stalkMap_surjective _)
  have h1 := finrank_stalk_eq_finrank_quotient_ker sY (Z.subschemeι ≫ C.idealSheaf.subschemeι) z hj
  rw [Category.assoc] at h1
  have hker : RingHom.ker ((Z.subschemeι.stalkMap z).hom.comp
      (C.idealSheaf.subschemeι.stalkMap (Z.subschemeι z)).hom) =
      localIdeal (C.idealSheaf.subschemeι (Z.subschemeι z)) D ⊔
        localIdeal (C.idealSheaf.subschemeι (Z.subschemeι z)) (Finsupp.single C 1) := by
    rw [← RingHom.comap_ker, Stacks.Chow.ker_stalkMap_subschemeι_eq_stalk Z z]
    subst hZ hs
    haveI := hcart.isInvertibleModule_divisorialSheaf
    change Ideal.comap _ (IdealSheafData.stalk (Stacks.Divisors.zeroScheme _ _ _) _) = _
    rw [Stacks.Divisors.zeroScheme_pullback, IdealSheafData.stalk_comap]
    erw [stalk_zeroScheme_oneSection hsm D heff hcart]
    rw [Ideal.comap_map_of_surjective _ (C.idealSheaf.subschemeι.stalkMap_surjective _),
      ← RingHom.ker_eq_comap_bot, Stacks.Chow.ker_stalkMap_subschemeι_eq_stalk C.idealSheaf,
      localIdeal_single_one]
  rw [localIntersectionNumber]
  erw [h1, hcomp, hker]
  rfl

end Global

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **Local intersection numbers compute `(D · C)`.** On a smooth surface `Y` over `k`, let `C` be
a proper curve and `D` an effective divisor not containing `C`. Then `C ∩ Supp D` is finite, and
`(D · C)` is defined and equals `∑_{q ∈ C ∩ Supp D} i_q(D, C)`. -/
@[mmp "lem_mmp_foundation_km_surface_local_intersection_sum"]
public theorem isIntersectionNumber_finsum_localIntersectionNumber (hY : IsVariety k sY)
    (hsm : IsSmoothScheme sY) (hdim : topologicalKrullDim Y = 2) (C : PrimeDivisor Y)
    (hC : IsProper (C.idealSheaf.subschemeι ≫ sY)) {D : Divisor Y}
    (hD : D.IsEffective) (hCD : C ∉ D.support) :
    (C.support ∩ (D.supp : Set Y)).Finite ∧
      IsIntersectionNumber sY (Divisor.toQDivisor D) C.idealSheaf
        (∑ᶠ q ∈ C.support ∩ (D.supp : Set Y),
          (localIntersectionNumber sY q D (Finsupp.single C 1) : ℚ)) := by
  classical
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := C.integral
  set ι := C.idealSheaf.subschemeι
  have heff : 0 ≤ D := DivisorWithCoeffs.isEffective_iff_nonneg.1 hD
  have hcart : D.IsCartier := isCartier_of_isSmoothScheme hsm D
  have hdim1 : topologicalKrullDim C.idealSheaf.subscheme ≤ 1 :=
    Stacks.ResolutionOfSurfaces.topologicalKrullDim_subscheme_le_one hdim C.idealSheaf
      (Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm C)
  have hrangeι : Set.range ι = C.support := Scheme.IdealSheafData.range_subschemeι _
  have hne : ∃ c : C.idealSheaf.subscheme, ι c ∉ D.supp := by
    have hgen : C.genericPoint ∈ Set.range ι := by
      rw [hrangeι, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    obtain ⟨c, hc⟩ := hgen
    refine ⟨c, ?_⟩
    rw [hc, DivisorWithCoeffs.mem_supp_iff]
    rintro ⟨E, hE0, hEc⟩
    obtain rfl := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E C hEc
    exact hE0 (by rw [DivisorWithCoeffs.coeff_apply]; exact Finsupp.notMem_support_iff.1 hCD)
  haveI := hcart.isInvertibleModule_divisorialSheaf
  have hinvC : AlgebraicGeometry.SheafOfModules.IsInvertible C.idealSheaf.subscheme.sheaf.obj
      C.idealSheaf.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback ι).obj D.divisorialSheaf) :=
    MMP.Mori.isInvertible_pullback_obj ι _
  set σ := MMP.Threefold.Mori.oneSection heff
  set t := (Stacks.NonvanishingSpelling.sectionsEquiv _
    ((Scheme.Modules.pullback ι).obj D.divisorialSheaf)).symm
      (Stacks.NonvanishingPullback.pullbackGlobalSection ι D.divisorialSheaf σ)
  have hloc := MMP.Threefold.Mori.nonvanishingLocus_oneSection heff hcart
  obtain ⟨c, hc⟩ := hne
  have ht0 : t.eval (op ⊤) ≠ 0 :=
    MMP.Threefold.Mori.eval_pullbackSection_ne_zero ι _ σ ⟨c, by rw [hloc]; exact hc⟩
  have ht : t.eval (op ⊤) = pullbackGlobalSections ι D.divisorialSheaf σ := by
    open Stacks.AlgebraicGeometry.GeneratingSectionsRestrict in
    rw [pullbackGlobalSections_eq_pullbackGlobalSection]
    exact (Stacks.NonvanishingSpelling.sectionsEquiv _ _).apply_symm_apply _
  set Z := zeroScheme C.idealSheaf.subscheme _ (t.eval (op ⊤))
  have hrange : Set.range Z.subschemeι = ι ⁻¹' D.supp := by
    have h := nonvanishingLocus_eq_compl_supportSet_zeroScheme _ _ ht0
    rw [MMP.Threefold.Mori.nonvanishingLocus_pullbackSection, hloc] at h
    ext p
    have h2 := congrArg (p ∈ ·) h
    simp only [Set.mem_preimage, Set.mem_compl_iff, eq_iff_iff,
      Scheme.IdealSheafData.mem_supportSet_iff_mem_support] at h2
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp only [Set.mem_preimage, SetLike.mem_coe]
    tauto
  have hfinι : (ι ⁻¹' (D.supp : Set Y)).Finite :=
    finite_of_isClosed (ι ≫ sY) hdim1 (D.supp.isClosed.preimage ι.continuous) ⟨c, hc⟩
  have hZfin : IsFinite (Z.subschemeι ≫ ι ≫ sY) :=
    have : Stacks.Divisors.IsEffectiveCartierDivisor Z :=
      (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection _ _ t).mpr
        (isRegularSection_of_eval_top_ne_zero _ t ht0)
    isFinite_divisorSubscheme k (ι ≫ sY) hdim1 _
  have hinjZ : Function.Injective Z.subschemeι := Z.subschemeι.isClosedEmbedding.injective
  have hinj : Function.Injective (Z.subschemeι ≫ ι) :=
    ι.isClosedEmbedding.injective.comp hinjZ
  have hrange2 : Set.range (Z.subschemeι ≫ ι) = C.support ∩ (D.supp : Set Y) := by
    rw [← hrangeι, ← Set.image_preimage_eq_range_inter, ← hrange, ← Set.range_comp]
    rfl
  have : Fintype Z.subscheme :=
    @Fintype.ofFinite _ ((Set.finite_range_iff hinjZ).1 (hrange ▸ hfinι))
  have hdeg : D.degreeOn k sY ι hdim1 hcart =
      ((∑ z : Z.subscheme,
        letI := stalkAlgebra (Z.subschemeι ≫ ι ≫ sY) z
        Module.finrank k (Z.subscheme.presheaf.stalk z) : ℕ) : ℤ) := by
    have hreg := isRegularSection_of_eval_top_ne_zero _ t ht0
    change invertibleCurveDegree k (ι ≫ sY) hdim1 _ = _
    rw [invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_unit_zeroScheme k _ hdim1 _ t
        hreg,
      finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections,
      finrank_globalSections_eq_finsum_finrank_stalk, finsum_eq_sum_of_fintype]
  refine ⟨hrange2 ▸ Set.finite_range _, hC, hdim1, QDivisor.isQCartier_toQDivisor hcart, ?_⟩
  rw [QDivisor.intersectionNumber_toQDivisor k sY ι hdim1 D hcart, hdeg, ← hrange2,
    finsum_mem_range hinj, finsum_eq_sum_of_fintype]
  push_cast
  exact Finset.sum_congr rfl fun z _ => by
    exact_mod_cast finrank_stalk_zeroScheme_eq_localIntersectionNumber hsm C heff hcart ht rfl z

end LocalIntersection

/-! ### The arithmetic genus of a proper curve -/

section ArithmeticGenus

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))

/-- If the constants `k → Γ(C, 𝒪_C)` are bijective then `dim_k H⁰(C, 𝒪_C) = 1`. -/
private lemma finrank_cohomologyOverField_zero_unit_eq_one [IsProper f]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent] (hbij : Function.Bijective f.appTop) :
    Module.finrank k (cohomologyOverField k f (SheafOfModules.unit C.ringCatSheaf) 0) = 1 := by
  rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
  letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  exact Module.finrank_of_bijective_algebraMap <|
    hbij.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)

/-- On a proper scheme of dimension at most one over `k`, `Hⁱ(C, 𝒪_C) = 0` for `i ≥ 2`. -/
private lemma isZero_cohomologyOverField_unit_of_two_le [IsProper f]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent] (hC : topologicalKrullDim C ≤ 1)
    (i : ℕ) (hi : 2 ≤ i) :
    Limits.IsZero (cohomologyOverField k f (SheafOfModules.unit C.ringCatSheaf) i) :=
  (MMP.finiteDimensional_and_isZero_cohomologyOverField_of_isProper k f _).2 i <|
    ((topologicalKrullDim_subspace_le _ _).trans hC).trans_lt <| by
      exact_mod_cast (show (1 : ℕ∞) < i by exact_mod_cast hi)

/-- The arithmetic genus of a proper curve whose global functions are the constants is
`dim_k H¹(C, 𝒪_C)`. -/
private lemma arithmeticGenus_eq_finrank_one [IsProper f]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent] (hC : topologicalKrullDim C ≤ 1)
    (hbij : Function.Bijective f.appTop) :
    MMP.Mori.arithmeticGenus f =
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit C.ringCatSheaf) 1) := by
  rw [MMP.Mori.arithmeticGenus,
    eulerCharacteristic_eq_sub_of_isZero k f _ (isZero_cohomologyOverField_unit_of_two_le f hC),
    finrank_cohomologyOverField_zero_unit_eq_one f hbij]
  ring

end ArithmeticGenus

/-- **Arithmetic genus of an integral proper curve.** Let `C` be an integral scheme proper over
an algebraically closed field `k` via `f`, with `dim C ≤ 1`. Then `f.appTop : k → Γ(C, 𝒪_C)` is
bijective, and the arithmetic genus `p_a(C) = 1 - χ(𝒪_C)` equals `dim_k H¹(C, 𝒪_C)`; in
particular `0 ≤ p_a(C)`. -/
@[mmp "lem_mmp_threefold_curve_genus_nonnegative"]
public theorem arithmeticGenus_eq_finrank_cohomologyOverField_one
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsIntegral C] [IsProper f] (hC : topologicalKrullDim C ≤ 1) :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
    Function.Bijective f.appTop ∧
      arithmeticGenus f =
        (Module.finrank k
          (cohomologyOverField k f (SheafOfModules.unit C.ringCatSheaf) 1) : ℤ) ∧
      0 ≤ arithmeticGenus f := by
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have hbij := (MMP.globalSections_isField_and_finite_of_isProper f).2.1 ‹_›
  have hg := arithmeticGenus_eq_finrank_one f hC hbij
  exact ⟨hbij, hg, hg ▸ Int.natCast_nonneg _⟩

section ProjectiveLine

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

/-- The morphism `Spec κ(x) ⟶ X` followed by `X ⟶ Spec Γ(X, ⊤)` is the spectrum of evaluation
at `x`. -/
private theorem fromSpecResidueField_toSpecΓ (x : X) :
    X.fromSpecResidueField x ≫ X.toSpecΓ = Spec.map (X.Γevaluation x) := by
  rw [Scheme.fromSpecResidueField, Category.assoc, Scheme.fromSpecStalk_toSpecΓ,
    ← Spec.map_comp]
  rfl

/-- At a closed point of a scheme locally of finite type over an algebraically closed field `k`,
the residue field has degree one over `k`. -/
private theorem finrank_residueField_of_isClosed (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Module.finrank k (X.residueField x) = 1 := by
  letI : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have hinv : (residueFieldIsoBase p x hx).inv =
      (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x := by
    apply Spec.map_injective
    rw [SpecMap_residueFieldIsoBase_inv, Spec.map_comp, Spec.map_comp,
      ← fromSpecResidueField_toSpecΓ, Category.assoc, Category.assoc,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  refine Module.finrank_of_bijective_algebraMap ?_
  rw [RingHom.algebraMap_toAlgebra, ← hinv]
  exact ConcreteCategory.bijective_of_isIso (residueFieldIsoBase p x hx).inv

/-- A proper curve of genus zero over an algebraically closed field, with `Γ(C, 𝒪_C) = k`, is
regular: a singular point would make the normalization a projective line over a finite extension
of `k` of degree `> 1` [Stacks, Tag 0DJB], and `k` has no such extension. -/
private theorem isRegularLocalRing_stalk_of_genus_eq_zero {C : Scheme.{u}}
    (sC : C ⟶ Spec (.of k)) [IsCurve k sC] [IsProper sC]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop)] (hg : genus sC = 0) (x : C) :
    IsRegularLocalRing (C.presheaf.stalk x) := by
  by_contra hx
  obtain ⟨k', _, _, -, -, -, -, -, ⟨_, hlt⟩, -⟩ :=
    exists_projectiveLine_normalization_of_genus_eq_zero k sC ⟨x, hx⟩ hg
  have := Module.finrank_of_bijective_algebraMap
    ⟨(algebraMap k k').injective, IsSepClosed.algebraMap_surjective k k'⟩
  omega

end ProjectiveLine

/-- An integral proper curve `C` over an algebraically closed field `k` has nonnegative arithmetic
genus, and its arithmetic genus is zero if and only if `C ≅ ℙ¹_k` over `k`. -/
@[mmp "lem_mmp_threefold_curve_genus_zero"]
public theorem arithmeticGenus_nonneg_and_eq_zero_iff {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) [IsProper sC] [IsIntegral C]
    (hdim : topologicalKrullDim C = 1) :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k sC
    0 ≤ arithmeticGenus sC ∧
      (arithmeticGenus sC = 0 ↔
        ∃ e : projectiveLine k ≅ C, e.hom ≫ sC = projectiveLine k ↘ Spec (.of k)) := by
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k sC
  obtain ⟨hbij, hpa, hnn⟩ :=
    MMP.Mori.arithmeticGenus_eq_finrank_cohomologyOverField_one sC hdim.le
  refine ⟨hnn, ⟨fun h0 => ?_, fun ⟨e, he⟩ => ?_⟩⟩
  · have hg : genus sC = 0 := by
      rw [← finrank_cohomologyOverField_one_unit_eq_genus]
      exact_mod_cast hpa.symm.trans h0
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact hbij.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)
    have : IsCurve k sC := (isCurve_iff k sC).mpr ⟨{ }, hdim⟩
    have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace sC
    obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := C))
      isClosed_univ.isLocallyClosed
    obtain ⟨L, hL, hdeg⟩ := exists_invertibleCurveDegree_eq_one_of_gcd sC hdim.le (n := 1)
      (fun _ ↦ x) (fun _ ↦ hx)
      (fun _ ↦ have := isRegularLocalRing_stalk_of_genus_eq_zero sC hg x
        isIntegrallyClosed_of_isRegularLocalRing _)
      (by simpa using finrank_residueField_of_isClosed sC x hx)
    obtain ⟨e, he⟩ := exists_iso_projectiveLine_of_invertibleCurveDegree_eq_one sC hdim hg L hdeg
    refine ⟨projectiveLineIsoProj k ≪≫ e.symm, ?_⟩
    rw [← projectiveLineIsoProj_hom_comp_projToSpecCoeff, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, ← he, Iso.inv_hom_id_assoc]
  · have hsC : sC = (e.inv ≫ (projectiveLineIsoProj k).hom) ≫
        Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1 := by
      rw [Category.assoc, projectiveLineIsoProj_hom_comp_projToSpecCoeff, ← he,
        Iso.inv_hom_id_assoc]
    rw [hpa, hsC, finrank_cohomologyOverField_unit_pushforward,
      finrank_cohomologyOverField_one_unit_eq_genus, Stacks.Curves.genus_projToSpecCoeff_one,
      Nat.cast_zero]

end MMP.Mori
