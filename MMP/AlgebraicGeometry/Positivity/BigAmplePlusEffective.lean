module
public import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
public import MMP.AlgebraicGeometry.Divisor.InvertibleSheafOfEffective
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
public import MMP.AlgebraicGeometry.Cohomology.ProperCoherentSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.PlaneConic
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.Positivity.CartierTwistEulerPolynomial
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Big Cartier divisors: ample plus effective, and birational invariance

Let `X` be a projective variety of dimension `n` over a field `k` and `D` a Cartier divisor on
`X` such that, for some `c > 0`, `h⁰(X, 𝒪_X(mD)) > c mⁿ` for infinitely many `m` (for instance
`D` big, `MMP.Mori.IsBigCartier`). Then some positive multiple `mD` is linearly equivalent to
`A + E` with `A` an ample effective Cartier divisor and `E` an effective Cartier divisor.

Bigness is a birational invariant: for a birational morphism `g : Y ⟶ X` of proper varieties
over `k`, a Cartier divisor `D` on `X` is big if and only if its pull-back `g^*D` is. Pulling
back sections gives `h⁰(X, mD) ≤ h⁰(Y, m g^*D)`; conversely the cokernel of `𝒪_X → g_*𝒪_Y` is
supported in dimension `< n`, so the projection formula gives
`h⁰(Y, m g^*D) ≤ h⁰(X, mD) + C m^{n-1}`.

## Main results

* `MMP.Mori.exists_linearlyEquivalent_ample_add_effective`: `mD ∼ A + E`.
* `MMP.Mori.isBigCartier_iff_of_isPullback`: `D` is big iff `g^*D` is big.

## Implementation notes

`h⁰` is `MMP.Mori.cartierH0`, the `k`-dimension of the global sections of `𝒪_X(D)` through the
structure morphism `f : X ⟶ Spec k`. Ampleness of `A` is ampleness of the invertible sheaf
`𝒪_X(A)` (`AlgebraicGeometry.Stacks.Ample.IsAmple`), intrinsic to `X`; effectivity and linear
equivalence are `MMP.Intersection.IsEffective` and `MMP.Intersection.LinearlyEquivalent`.
The set of `m` with `h⁰(X, 𝒪_X(mD)) > c mⁿ` is a set of natural numbers; being infinite, it
contains infinitely many positive ones, which is the source's hypothesis.

The pull-back `g^*D` is any Cartier divisor `D'` on `Y` with
`MMP.Intersection.IsPullback g D D'`, the relation characterising the pull-back by local
equations; since `Y` is integral and `g` dominant, such a `D'` exists and is unique. Sections
are pulled back through the identification of `𝓜_X(U)` with the function field of `X` for `U`
nonempty.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.60
-/

public section

open CategoryTheory AlgebraicGeometry MMP.Intersection

open scoped Stacks.SmallDerivedModel

universe u

namespace MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A projective variety carries an ample effective Cartier divisor: the zero scheme of a
non-zero section of a positive power `L^n` of an ample sheaf `L`, with `𝒪_X(A) ≅ L^n`. -/
private theorem exists_isEffective_isAmple (f : X ⟶ Spec (.of k)) (hX : IsProjectiveVariety k f) :
    ∃ A : X.CartierDivisor, IsEffective A ∧
      Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A) := by
  have : IsIntegral X := hX.toIsIntegral
  obtain ⟨-, L, hLinv, hLamp⟩ := Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective f
    hX.isProjective.isHQuasiProjective
  have hL : Stacks.Ample.IsAmple X L :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine f L hLamp
  obtain ⟨I, hI, -, -, n, hn, ⟨eI⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint X))
  obtain ⟨A, hA, hAI⟩ :=
    (MMP.CartierDivisor.isEffectiveCartierDivisor_iff_exists_subscheme_eq _).1 hI
  have e : MMP.CartierDivisor.sheaf A ≅ Stacks.Ample.tensorPowModule X L (n : ℤ) :=
    MMP.CartierDivisor.sheafIsoInvertibleSheaf A hA ≪≫
      eqToIso (by rw [hAI]) ≪≫ eI.symm
  refine ⟨A, hA, ?_⟩
  · have := MMP.CartierDivisor.isInvertibleModule_sheaf A
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn hL)

/-! ### Twisted sheaves and growth of `h⁰`

The sheaf `𝒪_X(D)` of a Cartier divisor, tensor powers and twists of it, and bounds for the
dimension of the global sections of a twist along short exact sequences. -/

namespace TwistGrowth

section Twists

open Stacks.SheafOfModules.Invertible MMP.CartierDivisorSheaf

/-- The sheaf `𝒪_X(D)` of a Cartier divisor `D`. -/
noncomputable abbrev sh (D : X.CartierDivisor) : X.Modules :=
  MMP.CartierDivisor.sheaf D

/-- The tensor product bifunctor on `𝒪_X`-modules. -/
noncomputable abbrev tens (X : Scheme.{u}) : X.Modules ⥤ X.Modules ⥤ X.Modules :=
  Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
    (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩

/-- Tensoring by an invertible sheaf is cancellable up to isomorphism. -/
theorem nonempty_iso_of_tensor_iso (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {M N : X.Modules}
    (h : ((tens X).obj M).obj L ≅ ((tens X).obj N).obj L) : Nonempty (M ≅ N) := by
  have : ((tens X).flip.obj L).IsEquivalence :=
    (isInvertible_iff_tensorRightFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 L).1
      inferInstance
  exact ⟨((tens X).flip.obj L).preimageIso h⟩

/-- `𝒪_X(0) ≅ 𝒪_X`. -/
theorem nonempty_sheaf_zero_iso :
    Nonempty (sh (0 : X.CartierDivisor) ≅ SheafOfModules.unit X.ringCatSheaf) := by
  set s0 := sh (0 : X.CartierDivisor)
  have h1 : ((tens X).obj (SheafOfModules.unit X.ringCatSheaf)).obj s0 ≅ s0 :=
    (tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 s0 0).symm ≪≫
      tensorPowerReindex X.presheaf X.ringCatSheaf.2 s0 (by norm_num : (0:ℤ) + 1 = 1) ≪≫
      tensorPowerOneIso X.presheaf X.ringCatSheaf.2 s0
  have h2 : ((tens X).obj s0).obj s0 ≅ s0 :=
    sheafMulIso (0 : X.CartierDivisor) 0 ≪≫ eqToIso (by rw [add_zero])
  exact nonempty_iso_of_tensor_iso s0 (h2.trans h1.symm)

/-- `𝒪_X(nD) ≅ 𝒪_X(D)^{⊗ n}`. -/
theorem nonempty_sheaf_zsmul_iso (D : X.CartierDivisor) (n : ℤ) :
    Nonempty (sh (n • D) ≅ tensorPower X.presheaf X.ringCatSheaf.2 (sh D) n) := by
  set L := sh D
  induction n using Int.induction_on with
  | zero =>
    obtain ⟨e⟩ := nonempty_sheaf_zero_iso (X := X)
    exact ⟨eqToIso (by rw [zero_smul]) ≪≫ e⟩
  | succ i ih =>
    obtain ⟨e⟩ := ih
    have h : sh (((i : ℤ) + 1) • D) ≅ ((tens X).obj (sh ((i : ℤ) • D))).obj L :=
      eqToIso (by rw [add_smul, one_smul]) ≪≫ (sheafMulIso ((i : ℤ) • D) D).symm
    exact ⟨h ≪≫ ((tens X).mapIso e).app L ≪≫ tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L i⟩
  | pred i ih =>
    obtain ⟨e⟩ := ih
    have h : ((tens X).obj (sh ((-(i : ℤ) - 1) • D))).obj L ≅ sh ((-(i : ℤ)) • D) :=
      sheafMulIso _ D ≪≫ eqToIso (by rw [sub_smul, one_smul, sub_add_cancel])
    have h2 : ((tens X).obj (tensorPower X.presheaf X.ringCatSheaf.2 L (-(i : ℤ) - 1))).obj L ≅
        sh ((-(i : ℤ)) • D) :=
      tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L _ ≪≫
        tensorPowerReindex X.presheaf X.ringCatSheaf.2 L (n := -(i : ℤ) - 1 + 1) (m := -(i : ℤ))
          (by ring) ≪≫ e.symm
    exact nonempty_iso_of_tensor_iso L (h.trans h2.symm)

/-- `𝒪_X(E) ⊗ 𝒪_X(D)^{⊗ m} ≅ 𝒪_X(E + mD)`, as a twisted sheaf. -/
theorem nonempty_twistedSheaf_iso {M : X.Modules} {E : X.CartierDivisor}
    (eM : sh E ≅ M) (D : X.CartierDivisor) (m : ℤ) :
    Nonempty (twistedSheaf M (fun _ : Fin 1 => sh D) (fun _ => m) ≅ sh (E + m • D)) := by
  obtain ⟨e'⟩ := nonempty_sheaf_zsmul_iso D m
  have h : sh (E + m • D) ≅ ((tens X).obj M).obj
      (tensorPower X.presheaf X.ringCatSheaf.2 (sh D) m) :=
    (sheafMulIso E (m • D)).symm ≪≫ tensorIso eM e'
  exact ⟨h.symm⟩

end Twists

section Growth

variable (k) (f : X ⟶ Spec (.of k))

/-- `h⁰` of a Cartier divisor is the dimension of degree-zero cohomology of its sheaf. -/
theorem cartierH0_eq_finrank (D : X.CartierDivisor) :
    cartierH0 k f D =
      Module.finrank k (cohomologyOverField k f (MMP.CartierDivisor.sheaf D) 0) :=
  ((cohomologyOverFieldZeroIsoSections k f
    (MMP.CartierDivisor.sheaf D)).toLinearEquiv.finrank_eq).symm

/-- `h⁰` is subadditive along a short exact sequence of finite-dimensional cohomologies. -/
theorem finrank_cohomologyOverField_zero_le_add {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
    [FiniteDimensional k (cohomologyOverField k f S.X₂ 0)]
    [FiniteDimensional k (cohomologyOverField k f S.X₃ 0)] :
    Module.finrank k (cohomologyOverField k f S.X₂ 0) ≤
      Module.finrank k (cohomologyOverField k f S.X₁ 0) +
        Module.finrank k (cohomologyOverField k f S.X₃ 0) := by
  obtain ⟨-, -, hex, -, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  set ψ := (cohomologyOverFieldMap k f S.g 0).hom
  have hker : Module.finrank k (LinearMap.ker ψ) ≤
      Module.finrank k (cohomologyOverField k f S.X₁ 0) :=
    (LinearMap.exact_iff.1 (hex 0)) ▸ LinearMap.finrank_range_le _
  have := LinearMap.finrank_range_add_finrank_ker ψ
  have := Submodule.finrank_le (LinearMap.range ψ)
  omega

/-- `h⁰` is monotone along the first map of a short exact sequence. -/
theorem finrank_cohomologyOverField_zero_le_of_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    [FiniteDimensional k (cohomologyOverField k f S.X₂ 0)] :
    Module.finrank k (cohomologyOverField k f S.X₁ 0) ≤
      Module.finrank k (cohomologyOverField k f S.X₂ 0) := by
  obtain ⟨-, hinj, -, -, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  exact LinearMap.finrank_le_finrank_of_injective hinj

variable [IsProper f] {r : ℕ} (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]

/-- For `f` proper and `G` coherent, `H⁰` of a twist of `G` by invertible sheaves is
finite-dimensional over `k`. -/
theorem finiteDimensional_twistedSheafFunctor_obj (G : X.Modules)
    (hG : _root_.SheafOfModules.IsCoherent G) (n : Fin r → ℤ) :
    FiniteDimensional k (cohomologyOverField k f ((twistedSheafFunctor L n).obj G) 0) :=
  have := forall_finiteDimensional_cohomologyOverField_of_isProper k f _
    (@twistedSheaf_isCoherent X r G L _ hG n) 0
  (cohomologyOverFieldIso k f (twistedSheafFunctorObjIso L n G) 0).toLinearEquiv.symm
    |>.finiteDimensional

omit [IsProper f] in
/-- `h⁰` of `G` twisted through `twistedSheafFunctor` equals `h⁰` of `twistedSheaf G L n`. -/
theorem finrank_twistedSheafFunctor_obj (G : X.Modules) (n : Fin r → ℤ) :
    Module.finrank k (cohomologyOverField k f ((twistedSheafFunctor L n).obj G) 0) =
      Module.finrank k (cohomologyOverField k f (twistedSheaf G L n) 0) :=
  finrank_cohomologyOverField_eq_of_iso k f (twistedSheafFunctorObjIso L n G) 0

/-- `h⁰` of the twists is subadditive along a short exact sequence of coherent sheaves. -/
theorem finrank_twistedSheaf_le_add {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h1 : _root_.SheafOfModules.IsCoherent S.X₁) (h2 : _root_.SheafOfModules.IsCoherent S.X₂)
    (h3 : _root_.SheafOfModules.IsCoherent S.X₃) (n : Fin r → ℤ) :
    Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₂ L n) 0) ≤
      Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₁ L n) 0) +
        Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₃ L n) 0) := by
  simpa only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
    finrank_twistedSheafFunctor_obj] using
    @finrank_cohomologyOverField_zero_le_add k _ X f _
      (shortExact_map_twistedSheafFunctor L hS n)
      (finiteDimensional_twistedSheafFunctor_obj k f L _ h1 n)
      (finiteDimensional_twistedSheafFunctor_obj k f L _ h2 n)
      (finiteDimensional_twistedSheafFunctor_obj k f L _ h3 n)

/-- `h⁰` of the twists is monotone along the first map of a short exact sequence. -/
theorem finrank_twistedSheaf_le_of_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (h2 : _root_.SheafOfModules.IsCoherent S.X₂) (n : Fin r → ℤ) :
    Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₁ L n) 0) ≤
      Module.finrank k (cohomologyOverField k f (twistedSheaf S.X₂ L n) 0) := by
  simpa only [ShortComplex.map_X₁, ShortComplex.map_X₂, finrank_twistedSheafFunctor_obj] using
    @finrank_cohomologyOverField_zero_le_of_shortExact k _ X f _
      (shortExact_map_twistedSheafFunctor L hS n)
      (finiteDimensional_twistedSheafFunctor_obj k f L _ h2 n)

end Growth

end TwistGrowth

open TwistGrowth

/-- **`h⁰` changes by `O(m^{n-1})` under a fixed twist.** On a projective variety `X` of
dimension `n ≥ 1`, for Cartier divisors `A` and `D` there is `C > 0` with
`h⁰(X, 𝒪_X(mD)) ≤ h⁰(X, 𝒪_X(mD - A)) + C m^{n-1}` for all `m > 0`. A regular meromorphic
section of `𝒪_X(-A)` gives difference sequences `0 → 𝒜 → 𝒪_X → 𝒬 → 0` and
`0 → 𝒜 → 𝒪_X(-A) → 𝒬' → 0` with `dim Supp 𝒬 ≤ n - 1`; twisting by `𝒪_X(D)^{⊗ m}` and the
growth bound for `𝒬` give the inequality. -/
private theorem cartierH0_le_cartierH0_sub_add_pow (f : X ⟶ Spec (.of k))
    (hX : IsProjectiveVariety k f) {n : ℕ} (hn : topologicalKrullDim X = n)
    (hn1 : 1 ≤ n) (A D : X.CartierDivisor) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → (cartierH0 k f (m • D) : ℝ) ≤
      cartierH0 k f (m • D - A) + C * (m : ℝ) ^ (n - 1) := by
  have : IsIntegral X := hX.toIsIntegral
  have : LocallyOfFiniteType f := hX.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsProper f := isProper_of_isProjectiveMorphism f hX.isProjective
  set O := SheafOfModules.unit X.ringCatSheaf
  have hO := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have hsuppO : _root_.SheafOfModules.supp O = Set.univ := supp_unit_eq_univ X
  have hdimO : natDimSupp O = n := by
    have := coe_natDimSupp_eq k f O (by rw [hsuppO]; exact Set.univ_nonempty.ne_empty)
    rw [topologicalKrullDim_supp_unit, hn] at this
    exact_mod_cast this
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_hasNoEmbeddedPoints X
    (PlaneConic.hasNoEmbeddedPoints_of_isIntegral X) (sh (-A))
  obtain ⟨S, T, hS, hT, cS1, cS2, cS3, cT1, cT2, cT3, ⟨eS⟩, ⟨eT⟩, ⟨e01⟩, -, -, hS3, -⟩ :=
    exists_differenceSequences_of_supp_eq_univ k f (sh (-A)) O hO (by omega)
      (PlaneConic.hasNoEmbeddedPoints_of_isIntegral X) hsuppO s hs
  have hd3 : topologicalKrullDim (_root_.SheafOfModules.supp S.X₃) ≤
      ((n - 1 : ℕ) : WithBot ℕ∞) := by
    by_cases h : _root_.SheafOfModules.supp S.X₃ = ∅
    · rw [(topologicalKrullDim_supp_eq_bot_iff _).2 h]; exact bot_le
    · rw [← coe_natDimSupp_eq k f _ h]
      exact_mod_cast (by omega : natDimSupp S.X₃ ≤ n - 1)
  obtain ⟨C, hC, hb⟩ :=
    MMP.Foundations.exists_finrank_cohomologyOverField_zero_twistedSheaf_le_pow k f (sh D) S.X₃
      cS3 (n - 1) hd3
  refine ⟨C, hC, fun m hm => ?_⟩
  obtain ⟨z⟩ := nonempty_sheaf_zero_iso (X := X)
  obtain ⟨i2⟩ := nonempty_twistedSheaf_iso (z ≪≫ eS.symm) D (m : ℤ)
  have eA : sh (0 + -A) ≅ T.X₂ :=
    (MMP.CartierDivisorSheaf.sheafMulIso 0 (-A)).symm ≪≫
      ((tens X).mapIso z).app (sh (-A)) ≪≫ eT.symm
  obtain ⟨i3⟩ := nonempty_twistedSheaf_iso eA D (m : ℤ)
  have h2 : cartierH0 k f (m • D) = Module.finrank k (cohomologyOverField k f
      (twistedSheaf S.X₂ (fun _ : Fin 1 => sh D) (fun _ => (m : ℤ))) 0) := by
    rw [cartierH0_eq_finrank, finrank_cohomologyOverField_eq_of_iso k f i2 0, zero_add,
      natCast_zsmul]
  have h3 : cartierH0 k f (m • D - A) = Module.finrank k (cohomologyOverField k f
      (twistedSheaf T.X₂ (fun _ : Fin 1 => sh D) (fun _ => (m : ℤ))) 0) := by
    rw [cartierH0_eq_finrank, finrank_cohomologyOverField_eq_of_iso k f i3 0, natCast_zsmul,
      zero_add, neg_add_eq_sub]
  have hle1 := finrank_twistedSheaf_le_add k f (fun _ : Fin 1 => sh D) hS cS1 cS2 cS3
    (fun _ => (m : ℤ))
  have hle2 := finrank_twistedSheaf_le_of_shortExact k f (fun _ : Fin 1 => sh D) hT cT2
    (fun _ => (m : ℤ))
  rw [finrank_cohomologyOverField_eq_of_iso k f (twistedSheafIsoOfIso _ e01 _) 0] at hle1
  have hb' := hb m (by exact_mod_cast hm)
  push_cast at hb'
  rw [h2, h3]
  calc _ ≤ ((Module.finrank k (cohomologyOverField k f
          (twistedSheaf T.X₁ (fun _ : Fin 1 => sh D) (fun _ => (m : ℤ))) 0) +
        Module.finrank k (cohomologyOverField k f
          (twistedSheaf S.X₃ (fun _ : Fin 1 => sh D) (fun _ => (m : ℤ))) 0) : ℕ) : ℝ) := by
        exact_mod_cast hle1
    _ ≤ _ := by push_cast; gcongr

/-- The stalks of `𝓜_X` are nontrivial: they contain the stalks of `𝒪_X`. -/
private theorem nontrivial_stalk_totalQuotient (x : X) :
    Nontrivial (X.totalQuotientSheaf.presheaf.stalk x) :=
  (stalkToTotalQuotient_injective x).nontrivial

/-- On an integral scheme a section of `𝓜_X` whose germ at `x` is a unit is a unit on a
neighbourhood of `x`. -/
private theorem exists_isUnit_res_of_isUnit_germ {U : X.Opens}
    (σ : X.totalQuotientSheaf.obj.obj (Opposite.op U)) {x : X} (hx : x ∈ U)
    (h : IsUnit (X.totalQuotientSheaf.presheaf.germ U x hx σ)) :
    ∃ (W : X.Opens) (i : W ⟶ U), x ∈ W ∧
      IsUnit (X.totalQuotientSheaf.obj.map i.op σ) := by
  obtain ⟨t, ht⟩ := h.exists_right_inv
  obtain ⟨V, hxV, τ, rfl⟩ := X.totalQuotientSheaf.presheaf.exists_germ_eq t
  have h1 : X.totalQuotientSheaf.presheaf.germ (U ⊓ V) x ⟨hx, hxV⟩
      (X.totalQuotientSheaf.obj.map (homOfLE inf_le_left).op σ *
        X.totalQuotientSheaf.obj.map (homOfLE inf_le_right).op τ) =
      X.totalQuotientSheaf.presheaf.germ (U ⊓ V) x ⟨hx, hxV⟩ 1 := by
    rw [map_mul, map_one]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact ht
  obtain ⟨W, hxW, i, i', hW⟩ := X.totalQuotientSheaf.presheaf.germ_eq (U := U ⊓ V) (V := U ⊓ V)
    x ⟨hx, hxV⟩ ⟨hx, hxV⟩ _ _ h1
  obtain rfl : i' = i := Subsingleton.elim _ _
  refine ⟨W, i' ≫ homOfLE inf_le_left, hxW, IsUnit.of_mul_eq_one
    (X.totalQuotientSheaf.obj.map (i' ≫ homOfLE inf_le_right).op τ) ?_⟩
  rwa [map_mul, map_one, totalQuotient_map_map, totalQuotient_map_map] at hW

/-- On an integral scheme a non-zero global section of `𝓜_X` is a unit. -/
private theorem isUnit_of_ne_zero_totalQuotient [IsIntegral X]
    {σ : X.totalQuotientSheaf.obj.obj (Opposite.op ⊤)} (hσ : σ ≠ 0) : IsUnit σ := by
  obtain ⟨x, hx⟩ : ∃ x : X, X.totalQuotientSheaf.presheaf.germ ⊤ x trivial σ ≠ 0 := by
    by_contra! h
    exact hσ (TopCat.Presheaf.section_ext X.totalQuotientSheaf ⊤ σ 0 fun x _ => by
      rw [h x, map_zero])
  have hux := Stacks.ChernCap42.isUnit_of_ne_zero_stalk_totalQuotientSheaf X x hx
  set η := genericPoint X
  have := nontrivial_stalk_totalQuotient η
  have hη : X.totalQuotientSheaf.presheaf.germ ⊤ η trivial σ ≠ 0 := by
    have := TopCat.Presheaf.germ_stalkSpecializes_apply X.totalQuotientSheaf.presheaf
      (U := ⊤) (trivial : x ∈ (⊤ : X.Opens)) ((genericPoint_spec X).specializes (Set.mem_univ x)) σ
    rw [← this]
    exact (hux.map _).ne_zero
  refine isUnit_of_locally σ fun y _ => exists_isUnit_res_of_isUnit_germ σ trivial ?_
  refine Stacks.ChernCap42.isUnit_of_ne_zero_stalk_totalQuotientSheaf X y fun h0 => hη ?_
  have := TopCat.Presheaf.germ_stalkSpecializes_apply X.totalQuotientSheaf.presheaf
    (U := ⊤) (trivial : y ∈ (⊤ : X.Opens)) ((genericPoint_spec X).specializes (Set.mem_univ y)) σ
  rw [← this, h0, map_zero]

/-- If a unit `u` of `Γ(X, 𝓜_X)` is a global section of `𝒪_X(D)`, then `D + div u` is
effective: its local equations `g u` are regular functions. -/
private theorem isEffective_add_principalDivisor {D : X.CartierDivisor}
    (u : (X.totalQuotientSheaf.obj.obj (Opposite.op ⊤))ˣ)
    (hu : (u : X.totalQuotientSheaf.obj.obj (Opposite.op ⊤)) ∈ lineBundleSections D ⊤) :
    IsEffective (D + MMP.Intersection.principalDivisor u) := by
  intro x
  obtain ⟨U, hxU, g, hg⟩ := exists_isLocalEquationOn D x
  have hE := hg.mul (isLocalEquationOn_principalDivisor_res u U)
  obtain ⟨r, hr⟩ := exists_toTotalQuotient_eq_of_germ_mem
    (V := U) ((g * resUnit (homOfLE le_top) u : (X.totalQuotientSheaf.obj.obj (Opposite.op U))ˣ) :
      X.totalQuotientSheaf.obj.obj (Opposite.op U))
    fun y hy => by
      have h := hu y trivial (X.totalQuotientSheaf.presheaf.germ U y hy (g : _))
        ⟨U, hy, g, hg, rfl⟩
      rw [Units.val_mul, map_mul, mul_comm]
      convert h using 2
      erw [TopCat.Presheaf.germ_res_apply]
  have hunit : IsUnit (toTotalQuotient U r) := hr ▸ (g * resUnit (homOfLE le_top) u).isUnit
  refine ⟨U, hxU, r, hunit, ?_⟩
  rwa [show hunit.unit = g * resUnit (homOfLE le_top) u from Units.ext hr]

/-- A non-zero `h⁰` gives a unit of `Γ(X, 𝓜_X)` lying in `Γ(X, 𝒪_X(D))` on an integral scheme. -/
private theorem exists_unit_mem_lineBundleSections [IsIntegral X] (f : X ⟶ Spec (.of k))
    {D : X.CartierDivisor} (hD : cartierH0 k f D ≠ 0) :
    ∃ u : (X.totalQuotientSheaf.obj.obj (Opposite.op ⊤))ˣ,
      (u : X.totalQuotientSheaf.obj.obj (Opposite.op ⊤)) ∈ lineBundleSections D ⊤ := by
  let _ : Module k Γ(MMP.CartierDivisor.sheaf D, ⊤) :=
    Module.compHom _ (scalarsToGlobalSections k f)
  have hpos : 0 < Module.finrank k Γ(MMP.CartierDivisor.sheaf D, ⊤) :=
    Nat.pos_of_ne_zero hD
  have := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨τ, hτ⟩ := exists_ne (0 : Γ(MMP.CartierDivisor.sheaf D, ⊤))
  have hσ : MMP.CartierDivisorSheaf.sectionVal τ ≠ 0 := fun h =>
    hτ (MMP.CartierDivisorSheaf.sectionVal_injective (h.trans rfl))
  obtain ⟨u, hu⟩ := isUnit_of_ne_zero_totalQuotient hσ
  exact ⟨u, hu ▸ (MMP.CartierDivisor.sectionVal_mem_lineBundleSections τ)⟩

/-- A Cartier divisor on a projective variety with a non-zero global section of its sheaf is
linearly equivalent to an effective one, the divisor of that section. -/
private theorem exists_isEffective_linearlyEquivalent (f : X ⟶ Spec (.of k))
    (hX : IsProjectiveVariety k f) {D : X.CartierDivisor}
    (hD : cartierH0 k f D ≠ 0) :
    ∃ E : X.CartierDivisor, IsEffective E ∧ LinearlyEquivalent D E := by
  have : IsIntegral X := hX.toIsIntegral
  obtain ⟨u, hu⟩ := exists_unit_mem_lineBundleSections f hD
  refine ⟨D + MMP.Intersection.principalDivisor u, isEffective_add_principalDivisor u hu, ?_⟩
  rw [LinearlyEquivalent, sub_add_cancel_left, ← MMP.Intersection.principalDivisor_inv]
  exact principalDivisor_mem _

/-- An irreducible space of Krull dimension `0` is its generic point. -/
private theorem eq_genericPoint_of_topologicalKrullDim_eq_zero [IsIntegral X]
    (hn : topologicalKrullDim X = 0) (x : X) : x = genericPoint X := by
  have hmin := Order.krullDim_nonpos_iff_forall_isMin.1 (le_of_eq hn)
  let Z : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hTZ : T ≤ Z := hmin T fun _ _ => Set.mem_univ _
  have hx : IsGenericPoint x ⊤ := by
    change closure {x} = Set.univ
    exact Set.eq_univ_of_univ_subset hTZ
  exact hx.eq (genericPoint_spec X)

/-- On a projective variety of dimension `0` (the spectrum of a field) every Cartier divisor
is trivial. -/
private theorem eq_zero_of_topologicalKrullDim_eq_zero (f : X ⟶ Spec (.of k))
    (hX : IsProjectiveVariety k f) (hn : topologicalKrullDim X = 0)
    (D : X.CartierDivisor) : D = 0 := by
  have : IsIntegral X := hX.toIsIntegral
  have : LocallyOfFiniteType f := hX.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hall := eq_genericPoint_of_topologicalKrullDim_eq_zero hn
  have hsurj : ∀ y : X, Function.Surjective (stalkToTotalQuotient y) := by
    intro y m
    obtain rfl := hall y
    refine ⟨totalQuotientStalkToFunctionField (genericPoint X) m,
      (totalQuotientStalkToFunctionField_bijective (genericPoint X)).1 ?_⟩
    rw [totalQuotientStalkToFunctionField_stalkToTotalQuotient]
    change (X.presheaf.stalkSpecializes _).hom _ = _
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  obtain ⟨U, hηU, g, hg⟩ := exists_isLocalEquationOn D (genericPoint X)
  have hUtop : U = ⊤ := eq_top_iff.2 fun y _ => by rwa [hall y]
  obtain ⟨r, hr⟩ := exists_toTotalQuotient_eq_of_germ_mem (g : X.totalQuotientSheaf.obj.obj
    (Opposite.op U)) fun y hy => hsurj y _
  have hru : IsUnit r := by
    refine X.toRingedSpace.isUnit_of_isUnit_germ U r fun y hy => ?_
    obtain rfl := hall y
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have h1 : X.totalQuotientSheaf.presheaf.germ U (genericPoint X) hy (g : _) = 0 := by
      rw [← hr, germ_toTotalQuotient]
      erw [h0]
      exact map_zero _
    have := nontrivial_stalk_totalQuotient (genericPoint X)
    exact ((g.isUnit.map (X.totalQuotientSheaf.presheaf.germ U (genericPoint X) hy).hom).ne_zero) h1
  have hg0 : IsLocalEquationOn (0 : X.CartierDivisor) U g := by
    have : g = Units.map (toTotalQuotient U).toMonoidHom hru.unit := Units.ext (by simp [hr])
    rw [IsLocalEquationOn, this, cartierClass_map_units, restrictDivisor_zero]
  exact eq_of_isLocalEquationOn (fun _ : Unit => U) (by simp [hUtop]) (fun _ => g)
    (fun _ => hg) (fun _ => hg0)

/-- Arithmetic: an infinite set of naturals on which `c mⁿ < h(m)` contains a positive `m` with
`C m^{n-1} < h(m)`. -/
private theorem exists_lt_of_infinite {n : ℕ} (hn : 1 ≤ n) {c C : ℝ} (hc : 0 < c)
    {h : ℕ → ℝ} (hS : {m : ℕ | c * (m : ℝ) ^ n < h m}.Infinite) :
    ∃ m : ℕ, 0 < m ∧ C * (m : ℝ) ^ (n - 1) < h m := by
  obtain ⟨m, hm, hmC⟩ := hS.exists_gt ⌈C / c⌉₊
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 (lt_of_le_of_lt (Nat.zero_le _) hmC)
  refine ⟨m, by exact_mod_cast hm0, lt_trans ?_ hm⟩
  have hCm : C < c * m := by
    have h1 : C / c < m := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hmC)
    rwa [div_lt_iff₀ hc, mul_comm] at h1
  have : (m : ℝ) ^ n = (m : ℝ) ^ (n - 1) * m := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [this, ← mul_assoc, mul_comm c, mul_assoc, mul_comm C]
  exact mul_lt_mul_of_pos_left hCm (pow_pos hm0 _)

/-- **Big divisors are ample plus effective (KM 2.60 (1) ⇒ (2)).** On a projective variety `X`
of dimension `n` over `k`, if a Cartier divisor `D` satisfies `h⁰(X, 𝒪_X(mD)) > c mⁿ` for some
`c > 0` and infinitely many `m`, then there are `m > 0`, an ample effective Cartier divisor `A`
and an effective Cartier divisor `E` with `mD ∼ A + E`. -/
@[mmp "lem_km2c_ample_plus_effective_of_big"]
public theorem exists_linearlyEquivalent_ample_add_effective (f : X ⟶ Spec (.of k))
    (hX : IsProjectiveVariety k f) {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : X.CartierDivisor)
    (hD : ∃ c : ℝ, 0 < c ∧
      {m : ℕ | c * (m : ℝ) ^ n < (cartierH0 k f (m • D) : ℝ)}.Infinite) :
    ∃ m : ℕ, 0 < m ∧ ∃ A E : X.CartierDivisor,
      MMP.Intersection.IsEffective A ∧ Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A) ∧
      MMP.Intersection.IsEffective E ∧
      MMP.Intersection.LinearlyEquivalent (m • D) (A + E) := by
  obtain ⟨A, hA, hAmp⟩ := exists_isEffective_isAmple f hX
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · have h0 := eq_zero_of_topologicalKrullDim_eq_zero f hX (by exact_mod_cast hn)
    refine ⟨1, one_pos, A, 0, hA, hAmp, ?_, ?_⟩
    · exact h0 A ▸ hA
    · rw [h0 (1 • D), h0 (A + 0)]
  obtain ⟨c, hc, hS⟩ := hD
  obtain ⟨C, hC, hle⟩ := cartierH0_le_cartierH0_sub_add_pow f hX hn hn1 A D
  obtain ⟨m, hm, hmC⟩ := exists_lt_of_infinite hn1 hc hS
  have hne : cartierH0 k f (m • D - A) ≠ 0 := fun h0 =>
    (by simpa [h0] using hle m hm : _ ≤ _).not_gt hmC
  obtain ⟨E, hE, hlin⟩ := exists_isEffective_linearlyEquivalent f hX hne
  refine ⟨m, hm, A, E, hA, hAmp, hE, ?_⟩
  simpa [LinearlyEquivalent, sub_sub] using hlin

section BirationalInvariance

open MMP.CartierDivisorSheaf
open Opposite TopologicalSpace

section KModel

variable {X : Scheme.{u}} [IsIntegral X]

private noncomputable def ιK (U : X.Opens) :
    X.functionField →+* X.totalQuotientSheaf.obj.obj (op U) :=
  ((functionFieldToTotalQuotientSheaf X).app (op U)).hom

private theorem genericPoint_mem {U : X.Opens} (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U := by
  obtain ⟨x, hx⟩ := hU
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, Set.mem_univ _, hx⟩

private theorem ιK_germ (U : X.Opens) (h : genericPoint X ∈ U) (a : Γ(X, U)) :
    ιK U (X.presheaf.germ U (genericPoint X) h a) = toK U a :=
  functionFieldToTotalQuotientSheaf_germ X U a h

private theorem ιK_res {U V : X.Opens} (h : V ≤ U) (c : X.functionField) :
    resK h (ιK U c) = ιK V c :=
  (congrArg (fun φ => φ.hom c)
    ((functionFieldToTotalQuotientSheaf X).naturality (homOfLE h).op)).symm

private theorem ιK_injective (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Function.Injective (ιK U) :=
  functionFieldToTotalQuotientSheaf_app_injective X U hU

private theorem ιK_surjective (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ιK U) := by
  intro s
  have : Nonempty U := hU.to_subtype
  obtain ⟨a, ha⟩ := exists_eq_constantSheafOnSpace_section X X.functionField U inferInstance
    (((totalQuotientSheafIsoConstant X).val.hom.hom.app (op U)) s)
  refine ⟨a, ?_⟩
  change ((totalQuotientSheafIsoConstant X).val.inv.hom.app (op U))
    (((toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U)) a) = s
  rw [← ha]
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (op U)) (totalQuotientSheafIsoConstant X).val.hom_inv_id) s

end KModel

section Dominant

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

private theorem functionFieldMap_germ (U : X.Opens) (hU : genericPoint X ∈ U) (a : Γ(X, U))
    (hY : genericPoint Y ∈ g ⁻¹ᵁ U) :
    functionFieldMap g (X.presheaf.germ U (genericPoint X) hU a) =
      Y.presheaf.germ (g ⁻¹ᵁ U) (genericPoint Y) hY (g.app U a) := by
  have hx : g (genericPoint Y) ∈ U := hY
  have h1 := functionFieldMap_algebraMap_stalk g (genericPoint Y)
    (X.presheaf.germ U (g (genericPoint Y)) hx a)
  have hn : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  have hn' : Nonempty (g ⁻¹ᵁ U) := ⟨⟨genericPoint Y, hY⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := U) hx a] at h1
  erw [Scheme.Hom.germ_stalkMap_apply g U (genericPoint Y) hx a] at h1
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) (U := g ⁻¹ᵁ U) hY _] at h1
  exact h1

end Dominant

section PullbackSmul

variable {X Y : Scheme.{u}}

private theorem isLocalEquationAt_zero (Z : Scheme.{u}) (x : Z) :
    IsLocalEquationAt (0 : Z.CartierDivisor) x 1 :=
  ⟨⊤, trivial, 1, isLocalEquationOn_one _, by simp⟩

private theorem isPullback_zero (g : Y ⟶ X) : IsPullback g (0 : X.CartierDivisor) 0 := by
  refine ⟨fun η _ => ?_, fun y => ⟨1, 1, ⟨1, isLocalEquationAt_zero _ _, isFraction_one_one_one _⟩,
    ?_, ?_, 1, isLocalEquationAt_zero _ _, ?_⟩⟩
  · simp [cartierSupport]
  · simp
  · simp
  · simpa only [map_one] using isFraction_one_one_one y

private theorem notMem_cartierSupport_add {Z : Scheme.{u}} {D₁ D₂ : Z.CartierDivisor} {x : Z}
    (h₁ : x ∉ cartierSupport D₁) (h₂ : x ∉ cartierSupport D₂) : x ∉ cartierSupport (D₁ + D₂) := by
  rw [germ_cartierSupport_eq_zero_iff] at *
  rw [map_add, h₁, h₂, add_zero]

private theorem notMem_cartierSupport_neg {Z : Scheme.{u}} {D : Z.CartierDivisor} {x : Z}
    (h : x ∉ cartierSupport D) : x ∉ cartierSupport (-D) := by
  rw [germ_cartierSupport_eq_zero_iff] at *
  rw [map_neg, h, neg_zero]

private theorem isPullback_add {g : Y ⟶ X} {D₁ D₂ : X.CartierDivisor} {D₁' D₂' : Y.CartierDivisor}
    (h₁ : IsPullback g D₁ D₁') (h₂ : IsPullback g D₂ D₂') :
    IsPullback g (D₁ + D₂) (D₁' + D₂') := by
  refine ⟨fun η hη => notMem_cartierSupport_add (h₁.1 η hη) (h₂.1 η hη), fun y => ?_⟩
  obtain ⟨a₁, b₁, ⟨e₁, he₁, hf₁⟩, ha₁, hb₁, e₁', he₁', hf₁'⟩ := h₁.2 y
  obtain ⟨a₂, b₂, ⟨e₂, he₂, hf₂⟩, ha₂, hb₂, e₂', he₂', hf₂'⟩ := h₂.2 y
  refine ⟨a₁ * a₂, b₁ * b₂, ⟨e₁ * e₂, he₁.add he₂, hf₁.mul hf₂⟩, ?_, ?_, e₁' * e₂',
    he₁'.add he₂', ?_⟩
  · rw [map_mul]; exact mul_mem ha₁ ha₂
  · rw [map_mul]; exact mul_mem hb₁ hb₂
  · rw [map_mul, map_mul]; exact hf₁'.mul hf₂'

private theorem isFraction_inv_swap {Z : Scheme.{u}} {x : Z}
    {f f' : Z.totalQuotientSheaf.presheaf.stalk x} {a b : Z.presheaf.stalk x}
    (h : IsFraction f a b) (hf : IsUnit f) (hf' : f' * f = 1) : IsFraction f' b a := by
  have ha : stalkToTotalQuotient x a = stalkToTotalQuotient x b * f := h.2.symm
  refine ⟨ha ▸ h.1.mul hf, ?_⟩
  rw [ha]
  linear_combination (stalkToTotalQuotient x b) * hf'

private theorem exists_isLocalEquationAt_neg {Z : Scheme.{u}} {D : Z.CartierDivisor} {x : Z}
    {f : Z.totalQuotientSheaf.presheaf.stalk x} (hf : IsLocalEquationAt D x f) :
    ∃ f', f' * f = 1 ∧ IsLocalEquationAt (-D) x f' := by
  obtain ⟨U, hxU, g, hg, rfl⟩ := hf
  refine ⟨Z.totalQuotientSheaf.presheaf.germ U x hxU (↑g⁻¹ : Z.totalQuotientSheaf.obj.obj (op U)),
    ?_, U, hxU, g⁻¹, hg.inv, rfl⟩
  rw [← map_mul, Units.inv_mul, map_one]

private theorem isPullback_neg {g : Y ⟶ X} {D : X.CartierDivisor} {D' : Y.CartierDivisor}
    (h : IsPullback g D D') : IsPullback g (-D) (-D') := by
  refine ⟨fun η hη => notMem_cartierSupport_neg (h.1 η hη), fun y => ?_⟩
  obtain ⟨a, b, ⟨e, he, hf⟩, ha, hb, e', he', hf'⟩ := h.2 y
  obtain ⟨i, hi, hie⟩ := exists_isLocalEquationAt_neg he
  obtain ⟨i', hi', hie'⟩ := exists_isLocalEquationAt_neg he'
  exact ⟨b, a, ⟨i, hie, isFraction_inv_swap hf he.isUnit hi⟩, hb, ha, i', hie',
    isFraction_inv_swap hf' he'.isUnit hi'⟩

private theorem isPullback_zsmul {g : Y ⟶ X} {D : X.CartierDivisor} {D' : Y.CartierDivisor}
    (h : IsPullback g D D') (m : ℤ) : IsPullback g (m • D) (m • D') := by
  induction m using Int.induction_on with
  | zero => simpa using isPullback_zero g
  | succ i ih => simpa [add_smul] using isPullback_add ih h
  | pred i ih =>
    have := isPullback_add ih (isPullback_neg h)
    simpa [sub_eq_add_neg, add_smul] using this

end PullbackSmul

section LocalFraction

variable {Z : Scheme.{u}}

private theorem exists_local_fraction {D : Z.CartierDivisor} {x : Z} {U : Z.Opens} (hxU : x ∈ U)
    (A B : Γ(Z, U)) {e : Z.totalQuotientSheaf.presheaf.stalk x} (he : IsLocalEquationAt D x e)
    (hf : IsFraction e (Z.presheaf.germ U x hxU A) (Z.presheaf.germ U x hxU B)) :
    ∃ (U₀ : Z.Opens) (h₀ : U₀ ≤ U) (_ : x ∈ U₀) (f : (Z.totalQuotientSheaf.obj.obj (op U₀))ˣ),
      IsLocalEquationOn D U₀ f ∧
      toK U₀ (Z.presheaf.map (homOfLE h₀).op B) * (f : Z.totalQuotientSheaf.obj.obj (op U₀)) =
        toK U₀ (Z.presheaf.map (homOfLE h₀).op A) := by
  obtain ⟨U₁, hx₁, f₁, hf₁, rfl⟩ := he
  have h2 := hf.2
  rw [← germ_toTotalQuotient, ← germ_toTotalQuotient] at h2
  have hxW : x ∈ U ⊓ U₁ := ⟨hxU, hx₁⟩
  have e : Z.totalQuotientSheaf.presheaf.germ (U ⊓ U₁) x hxW
      (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op B) * resK inf_le_right (f₁ : _)) =
      Z.totalQuotientSheaf.presheaf.germ (U ⊓ U₁) x hxW
        (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op A)) := by
    rw [map_mul, ← resK_toK inf_le_left B, ← resK_toK inf_le_left A]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply]
    exact h2
  obtain ⟨U₀, hx₀, i, j, hij⟩ := Z.totalQuotientSheaf.presheaf.germ_eq x hxW hxW _ _ e
  have hij' : i = j := Subsingleton.elim _ _
  subst hij'
  refine ⟨U₀, i.le.trans inf_le_left, hx₀, resUnit (i ≫ homOfLE inf_le_right) f₁,
    isLocalEquationOn_resUnit _ hf₁, ?_⟩
  have h3 : resK i.le (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op B) *
      resK inf_le_right (f₁ : _)) =
        resK i.le (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op A)) := hij
  rw [map_mul, ← resK_toK inf_le_left B, ← resK_toK inf_le_left A, resK_resK, resK_resK,
    resK_resK] at h3
  rw [← resK_toK _ B, ← resK_toK _ A]
  convert h3 using 2
  rfl

end LocalFraction

section Rho

private theorem subsingleton_totalQuotient_of_not_nonempty {Z : Scheme.{u}} {U : Z.Opens}
    (h : ¬ (U : Set Z).Nonempty) : Subsingleton (Z.totalQuotientSheaf.obj.obj (op U)) := by
  have : U = ⊥ := TopologicalSpace.Opens.coe_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp h)
  subst this
  exact CommRingCat.subsingleton_of_isTerminal
    (TopCat.Sheaf.isTerminalOfEmpty Z.totalQuotientSheaf)

private def trivRingHom (R S : Type*) [CommRing R] [CommRing S] [Subsingleton S] : R →+* S where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := rfl
  map_add' _ _ := Subsingleton.elim _ _

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

omit [IsIntegral X] [IsIntegral Y] [IsDominant g] in
private theorem not_nonempty_preimage {U : X.Opens} (h : ¬ (U : Set X).Nonempty) :
    ¬ ((g ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
  rintro ⟨y, hy⟩
  exact h ⟨g y, hy⟩

private theorem nonempty_preimage {U : X.Opens} (h : (U : Set X).Nonempty) :
    ((g ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
  have hη : genericPoint X ∈ U := genericPoint_mem h
  refine ⟨genericPoint Y, ?_⟩
  change g (genericPoint Y) ∈ U
  rw [map_genericPoint_of_isDominant g]; exact hη

open Classical in
/-- The ring map `𝓜_X(U) → 𝓜_Y(g⁻¹U)` induced by the extension of function fields. -/
private noncomputable def rho (U : X.Opens) :
    X.totalQuotientSheaf.obj.obj (op U) →+* Y.totalQuotientSheaf.obj.obj (op (g ⁻¹ᵁ U)) :=
  if hU : (U : Set X).Nonempty then
    (ιK (g ⁻¹ᵁ U)).comp ((functionFieldMap g).comp
      (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm.toRingHom)
  else
    haveI := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hU)
    trivRingHom _ _

private theorem rho_ιK {U : X.Opens} (hU : (U : Set X).Nonempty) (κ : X.functionField) :
    rho g U (ιK U κ) = ιK (g ⁻¹ᵁ U) (functionFieldMap g κ) := by
  unfold rho
  simp only [hU, ↓reduceDIte, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  have : (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm (ιK U κ) =
      κ :=
    (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm_apply_apply κ
  rw [this]

private theorem rho_res {U V : X.Opens} (h : V ≤ U) (σ : X.totalQuotientSheaf.obj.obj (op U)) :
    resK (g.preimage_mono h) (rho g U σ) = rho g V (resK h σ) := by
  by_cases hV : (V : Set X).Nonempty
  · have hU : (U : Set X).Nonempty := hV.mono h
    obtain ⟨κ, rfl⟩ := ιK_surjective U hU σ
    rw [rho_ιK g hU, ιK_res h, ιK_res (g.preimage_mono h), rho_ιK g hV]
  · have := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hV)
    exact Subsingleton.elim _ _

private theorem rho_toK (U : X.Opens) (a : Γ(X, U)) :
    rho g U (toK U a) = toK (g ⁻¹ᵁ U) (g.app U a) := by
  by_cases hU : (U : Set X).Nonempty
  · have hη : genericPoint X ∈ U := genericPoint_mem hU
    have hY : genericPoint Y ∈ g ⁻¹ᵁ U := genericPoint_mem (nonempty_preimage g hU)
    rw [← ιK_germ U hη a, rho_ιK g hU, functionFieldMap_germ g U hη a hY, ιK_germ _ hY]
  · have := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hU)
    exact Subsingleton.elim _ _

private theorem rho_injective {U : X.Opens} (hU : (U : Set X).Nonempty) :
    Function.Injective (rho g U) := by
  intro s t h
  obtain ⟨κ, rfl⟩ := ιK_surjective U hU s
  obtain ⟨κ', rfl⟩ := ιK_surjective U hU t
  rw [rho_ιK g hU, rho_ιK g hU] at h
  rw [(functionFieldMap g).injective (ιK_injective _ (nonempty_preimage g hU) h)]

end Rho

section Key

private theorem exists_common_rep_le {Z : Scheme.{u}} (x : Z) (W : Z.Opens) (hxW : x ∈ W)
    (a b : Z.presheaf.stalk x) :
    ∃ (U : Z.Opens) (_ : U ≤ W) (hx : x ∈ U) (A B : Γ(Z, U)),
      Z.presheaf.germ U x hx A = a ∧ Z.presheaf.germ U x hx B = b := by
  obtain ⟨U₁, hx₁, A₁, rfl⟩ := Z.presheaf.exists_germ_eq a
  obtain ⟨U₂, hx₂, B₂, rfl⟩ := Z.presheaf.exists_germ_eq b
  refine ⟨U₁ ⊓ U₂ ⊓ W, inf_le_right, ⟨⟨hx₁, hx₂⟩, hxW⟩,
    Z.presheaf.map (homOfLE (inf_le_left.trans inf_le_left)).op A₁,
    Z.presheaf.map (homOfLE (inf_le_left.trans inf_le_right)).op B₂, ?_, ?_⟩ <;>
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

private theorem mul_left_cancel_totalQuotient {Z : Scheme.{u}} [IsIntegral Z] {V : Z.Opens}
    (hV : (V : Set Z).Nonempty) {B x y : Z.totalQuotientSheaf.obj.obj (op V)} (hB : B ≠ 0)
    (h : B * x = B * y) : x = y := by
  obtain ⟨x', rfl⟩ := ιK_surjective V hV x
  obtain ⟨y', rfl⟩ := ιK_surjective V hV y
  obtain ⟨B', rfl⟩ := ιK_surjective V hV B
  have hB' : B' ≠ 0 := fun h0 => hB (by rw [h0, map_zero])
  have h' : B' * x' = B' * y' := ιK_injective V hV (by simpa only [map_mul] using h)
  rw [mul_left_cancel₀ hB' h']

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

/-- Local equations of a pull-back are the pulled-back local equations. -/
private theorem exists_local_pullback_equation {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') (y : Y) (W : X.Opens) (hW : g y ∈ W) :
    ∃ (U₀ : X.Opens) (_ : U₀ ≤ W) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U₀) (_ : y ∈ V)
      (f₀ : (X.totalQuotientSheaf.obj.obj (op U₀))ˣ) (f' : (Y.totalQuotientSheaf.obj.obj (op V))ˣ),
      IsLocalEquationOn E U₀ f₀ ∧ IsLocalEquationOn E' V f' ∧
        resK hV (rho g U₀ (f₀ : X.totalQuotientSheaf.obj.obj (op U₀))) =
          (f' : Y.totalQuotientSheaf.obj.obj (op V)) := by
  obtain ⟨a, b, ⟨e, he, hf⟩, -, hb, e', he', hf'⟩ := h.2 y
  obtain ⟨U, hUW, hxU, A, B, rfl, rfl⟩ := exists_common_rep_le (g y) W hW a b
  obtain ⟨U₀, h₀, hx₀, f₀, hf₀, hAB⟩ := exists_local_fraction hxU A B he hf
  have hyU₀ : y ∈ g ⁻¹ᵁ U₀ := hx₀
  set A₀ := X.presheaf.map (homOfLE h₀).op A with hA₀
  set B₀ := X.presheaf.map (homOfLE h₀).op B with hB₀
  have hgA : X.presheaf.germ U₀ (g y) hx₀ A₀ = X.presheaf.germ U (g y) hxU A :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hgB : X.presheaf.germ U₀ (g y) hx₀ B₀ = X.presheaf.germ U (g y) hxU B :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hfr : IsFraction e' (Y.presheaf.germ (g ⁻¹ᵁ U₀) y hyU₀ (g.app U₀ A₀))
      (Y.presheaf.germ (g ⁻¹ᵁ U₀) y hyU₀ (g.app U₀ B₀)) := by
    rw [← Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀, ← Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀,
      hgA, hgB]
    exact hf'
  obtain ⟨V, h₁, hy₁, f', hf'', hAB'⟩ := exists_local_fraction hyU₀ _ _ he' hfr
  refine ⟨U₀, h₀.trans hUW, V, h₁, hy₁, f₀, f', hf₀, hf'', ?_⟩
  have hne : toK V (Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀)) ≠ 0 := by
    intro h0
    have h1 : Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀) = 0 :=
      MMP.Intersection.injective_toTotalQuotient V (by rw [h0, map_zero])
    have h2 : Y.presheaf.germ V y hy₁ (Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀)) =
        (g.stalkMap y).hom (X.presheaf.germ U (g y) hxU B) := by
      erw [TopCat.Presheaf.germ_res_apply]
      rw [← hgB]
      exact (Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀ B₀).symm
    rw [h1, map_zero] at h2
    rw [← h2] at hb
    exact zero_notMem_nonZeroDivisors hb
  have e1 := congrArg (fun t => resK h₁ (rho g U₀ t)) hAB
  simp only [map_mul] at e1
  rw [rho_toK, rho_toK, resK_toK, resK_toK] at e1
  exact mul_left_cancel_totalQuotient ⟨y, hy₁⟩ hne (e1.trans hAB'.symm)

private theorem resK_rho_inv {U₀ : X.Opens} {V : Y.Opens} (hV : V ≤ g ⁻¹ᵁ U₀)
    {f₀ : (X.totalQuotientSheaf.obj.obj (op U₀))ˣ} {f' : (Y.totalQuotientSheaf.obj.obj (op V))ˣ}
    (hff : resK hV (rho g U₀ (f₀ : X.totalQuotientSheaf.obj.obj (op U₀))) =
      (f' : Y.totalQuotientSheaf.obj.obj (op V))) :
    resK hV (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) =
      (↑f'⁻¹ : Y.totalQuotientSheaf.obj.obj (op V)) := by
  have hinv : resK hV (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) *
      (f' : Y.totalQuotientSheaf.obj.obj (op V)) = 1 := by
    rw [← hff, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  exact Units.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hinv)

/-- The pull-back of a section of `𝒪_X(E)` over `W` is a section of `𝒪_Y(E')` over `g⁻¹W`. -/
private theorem mem_rho {E : X.CartierDivisor} {E' : Y.CartierDivisor} (h : IsPullback g E E')
    (W : X.Opens) (s : X.totalQuotientSheaf.obj.obj (op W)) (hs : Mem E W s) :
    Mem E' (g ⁻¹ᵁ W) (rho g W s) := by
  refine Mem.of_locally fun y hy => ?_
  obtain ⟨U₀, hU₀, V, hV, hyV, f₀, f', hf₀, hf', hff⟩ := exists_local_pullback_equation g h y W hy
  refine ⟨V, hV.trans (g.preimage_mono hU₀), hyV, ?_⟩
  refine (mem_iff (U := V) (V := V) hf' le_rfl _).2 ?_
  obtain ⟨C, hC⟩ := (mem_iff (U := U₀) (V := U₀) hf₀ le_rfl _).1 (hs.res hU₀)
  refine ⟨Y.presheaf.map (homOfLE hV).op (g.app U₀ C), ?_⟩
  have e1 : resK (hV.trans (g.preimage_mono hU₀)) (rho g W s) =
      resK hV (rho g U₀ (resK hU₀ s)) := by
    rw [← rho_res g hU₀ s, resK_resK]
  rw [e1, ← hC, map_mul, map_mul, rho_toK, resK_toK]
  simp only [resK_id]
  rw [resK_rho_inv g hV hff]

private theorem epi_of_surjective_on_covering {Z : Scheme.{u}} (B : Z.Opens → Prop)
    (hB : ∀ (U : Z.Opens) (T : CategoryTheory.Sieve U),
      (∀ ⦃V : Z.Opens⦄ (f : V ⟶ U), B V → T f) → T ∈ Opens.grothendieckTopology Z U)
    {M N : Z.Modules} (φ : M ⟶ N)
    (hφ : ∀ V : Z.Opens, B V → Function.Surjective (φ.val.app (op V))) : Epi φ := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Z)
      ((SheafOfModules.toSheaf Z.ringCatSheaf).map φ).hom :=
    ⟨fun s => hB _ _ fun V f hV => hφ V hV (N.val.map f.op s)⟩
  exact (SheafOfModules.toSheaf Z.ringCatSheaf).epi_of_epi_map (Sheaf.epi_of_isLocallySurjective _)

/-- The map `𝒪_X(E) ⟶ g_* 𝒪_Y(E')`, `s ↦ g^*s`. -/
private noncomputable def lambdaPre {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') :
    (MMP.CartierDivisor.sheaf E).val ⟶
      ((Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E')).val :=
    (PresheafOfModules.homMk
      { app := fun U => AddCommGrpCat.ofHom
          { toFun := fun s => (⟨rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s),
              mem_rho g h U.unop _ (show ↥((MMP.CartierDivisor.sheafSubmodule E).obj U) from s).2⟩ :
                ↥((MMP.CartierDivisor.sheafSubmodule E').obj (op (g ⁻¹ᵁ U.unop))))
            map_zero' := Subtype.ext (by change rho g U.unop 0 = 0; exact map_zero _)
            map_add' := fun s t => Subtype.ext (by
              exact map_add (rho g U.unop) _ _) }
        naturality := fun {U V} i => by
          ext s
          exact Subtype.ext (rho_res g i.unop.le _).symm }
      (fun U r s => Subtype.ext (by
        change rho g U.unop (toK U.unop r * MMP.CartierDivisorSheaf.sectionVal s) =
          toK (g ⁻¹ᵁ U.unop) (g.app U.unop r) *
            rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s)
        rw [map_mul]
        exact congrArg (· * rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s))
          (rho_toK g U.unop r))))

private noncomputable def lambdaHom {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') :
    MMP.CartierDivisor.sheaf E ⟶ (Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E') :=
  (SheafOfModules.fullyFaithfulForget _).preimage (lambdaPre g h)

private theorem lambdaHom_val {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') : (lambdaHom g h).val = lambdaPre g h :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).map_preimage
    (show (SheafOfModules.forget X.ringCatSheaf).obj (MMP.CartierDivisor.sheaf E) ⟶
      (SheafOfModules.forget X.ringCatSheaf).obj
        ((Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E')) from lambdaPre g h)

private theorem sectionVal_lambdaHom_app {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') (U : X.Opens) (s : Γ(MMP.CartierDivisor.sheaf E, U)) :
    MMP.CartierDivisorSheaf.sectionVal ((lambdaHom g h).app U s) =
      rho g U (MMP.CartierDivisorSheaf.sectionVal s) := by
  have := congrArg (fun φ => φ.app (op U) s) (lambdaHom_val g h)
  exact congrArg MMP.CartierDivisorSheaf.sectionVal this

end Key

private theorem scalarsToGlobalSections_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) :
    scalarsToGlobalSections k sX =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom := by
  have : sX.appLE ⊤ ⊤ (by simp) = sX.appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [this]; rfl

open MMP.CartierDivisor in
/-- On a proper `k`-scheme the global sections of `𝒪_X(D)` are finite-dimensional over `k`. -/
private theorem finiteDimensional_sections {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] (D : X.CartierDivisor) :
    letI := Module.compHom Γ(sheaf D, ⊤) (scalarsToGlobalSections k sX)
    FiniteDimensional k Γ(sheaf D, ⊤) := by
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sX
    (sheaf D) 1
  have := finiteDimensional_cohomologyOverField_of_isProper k sX (sheaf D) 0
  have e := (cohomologyOverFieldZeroLinearIso k sX (sheaf D)).toLinearEquiv
  have key : ∀ φ : k →+* Γ(X, ⊤),
      φ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom →
        (letI := Module.compHom Γ(sheaf D, ⊤) φ; FiniteDimensional k Γ(sheaf D, ⊤)) := by
    rintro φ rfl
    have := Module.Finite.equiv e
    exact this
  exact key _ (scalarsToGlobalSections_eq sX)

/-- An injective `ψ`-semilinear map between modules that are `k`-vector spaces through `φ` and
`ψ ∘ φ` does not decrease the `k`-dimension, the target being finite-dimensional. -/
private theorem finrank_compHom_le_of_injective {k : Type u} [Field k] {R S : Type u} [CommRing R]
    [CommRing S] (φ : k →+* R) (ψ : R →+* S) {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] (p : M →ₛₗ[ψ] N) (hp : Function.Injective p)
    (hN : letI := Module.compHom N (ψ.comp φ); FiniteDimensional k N) :
    (letI := Module.compHom M φ; Module.finrank k M) ≤
      (letI := Module.compHom N (ψ.comp φ); Module.finrank k N) := by
  let _ := Module.compHom M φ
  let _ := Module.compHom N (ψ.comp φ)
  let p' : M →ₗ[k] N :=
    { toFun := p, map_add' := p.map_add, map_smul' := fun c x => p.map_smulₛₗ (φ c) x }
  exact LinearMap.finrank_le_finrank_of_injective (f := p') hp

/-- The `k`-structure on `Γ(Y, 𝒪_Y)` is the one transported along `g` from `Γ(X, 𝒪_X)`. -/
private theorem scalarsToGlobalSections_comp {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X) :
    scalarsToGlobalSections k (g ≫ sX) =
      g.appTop.hom.comp (scalarsToGlobalSections k sX) := by
  simp [scalarsToGlobalSections]
  rfl

/-- Pulling back rational functions along the dominant `g` (with `Y` integral) carries global
sections of `𝒪_X(mD)` injectively to global sections of `𝒪_Y(mD')`. -/
private theorem exists_injective_sectionPullback {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (g : Y ⟶ X) [IsDominant g] {D : X.CartierDivisor} {D' : Y.CartierDivisor}
    (hD' : MMP.Intersection.IsPullback g D D') (m : ℤ) :
    ∃ p : Γ(MMP.CartierDivisor.sheaf (m • D), ⊤) →ₛₗ[g.appTop.hom]
      Γ(MMP.CartierDivisor.sheaf (m • D'), ⊤), Function.Injective p := by
  have hm := isPullback_zsmul hD' m
  let F : ↥((MMP.CartierDivisor.sheafSubmodule (m • D)).obj (op ⊤)) →
      ↥((MMP.CartierDivisor.sheafSubmodule (m • D')).obj (op ⊤)) := fun s =>
    ⟨rho g ⊤ s.1, mem_rho g hm ⊤ _ s.2⟩
  refine ⟨{ toFun := F, map_add' := fun s t => ?_, map_smul' := fun c s => ?_ }, ?_⟩
  · exact MMP.CartierDivisorSheaf.sectionVal_injective (map_add _ _ _)
  · refine MMP.CartierDivisorSheaf.sectionVal_injective ?_
    change rho g ⊤ (toK ⊤ c * MMP.CartierDivisorSheaf.sectionVal s) =
      toK (g ⁻¹ᵁ ⊤) (g.app ⊤ c) * rho g ⊤ (MMP.CartierDivisorSheaf.sectionVal s)
    rw [map_mul, rho_toK]
  · intro s t hst
    exact MMP.CartierDivisorSheaf.sectionVal_injective (rho_injective (U := ⊤) g ⟨genericPoint X,
        trivial⟩
      (congrArg MMP.CartierDivisorSheaf.sectionVal hst))

/-- Pulling back sections: `h⁰(X, mD) ≤ h⁰(Y, mD')`. -/
private theorem cartierH0_le_of_isPullback {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : IsProperVariety k sX) (hY : IsProperVariety k sY)
    (g : Y ⟶ X) (hg : g ≫ sX = sY) (hbir : IsBirationalMorphism g)
    {D : X.CartierDivisor} {D' : Y.CartierDivisor} (hD' : MMP.Intersection.IsPullback g D D')
    (m : ℤ) : cartierH0 k sX (m • D) ≤ cartierH0 k sY (m • D') := by
  have := hX.toIsVariety
  have := hY.toIsVariety
  have : IsDominant g := hbir.isDominant
  obtain ⟨p, hp⟩ := exists_injective_sectionPullback g hD' m
  subst hg
  have : IsProper (g ≫ sX) := hY.toIsProper
  have hN := finiteDimensional_sections (g ≫ sX) (m • D')
  unfold cartierH0
  rw [scalarsToGlobalSections_comp] at hN ⊢
  exact finrank_compHom_le_of_injective _ _ p hp hN

section Biregular

private lemma isIso_app_of_isIso_morphismRestrict {X Y : Scheme.{u}} (g : Y ⟶ X) {W : X.Opens}
    (hW : IsIso (g ∣_ W)) : IsIso (g.app W) := by
  have h := morphismRestrict_appTop g W
  have : IsIso (g.app (W.ι ''ᵁ ⊤) ≫
      Y.presheaf.map (eqToHom (image_morphismRestrict_preimage g W ⊤)).op) := by
    rw [← h]; exact Scheme.Hom.instIsIsoCommRingCatApp _ ⊤
  have := IsIso.of_isIso_comp_right (g.app (W.ι ''ᵁ ⊤))
    (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage g W ⊤)).op)
  rwa [Scheme.Opens.ι_image_top] at this

/-- A morphism `g` whose rational map is that of a partial isomorphism `e` agrees with `e` on
`e.source`. -/
private lemma iso_hom_comp_ι_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [X.IsSeparated] (g : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = g.toRationalMap) :
    e.iso.hom ≫ e.target.ι = e.source.ι ≫ g := by
  obtain ⟨W, hW, hWl, hWr, hEq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
  have hWl' : W ≤ e.source := hWl
  have : IsDominant (Y.homOfLE hWl') := AlgebraicGeometry.Opens.isDominant_homOfLE hW _
  refine ext_of_isDominant (Y.homOfLE hWl') ?_
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom] at hEq
  refine hEq.trans ?_
  rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
  exact Scheme.homOfLE_ι_assoc Y (show W ≤ ⊤ from hWr) g

/-- A morphism `g : Y ⟶ X` of reduced separated schemes which agrees with a partial isomorphism
`e` on `e.source` is an isomorphism over the domain of definition of the rational map `e⁻¹`:
the morphism `s` representing `e⁻¹` there is a section of `g`, and it is a retraction because
`g ≫ s` and the identity agree on the dense open `e.source`. -/
private lemma isBiregular_domain_symm {X Y : Scheme.{u}} [IsReduced X] [IsReduced Y]
    [X.IsSeparated] [Y.IsSeparated] (g : Y ⟶ X) (e : Y.PartialIso X)
    (key : e.iso.hom ≫ e.target.ι = e.source.ι ≫ g) :
    IsBiregular g e.symm.toRationalMap.domain := by
  set V := e.symm.toRationalMap.domain
  let s : V.toScheme ⟶ Y := e.symm.toRationalMap.toPartialMap.hom
  have hTV : e.target ≤ V := e.symm.toPartialMap.le_domain_toRationalMap
  have hs : X.homOfLE hTV ≫ s = e.iso.inv ≫ e.source.ι :=
    e.symm.toPartialMap.toPartialMap_toRationalMap_restrict
  have hsg : s ≫ g = V.ι := by
    have : IsDominant (X.homOfLE hTV) :=
      AlgebraicGeometry.Opens.isDominant_homOfLE e.dense_target _
    refine ext_of_isDominant (X.homOfLE hTV) ?_
    rw [reassoc_of% hs, ← key, Iso.inv_hom_id_assoc, Scheme.homOfLE_ι]
  have hrange : Set.range s ⊆ Set.range (g ⁻¹ᵁ V).ι := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    change g (s v) ∈ V
    rw [← Scheme.Hom.comp_apply, hsg]
    exact v.2
  let s' : V.toScheme ⟶ (g ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift (g ⁻¹ᵁ V).ι s hrange
  have hs' : s' ≫ (g ⁻¹ᵁ V).ι = s := IsOpenImmersion.lift_fac _ _ _
  have hSV : e.source ≤ g ⁻¹ᵁ V := by
    intro y hy
    obtain ⟨y', rfl⟩ : y ∈ Set.range e.source.ι := by rwa [Scheme.Opens.range_ι]
    change g (e.source.ι y') ∈ V
    rw [← Scheme.Hom.comp_apply, ← key, Scheme.Hom.comp_apply]
    exact hTV (e.iso.hom y').2
  refine ⟨⟨s', ?_, ?_⟩⟩
  · rw [← cancel_mono (g ⁻¹ᵁ V).ι, Category.assoc, hs', Category.id_comp]
    have : IsDominant (Y.homOfLE hSV) :=
      AlgebraicGeometry.Opens.isDominant_homOfLE e.dense_source _
    refine ext_of_isDominant (Y.homOfLE hSV) ?_
    have hj : Y.homOfLE hSV ≫ (g ∣_ V) = e.iso.hom ≫ X.homOfLE hTV := by
      rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
        Category.assoc, Scheme.homOfLE_ι, key]
    rw [reassoc_of% hj, hs, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]
  · rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hs', hsg,
      Category.id_comp]

/-- A birational morphism of integral separated schemes is an isomorphism over a nonempty open. -/
private lemma exists_nonempty_isBiregular {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.IsSeparated] [Y.IsSeparated] (g : Y ⟶ X) (hg : IsBirationalMorphism g) :
    ∃ V : X.Opens, (V : Set X).Nonempty ∧ IsBiregular g V := by
  obtain ⟨e, he⟩ := hg
  obtain ⟨x, hx⟩ := e.dense_target.nonempty
  exact ⟨_, ⟨x, e.symm.toPartialMap.le_domain_toRationalMap hx⟩,
    isBiregular_domain_symm g e (iso_hom_comp_ι_eq_of_toRationalMap_eq g e he)⟩

end Biregular

/-- A space whose topological Krull dimension is negative is empty. -/
private lemma isEmpty_of_topologicalKrullDim_lt_zero {T : Type*} [TopologicalSpace T]
    (h : topologicalKrullDim T < 0) : IsEmpty T :=
  ⟨fun x => h.not_ge (Order.krullDim_nonneg_iff.mpr
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩)⟩

/-- `h⁰(mD)` is the dimension of the global sections of the twist `𝒪_X ⊗ 𝒪_X(D)^{⊗ m}`. -/
private theorem cartierH0_smul_eq_finrank_twist {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (D : X.CartierDivisor) (m : ℤ) :
    cartierH0 k sX (m • D) =
      Module.finrank k (cohomologyOverField k sX
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
          (fun _ : Fin 1 => sh D) (fun _ => m)) 0) := by
  rw [cartierH0_eq_finrank]
  obtain ⟨e⟩ := MMP.Resolution.Bridges.cartierSheaf_sum_iso_twistedSheaf (fun _ : Fin 1 => D)
    (fun _ => m)
  have := finrank_cohomologyOverField_eq_of_iso k sX e 0
  rwa [show (∑ _i : Fin 1, m • D) = m • D by simp] at this

/-- A coherent module supported in dimension `< n` has `m · h⁰(Q ⊗ L^m) ≤ C mⁿ`. -/
private theorem exists_mul_finrank_twist_le {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (Q : X.Modules)
    (hQ : SheafOfModules.IsCoherent Q) (n : ℕ)
    (hdim : topologicalKrullDim (SheafOfModules.supp Q) < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℤ, 0 < m →
      (m : ℝ) * (Module.finrank k (cohomologyOverField k sX
        (twistedSheaf Q (fun _ : Fin 1 => L) (fun _ => m)) 0) : ℝ) ≤ C * (m : ℝ) ^ n := by
  cases n with
  | zero =>
    rw [Nat.cast_zero] at hdim
    have hemp : SheafOfModules.supp Q = ∅ :=
      Set.isEmpty_coe_sort.mp (isEmpty_of_topologicalKrullDim_lt_zero hdim)
    refine ⟨1, one_pos, fun m hm => ?_⟩
    have hz' := isZero_twistedSheaf_of_isZero (fun _ : Fin 1 => L)
      (SheafOfModules.isZero_of_supp_eq_empty Q hemp) (fun _ => m)
    have := ModuleCat.subsingleton_of_isZero (isZero_cohomologyOverField_of_isZero k sX hz' 0)
    rw [Module.finrank_zero_of_subsingleton]
    simp
  | succ n =>
    obtain ⟨C, hC, h⟩ :=
      MMP.Foundations.exists_finrank_cohomologyOverField_zero_twistedSheaf_le_pow k sX L Q hQ n
        (ENat.WithBot.lt_add_one_iff.mp hdim)
    refine ⟨C, hC, fun m hm => ?_⟩
    calc (m : ℝ) * _ ≤ (m : ℝ) * (C * (m : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left (h m hm) (by exact_mod_cast hm.le)
      _ = C * (m : ℝ) ^ (n + 1) := by ring

/-- Over an open where `g` is biregular, `𝒪_X → g_*𝒪_Y` restricts to an isomorphism. -/
theorem isIso_restrict_unitToPushforwardUnit {X Y : Scheme.{u}} (g : Y ⟶ X) {V : X.Opens}
    (hV : IsBiregular g V) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      (ClosedImmersionCoherentImage.unitToPushforwardUnit g)) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  have hW : V.ι ''ᵁ W ≤ V := by
    rintro x ⟨y, _, rfl⟩
    exact y.2
  have h1 : IsIso (g.app (V.ι ''ᵁ W)) :=
    isIso_app_of_isIso_morphismRestrict g (isBiregular_iff_le_biregularLocus.mpr
      (hW.trans (le_biregularLocus hV)))
  change IsIso (Scheme.Modules.Hom.app (ClosedImmersionCoherentImage.unitToPushforwardUnit g)
    (V.ι ''ᵁ W))
  have h : IsIso (g.toRingCatSheafHom.hom.app (Opposite.op (V.ι ''ᵁ W))) := by
    change IsIso ((forget₂ CommRingCat RingCat).map (g.app (V.ι ''ᵁ W)))
    infer_instance
  change IsIso ((forget₂ RingCat AddCommGrpCat).map
    (g.toRingCatSheafHom.hom.app (Opposite.op (V.ι ''ᵁ W))))
  infer_instance

/-- A subset of the complement of a nonempty open of an integral scheme of dimension `n` has
dimension `< n`. -/
theorem topologicalKrullDim_lt_of_subset_compl {X : Scheme.{u}} [IsIntegral X] {V : X.Opens}
    (hVne : (V : Set X).Nonempty) {n : ℕ} (hn : topologicalKrullDim X = n) {S : Set X}
    (hS : S ⊆ (V : Set X)ᶜ) : topologicalKrullDim S < n := by
  have hfin : topologicalKrullDim X < ⊤ := by
    rw [hn]
    change (((n : ℕ) : ℕ∞) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞)
    exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)
  have hlt := topologicalKrullDim_lt_of_isClosed_ne_univ V.isOpen.isClosed_compl
    (Set.compl_ne_univ.mpr hVne) hfin
  rw [hn] at hlt
  exact ((Topology.IsEmbedding.inclusion hS).isInducing.topologicalKrullDim_le).trans_lt hlt

/-- The quotient `Q = g_*𝒪_Y / 𝒪_X` is coherent and supported in dimension `< n`
(`𝒪_X → g_*𝒪_Y` is injective, an isomorphism at the generic point, and `g_*𝒪_Y` is coherent as
`g` is proper). -/
private theorem exists_shortExact_pushforward_unit {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : IsProperVariety k sX) (hY : IsProperVariety k sY)
    (g : Y ⟶ X) (hg : g ≫ sX = sY) (hbir : IsBirationalMorphism g)
    (n : ℕ) (hn : topologicalKrullDim X = n) :
    ∃ S : ShortComplex X.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ SheafOfModules.unit X.ringCatSheaf) ∧
      Nonempty (S.X₂ ≅ (Scheme.Modules.pushforward g).obj (SheafOfModules.unit Y.ringCatSheaf)) ∧
      SheafOfModules.IsCoherent S.X₁ ∧ SheafOfModules.IsCoherent S.X₂ ∧
      SheafOfModules.IsCoherent S.X₃ ∧
      topologicalKrullDim (SheafOfModules.supp S.X₃) < n := by
  have hXi := hX.toIsVariety
  have hYi : IsProperVariety k (g ≫ sX) := hg ▸ hY
  have hYv := hYi.toIsVariety
  have : IsIntegral X := hXi.toIsIntegral
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsDominant g := hbir.isDominant
  have : IsSeparated sX := hXi.toIsSeparated
  have : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sX]; infer_instance⟩
  have : IsSeparated (g ≫ sX) := hYv.toIsSeparated
  have : Y.IsSeparated := ⟨by rw [← Limits.terminal.comp_from (g ≫ sX)]; infer_instance⟩
  have : IsProper (g ≫ sX) := hYi.toIsProper
  have : IsProper g := IsProper.of_comp g sX
  have : LocallyOfFiniteType sX := hXi.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hcohY : (SheafOfModules.unit Y.ringCatSheaf).IsCoherent := by
    have : LocallyOfFiniteType (g ≫ sX) := hYv.toLocallyOfFiniteType
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
    exact Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Y
  have hcohX : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  have hcohP :
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit Y.ringCatSheaf)).IsCoherent :=
    (Stacks.AlgebraicGeometry.ProperMapping.isCoherent_higherDirectImage_zero_iff g _).1
      (ProperCoherenceWitness.higherDirectImageIsCoherent Y X g inferInstance inferInstance _
        hcohY 0)
  -- the map `𝒪_X → g_* 𝒪_Y`
  let i : SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward g).obj (SheafOfModules.unit Y.ringCatSheaf) :=
    ClosedImmersionCoherentImage.unitToPushforwardUnit g
  have hmono : Mono i := by
    refine (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
      (PresheafOfModules.mono_of_injective fun W e e' hee => ?_)
    have : IsSchemeTheoreticallyDominant g := .of_isDominant g
    exact g.app_injective W.unop hee
  obtain ⟨V, hVne, hV⟩ := exists_nonempty_isBiregular g hbir
  refine ⟨_, ShortComplex.shortExact_mk_cokernel_π i, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, hcohX, hcohP,
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel_modules hcohX hcohP i, ?_⟩
  change topologicalKrullDim (SheafOfModules.supp (Limits.cokernel i)) < n
  exact topologicalKrullDim_lt_of_subset_compl hVne hn fun x hx hxV =>
    Stacks.AlgebraicGeometry.ConfinedDevissage.notMem_supp_cokernel_of_isIso_restrict i V
      (isIso_restrict_unitToPushforwardUnit g hV) x hxV hx

/-- The adjoint `g^*𝒪_X(D) ⟶ 𝒪_Y(D')` of the pull-back of sections is an epimorphism. -/
private theorem epi_homEquiv_symm_lambdaHom {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) [IsDominant g] {D : X.CartierDivisor} {D' : Y.CartierDivisor}
    (hD' : MMP.Intersection.IsPullback g D D') :
    Epi (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv (sh D) (sh D')).symm
      (lambdaHom g hD')) := by
  let ℓ := lambdaHom g hD'
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  let ψ : (Scheme.Modules.pullback g).obj (sh D) ⟶
      sh D' := (adj.homEquiv _ _).symm ℓ
  change Epi ψ
  have hψ : ∀ (U : X.Opens) (s : Γ(sh D, U)),
      ψ.app (g ⁻¹ᵁ U) ((adj.unit.app (sh D)).app U s) =
        ℓ.app U s := by
    have h1 : adj.unit.app (sh D) ≫ (Scheme.Modules.pushforward g).map ψ = ℓ := by
      have := (adj.homEquiv _ _).apply_symm_apply ℓ
      rwa [Adjunction.homEquiv_unit] at this
    exact fun U s => congrArg (fun φ => φ.app U s) h1
  refine epi_of_surjective_on_covering
    (fun V : Y.Opens => Function.Surjective (ψ.app V)) ?_ ψ (fun V hV => hV)
  intro U T hT
  rw [Opens.mem_grothendieckTopology]
  intro y hy
  obtain ⟨U₀, -, V₀, hV₀, hyV₀, f₀, f', hf₀, hf', hff⟩ :=
    exists_local_pullback_equation g hD' y ⊤ trivial
  refine ⟨V₀ ⊓ U, homOfLE inf_le_right, hT (homOfLE inf_le_right) ?_, ⟨hyV₀, hy⟩⟩
  have hVV₀ : V₀ ⊓ U ≤ V₀ := inf_le_left
  intro t
  have hmem : Mem D' (V₀ ⊓ U) (MMP.CartierDivisorSheaf.sectionVal t) :=
    (show ↥((MMP.CartierDivisor.sheafSubmodule D').obj (op (V₀ ⊓ U))) from t).2
  obtain ⟨a, ha⟩ := (mem_iff (U := V₀) (V := V₀ ⊓ U) hf' hVV₀ _).1 hmem
  let e₀ : Γ(sh D, U₀) :=
    (⟨(↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀)), mem_inv hf₀⟩ :
      ↥((MMP.CartierDivisor.sheafSubmodule D).obj (op U₀)))
  let ε := (adj.unit.app (sh D)).app U₀ e₀
  refine ⟨a • ((Scheme.Modules.pullback g).obj
    (sh D)).presheaf.map
      (homOfLE (hVV₀.trans hV₀)).op ε, ?_⟩
  apply MMP.CartierDivisorSheaf.sectionVal_injective
  rw [Scheme.Modules.Hom.app_smul]
  have nat := PresheafOfModules.naturality_apply ψ.val (homOfLE (hVV₀.trans hV₀)).op ε
  have h3 : MMP.CartierDivisorSheaf.sectionVal
      (ψ.app (V₀ ⊓ U) (((Scheme.Modules.pullback g).obj
        (sh D)).presheaf.map
          (homOfLE (hVV₀.trans hV₀)).op ε)) =
      resK (hVV₀.trans hV₀) (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) :=
    (congrArg MMP.CartierDivisorSheaf.sectionVal (nat.trans (congrArg
      ((sh D').val.map (homOfLE (hVV₀.trans hV₀)).op) (hψ U₀ e₀)))).trans
      (congrArg (resK (hVV₀.trans hV₀)) (sectionVal_lambdaHom_app g hD' U₀ e₀))
  change toK (V₀ ⊓ U) a * MMP.CartierDivisorSheaf.sectionVal
    (ψ.app (V₀ ⊓ U) (((Scheme.Modules.pullback g).obj
        (sh D)).presheaf.map
          (homOfLE (hVV₀.trans hV₀)).op ε)) = _
  rw [h3, ← ha, ← resK_resK hVV₀ hV₀, resK_rho_inv g hV₀ hff]

/-- The pull-back of `𝒪_X(D)` is `𝒪_Y(D')`: `g^*𝒪_X(D) ≅ 𝒪_Y(D')` for `D' = g^*D`. -/
private theorem nonempty_pullback_sheaf_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : IsProperVariety k sX) (hY : IsProperVariety k sY)
    (g : Y ⟶ X) (hg : g ≫ sX = sY) (hbir : IsBirationalMorphism g)
    {D : X.CartierDivisor} {D' : Y.CartierDivisor} (hD' : MMP.Intersection.IsPullback g D D') :
    Nonempty ((Scheme.Modules.pullback g).obj (sh D) ≅
      sh D') := by
  have hXi := hX.toIsVariety
  have hYi : IsProperVariety k (g ≫ sX) := hg ▸ hY
  have hYv := hYi.toIsVariety
  have : IsIntegral X := hXi.toIsIntegral
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsDominant g := hbir.isDominant
  have hinvpb : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj (sh D)) :=
    SheafOfModules.isInvertible_pullback g _
  let ψ : (Scheme.Modules.pullback g).obj (sh D) ⟶ sh D' :=
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm (lambdaHom g hD')
  have : Epi ψ := epi_homEquiv_symm_lambdaHom g hD'
  exact ⟨@asIso _ _ _ _ ψ (Stacks.Chow.GenuineChern.isIso_of_epi_of_isInvertible ψ hinvpb
    inferInstance)⟩

/-- The twist of a direct image is the direct image of the twist (projection formula for the
invertible module `L^{⊗ m}`), for an arbitrary morphism. -/
private theorem nonempty_twistedSheaf_pushforward_iso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 ((Scheme.Modules.pullback g).obj L)]
    (N : Y.Modules) (m : ℤ) :
    Nonempty (twistedSheaf ((Scheme.Modules.pushforward g).obj N) (fun _ : Fin 1 => L)
        (fun _ => m) ≅
      (Scheme.Modules.pushforward g).obj
        (twistedSheaf N (fun _ : Fin 1 => (Scheme.Modules.pullback g).obj L) (fun _ => m))) := by
  have e := Stacks.ProjectionFormula.higherDirectImageTwistedSheafIso g (fun _ : Fin 1 => L) N
    (fun _ => m) 0
  have z1 : ((Scheme.Modules.pushforward g).rightDerivedPlus 0).obj N ≅
      (Scheme.Modules.pushforward g).obj N :=
    Stacks.RightDerivedPlus.rightDerivedPlusZeroObjIso _ N
  have z2 : ((Scheme.Modules.pushforward g).rightDerivedPlus 0).obj
      (twistedSheaf N (fun _ : Fin 1 => (Scheme.Modules.pullback g).obj L) (fun _ => m)) ≅
      (Scheme.Modules.pushforward g).obj
        (twistedSheaf N (fun _ : Fin 1 => (Scheme.Modules.pullback g).obj L) (fun _ => m)) :=
    Stacks.RightDerivedPlus.rightDerivedPlusZeroObjIso _ _
  have e' : twistedSheaf (((Scheme.Modules.pushforward g).rightDerivedPlus 0).obj N)
      (fun _ : Fin 1 => L) (fun _ => m) ≅
    ((Scheme.Modules.pushforward g).rightDerivedPlus 0).obj
      (twistedSheaf N (fun _ : Fin 1 => (Scheme.Modules.pullback g).obj L) (fun _ => m)) :=
    e.symm
  exact ⟨(twistedSheafIsoOfIso (fun _ : Fin 1 => L) z1.symm (fun _ => m)).trans (e'.trans z2)⟩

/-- The twist by an invertible module depends only on its isomorphism class. -/
private theorem nonempty_twistedSheaf_iso_of_iso {Z : Scheme.{u}} (F : Z.Modules)
    (L L' : Z.Modules) [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L'] (e : L ≅ L') (m : ℤ) :
    Nonempty (twistedSheaf F (fun _ : Fin 1 => L) (fun _ => m) ≅
      twistedSheaf F (fun _ : Fin 1 => L') (fun _ => m)) :=
  ⟨Stacks.SheafOfModules.Invertible.tensorProductIso Z.presheaf Z.ringCatSheaf.2 (Iso.refl F)
    (Stacks.SheafOfModules.TensorPower.tensorPowerCongr Z.presheaf Z.ringCatSheaf.2 e m)⟩

/-- Global sections of a direct image are those of the module. -/
private theorem finrank_cohomologyOverField_pushforward_zero {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X) (N : Y.Modules) :
    Module.finrank k (cohomologyOverField k sX ((Scheme.Modules.pushforward g).obj N) 0) =
      Module.finrank k (cohomologyOverField k (g ≫ sX) N 0) := by
  have e1 : Module.finrank k (cohomologyOverField k sX ((Scheme.Modules.pushforward g).obj N) 0) =
      (letI : Module k Γ((Scheme.Modules.pushforward g).obj N, ⊤) :=
        Module.compHom _ (scalarsToGlobalSections k sX)
      Module.finrank k Γ((Scheme.Modules.pushforward g).obj N, ⊤)) := by
    rw [(cohomologyOverFieldZeroLinearIso k sX _).toLinearEquiv.finrank_eq,
      scalarsToGlobalSections_eq]
    rfl
  have e2 : Module.finrank k (cohomologyOverField k (g ≫ sX) N 0) =
      (letI : Module k Γ(N, ⊤) :=
        Module.compHom _ (scalarsToGlobalSections k (g ≫ sX))
      Module.finrank k Γ(N, ⊤)) := by
    rw [(cohomologyOverFieldZeroLinearIso k (g ≫ sX) N).toLinearEquiv.finrank_eq,
      scalarsToGlobalSections_eq]
    rfl
  rw [e1, e2]
  rfl

/-- `h⁰(Y, 𝒪_Y(mD')) ≤ h⁰(X, g_*𝒪_Y ⊗ 𝒪_X(D)^{⊗ m})`: by the projection formula the right side
is `h⁰(Y, g^*𝒪_X(D)^{⊗ m})`, and `g^*𝒪_X(D) ≅ 𝒪_Y(D')`. -/
private theorem cartierH0_le_finrank_twist_pushforward {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : IsProperVariety k sX) (hY : IsProperVariety k sY)
    (g : Y ⟶ X) (hg : g ≫ sX = sY) (hbir : IsBirationalMorphism g)
    {D : X.CartierDivisor} {D' : Y.CartierDivisor} (hD' : MMP.Intersection.IsPullback g D D')
    (m : ℤ) :
    cartierH0 k sY (m • D') ≤
      Module.finrank k (cohomologyOverField k sX
        (twistedSheaf ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit Y.ringCatSheaf))
          (fun _ : Fin 1 => sh D) (fun _ => m)) 0) := by
  obtain ⟨ψ⟩ := nonempty_pullback_sheaf_iso hX hY g hg hbir hD'
  subst hg
  have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj (sh D)) :=
    SheafOfModules.isInvertible_pullback g _
  obtain ⟨e₃⟩ := nonempty_twistedSheaf_iso_of_iso (SheafOfModules.unit Y.ringCatSheaf) _ _ ψ m
  obtain ⟨e₅⟩ := nonempty_twistedSheaf_pushforward_iso g
    (sh D) (SheafOfModules.unit Y.ringCatSheaf) m
  exact le_of_eq ((cartierH0_smul_eq_finrank_twist (g ≫ sX) D' m).trans
    ((finrank_cohomologyOverField_eq_of_iso k (g ≫ sX) e₃ 0).symm.trans
      ((finrank_cohomologyOverField_pushforward_zero sX g _).symm.trans
        (finrank_cohomologyOverField_eq_of_iso k sX e₅ 0).symm)))

/-- The cokernel bound: `m · h⁰(Y, mD') ≤ m · h⁰(X, mD) + C mⁿ`, i.e.
`h⁰(Y, mD') ≤ h⁰(X, mD) + C m^{n-1}` for `n = dim X`. -/
private theorem exists_cartierH0_isPullback_le {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : IsProperVariety k sX) (hY : IsProperVariety k sY)
    (g : Y ⟶ X) (hg : g ≫ sX = sY) (hbir : IsBirationalMorphism g)
    {D : X.CartierDivisor} {D' : Y.CartierDivisor} (hD' : MMP.Intersection.IsPullback g D D')
    (n : ℕ) (hn : topologicalKrullDim X = n) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℤ, 0 < m →
      (m : ℝ) * cartierH0 k sY (m • D') ≤
        (m : ℝ) * cartierH0 k sX (m • D) + C * (m : ℝ) ^ n := by
  have := hX.toIsProper
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, h1, h2, h3, hdim⟩ :=
    exists_shortExact_pushforward_unit hX hY g hg hbir n hn
  obtain ⟨C, hC, hCm⟩ := exists_mul_finrank_twist_le sX (sh D)
    S.X₃ h3 n hdim
  refine ⟨C, hC, fun m hm => ?_⟩
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have e2 := finrank_cohomologyOverField_eq_of_iso k sX
    (twistedSheafIsoOfIso (fun _ : Fin 1 => sh D) e₂ (fun _ => m)) 0
  have e1 := finrank_cohomologyOverField_eq_of_iso k sX
    (twistedSheafIsoOfIso (fun _ : Fin 1 => sh D) e₁ (fun _ => m)) 0
  have hadd := finrank_twistedSheaf_le_add k sX (fun _ : Fin 1 => sh D) hS h1 h2 h3 (fun _ => m)
  have hP2 := cartierH0_le_finrank_twist_pushforward hX hY g hg hbir hD' m
  have hX0 := cartierH0_smul_eq_finrank_twist sX D m
  have hnat : cartierH0 k sY (m • D') ≤ cartierH0 k sX (m • D) + Module.finrank k
      (cohomologyOverField k sX (twistedSheaf S.X₃ (fun _ : Fin 1 => sh D) (fun _ => m)) 0) := by
    rw [hX0]
    omega
  have hreal : (cartierH0 k sY (m • D') : ℝ) ≤ cartierH0 k sX (m • D) + (Module.finrank k
      (cohomologyOverField k sX (twistedSheaf S.X₃ (fun _ : Fin 1 => sh D) (fun _ => m)) 0) : ℝ) :=
    by exact_mod_cast hnat
  have := hCm m hm
  nlinarith [mul_le_mul_of_nonneg_left hreal hm'.le]

/-- **Bigness is a birational invariant.** For a birational morphism `g : Y ⟶ X` of proper
varieties over `k`, a Cartier divisor `D` on `X` is big if and only if its pull-back `D'` to `Y`
is big. -/
@[mmp "lem_km2c_big_birational_invariance"]
public theorem isBigCartier_iff_of_isPullback {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : IsProperVariety k sX) (hY : IsProperVariety k sY)
    (g : Y ⟶ X) (hg : g ≫ sX = sY) (hbir : IsBirationalMorphism g)
    {D : X.CartierDivisor} {D' : Y.CartierDivisor} (hD' : MMP.Intersection.IsPullback g D D') :
    IsBigCartier k sX D ↔ IsBigCartier k sY D' := by
  have hdim : topologicalKrullDim X = topologicalKrullDim Y :=
    topologicalKrullDim_eq_of_isBirationalMorphism sX sY hbir
  constructor
  · rintro ⟨n, hn, c, hc, k₀, h⟩
    refine ⟨n, hdim ▸ hn, c, hc, k₀, fun m hm => (h m hm).trans_le ?_⟩
    exact_mod_cast cartierH0_le_of_isPullback hX hY g hg hbir hD' m
  · rintro ⟨n, hn, c, hc, k₀, h⟩
    obtain ⟨C, hC, hCb⟩ := exists_cartierH0_isPullback_le hX hY g hg hbir hD' n (hdim ▸ hn)
    refine ⟨n, hdim ▸ hn, c / 2, half_pos hc, max k₀ (max 1 ⌈2 * C / c⌉), fun m hm => ?_⟩
    have hm0 : k₀ ≤ m := le_of_max_le_left hm
    have hm1 : (1 : ℤ) ≤ m := (le_max_left _ _).trans (le_of_max_le_right hm)
    have hm2 : ⌈2 * C / c⌉ ≤ m := (le_max_right _ _).trans (le_of_max_le_right hm)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hmC : 2 * C / c ≤ (m : ℝ) := by exact_mod_cast (Int.ceil_le.mp hm2)
    have hCm : 2 * C ≤ c * m := by
      rw [div_le_iff₀ hc] at hmC
      linarith
    have h1 := h m hm0
    have h2 := hCb m (by omega)
    have hpow : (0 : ℝ) < (m : ℝ) ^ n := pow_pos hmpos n
    have key : (m : ℝ) * (c / 2 * (m : ℝ) ^ n) < (m : ℝ) * MMP.Mori.cartierH0 k sX (m • D) := by
      nlinarith [mul_lt_mul_of_pos_left h1 hmpos, mul_le_mul_of_nonneg_right hCm hpow.le]
    exact lt_of_mul_lt_mul_left key hmpos.le

end BirationalInvariance

end MMP.Mori
