module
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
public import MMP.AlgebraicGeometry.Curves.Maps.CoefficientSpace
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor

/-!
# A vertical coefficient-one boundary admits nonzero vanishing pluriforms

Let `X` be a smooth projective variety of dimension `n` over a field `k`, `B` an snc
`ℚ`-divisor with coefficients at most one, `D = K_X + B`, and `T = B^{=1}` the reduced
coefficient-one part. Suppose `D` is semiample and its contraction `f : X ⟶ Y` satisfies
`rD = f^*A` for some `r > 0` and an ample Cartier divisor `A` on `Y`. If every component of `T`
has image a proper subset of `Y`, then for every `a ≥ 1` the space `H⁰(X, mD - aT)` is nonzero
for arbitrarily large `m` divisible by any prescribed integer.

The proof takes a section of `I^a ⊗ 𝒪_Y(NA)` nonzero at the generic point of `Y`, where `I` is
the ideal of the union of the images of the components of `T`, and pulls it back.

## Main results

* `MMP.Fourfold.exists_pluricanonicalSections_sub_coeffOnePart_ne_bot`.

## Implementation notes

* `H⁰(X, mD - aT)` is the space of rational `m`-canonical forms `τ` with
  `div τ + ⌊mB⌋ - aT ≥ 0`, that is `MMP.Mori.pluricanonicalSections` of `⌊mB⌋ - aT`; for `r ∣ m`
  the divisor `mB` is integral. This is independent of the choice of canonical divisor.
* The relation `rD = f^*A` is an equality of divisors `r(K + B) = f^*A` for some canonical
  divisor `K`, i.e. linear equivalence `r(K_X + B) ∼ f^*A`; the pull-back is
  `MMP.Mori.Divisor.pullback`, whose side condition (`f` maps the generic point outside
  `Supp A`) is packaged existentially.
* The contraction is `MMP.Fourfold.IsContraction`: projective, surjective, with `f_* 𝒪_X = 𝒪_Y`,
  between normal varieties.
* The base field is arbitrary; the source works over `ℂ`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- `𝒪_Y(mA) ≅ 𝒪_Y(A)^{⊗ m}` for a Cartier divisor `A`. -/
private noncomputable def divisorialSheafNsmulIso {V : Scheme.{u}} [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] {A : Divisor V} (hA : A.IsCartier) (m : ℕ) :
    haveI := hA.isInvertibleModule_divisorialSheaf
    (m • A).divisorialSheaf ≅ Stacks.Ample.tensorPowModule V A.divisorialSheaf (m : ℤ) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  induction m with
  | zero =>
    exact eqToIso (by rw [zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso ≪≫
      (Stacks.Ample.tensorPowModuleZeroIso V A.divisorialSheaf).symm
  | succ n ih =>
    exact eqToIso (by rw [succ_nsmul]) ≪≫
      ((hA.nsmul n).divisorialSheafTensorIso hA).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso ih).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso V A.divisorialSheaf).symm ≪≫
      Stacks.Ample.tensorPowModuleAddIso V A.divisorialSheaf (n : ℤ) 1 ≪≫
      eqToIso (by push_cast; rfl)

/-- **Sections of multiples of an ample divisor vanishing on a closed set.** If `A` is an ample
Cartier divisor on a Noetherian normal integral scheme `Y` and `W ⊆ Y` is a closed set missing
the generic point, there are `n ≥ 1` and `g ∈ K(Y)^×` with `div g + nA ≥ 0` and
`W ⊆ Supp (div g + nA)`. -/
private theorem exists_nonneg_principalDivisor_add_supp_superset {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {A : Divisor Y} (hAc : A.IsCartier)
    (hA : A.IsAmple hAc) {W : Set Y} (hW : IsClosed W) (hη : genericPoint Y ∉ W) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ g : (RationalFunctions Y)ˣ,
      0 ≤ principalDivisor g + (n : ℤ) • A ∧
        W ⊆ (DivisorWithCoeffs.supp (principalDivisor g + (n : ℤ) • A) : Set Y) := by
  haveI := hAc.isInvertibleModule_divisorialSheaf
  obtain ⟨n, hn, s, -, hηs, hsW⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite _ hA
      (Set.finite_singleton (genericPoint Y)) ⟨Wᶜ, hW.isOpen_compl⟩
      (Set.singleton_subset_iff.2 hη)
  rw [Stacks.AmpleTheory.coe_powNonvanishingOpen] at hηs hsW
  set e := divisorialSheafNsmulIso hAc n
  set t := (e.symm.hom.val.app (Opposite.op ⊤)) s with ht
  have hts := MMP.Fourfold.nonvanishingLocus_app_top_eq_of_iso e.symm s
  rw [← ht] at hts
  let σ : (n • A).divisorialSubmodule ⊤ := t
  have hσ : σ ≠ 0 := fun h0 => by
    have hη' : genericPoint Y ∈ Stacks.Ample.nonvanishingLocus (n • A).divisorialSheaf t := by
      rw [hts]
      exact hηs rfl
    rw [show t = (0 : ↑((n • A).divisorialSheaf.presheaf.obj (Opposite.op ⊤))) from h0,
      Stacks.Ample.nonvanishingLocus_zero] at hη'
    exact hη'
  set g := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  have hE0 := Divisor.zeroDivisor_nonneg (n • A) σ hσ
  rw [Divisor.zeroDivisor_eq] at hE0
  set E := principalDivisor g + n • A with hE
  have hEc : E.IsCartier := (Divisor.isCartier_principalDivisor g).add (hAc.nsmul n)
  have hcoeff : ∀ P : MMP.Mori.PrimeDivisor Y,
      (n • A).coeff P = E.coeff P + P.ord g⁻¹ := fun P => by
    rw [hE, DivisorWithCoeffs.coeff_add, coeff_principalDivisor, PrimeDivisor.ord_inv]
    ring
  have hone : (Divisor.divisorialSheafMulIso g⁻¹ hcoeff).hom.val.app (Opposite.op ⊤) t =
      MMP.Threefold.Mori.oneSection hE0 := by
    apply Subtype.ext
    funext Z
    refine Eq.trans ?_
      (congrFun (Divisor.coe_structureSheafToDivisorialSheaf_app hE0 ⊤ (1 : Γ(Y, ⊤))) Z).symm
    change ((g⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1 * σ.1 Z = _
    have hgZ : ((g : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1 = σ.1 Z := rfl
    rw [← hgZ, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply]
    exact (map_one (Y.presheaf.germ ⊤ (componentGenericPoint Y Z.1) trivial).hom).symm
  have hnv := MMP.Fourfold.nonvanishingLocus_app_top_eq_of_iso
    (Divisor.divisorialSheafMulIso g⁻¹ hcoeff) t
  rw [hone, MMP.Threefold.Mori.nonvanishingLocus_oneSection hE0 hEc, hts] at hnv
  refine ⟨n, hn, g, by rwa [natCast_zsmul], ?_⟩
  intro x hx
  rw [natCast_zsmul]
  by_contra hxE
  have hx' : x ∈ (DivisorWithCoeffs.supp E : Set Y)ᶜ := hxE
  rw [hnv] at hx'
  exact hsW hx' hx

/-- **The pull-back of an effective Cartier divisor is effective, and positive over its
support.** If `E ≥ 0` is Cartier on `Y` and `F = f^*E`, then `F ≥ 0`, and `F` has coefficient
`≥ 1` along every prime divisor `P` of `X` with `f(η_P) ∈ Supp E`. -/
private theorem coeff_nonneg_and_one_le_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {E : Divisor Y} (hE0 : 0 ≤ E)
    (hEc : E.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ E.supp}
    {F : Divisor X} (hF : E.IsPullback f hB F) (P : MMP.Mori.PrimeDivisor X) :
    0 ≤ F.coeff P ∧ (f P.genericPoint ∈ E.supp → 1 ≤ F.coeff P) := by
  obtain ⟨U, hU, φ, hφ⟩ := hEc (f P.genericPoint)
  have hPU : (P.support ∩ f ⁻¹ᵁ U).Nonempty := (P.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp hU
  rw [hF U φ hφ P hPU]
  have hWc := mem_pointComponent (f P.genericPoint)
  obtain ⟨ϖ, hϖ⟩ := exists_stalk_eq_of_forall_zero_le_ord hWc φ fun E' hE' => by
    rw [← hφ E' ⟨_, hE', hU⟩]
    exact hE0 E'
  have h1 := MMP.Fourfold.pullbackComponent_val_eq_stalkMap f hB hφ hWc ϖ hϖ.symm
    P.genericPoint_mem_component (P.map_componentGenericPoint_mem f hPU)
  by_cases hm : ϖ ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (f P.genericPoint))
  · have := MMP.Fourfold.PrimeDivisor.ordUnit_pos_of_mem_maximalIdeal P
      (map_nonunit (f.stalkMap P.genericPoint).hom ϖ hm) h1.symm
    exact ⟨this.le, fun _ => this⟩
  · have hu : IsUnit ϖ := IsLocalRing.notMem_maximalIdeal.mp hm
    have h0 := P.ordUnit_eq_zero_of_isUnit (hu.map (f.stalkMap P.genericPoint).hom) h1.symm
    refine ⟨h0.ge, fun hy => ?_⟩
    exfalso
    obtain ⟨E', hE'ne, hyE'⟩ := DivisorWithCoeffs.mem_supp_iff.1 hy
    apply hE'ne
    rw [hφ E' ⟨_, hyE', hU⟩]
    have hspec : E'.genericPoint ⤳ f P.genericPoint := specializes_iff_mem_closure.mpr (by
      rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hyE')
    have hcomp : f P.genericPoint ∈ E'.component.1 := E'.support_subset_component hyE'
    have hW : pointComponent (f P.genericPoint) = E'.component :=
      eq_of_mem_irreducibleComponents hWc hcomp
    refine E'.ord_eq_zero_of_isUnit (hu.map (Y.presheaf.stalkSpecializes hspec).hom) ?_
    rw [E'.toComponent_stalkSpecializes hspec hcomp]
    have key : ∀ (W : irreducibleComponents Y) (hW1 : f P.genericPoint ∈ W.1),
        W = E'.component → (stalkToRationalFunctions Y hW1).hom ϖ = (φ : RationalFunctions Y) W →
          (stalkToRationalFunctions Y hcomp).hom ϖ = (φ : RationalFunctions Y) E'.component := by
      rintro W hW1 rfl h
      exact h
    exact key _ hWc hW hϖ

/-- The components of `B^{=1}` are the prime divisors with coefficient one in `B`. -/
private theorem mem_support_coeffOnePart_iff {X : Scheme.{u}} {B : QDivisor X}
    {P : MMP.Mori.PrimeDivisor X} : P ∈ (coeffOnePart B).support ↔ B.coeff P = 1 := by
  rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, coeff_coeffOnePart]
  split_ifs with h <;> simp [h]

/-- If every component of `T = B^{=1}` has image a proper subset of `Y` under a proper `f`, the
image `f(T)` lies in a closed set missing the generic point of `Y`. -/
private theorem exists_isClosed_genericPoint_notMem_image_coeffOnePart {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y]
    {B : QDivisor X} {f : X ⟶ Y} [IsProper f]
    (hT : ∀ P : MMP.Mori.PrimeDivisor X, B.coeff P = 1 → f '' P.support ≠ Set.univ) :
    ∃ W : Set Y, IsClosed W ∧ genericPoint Y ∉ W ∧
      ∀ P : MMP.Mori.PrimeDivisor X, B.coeff P = 1 → f P.genericPoint ∈ W := by
  refine ⟨⋃ P ∈ (coeffOnePart B).support, f '' P.support,
    (coeffOnePart B).support.finite_toSet.isClosed_biUnion fun P _ =>
      f.isClosedMap _ P.idealSheaf.support.isClosed, fun h => ?_, fun P hB1 => ?_⟩
  · obtain ⟨P, hP, hPη⟩ := Set.mem_iUnion₂.mp h
    refine hT P (mem_support_coeffOnePart_iff.mp hP) (Set.eq_univ_of_univ_subset ?_)
    rw [← (genericPoint_spec Y).def]
    exact closure_minimal (Set.singleton_subset_iff.2 hPη)
      (f.isClosedMap _ P.idealSheaf.support.isClosed)
  · refine Set.mem_iUnion₂.mpr ⟨P, mem_support_coeffOnePart_iff.mpr hB1, P.genericPoint, ?_, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- The coefficient bound making `g^c` a section of `n c A' - a T`, from the effectivity of
`div g + n A'` and its positivity along `T`, for `a ≤ c`. -/
private theorem exp_neg_coeff_le_valuation_pow {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {B : QDivisor X} {A' : Divisor X}
    {g : (RationalFunctions X)ˣ} {n c : ℕ} {a : ℤ} (hc : a ≤ c) (P : MMP.Mori.PrimeDivisor X)
    (h0 : 0 ≤ (principalDivisor g + (n : ℤ) • A').coeff P)
    (h1 : B.coeff P = 1 → 1 ≤ (principalDivisor g + (n : ℤ) • A').coeff P) :
    WithZero.exp (-((((n * c : ℕ) : ℤ) • A' - a • coeffOnePart B).coeff P)) ≤
      P.valuation (((g ^ c : (RationalFunctions X)ˣ) : RationalFunctions X) P.component) := by
  rw [P.valuation_component, WithZero.exp_le_exp, PrimeDivisor.ord_pow]
  have hFc : (principalDivisor g + (n : ℤ) • A').coeff P = P.ord g + n * A'.coeff P := by
    rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor, DivisorWithCoeffs.coeff_smul,
      smul_eq_mul]
  have hDc : (((n * c : ℕ) : ℤ) • A' - a • coeffOnePart B).coeff P =
      (n * c : ℕ) * A'.coeff P - a * (coeffOnePart B).coeff P := by
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  rw [hFc] at h0 h1
  rw [hDc, coeff_coeffOnePart, nsmul_eq_mul]
  push_cast
  split_ifs with hB1
  · nlinarith [mul_nonneg (Int.natCast_nonneg c) (sub_nonneg.mpr (h1 hB1))]
  · nlinarith [mul_nonneg (Int.natCast_nonneg c) h0]

/-- Ample sections of `N A` vanishing on `f(T)`, pulled back along `f`: sections of
`N f^*A - aT`. -/
private theorem exists_ne_zero_mem_divisorialSubmodule_pullback_sub {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {B : QDivisor X}
    {f : X ⟶ Y} (hf : IsContraction sX sY f)
    {A : Divisor Y} (hAc : A.IsCartier) (hA : A.IsAmple hAc)
    (hAf : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ A.supp)
    (hT : ∀ P : MMP.Mori.PrimeDivisor X, B.coeff P = 1 → f '' P.support ≠ Set.univ)
    {a : ℤ} (ha : 1 ≤ a) {q : ℕ} (hq : 0 < q) (M₀ : ℕ) :
    ∃ N : ℕ, M₀ ≤ N ∧ q ∣ N ∧
      ((N : ℤ) • A.pullback hAc hAf - a • coeffOnePart B).divisorialSubmodule ⊤ ≠ ⊥ := by
  classical
  have : IsIntegral Y := hf.isNormalVariety_target.1.toIsIntegral
  have : IsProper f :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hf.isProjectiveMorphism).2
  have hgen : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) = genericPoint Y :=
    fun Z => by
      have hZ : Z.1 ∈ ({Set.univ} : Set (Set X)) :=
        irreducibleComponents_eq_singleton (X := X) ▸ Z.2
      have hgp := (isGenericPoint_componentGenericPoint X Z).image f.continuous
      rw [Set.mem_singleton_iff.mp hZ, Set.image_univ, hf.surjective.range_eq, closure_univ] at hgp
      exact hgp.eq (genericPoint_spec Y)
  have hη : ∀ (D : Divisor Y) (Z : irreducibleComponents X),
      f (componentGenericPoint X Z) ∉ D.supp := fun D Z => by
    rw [hgen]
    exact MMP.Fourfold.genericPoint_notMem_supp D
  obtain ⟨W, hWc, hηW, hTW⟩ := exists_isClosed_genericPoint_notMem_image_coeffOnePart hT
  obtain ⟨n, hn, g, hE0, hWE⟩ := exists_nonneg_principalDivisor_add_supp_superset hAc hA hWc hηW
  set E := principalDivisor g + (n : ℤ) • A
  have hEc : E.IsCartier := (Divisor.isCartier_principalDivisor g).add (hAc.zsmul n)
  set g' := pullbackRationalFunction f g (hη _)
  set A' := A.pullback hAc hAf
  have hF : E.IsPullback f (hη E) (principalDivisor g' + (n : ℤ) • A') :=
    Divisor.IsPullback.add (Divisor.isCartier_principalDivisor g) (hAc.zsmul n) (hη E)
      (Divisor.isPullback_principalDivisor g (hη _))
      ((Divisor.isPullback_pullback hAc hAf).zsmul hAc n (hη _))
  have hFP := fun P => coeff_nonneg_and_one_le_of_isPullback hE0 hEc hF P
  set c : ℕ := a.toNat * q * (M₀ + 1)
  have hc : a ≤ (c : ℤ) := by
    have : a.toNat ≤ c :=
      (Nat.le_mul_of_pos_right _ hq).trans (Nat.le_mul_of_pos_right _ M₀.succ_pos)
    omega
  refine ⟨n * c, ?_, ?_, ?_⟩
  · have h1 : M₀ + 1 ≤ c := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hq)
    nlinarith
  · exact Dvd.dvd.mul_left (Dvd.intro_left _ rfl |>.mul_right _) n
  · let σ : (((n * c : ℕ) : ℤ) • A' - a • coeffOnePart B).divisorialSubmodule ⊤ :=
      ⟨fun Z => (((g' ^ c : (RationalFunctions X)ˣ)) : RationalFunctions X) Z.1, fun P _ =>
        Or.inr <| exp_neg_coeff_le_valuation_pow hc P (hFP P).1 fun hB1 =>
          (hFP P).2 (hWE (hTW P hB1))⟩
    exact (Submodule.ne_bot_iff _).2 ⟨σ.1, σ.2, fun h0 =>
      ((g' ^ c).isUnit.map (Pi.evalMonoidHom _ (pointComponent (Classical.arbitrary X)))).ne_zero
        (congrFun h0 ⟨pointComponent (Classical.arbitrary X), trivial⟩)⟩

/-- On a smooth integral `X` of dimension `d` and for a basis `b` of `Ω^d_{k(X)/k}`, there is an
integer `e` (the order of `b` along `Γ`) with `ord_Γ(τ) = v_Γ(τ / b^{⊗m}) + m e` for every
nonzero rational `m`-canonical form `τ`. -/
private theorem exists_ordForm_eq_ord_repr_add_mul {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of k)} [Smooth sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) (Γ : MMP.Mori.PrimeDivisor X)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k])) :
    ∃ e : ℤ, ∀ (m : ℤ) (τ : RationalPluriForms sX d m), τ ≠ 0 →
      Γ.ordForm τ = X.ord ((ZTensorPower.basis b m).repr τ ()) Γ.genericPoint + m * e := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  exact exists_ordAt_eq_add_mul Γ.ord_mul_of_ne_zero (fun _ ha => Γ.ord_algebraMap_of_isUnit ha)
    (MMP.Threefold.Resolution.exists_topForms_generator_stalk sX hd Γ.genericPoint) b

/-- A nonzero section of `𝒪_X(N F + G)` with `F = r(K + B)` gives a nonzero rational
`N r`-canonical form in `H⁰(X, N r K + ⌊N r B⌋ + G)`: multiply it by `ω^{⊗N r}`, where
`div ω = K`. -/
private theorem pluricanonicalSections_ne_bot_of_divisorialSubmodule_ne_bot {k : Type u}
    [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {r : ℕ} (hr : 0 < r) {F : Divisor X}
    (hF : Divisor.toQDivisor F = (r : ℚ) • (Divisor.toQDivisor K + B)) (N : ℕ) (G : Divisor X)
    (hG : ((N : ℤ) • F + G).divisorialSubmodule ⊤ ≠ ⊥) :
    pluricanonicalSections sX n (N * r)
      (DivisorWithCoeffs.roundDown (((N * r : ℕ) : ℤ) • B) + G) ⊤ ≠ ⊥ := by
  classical
  have hsmooth : IsSmoothScheme sX := hXB.isSmoothScheme
  have hX : IsNormalVariety k sX := ⟨hXB.isProjectiveVariety.toIsVariety, inferInstance⟩
  have hsm : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.genericPoint ∈ smoothLocus sX := fun Γ => by
    rw [hsmooth]
    trivial
  have : Smooth sX := MMP.Threefold.Resolution.smooth_of_isSmoothScheme hsmooth
  have hn := Divisor.IsCanonicalDivisor.topologicalKrullDim_eq hK
  obtain ⟨ω, hω0, hω⟩ :=
    MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus hX hsm hK
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hG
  let σ : ((N : ℤ) • F + G).divisorialSubmodule ⊤ := ⟨x, hx⟩
  have hσ : σ ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨g, hg0, hg⟩ := MMP.Positivity.exists_ord_eq_of_units
    (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  let := functionFieldAlgebra sX
  let b : Module.Basis Unit X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]) :=
    Module.basisUnique Unit (MMP.Positivity.finrank_topForms_functionField_eq_one hX hsm hn)
  set c := (ZTensorPower.basis b 1).repr ω () with hc
  have hc0 : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  set m : ℕ := N * r
  let τ : RationalPluriForms sX n m := (g * c ^ (m : ℤ)) • ZTensorPower.basis b m ()
  have hτ0 : τ ≠ 0 :=
    smul_ne_zero (mul_ne_zero hg0 (zpow_ne_zero _ hc0)) ((ZTensorPower.basis b m).ne_zero ())
  refine (AddSubgroup.ne_bot_iff_exists_ne_zero).2 ⟨⟨τ, ?_⟩, fun h => hτ0 (congrArg Subtype.val h)⟩
  rw [mem_pluricanonicalSections_of_ne_bot (by simp)]
  intro Γ _ _
  obtain ⟨e, he⟩ := exists_ordForm_eq_ord_repr_add_mul hn Γ b
  have e1 := he 1 ω hω0
  rw [← hc, hω Γ] at e1
  have hrepr : (ZTensorPower.basis b m).repr τ () = g * c ^ (m : ℤ) := by simp [τ]
  have e2 := he m τ hτ0
  rw [hrepr, Scheme.ord_mul hg0 (zpow_ne_zero _ hc0), ord_zpow _ hc0] at e2
  have hσΓ := Divisor.zeroDivisor_nonneg _ σ hσ Γ
  rw [Divisor.zeroDivisor_eq] at hσΓ
  change 0 ≤ (MMP.Mori.principalDivisor _).coeff Γ + ((N : ℤ) • F + G).coeff Γ at hσΓ
  rw [coeff_principalDivisor, hg Γ] at hσΓ
  have hFΓ : (F.coeff Γ : ℚ) = r * (K.coeff Γ + B.coeff Γ) := by
    simpa [mul_add] using congrArg (fun D : QDivisor X => D.coeff Γ) hF
  have hB : (((m : ℤ) • B).coeff Γ) = ((N * F.coeff Γ - m * K.coeff Γ : ℤ) : ℚ) := by
    simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, m]
    push_cast
    rw [hFΓ]
    ring
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_roundDown, hB,
    Int.floor_intCast, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hσΓ ⊢
  have hmK : (m : ℤ) * K.coeff Γ = m * X.ord c Γ.genericPoint + m * e := by
    rw [e1]
    ring
  linarith

/-- **Nonzero pluriforms vanishing along a vertical floor.** Let `X` be a smooth projective
variety of dimension `n` over `k`, `B` an snc `ℚ`-divisor with coefficients at most one,
`K` a canonical divisor with `K + B` semiample, and `f : X ⟶ Y` a contraction with
`r(K + B) = f^*A` for some `r > 0` and some ample Cartier divisor `A` on `Y`. If every prime
divisor of `T = B^{=1}` (`MMP.Fourfold.coeffOnePart`) has image a proper subset of `Y`, then for
every `a ≥ 1`, every `q > 0` and every bound `M₀` there is `m ≥ M₀` divisible by `q` such that
`H⁰(X, m(K + B) - aT)` is nonzero. -/
@[mmp "lem_fourfold_vertical_floor_nonzero_pluriform"]
public theorem exists_pluricanonicalSections_sub_coeffOnePart_ne_bot {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {n : ℕ} {B : QDivisor X}
    (hXB : IsSNCSubboundaryPair sX B) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (hD : Flips.IsEventuallyFree k sX (Divisor.toQDivisor K + B))
    {f : X ⟶ Y} (hf : IsContraction sX sY f)
    {r : ℕ} (hr : 0 < r) {A : Divisor Y} (hAc : A.IsCartier) (hA : A.IsAmple hAc)
    (hrD : ∃ hAf : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ A.supp,
      Divisor.toQDivisor (A.pullback hAc hAf) = (r : ℚ) • (Divisor.toQDivisor K + B))
    (hT : ∀ P : Mori.PrimeDivisor X, B.coeff P = 1 → f '' P.support ≠ Set.univ)
    {a : ℤ} (ha : 1 ≤ a) {q : ℕ} (hq : 0 < q) (M₀ : ℕ) :
    ∃ m : ℕ, M₀ ≤ m ∧ q ∣ m ∧
      pluricanonicalSections sX n m
        (DivisorWithCoeffs.roundDown ((m : ℤ) • B) - a • coeffOnePart B) ⊤ ≠ ⊥ := by
  obtain ⟨hAf, hF⟩ := hrD
  obtain ⟨N, hN, hqN, hsec⟩ :=
    exists_ne_zero_mem_divisorialSubmodule_pullback_sub hf hAc hA hAf hT ha hq M₀
  refine ⟨N * r, hN.trans (Nat.le_mul_of_pos_right N hr),
    dvd_mul_of_dvd_left hqN r, ?_⟩
  rw [sub_eq_add_neg]
  exact pluricanonicalSections_ne_bot_of_divisorialSubmodule_ne_bot hXB hK hr hF N _
    (by rwa [← sub_eq_add_neg])

end MMP.Fourfold
