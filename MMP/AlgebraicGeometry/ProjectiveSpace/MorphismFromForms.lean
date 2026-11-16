module

public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj

/-!
# Morphisms to projective space from forms without common zero

Let `k` be a field, `R` a `k`-algebra and `c : ι → R` a family of elements generating the unit
ideal.  The family `(c_b)_b` is the family of homogeneous coordinates of an `R`-valued point of
`ℙ^ι_k`: this file builds the corresponding morphism `Spec R ⟶ ℙ^ι_k` over `Spec k`, and for a
scheme `U` over `k` the morphism `U ⟶ ℙ^ι_k` attached to `c : ι → Γ(U, ⊤)`.

The morphism `Spec R ⟶ ℙ^ι_k` is the composite of `Spec R ⟶ Spec R[t]_{(t)} ⟶ Proj R[t]`
(the chart `D₊(t)`, whose ring of functions is evaluation `t = 1`) and `Proj` of the graded
homomorphism `k[X_b : b ∈ ι] ⟶ R[t]`, `X_b ↦ c_b t`.  The value at a point `p` of `Spec R` is
computed in `MMP.Chow.mem_asHomogeneousIdeal_formsToProjSpace_iff`: a homogeneous polynomial `f`
lies in the homogeneous prime ideal of the image of `p` iff `f((c_b)_b) ∈ p`.

## Main definitions

* `MMP.Chow.formsToProjSpace`: the morphism `Spec R ⟶ ℙ^ι_k`.
* `MMP.Chow.sectionsToProjSpace`: the morphism `U ⟶ ℙ^ι_k` of a scheme with coefficients in
  `Γ(U, ⊤)`.
* `MMP.Chow.structureAlgebra`: the `k`-algebra structure of `Γ(U, ⊤)` from `U ⟶ Spec k`.

## Main results

* `MMP.Chow.formsToProjSpace_toSpec`, `MMP.Chow.sectionsToProjSpace_toSpec`: the morphisms lie
  over `Spec k`.
* `MMP.Chow.mem_asHomogeneousIdeal_formsToProjSpace_iff`,
  `MMP.Chow.mem_asHomogeneousIdeal_formsToProjSpace_iff_residueField`,
  `MMP.Chow.mem_asHomogeneousIdeal_sectionsToProjSpace_iff`: the image of a point, in terms of
  the evaluation of the coefficients in the residue field.
* `MMP.Chow.linear_mem_asHomogeneousIdeal_formsToProjSpace`,
  `MMP.Chow.linear_mem_asHomogeneousIdeal_sectionsToProjSpace`: if the values of the
  coefficients at a point are a multiple of a vector `a` with entries in `k`, then
  `a_{b'} X_b - a_b X_{b'}` lies in the homogeneous prime ideal of the image.
* `MMP.Chow.comp_formsToProjSpace`, `MMP.Chow.comp_sectionsToProjSpace`: compatibility with
  pulling back the coefficients along a `k`-algebra homomorphism, resp. a morphism of schemes.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization ProjectiveSpectrum
open Stacks.AlgebraicGeometry.PolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MMP.Chow

/-! ### Points of the open immersion `Proj.awayι` -/

section Away

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)

/-- A fraction `num / f ^ n` lies in the prime `q` of `Spec A⁰_f` iff its numerator lies in the
homogeneous prime ideal of the image of `q` under `Proj.awayι`. -/
theorem mk_mem_iff_num_mem_awayι (q : Spec (.of (Away 𝒜 f)))
    (z : NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ q.asIdeal ↔
      z.num.1 ∈ ((AlgebraicGeometry.Proj.awayι 𝒜 f f_deg hm).base q).asHomogeneousIdeal := by
  set x := (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv.base q with hx
  have h1 : (AlgebraicGeometry.Proj.basicOpenToSpec 𝒜 f).base x = q := by
    have h : (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫
        (AlgebraicGeometry.Proj.basicOpenToSpec 𝒜 f) = 𝟙 _ := by
      rw [← AlgebraicGeometry.Proj.basicOpenIsoSpec_hom 𝒜 f f_deg hm]
      exact (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv_hom_id
    exact congrArg (fun g => (g.base : _ → _) q) h
  have h2 := ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 x z
  have h3 : (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base x =
      (AlgebraicGeometry.Proj.basicOpenToSpec 𝒜 f).base x := rfl
  rwa [h3, h1] at h2

section Map

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
  [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)

/-- `HomogeneousLocalization.Away.map` followed by the identification `f s = s'`. -/
def awayMapOfEq (s : A) {s' : B} (e : f s = s') : Away 𝒜 s →+* Away ℬ s' := by
  subst e; exact Away.map f s

/-- `awayMapOfEq f s e` sends `x / s ^ n` to `f x / s' ^ n`. -/
theorem awayMapOfEq_mk (s : A) {s' : B} (e : f s = s') {d : ℕ} (hs : s ∈ 𝒜 d) (hs' : s' ∈ ℬ d)
    (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) (hx' : f x ∈ ℬ (n • d)) :
    awayMapOfEq f s e (Away.mk 𝒜 hs n x hx) = Away.mk ℬ hs' n (f x) hx' := by
  subst e; exact Away.map_mk f s hs n x hx

/-- `Proj.awayι` for `s'` followed by `Proj.map f` equals `Spec` of `awayMapOfEq f s e` followed by
`Proj.awayι` for `s`, where `f s = s'`. -/
theorem awayι_comp_map_of_eq (hf : HomogeneousIdeal.irrelevant ℬ ≤
      (HomogeneousIdeal.irrelevant 𝒜).map f) {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i)
    {s' : B} (e : f s = s') (hs' : s' ∈ ℬ i) :
    AlgebraicGeometry.Proj.awayι ℬ s' hs' hi ≫ AlgebraicGeometry.Proj.map f hf =
      Spec.map (CommRingCat.ofHom (awayMapOfEq f s e)) ≫
        AlgebraicGeometry.Proj.awayι 𝒜 s hs hi := by
  subst e; exact AlgebraicGeometry.Proj.awayι_comp_map f hf hi s hs

/-- `Proj.map` of equal graded homomorphisms are equal, whatever the proofs of the
irrelevant-ideal hypothesis. -/
theorem proj_map_congr {f₁ f₂ : 𝒜 →+*ᵍ ℬ} (h : f₁ = f₂)
    (h₁ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f₁)
    (h₂ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f₂) :
    AlgebraicGeometry.Proj.map f₁ h₁ = AlgebraicGeometry.Proj.map f₂ h₂ := by
  subst h; rfl

end Map

end Away

/-! ### The morphism `Spec R ⟶ ℙ^ι_k` -/

section Forms

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {ι : Type u}

open MvPolynomial in
/-- The substitution `X_b ↦ c_b t` from `k[X_b : b ∈ ι]` to `R[t]`. -/
def formsAlgHom (c : ι → R) : MvPolynomial ι k →ₐ[k] MvPolynomial PUnit.{u + 1} R :=
  aeval fun b => C (c b) * X PUnit.unit

open MvPolynomial in
/-- `formsAlgHom c` sends the variable `X_b` to `c_b t`. -/
@[simp] theorem formsAlgHom_X (c : ι → R) (b : ι) :
    formsAlgHom (k := k) c (X b) = C (c b) * X PUnit.unit :=
  aeval_X _ _

open MvPolynomial in
/-- For `f` homogeneous of degree `n`, `formsAlgHom c f = f(c) t ^ n`. -/
theorem formsAlgHom_eq_of_isHomogeneous (c : ι → R) {n : ℕ} {f : MvPolynomial ι k}
    (hf : f.IsHomogeneous n) :
    formsAlgHom c f = C (aeval c f) * X PUnit.unit ^ n := by
  have h1 : formsAlgHom c f = eval₂ (algebraMap k (MvPolynomial PUnit.{u + 1} R))
      (fun b => X PUnit.unit * C (c b)) f := by
    rw [formsAlgHom, aeval_def]
    simp only [mul_comm]
  rw [h1, eval₂_mul_left_of_isHomogeneous _ _ _ hf, mul_comm]
  congr 1
  rw [aeval_def, ← coe_eval₂Hom, hom_eval₂]
  rfl

/-- The substitution `X_b ↦ c_b t`, as a homomorphism of graded rings for the gradings by total
degree. -/
def formsGradedHom (c : ι → R) :
    MvPolynomial.homogeneousSubmodule ι k →+*ᵍ
      MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R where
  toRingHom := (formsAlgHom c).toRingHom
  map_mem {i x} hx := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hx ⊢
    have h := formsAlgHom_eq_of_isHomogeneous c hx
    have h2 := (MvPolynomial.isHomogeneous_C PUnit.{u + 1} (MvPolynomial.aeval c x)).mul
      ((MvPolynomial.isHomogeneous_X R PUnit.unit).pow i)
    simp only [zero_add, one_mul] at h2
    exact h ▸ h2

/-- `formsGradedHom c` acts as `formsAlgHom c`. -/
@[simp] theorem formsGradedHom_apply (c : ι → R) (f : MvPolynomial ι k) :
    formsGradedHom c f = formsAlgHom c f := rfl

omit [Algebra k R] in
/-- The irrelevant ideal of `R[t]` is contained in the ideal generated by `t`. -/
theorem irrelevant_le_span_X_pUnit :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)).toIdeal ≤
      Ideal.span {(MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{u + 1} R)} := by
  rw [HomogeneousIdeal.irrelevant_eq_span]
  refine Ideal.span_le.mpr ?_
  intro f hf
  simp only [Set.mem_iUnion] at hf
  obtain ⟨m, hm, hf⟩ := hf
  have := (MvPolynomial.mem_ideal_span_X_image (x := f)
    (s := (Set.univ : Set PUnit.{u + 1}))).mpr ?_
  · have e : (MvPolynomial.X '' (Set.univ : Set PUnit.{u + 1}) :
        Set (MvPolynomial PUnit.{u + 1} R)) = {MvPolynomial.X PUnit.unit} := by
      ext y
      simp only [Set.image_univ, Set.mem_range, Set.mem_singleton_iff]
      exact ⟨fun ⟨⟨⟩, h⟩ => h.symm, fun h => ⟨PUnit.unit, h.symm⟩⟩
    rwa [e] at this
  · intro e he
    rw [MvPolynomial.mem_support_iff] at he
    have hw := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hf he
    by_contra hcon
    push Not at hcon
    have : e = 0 := Finsupp.ext fun i => by simpa using hcon i (Set.mem_univ i)
    subst this
    simp at hw
    omega

/-- If `c` generates the unit ideal, the irrelevant ideal of `R[t]` is contained in the image under
`formsGradedHom c` of the irrelevant ideal of `k[X_b : b ∈ ι]`. -/
theorem irrelevant_le_map_formsGradedHom (c : ι → R) (hc : Ideal.span (Set.range c) = ⊤) :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule ι k)).map
        (formsGradedHom c) := by
  intro b hb
  have hb' : b ∈ (HomogeneousIdeal.irrelevant
    (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)).toIdeal := hb
  change b ∈ (HomogeneousIdeal.map _ _).toIdeal
  rw [HomogeneousIdeal.toIdeal_map]
  refine (Ideal.span_le.mpr ?_) (irrelevant_le_span_X_pUnit hb')
  rintro _ rfl
  have h1 : (1 : R) ∈ Ideal.span (Set.range c) := hc ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp h1
  have h2 : (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{u + 1} R) =
      ∑ b ∈ r.support, MvPolynomial.C (r b) * formsGradedHom (k := k) c (MvPolynomial.X b) := by
    have e : ∑ b ∈ r.support, MvPolynomial.C (r b) * formsGradedHom (k := k) c (MvPolynomial.X b) =
        MvPolynomial.C (r.sum fun i a => a • c i) * MvPolynomial.X PUnit.unit := by
      simp only [formsGradedHom_apply, formsAlgHom, MvPolynomial.aeval_X, Finsupp.sum, map_sum,
        Finset.sum_mul, smul_eq_mul, map_mul, mul_assoc]
    rw [e, hr, map_one, one_mul]
  rw [h2]
  refine Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ ?_
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos
    (MvPolynomial.isHomogeneous_X k b))

/-- Evaluation at `t = 1` of the degree-zero part of the localisation of `R[t]` at `t`:
`a / t ^ n ↦` the coefficient of `t ^ n` in `a`. -/
def awayEval :
    Away (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R) (MvPolynomial.X PUnit.unit) →+* R :=
  MvPolynomial.constantCoeff.comp (fromAway R PUnit.unit)

/-- `awayEval` sends `a / t ^ n` to the constant coefficient of the dehomogenisation of `a`. -/
theorem awayEval_mk' (n : ℕ) (a : MvPolynomial PUnit.{u + 1} R)
    (h : a ∈ MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R (n • 1)) :
    awayEval (Away.mk (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)
      (X_mem_one R PUnit.unit) n a h) = MvPolynomial.constantCoeff (dehom R PUnit.unit a) := by
  have hfrom : fromAway R PUnit.unit
      (Away.mk (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)
        (X_mem_one R PUnit.unit) n a h) = dehom R PUnit.unit a := by
    simp only [fromAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk]
    exact awayLift_dehom_mk R PUnit.unit _ n
  rw [awayEval, RingHom.comp_apply, hfrom]

/-- `awayEval` sends `r t ^ n / t ^ n` to `r`. -/
theorem awayEval_mk (r : R) (n : ℕ) (a : MvPolynomial PUnit.{u + 1} R)
    (h : a ∈ MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R (n • 1))
    (ha : a = MvPolynomial.C r * MvPolynomial.X PUnit.unit ^ n) :
    awayEval (Away.mk (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)
      (X_mem_one R PUnit.unit) n a h) = r := by
  rw [awayEval_mk', ha]
  simp [dehom_C, dehom_X_self]

/-- `awayEval` sends the image of the constant `s` of degree zero to `s`. -/
theorem awayEval_fromZeroRingHom (s : R)
    (h : (MvPolynomial.C s : MvPolynomial PUnit.{u + 1} R) ∈
      MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R 0) :
    awayEval (fromZeroRingHom (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)
      (Submonoid.powers (MvPolynomial.X PUnit.unit)) ⟨MvPolynomial.C s, h⟩) = s := by
  have hv : (fromZeroRingHom (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)
      (Submonoid.powers (MvPolynomial.X PUnit.unit)) ⟨MvPolynomial.C s, h⟩).val =
      algebraMap (MvPolynomial PUnit.{u + 1} R)
        (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{u + 1} R))
        (MvPolynomial.C s) := by
    rw [← Localization.mk_one_eq_algebraMap]
    rfl
  have hf : fromAway R PUnit.unit (fromZeroRingHom
      (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)
      (Submonoid.powers (MvPolynomial.X PUnit.unit)) ⟨MvPolynomial.C s, h⟩) =
      dehom R PUnit.unit (MvPolynomial.C s) := by
    simp only [fromAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, hv]
    exact IsLocalization.Away.lift_eq _ _ _
  rw [awayEval, RingHom.comp_apply, hf, dehom_C, MvPolynomial.constantCoeff_C]

/-- **The morphism `Spec R ⟶ ℙ^ι_k` attached to coefficients `c` generating the unit ideal.**
It is the composite of `Spec R ⟶ D₊(t) ⊆ Proj R[t]` and `Proj` of the graded homomorphism
`k[X_b] ⟶ R[t]`, `X_b ↦ c_b t`. -/
def formsToProjSpace (c : ι → R) (hc : Ideal.span (Set.range c) = ⊤) :
    Spec (.of R) ⟶ Intersection.ProjSpace k ι :=
  Spec.map (CommRingCat.ofHom awayEval) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R) (MvPolynomial.X PUnit.unit)
      (X_mem_one R PUnit.unit) Nat.one_pos ≫
    Proj.map (formsGradedHom c) (irrelevant_le_map_formsGradedHom c hc)

/-- `formsToProjSpace c hc` lies over `Spec k`: composed with the structure morphism of `ℙ^ι_k` it
is `Spec` of `algebraMap k R`. -/
theorem formsToProjSpace_toSpec (c : ι → R) (hc : Ideal.span (Set.range c) = ⊤) :
    formsToProjSpace c hc ≫ Intersection.ProjSpace.toSpec k ι =
      Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
  rw [formsToProjSpace, Intersection.ProjSpace.toSpec]
  simp only [Category.assoc, Proj.map_toSpecZero_assoc, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp]
  congr 1
  ext x
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  have e : (formsGradedHom c).gradedZeroRingHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule ι k 0) x) =
      ⟨MvPolynomial.C (algebraMap k R x), MvPolynomial.isHomogeneous_C _ _⟩ :=
    Subtype.ext (by
      refine ((formsAlgHom (k := k) c).commutes x).trans ?_
      simp [MvPolynomial.algebraMap_eq])
  rw [e]
  exact awayEval_fromZeroRingHom _ _

/-- **The value of `formsToProjSpace` at a point.**  A homogeneous polynomial `f` lies in the
homogeneous prime ideal of the image of the point `p` iff `f((c_b)_b) ∈ p`. -/
theorem mem_asHomogeneousIdeal_formsToProjSpace_iff (c : ι → R)
    (hc : Ideal.span (Set.range c) = ⊤) (p : Spec (.of R)) {n : ℕ} {f : MvPolynomial ι k}
    (hf : f.IsHomogeneous n) :
    f ∈ ((formsToProjSpace (k := k) c hc).base p).asHomogeneousIdeal ↔
      MvPolynomial.aeval (R := k) c f ∈ p.asIdeal := by
  have h : formsAlgHom c f ∈
      MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R (n • 1) := by
    rw [smul_eq_mul, mul_one]
    exact (formsGradedHom c).map_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2 hf)
  let z : NumDenSameDeg (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)
      (Submonoid.powers (MvPolynomial.X PUnit.unit)) :=
    ⟨n • 1, ⟨formsAlgHom c f, h⟩,
      ⟨MvPolynomial.X PUnit.unit ^ n, SetLike.pow_mem_graded n (X_mem_one R PUnit.unit)⟩,
      ⟨n, rfl⟩⟩
  have h1 := mk_mem_iff_num_mem_awayι (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)
    (X_mem_one R PUnit.unit) Nat.one_pos
    ((Spec.map (CommRingCat.ofHom awayEval)).base p) z
  have h2 : HomogeneousLocalization.mk z =
      Away.mk (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R) (X_mem_one R PUnit.unit) n
        (formsAlgHom c f) h := rfl
  have h3 := awayEval_mk (MvPolynomial.aeval (R := k) c f) n (formsAlgHom c f) h
    (formsAlgHom_eq_of_isHomogeneous c hf)
  have h4 : f ∈ ((formsToProjSpace (k := k) c hc).base p).asHomogeneousIdeal ↔
      formsAlgHom c f ∈ ((Proj.awayι (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)
        (MvPolynomial.X PUnit.unit) (X_mem_one R PUnit.unit) Nat.one_pos).base
        ((Spec.map (CommRingCat.ofHom awayEval)).base p)).asHomogeneousIdeal := Iff.rfl
  refine h4.trans (h1.symm.trans ?_)
  rw [h2]
  have h5 : Away.mk (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R) (X_mem_one R PUnit.unit) n
        (formsAlgHom c f) h ∈ ((Spec.map (CommRingCat.ofHom awayEval)).base p).asIdeal ↔
      awayEval (Away.mk (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)
        (X_mem_one R PUnit.unit) n (formsAlgHom c f) h) ∈ p.asIdeal := Iff.rfl
  rw [h5, h3]

/-! #### Compatibility with ring homomorphisms -/

section BaseChange

variable {R' : Type u} [CommRing R'] [Algebra k R']

/-- The coefficientwise map `R[t] ⟶ R'[t]` along a ring homomorphism, as a graded homomorphism. -/
def baseChangeGradedHom (g : R →+* R') :
    MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R →+*ᵍ
      MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R' where
  toRingHom := MvPolynomial.map g
  map_mem {i x} hx := (MvPolynomial.mem_homogeneousSubmodule _ _).2
    (((MvPolynomial.mem_homogeneousSubmodule _ _).1 hx).map g)

/-- `baseChangeGradedHom g` acts as `MvPolynomial.map g`. -/
@[simp] theorem baseChangeGradedHom_apply (g : R →+* R') (p : MvPolynomial PUnit.{u + 1} R) :
    baseChangeGradedHom g p = MvPolynomial.map g p := rfl

/-- Composing `formsGradedHom c` with the coefficientwise map along `g` gives
`formsGradedHom (g ∘ c)`. -/
theorem baseChangeGradedHom_comp_formsGradedHom (g : R →ₐ[k] R') (c : ι → R) :
    (baseChangeGradedHom g.toRingHom).comp (formsGradedHom (k := k) c) =
      formsGradedHom (g ∘ c) := by
  refine GradedRingHom.ext fun f => ?_
  have : (MvPolynomial.mapAlgHom g).comp (formsAlgHom (k := k) c) = formsAlgHom (g ∘ c) :=
    MvPolynomial.algHom_ext fun b => by simp [formsAlgHom]
  exact DFunLike.congr_fun this f

/-- The irrelevant ideal of `R'[t]` is contained in the image under `baseChangeGradedHom g` of the
irrelevant ideal of `R[t]`. -/
theorem irrelevant_le_map_baseChangeGradedHom (g : R →+* R') :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R') ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)).map
        (baseChangeGradedHom g) := by
  intro b hb
  have hb' : b ∈ (HomogeneousIdeal.irrelevant
    (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R')).toIdeal := hb
  change b ∈ (HomogeneousIdeal.map _ _).toIdeal
  rw [HomogeneousIdeal.toIdeal_map]
  refine (Ideal.span_le.mpr ?_) (irrelevant_le_span_X_pUnit hb')
  rintro _ rfl
  have := Ideal.mem_map_of_mem (baseChangeGradedHom g)
    (HomogeneousIdeal.mem_irrelevant_of_mem (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R)
      Nat.one_pos (MvPolynomial.isHomogeneous_X R PUnit.unit))
  simpa using this

/-- `awayEval` commutes with the map of localisations induced by `baseChangeGradedHom g`:
evaluating after base change is `g` applied to the evaluation. -/
theorem awayEval_comp_baseChange (g : R →+* R') (x : Away
    (MvPolynomial.homogeneousSubmodule PUnit.{u + 1} R) (MvPolynomial.X PUnit.unit))
    (e : baseChangeGradedHom g (MvPolynomial.X PUnit.unit) = MvPolynomial.X PUnit.unit) :
    awayEval (awayMapOfEq (baseChangeGradedHom g) _ e x) = g (awayEval x) := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (X_mem_one R PUnit.unit) x
  rw [awayMapOfEq_mk _ _ e (X_mem_one R PUnit.unit) (X_mem_one R' PUnit.unit) n a ha
      (GradedRingHom.map_mem _ ha), awayEval_mk', awayEval_mk']
  have : (MvPolynomial.constantCoeff.comp (dehom R' PUnit.unit)).comp (MvPolynomial.map g) =
      g.comp (MvPolynomial.constantCoeff.comp (dehom R PUnit.unit)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [dehom_C]
    · cases i; simp [dehom_X_self]
  exact DFunLike.congr_fun this a

/-- **Naturality in the base ring.**  For a `k`-algebra homomorphism `g : R ⟶ R'`, the
composite `Spec R' ⟶ Spec R ⟶ ℙ^ι_k` is the morphism attached to the coefficients `g ∘ c`. -/
theorem comp_formsToProjSpace (g : R →ₐ[k] R') (c : ι → R) (hc : Ideal.span (Set.range c) = ⊤)
    (hc' : Ideal.span (Set.range (g ∘ c)) = ⊤) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ formsToProjSpace (k := k) c hc =
      formsToProjSpace (k := k) (g ∘ c) hc' := by
  have hτ := irrelevant_le_map_baseChangeGradedHom g.toRingHom
  have e : baseChangeGradedHom g.toRingHom (MvPolynomial.X PUnit.unit) =
      MvPolynomial.X PUnit.unit := MvPolynomial.map_X _ _
  have hcomp : AlgebraicGeometry.Proj.map (formsGradedHom (g ∘ c))
      (irrelevant_le_map_formsGradedHom (g ∘ c) hc') =
      AlgebraicGeometry.Proj.map (baseChangeGradedHom g.toRingHom) hτ ≫
        AlgebraicGeometry.Proj.map (formsGradedHom (k := k) c)
          (irrelevant_le_map_formsGradedHom c hc) := by
    rw [← AlgebraicGeometry.Proj.map_comp]
    exact proj_map_congr (baseChangeGradedHom_comp_formsGradedHom g c).symm _ _
  have hr : CommRingCat.ofHom (awayEval (R := R)) ≫ CommRingCat.ofHom g.toRingHom =
      CommRingCat.ofHom (awayMapOfEq (baseChangeGradedHom g.toRingHom) _ e) ≫
        CommRingCat.ofHom (awayEval (R := R')) := by
    ext x
    exact (awayEval_comp_baseChange g.toRingHom x e).symm
  unfold formsToProjSpace
  rw [hcomp, ← Category.assoc (AlgebraicGeometry.Proj.awayι _ _ _ _),
    awayι_comp_map_of_eq (baseChangeGradedHom g.toRingHom) hτ Nat.one_pos _
      (X_mem_one R PUnit.unit) e (X_mem_one R' PUnit.unit)]
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hr]

end BaseChange

/-- The linear form `a_{b'} X_b - a_b X_{b'}` is homogeneous of degree one. -/
theorem isHomogeneous_smul_X_sub_smul_X {k : Type*} [CommRing k] {ι : Type*} (a : ι → k)
    (b b' : ι) :
    (a b' • (MvPolynomial.X b : MvPolynomial ι k) - a b • MvPolynomial.X b').IsHomogeneous 1 := by
  simp only [MvPolynomial.smul_eq_C_mul]
  refine MvPolynomial.IsHomogeneous.sub ?_ ?_
  · simpa using (MvPolynomial.isHomogeneous_C ι (a b')).mul (MvPolynomial.isHomogeneous_X k b)
  · simpa using (MvPolynomial.isHomogeneous_C ι (a b)).mul (MvPolynomial.isHomogeneous_X k b')

/-- The point description over the residue field: a homogeneous polynomial `f` lies in the
homogeneous prime ideal of the image of `p` iff `f` vanishes at the image of the coefficients
`(c_b)_b` in the residue field `κ(p)`. -/
theorem mem_asHomogeneousIdeal_formsToProjSpace_iff_residueField (c : ι → R)
    (hc : Ideal.span (Set.range c) = ⊤) (p : PrimeSpectrum R) {n : ℕ} {f : MvPolynomial ι k}
    (hf : f.IsHomogeneous n) :
    f ∈ ((formsToProjSpace (k := k) c hc).base p).asHomogeneousIdeal ↔
      MvPolynomial.eval₂ ((algebraMap R p.asIdeal.ResidueField).comp (algebraMap k R))
        (fun b => algebraMap R p.asIdeal.ResidueField (c b)) f = 0 := by
  rw [mem_asHomogeneousIdeal_formsToProjSpace_iff c hc p hf,
    ← Ideal.algebraMap_residueField_eq_zero (I := p.asIdeal), MvPolynomial.aeval_def]
  rw [MvPolynomial.eval₂_comp_left]
  rfl

/-- **The linear relations among the coordinates of the value at a point.**  If the image of
`(c_b)_b` in the residue field `κ(p)` is a scalar multiple `l` of a vector `(a_b)_b` with
coefficients in `k`, then `a_{b'} X_b - a_b X_{b'}` lies in the homogeneous prime ideal of the
image of `p`, for all `b b'`. -/
theorem linear_mem_asHomogeneousIdeal_formsToProjSpace (c : ι → R)
    (hc : Ideal.span (Set.range c) = ⊤) (p : PrimeSpectrum R) (a : ι → k)
    (l : p.asIdeal.ResidueField)
    (hl : ∀ b, algebraMap R p.asIdeal.ResidueField (c b) =
      l * algebraMap R p.asIdeal.ResidueField (algebraMap k R (a b))) (b b' : ι) :
    a b' • (MvPolynomial.X b : MvPolynomial ι k) - a b • MvPolynomial.X b' ∈
      ((formsToProjSpace (k := k) c hc).base p).asHomogeneousIdeal := by
  rw [mem_asHomogeneousIdeal_formsToProjSpace_iff_residueField c hc p
    (isHomogeneous_smul_X_sub_smul_X a b b')]
  simp only [MvPolynomial.smul_eq_C_mul]
  rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X]
  simp only [RingHom.comp_apply, hl]
  ring

end Forms

/-! ### Schemes over `k` -/

section Sections

variable {k : Type u} [Field k] {ι : Type u} {U : Scheme.{u}}

/-- The `k`-algebra structure on `Γ(U, ⊤)` of a scheme `U` over `Spec k`. -/
abbrev structureAlgebra (sU : U ⟶ Spec (.of k)) : Algebra k Γ(U, ⊤) :=
  (CommRingCat.Hom.hom ((Scheme.ΓSpecIso (.of k)).inv ≫ sU.appTop)).toAlgebra

/-- For the `k`-algebra structure `structureAlgebra sU`, the morphism `sU` is `U ⟶ Spec Γ(U, ⊤)`
followed by `Spec` of `algebraMap k Γ(U, ⊤)`. -/
theorem eq_toSpecΓ_comp_structureAlgebra (sU : U ⟶ Spec (.of k)) :
    letI := structureAlgebra sU
    sU = U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(U, ⊤))) := by
  letI := structureAlgebra sU
  have h := Scheme.toSpecΓ_naturality sU
  rw [← SpecMap_ΓSpecIso_hom] at h
  have e : Spec.map (CommRingCat.ofHom (algebraMap k Γ(U, ⊤))) =
      Spec.map sU.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of k)).inv := by
    rw [← Spec.map_comp]; rfl
  rw [e, ← Category.assoc, ← h, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]

variable [Algebra k Γ(U, ⊤)]

/-- **The morphism `U ⟶ ℙ^ι_k` attached to sections without common zero.**  For sections
`c : ι → Γ(U, ⊤)` generating the unit ideal, it is `U ⟶ Spec Γ(U, ⊤)` followed by
`formsToProjSpace`. -/
def sectionsToProjSpace (c : ι → Γ(U, ⊤)) (hc : Ideal.span (Set.range c) = ⊤) :
    U ⟶ Intersection.ProjSpace k ι :=
  U.toSpecΓ ≫ formsToProjSpace (k := k) c hc

/-- `sectionsToProjSpace c hc` lies over `Spec k`: composed with the structure morphism of `ℙ^ι_k`
it is the structure morphism `sU` of `U`. -/
theorem sectionsToProjSpace_toSpec (sU : U ⟶ Spec (.of k))
    (hsU : sU = U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(U, ⊤))))
    (c : ι → Γ(U, ⊤)) (hc : Ideal.span (Set.range c) = ⊤) :
    sectionsToProjSpace (k := k) c hc ≫ Intersection.ProjSpace.toSpec k ι = sU := by
  rw [hsU, sectionsToProjSpace, Category.assoc, formsToProjSpace_toSpec]

/-- **Naturality in the scheme.**  For `h : U' ⟶ U` compatible with the `k`-algebra structures on
the global sections, `h ≫ sectionsToProjSpace c` is the morphism attached to the pulled back
sections `h.appTop ∘ c`. -/
theorem comp_sectionsToProjSpace {U' : Scheme.{u}} [Algebra k Γ(U', ⊤)] (h : U' ⟶ U)
    (hh : ∀ x : k, h.appTop.hom (algebraMap k Γ(U, ⊤) x) = algebraMap k Γ(U', ⊤) x)
    (c : ι → Γ(U, ⊤)) (hc : Ideal.span (Set.range c) = ⊤)
    (hc' : Ideal.span (Set.range fun b => h.appTop.hom (c b)) = ⊤) :
    h ≫ sectionsToProjSpace (k := k) c hc =
      sectionsToProjSpace (k := k) (fun b => h.appTop.hom (c b)) hc' := by
  let g : Γ(U, ⊤) →ₐ[k] Γ(U', ⊤) := { h.appTop.hom with commutes' := hh }
  rw [sectionsToProjSpace, sectionsToProjSpace, ← Category.assoc, Scheme.toSpecΓ_naturality,
    Category.assoc]
  exact congrArg (U'.toSpecΓ ≫ ·) (comp_formsToProjSpace g c hc hc')

/-- Pulling back sections along `h : U' ⟶ U` preserves the property of generating the unit
ideal. -/
theorem span_range_appTop_comp_eq_top {U' : Scheme.{u}} (h : U' ⟶ U) (c : ι → Γ(U, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) :
    Ideal.span (Set.range fun b => h.appTop.hom (c b)) = ⊤ := by
  have := congrArg (Ideal.map h.appTop.hom) hc
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this

/-- **The value of `sectionsToProjSpace` at a point `u : U`.**  A homogeneous polynomial `f` lies
in the homogeneous prime ideal of the image of `u` iff `f` vanishes at the values
`c_b(u) ∈ κ(u)` of the coefficients. -/
theorem mem_asHomogeneousIdeal_sectionsToProjSpace_iff (c : ι → Γ(U, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) (u : U) {n : ℕ} {f : MvPolynomial ι k}
    (hf : f.IsHomogeneous n) :
    f ∈ ((sectionsToProjSpace (k := k) c hc).base u).asHomogeneousIdeal ↔
      MvPolynomial.eval₂ ((U.Γevaluation u).hom.comp (algebraMap k Γ(U, ⊤)))
        (fun b => U.Γevaluation u (c b)) f = 0 := by
  have h1 := mem_asHomogeneousIdeal_formsToProjSpace_iff (k := k) c hc (U.toSpecΓ.base u) hf
  change f ∈ ((formsToProjSpace (k := k) c hc).base (U.toSpecΓ.base u)).asHomogeneousIdeal ↔ _
  rw [h1]
  have hb : u ∈ U.basicOpen (MvPolynomial.aeval (R := k) c f) ↔
      MvPolynomial.aeval (R := k) c f ∉ (U.toSpecΓ.base u).asIdeal := by
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact PrimeSpectrum.mem_basicOpen _ _
  have h2 := Scheme.evaluation_eq_zero_iff_notMem_basicOpen (X := U) (U := ⊤) u trivial
    (MvPolynomial.aeval (R := k) c f)
  rw [← not_not (a := _ ∈ (U.toSpecΓ.base u).asIdeal), ← hb, ← h2, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_comp_left]
  rfl

/-- **The linear relations among the coordinates of the value at a point `u`.**  If the vector
of values `(c_b(u))_b` in `κ(u)` is a multiple `l` of a vector `(a_b)_b` with coefficients in `k`,
then `a_{b'} X_b - a_b X_{b'}` lies in the homogeneous prime ideal of the image of `u`. -/
theorem linear_mem_asHomogeneousIdeal_sectionsToProjSpace (c : ι → Γ(U, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) (u : U) (a : ι → k) (l : U.residueField u)
    (hl : ∀ b, U.Γevaluation u (c b) = l * U.Γevaluation u (algebraMap k Γ(U, ⊤) (a b)))
    (b b' : ι) :
    a b' • (MvPolynomial.X b : MvPolynomial ι k) - a b • MvPolynomial.X b' ∈
      ((sectionsToProjSpace (k := k) c hc).base u).asHomogeneousIdeal := by
  rw [mem_asHomogeneousIdeal_sectionsToProjSpace_iff c hc u
    (isHomogeneous_smul_X_sub_smul_X a b b')]
  simp only [MvPolynomial.smul_eq_C_mul]
  rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X]
  simp only [RingHom.comp_apply, hl]
  ring

end Sections

end MMP.Chow
