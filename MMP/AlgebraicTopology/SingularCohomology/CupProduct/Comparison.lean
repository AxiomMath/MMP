module

public import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Cochains
public import MMP.AlgebraicTopology.SingularCohomology.Relative
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Singular cochains as functions on simplices

The singular cochain complex `MMP.singularCochainComplex R R` of a space `Y`, with
coefficients in the ring `R`, has in degree `n` the `R`-linear maps from the free module on the
singular `n`-simplices to `R`; such a map is the same as a function on singular `n`-simplices,
and under this identification the differential is the coboundary
`MMP.SingularCochain.coboundary` and restriction to a subspace `A` is restriction
of functions. Hence the relative cochain complex of `(Y, A)` is the complex of functions
vanishing on the simplices of `A`, and the relative cohomology
`MMP.relativeSingularCohomology R R Y A n` is `Z^n(Y, A) / B^n(Y, A)`, i.e.
`MMP.SingularCochain.relCohomology R A n`.

## Main definitions

* `MMP.SingularCochain.cochainEquiv`: cochains as functions on simplices.
* `MMP.SingularCochain.relComplex`: the complex of cochains vanishing on `A`.
* `MMP.SingularCochain.relativeSingularCohomologyEquiv`:
  `H^n(Y, A; R) ≃ Z^n(Y, A) / B^n(Y, A)`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Simplicial Convexity

universe u

namespace MMP

namespace SingularCochain

open SingularChain

variable (R : Type u) [CommRing R] (Y : TopCat.{u})

/-- The singular chain complex of `Y` with coefficients in `R`. -/
abbrev chainCx : ChainComplex (ModuleCat.{u} R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj Y

/-- The differential of the singular chain complex sends the generator of a singular
`(n + 1)`-simplex `σ` to the alternating sum of the generators of its faces. -/
@[reassoc]
lemma ι_chainCx_d (n : ℕ) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n + 1⦌)) :
    Sigma.ι (fun _ ↦ ModuleCat.of R R) σ ≫ (chainCx R Y).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        Sigma.ι (fun _ ↦ ModuleCat.of R R) ((TopCat.toSSet.obj Y).δ i σ) := by
  have : (chainCx R Y).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      SimplicialObject.δ (TopCat.toSSet.obj Y ⋙ sigmaConst.obj (ModuleCat.of R R)) i :=
    AlternatingFaceMapComplex.obj_d_eq _ n
  rw [this]
  erw [Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  erw [Preadditive.comp_zsmul]
  congr 1
  simp only [SimplicialObject.δ, sigmaConst]
  erw [Sigma.ι_comp_map', Category.id_comp]

/-- The map of singular chains induced by `f : Y' ⟶ Y` sends the generator of a singular
simplex `σ` of `Y'` to the generator of its image under `f`. -/
@[reassoc]
lemma ι_chainCx_map {Y' : TopCat.{u}} (f : Y' ⟶ Y) (n : ℕ)
    (σ : (TopCat.toSSet.obj Y').obj (op ⦋n⦌)) :
    Sigma.ι (fun _ ↦ ModuleCat.of R R) σ ≫
        (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).map f).f n =
      Sigma.ι (fun _ ↦ ModuleCat.of R R) ((TopCat.toSSet.map f).app _ σ) := by
  dsimp [singularChainComplexFunctor, SSet.chainComplexFunctor]
  simp [Sigma.ι_comp_map']

/-- The singular `n`-simplices of `Y` in Mathlib's singular simplicial set are the continuous maps
`Δⁿ → Y`. -/
def simplexEquiv (n : ℕ) : (TopCat.toSSet.obj Y).obj (op ⦋n⦌) ≃ Simplex Y n :=
  (Y.toSSetObjEquiv (op ⦋n⦌)).trans
    { toFun f := f.comp ⟨stdSimplexHomeo _, (stdSimplexHomeo _).continuous⟩
      invFun g := g.comp ⟨(stdSimplexHomeo _).symm, (stdSimplexHomeo _).symm.continuous⟩
      left_inv f := by ext; simp
      right_inv g := by ext; simp }

/-- The function on singular simplices given by a singular cochain. -/
def cochainToFun (n : ℕ) :
    ((singularCochainComplex R (ModuleCat.of R R)).obj (op Y)).X n →ₗ[R] (Simplex Y n → R) where
  toFun φ τ := (Sigma.ι (fun _ ↦ ModuleCat.of R R) ((simplexEquiv Y n).symm τ) ≫ φ).hom 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The value of `cochainToFun R Y n φ` on a simplex `τ` is the value of `φ` on the generator
of `τ`. -/
lemma cochainToFun_apply (n : ℕ)
    (φ : ((singularCochainComplex R (ModuleCat.of R R)).obj (op Y)).X n) (τ : Simplex Y n) :
    cochainToFun R Y n φ τ =
      (Sigma.ι (fun _ ↦ ModuleCat.of R R) ((simplexEquiv Y n).symm τ) ≫ φ).hom 1 :=
  rfl

/-- The singular cochain given by a function on singular simplices. -/
def cochainOfFun (n : ℕ) (g : Simplex Y n → R) :
    ((singularCochainComplex R (ModuleCat.of R R)).obj (op Y)).X n :=
  Sigma.desc fun σ ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton R R (g (simplexEquiv Y n σ)))

/-- A singular cochain is a function on singular simplices. -/
def cochainEquiv (n : ℕ) :
    ((singularCochainComplex R (ModuleCat.of R R)).obj (op Y)).X n ≃ₗ[R] (Simplex Y n → R) :=
  LinearEquiv.ofBijective (cochainToFun R Y n)
    ⟨fun _ _ h ↦ by
      refine Sigma.hom_ext _ _ fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
      have := congr_fun h (simplexEquiv Y n σ)
      rwa [cochainToFun_apply, cochainToFun_apply, Equiv.symm_apply_apply] at this,
    fun g ↦ ⟨cochainOfFun R Y n g, by
        ext τ
        change (Sigma.ι (fun _ ↦ ModuleCat.of R R) ((simplexEquiv Y n).symm τ) ≫
          Sigma.desc fun σ ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton R R
            (g (simplexEquiv Y n σ)))).hom 1 = g τ
        rw [Sigma.ι_desc, Equiv.apply_symm_apply]
        simp⟩⟩

/-- The value of `cochainEquiv R Y n φ` on a simplex `τ` is the value of `φ` on the generator
of `τ`. -/
lemma cochainEquiv_apply (n : ℕ)
    (φ : ((singularCochainComplex R (ModuleCat.of R R)).obj (op Y)).X n) (τ : Simplex Y n) :
    cochainEquiv R Y n φ τ =
      (Sigma.ι (fun _ ↦ ModuleCat.of R R) ((simplexEquiv Y n).symm τ) ≫ φ).hom 1 :=
  rfl

/-- Under `simplexEquiv`, the `i`-th face of a singular simplex `τ` is its composition with
the face map `face n i`. -/
lemma simplexEquiv_symm_δ (n : ℕ) (τ : Simplex Y (n + 1)) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj Y).δ i ((simplexEquiv Y (n + 1)).symm τ) =
      (simplexEquiv Y n).symm (τ.comp (face n i)) := by
  show (Y.toSSetObjEquiv (op ⦋n⦌)).symm ((τ.comp ⟨(stdSimplexHomeo _).symm, (stdSimplexHomeo _).symm.continuous⟩).comp
      ⟨StdSimplex.map i.succAbove, by fun_prop⟩) =
    (Y.toSSetObjEquiv (op ⦋n⦌)).symm ((τ.comp (face n i)).comp ⟨(stdSimplexHomeo _).symm, (stdSimplexHomeo _).symm.continuous⟩)
  congr 1
  ext z
  exact congrArg τ (stdSimplexHomeo_symm_face n i z)

/-- The differential of singular cochains is the coboundary of functions on simplices. -/
lemma cochainEquiv_d (n : ℕ) (φ : ((singularCochainComplex R (ModuleCat.of R R)).obj (op Y)).X n) :
    cochainEquiv R Y (n + 1)
        ((((singularCochainComplex R (ModuleCat.of R R)).obj (op Y)).d n (n + 1)).hom φ) =
      coboundary R n (cochainEquiv R Y n φ) := by
  ext τ
  rw [cochainEquiv_apply, coboundary_apply]
  change (Sigma.ι (fun _ ↦ ModuleCat.of R R) ((simplexEquiv Y (n + 1)).symm τ) ≫
    (chainCx R Y).d (n + 1) n ≫ φ).hom 1 = _
  erw [ι_chainCx_d_assoc, Preadditive.sum_comp]
  simp only [ModuleCat.hom_sum, simplexEquiv_symm_δ]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  erw [Preadditive.zsmul_comp]
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
  push_cast
  rfl

/-- Restriction of singular cochains to a subspace is restriction of functions. -/
lemma cochainEquiv_restriction (A : Set Y) (n : ℕ)
    (φ : ((singularCochainComplex R (ModuleCat.of R R)).obj (op Y)).X n)
    (τ : Simplex (TopCat.of A) n) :
    cochainEquiv R (TopCat.of A) n
        (((singularCochainRestriction R (ModuleCat.of R R) Y A).f n).hom φ) τ =
      cochainEquiv R Y n φ ((subspaceInclusion Y A).hom.comp τ) := by
  rw [cochainEquiv_apply]
  change (Sigma.ι (fun _ ↦ ModuleCat.of R R) ((simplexEquiv (TopCat.of A) n).symm τ) ≫
    (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).map
      (subspaceInclusion Y A)).f n ≫ φ).hom 1 = _
  erw [ι_chainCx_map_assoc]
  rfl

variable {Y}

/-- The coboundary on cochains vanishing on `A`. -/
def vanishingCoboundary (A : Set Y) (n : ℕ) : vanishing R n A →ₗ[R] vanishing R (n + 1) A :=
  ((coboundary R n).domRestrict _).codRestrict _ (fun φ ↦ coboundary_mem_vanishing φ.2)

/-- The complex of singular cochains of `Y` vanishing on the simplices of `A`. -/
def relComplex (A : Set Y) : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (vanishing R n A))
    (fun n ↦ ModuleCat.ofHom (vanishingCoboundary R A n))
    (fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun φ ↦
      Subtype.ext (coboundary_coboundary (R := R) n φ.1)))

/-- The differential of `relComplex R A` in degree `n` is `vanishingCoboundary R A n`. -/
lemma relComplex_d (A : Set Y) (n : ℕ) :
    (relComplex R A).d n (n + 1) = ModuleCat.ofHom (vanishingCoboundary R A n) :=
  CochainComplex.of_d (fun n ↦ ModuleCat.of R (vanishing R n A))
    (fun n ↦ ModuleCat.ofHom (vanishingCoboundary R A n)) n

/-- The inclusion of the cochains vanishing on `A` into all singular cochains. -/
def relInclusion (A : Set Y) :
    relComplex R A ⟶ (singularCochainComplex R (ModuleCat.of R R)).obj (op Y) where
  f n := ModuleCat.ofHom ((cochainEquiv R Y n).symm.toLinearMap ∘ₗ (vanishing R n A).subtype)
  comm' i j hij := by
    obtain rfl : j = i + 1 := by simpa using hij.symm
    refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ (cochainEquiv R Y (i + 1)).injective ?_)
    change cochainEquiv R Y (i + 1) ((((singularCochainComplex R (ModuleCat.of R R)).obj
        (op Y)).d i (i + 1)).hom ((cochainEquiv R Y i).symm φ.1)) =
      cochainEquiv R Y (i + 1) ((cochainEquiv R Y (i + 1)).symm
        (((relComplex R A).d i (i + 1)).hom φ).1)
    rw [cochainEquiv_d, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      relComplex_d]
    rfl

/-- A cochain vanishing on `A` restricts to zero on `A`. -/
lemma relInclusion_comp_restriction (A : Set Y) :
    relInclusion R A ≫ singularCochainRestriction R (ModuleCat.of R R) Y A = 0 := by
  ext n φ
  apply (cochainEquiv R (TopCat.of A) n).injective
  ext τ
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    cochainEquiv_restriction, HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply,
    map_zero]
  change cochainEquiv R Y n ((cochainEquiv R Y n).symm φ.1) _ = 0
  rw [LinearEquiv.apply_symm_apply]
  exact φ.2 _ (Set.range_subset_iff.2 fun t ↦ (τ t).2)

/-- The short complex `0 → C^*(Y, A) → C^*(Y) → C^*(A)`. -/
def relShortComplex (A : Set Y) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (relInclusion R A) (singularCochainRestriction R (ModuleCat.of R R) Y A)
    (relInclusion_comp_restriction R A)

/-- The sequence `C^*(Y, A) → C^*(Y) → C^*(A)` is exact at `C^*(Y)`. -/
lemma relShortComplex_exact (A : Set Y) : (relShortComplex R A).Exact := by
  refine HomologicalComplex.exact_of_degreewise_exact _ fun n ↦
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx ↦ ?_
  have hx' : ∀ τ, cochainEquiv R (TopCat.of A) n
      (((singularCochainRestriction R (ModuleCat.of R R) Y A).f n).hom x) τ = 0 := by
    intro τ
    rw [show ((singularCochainRestriction R (ModuleCat.of R R) Y A).f n).hom x = 0 from hx,
      map_zero]
    rfl
  refine ⟨⟨cochainEquiv R Y n x, fun σ hσ ↦ ?_⟩, (cochainEquiv R Y n).symm_apply_apply x⟩
  have := hx' ⟨fun t ↦ ⟨σ t, hσ ⟨t, rfl⟩⟩, σ.continuous.subtype_mk _⟩
  erw [cochainEquiv_restriction] at this
  exact this

/-- The inclusion of the cochains vanishing on `A` is a monomorphism. -/
instance (A : Set Y) : Mono (relInclusion R A) :=
  HomologicalComplex.mono_of_mono_f _ fun n ↦ (ModuleCat.mono_iff_injective _).2 fun _ _ h ↦
    Subtype.ext ((cochainEquiv R Y n).symm.injective h)

/-- The first map of `relShortComplex R A` is a monomorphism. -/
instance (A : Set Y) : Mono (relShortComplex R A).f :=
  inferInstanceAs (Mono (relInclusion R A))

/-- The relative cochain complex of `(Y, A)` is the complex of cochains vanishing on `A`. -/
def relComplexIso (A : Set Y) :
    relativeSingularCochainComplex R (ModuleCat.of R R) Y A ≅ relComplex R A :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel _) (relShortComplex_exact R A).fIsKernel

/-- As a function on simplices, the differential of `relComplex R A` applied to `φ` is the
coboundary of `φ`. -/
lemma relComplex_d_apply (A : Set Y) (n : ℕ) (φ : (relComplex R A).X n) :
    (vanishing R (n + 1) A).subtype (((relComplex R A).d n (n + 1)).hom φ) =
      coboundary R n ((vanishing R n A).subtype φ) := by
  rw [relComplex_d]
  rfl

/-- The differential of `relComplex R A` vanishes on `φ` if and only if the coboundary of `φ`
vanishes. -/
lemma relComplex_d_eq_zero_iff (A : Set Y) (n : ℕ) (φ : (relComplex R A).X n) :
    ((relComplex R A).d n (n + 1)).hom φ = 0 ↔
      coboundary R n ((vanishing R n A).subtype φ) = 0 := by
  rw [← relComplex_d_apply]
  exact Subtype.ext_iff

/-- A function on simplices is a relative cocycle if and only if it vanishes on `A` and its
coboundary is zero. -/
lemma mem_relCocycles_iff (A : Set Y) (n : ℕ) (φ : Simplex Y n → R) :
    φ ∈ relCocycles R A n ↔ φ ∈ vanishing R n A ∧ coboundary R n φ = 0 :=
  Submodule.mem_inf.trans (and_congr Iff.rfl LinearMap.mem_ker)

/-- The relative cocycles of `relComplex`, in the short complex computing its homology, are the
relative cocycles `Z^n(Y, A)`. -/
def scCocyclesEquiv (A : Set Y) (i n : ℕ) :
    LinearMap.ker ((relComplex R A).sc' i n (n + 1)).g.hom ≃ₗ[R] relCocycles R A n where
  toFun x := ⟨(vanishing R n A).subtype x.1, (mem_relCocycles_iff R A n _).2
    ⟨((x.1 : (relComplex R A).X n) : vanishing R n A).2,
      (relComplex_d_eq_zero_iff R A n x.1).1 (LinearMap.mem_ker.1 x.2)⟩⟩
  invFun y := ⟨(⟨y.1, ((mem_relCocycles_iff R A n _).1 y.2).1⟩ : vanishing R n A),
    LinearMap.mem_ker.2 ((relComplex_d_eq_zero_iff R A n
      (⟨y.1, ((mem_relCocycles_iff R A n _).1 y.2).1⟩ : vanishing R n A)).2
        ((mem_relCocycles_iff R A n _).1 y.2).2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The function on simplices underlying `scCocyclesEquiv R A i n x` is the underlying cochain
of `x`. -/
lemma scCocyclesEquiv_apply (A : Set Y) (i n : ℕ)
    (x : LinearMap.ker ((relComplex R A).sc' i n (n + 1)).g.hom) :
    (scCocyclesEquiv R A i n x : Simplex Y n → R) = (vanishing R n A).subtype x.1 :=
  rfl

/-- The homology of `relComplex` is the relative cohomology `Z^n(Y, A) / B^n(Y, A)`. -/
def relHomologyEquiv (A : Set Y) (n : ℕ) :
    (relComplex R A).homology n ≃ₗ[R] relCohomology R A n :=
  match n with
  | 0 => (((relComplex R A).homologyIsoSc' 0 0 1 (by simp) (by simp)) ≪≫
      ShortComplex.moduleCatHomologyIso _).toLinearEquiv.trans
        (Submodule.Quotient.equiv _ _ (scCocyclesEquiv R A 0 0) (by
          ext y
          simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_comap,
            Submodule.coe_subtype]
          constructor
          · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
            change (vanishing R 0 A).subtype (((relComplex R A).d 0 0).hom x) ∈
              relCoboundaries R A 0
            rw [(relComplex R A).shape 0 0 (by simp)]
            exact Submodule.zero_mem _
          · intro hy
            have hy0 : y = 0 := Subtype.ext ((Submodule.mem_bot R).1 hy)
            refine ⟨0, ⟨0, map_zero _⟩, ?_⟩
            rw [map_zero, hy0]))
  | n + 1 => (((relComplex R A).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)) ≪≫
      ShortComplex.moduleCatHomologyIso _).toLinearEquiv.trans
        (Submodule.Quotient.equiv _ _ (scCocyclesEquiv R A n (n + 1)) (by
          ext y
          simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_comap,
            Submodule.coe_subtype]
          constructor
          · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
            exact ⟨_, ((x : (relComplex R A).X n) : vanishing R n A).2,
              (relComplex_d_apply R A n x).symm⟩
          · rintro ⟨x, hx, hxy⟩
            exact ⟨_, ⟨⟨x, hx⟩, rfl⟩,
              Subtype.ext ((relComplex_d_apply R A n ⟨x, hx⟩).trans hxy)⟩))

/-- The singular cohomology `H^n(Y, A; R)` of a pair is the relative cohomology
`Z^n(Y, A) / B^n(Y, A)` of cochains on singular simplices. -/
def relativeSingularCohomologyEquiv (A : Set Y) (n : ℕ) :
    relativeSingularCohomology R (ModuleCat.of R R) Y A n ≃ₗ[R] relCohomology R A n :=
  (HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat rfl ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (relComplexIso R A)).toLinearEquiv.trans
      (relHomologyEquiv R A n)

end SingularCochain

end MMP
