module

public import MMP.AlgebraicTopology.ThomClass.Basic
public import Mathlib.Topology.VectorBundle.Constructions
/-!
# Naturality of the Thom class (Fulton, §19.1)

A continuous map `g : Y' → Y` with `g(A') ⊆ A` pulls singular cochains of `Y` vanishing on `A`
back to cochains of `Y'` vanishing on `A'`, `φ ↦ (τ ↦ φ (g ∘ τ))`; this commutes with the
coboundary and so induces `g^* : H^n(Y, A) → H^n(Y', A')` on cocycles modulo coboundaries. Under
the identification `MMP.SingularCochain.relativeSingularCohomologyEquiv` of
singular cohomology with cocycles modulo coboundaries, it is the map of pairs
`MMP.relativeSingularCohomology.map` induced by `g`.

For a complex vector bundle `E` on `X` and a continuous map `f : X' → X`, the induced bundle map
`f̃ : f^* E → E` restricts on the fibre over `x'` to the identity `(f^* E)_{x'} = E_{f x'}`, and
maps `f^* E - 0` into `E - 0`. So `f̃` sends an oriented simplex around `0` in `(f^* E)_{x'}`
to one in `E_{f x'}`, and the Thom-class condition `⟨u, μ_{E_x}⟩ = 1` for `u` gives it for
`f̃^* u`: the pull-back of the Thom class `u_E` is the Thom class `u_{f^* E}` (by uniqueness of
the Thom class, Milnor–Stasheff, Thm. 10.4).

## Main definitions

* `MMP.SingularCochain.cochainPullback`: the pull-back of cochains.
* `MMP.SingularCochain.relCohomologyMap`: `g^*` on cocycles modulo coboundaries.

## Main results

* `MMP.SingularCochain.relativeSingularCohomologyEquiv_map`: the identification of
  singular cohomology with cocycles modulo coboundaries is natural.
* `MMP.IsThomClass.pullback`: `f̃^*` of a Thom class of `E` is a Thom class of `f^* E`.

## Implementation notes

The Thom class is the predicate `MMP.IsThomClass` (a class with the defining property; it is
unique by Thom's theorem), so the naturality `f̃^* u_E = u_{f^* E}` is stated as "`f̃^*` of a Thom
class of `E` is a Thom class of `f^* E`". The pull-back `f̃^*` is the map of pairs
`(f^* E, f^* E - 0) → (E, E - 0)`; the zero section of `f^* E` is the preimage of that of `E`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], §§9–10.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Set Bundle AlgebraicTopology

universe u

namespace MMP

namespace SingularCochain

open SingularChain

variable (R : Type u) [CommRing R] {Y' Y : TopCat.{u}} (g : Y' ⟶ Y)

/-- The pull-back `φ ↦ (τ ↦ φ (g ∘ τ))` of singular cochains along a continuous map `g`. -/
def cochainPullback (n : ℕ) : (Simplex Y n → R) →ₗ[R] (Simplex Y' n → R) where
  toFun φ τ := φ (g.hom.comp τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {R}

/-- The value of `cochainPullback R g n φ` on a simplex `τ` is `φ (g ∘ τ)`. -/
@[simp]
lemma cochainPullback_apply (n : ℕ) (φ : Simplex Y n → R) (τ : Simplex Y' n) :
    cochainPullback R g n φ τ = φ (g.hom.comp τ) :=
  rfl

/-- The pull-back of cochains commutes with the coboundary. -/
lemma coboundary_cochainPullback (n : ℕ) (φ : Simplex Y n → R) :
    coboundary R n (cochainPullback R g n φ) = cochainPullback R g (n + 1) (coboundary R n φ) := by
  ext τ
  simp only [coboundary_apply, cochainPullback_apply, ContinuousMap.comp_assoc]

variable {A' : Set Y'} {A : Set Y}

/-- If `g(A') ⊆ A`, the pull-back of a cochain vanishing on `A` vanishes on `A'`. -/
lemma cochainPullback_mem_vanishing (h : A' ⊆ g ⁻¹' A) {n : ℕ} {φ : Simplex Y n → R}
    (hφ : φ ∈ vanishing R n A) : cochainPullback R g n φ ∈ vanishing R n A' := fun τ hτ ↦
  hφ _ (by rintro _ ⟨t, rfl⟩; exact h (hτ ⟨t, rfl⟩))

/-- If `g(A') ⊆ A`, the pull-back of a relative cocycle of `(Y, A)` is a relative cocycle of
`(Y', A')`. -/
lemma cochainPullback_mem_relCocycles (h : A' ⊆ g ⁻¹' A) {n : ℕ} {φ : Simplex Y n → R}
    (hφ : φ ∈ relCocycles R A n) : cochainPullback R g n φ ∈ relCocycles R A' n := by
  rw [mem_relCocycles_iff] at hφ ⊢
  refine ⟨cochainPullback_mem_vanishing g h hφ.1, ?_⟩
  rw [coboundary_cochainPullback, hφ.2, map_zero]

/-- If `g(A') ⊆ A`, the pull-back of a relative coboundary of `(Y, A)` is a relative coboundary
of `(Y', A')`. -/
lemma cochainPullback_mem_relCoboundaries (h : A' ⊆ g ⁻¹' A) {n : ℕ} {φ : Simplex Y n → R}
    (hφ : φ ∈ relCoboundaries R A n) : cochainPullback R g n φ ∈ relCoboundaries R A' n := by
  cases n with
  | zero =>
    have : φ = 0 := (Submodule.mem_bot R).1 hφ
    rw [this, map_zero]
    exact Submodule.zero_mem _
  | succ n =>
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    exact ⟨_, cochainPullback_mem_vanishing g h hψ, coboundary_cochainPullback g n ψ⟩

variable (R) in
/-- The pull-back of relative cocycles. -/
def relCocyclesMap (h : A' ⊆ g ⁻¹' A) (n : ℕ) : relCocycles R A n →ₗ[R] relCocycles R A' n :=
  (cochainPullback R g n).restrict fun _ hφ ↦ cochainPullback_mem_relCocycles g h hφ

variable (R) in
/-- The pull-back `g^* : H^n(Y, A) → H^n(Y', A')` on cocycles modulo coboundaries. -/
def relCohomologyMap (h : A' ⊆ g ⁻¹' A) (n : ℕ) : relCohomology R A n →ₗ[R] relCohomology R A' n :=
  Submodule.mapQ _ _ (relCocyclesMap R g h n) fun _ hφ ↦
    cochainPullback_mem_relCoboundaries g h hφ

/-- `relCohomologyMap` sends the class of a cocycle `φ` to the class of its pull-back. -/
lemma relCohomologyMap_mk (h : A' ⊆ g ⁻¹' A) (n : ℕ) (φ : relCocycles R A n) :
    relCohomologyMap R g h n (Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk ⟨cochainPullback R g n φ.1, cochainPullback_mem_relCocycles g h φ.2⟩ :=
  rfl

variable (R) in
/-- The pull-back on the complex of cochains vanishing on a subset. -/
def relComplexMap (h : A' ⊆ g ⁻¹' A) : relComplex R A ⟶ relComplex R A' where
  f n := ModuleCat.ofHom ((cochainPullback R g n).restrict fun _ hφ ↦
    cochainPullback_mem_vanishing g h hφ)
  comm' i j hij := by
    obtain rfl : j = i + 1 := by simpa using hij.symm
    refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ Subtype.ext ?_)
    change (vanishing R (i + 1) A').subtype (((relComplex R A').d i (i + 1)).hom _) =
      cochainPullback R g (i + 1)
        ((vanishing R (i + 1) A).subtype (((relComplex R A).d i (i + 1)).hom φ))
    rw [relComplex_d_apply, relComplex_d_apply]
    exact coboundary_cochainPullback g i φ.1

/-- In degree `n`, `relComplexMap` is the pull-back of the underlying cochain. -/
lemma relComplexMap_f_apply (h : A' ⊆ g ⁻¹' A) (n : ℕ) (φ : (relComplex R A).X n) :
    (vanishing R n A').subtype (((relComplexMap R g h).f n).hom φ) =
      cochainPullback R g n ((vanishing R n A).subtype φ) :=
  rfl

/-- Under `cochainEquiv`, the map induced by `g` on singular cochains is
`cochainPullback R g n`. -/
lemma cochainEquiv_map (n : ℕ)
    (φ : ((singularCochainComplex R (ModuleCat.of R R)).obj (op Y)).X n) :
    cochainEquiv R Y' n ((((singularCochainComplex R (ModuleCat.of R R)).map g.op).f n).hom φ) =
      cochainPullback R g n (cochainEquiv R Y n φ) := by
  ext τ
  rw [cochainEquiv_apply]
  change (Sigma.ι (fun _ ↦ ModuleCat.of R R) ((simplexEquiv Y' n).symm τ) ≫
    (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).map g).f n ≫
      φ).hom 1 = _
  erw [ι_chainCx_map_assoc]
  rfl

/-- `relComplexMap` is compatible, under `relInclusion`, with the map induced by `g` on the
singular cochain complex. -/
lemma relComplexMap_comp_relInclusion (h : A' ⊆ g ⁻¹' A) :
    relComplexMap R g h ≫ relInclusion R A' =
      relInclusion R A ≫ (singularCochainComplex R (ModuleCat.of R R)).map g.op := by
  ext n φ
  apply (cochainEquiv R Y' n).injective
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, cochainEquiv_map]
  change cochainEquiv R Y' n ((cochainEquiv R Y' n).symm _) =
    cochainPullback R g n (cochainEquiv R Y n ((cochainEquiv R Y n).symm φ.1))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The composite of `relComplexIso` with `relInclusion` is the kernel inclusion. -/
lemma relComplexIso_hom_comp_relInclusion (A : Set Y) :
    (relComplexIso R A).hom ≫ relInclusion R A = kernel.ι _ :=
  IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel _) (relShortComplex_exact R A).fIsKernel
    WalkingParallelPair.zero

/-- The isomorphism `relComplexIso` is natural in maps of pairs. -/
lemma relComplexIso_hom_naturality (h : A' ⊆ g ⁻¹' A) :
    relativeSingularCochainComplex.map R (ModuleCat.of R R) g h ≫ (relComplexIso R A').hom =
      (relComplexIso R A).hom ≫ relComplexMap R g h := by
  rw [← cancel_mono (relInclusion R A'), Category.assoc, relComplexIso_hom_comp_relInclusion,
    Category.assoc, relComplexMap_comp_relInclusion, ← Category.assoc,
    relComplexIso_hom_comp_relInclusion, relativeSingularCochainComplex.map_ι]

/-- On classes of cycles, `relHomologyEquiv` is the class of the underlying cocycle. -/
lemma relHomologyEquiv_homologyπ (A : Set Y) (n : ℕ)
    (z : (relComplex R A).cycles n) (w : relCocycles R A n)
    (hw : (w : Simplex Y n → R) = (vanishing R n A).subtype (((relComplex R A).iCycles n).hom z)) :
    relHomologyEquiv R A n (((relComplex R A).homologyπ n).hom z) = Submodule.Quotient.mk w := by
  have key : ∀ (i k : ℕ) (hi : (ComplexShape.up ℕ).prev n = i)
      (hk : (ComplexShape.up ℕ).next n = k),
      ((relComplex R A).homologyIsoSc' i n k hi hk ≪≫
        ((relComplex R A).sc' i n k).moduleCatHomologyIso).hom.hom
          (((relComplex R A).homologyπ n).hom z) =
        ((relComplex R A).sc' i n k).moduleCatLeftHomologyData.π.hom
          (((relComplex R A).sc' i n k).moduleCatCyclesIso.hom.hom
            (((relComplex R A).cyclesIsoSc' i n k hi hk).hom.hom z)) := by
    intro i k hi hk
    rw [Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
    have e := congrArg (fun f ↦ ModuleCat.Hom.hom f z)
      (HomologicalComplex.π_homologyIsoSc'_hom (relComplex R A) i n k hi hk)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    rw [e]
    exact ShortComplex.π_moduleCatCyclesIso_hom_apply _ _
  have val : ∀ (i k : ℕ) (hi : (ComplexShape.up ℕ).prev n = i)
      (hk : (ComplexShape.up ℕ).next n = k),
      Subtype.val (((relComplex R A).sc' i n k).moduleCatCyclesIso.hom.hom
            (((relComplex R A).cyclesIsoSc' i n k hi hk).hom.hom z)) =
        ((relComplex R A).iCycles n).hom z := by
    intro i k hi hk
    have e1 := congrArg (fun f ↦ ModuleCat.Hom.hom f z)
      (HomologicalComplex.cyclesIsoSc'_hom_iCycles (relComplex R A) i n k hi hk)
    have e2 := ShortComplex.moduleCatCyclesIso_hom_i_apply ((relComplex R A).sc' i n k)
      (((relComplex R A).cyclesIsoSc' i n k hi hk).hom.hom z)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1
    refine Eq.trans ?_ e1
    exact e2
  cases n with
  | zero =>
    have h1 := key 0 1 (by simp) (by simp)
    have h2 := val 0 1 (by simp) (by simp)
    rw [relHomologyEquiv]
    erw [LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, h1]
    change Submodule.Quotient.mk (scCocyclesEquiv R A 0 0 _) = _
    congr 1
    apply Subtype.ext
    rw [hw]
    exact congrArg (vanishing R _ A).subtype h2
  | succ n =>
    have h1 := key n (n + 2) (by simp) (by simp)
    have h2 := val n (n + 2) (by simp) (by simp)
    rw [relHomologyEquiv]
    erw [LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, h1]
    change Submodule.Quotient.mk (scCocyclesEquiv R A n (n + 1) _) = _
    congr 1
    apply Subtype.ext
    rw [hw]
    exact congrArg (vanishing R _ A).subtype h2

/-- The underlying cochain of a cycle of `relComplex` is a relative cocycle. -/
lemma iCycles_mem_relCocycles (A : Set Y) (n : ℕ) (z : (relComplex R A).cycles n) :
    (vanishing R n A).subtype (((relComplex R A).iCycles n).hom z) ∈ relCocycles R A n := by
  refine (mem_relCocycles_iff R A n _).2
    ⟨(((relComplex R A).iCycles n).hom z : vanishing R n A).2, ?_⟩
  refine (relComplex_d_eq_zero_iff R A n _).1 ?_
  have := congrArg (fun f ↦ ModuleCat.Hom.hom f z) ((relComplex R A).iCycles_d n (n + 1))
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at this
  exact this

/-- A cycle of `relComplex` as a relative cocycle. -/
def cyclesToRelCocycles (A : Set Y) (n : ℕ) (z : (relComplex R A).cycles n) : relCocycles R A n :=
  ⟨(vanishing R n A).subtype (((relComplex R A).iCycles n).hom z), iCycles_mem_relCocycles A n z⟩

/-- The identification `relHomologyEquiv` commutes with the maps induced by `g`. -/
lemma relHomologyEquiv_naturality (h : A' ⊆ g ⁻¹' A) (n : ℕ) (x : (relComplex R A).homology n) :
    relHomologyEquiv R A' n (HomologicalComplex.homologyMap (relComplexMap R g h) n |>.hom x) =
      relCohomologyMap R g h n (relHomologyEquiv R A n x) := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((relComplex R A).homologyπ n)).1 inferInstance x
  have e := congrArg (fun f ↦ ModuleCat.Hom.hom f z)
    (HomologicalComplex.homologyπ_naturality (relComplexMap R g h) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  erw [e]
  erw [relHomologyEquiv_homologyπ A n z (cyclesToRelCocycles A n z) rfl,
    relHomologyEquiv_homologyπ A' n _
      (cyclesToRelCocycles A' n
        (HomologicalComplex.cyclesMap (relComplexMap R g h) n |>.hom z)) rfl,
    relCohomologyMap_mk]
  congr 1
  apply Subtype.ext
  have e2 := congrArg (fun f ↦ ModuleCat.Hom.hom f z)
    (HomologicalComplex.cyclesMap_i (relComplexMap R g h) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e2
  change (vanishing R n A').subtype _ = _
  rw [e2]
  rfl

/-- The identification `MMP.SingularCochain.relativeSingularCohomologyEquiv` of
singular cohomology with cocycles modulo coboundaries is natural in maps of pairs. -/
theorem relativeSingularCohomologyEquiv_map (h : A' ⊆ g ⁻¹' A) (n : ℕ)
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y A n) :
    relativeSingularCohomologyEquiv R A' n ((relativeSingularCohomology.map R _ g h n).hom x) =
      relCohomologyMap R g h n (relativeSingularCohomologyEquiv R A n x) := by
  have e1 := congrArg (fun f ↦ ModuleCat.Hom.hom f x)
    (HomologicalComplex.extendHomologyIso_hom_naturality
      (relativeSingularCochainComplex.map R (ModuleCat.of R R) g h) ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) rfl)
  have e2 := congrArg (fun f ↦ ModuleCat.Hom.hom f
      (((relativeSingularCochainComplex R (ModuleCat.of R R) Y A).extendHomologyIso
        ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom.hom x))
    (congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n) (relComplexIso_hom_naturality g h))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, HomologicalComplex.homologyMap_comp] at e1 e2
  change relHomologyEquiv R A' n (HomologicalComplex.homologyMap (relComplexIso R A').hom n |>.hom
      (((relativeSingularCochainComplex R (ModuleCat.of R R) Y' A').extendHomologyIso
        ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom.hom
          ((relativeSingularCohomology.map R _ g h n).hom x))) =
    relCohomologyMap R g h n (relHomologyEquiv R A n (HomologicalComplex.homologyMap
      (relComplexIso R A).hom n |>.hom (((relativeSingularCochainComplex R (ModuleCat.of R R) Y
        A).extendHomologyIso ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom.hom x)))
  rw [← relHomologyEquiv_naturality, ← e2]
  congr 2

/-- Evaluating the pull-back of `φ` on a chain `c` is evaluating `φ` on the push-forward of `c`. -/
lemma eval_cochainPullback {n : ℕ} (φ : Simplex Y n → R) (c : Chain R Y' n) :
    eval (cochainPullback R g n φ) c = eval φ (Finsupp.mapDomain g.hom.comp c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, Finsupp.mapDomain_add, map_add, hc, hd]
  | single σ a => simp [Finsupp.mapDomain_single, cochainPullback_apply]

/-- `relEval c` depends only on the chain `c`. -/
lemma relEval_congr {Z : Type*} [TopologicalSpace Z] {S : Set Z} {n : ℕ} {c c' : Chain R Z n}
    (e : c = c') (hc : ∀ φ ∈ relCoboundaries R S n, eval φ c = 0)
    (hc' : ∀ φ ∈ relCoboundaries R S n, eval φ c' = 0) : relEval c hc = relEval c' hc' := by
  subst e
  rfl

/-- Evaluating `g^* y` on a chain `c` is evaluating `y` on the push-forward of `c`. -/
lemma relEval_relCohomologyMap {n : ℕ} (h : A' ⊆ g ⁻¹' A) (c : Chain R Y' n)
    (hc : ∀ φ ∈ relCoboundaries R A' n, eval φ c = 0)
    (hc' : ∀ φ ∈ relCoboundaries R A n, eval φ (Finsupp.mapDomain g.hom.comp c) = 0)
    (y : relCohomology R A n) :
    relEval c hc (relCohomologyMap R g h n y) = relEval (Finsupp.mapDomain g.hom.comp c) hc' y := by
  induction y using Submodule.Quotient.induction_on with
  | H φ =>
    rw [relCohomologyMap_mk, relEval_mk, relEval_mk]
    exact eval_cochainPullback g φ.1 c

end SingularCochain

section ThomClass

open ThomClass SingularChain SingularCochain

variable {R : Type u} [CommRing R] {B B' : Type u} [TopologicalSpace B] [TopologicalSpace B']
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (E : B → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [_root_.VectorBundle ℂ F E]
  (f : C(B', B))

/-- The fibres `(f^* E)_{x'} = E_{f x'}` of a pull-back bundle are additive groups when those of
`E` are. -/
instance pullbackAddCommGroup (x : B') : AddCommGroup ((f *ᵖ E) x) :=
  inferInstanceAs <| AddCommGroup (E (f x))

/-- The induced bundle map `f̃ : f^* E → E`, as a map of spaces. -/
def pullbackBundleMap : TopCat.of (TotalSpace F (f *ᵖ E)) ⟶ TopCat.of (TotalSpace F E) :=
  TopCat.ofHom ⟨Pullback.lift f, Pullback.continuous_lift F E f⟩

omit [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [_root_.VectorBundle ℂ F E] in
/-- The induced bundle map `f̃ : f^* E → E` maps the complement of the zero section of `f^* E`
into the complement of the zero section of `E`. -/
lemma pullbackBundleMap_compl_zeroSection :
    (range (zeroSection F (f *ᵖ E)))ᶜ ⊆ pullbackBundleMap F E f ⁻¹' (range (zeroSection F E))ᶜ := by
  rintro ⟨x', v⟩ hp ⟨y, hy⟩
  refine hp ⟨x', ?_⟩
  have h1 : y = f x' := congrArg TotalSpace.proj hy
  subst h1
  have h2 : (0 : E (f x')) = v := (TotalSpace.mk_inj).1 hy
  rw [zeroSection, ← h2]
  rfl

/-- **Naturality of the Thom class** (Fulton, §19.1): for a complex vector bundle `E` on `X`, a
continuous `f : X' → X` and the induced bundle map `f̃ : f^* E → E`, the pull-back `f̃^* u` of a
Thom class `u` of `E` is a Thom class of `f^* E`. Combined with uniqueness of Thom classes
(Milnor–Stasheff, Thm. 10.4), this gives `f̃^* u_E = u_{f^* E}`. -/
theorem IsThomClass.pullback
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F E))
      (range (zeroSection F E)) (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsThomClass F E u) :
    IsThomClass F (f *ᵖ E) ((relativeSingularCohomology.map R (ModuleCat.of R R)
      (pullbackBundleMap F E f) (pullbackBundleMap_compl_zeroSection F E f) _).hom u) := by
  intro x' ψ v hv
  rw [relativeSingularCohomologyEquiv_map]
  have hσ : (pullbackBundleMap F E f).hom.comp (fibreSimplex F x' ψ v) =
      fibreSimplex F (f x') ψ v :=
    ContinuousMap.ext fun _ ↦ rfl
  have hc' : ∀ φ ∈ relCoboundaries R (range (zeroSection F E))ᶜ (2 * Module.finrank ℂ F),
      eval φ (Finsupp.mapDomain (pullbackBundleMap F E f).hom.comp
        (Finsupp.single (fibreSimplex F x' ψ v) 1)) = 0 := by
    rw [Finsupp.mapDomain_single, hσ]
    exact eval_single_eq_zero_of_mem_relCoboundaries _
      (fibreSimplex_notMem_range_zeroSection F (f x') ψ hv)
  refine (relEval_relCohomologyMap (pullbackBundleMap F E f) _ _ _ hc' _).trans ?_
  exact (LinearMap.congr_fun (relEval_congr (by rw [Finsupp.mapDomain_single, hσ]) hc' _) _).trans
    (hu (f x') ψ v hv)

end ThomClass

end MMP
