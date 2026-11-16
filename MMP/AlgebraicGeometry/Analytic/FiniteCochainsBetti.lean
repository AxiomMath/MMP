module
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicTopology.ComplexVectorBundle.FirstChernClass
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicGeometry.Analytic.FiniteHomotopyType

/-!
# Finite cochains and Betti numbers of projective complex schemes

Let `X` be a projective scheme over `ℂ` with complex realization `X^an`. The integral singular
chain complex `C_•(X^an; ℤ)` is chain homotopy equivalent to a bounded complex of finitely
generated free abelian groups. Consequently every `H^i(X^an; ℤ)` is finitely generated, the change
of coefficients `H^i(X^an; ℤ) → H^i(X^an; ℚ)` exhibits `H^i(X^an; ℚ)` as `H^i(X^an; ℤ) ⊗_ℤ ℚ`,
and the rational singular homology `H_k(X^an; ℚ)` is finite-dimensional in every degree, so the
cycle spans `Cyc_r(X)` and `Cyc_2(X × ℙ¹)` defining the cycle ranks are finite-dimensional.

## Main results

* `MMP.Analytic.exists_homotopyEquiv_singularChainComplex_of_isProjectiveMorphism`: the finite
  integral cochain model, the finite generation of integral cohomology, and the rational
  coefficient isomorphism.
* `MMP.Analytic.finite_analyticSingularCohomology_of_isProjectiveMorphism`: `H^i(X^an; R)` is a
  finite `R`-module for every Noetherian coefficient ring `R`.
* `MMP.Analytic.isBaseChange_mapCoeff_of_isProjectiveMorphism`: the change of coefficients
  `H^i(X^an; ℤ) → H^i(X^an; ℚ)` is a base change from `ℤ` to `ℚ`.
* `MMP.Analytic.finiteDimensional_singularHomology_of_isProjective`: `H_k(X, ℚ)`, `Cyc_r(X)` and
  `Cyc_2(X × ℙ¹)` are finite-dimensional for projective `X` over `ℂ`.

## Implementation notes

The space `X^an` is homotopy equivalent to the polyhedron `|K|` of a finite simplicial complex
`K` (`MMP.Analytic.exists_homotopyEquiv_finite_simplicialComplex_of_isProjective`). For `|K|`,
the oriented simplicial chains `C_•(K)` map to singular chains by the affine simplices of the
faces; in the other direction Hatcher's subdivision operator moves every chain into the chains
small for the open stars of the vertices, and the method of acyclic carriers (the carriers are
cones of faces with star-shaped polyhedra) gives the homotopy inverse. Applying `Hom_ℤ(-, A)`, the
statement "cohomology with coefficients in `A` is computed by `Hom(C_•, A)`" is formalized by the
stronger, coefficient-free homotopy equivalence of chain complexes. Every cocycle `ψ` of `X^an`
is cohomologous to `(ψ ∘ f) ∘ g` for the equivalence `f, g`, which gives finite generation over
any Noetherian coefficient ring; a
rational cochain on the finitely generated `C_n` becomes integral after multiplication by some
`s ≠ 0`, which gives the base change. The isomorphism `H^i(X^an; ℤ) ⊗_ℤ ℚ ≅ H^i(X^an; ℚ)` is
stated as `IsBaseChange ℚ` of `MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) i`,
viewed as a `ℤ`-linear map.

The rational homology is finite-dimensional because extension of scalars to `ℚ` carries the
integral homotopy equivalence to one with a complex of finite-dimensional `ℚ`-vector spaces. The
cycle rank `MMP.Analytic.cycleRank` and the boxed rank `MMP.Fourfold.boxedSurfaceRank` are
`Module.finrank`s, so their finiteness is stated as `FiniteDimensional ℚ` of the cycle spans;
these sit in Borel–Moore homology, which on the compact space `X^an` is singular homology.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.21 and Theorem 2.27.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology
open MMP.Analytic.ComplexPoints
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open MMP (IsComplexScheme)

namespace MMP.Proof_lem_mmp_projective_finite_cochains

open MMP.Analytic MMP.Analytic.ComplexPoints
open MMP MMP.SingularChain MMP.SingularCochain

section cochains

variable {Y : TopCat.{0}} (R : Type) [CommRing R]

/-- The `ℤ`-linear map on integral singular chains extending a function on simplices. -/
private noncomputable def extend (M : Type) [AddCommGroup M] [Module ℤ M] {n : ℕ}
    (ψ : Simplex Y n → M) : (chainCx ℤ Y).X n →ₗ[ℤ] M :=
  (Sigma.desc fun σ ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M (ψ (simplexEquiv Y n σ))) :
    (chainCx ℤ Y).X n ⟶ ModuleCat.of ℤ M).hom

/-- The generator of the chains given by a simplex. -/
private noncomputable abbrev gen {n : ℕ} (τ : Simplex Y n) : (chainCx ℤ Y).X n :=
  (Sigma.ι (fun _ ↦ ModuleCat.of ℤ ℤ) ((simplexEquiv Y n).symm τ)).hom 1

private lemma extend_gen {M : Type} [AddCommGroup M] [Module ℤ M] {n : ℕ} (ψ : Simplex Y n → M)
    (τ : Simplex Y n) : extend M ψ (gen τ) = ψ τ := by
  change (Sigma.ι (fun _ ↦ ModuleCat.of ℤ ℤ) ((simplexEquiv Y n).symm τ) ≫
    (Sigma.desc fun σ ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M (ψ (simplexEquiv Y n σ))) :
      (chainCx ℤ Y).X n ⟶ ModuleCat.of ℤ M)).hom 1 = _
  rw [Sigma.ι_desc]
  exact @one_smul ℤ M _ Module.toDistribMulAction.toMulAction _

/-- The singular boundary of a generator is the alternating sum of its faces. -/
private lemma d_gen {n : ℕ} (τ : Simplex Y (n + 1)) :
    ((chainCx ℤ Y).d (n + 1) n).hom (gen τ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • gen (τ.comp (face n i)) := by
  change (Sigma.ι (fun _ ↦ ModuleCat.of ℤ ℤ) ((simplexEquiv Y (n + 1)).symm τ) ≫
    (chainCx ℤ Y).d (n + 1) n).hom 1 = _
  erw [ι_chainCx_d, ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun s => ((-1 : ℤ) ^ (i : ℕ) • Sigma.ι (fun _ ↦ ModuleCat.of ℤ ℤ) s).hom 1)
    (simplexEquiv_symm_δ Y n τ i)

private lemma linearMap_ext {M : Type} [AddCommGroup M] [Module ℤ M] {n : ℕ}
    {L L' : (chainCx ℤ Y).X n →ₗ[ℤ] M} (h : ∀ τ : Simplex Y n, L (gen τ) = L' (gen τ)) :
    L = L' := by
  have : (ModuleCat.ofHom L : (chainCx ℤ Y).X n ⟶ ModuleCat.of ℤ M) = ModuleCat.ofHom L' := by
    refine Sigma.hom_ext _ _ fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    have := h (simplexEquiv Y n σ)
    simp only [gen, Equiv.symm_apply_apply] at this
    exact this
  exact congrArg ModuleCat.Hom.hom this

private lemma extend_injective {n : ℕ} : Function.Injective (extend R (Y := Y) (n := n)) :=
  fun ψ ψ' h ↦ funext fun τ ↦ by rw [← extend_gen ψ, ← extend_gen ψ', h]

private lemma extend_add {n : ℕ} (ψ ψ' : Simplex Y n → R) :
    extend R (ψ + ψ') = extend R ψ + extend R ψ' :=
  linearMap_ext fun τ ↦ by simp [extend_gen]

private lemma extend_coboundary {n : ℕ} (ψ : Simplex Y n → R) :
    extend R (coboundary R n ψ) = (extend R ψ).comp ((chainCx ℤ Y).d (n + 1) n).hom := by
  refine linearMap_ext fun τ ↦ ?_
  rw [extend_gen, coboundary_apply, LinearMap.comp_apply, d_gen, map_sum]
  simp [extend_gen]

/-- Cochains vanishing on the empty set are all cochains. -/
private lemma mem_vanishing_univ_compl {n : ℕ} (ψ : Simplex Y n → R) :
    ψ ∈ vanishing R n (Set.univᶜ : Set Y) := fun σ hσ ↦
  absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp)

private lemma mem_relCocycles_iff {n : ℕ} (ψ : Simplex Y n → R) :
    ψ ∈ relCocycles R (Set.univᶜ : Set Y) n ↔ coboundary R n ψ = 0 :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨mem_vanishing_univ_compl R ψ, h⟩⟩

private lemma coboundary_mem_relCoboundaries {n : ℕ} (χ : Simplex Y n → R) :
    coboundary R n χ ∈ relCoboundaries R (Set.univᶜ : Set Y) (n + 1) :=
  ⟨χ, mem_vanishing_univ_compl R χ, rfl⟩

private lemma extend_zero {n : ℕ} : extend R (0 : Simplex Y n → R) = 0 :=
  linearMap_ext fun τ ↦ by simp [extend_gen]

private lemma extend_comp_d_eq_zero {n : ℕ} {ψ : Simplex Y (n + 1) → R}
    (hψ : coboundary R (n + 1) ψ = 0) :
    (extend R ψ).comp ((chainCx ℤ Y).d (n + 2) (n + 1)).hom = 0 := by
  rw [← extend_coboundary, hψ, extend_zero]

end cochains

section transfer

variable {Y : TopCat.{0}} (R : Type) [CommRing R] {C : ChainComplex (ModuleCat.{0} ℤ) ℕ}
  (e : HomotopyEquiv C (chainCx ℤ Y))

/-- The cochain `ψ ∘ f ∘ g` for a homotopy equivalence `f : C ≃ C_•(Y)` with inverse `g`. -/
private noncomputable def pull {n : ℕ} (ψ : Simplex Y n → R) : Simplex Y n → R :=
  fun τ ↦ extend R ψ ((e.hom.f n).hom ((e.inv.f n).hom (gen τ)))

private lemma extend_pull {n : ℕ} (ψ : Simplex Y n → R) :
    extend R (pull R e ψ) = (extend R ψ).comp ((e.inv ≫ e.hom).f n).hom :=
  linearMap_ext fun τ ↦ by rw [extend_gen]; rfl

private lemma pull_eq_zero_deg {ψ : Simplex Y 0 → R} (hψ : coboundary R 0 ψ = 0) :
    pull R e ψ = ψ := by
  refine extend_injective R ?_
  have hc := e.homotopyInvHomId.comm 0
  rw [dNext_eq_zero _ _ (by simp), prevD_eq _ (j' := 1) (by simp), zero_add] at hc
  rw [extend_pull, hc]
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.comp_add, LinearMap.comp_id]
  rw [← LinearMap.comp_assoc, ← extend_coboundary, hψ, extend_zero, LinearMap.zero_comp,
    zero_add]

private lemma exists_pull_eq_succ {k : ℕ} {ψ : Simplex Y (k + 1) → R}
    (hψ : coboundary R (k + 1) ψ = 0) :
    ∃ χ : Simplex Y k → R, pull R e ψ = ψ + coboundary R k χ := by
  refine ⟨fun τ ↦ extend R ψ ((e.homotopyInvHomId.hom k (k + 1)).hom (gen τ)), ?_⟩
  refine extend_injective R ?_
  have hc := e.homotopyInvHomId.comm (k + 1)
  rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (k + 1) k from rfl),
    prevD_eq _ (show (ComplexShape.down ℕ).Rel (k + 2) (k + 1) from rfl)] at hc
  rw [extend_pull, hc, extend_add, extend_coboundary]
  have hχ : extend R (fun τ ↦ extend R ψ ((e.homotopyInvHomId.hom k (k + 1)).hom (gen τ))) =
      (extend R ψ).comp (e.homotopyInvHomId.hom k (k + 1)).hom :=
    linearMap_ext fun τ ↦ by rw [extend_gen]; rfl
  rw [hχ]
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.comp_add, LinearMap.comp_id]
  rw [← LinearMap.comp_assoc (f := (e.homotopyInvHomId.hom (k + 1) (k + 2)).hom),
    extend_comp_d_eq_zero R hψ, LinearMap.zero_comp, add_zero]
  exact add_comm _ _

/-- A cocycle of `Y` restricts along `f` to a cocycle of `C`. -/
private lemma extend_comp_hom_comp_d {n : ℕ} {ψ : Simplex Y n → R}
    (hψ : coboundary R n ψ = 0) :
    ((extend R ψ).comp (e.hom.f n).hom).comp (C.d (n + 1) n).hom = 0 := by
  rw [LinearMap.comp_assoc, ← ModuleCat.hom_comp, ← e.hom.comm, ModuleCat.hom_comp,
    ← LinearMap.comp_assoc, ← extend_coboundary, hψ, extend_zero, LinearMap.zero_comp]

/-- The cochain of `Y` obtained from a cochain of `C` along `g`. -/
private noncomputable def push {n : ℕ} (φ : C.X n →ₗ[ℤ] R) : Simplex Y n → R :=
  fun τ ↦ φ ((e.inv.f n).hom (gen τ))

private lemma extend_push {n : ℕ} (φ : C.X n →ₗ[ℤ] R) :
    extend R (push R e φ) = φ.comp (e.inv.f n).hom :=
  linearMap_ext fun τ ↦ by rw [extend_gen]; rfl

private lemma coboundary_push {n : ℕ} (φ : C.X (n + 1) →ₗ[ℤ] R) (φ' : C.X n →ₗ[ℤ] R)
    (h : φ = φ'.comp (C.d (n + 1) n).hom) :
    push R e φ = coboundary R n (push R e φ') := by
  refine extend_injective R ?_
  rw [extend_push, extend_coboundary, extend_push, h, LinearMap.comp_assoc, LinearMap.comp_assoc,
    ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, e.inv.comm]

private lemma coboundary_push_eq_zero {n : ℕ} {φ : C.X n →ₗ[ℤ] R}
    (h : φ.comp (C.d (n + 1) n).hom = 0) : coboundary R n (push R e φ) = 0 := by
  refine extend_injective R ?_
  rw [extend_coboundary, extend_push, extend_zero, LinearMap.comp_assoc, ← ModuleCat.hom_comp,
    ← e.inv.comm, ModuleCat.hom_comp, ← LinearMap.comp_assoc, h, LinearMap.zero_comp]

private lemma pull_sub_mem_relCoboundaries {n : ℕ} {ψ : Simplex Y n → R}
    (hψ : coboundary R n ψ = 0) :
    pull R e ψ - ψ ∈ relCoboundaries R (Set.univᶜ : Set Y) n := by
  cases n with
  | zero =>
    rw [pull_eq_zero_deg R e hψ, sub_self]
    exact zero_mem _
  | succ k =>
    obtain ⟨χ, hχ⟩ := exists_pull_eq_succ R e hψ
    rw [hχ, add_sub_cancel_left]
    exact coboundary_mem_relCoboundaries R χ

end transfer

section finiteness

variable {Y : TopCat.{0}} (R : Type) [CommRing R] {C : ChainComplex (ModuleCat.{0} ℤ) ℕ}
  (e : HomotopyEquiv C (chainCx ℤ Y))

/-- `R`-valued linear forms on a finitely generated abelian group form a finite `R`-module, for
`R` Noetherian: they embed into the forms on a free module `ℤ^b` surjecting onto it. -/
private lemma finite_linearMap_int [IsNoetherianRing R] (M : Type) [AddCommGroup M]
    [Module ℤ M] [Module.Finite ℤ M] : Module.Finite R (M →ₗ[ℤ] R) := by
  obtain ⟨b, π, hπ⟩ := Module.Finite.exists_fin' ℤ M
  exact Module.Finite.of_injective (LinearMap.lcomp R R π) fun φ ψ h ↦ LinearMap.ext fun m ↦ by
    obtain ⟨x, rfl⟩ := hπ m
    exact LinearMap.congr_fun h x

/-- `φ ↦ φ ∘ g` on `R`-valued cochains of `C`. -/
private noncomputable def pushLinear (n : ℕ) : (C.X n →ₗ[ℤ] R) →ₗ[R] (Simplex Y n → R) where
  toFun φ := push R e φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The class of `φ ∘ g` for an `R`-valued cocycle `φ` of `C`. -/
private noncomputable def cocycleClass (n : ℕ) :
    LinearMap.ker (LinearMap.lcomp R R (C.d (n + 1) n).hom) →ₗ[R]
      relCohomology R (Set.univᶜ : Set Y) n :=
  (Submodule.mkQ _).comp (LinearMap.codRestrict (relCocycles R (Set.univᶜ : Set Y) n)
    ((pushLinear R e n).comp (Submodule.subtype _)) fun φ ↦
      (mem_relCocycles_iff R _).2 (coboundary_push_eq_zero R e (LinearMap.mem_ker.1 φ.2)))

private lemma cocycleClass_surjective (n : ℕ) : Function.Surjective (cocycleClass R e n) := by
  intro x
  obtain ⟨⟨ψ, hψ⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hψ' := (mem_relCocycles_iff R ψ).1 hψ
  refine ⟨⟨(extend R ψ).comp (e.hom.f n).hom,
    LinearMap.mem_ker.2 (extend_comp_hom_comp_d R e hψ')⟩, ?_⟩
  exact (Submodule.Quotient.eq _).2 (pull_sub_mem_relCoboundaries R e hψ')

include e in
/-- The singular cohomology of `Y` with coefficients in a Noetherian ring `R` is a finite
`R`-module, when `C_•(Y; ℤ)` is homotopy equivalent to a complex of finitely generated abelian
groups: every class is that of `φ ∘ g` for a cocycle `φ` of the finite `R`-module
`Hom_ℤ(C_n, R)`. -/
private theorem finite_singularCohomology [IsNoetherianRing R] [∀ i, Module.Finite ℤ (C.X i)]
    (n : ℕ) : Module.Finite R (singularCohomology R Y n) := by
  have : Module.Finite R (C.X n →ₗ[ℤ] R) :=
    @finite_linearMap_int R _ _ (C.X n) _ (C.X n).isModule (‹∀ i, Module.Finite ℤ (C.X i)› n)
  have : IsNoetherian R (C.X n →ₗ[ℤ] R) := isNoetherian_of_isNoetherianRing_of_finite _ _
  have := Module.Finite.of_surjective _ (cocycleClass_surjective R e n)
  exact Module.Finite.equiv (relativeSingularCohomologyEquiv R (Set.univᶜ : Set Y) n).symm

end finiteness

section rational

/-- A rational-valued linear form on a finitely generated abelian group has an integral
nonzero multiple. -/
private lemma exists_intCast_eq_mul {M : Type} [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
    (φ : M →ₗ[ℤ] ℚ) : ∃ s : ℤ, s ≠ 0 ∧ ∃ φ' : M →ₗ[ℤ] ℤ, ∀ m, (φ' m : ℚ) = s * φ m := by
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := M)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) S (fun m ↦ φ m)
  let I : Submodule ℤ ℚ := LinearMap.range (Algebra.linearMap ℤ ℚ)
  have hI : ∀ m, ((b : ℤ) • φ) m ∈ I := by
    have : Submodule.span ℤ (S : Set M) ≤ I.comap ((b : ℤ) • φ) := by
      rw [Submodule.span_le]
      intro m hm
      obtain ⟨a, ha⟩ := hb m hm
      exact ⟨a, by simpa [Algebra.smul_def] using ha⟩
    intro m
    exact this (hS ▸ Submodule.mem_top)
  have hinj : Function.Injective (Algebra.linearMap ℤ ℚ) := fun a a' h ↦ by
    simpa using h
  refine ⟨b, nonZeroDivisors.coe_ne_zero b,
    (LinearEquiv.ofInjective _ hinj).symm.toLinearMap.comp (LinearMap.codRestrict I _ hI),
    fun m ↦ ?_⟩
  have := LinearEquiv.ofInjective_apply (Algebra.linearMap ℤ ℚ) (h := hinj)
    ((LinearEquiv.ofInjective _ hinj).symm (LinearMap.codRestrict I _ hI m))
  rw [LinearEquiv.apply_symm_apply] at this
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
    show ∀ t : ℤ, (t : ℚ) = Algebra.linearMap ℤ ℚ t from fun t ↦ by simp, ← this,
    LinearMap.codRestrict_apply, LinearMap.smul_apply, zsmul_eq_mul]

variable {Y : TopCat.{0}} {C : ChainComplex (ModuleCat.{0} ℤ) ℕ}
  (e : HomotopyEquiv C (chainCx ℤ Y))

private lemma extend_cochainMap {n : ℕ} (ψ : Simplex Y n → ℤ) (c : (chainCx ℤ Y).X n) :
    extend ℚ (singularCohomology.cochainMap (Int.castRingHom ℚ) n ψ) c = (extend ℤ ψ c : ℚ) := by
  have : extend ℚ (singularCohomology.cochainMap (Int.castRingHom ℚ) n ψ) =
      (Algebra.linearMap ℤ ℚ).comp (extend ℤ ψ) :=
    linearMap_ext fun τ ↦ by simp [extend_gen]
  simp [this]

/-- The change of coefficients `H^n(Y; ℤ) → H^n(Y; ℚ)`, as a `ℤ`-linear map. -/
private noncomputable def coeffMap (Y : TopCat.{0}) (i : ℕ) :
    singularCohomology ℤ Y i →ₗ[ℤ] singularCohomology ℚ Y i :=
  { toFun := singularCohomology.mapCoeff (Int.castRingHom ℚ) (Y := Y) i
    map_add' := map_add _
    map_smul' := fun r x ↦ by
      rw [map_smulₛₗ, eq_intCast, Int.cast_smul_eq_zsmul, RingHom.id_apply] }

private lemma relativeSingularCohomologyEquiv_coeffMap (i : ℕ) (x : singularCohomology ℤ Y i) :
    relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set Y) i (coeffMap Y i x) =
      singularCohomology.relCohomologyMap (Int.castRingHom ℚ) (Set.univᶜ : Set Y) i
        (relativeSingularCohomologyEquiv ℤ (Set.univᶜ : Set Y) i x) := by
  simp [coeffMap, singularCohomology.mapCoeff]

private lemma relCohomologyMap_mk {i : ℕ} (x : relCocycles ℤ (Set.univᶜ : Set Y) i) :
    singularCohomology.relCohomologyMap (Int.castRingHom ℚ) (Set.univᶜ : Set Y) i
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (singularCohomology.relCocyclesMap (Int.castRingHom ℚ) _ i x) :=
  rfl

include e in
private lemma coeffMap_surj [∀ i, Module.Finite ℤ (C.X i)] (i : ℕ)
    (y : singularCohomology ℚ Y i) :
    ∃ x : singularCohomology ℤ Y i × nonZeroDivisors ℤ, x.2 • y = coeffMap Y i x.1 := by
  obtain ⟨⟨ψ, hψ⟩, hy⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set Y) i y)
  have hψ' := (mem_relCocycles_iff ℚ ψ).1 hψ
  obtain ⟨s, hs, φ', hφ'⟩ := exists_intCast_eq_mul ((extend ℚ ψ).comp (e.hom.f i).hom)
  have hφ'd : φ'.comp (C.d (i + 1) i).hom = 0 := by
    ext m
    apply Int.cast_injective (α := ℚ)
    rw [LinearMap.comp_apply, hφ', ← LinearMap.comp_apply,
      extend_comp_hom_comp_d ℚ e hψ']
    simp
  have hc := (mem_relCocycles_iff ℤ (push ℤ e φ')).2 (coboundary_push_eq_zero ℤ e hφ'd)
  refine ⟨((relativeSingularCohomologyEquiv ℤ (Set.univᶜ : Set Y) i).symm
    (Submodule.Quotient.mk ⟨push ℤ e φ', hc⟩), ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩), ?_⟩
  apply (relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set Y) i).injective
  rw [relativeSingularCohomologyEquiv_coeffMap, LinearEquiv.apply_symm_apply,
    relCohomologyMap_mk, Submonoid.smul_def, ← Int.cast_smul_eq_zsmul ℚ, map_smul, ← hy,
    ← Submodule.Quotient.mk_smul]
  refine (Submodule.Quotient.eq _).2 ?_
  have hpush : singularCohomology.cochainMap (Int.castRingHom ℚ) i (push ℤ e φ') =
      (s : ℚ) • pull ℚ e ψ := by
    funext τ
    simp only [singularCohomology.cochainMap_apply, eq_intCast, Pi.smul_apply, smul_eq_mul]
    exact hφ' _
  change (s : ℚ) • ψ - singularCohomology.cochainMap (Int.castRingHom ℚ) i (push ℤ e φ') ∈
    relCoboundaries ℚ (Set.univᶜ : Set Y) i
  rw [hpush, ← smul_sub, ← neg_sub, smul_neg]
  exact neg_mem (Submodule.smul_mem _ _ (pull_sub_mem_relCoboundaries ℚ e hψ'))

include e in
private lemma exists_smul_mem_of_coeffMap_eq_zero [∀ i, Module.Finite ℤ (C.X i)] (i : ℕ)
    (x : singularCohomology ℤ Y i) (hx : coeffMap Y i x = 0) (ψ : Simplex Y i → ℤ)
    (hψ : ψ ∈ relCocycles ℤ (Set.univᶜ : Set Y) i)
    (hxψ : Submodule.Quotient.mk ⟨ψ, hψ⟩ = relativeSingularCohomologyEquiv ℤ (Set.univᶜ : Set Y) i x) :
    ∃ s : ℤ, s ≠ 0 ∧ s • ψ ∈ relCoboundaries ℤ (Set.univᶜ : Set Y) i := by
  have h0 := congrArg (relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set Y) i) hx
  rw [relativeSingularCohomologyEquiv_coeffMap, ← hxψ, map_zero, relCohomologyMap_mk] at h0
  have hmem' := (Submodule.Quotient.mk_eq_zero _).1 h0
  have hmem : singularCohomology.cochainMap (Int.castRingHom ℚ) i ψ ∈
      relCoboundaries ℚ (Set.univᶜ : Set Y) i := hmem'
  cases i with
  | zero =>
    refine ⟨1, one_ne_zero, ?_⟩
    have : singularCohomology.cochainMap (Int.castRingHom ℚ) 0 ψ = 0 := hmem
    have hψ0 : ψ = 0 := funext fun τ ↦ by simpa using congr_fun this τ
    rw [hψ0, smul_zero]
    exact zero_mem _
  | succ k =>
    obtain ⟨χ, -, hχ⟩ := hmem
    obtain ⟨s, hs, χ', hχ'⟩ := exists_intCast_eq_mul ((extend ℚ χ).comp (e.hom.f k).hom)
    have hrel : s • ((extend ℤ ψ).comp (e.hom.f (k + 1)).hom) = χ'.comp (C.d (k + 1) k).hom := by
      ext m
      apply Int.cast_injective (α := ℚ)
      rw [LinearMap.comp_apply, hχ', LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul,
        Int.cast_mul]
      congr 1
      rw [← extend_cochainMap, ← hχ, extend_coboundary, LinearMap.comp_apply,
        LinearMap.comp_apply]
      congr 1
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, e.hom.comm]
      rfl
    refine ⟨s, hs, ?_⟩
    have hspull : push ℤ e (s • ((extend ℤ ψ).comp (e.hom.f (k + 1)).hom)) =
        s • pull ℤ e ψ := rfl
    have : s • ψ = coboundary ℤ k (push ℤ e χ') - s • (pull ℤ e ψ - ψ) := by
      rw [← coboundary_push ℤ e _ χ' hrel, hspull, smul_sub]
      abel
    rw [this]
    exact sub_mem (coboundary_mem_relCoboundaries ℤ _)
      (Submodule.smul_mem _ s (pull_sub_mem_relCoboundaries ℤ e ((mem_relCocycles_iff ℤ ψ).1 hψ)))

include e in
private theorem isBaseChange_coeffMap [∀ i, Module.Finite ℤ (C.X i)] (i : ℕ) :
    IsBaseChange ℚ (coeffMap Y i) := by
  have : IsLocalizedModule (nonZeroDivisors ℤ) (coeffMap Y i) :=
    { map_units := by
        haveI := isLocalizedModule_id (S := nonZeroDivisors ℤ) (M := singularCohomology ℚ Y i) ℚ
        exact IsLocalizedModule.map_units (LinearMap.id)
      surj := coeffMap_surj e i
      exists_of_eq := fun {x₁ x₂} h ↦ by
        obtain ⟨⟨ψ, hψ⟩, hxψ⟩ := Submodule.Quotient.mk_surjective _
          (relativeSingularCohomologyEquiv ℤ (Set.univᶜ : Set Y) i (x₁ - x₂))
        obtain ⟨s, hs, hsψ⟩ := exists_smul_mem_of_coeffMap_eq_zero e i (x₁ - x₂)
          (by rw [map_sub, h, sub_self]) ψ hψ hxψ
        refine ⟨⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩, ?_⟩
        have key : s • (x₁ - x₂) = 0 := by
          apply (relativeSingularCohomologyEquiv ℤ (Set.univᶜ : Set Y) i).injective
          rw [map_zsmul, map_zero, ← hxψ, ← Submodule.mkQ_apply, ← map_zsmul,
            Submodule.mkQ_apply]
          exact (Submodule.Quotient.mk_eq_zero _).2 hsψ
        change (singularCohomology ℤ Y i).isModule.smul s x₁ =
          (singularCohomology ℤ Y i).isModule.smul s x₂
        rw [int_smul_eq_zsmul, int_smul_eq_zsmul, ← sub_eq_zero, ← zsmul_sub]
        exact key }
  exact IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ _

end rational

section polyhedron

/-!
### Singular chains of a finite polyhedron

For a finite geometric simplicial complex `K`, the oriented simplicial chain complex of `K` is
chain homotopy equivalent to the singular chain complex of `|K|`.
-/

open Finsupp Set

section simplicial

variable {V : Type*} [LinearOrder V]

/-- The sign `(-1) ^ #{x ∈ s | x < u}` of a vertex `u` in a finite set `s`. -/
private def sgn (u : V) (s : Finset V) : ℤ := (-1) ^ (s.filter (· < u)).card

private lemma sgn_mul_self (u : V) (s : Finset V) : sgn u s * sgn u s = 1 := by
  rw [sgn, ← pow_add, ← two_mul, pow_mul]
  simp

private lemma sgn_erase_self (u : V) (s : Finset V) : sgn u (s.erase u) = sgn u s := by
  rw [sgn, sgn, Finset.filter_erase, Finset.erase_eq_of_notMem (by simp)]

private lemma sgn_insert_self (u : V) (s : Finset V) : sgn u (insert u s) = sgn u s := by
  rw [sgn, sgn, Finset.filter_insert, if_neg (lt_irrefl u)]

private lemma sgn_erase {u w : V} {s : Finset V} (hu : u ∈ s) :
    sgn w (s.erase u) = if u < w then -sgn w s else sgn w s := by
  rw [sgn, sgn, Finset.filter_erase]
  split_ifs with h
  · rw [Finset.card_erase_of_mem (by simp [hu, h])]
    have : 0 < (s.filter (· < w)).card := Finset.card_pos.2 ⟨u, by simp [hu, h]⟩
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt this
    simp [hk, pow_succ]
  · rw [Finset.erase_eq_of_notMem (by simp [h])]

private lemma sgn_insert {u w : V} {s : Finset V} (hu : u ∉ s) :
    sgn w (insert u s) = if u < w then -sgn w s else sgn w s := by
  have h := sgn_erase (w := w) (Finset.mem_insert_self u s)
  rw [Finset.erase_insert hu] at h
  rw [h]
  split_ifs <;> simp

/-- The ungraded simplicial boundary `∂ s = ∑_{u ∈ s} sgn u s • (s - u)`. -/
private noncomputable def bdS : (Finset V →₀ ℤ) →ₗ[ℤ] (Finset V →₀ ℤ) :=
  linearCombination ℤ fun s ↦ ∑ u ∈ s, sgn u s • single (s.erase u) 1

private lemma bdS_single (s : Finset V) :
    bdS (single s 1) = ∑ u ∈ s, sgn u s • single (s.erase u) (1 : ℤ) := by
  simp [bdS]

private lemma bdS_bdS_single (s : Finset V) : bdS (bdS (single s 1)) = 0 := by
  rw [bdS_single, map_sum]
  simp_rw [map_zsmul, bdS_single, Finset.smul_sum, smul_smul]
  rw [Finset.sum_sigma' s (fun u ↦ s.erase u)
    (fun u w ↦ (sgn u s * sgn w (s.erase u)) • single ((s.erase u).erase w) (1 : ℤ))]
  refine Finset.sum_involution (fun x _ ↦ ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨u, w⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_erase] at hx
    obtain ⟨hu, hwu, hw⟩ := hx
    dsimp only
    rw [Finset.erase_right_comm, ← add_smul, sgn_erase hu, sgn_erase hw]
    rcases lt_or_gt_of_ne hwu with h | h
    · rw [if_neg (not_lt.2 h.le), if_pos h]
      ring_nf
      simp
    · rw [if_pos h, if_neg (not_lt.2 h.le)]
      ring_nf
      simp
  · rintro ⟨u, w⟩ hx _ h
    simp only [Finset.mem_sigma, Finset.mem_erase] at hx
    simp only [Sigma.mk.injEq] at h
    exact hx.2.1 h.1
  · rintro ⟨u, w⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_erase] at hx ⊢
    exact ⟨hx.2.2, hx.2.1.symm, hx.1⟩
  · rintro ⟨u, w⟩ _
    rfl

private lemma bdS_bdS (c : Finset V →₀ ℤ) : bdS (bdS c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, add_zero]
  | single s a =>
    rw [← smul_single_one, map_zsmul, map_zsmul, bdS_bdS_single, smul_zero]

/-- The cone over the vertex `v`: `s ↦ sgn v s • (s + v)` if `v ∉ s`, and `0` otherwise. -/
private noncomputable def coneS (v : V) : (Finset V →₀ ℤ) →ₗ[ℤ] (Finset V →₀ ℤ) :=
  linearCombination ℤ fun s ↦ if v ∈ s then 0 else sgn v s • single (insert v s) 1

private lemma coneS_single (v : V) (s : Finset V) :
    coneS v (single s 1) = if v ∈ s then 0 else sgn v s • single (insert v s) (1 : ℤ) := by
  simp [coneS]

private lemma bdS_coneS_add_single (v : V) (s : Finset V) :
    bdS (coneS v (single s 1)) + coneS v (bdS (single s 1)) = single s 1 := by
  rw [coneS_single, bdS_single, map_sum]
  simp_rw [map_zsmul, coneS_single]
  by_cases hv : v ∈ s
  · rw [if_pos hv, map_zero, zero_add, Finset.sum_eq_single_of_mem v hv]
    · rw [if_neg (by simp), smul_smul, sgn_erase_self, sgn_mul_self, one_smul,
        Finset.insert_erase hv]
    · intro u _ hu
      rw [if_pos (Finset.mem_erase.2 ⟨Ne.symm hu, hv⟩), smul_zero]
  · rw [if_neg hv, map_zsmul, bdS_single, Finset.sum_insert hv, Finset.erase_insert hv,
      smul_add, add_assoc, sgn_insert_self, smul_smul, sgn_mul_self, one_smul, add_eq_left,
      Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun u hu ↦ ?_
    have hvu : v ≠ u := fun h ↦ hv (h ▸ hu)
    rw [if_neg (fun h ↦ hv (Finset.mem_of_mem_erase h)), smul_smul, smul_smul,
      Finset.erase_insert_of_ne hvu, sgn_insert hv, sgn_erase hu, ← add_smul]
    rcases lt_or_gt_of_ne hvu with h | h
    · rw [if_pos h, if_neg (not_lt.2 h.le)]
      ring_nf
      simp
    · rw [if_neg (not_lt.2 h.le), if_pos h]
      ring_nf
      simp

private lemma bdS_coneS_add (v : V) (c : Finset V →₀ ℤ) :
    bdS (coneS v c) + coneS v (bdS c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, add_add_add_comm, hc, hd]
  | single s a =>
    rw [← smul_single_one, map_zsmul, map_zsmul, map_zsmul, map_zsmul, ← smul_add,
      bdS_coneS_add_single]

/-- Induction over the chains supported on a set. -/
private lemma supported_induction {α : Type*} {s : Set α} {p : (α →₀ ℤ) → Prop} (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y)) (hsingle : ∀ a ∈ s, ∀ b : ℤ, p (single a b))
    {c : α →₀ ℤ} (hc : c ∈ supported ℤ ℤ s) : p c := by
  rw [← c.sum_single]
  exact Finset.sum_induction _ p hadd h0 fun a ha ↦ hsingle a ((mem_supported ℤ c).1 hc ha) _

/-- A linear map sending the basis vectors on `s` into a submodule sends the chains supported on
`s` there. -/
private lemma map_mem_of_supported {α M : Type*} [AddCommGroup M] {s : Set α} (L : (α →₀ ℤ) →ₗ[ℤ] M)
    {P : Submodule ℤ M} (h : ∀ a ∈ s, L (single a 1) ∈ P) {c : α →₀ ℤ}
    (hc : c ∈ supported ℤ ℤ s) : L c ∈ P :=
  supported_induction (p := fun c ↦ L c ∈ P) (by simp)
    (fun x y hx hy ↦ by rw [map_add]; exact P.add_mem hx hy)
    (fun a ha b ↦ by rw [← smul_single_one, map_zsmul]; exact P.smul_of_tower_mem b (h a ha)) hc

private lemma map_mem_of_forall_single {α M : Type*} [AddCommGroup M] (L : (α →₀ ℤ) →ₗ[ℤ] M)
    {P : Submodule ℤ M} (h : ∀ a, L (single a 1) ∈ P) (c : α →₀ ℤ) : L c ∈ P :=
  map_mem_of_supported L (s := univ) (fun a _ ↦ h a) (by rw [supported_univ]; trivial)

/-- The augmentation: the sum of the coefficients. -/
private noncomputable def augS : (Finset V →₀ ℤ) →ₗ[ℤ] ℤ := linearCombination ℤ fun _ ↦ 1

private lemma augS_single (s : Finset V) (a : ℤ) : augS (single s a) = a := by simp [augS]

/-- Chains on the members of `L` with `k + 1` vertices. -/
private abbrev facesOn (L : Set (Finset V)) (k : ℕ) : Submodule ℤ (Finset V →₀ ℤ) :=
  supported ℤ ℤ {s | s ∈ L ∧ s.card = k + 1}

private lemma facesOn_mono {L L' : Set (Finset V)} (h : L ⊆ L') (k : ℕ) : facesOn L k ≤ facesOn L' k :=
  supported_mono fun _ hs ↦ ⟨h hs.1, hs.2⟩

private lemma bdS_eq_single_empty {L : Set (Finset V)} {c : Finset V →₀ ℤ} (hc : c ∈ facesOn L 0) :
    bdS c = single ∅ (augS c) := by
  refine supported_induction (p := fun c ↦ bdS c = single ∅ (augS c)) (by simp)
    (fun x y hx hy ↦ by rw [map_add, map_add, hx, hy, single_add]) (fun s hs b ↦ ?_) hc
  obtain ⟨u, rfl⟩ := Finset.card_eq_one.1 hs.2
  rw [← smul_single_one, map_zsmul, map_zsmul, bdS_single, augS_single, Finset.sum_singleton,
    Finset.erase_singleton, sgn, Finset.filter_singleton, if_neg (lt_irrefl u)]
  simp

private lemma bdS_mem_facesOn {L : Set (Finset V)} (hL : ∀ s ∈ L, ∀ t ⊆ s, t.Nonempty → t ∈ L) {k : ℕ}
    {c : Finset V →₀ ℤ} (hc : c ∈ facesOn L (k + 1)) : bdS c ∈ facesOn L k := by
  refine map_mem_of_supported _ (fun s hs ↦ ?_) hc
  rw [bdS_single]
  refine Submodule.sum_mem _ fun u hu ↦ Submodule.smul_of_tower_mem _ _ (single_mem_supported ℤ _ ?_)
  have hcard : (s.erase u).card = k + 1 := by rw [Finset.card_erase_of_mem hu, hs.2]; rfl
  exact ⟨hL s hs.1 _ (Finset.erase_subset u s) (Finset.card_pos.1 (by omega)), hcard⟩

private lemma coneS_mem_facesOn {L : Set (Finset V)} {v : V} (hL : ∀ s ∈ L, insert v s ∈ L) {k : ℕ}
    {c : Finset V →₀ ℤ} (hc : c ∈ facesOn L k) : coneS v c ∈ facesOn L (k + 1) := by
  refine map_mem_of_supported _ (fun s hs ↦ ?_) hc
  rw [coneS_single]
  split_ifs with hv
  · exact zero_mem _
  · exact Submodule.smul_of_tower_mem _ _ (single_mem_supported ℤ _
      ⟨hL s hs.1, by rw [Finset.card_insert_of_notMem hv, hs.2]⟩)

/-- A cone is acyclic in degree `0`. -/
private lemma exists_bdS_eq_of_cone_zero {L : Set (Finset V)} {v : V} (hL : ∀ s ∈ L, insert v s ∈ L)
    {z : Finset V →₀ ℤ} (hz : z ∈ facesOn L 0) (haug : augS z = 0) :
    ∃ w ∈ facesOn L 1, bdS w = z := by
  refine ⟨coneS v z, coneS_mem_facesOn hL hz, ?_⟩
  have h := bdS_coneS_add v z
  rwa [bdS_eq_single_empty hz, haug, single_zero, map_zero, add_zero] at h

/-- A cone is acyclic in positive degrees. -/
private lemma exists_bdS_eq_of_cone {L : Set (Finset V)} {v : V} (hL : ∀ s ∈ L, insert v s ∈ L) {k : ℕ}
    {z : Finset V →₀ ℤ} (hz : z ∈ facesOn L (k + 1)) (hbd : bdS z = 0) :
    ∃ w ∈ facesOn L (k + 2), bdS w = z := by
  refine ⟨coneS v z, coneS_mem_facesOn hL hz, ?_⟩
  have h := bdS_coneS_add v z
  rwa [hbd, map_zero, add_zero] at h

section graded

variable (Kab : Set (Finset V))

/-- The oriented `n`-simplices of `Kab`: its members with `n + 1` vertices. -/
private abbrev Face (n : ℕ) : Type _ := ↥{s : Finset V | s ∈ Kab ∧ s.card = n + 1}

/-- Graded simplicial chains as ungraded ones. -/
private noncomputable def embS (n : ℕ) : (Face Kab n →₀ ℤ) →ₗ[ℤ] (Finset V →₀ ℤ) :=
  (facesOn Kab n).subtype ∘ₗ (supportedEquivFinsupp _).symm.toLinearMap

variable {Kab}

private lemma embS_mem (n : ℕ) (c : Face Kab n →₀ ℤ) : embS Kab n c ∈ facesOn Kab n :=
  ((supportedEquivFinsupp (M := ℤ) (R := ℤ) _).symm c).2

private lemma embS_injective (n : ℕ) : Function.Injective (embS Kab n) :=
  Subtype.val_injective.comp
    (supportedEquivFinsupp (M := ℤ) (R := ℤ) {s : Finset V | s ∈ Kab ∧ s.card = n + 1}).symm.injective

private lemma embS_single (n : ℕ) (s : Face Kab n) (a : ℤ) : embS Kab n (single s a) = single s.1 a :=
  supportedEquivFinsupp_symm_single (M := ℤ) (R := ℤ) _ s a

private lemma embS_toFace (n : ℕ) {c : Finset V →₀ ℤ} (hc : c ∈ facesOn Kab n) :
    embS Kab n (supportedEquivFinsupp (M := ℤ) (R := ℤ) _ ⟨c, hc⟩) = c := by
  simp [embS]

private lemma embS_apply (n : ℕ) (c : Face Kab n →₀ ℤ) (s : Face Kab n) : embS Kab n c s.1 = c s := by
  have := supportedEquivFinsupp_apply_apply (M := ℤ) (R := ℤ) _
    ((supportedEquivFinsupp (M := ℤ) (R := ℤ)
      {s : Finset V | s ∈ Kab ∧ s.card = n + 1}).symm c) s
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

variable (hKab : ∀ s ∈ Kab, ∀ t ⊆ s, t.Nonempty → t ∈ Kab)

include hKab

/-- The simplicial boundary of `Kab`. -/
private noncomputable def dS (n : ℕ) : (Face Kab (n + 1) →₀ ℤ) →ₗ[ℤ] (Face Kab n →₀ ℤ) :=
  (supportedEquivFinsupp _).toLinearMap ∘ₗ LinearMap.codRestrict (facesOn Kab n)
    (bdS ∘ₗ embS Kab (n + 1)) fun c ↦ bdS_mem_facesOn hKab (embS_mem _ c)

private lemma embS_dS (n : ℕ) (c : Face Kab (n + 1) →₀ ℤ) :
    embS Kab n (dS hKab n c) = bdS (embS Kab (n + 1) c) := by
  simp [dS, embS]

private lemma subset_of_mem_support_dS {n : ℕ} {s : Face Kab (n + 1)} {s' : Face Kab n}
    (h : s' ∈ (dS hKab n (single s 1)).support) : s'.1 ⊆ s.1 := by
  rw [Finsupp.mem_support_iff, ← embS_apply, embS_dS, embS_single, bdS_single] at h
  by_contra hne
  apply h
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun u _ ↦ ?_
  rw [Finsupp.smul_apply, Finsupp.single_apply,
    if_neg fun (h : (s.1).erase u = s'.1) ↦ hne (h ▸ Finset.erase_subset u s.1), smul_zero]

private lemma dS_dS (n : ℕ) (c : Face Kab (n + 2) →₀ ℤ) : dS hKab n (dS hKab (n + 1) c) = 0 :=
  embS_injective n (by rw [embS_dS, embS_dS, bdS_bdS, map_zero])

end graded

end simplicial

/-- Linear maps out of a free module agreeing on the basis agree. -/
private lemma lhom_ext_one {α M : Type*} [AddCommGroup M] {L L' : (α →₀ ℤ) →ₗ[ℤ] M}
    (h : ∀ a, L (single a 1) = L' (single a 1)) : L = L' :=
  Finsupp.lhom_ext' fun a ↦ LinearMap.ext_ring (h a)

section carrier

variable {B : ℕ → Type*} (dB : ∀ n, (B (n + 1) →₀ ℤ) →ₗ[ℤ] (B n →₀ ℤ))
  {D : ℕ → Type*} [∀ n, AddCommGroup (D n)] (dD : ∀ n, D (n + 1) →ₗ[ℤ] D n) (ε : D 0 →ₗ[ℤ] ℤ)
  (Φ : ∀ n, B n → ∀ k, Submodule ℤ (D k))

/-- The faces of a basis element have smaller carriers. -/
private def CarrierMono : Prop :=
  ∀ n (b : B (n + 1)), ∀ b' ∈ (dB n (single b 1)).support, ∀ k, Φ n b' k ≤ Φ (n + 1) b k

/-- The carriers are acyclic (augmented). -/
private def CarrierAcyclic : Prop :=
  (∀ n (b : B n) z, z ∈ Φ n b 0 → ε z = 0 → ∃ w ∈ Φ n b 1, dD 0 w = z) ∧
  ∀ n (b : B n) k z, z ∈ Φ n b (k + 1) → dD k z = 0 → ∃ w ∈ Φ n b (k + 2), dD (k + 1) w = z

variable {dB Φ}

private lemma map_dB_mem (hmono : CarrierMono dB Φ) {n k : ℕ} (L : (B n →₀ ℤ) →ₗ[ℤ] D k)
    (hL : ∀ b', L (single b' 1) ∈ Φ n b' k) (b : B (n + 1)) :
    L (dB n (single b 1)) ∈ Φ (n + 1) b k := by
  rw [← (dB n (single b 1)).sum_single, map_finsuppSum]
  refine Submodule.finsuppSum_mem _ _ _ _ fun b' hb' ↦ ?_
  rw [← smul_single_one, map_zsmul]
  exact Submodule.smul_of_tower_mem _ _ (hmono n b b' (Finsupp.mem_support_iff.2 hb') k (hL b'))

variable {dD ε}

/-- **Acyclic carriers, existence.** -/
private theorem exists_chainMap_carried (hdB : ∀ n c, dB n (dB (n + 1) c) = 0)
    (hmono : CarrierMono dB Φ) (hacyc : CarrierAcyclic dD ε Φ) (f0 : B 0 → D 0)
    (hf0 : ∀ b, f0 b ∈ Φ 0 b 0) (hε : ∀ b : B 1, ε (linearCombination ℤ f0 (dB 0 (single b 1))) = 0) :
    ∃ f : ∀ n, (B n →₀ ℤ) →ₗ[ℤ] D n, (∀ b, f 0 (single b 1) = f0 b) ∧
      (∀ n b, f n (single b 1) ∈ Φ n b n) ∧ ∀ n c, dD n (f (n + 1) c) = f n (dB n c) := by
  let P : ∀ n, ((B n →₀ ℤ) →ₗ[ℤ] D n) × ((B (n + 1) →₀ ℤ) →ₗ[ℤ] D (n + 1)) → Prop :=
    fun n p ↦ (∀ b, p.1 (single b 1) ∈ Φ n b n) ∧ (∀ b, p.2 (single b 1) ∈ Φ (n + 1) b (n + 1)) ∧
      ∀ c, dD n (p.2 c) = p.1 (dB n c)
  have step : ∀ n p, P n p → ∃ q : ((B (n + 1) →₀ ℤ) →ₗ[ℤ] D (n + 1)) ×
      ((B (n + 2) →₀ ℤ) →ₗ[ℤ] D (n + 2)), q.1 = p.2 ∧ P (n + 1) q := by
    intro n p hp
    have hz : ∀ b : B (n + 2), ∃ w ∈ Φ (n + 2) b (n + 2),
        dD (n + 1) w = p.2 (dB (n + 1) (single b 1)) := fun b ↦
      hacyc.2 _ b _ _ (map_dB_mem hmono p.2 hp.2.1 b) (by rw [hp.2.2, hdB, map_zero])
    choose w hwΦ hw using hz
    refine ⟨(p.2, linearCombination ℤ w), rfl, hp.2.1, fun b ↦ by simpa using hwΦ b, ?_⟩
    intro c
    have := congrArg (fun L : (B (n + 2) →₀ ℤ) →ₗ[ℤ] D (n + 1) ↦ L c)
      (lhom_ext_one (L := dD (n + 1) ∘ₗ linearCombination ℤ w) (L' := p.2 ∘ₗ dB (n + 1))
        fun b ↦ by simpa using hw b)
    simpa using this
  choose next hnext using step
  have hz1 : ∀ b : B 1, ∃ w ∈ Φ 1 b 1, dD 0 w = linearCombination ℤ f0 (dB 0 (single b 1)) :=
    fun b ↦ hacyc.1 _ b _ (map_dB_mem hmono _ (fun b' ↦ by simpa using hf0 b') b) (hε b)
  choose w1 hw1Φ hw1 using hz1
  have hp0 : P 0 (linearCombination ℤ f0, linearCombination ℤ w1) := by
    refine ⟨fun b ↦ by simpa using hf0 b, fun b ↦ by simpa using hw1Φ b, fun c ↦ ?_⟩
    have := congrArg (fun L : (B 1 →₀ ℤ) →ₗ[ℤ] D 0 ↦ L c)
      (lhom_ext_one (L := dD 0 ∘ₗ linearCombination ℤ w1)
        (L' := linearCombination ℤ f0 ∘ₗ dB 0) fun b ↦ by simpa using hw1 b)
    simpa using this
  let stage : ∀ n, {p // P n p} := fun n ↦ Nat.rec (motive := fun n ↦ {p // P n p})
    ⟨_, hp0⟩ (fun n s ↦ ⟨next n s.1 s.2, (hnext n s.1 s.2).2⟩) n
  refine ⟨fun n ↦ (stage n).1.1, fun b ↦ by simp [stage], fun n b ↦ (stage n).2.1 b,
    fun n c ↦ ?_⟩
  have h1 : (stage (n + 1)).1.1 = (stage n).1.2 := (hnext n (stage n).1 (stage n).2).1
  change dD n ((stage (n + 1)).1.1 c) = (stage n).1.1 (dB n c)
  rw [h1]
  exact (stage n).2.2.2 c

/-- **Acyclic carriers, uniqueness up to homotopy.** -/
private theorem exists_homotopy_carried (hdB : ∀ n c, dB n (dB (n + 1) c) = 0)
    (hmono : CarrierMono dB Φ) (hacyc : CarrierAcyclic dD ε Φ)
    (f g : ∀ n, (B n →₀ ℤ) →ₗ[ℤ] D n)
    (hf : ∀ n c, dD n (f (n + 1) c) = f n (dB n c)) (hg : ∀ n c, dD n (g (n + 1) c) = g n (dB n c))
    (hfΦ : ∀ n b, f n (single b 1) ∈ Φ n b n) (hgΦ : ∀ n b, g n (single b 1) ∈ Φ n b n)
    (hε : ∀ b, ε (f 0 (single b 1)) = ε (g 0 (single b 1))) :
    ∃ h : ∀ n, (B n →₀ ℤ) →ₗ[ℤ] D (n + 1), (∀ n b, h n (single b 1) ∈ Φ n b (n + 1)) ∧
      (∀ c, f 0 c - g 0 c = dD 0 (h 0 c)) ∧
      ∀ n c, f (n + 1) c - g (n + 1) c = dD (n + 1) (h (n + 1) c) + h n (dB n c) := by
  let P : ∀ n, ((B n →₀ ℤ) →ₗ[ℤ] D (n + 1)) × ((B (n + 1) →₀ ℤ) →ₗ[ℤ] D (n + 2)) → Prop :=
    fun n p ↦ (∀ b, p.1 (single b 1) ∈ Φ n b (n + 1)) ∧
      (∀ b, p.2 (single b 1) ∈ Φ (n + 1) b (n + 2)) ∧
      ∀ c, f (n + 1) c - g (n + 1) c = dD (n + 1) (p.2 c) + p.1 (dB n c)
  have step : ∀ n p, P n p → ∃ q : ((B (n + 1) →₀ ℤ) →ₗ[ℤ] D (n + 2)) ×
      ((B (n + 2) →₀ ℤ) →ₗ[ℤ] D (n + 3)), q.1 = p.2 ∧ P (n + 1) q := by
    intro n p hp
    have hz : ∀ b : B (n + 2), ∃ w ∈ Φ (n + 2) b (n + 3), dD (n + 2) w =
        f (n + 2) (single b 1) - g (n + 2) (single b 1) - p.2 (dB (n + 1) (single b 1)) := by
      intro b
      refine hacyc.2 _ b _ _ (sub_mem (sub_mem (hfΦ _ b) (hgΦ _ b))
        (map_dB_mem hmono p.2 hp.2.1 b)) ?_
      rw [map_sub, map_sub, hf, hg, hp.2.2, hdB, map_zero, add_zero, sub_self]
    choose w hwΦ hw using hz
    refine ⟨(p.2, linearCombination ℤ w), rfl, hp.2.1, fun b ↦ by simpa using hwΦ b, ?_⟩
    intro c
    have := congrArg (fun L : (B (n + 2) →₀ ℤ) →ₗ[ℤ] D (n + 2) ↦ L c)
      (lhom_ext_one (L := dD (n + 2) ∘ₗ linearCombination ℤ w)
        (L' := f (n + 2) - g (n + 2) - p.2 ∘ₗ dB (n + 1)) fun b ↦ by simpa using hw b)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply] at this
    dsimp only
    rw [this]
    abel
  choose next hnext using step
  have hz0 : ∀ b : B 0, ∃ w ∈ Φ 0 b 1, dD 0 w = f 0 (single b 1) - g 0 (single b 1) :=
    fun b ↦ hacyc.1 _ b _ (sub_mem (hfΦ 0 b) (hgΦ 0 b)) (by rw [map_sub, hε, sub_self])
  choose w0 hw0Φ hw0 using hz0
  have heq0 : ∀ c, f 0 c - g 0 c = dD 0 (linearCombination ℤ w0 c) := by
    intro c
    have := congrArg (fun L : (B 0 →₀ ℤ) →ₗ[ℤ] D 0 ↦ L c)
      (lhom_ext_one (L := f 0 - g 0) (L' := dD 0 ∘ₗ linearCombination ℤ w0)
        fun b ↦ by simpa using (hw0 b).symm)
    simpa using this
  have hz1 : ∀ b : B 1, ∃ w ∈ Φ 1 b 2, dD 1 w =
      f 1 (single b 1) - g 1 (single b 1) - linearCombination ℤ w0 (dB 0 (single b 1)) := by
    intro b
    refine hacyc.2 _ b _ _ (sub_mem (sub_mem (hfΦ _ b) (hgΦ _ b))
      (map_dB_mem hmono _ (fun b' ↦ by simpa using hw0Φ b') b)) ?_
    rw [map_sub, map_sub, hf, hg, ← heq0, sub_self]
  choose w1 hw1Φ hw1 using hz1
  have hp0 : P 0 (linearCombination ℤ w0, linearCombination ℤ w1) := by
    refine ⟨fun b ↦ by simpa using hw0Φ b, fun b ↦ by simpa using hw1Φ b, fun c ↦ ?_⟩
    have := congrArg (fun L : (B 1 →₀ ℤ) →ₗ[ℤ] D 1 ↦ L c)
      (lhom_ext_one (L := dD 1 ∘ₗ linearCombination ℤ w1)
        (L' := f 1 - g 1 - linearCombination ℤ w0 ∘ₗ dB 0) fun b ↦ by simpa using hw1 b)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply] at this
    dsimp only
    rw [this]
    abel
  let stage : ∀ n, {p // P n p} := fun n ↦ Nat.rec (motive := fun n ↦ {p // P n p})
    ⟨_, hp0⟩ (fun n s ↦ ⟨next n s.1 s.2, (hnext n s.1 s.2).2⟩) n
  refine ⟨fun n ↦ (stage n).1.1, fun n b ↦ (stage n).2.1 b, heq0, fun n c ↦ ?_⟩
  have h1 : (stage (n + 1)).1.1 = (stage n).1.2 := (hnext n (stage n).1 (stage n).2).1
  change _ = dD (n + 1) ((stage (n + 1)).1.1 c) + (stage n).1.1 (dB n c)
  rw [h1]
  exact (stage n).2.2.2 c

end carrier

section geom

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Geometry.SimplicialComplex ℝ E)

/-- The open star of `v`: the points all of whose faces contain `v`. -/
private def openStar (v : E) : Set E := {x | ∀ σ ∈ K.faces, x ∈ convexHull ℝ (σ : Set E) → v ∈ σ}

private lemma isOpen_openStar (hK : K.faces.Finite) (v : E) : IsOpen (openStar K v) := by
  have : (openStar K v)ᶜ = ⋃ σ ∈ {σ | σ ∈ K.faces ∧ v ∉ σ}, convexHull ℝ (σ : Set E) := by
    ext x
    simp only [openStar, mem_compl_iff, mem_setOf_eq, not_forall, mem_iUnion, exists_prop]
    exact ⟨fun ⟨σ, hσ, hx, hv⟩ ↦ ⟨σ, ⟨hσ, hv⟩, hx⟩, fun ⟨σ, ⟨hσ, hv⟩, hx⟩ ↦ ⟨σ, hσ, hx, hv⟩⟩
  rw [← isClosed_compl_iff, this]
  exact (hK.subset fun σ hσ ↦ hσ.1).isClosed_biUnion fun σ _ ↦
    (σ.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed

variable {K}

private lemma exists_minFace {x : E} (hx : x ∈ K.space) : ∃ F ∈ K.faces, x ∈ convexHull ℝ (F : Set E) ∧
    ∀ σ ∈ K.faces, x ∈ convexHull ℝ (σ : Set E) → F ⊆ σ := by
  classical
  have hP : ∃ n, ∃ F ∈ K.faces, x ∈ convexHull ℝ (F : Set E) ∧ F.card = n := by
    obtain ⟨F, hF, hxF⟩ := Geometry.SimplicialComplex.mem_space_iff.1 hx
    exact ⟨_, F, hF, hxF, rfl⟩
  obtain ⟨F, hF, hxF, hcard⟩ := Nat.find_spec hP
  refine ⟨F, hF, hxF, fun σ hσ hxσ ↦ ?_⟩
  have hx' : x ∈ convexHull ℝ ((F ∩ σ : Finset E) : Set E) := by
    rw [Finset.coe_inter]
    exact K.inter_subset_convexHull hF hσ ⟨hxF, hxσ⟩
  have hne : (F ∩ σ).Nonempty := by
    rw [← Finset.coe_nonempty]
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, convexHull_empty] at hx'
    exact hx'
  have hmin := Nat.find_min' hP ⟨F ∩ σ, K.down_closed hF Finset.inter_subset_left hne, hx', rfl⟩
  have := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left (s₁ := F) (s₂ := σ))
    (by omega)
  rw [← this]
  exact Finset.inter_subset_right

end geom

section carriers

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Geometry.SimplicialComplex ℝ E}
  {n : ℕ}

/-- The faces carrying a singular simplex `τ` of `|K|`: faces `ρ` lying in every face whose
closed simplex contains `τ`, such that `ρ` together with all the vertices `v` whose open star
contains `τ` spans a face. -/
private def carrierFaces (τ : Simplex K.space n) : Set (Finset E) :=
  {ρ | ρ ∈ K.faces ∧ (∀ σ ∈ K.faces, (∀ t, (τ t : E) ∈ convexHull ℝ (σ : Set E)) → ρ ⊆ σ) ∧
    ∃ μ ∈ K.faces, ρ ⊆ μ ∧ ∀ v, (∀ t, (τ t : E) ∈ openStar K v) → v ∈ μ}

/-- The union of the closed simplices of the carrier faces. -/
private def carrierSpace (τ : Simplex K.space n) : Set E :=
  ⋃ ρ ∈ carrierFaces τ, convexHull ℝ (ρ : Set E)

private lemma carrierFaces_mono {m : ℕ} {τ : Simplex K.space n} {τ' : Simplex K.space m}
    (h : ∀ t', ∃ t, τ' t' = τ t) : carrierFaces τ' ⊆ carrierFaces τ := by
  rintro ρ ⟨hρ, h1, μ, hμ, hρμ, h2⟩
  refine ⟨hρ, fun σ hσ hτσ ↦ h1 σ hσ fun t' ↦ ?_, μ, hμ, hρμ, fun v hv ↦ h2 v fun t' ↦ ?_⟩
  · obtain ⟨t, ht⟩ := h t'
    rw [ht]
    exact hτσ t
  · obtain ⟨t, ht⟩ := h t'
    rw [ht]
    exact hv t

private lemma carrierSpace_mono {m : ℕ} {τ : Simplex K.space n} {τ' : Simplex K.space m}
    (h : ∀ t', ∃ t, τ' t' = τ t) : carrierSpace τ' ⊆ carrierSpace τ :=
  biUnion_subset_biUnion_left (carrierFaces_mono h)

private lemma insert_mem_carrierFaces [DecidableEq E] {τ : Simplex K.space n} {v : E}
    (hv : ∀ t, (τ t : E) ∈ openStar K v) {ρ : Finset E} (hρ : ρ ∈ carrierFaces τ) :
    insert v ρ ∈ carrierFaces τ := by
  obtain ⟨-, h1, μ, hμ, hρμ, h2⟩ := hρ
  have hvμ := h2 v hv
  refine ⟨K.down_closed hμ (Finset.insert_subset hvμ hρμ) (Finset.insert_nonempty _ _),
    fun σ hσ hτσ ↦ Finset.insert_subset (hv (stdSimplex.vertex 0) σ hσ (hτσ _)) (h1 σ hσ hτσ),
    μ, hμ, Finset.insert_subset hvμ hρμ, h2⟩

private lemma minFace_mem_carrierFaces {τ : Simplex K.space n} (t : stdSimplex ℝ (Fin (n + 1))) :
    ∃ F ∈ carrierFaces τ, (τ t : E) ∈ convexHull ℝ (F : Set E) := by
  obtain ⟨F, hF, hxF, hmin⟩ := exists_minFace (τ t).2
  exact ⟨F, ⟨hF, fun σ hσ hτσ ↦ hmin σ hσ (hτσ t), F, hF, subset_rfl,
    fun v hv ↦ hv t F hF hxF⟩, hxF⟩

private lemma singleton_mem_carrierFaces {τ : Simplex K.space n} {v : E}
    (hv : ∀ t, (τ t : E) ∈ openStar K v) : {v} ∈ carrierFaces τ := by
  classical
  obtain ⟨F, ⟨hF, h1, μ, hμ, hFμ, h2⟩, -⟩ := minFace_mem_carrierFaces (τ := τ) (stdSimplex.vertex 0)
  refine ⟨K.down_closed hμ (Finset.singleton_subset_iff.2 (h2 v hv)) (Finset.singleton_nonempty v),
    fun σ hσ hτσ ↦ Finset.singleton_subset_iff.2 (hv (stdSimplex.vertex 0) σ hσ (hτσ _)),
    μ, hμ, Finset.singleton_subset_iff.2 (h2 v hv), h2⟩

private lemma subset_of_mem_carrierFaces {τ : Simplex K.space n} {s : Finset E} (hs : s ∈ K.faces)
    (hτs : ∀ t, (τ t : E) ∈ convexHull ℝ (s : Set E)) {ρ : Finset E} (hρ : ρ ∈ carrierFaces τ) :
    ρ ⊆ s :=
  hρ.2.1 s hs hτs

private lemma mem_carrierSpace (τ : Simplex K.space n) (t : stdSimplex ℝ (Fin (n + 1))) :
    (τ t : E) ∈ carrierSpace τ := by
  obtain ⟨F, hF, hxF⟩ := minFace_mem_carrierFaces (τ := τ) t
  exact mem_biUnion hF hxF

private lemma carrierSpace_subset (τ : Simplex K.space n) : carrierSpace τ ⊆ K.space :=
  iUnion₂_subset fun ρ hρ ↦ K.convexHull_subset_space hρ.1

private lemma starConvex_carrierSpace {τ : Simplex K.space n} {v : E}
    (hv : ∀ t, (τ t : E) ∈ openStar K v) : StarConvex ℝ v (carrierSpace τ) := by
  classical
  intro y hy a b ha hb hab
  obtain ⟨ρ, hρ, hyρ⟩ := mem_iUnion₂.1 hy
  refine mem_biUnion (insert_mem_carrierFaces hv hρ) ?_
  exact convex_convexHull ℝ _ (subset_convexHull ℝ _ (by simp))
    (convexHull_mono (by simp [Set.subset_insert]) hyρ) ha hb hab

end carriers

section transfer

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Set E}

/-- The inclusion of a subspace. -/
private def incl (A : Set E) : C(A, E) := ⟨Subtype.val, continuous_subtype_val⟩

private lemma postcomp_incl_injective (n : ℕ) : Function.Injective (postcomp ℤ (incl A) n) :=
  mapDomain_injective fun σ σ' h ↦ ContinuousMap.ext fun t ↦
    Subtype.ext (congrArg (fun f : C(stdSimplex ℝ (Fin (n + 1)), E) ↦ f t) h)

private lemma exists_postcomp_incl_eq {n : ℕ} {C : Set E} (hC : C ⊆ A) {w : Chain ℤ E n}
    (hw : w ∈ inside ℤ n C) :
    ∃ w' ∈ inside ℤ n (Subtype.val ⁻¹' C : Set A), postcomp ℤ (incl A) n w' = w := by
  rw [inside, ← w.sum_single] at *
  refine Finset.sum_induction _ (fun w ↦ ∃ w' ∈ inside ℤ n (Subtype.val ⁻¹' C : Set A),
    postcomp ℤ (incl A) n w' = w) ?_ ⟨0, zero_mem _, map_zero _⟩ fun σ hσ ↦ ?_
  · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, map_add _ _ _⟩
  · have hσC : range σ ⊆ C := (mem_supported ℤ w).1 (by rwa [w.sum_single] at hw) hσ
    let σ' : Simplex A n := ⟨fun t ↦ ⟨σ t, hC (hσC ⟨t, rfl⟩)⟩, by fun_prop⟩
    refine ⟨single σ' (w σ), single_mem_supported ℤ _ ?_, ?_⟩
    · rintro _ ⟨t, rfl⟩
      exact hσC ⟨t, rfl⟩
    · rw [postcomp_single]
      rfl

private lemma postcomp_incl_mem_inside {n : ℕ} {C : Set E} {c : Chain ℤ A n}
    (hc : c ∈ inside ℤ n (Subtype.val ⁻¹' C : Set A)) : postcomp ℤ (incl A) n c ∈ inside ℤ n C :=
  postcomp_mem_inside _ (fun _ h ↦ h) hc

private lemma aug_postcomp {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] (f : C(Y, Z)) {n : ℕ}
    (c : Chain ℤ Y n) : aug ℤ n (postcomp ℤ f n c) = aug ℤ n c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, map_add, hc, hd]
  | single σ a => rw [postcomp_single, aug_single, aug_single]

/-- A star-shaped subset of a subspace is acyclic, in the chains of the subspace. -/
private lemma exists_bd_eq_of_starConvex_of_subset {C : Set E} {p : E} (hCA : C ⊆ A)
    (hC : StarConvex ℝ p C) {m : ℕ} {c : Chain ℤ A (m + 1)}
    (hc : c ∈ inside ℤ (m + 1) (Subtype.val ⁻¹' C : Set A)) (hbd : bd ℤ m c = 0) :
    ∃ w ∈ inside ℤ (m + 2) (Subtype.val ⁻¹' C : Set A), bd ℤ (m + 1) w = c := by
  obtain ⟨w, hw, hbw⟩ := exists_bd_eq_of_starConvex hC (postcomp_incl_mem_inside hc)
    (by rw [← postcomp_bd, hbd, map_zero])
  obtain ⟨w', hw', rfl⟩ := exists_postcomp_incl_eq hCA hw
  exact ⟨w', hw', postcomp_incl_injective _ (by rw [postcomp_bd, hbw])⟩

private lemma exists_bd_eq_of_starConvex_of_subset_zero {C : Set E} {p : E} (hCA : C ⊆ A)
    (hC : StarConvex ℝ p C) {c : Chain ℤ A 0}
    (hc : c ∈ inside ℤ 0 (Subtype.val ⁻¹' C : Set A)) (haug : aug ℤ 0 c = 0) :
    ∃ w ∈ inside ℤ 1 (Subtype.val ⁻¹' C : Set A), bd ℤ 0 w = c := by
  obtain ⟨w, hw, hbw⟩ := exists_bd_eq_of_starConvex_zero hC (postcomp_incl_mem_inside hc)
    (by rw [aug_postcomp, haug])
  obtain ⟨w', hw', rfl⟩ := exists_postcomp_incl_eq hCA hw
  exact ⟨w', hw', postcomp_incl_injective _ (by rw [postcomp_bd, hbw])⟩

end transfer

section smallInside

variable {Y : Type*} [TopologicalSpace Y]

private lemma inside_eq_small_singleton (n : ℕ) (U : Set Y) : inside ℤ n U = small ℤ n {U} := by
  simp only [inside, SingularChain.small, mem_singleton_iff, exists_eq_left]

private lemma homotopyUpTo_mem_inside {m n : ℕ} {U : Set Y} {c : Chain ℤ Y n}
    (hc : c ∈ inside ℤ n U) : homotopyUpTo ℤ m n c ∈ inside ℤ (n + 1) U := by
  rw [inside_eq_small_singleton] at hc ⊢
  simp only [homotopyUpTo]
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ ↦ subdivHomotopy_mem_small (subdiv_pow_mem_small i hc)

private lemma smallHomotopy_mem_inside (𝒰 : Set (Set Y)) {n : ℕ} {U : Set Y} {c : Chain ℤ Y n}
    (hc : c ∈ inside ℤ n U) : smallHomotopy ℤ 𝒰 n c ∈ inside ℤ (n + 1) U :=
  VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
    rw [smallHomotopy_single]
    exact homotopyUpTo_mem_inside (single_mem_supported ℤ _ hσ)) hc

private lemma smallChainMap_mem_inside (𝒰 : Set (Set Y)) {n : ℕ} {U : Set Y} {c : Chain ℤ Y n}
    (hc : c ∈ inside ℤ n U) : smallChainMap ℤ 𝒰 n c ∈ inside ℤ n U := by
  cases n with
  | zero =>
    rw [smallChainMap_zero]
    exact sub_mem hc (bd_mem_inside (smallHomotopy_mem_inside 𝒰 hc))
  | succ n =>
    rw [smallChainMap_succ]
    exact sub_mem (sub_mem hc (bd_mem_inside (smallHomotopy_mem_inside 𝒰 hc)))
      (smallHomotopy_mem_inside 𝒰 (bd_mem_inside hc))

private lemma aug_smallChainMap_zero (𝒰 : Set (Set Y)) (c : Chain ℤ Y 0) :
    aug ℤ 0 (smallChainMap ℤ 𝒰 0 c) = aug ℤ 0 c := by
  rw [smallChainMap_zero, map_sub, aug_bd_zero, sub_zero]

end smallInside

section affine

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine simplex `t ↦ ∑ i, t i • w i` with vertices `w`. -/
private def affineMap {n : ℕ} (w : Fin (n + 1) → E) : C(stdSimplex ℝ (Fin (n + 1)), E) :=
  ⟨fun t ↦ ∑ i, (t i) • w i, by
    refine continuous_finset_sum _ fun i _ ↦ Continuous.smul ?_ continuous_const
    exact (continuous_apply i).comp continuous_subtype_val⟩

private lemma affineMap_apply {n : ℕ} (w : Fin (n + 1) → E) (t : stdSimplex ℝ (Fin (n + 1))) :
    affineMap w t = ∑ i, (t i) • w i := rfl

private lemma affineMap_comp_face {n : ℕ} (w : Fin (n + 2) → E) (i : Fin (n + 2)) :
    (affineMap w).comp (face n i) = affineMap (w ∘ i.succAbove) := by
  classical
  ext t
  simp only [ContinuousMap.comp_apply, affineMap_apply, face, ContinuousMap.coe_mk,
    stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Function.comp_apply, Finset.sum_smul]
  exact Finset.sum_fiberwise_of_maps_to (g := i.succAbove) (fun _ _ ↦ Finset.mem_univ _)
    (fun j ↦ t j • w (i.succAbove j)) |>.symm.trans (Finset.sum_congr rfl fun k _ ↦
      Finset.sum_congr (by ext; simp) fun j hj ↦ by
        rw [(Finset.mem_filter.1 hj).2]) |>.symm

private lemma affineMap_mem_convexHull {n : ℕ} (w : Fin (n + 1) → E) (t : stdSimplex ℝ (Fin (n + 1))) :
    affineMap w t ∈ convexHull ℝ (range w) :=
  (convex_convexHull ℝ _).sum_mem (fun i _ ↦ stdSimplex.zero_le t i) (stdSimplex.sum_eq_one t)
    fun i _ ↦ subset_convexHull ℝ _ ⟨i, rfl⟩

variable [LinearOrder E] (K : Geometry.SimplicialComplex ℝ E)

/-- The affine singular simplex of a face, with its vertices in increasing order. -/
private def affSimplex {n : ℕ} (s : Finset E) (hs : s ∈ K.faces) (hc : s.card = n + 1) :
    Simplex K.space n :=
  ⟨fun t ↦ ⟨affineMap (s.orderEmbOfFin hc) t, K.convexHull_subset_space hs (by
      have := affineMap_mem_convexHull (s.orderEmbOfFin hc) t
      rwa [Finset.range_orderEmbOfFin] at this)⟩,
    by fun_prop⟩

private lemma affSimplex_mem_convexHull {n : ℕ} (s : Finset E) (hs : s ∈ K.faces) (hc : s.card = n + 1)
    (t : stdSimplex ℝ (Fin (n + 1))) : (affSimplex K s hs hc t : E) ∈ convexHull ℝ (s : Set E) := by
  have := affineMap_mem_convexHull (s.orderEmbOfFin hc) t
  rwa [Finset.range_orderEmbOfFin] at this

variable {K} in
private lemma orderEmbOfFin_erase {n : ℕ} {s : Finset E} (hc : s.card = n + 2) (i : Fin (n + 2))
    (hc' : (s.erase (s.orderEmbOfFin hc i)).card = n + 1) :
    ⇑((s.erase (s.orderEmbOfFin hc i)).orderEmbOfFin hc') =
      ⇑(s.orderEmbOfFin hc) ∘ i.succAbove := by
  refine (Finset.orderEmbOfFin_unique hc' (fun j ↦ ?_)
    ((s.orderEmbOfFin hc).strictMono.comp (Fin.strictMono_succAbove i))).symm
  refine Finset.mem_erase.2 ⟨fun h ↦ Fin.succAbove_ne i j ((s.orderEmbOfFin hc).injective h),
    Finset.orderEmbOfFin_mem _ _ _⟩

variable {K} in
private lemma sgn_orderEmbOfFin {k : ℕ} {s : Finset E} (hc : s.card = k) (i : Fin k) :
    sgn (s.orderEmbOfFin hc i) s = (-1) ^ (i : ℕ) := by
  rw [sgn]
  congr 1
  have : s.filter (· < s.orderEmbOfFin hc i) =
      (Finset.Iio i).map (s.orderEmbOfFin hc).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨j, rfl⟩ : x ∈ Set.range (s.orderEmbOfFin hc) := by
        rwa [Finset.range_orderEmbOfFin]
      exact ⟨j, (s.orderEmbOfFin hc).lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, (s.orderEmbOfFin hc).lt_iff_lt.2 hj⟩
  rw [this, Finset.card_map, Fin.card_Iio]

/-- Simplicial chains as singular chains: a face goes to its affine simplex. -/
private noncomputable def simplicialToSingular (n : ℕ) : (Finset E →₀ ℤ) →ₗ[ℤ] Chain ℤ K.space n := by
  classical
  exact linearCombination ℤ fun s ↦
    if h : s ∈ K.faces ∧ s.card = n + 1 then single (affSimplex K s h.1 h.2) 1 else 0

private lemma simplicialToSingular_single {n : ℕ} {s : Finset E} (hs : s ∈ K.faces)
    (hc : s.card = n + 1) :
    simplicialToSingular K n (single s 1) = single (affSimplex K s hs hc) 1 := by
  simp [simplicialToSingular, hs, hc]

private lemma bd_simplicialToSingular {n : ℕ} {z : Finset E →₀ ℤ} (hz : z ∈ facesOn K.faces (n + 1)) :
    bd ℤ n (simplicialToSingular K (n + 1) z) = simplicialToSingular K n (bdS z) := by
  refine supported_induction (p := fun z ↦ bd ℤ n (simplicialToSingular K (n + 1) z) =
      simplicialToSingular K n (bdS z)) (by simp)
    (fun x y hx hy ↦ by rw [map_add, map_add, map_add, map_add, hx, hy]) (fun s hs b ↦ ?_) hz
  rw [← smul_single_one, map_zsmul, map_zsmul, map_zsmul, map_zsmul]
  congr 1
  have key : ∀ g : E → Chain ℤ K.space n, ∑ x ∈ s, g x = ∑ i, g (s.orderEmbOfFin hs.2 i) := by
    intro g
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ s hs.2]
    rw [Finset.sum_map]
    rfl
  rw [simplicialToSingular_single K hs.1 hs.2, bd_single, bdS_single, map_sum, key]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hc' : (s.erase (s.orderEmbOfFin hs.2 i)).card = n + 1 := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hs.2]
    rfl
  have hf : s.erase (s.orderEmbOfFin hs.2 i) ∈ K.faces :=
    K.down_closed hs.1 (Finset.erase_subset _ _) (Finset.card_pos.1 (by omega))
  rw [map_zsmul, simplicialToSingular_single K hf hc', sgn_orderEmbOfFin]
  congr 2
  ext t
  change affineMap _ (face n i t) = affineMap _ t
  rw [← ContinuousMap.comp_apply, affineMap_comp_face, orderEmbOfFin_erase hs.2 i hc']

end affine

section smallBasis

variable {Y : Type*} [TopologicalSpace Y] (𝒰 : Set (Set Y))

/-- The `𝒰`-small singular `n`-simplices. -/
private abbrev SmallSimplex (n : ℕ) : Type _ := ↥{σ : Simplex Y n | ∃ U ∈ 𝒰, range σ ⊆ U}

/-- Chains on small simplices as singular chains. -/
private noncomputable def inclSm (n : ℕ) : (SmallSimplex 𝒰 n →₀ ℤ) →ₗ[ℤ] Chain ℤ Y n :=
  (small ℤ n 𝒰).subtype ∘ₗ (supportedEquivFinsupp (M := ℤ) (R := ℤ) _).symm.toLinearMap

variable {𝒰}

private lemma inclSm_mem (n : ℕ) (c : SmallSimplex 𝒰 n →₀ ℤ) : inclSm 𝒰 n c ∈ small ℤ n 𝒰 :=
  ((supportedEquivFinsupp (M := ℤ) (R := ℤ) _).symm c).2

private lemma inclSm_injective (n : ℕ) : Function.Injective (inclSm 𝒰 n) :=
  Subtype.val_injective.comp
    (supportedEquivFinsupp (M := ℤ) (R := ℤ) {σ : Simplex Y n | ∃ U ∈ 𝒰, range σ ⊆ U}).symm.injective

private lemma inclSm_single (n : ℕ) (σ : SmallSimplex 𝒰 n) (a : ℤ) :
    inclSm 𝒰 n (single σ a) = single σ.1 a :=
  supportedEquivFinsupp_symm_single (M := ℤ) (R := ℤ) _ σ a

private lemma inclSm_apply (n : ℕ) (c : SmallSimplex 𝒰 n →₀ ℤ) (σ : SmallSimplex 𝒰 n) :
    inclSm 𝒰 n c σ.1 = c σ := by
  have := supportedEquivFinsupp_apply_apply (M := ℤ) (R := ℤ) _
    ((supportedEquivFinsupp (M := ℤ) (R := ℤ)
      {σ : Simplex Y n | ∃ U ∈ 𝒰, range σ ⊆ U}).symm c) σ
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

private lemma bd_mem_small {n : ℕ} {c : Chain ℤ Y (n + 1)} (hc : c ∈ small ℤ (n + 1) 𝒰) :
    bd ℤ n c ∈ small ℤ n 𝒰 :=
  VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
    obtain ⟨U, hU, hσU⟩ := hσ
    rw [bd_single]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (single_mem_supported ℤ _ ?_)
    exact ⟨U, hU, fun _ ⟨t, ht⟩ ↦ hσU ⟨_, ht⟩⟩) hc

variable (𝒰) in
/-- The boundary of small chains. -/
private noncomputable def dSm (n : ℕ) : (SmallSimplex 𝒰 (n + 1) →₀ ℤ) →ₗ[ℤ] (SmallSimplex 𝒰 n →₀ ℤ) :=
  (supportedEquivFinsupp (M := ℤ) (R := ℤ) _).toLinearMap ∘ₗ LinearMap.codRestrict (small ℤ n 𝒰)
    (bd ℤ n ∘ₗ inclSm 𝒰 (n + 1)) fun c ↦ bd_mem_small (inclSm_mem _ c)

private lemma inclSm_dSm (n : ℕ) (c : SmallSimplex 𝒰 (n + 1) →₀ ℤ) :
    inclSm 𝒰 n (dSm 𝒰 n c) = bd ℤ n (inclSm 𝒰 (n + 1) c) := by
  simp [dSm, inclSm]

private lemma dSm_dSm (n : ℕ) (c : SmallSimplex 𝒰 (n + 2) →₀ ℤ) : dSm 𝒰 n (dSm 𝒰 (n + 1) c) = 0 :=
  inclSm_injective n (by rw [inclSm_dSm, inclSm_dSm, bd_bd, map_zero])

private lemma mem_support_dSm {n : ℕ} {σ : SmallSimplex 𝒰 (n + 1)} {τ : SmallSimplex 𝒰 n}
    (h : τ ∈ (dSm 𝒰 n (single σ 1)).support) : ∃ i, τ.1 = σ.1.comp (face n i) := by
  classical
  rw [Finsupp.mem_support_iff, ← inclSm_apply, inclSm_dSm, inclSm_single, bd_single] at h
  by_contra hne
  simp only [not_exists] at hne
  apply h
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg fun h ↦ hne i h.symm, smul_zero]

private lemma inclSm_mem_inside {n : ℕ} {U : Set Y} {c : SmallSimplex 𝒰 n →₀ ℤ}
    (hc : inclSm 𝒰 n c ∈ inside ℤ n U) : c ∈ supported ℤ ℤ {σ | range σ.1 ⊆ U} := by
  intro σ hσ
  rw [Finset.mem_coe, Finsupp.mem_support_iff, ← inclSm_apply] at hσ
  exact hc (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hσ))

variable (h𝒰 : ∀ U ∈ 𝒰, IsOpen U) (hcov : ⋃₀ 𝒰 = univ)

include h𝒰 hcov

variable (𝒰) in
/-- Hatcher's small-chain map, landing in the small chains. -/
private noncomputable def toSmall (n : ℕ) : Chain ℤ Y n →ₗ[ℤ] (SmallSimplex 𝒰 n →₀ ℤ) :=
  (supportedEquivFinsupp (M := ℤ) (R := ℤ) _).toLinearMap ∘ₗ LinearMap.codRestrict (small ℤ n 𝒰)
    (smallChainMap ℤ 𝒰 n) fun c ↦ smallChainMap_mem_small h𝒰 n (by rw [hcov]; exact mem_inside_univ c)

private lemma inclSm_toSmall (n : ℕ) (c : Chain ℤ Y n) :
    inclSm 𝒰 n (toSmall 𝒰 h𝒰 hcov n c) = smallChainMap ℤ 𝒰 n c := by
  simp [toSmall, inclSm]

private lemma dSm_toSmall (n : ℕ) (c : Chain ℤ Y (n + 1)) :
    dSm 𝒰 n (toSmall 𝒰 h𝒰 hcov (n + 1) c) = toSmall 𝒰 h𝒰 hcov n (bd ℤ n c) :=
  inclSm_injective n (by rw [inclSm_dSm, inclSm_toSmall, inclSm_toSmall, bd_smallChainMap])

end smallBasis

section comparison

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E)

private lemma faces_down : ∀ s ∈ K.faces, ∀ t ⊆ s, t.Nonempty → t ∈ K.faces :=
  fun _ hs _ ht hne ↦ K.down_closed hs ht hne

/-- The cover of `|K|` by the open stars of the vertices. -/
private def starCover : Set (Set K.space) :=
  range fun v : E ↦ (Subtype.val ⁻¹' openStar K v : Set K.space)

variable {K}

private lemma isOpen_of_mem_starCover (hK : K.faces.Finite) : ∀ U ∈ starCover K, IsOpen U := by
  rintro _ ⟨v, rfl⟩
  exact (isOpen_openStar K hK v).preimage continuous_subtype_val

private lemma sUnion_starCover : ⋃₀ starCover K = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨F, hF, hxF, hmin⟩ := exists_minFace x.2
  obtain ⟨v, hv⟩ : F.Nonempty := Finset.nonempty_iff_ne_empty.2 fun h ↦ by
    rwa [h, Finset.coe_empty, convexHull_empty] at hxF
  exact ⟨_, ⟨v, rfl⟩, fun σ hσ hxσ ↦ hmin σ hσ hxσ hv⟩

private lemma exists_openStar {n : ℕ} (b : SmallSimplex (starCover K) n) :
    ∃ v, ∀ t, (b.1 t : E) ∈ openStar K v := by
  obtain ⟨_, ⟨v, rfl⟩, hb⟩ := b.2
  exact ⟨v, fun t ↦ hb ⟨t, rfl⟩⟩

private theorem exists_simplicial_singular_comparison (hK : K.faces.Finite) :
    ∃ (F : ∀ n, (Face K.faces n →₀ ℤ) →ₗ[ℤ] Chain ℤ K.space n)
      (G : ∀ n, Chain ℤ K.space n →ₗ[ℤ] (Face K.faces n →₀ ℤ))
      (h₁ : ∀ n, (Face K.faces n →₀ ℤ) →ₗ[ℤ] (Face K.faces (n + 1) →₀ ℤ))
      (h₂ : ∀ n, Chain ℤ K.space n →ₗ[ℤ] Chain ℤ K.space (n + 1)),
      (∀ n c, bd ℤ n (F (n + 1) c) = F n (dS (faces_down K) n c)) ∧
      (∀ n c, dS (faces_down K) n (G (n + 1) c) = G n (bd ℤ n c)) ∧
      (∀ c, G 0 (F 0 c) - c = dS (faces_down K) 0 (h₁ 0 c)) ∧
      (∀ n c, G (n + 1) (F (n + 1) c) - c =
        dS (faces_down K) (n + 1) (h₁ (n + 1) c) + h₁ n (dS (faces_down K) n c)) ∧
      (∀ c, F 0 (G 0 c) - c = bd ℤ 0 (h₂ 0 c)) ∧
      ∀ n c, F (n + 1) (G (n + 1) c) - c = bd ℤ (n + 1) (h₂ (n + 1) c) + h₂ n (bd ℤ n c) := by
  set 𝒰 := starCover K
  have h𝒰 := isOpen_of_mem_starCover hK
  have hcov : ⋃₀ 𝒰 = univ := sUnion_starCover
  choose v hv using fun n (b : SmallSimplex 𝒰 n) ↦ exists_openStar b
  have hmono1 : CarrierMono (dSm 𝒰)
      (fun n (b : SmallSimplex 𝒰 n) k ↦ facesOn (carrierFaces b.1) k) := by
    intro n b b' hb' k
    obtain ⟨i, hi⟩ := mem_support_dSm hb'
    exact facesOn_mono (carrierFaces_mono fun t' ↦ ⟨face n i t', by rw [hi]; rfl⟩) k
  have hacyc1 : CarrierAcyclic (D := fun _ ↦ Finset E →₀ ℤ) (fun _ ↦ bdS) augS
      (fun n (b : SmallSimplex 𝒰 n) k ↦ facesOn (carrierFaces b.1) k) :=
    ⟨fun n b _ hz hz0 ↦ exists_bdS_eq_of_cone_zero
        (fun _ hs ↦ insert_mem_carrierFaces (hv n b) hs) hz hz0,
      fun n b _ _ hz hbd ↦ exists_bdS_eq_of_cone
        (fun _ hs ↦ insert_mem_carrierFaces (hv n b) hs) hz hbd⟩
  have heps1 : ∀ b : SmallSimplex 𝒰 1, augS (linearCombination ℤ
      (fun b ↦ single ({v 0 b} : Finset E) (1 : ℤ)) (dSm 𝒰 0 (single b 1))) = 0 := by
    intro b
    have h1 : augS ∘ₗ linearCombination ℤ (fun b ↦ single ({v 0 b} : Finset E) (1 : ℤ)) =
        aug ℤ 0 ∘ₗ inclSm 𝒰 0 :=
      lhom_ext_one fun b ↦ by simp [augS_single, inclSm_single, aug_single]
    have h2 := congrArg (fun L ↦ L (dSm 𝒰 0 (single b 1))) h1
    simp only [LinearMap.comp_apply] at h2
    rw [h2, inclSm_dSm, aug_bd_zero]
  obtain ⟨ψ, hψ0, hψΦ, hψd⟩ := exists_chainMap_carried (D := fun _ ↦ Finset E →₀ ℤ)
    (dD := fun _ ↦ bdS) (ε := augS) dSm_dSm hmono1 hacyc1
    (fun b ↦ single ({v 0 b} : Finset E) (1 : ℤ))
    (fun b ↦ single_mem_supported ℤ _ ⟨singleton_mem_carrierFaces (hv 0 b), rfl⟩) heps1
  have hψK : ∀ n c, ψ n c ∈ facesOn K.faces n := fun n c ↦
    map_mem_of_forall_single (ψ n) (fun b ↦ facesOn_mono (fun _ hs ↦ hs.1) n (hψΦ n b)) c
  have hψaug : ∀ c, augS (ψ 0 c) = aug ℤ 0 (inclSm 𝒰 0 c) := by
    intro c
    have h1 : augS ∘ₗ ψ 0 = aug ℤ 0 ∘ₗ inclSm 𝒰 0 :=
      lhom_ext_one fun b ↦ by
        simp only [LinearMap.comp_apply]
        rw [hψ0, augS_single, inclSm_single, aug_single]
    exact congrArg (fun L ↦ L c) h1
  let G : ∀ n, Chain ℤ K.space n →ₗ[ℤ] (Face K.faces n →₀ ℤ) := fun n ↦
    (supportedEquivFinsupp (M := ℤ) (R := ℤ) _).toLinearMap ∘ₗ
      LinearMap.codRestrict (facesOn K.faces n) (ψ n ∘ₗ toSmall 𝒰 h𝒰 hcov n)
        fun c ↦ hψK n _
  have hG : ∀ n c, embS K.faces n (G n c) = ψ n (toSmall 𝒰 h𝒰 hcov n c) :=
    fun n c ↦ embS_toFace n _
  let F : ∀ n, (Face K.faces n →₀ ℤ) →ₗ[ℤ] Chain ℤ K.space n := fun n ↦
    simplicialToSingular K n ∘ₗ embS K.faces n
  have hF : ∀ n c, F n c = simplicialToSingular K n (embS K.faces n c) := fun _ _ ↦ rfl
  have hFd : ∀ n c, bd ℤ n (F (n + 1) c) = F n (dS (faces_down K) n c) := by
    intro n c
    rw [hF, hF, bd_simplicialToSingular K (embS_mem _ c), embS_dS]
  have hGd : ∀ n c, dS (faces_down K) n (G (n + 1) c) = G n (bd ℤ n c) := fun n c ↦
    embS_injective n (by rw [embS_dS, hG, hG, hψd, dSm_toSmall])
  have hFsingle : ∀ n (s : Face K.faces n),
      F n (single s 1) = single (affSimplex K s.1 s.2.1 s.2.2) 1 := by
    intro n s
    rw [hF, embS_single, simplicialToSingular_single K s.2.1 s.2.2]
  have hmono2 : CarrierMono (dS (faces_down K))
      (fun n (s : Face K.faces n) k ↦ facesOn {t | t ∈ K.faces ∧ t ⊆ s.1} k) := by
    intro n s s' hs' k
    refine facesOn_mono (fun t ht ↦ ?_) k
    exact ⟨ht.1, ht.2.trans (subset_of_mem_support_dS _ hs')⟩
  have hins : ∀ n (s : Face K.faces n), ∃ w, ∀ t ∈ {t | t ∈ K.faces ∧ t ⊆ s.1},
      insert w t ∈ {t | t ∈ K.faces ∧ t ⊆ s.1} := by
    intro n s
    obtain ⟨w, hw⟩ := Finset.card_pos.1 (by rw [s.2.2]; omega)
    exact ⟨w, fun t ht ↦ ⟨K.down_closed s.2.1 (Finset.insert_subset hw ht.2)
      (Finset.insert_nonempty _ _), Finset.insert_subset hw ht.2⟩⟩
  have hacyc2 : CarrierAcyclic (D := fun _ ↦ Finset E →₀ ℤ) (fun _ ↦ bdS) augS
      (fun n (s : Face K.faces n) k ↦ facesOn {t | t ∈ K.faces ∧ t ⊆ s.1} k) := by
    refine ⟨fun n s z hz hz0 ↦ ?_, fun n s k z hz hbd ↦ ?_⟩
    · obtain ⟨w, hw⟩ := hins n s
      exact exists_bdS_eq_of_cone_zero hw hz hz0
    · obtain ⟨w, hw⟩ := hins n s
      exact exists_bdS_eq_of_cone hw hz hbd
  have hf2 : ∀ n c, bdS (embS K.faces (n + 1) (G (n + 1) (F (n + 1) c))) =
      embS K.faces n (G n (F n (dS (faces_down K) n c))) := by
    intro n c
    rw [← embS_dS (faces_down K), hGd, hFd]
  have hfΦ2 : ∀ n (s : Face K.faces n), embS K.faces n (G n (F n (single s 1))) ∈
      facesOn {t | t ∈ K.faces ∧ t ⊆ s.1} n := by
    intro n s
    rw [hG, hFsingle]
    have hin : toSmall 𝒰 h𝒰 hcov n (single (affSimplex K s.1 s.2.1 s.2.2) 1) ∈
        supported ℤ ℤ {b : SmallSimplex 𝒰 n |
          range b.1 ⊆ (Subtype.val ⁻¹' convexHull ℝ (s.1 : Set E) : Set K.space)} :=
      inclSm_mem_inside (by
        rw [inclSm_toSmall]
        exact smallChainMap_mem_inside 𝒰 (single_mem_supported ℤ _ (by
          rintro _ ⟨t, rfl⟩
          exact affSimplex_mem_convexHull K _ _ _ t)))
    refine map_mem_of_supported (ψ n) (fun b hb ↦ ?_) hin
    refine facesOn_mono (fun t ht ↦ ?_) n (hψΦ n b)
    exact ⟨ht.1, subset_of_mem_carrierFaces s.2.1 (fun t' ↦ hb ⟨t', rfl⟩) ht⟩
  have hgΦ2 : ∀ n (s : Face K.faces n), embS K.faces n (single s 1) ∈
      facesOn {t | t ∈ K.faces ∧ t ⊆ s.1} n := by
    intro n s
    rw [embS_single]
    exact single_mem_supported ℤ _ ⟨⟨s.2.1, subset_rfl⟩, s.2.2⟩
  have hε2 : ∀ s : Face K.faces 0, augS (embS K.faces 0 (G 0 (F 0 (single s 1)))) =
      augS (embS K.faces 0 (single s 1)) := by
    intro s
    rw [hG, hψaug, inclSm_toSmall, aug_smallChainMap_zero, embS_single, augS_single, hFsingle,
      aug_single]
  obtain ⟨k₁, hk₁Φ, hk₁0, hk₁s⟩ := exists_homotopy_carried (D := fun _ ↦ Finset E →₀ ℤ)
    (dD := fun _ ↦ bdS) (ε := augS) (dS_dS (faces_down K)) hmono2 hacyc2
    (fun n ↦ embS K.faces n ∘ₗ G n ∘ₗ F n) (fun n ↦ embS K.faces n) hf2
    (fun n c ↦ (embS_dS (faces_down K) n c).symm) hfΦ2 hgΦ2 hε2
  have hk₁K : ∀ n c, k₁ n c ∈ facesOn K.faces (n + 1) := fun n c ↦
    map_mem_of_forall_single (k₁ n) (fun s ↦ facesOn_mono (fun _ ht ↦ ht.1) _ (hk₁Φ n s)) c
  let h₁ : ∀ n, (Face K.faces n →₀ ℤ) →ₗ[ℤ] (Face K.faces (n + 1) →₀ ℤ) := fun n ↦
    (supportedEquivFinsupp (M := ℤ) (R := ℤ) _).toLinearMap ∘ₗ
      LinearMap.codRestrict (facesOn K.faces (n + 1)) (k₁ n) (hk₁K n)
  have hh₁ : ∀ n c, embS K.faces (n + 1) (h₁ n c) = k₁ n c := fun n c ↦ embS_toFace (n + 1) _
  have hmono3 : CarrierMono (dSm 𝒰) (fun n (b : SmallSimplex 𝒰 n) k ↦
      inside ℤ k (Subtype.val ⁻¹' carrierSpace b.1 : Set K.space)) := by
    intro n b b' hb' k
    obtain ⟨i, hi⟩ := mem_support_dSm hb'
    exact supported_mono fun σ hσ ↦ hσ.trans
      (preimage_mono (carrierSpace_mono fun t' ↦ ⟨face n i t', by rw [hi]; rfl⟩))
  have hacyc3 : CarrierAcyclic (D := fun n ↦ Chain ℤ K.space n) (fun n ↦ bd ℤ n) (aug ℤ 0)
      (fun n (b : SmallSimplex 𝒰 n) k ↦
        inside ℤ k (Subtype.val ⁻¹' carrierSpace b.1 : Set K.space)) :=
    ⟨fun n b _ hz hz0 ↦ exists_bd_eq_of_starConvex_of_subset_zero (carrierSpace_subset _)
        (starConvex_carrierSpace (hv n b)) hz hz0,
      fun n b _ _ hz hbd ↦ exists_bd_eq_of_starConvex_of_subset (carrierSpace_subset _)
        (starConvex_carrierSpace (hv n b)) hz hbd⟩
  have hf3 : ∀ n c, bd ℤ n (simplicialToSingular K (n + 1) (ψ (n + 1) c)) =
      simplicialToSingular K n (ψ n (dSm 𝒰 n c)) := by
    intro n c
    rw [bd_simplicialToSingular K (hψK _ c), hψd]
  have hfΦ3 : ∀ n (b : SmallSimplex 𝒰 n), simplicialToSingular K n (ψ n (single b 1)) ∈
      inside ℤ n (Subtype.val ⁻¹' carrierSpace b.1 : Set K.space) := by
    intro n b
    refine map_mem_of_supported _ (fun s hs ↦ ?_) (hψΦ n b)
    rw [simplicialToSingular_single K hs.1.1 hs.2]
    refine single_mem_supported ℤ _ ?_
    rintro _ ⟨t, rfl⟩
    exact mem_biUnion hs.1 (affSimplex_mem_convexHull K _ _ _ t)
  have hgΦ3 : ∀ n (b : SmallSimplex 𝒰 n), inclSm 𝒰 n (single b 1) ∈
      inside ℤ n (Subtype.val ⁻¹' carrierSpace b.1 : Set K.space) := by
    intro n b
    rw [inclSm_single]
    refine single_mem_supported ℤ _ ?_
    rintro _ ⟨t, rfl⟩
    exact mem_carrierSpace b.1 t
  have hε3 : ∀ b : SmallSimplex 𝒰 0, aug ℤ 0 (simplicialToSingular K 0 (ψ 0 (single b 1))) =
      aug ℤ 0 (inclSm 𝒰 0 (single b 1)) := by
    intro b
    rw [hψ0, simplicialToSingular_single K (singleton_mem_carrierFaces (hv 0 b)).1
      (Finset.card_singleton _), aug_single, inclSm_single, aug_single]
  obtain ⟨k₃, -, hk₃0, hk₃s⟩ := exists_homotopy_carried (D := fun n ↦ Chain ℤ K.space n)
    (dD := fun n ↦ bd ℤ n) (ε := aug ℤ 0) dSm_dSm hmono3 hacyc3
    (fun n ↦ simplicialToSingular K n ∘ₗ ψ n) (fun n ↦ inclSm 𝒰 n) hf3
    (fun n c ↦ (inclSm_dSm n c).symm) hfΦ3 hgΦ3 hε3
  let h₂ : ∀ n, Chain ℤ K.space n →ₗ[ℤ] Chain ℤ K.space (n + 1) := fun n ↦
    k₃ n ∘ₗ toSmall 𝒰 h𝒰 hcov n - smallHomotopy ℤ 𝒰 n
  have hFG : ∀ n c, F n (G n c) = simplicialToSingular K n (ψ n (toSmall 𝒰 h𝒰 hcov n c)) := by
    intro n c
    rw [hF, hG]
  refine ⟨F, G, h₁, h₂, hFd, hGd, fun c ↦ ?_, fun n c ↦ ?_, fun c ↦ ?_, fun n c ↦ ?_⟩
  · refine embS_injective 0 ?_
    rw [map_sub, embS_dS, hh₁]
    exact hk₁0 c
  · refine embS_injective (n + 1) ?_
    rw [map_sub, map_add, embS_dS, hh₁, hh₁]
    exact hk₁s n c
  · have h := hk₃0 (toSmall 𝒰 h𝒰 hcov 0 c)
    simp only [LinearMap.comp_apply] at h
    rw [inclSm_toSmall, smallChainMap_zero] at h
    rw [hFG]
    simp only [h₂, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    rw [← h]
    abel
  · have h := hk₃s n (toSmall 𝒰 h𝒰 hcov (n + 1) c)
    simp only [LinearMap.comp_apply] at h
    rw [inclSm_toSmall, smallChainMap_succ, dSm_toSmall] at h
    rw [hFG]
    simp only [h₂, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    rw [sub_eq_iff_eq_add.1 h]
    abel

end comparison

/-- The chain complex of `ℤ`-modules `M n` with differentials `d n`. -/
private noncomputable abbrev ofLinear (M : ℕ → Type) [∀ n, AddCommGroup (M n)]
    (d : ∀ n, M (n + 1) →ₗ[ℤ] M n) (hd : ∀ n c, d n (d (n + 1) c) = 0) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of ℤ (M n)) (fun n ↦ ModuleCat.ofHom (d n))
    (fun n ↦ by ext c; simp [hd])

section ofLinear

variable {M : ℕ → Type} [∀ n, AddCommGroup (M n)] {d : ∀ n, M (n + 1) →ₗ[ℤ] M n}
  {hd : ∀ n c, d n (d (n + 1) c) = 0}

private lemma ofLinear_d (n : ℕ) : (ofLinear M d hd).d (n + 1) n = ModuleCat.ofHom (d n) :=
    ChainComplex.of_d (fun n ↦ ModuleCat.of ℤ (M n)) (fun n ↦ ModuleCat.ofHom (d n)) n

variable {M' : ℕ → Type} [∀ n, AddCommGroup (M' n)] {d' : ∀ n, M' (n + 1) →ₗ[ℤ] M' n}
  {hd' : ∀ n c, d' n (d' (n + 1) c) = 0}

/-- A chain map between complexes of modules given by linear maps. -/
private noncomputable def homOfLinear (F : ∀ n, M n →ₗ[ℤ] M' n)
    (hF : ∀ n c, d' n (F (n + 1) c) = F n (d n c)) : ofLinear M d hd ⟶ ofLinear M' d' hd' :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (F n)) fun n ↦ by
    rw [ofLinear_d, ofLinear_d]
    ext c
    exact hF n c

private lemma homOfLinear_f (F : ∀ n, M n →ₗ[ℤ] M' n) (hF : ∀ n c, d' n (F (n + 1) c) = F n (d n c))
    (n : ℕ) : (homOfLinear (hd := hd) (hd' := hd') F hF).f n = ModuleCat.ofHom (F n) := rfl

/-- A homotopy given by linear maps. -/
private noncomputable def homotopyOfLinear {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f g : C ⟶ D)
    (k : ∀ n, C.X n →ₗ[ℤ] D.X (n + 1))
    (h0 : ∀ c, (f.f 0).hom c = (D.d 1 0).hom (k 0 c) + (g.f 0).hom c)
    (hs : ∀ n c, (f.f (n + 1)).hom c = k n ((C.d (n + 1) n).hom c) +
      (D.d (n + 2) (n + 1)).hom (k (n + 1) c) + (g.f (n + 1)).hom c) : Homotopy f g where
  hom i j := if h : i + 1 = j then ModuleCat.ofHom (k i) ≫ eqToHom (by rw [h]) else 0
  zero i j hij := dif_neg fun h ↦ hij (by simp [← h])
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, dif_pos rfl,
        eqToHom_refl, Category.comp_id, zero_add]
      ext c
      exact h0 c
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, dif_pos rfl,
        dif_pos rfl, eqToHom_refl, eqToHom_refl, Category.comp_id, Category.comp_id]
      ext c
      exact hs n c

/-- A homotopy equivalence of complexes of modules given by linear data. -/
private noncomputable def homotopyEquivOfLinear (F : ∀ n, M n →ₗ[ℤ] M' n) (G : ∀ n, M' n →ₗ[ℤ] M n)
    (h₁ : ∀ n, M n →ₗ[ℤ] M (n + 1)) (h₂ : ∀ n, M' n →ₗ[ℤ] M' (n + 1))
    (hF : ∀ n c, d' n (F (n + 1) c) = F n (d n c)) (hG : ∀ n c, d n (G (n + 1) c) = G n (d' n c))
    (hGF0 : ∀ c, G 0 (F 0 c) - c = d 0 (h₁ 0 c))
    (hGF : ∀ n c, G (n + 1) (F (n + 1) c) - c = d (n + 1) (h₁ (n + 1) c) + h₁ n (d n c))
    (hFG0 : ∀ c, F 0 (G 0 c) - c = d' 0 (h₂ 0 c))
    (hFG : ∀ n c, F (n + 1) (G (n + 1) c) - c = d' (n + 1) (h₂ (n + 1) c) + h₂ n (d' n c)) :
    HomotopyEquiv (ofLinear M d hd) (ofLinear M' d' hd') where
  hom := homOfLinear F hF
  inv := homOfLinear G hG
  homotopyHomInvId := homotopyOfLinear _ _ h₁
    (fun c ↦ by
      rw [ofLinear_d]
      simp only [HomologicalComplex.comp_f, homOfLinear_f, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.comp_apply, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
      rw [← sub_eq_iff_eq_add]
      exact hGF0 c)
    (fun n c ↦ by
      rw [ofLinear_d, ofLinear_d]
      simp only [HomologicalComplex.comp_f, homOfLinear_f, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.comp_apply, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
      rw [← sub_eq_iff_eq_add, hGF n c]
      exact add_comm _ _)
  homotopyInvHomId := homotopyOfLinear _ _ h₂
    (fun c ↦ by
      rw [ofLinear_d]
      simp only [HomologicalComplex.comp_f, homOfLinear_f, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.comp_apply, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
      rw [← sub_eq_iff_eq_add]
      exact hFG0 c)
    (fun n c ↦ by
      rw [ofLinear_d, ofLinear_d]
      simp only [HomologicalComplex.comp_f, homOfLinear_f, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.comp_apply, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
      rw [← sub_eq_iff_eq_add, hFG n c]
      exact add_comm _ _)

end ofLinear

section singular

variable (Y : Type) [TopologicalSpace Y]

/-- The finite singular chain complex of `Y`. -/
private noncomputable abbrev finChainCx : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ofLinear (fun n ↦ Chain ℤ Y n) (fun n ↦ bd ℤ n) bd_bd

/-- Singular chains as finite formal sums. -/
private noncomputable abbrev toFin (n : ℕ) : (chainCx ℤ (TopCat.of Y)).X n →ₗ[ℤ] Chain ℤ Y n :=
  extend (Y := TopCat.of Y) (Chain ℤ Y n) fun τ ↦ single τ 1

variable {Y}

/-- Finite sums as singular chains. -/
private noncomputable def ofFin (n : ℕ) : Chain ℤ Y n →ₗ[ℤ] (chainCx ℤ (TopCat.of Y)).X n :=
  linearCombination ℤ fun τ ↦ gen (Y := TopCat.of Y) τ

/-- The two descriptions of singular chains agree. -/
private noncomputable def finEquiv (n : ℕ) : (chainCx ℤ (TopCat.of Y)).X n ≃ₗ[ℤ] Chain ℤ Y n :=
  LinearEquiv.ofLinear (toFin Y n) (ofFin n)
    (Finsupp.lhom_ext' fun τ ↦ LinearMap.ext_ring (by simp [ofFin, extend_gen]))
    (linearMap_ext (L := ofFin (Y := Y) n ∘ₗ toFin Y n)
      (L' := LinearMap.id (R := ℤ) (M := (chainCx ℤ (TopCat.of Y)).X n)) fun τ ↦ by
      rw [LinearMap.comp_apply, extend_gen, LinearMap.id_apply]
      simp only [ofFin, linearCombination_single]
      exact @one_smul ℤ _ _ ((chainCx ℤ (TopCat.of Y)).X n).isModule.toMulAction _)

private lemma finEquiv_apply (n : ℕ) (c : (chainCx ℤ (TopCat.of Y)).X n) :
    finEquiv n c = toFin Y n c := rfl

private lemma toFin_d (n : ℕ) (c : (chainCx ℤ (TopCat.of Y)).X (n + 1)) :
    toFin Y n (((chainCx ℤ (TopCat.of Y)).d (n + 1) n).hom c) = bd ℤ n (toFin Y (n + 1) c) := by
  have := linearMap_ext (L := toFin Y n ∘ₗ ((chainCx ℤ (TopCat.of Y)).d (n + 1) n).hom)
    (L' := bd ℤ n ∘ₗ toFin Y (n + 1)) fun τ ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, d_gen, map_sum, extend_gen, bd_single]
      simp [extend_gen]
  exact congrArg (fun L ↦ L c) this

variable (Y) in
/-- The singular chain complex of `Y` is its finite chain complex. -/
private noncomputable def chainCxIso : chainCx ℤ (TopCat.of Y) ≅ finChainCx Y :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ (finEquiv n).toModuleIso) (by
    rintro i j (rfl : j + 1 = i)
    rw [ofLinear_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
      ModuleCat.hom_ofHom, LinearEquiv.coe_coe, finEquiv_apply]
    exact (toFin_d j c).symm)

end singular

section homotopyInvariance

/-- A homotopy equivalence of spaces induces one of singular chain complexes. -/
private noncomputable def chainCxHomotopyEquiv {X Y : TopCat.{0}} (e : ContinuousMap.HomotopyEquiv X Y) :
    HomotopyEquiv (chainCx ℤ X) (chainCx ℤ Y) where
  hom := ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom e.toFun)
  inv := ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom e.invFun)
  homotopyHomInvId := (Homotopy.ofEq (CategoryTheory.Functor.map_comp _ _ _).symm).trans
    ((TopCat.Homotopy.singularChainComplexFunctorObjMap
      (f := TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (g := 𝟙 X) e.left_inv.some _).trans
      (Homotopy.ofEq (CategoryTheory.Functor.map_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (CategoryTheory.Functor.map_comp _ _ _).symm).trans
    ((TopCat.Homotopy.singularChainComplexFunctorObjMap
      (f := TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (g := 𝟙 Y) e.right_inv.some _).trans
      (Homotopy.ofEq (CategoryTheory.Functor.map_id _ _)))

end homotopyInvariance

end polyhedron

/-- The integral singular chain complex of the complex points of a projective complex scheme is
homotopy equivalent to a bounded complex of finitely generated free abelian groups. -/
private theorem exists_finite_free_model {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjectiveMorphism sX) :
    ∃ C : ChainComplex (ModuleCat.{0} ℤ) ℕ,
      (∀ i, Module.Free ℤ (C.X i) ∧ Module.Finite ℤ (C.X i)) ∧
      (∃ N : ℕ, ∀ i, N < i → IsZero (C.X i)) ∧
      Nonempty (HomotopyEquiv C
        (((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
          (analyticSpace sX))) := by
  obtain ⟨N, K, hK, ⟨e⟩⟩ :=
    MMP.Analytic.exists_homotopyEquiv_finite_simplicialComplex_of_isProjective sX hX.isProjective
  letI : LinearOrder (EuclideanSpace ℝ (Fin N)) := IsWellOrder.linearOrder WellOrderingRel
  obtain ⟨F, G, h₁, h₂, hF, hG, h₁0, h₁s, h₂0, h₂s⟩ :=
    exists_simplicial_singular_comparison (K := K) hK
  refine ⟨ofLinear (fun n ↦ Face K.faces n →₀ ℤ) (dS (faces_down K)) (dS_dS (faces_down K)),
    fun i ↦ ?_, ⟨hK.toFinset.sup Finset.card, fun i hi ↦ ?_⟩, ⟨?_⟩⟩
  · haveI : Finite (Face K.faces i) := (hK.subset fun s hs ↦ hs.1).to_subtype
    exact ⟨inferInstance, inferInstance⟩
  · haveI : IsEmpty (Face K.faces i) := ⟨fun s ↦ by
      have := Finset.le_sup (f := Finset.card) (hK.mem_toFinset.2 s.2.1)
      rw [s.2.2] at this
      omega⟩
    exact ModuleCat.isZero_of_subsingleton _
  · exact (homotopyEquivOfLinear F G h₁ h₂ hF hG h₁0 h₁s h₂0 h₂s).trans
      ((HomotopyEquiv.ofIso (chainCxIso K.space)).symm.trans (chainCxHomotopyEquiv e.symm))

end MMP.Proof_lem_mmp_projective_finite_cochains

namespace MMP.Analytic

open MMP.Proof_lem_mmp_projective_finite_cochains

/-- **Finite cochains for a projective complex scheme.** For a projective scheme `X` over `ℂ`,
the integral singular chain complex of `X^an` is homotopy equivalent to a bounded complex of
finitely generated free abelian groups; consequently every `H^i(X^an; ℤ)` is finitely generated,
and the change of coefficients `H^i(X^an; ℤ) → H^i(X^an; ℚ)` is a base change to `ℚ`, i.e.
induces `H^i(X^an; ℤ) ⊗_ℤ ℚ ≃ H^i(X^an; ℚ)`. -/
@[mmp "lem_mmp_projective_finite_cochains"]
public theorem exists_homotopyEquiv_singularChainComplex_of_isProjectiveMorphism
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX) :
    (∃ C : ChainComplex (ModuleCat.{0} ℤ) ℕ,
      (∀ i, Module.Free ℤ (C.X i) ∧ Module.Finite ℤ (C.X i)) ∧
      (∃ N : ℕ, ∀ i, N < i → IsZero (C.X i)) ∧
      Nonempty (HomotopyEquiv C
        (((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
          (analyticSpace sX)))) ∧
    (∀ i : ℕ, Module.Finite ℤ (singularCohomology ℤ (analyticSpace sX) i)) ∧
    ∀ i : ℕ, IsBaseChange ℚ
      ({ toFun := singularCohomology.mapCoeff (Int.castRingHom ℚ) (Y := analyticSpace sX) i
         map_add' := map_add _
         map_smul' := fun r x ↦ by
           rw [map_smulₛₗ, eq_intCast, Int.cast_smul_eq_zsmul, RingHom.id_apply] } :
        singularCohomology ℤ (analyticSpace sX) i →ₗ[ℤ] singularCohomology ℚ (analyticSpace sX) i) := by
  obtain ⟨C, hC, hN, ⟨e⟩⟩ := exists_finite_free_model sX hX
  haveI : ∀ i, Module.Finite ℤ (C.X i) := fun i ↦ (hC i).2
  exact ⟨⟨C, hC, hN, ⟨e⟩⟩, finite_singularCohomology ℤ e, isBaseChange_coeffMap e⟩

/-- For a projective scheme `X` over `ℂ` and a Noetherian ring `R`, every singular cohomology
group `H^i(X^an; R)` is a finite `R`-module. -/
public theorem finite_analyticSingularCohomology_of_isProjectiveMorphism {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX) (R : Type) [CommRing R]
    [IsNoetherianRing R] (i : ℕ) : Module.Finite R (singularCohomology R (analyticSpace sX) i) := by
  obtain ⟨C, hC, -, ⟨e⟩⟩ := exists_finite_free_model sX hX
  have : ∀ i, Module.Finite ℤ (C.X i) := fun i ↦ (hC i).2
  exact finite_singularCohomology R e i

end MMP.Analytic

namespace MMP.Analytic

/-- For a projective scheme `X` over `ℂ`, the change of coefficients
`H^i(X^an; ℤ) → H^i(X^an; ℚ)` exhibits `H^i(X^an; ℚ)` as the base change
`H^i(X^an; ℤ) ⊗_ℤ ℚ`. -/
@[mmp "lem_mmp_projective_betti_rationalization"]
public theorem isBaseChange_mapCoeff_of_isProjectiveMorphism {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX) (i : ℕ) :
    IsBaseChange ℚ
      ({ toFun := singularCohomology.mapCoeff (Int.castRingHom ℚ) (Y := Analytification.space sX) i
         map_add' := map_add _
         map_smul' := fun r x ↦ by
           rw [map_smulₛₗ, eq_intCast, Int.cast_smul_eq_zsmul, RingHom.id_apply] } :
        analyticSingularCohomology ℤ sX i →ₗ[ℤ] analyticSingularCohomology ℚ sX i) :=
  (exists_homotopyEquiv_singularChainComplex_of_isProjectiveMorphism sX hX).2.2 i

end MMP.Analytic

namespace MMP.Proof_lem_mmp_indexd_projective_homology_finite

open scoped TensorProduct

/-- Extension of scalars `ℤ → ℚ` is additive. -/
private lemma additive_extendScalars :
    (ModuleCat.extendScalars.{0, 0, 0} (algebraMap ℤ ℚ)).Additive :=
  ⟨fun {_ _ _ _} => by
    ext x; simp [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map']; rfl⟩

/-- A chain complex of finite-dimensional `ℚ`-vector spaces has finite-dimensional homology. -/
private lemma finiteDimensional_homology {K : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (h : ∀ i, FiniteDimensional ℚ (K.X i)) (k : ℕ) : FiniteDimensional ℚ (K.homology k) := by
  have : FiniteDimensional ℚ (K.cycles k) :=
    Module.Finite.of_injective (K.iCycles k).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)
  exact Module.Finite.of_surjective (K.homologyπ k).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- The rational singular homology of the complex realization of an H-projective scheme over `ℂ`
is finite-dimensional. -/
private lemma finiteDimensional_homology_analyticSpace {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjectiveMorphism sX) (k : ℕ) :
    FiniteDimensional ℚ ((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).obj (MMP.Analytic.ComplexPoints.analyticSpace sX)).homology k) := by
  obtain ⟨⟨C, hC, -, ⟨e⟩⟩, -⟩ :=
    MMP.Analytic.exists_homotopyEquiv_singularChainComplex_of_isProjectiveMorphism sX hX
  let F := ModuleCat.extendScalars.{0, 0, 0} (algebraMap ℤ ℚ)
  have : F.Additive := additive_extendScalars
  let e' := F.mapHomotopyEquiv e
  let i₁ := (SSet.chainComplexFunctorObjCompMapIso F (ModuleCat.of ℤ ℤ)).app
    (TopCat.toSSet.obj (MMP.Analytic.ComplexPoints.analyticSpace sX))
  let i₂ : F.obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℚ ℚ :=
    (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toModuleIso
  let i₃ := ((SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).mapIso i₂).app
    (TopCat.toSSet.obj (MMP.Analytic.ComplexPoints.analyticSpace sX))
  have hfin : ∀ i, FiniteDimensional ℚ (((F.mapHomologicalComplex _).obj C).X i) := fun i ↦
    have := (hC i).2
    inferInstanceAs (FiniteDimensional ℚ (ℚ ⊗[ℤ] C.X i))
  have := finiteDimensional_homology hfin k
  let j := e'.toHomologyIso k ≪≫ (HomologicalComplex.homologyFunctor _ _ k).mapIso (i₁ ≪≫ i₃)
  exact Module.Finite.equiv j.toLinearEquiv

section BorelMoore

open MMP MMP.LocallyFiniteChain

variable (Y : TopCat.{0})

/-- A finitely supported family of simplices is locally finite. -/
private lemma isLocallyFiniteSet_of_finite {S : Type*} {car : S → Set Y} {s : Set S}
    (hs : s.Finite) : IsLocallyFiniteSet car s :=
  fun _ ↦ ⟨Set.univ, Filter.univ_mem, hs.subset fun _ hτ ↦ hτ.1⟩

/-- Finite singular chains, as locally finite singular chains. -/
private noncomputable def finsuppToLF (n : SimplexCategoryᵒᵖ) :
    ((TopCat.toSSet.obj Y).obj n →₀ ℚ) →ₗ[ℚ]
      lfChains ℚ (ModuleCat.of ℚ ℚ) (singularSimplexImage Y (n := n)) :=
  (Finsupp.lcoeFun).codRestrict _ fun f ↦
    isLocallyFiniteSet_of_finite Y (by simpa [Finsupp.fun_support_eq] using f.support.finite_toSet)

/-- On a compact space every locally finite chain is finite. -/
private lemma bijective_finsuppToLF [CompactSpace Y] (n : SimplexCategoryᵒᵖ) :
    Function.Bijective (finsuppToLF Y n) := by
  refine ⟨fun f g h ↦ Finsupp.ext fun σ ↦ congr_fun (congrArg Subtype.val h) σ, fun c ↦ ?_⟩
  have hfin : (Function.support c.1).Finite := by
    refine (c.2.finite_inter_compact isCompact_univ).subset fun σ hσ ↦ ⟨hσ, ?_⟩
    obtain ⟨y, hy⟩ := nonempty_singularSimplexImage σ
    exact ⟨y, hy, trivial⟩
  exact ⟨Finsupp.ofSupportFinite c.1 hfin, Subtype.ext rfl⟩

/-- The coproduct of copies of `ℚ` indexed by `S` is `S →₀ ℚ`. -/
private noncomputable def sigmaIsoFinsupp (S : Type) :
    (∐ fun _ : S ↦ ModuleCat.of ℚ ℚ) ≅ ModuleCat.of ℚ (S →₀ ℚ) :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso (ModuleCat.finsuppCoconeIsColimit ℚ ℚ S)

@[reassoc]
private lemma ι_sigmaIsoFinsupp_hom {S : Type} (σ : S) :
    Sigma.ι _ σ ≫ (sigmaIsoFinsupp S).hom = ModuleCat.ofHom (Finsupp.lsingle σ) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk σ)

private lemma sigmaIsoFinsupp_hom_ι_apply {S : Type} (σ : S) (q : ℚ) :
    (sigmaIsoFinsupp S).hom.hom ((Sigma.ι (fun _ : S ↦ ModuleCat.of ℚ ℚ) σ).hom q) =
      Finsupp.single σ q := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ι_sigmaIsoFinsupp_hom]
  rfl

/-- The comparison from singular chains (as a coproduct) to locally finite chains. -/
private noncomputable def toLF :
    ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj (ModuleCat.of ℚ ℚ))).obj
      (TopCat.toSSet.obj Y) ⟶ locallyFiniteSingularChains ℚ (ModuleCat.of ℚ ℚ) Y where
  app n := (sigmaIsoFinsupp _).hom ≫ ModuleCat.ofHom (finsuppToLF Y n)
  naturality n m θ := by
    dsimp [sigmaConst]
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    simp only [Sigma.ι_comp_map'_assoc, Category.id_comp]
    refine ModuleCat.hom_ext (LinearMap.ext_ring (Subtype.ext (funext fun τ ↦ ?_)))
    change ((sigmaIsoFinsupp _).hom.hom ((Sigma.ι (fun _ ↦ ModuleCat.of ℚ ℚ)
        ((TopCat.toSSet.obj Y).map θ σ)).hom 1) : (TopCat.toSSet.obj Y).obj m →₀ ℚ) τ =
      pushforwardFun ((TopCat.toSSet.obj Y).map θ)
        ⇑((sigmaIsoFinsupp _).hom.hom ((Sigma.ι (fun _ ↦ ModuleCat.of ℚ ℚ) σ).hom 1)) τ
    rw [sigmaIsoFinsupp_hom_ι_apply, sigmaIsoFinsupp_hom_ι_apply]
    classical
    rw [pushforwardFun_apply_eq_sum _ _ τ {σ} fun σ' h _ ↦ by
      by_contra h'
      exact h (Finsupp.single_eq_of_ne (by simpa using h'))]
    simp [Finsupp.single_apply]

private lemma isIso_toLF_app [CompactSpace Y] (n : SimplexCategoryᵒᵖ) :
    IsIso ((toLF Y).app n) := by
  change IsIso ((sigmaIsoFinsupp _ ≪≫
    (LinearEquiv.ofBijective _ (bijective_finsuppToLF Y n)).toModuleIso).hom)
  infer_instance

/-- On a compact space, Borel–Moore homology is singular homology. -/
private noncomputable def borelMooreHomologyIso [CompactSpace Y] (k : ℕ) :
    borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y k ≅
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).obj Y).homology k :=
  have : IsIso (toLF Y) := by
    have := isIso_toLF_app Y
    exact NatIso.isIso_of_isIso_app _
  borelMooreHomologyIsoOfNat ℚ _ Y k ≪≫ (HomologicalComplex.homologyFunctor _ _ k).mapIso
    ((alternatingFaceMapComplex _).mapIso (asIso (toLF Y))).symm

end BorelMoore

/-- The complex realization of a proper scheme over `ℂ` is compact. -/
private lemma compactSpace_complexPoints {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsProper (X ↘ Spec (.of ℂ))] :
    CompactSpace (MMP.Analytic.ComplexPoints (X ↘ Spec (.of ℂ))) := by
  letI : (Spec (.of ℂ)).Over (Spec (.of ℂ)) := ⟨𝟙 _⟩
  have : (X ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) := ⟨Category.comp_id _⟩
  have : LocallyOfFiniteType (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
    show LocallyOfFiniteType (𝟙 _) from inferInstance
  have hp := MMP.UnderlyingSpace.isProperMap_map (K := ℂ) (X ↘ Spec (.of ℂ))
  have : Subsingleton (MMP.UnderlyingSpace ℂ (Spec (.of ℂ))) :=
    ⟨fun p q ↦ MMP.UnderlyingSpace.ext
      (((Category.comp_id _).symm.trans p.toHom_comp_over).trans
        ((Category.comp_id _).symm.trans q.toHom_comp_over).symm)⟩
  have : CompactSpace (MMP.UnderlyingSpace ℂ X) :=
    ⟨by simpa using hp.isCompact_preimage Set.subsingleton_univ.isCompact⟩
  exact (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := X)).symm.compactSpace

open MMP.Analytic in
/-- The cycle span `Cyc_r(X)` of an H-projective complex scheme is finite-dimensional: it sits in
`H^BM_{2r}(X, ℚ)`, which is singular homology of the compact space `X^an`. -/
private lemma finiteDimensional_cycleSpan {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (hX : IsProjectiveMorphism (X ↘ Spec (.of ℂ))) (r : ℕ) :
    FiniteDimensional ℚ (cycleSpan X r) :=
  have := isProper_of_isProjectiveMorphism _ hX
  have := compactSpace_complexPoints (X := X)
  have := finiteDimensional_homology_analyticSpace _ hX (2 * r)
  have : FiniteDimensional ℚ (MMP.Analytic.borelMooreHomology (X ↘ Spec (.of ℂ)) (2 * r)) :=
    .equiv (borelMooreHomologyIso _ (2 * r)).symm.toLinearEquiv
  inferInstance

end MMP.Proof_lem_mmp_indexd_projective_homology_finite

namespace MMP.Analytic

open MMP.Proof_lem_mmp_indexd_projective_homology_finite

/-- The rational singular homology of the complex realization of a projective scheme over `ℂ` is
finite-dimensional in every degree; consequently every cycle span `Cyc_r(X)` and the cycle span
`Cyc_2(X × ℙ¹)` defining the boxed divisor cycle rank are finite-dimensional. -/
@[mmp "lem_mmp_indexd_projective_homology_finite"]
public theorem finiteDimensional_singularHomology_of_isProjective (X : Scheme.{0})
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] (hX : IsProjective (X ↘ Spec (.of ℂ))) :
    (∀ k : ℕ, FiniteDimensional ℚ (singularHomology (X ↘ Spec (.of ℂ)) k)) ∧
    (∀ r : ℕ, FiniteDimensional ℚ (cycleSpan X r)) ∧
    letI : (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) :=
      ⟨projToSpecCoeff ℂ 1⟩
    haveI := MMP.Fourfold.isComplexScheme_projectiveSpace 1 rfl
    haveI : IsComplexScheme (CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
        (projToSpecCoeff ℂ 1)) :=
      MMP.Chow.isComplexScheme_pullback X (AlgebraicGeometry.Proj (polyGrading ℂ 1))
    FiniteDimensional ℚ
      (cycleSpan (CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ)) (projToSpecCoeff ℂ 1)) 2) := by
  letI : (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) :=
    ⟨projToSpecCoeff ℂ 1⟩
  haveI := MMP.Fourfold.isComplexScheme_projectiveSpace 1 rfl
  haveI : IsComplexScheme (CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
      (projToSpecCoeff ℂ 1)) :=
    MMP.Chow.isComplexScheme_pullback X (AlgebraicGeometry.Proj (polyGrading ℂ 1))
  have hP := isProjectiveMorphism_of_isProjective_of_isAffine _ hX
  have hL : IsProjectiveMorphism (projToSpecCoeff ℂ 1) :=
    IsProjectiveMorphism.of_iso
      (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison ℂ 1).iso (Iso.refl _) (by
        rw [Iso.refl_hom, Category.comp_id]
        exact (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison ℂ 1).toBase)
      ⟨1, 𝟙 _, inferInstance, Category.id_comp _⟩
  exact ⟨finiteDimensional_homology_analyticSpace _ hP, finiteDimensional_cycleSpan hP,
    finiteDimensional_cycleSpan
      (show IsProjectiveMorphism (CategoryTheory.Limits.pullback.snd (X ↘ Spec (.of ℂ))
          (projToSpecCoeff ℂ 1) ≫ projToSpecCoeff ℂ 1) from
        (hP.baseChange (projToSpecCoeff ℂ 1)).comp hL) 2⟩

end MMP.Analytic
