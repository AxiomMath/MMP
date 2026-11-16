module

public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.AlgebraicGeometry.Analytic.BorelMoore
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleBridge.Basic
public import StacksFrontier.Topology.Sheaves.Modules.Invertible
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorGenerator
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
public import MMP.AlgebraicTopology.ThomClass.Natural
public import MMP.AlgebraicTopology.SingularCohomology.Ring
public import MMP.AlgebraicTopology.CapProduct.Support
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.VectorBundle.Basic

/-!
# The first Chern class of a complex line bundle

For a topological space `Y` and a commutative ring `R`, `H^n(Y; R)` is the singular cohomology of
`Y` with coefficients in `R`. It has the unit `1 ∈ H^0(Y; R)`, and a ring homomorphism
`f : R →+* S` induces the change of coefficients `f_* : H^n(Y; R) → H^n(Y; S)`, `[φ] ↦ [f ∘ φ]`
(for instance `H^n(Y; ℤ) → H^n(Y; ℚ)`). For a scheme `X` over `ℂ`, `H^n(X; R)` is the singular
cohomology of the analytic space `X^an`.

Let `E` be a complex topological line bundle on a space `B`. Its first Chern class
`c₁(E) ∈ H²(B; ℤ)` is the primary obstruction to a nowhere vanishing section, the Euler class of
the underlying oriented plane bundle (Milnor–Stasheff, §12 and §14). It is computed as follows.
Over every point `y` take the reference vector of coordinate `1` in the trivialization at `y`.
A singular simplex is *small* if it lies in the base of a trivialization of the atlas, and
each small simplex is assigned such a trivialization. Over a small `1`-simplex `τ`, the reference
vectors at its ends are joined by the path of nonzero vectors whose coordinate in the
trivialization of `τ` has the principal logarithm of the ratio of the end coordinates as its
total logarithmic increment. For a small `2`-simplex `σ`, in the trivialization `e` of `σ` the
coordinate of this section along `∂σ` is a loop in `ℂ^×`; its winding number `n(σ)` is
`1/2πi` times the alternating sum over the edges `τ` of `σ` of the increments of the logarithm,
each increment being that in the trivialization of `τ` plus the increment along `τ` of a
continuous logarithm of the transition function to `e`. In any trivialization over a small
`2`-simplex the same sum is the coboundary of the edge increments, so on small `3`-simplices
`δ n = 0`. The small-chains map `ρ` (Hatcher, Prop. 2.21), chain homotopic to the identity, with
values in small chains and fixing small simplices, carries `n` to a cocycle `n ∘ ρ` on all
singular `2`-simplices, and `c₁(E)` is its class.

## Main definitions

* `MMP.Analytic.singularCohomology R Y n`: `H^n(Y; R)`.
* `MMP.Analytic.singularCohomology.one`: the unit `1 ∈ H^0(Y; R)`.
* `MMP.Analytic.singularCohomology.mapCoeff`: the change of coefficients `f_*`.
* `MMP.Analytic.analyticSingularCohomology R sX n`: `H^n(X^an; R)`.
* `MMP.Analytic.logIncrement f τ`: the increment along a `1`-simplex `τ` of a continuous
  logarithm of `f ∘ τ`.
* `MMP.Analytic.ComplexLineBundle.transition`: the transition functions of a complex line
  bundle.
* `MMP.Analytic.ComplexLineBundle.obstructionPhase`: `2πi` times the winding number of the
  reference section around the boundary of a `2`-simplex.
* `MMP.Analytic.ComplexLineBundle.obstructionCocycle`: the obstruction cocycle `n ∘ ρ`.
* `MMP.Analytic.firstChernClass E`: `c₁(E) ∈ H²(B; ℤ)`.
* `MMP.Analytic.analyticFirstChernClass L`: `c₁(L) ∈ H²(X^an; ℤ)` for a complex topological
  line bundle `L` on `X^an`.
* `MMP.Analytic.InvertibleModule.Generator L`: a local generator `a ∈ L(W)` of an
  `𝒪_X`-module, with `c ↦ c • a|_V` bijective `𝒪_X(V) → L(V)` for all `V ⊆ W`.
* `MMP.Analytic.InvertibleModule.transitionSection`: the transition function `g` of two local
  generators, `a = g • a'` on the overlap.
* `MMP.Analytic.InvertibleModule.lineBundleCore L`, `topologicalLineBundle L`: the complex
  topological line bundle on `X^an` underlying an invertible `𝒪_X`-module `L`, with charts the
  local generators and changes of coordinates the values of the transition functions.
* `MMP.Analytic.algebraicFirstChernClass L`: `c₁(L) ∈ H²(X^an; ℤ)` for an invertible
  `𝒪_X`-module `L`.

## Main results

* `MMP.Analytic.singularCohomology.mapCoeff_ofCocycle`, `mapCoeff_one`: `f_* [φ] = [f ∘ φ]` and
  `f_* 1 = 1`.
* `MMP.Analytic.exists_continuous_log`: a nowhere vanishing continuous function on a standard
  simplex has a continuous logarithm.
* `MMP.Analytic.sum_logIncrement_face`: the increments of a continuous logarithm around the
  boundary of a `2`-simplex cancel.
* `MMP.Analytic.ComplexLineBundle.exists_obstructionPhase_eq`: the obstruction phase of a small
  `2`-simplex lies in `2πi ℤ`.
* `MMP.Analytic.ComplexLineBundle.coboundary_obstructionCochain`: `δ n = 0` on small
  `3`-simplices.
* `MMP.Analytic.ComplexLineBundle.coboundary_obstructionCocycle`: `n ∘ ρ` is a cocycle.
* `MMP.Analytic.ComplexLineBundle.obstructionCocycle_mul`: on a small `2`-simplex, `n ∘ ρ` is the
  winding number of the reference section around its boundary.
* `MMP.Analytic.InvertibleModule.exists_generator`: an invertible module has a local generator
  around every point (Stacks, Tag 0B8M).
* `MMP.Analytic.InvertibleModule.transitionSection_trans`: the cocycle condition `g₁₃ = g₁₂ g₂₃`.
* `MMP.Analytic.InvertibleModule.continuousOn_evalExt`: evaluation of a section over `U` is
  continuous on `U(ℂ) ⊆ X^an`.
* `MMP.Analytic.algebraicFirstChernClass_eq_of_iso`: isomorphic invertible modules have the same
  first Chern class.
* `MMP.Analytic.algebraicFirstChernClass_sheafTensor`: `c₁(L ⊗ M) = c₁(L) + c₁(M)`.
* `MMP.Analytic.algebraicFirstChernClass_pullback`: `c₁(f^* L) = f^* c₁(L)` for a morphism `f`
  over `ℂ`.

## Implementation notes

* The line bundle is a Mathlib vector bundle with fibre `ℂ`, and the trivializing opens are the
  base sets of its atlas. The trivialization assigned to a small simplex and the continuous
  logarithms are chosen; every choice is among objects shown to exist, and the increments of
  continuous logarithms do not depend on the logarithm. That the class does not depend on the
  remaining choices (the trivializations of simplices, the reference vectors and the paths over
  edges) is not proved here.
* The sign is that of the obstruction cocycle, the winding number of the section around `∂σ`
  for the complex orientation of the fibres; the identification with the Euler class
  `e(E_ℝ) = c₁(E)` of Milnor–Stasheff, Thm. 12.5 and §14, is not proved here.
* Integral cohomology is that of a space in `Type`, the universe of `ℤ`.
* An invertible module is `AlgebraicGeometry.SheafOfModules.IsInvertible`; the topological line
  bundle is built over the `ℂ`-points of `X` over `ℂ` with structure morphism `X ↘ Spec ℂ`, from
  all local generators. Its fibre over `x` is not identified here with the fibre `L(x)` of `L`.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004], Appendix A.
* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], §§12, 14.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.21.
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M).
* [A. Dold, *Lectures on Algebraic Topology*][dold1995], VI.7.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace MMP.Analytic

open MMP MMP.SingularChain MMP.SingularCochain

variable (R : Type u) [CommRing R]

/-- The singular cohomology `H^n(Y; R)` of a space `Y` with coefficients in a commutative
ring `R`. -/
abbrev singularCohomology (Y : TopCat.{u}) (n : ℕ) : ModuleCat.{u} R :=
  cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ n

namespace singularCohomology

/-- The unit `1 ∈ H^0(Y; R)`, the class of the constant `0`-cocycle `1`. -/
def one (Y : TopCat.{u}) : singularCohomology R Y 0 :=
  CohomologyRing.oneNat R Y

variable {R} {S : Type u} [CommRing S] (f : R →+* S) {Y : TopCat.{u}}

/-- Composition with `f : R →+* S`, an `f`-semilinear map of singular cochains. -/
def cochainMap (n : ℕ) : (Simplex Y n → R) →ₛₗ[f] (Simplex Y n → S) where
  toFun φ := f ∘ φ
  map_add' φ ψ := by ext; simp
  map_smul' r φ := by ext; simp

/-- `cochainMap f n φ σ = f (φ σ)`. -/
@[simp]
lemma cochainMap_apply {n : ℕ} (φ : Simplex Y n → R) (σ : Simplex Y n) :
    cochainMap f n φ σ = f (φ σ) :=
  rfl

/-- Composition with `f` commutes with the coboundary. -/
lemma coboundary_cochainMap (n : ℕ) (φ : Simplex Y n → R) :
    coboundary S n (cochainMap f n φ) = cochainMap f (n + 1) (coboundary R n φ) := by
  ext σ
  simp [coboundary_apply, map_sum]

/-- Composition with `f` carries a cochain vanishing on the simplices in `A` to one vanishing on
the simplices in `A`. -/
lemma cochainMap_mem_vanishing {n : ℕ} {A : Set Y} {φ : Simplex Y n → R}
    (hφ : φ ∈ vanishing R n A) : cochainMap f n φ ∈ vanishing S n A := fun σ hσ ↦ by
  simp [hφ σ hσ]

/-- Composition with `f` carries relative cocycles to relative cocycles. -/
lemma cochainMap_mem_relCocycles {n : ℕ} {A : Set Y} {φ : Simplex Y n → R}
    (hφ : φ ∈ relCocycles R A n) : cochainMap f n φ ∈ relCocycles S A n :=
  ⟨cochainMap_mem_vanishing f hφ.1, by
    change coboundary S n _ = 0
    rw [coboundary_cochainMap]
    rw [show coboundary R n φ = 0 from hφ.2, map_zero]⟩

/-- Composition with `f` carries relative coboundaries to relative coboundaries. -/
lemma cochainMap_mem_relCoboundaries {n : ℕ} {A : Set Y} {φ : Simplex Y n → R}
    (hφ : φ ∈ relCoboundaries R A n) : cochainMap f n φ ∈ relCoboundaries S A n := by
  cases n with
  | zero =>
    change φ ∈ (⊥ : Submodule R _) at hφ
    rw [Submodule.mem_bot] at hφ
    subst hφ
    rw [map_zero]
    exact zero_mem _
  | succ n =>
    obtain ⟨α, hα, rfl⟩ := hφ
    exact ⟨cochainMap f n α, cochainMap_mem_vanishing f hα, coboundary_cochainMap f n α⟩

/-- The change of coefficients on relative cocycles. -/
def relCocyclesMap (A : Set Y) (n : ℕ) : relCocycles R A n →ₛₗ[f] relCocycles S A n :=
  LinearMap.codRestrict (relCocycles S A n) ((cochainMap f n).comp (relCocycles R A n).subtype)
    fun φ ↦ cochainMap_mem_relCocycles f φ.2

/-- The change of coefficients `Z^n(Y, A; R) / B^n(Y, A; R) → Z^n(Y, A; S) / B^n(Y, A; S)`. -/
def relCohomologyMap (A : Set Y) (n : ℕ) : relCohomology R A n →ₛₗ[f] relCohomology S A n :=
  Submodule.mapQ _ _ (relCocyclesMap f A n) fun _ hφ ↦ cochainMap_mem_relCoboundaries f hφ

/-- The change of coefficients `f_* : H^n(Y; R) → H^n(Y; S)` along `f : R →+* S`,
`[φ] ↦ [f ∘ φ]`. -/
def mapCoeff (n : ℕ) : singularCohomology R Y n →ₛₗ[f] singularCohomology S Y n :=
  ((relativeSingularCohomologyEquiv S (Set.univᶜ : Set Y) n).symm.toLinearMap.comp
    (relCohomologyMap f (Set.univᶜ : Set Y) n)).comp
      (relativeSingularCohomologyEquiv R (Set.univᶜ : Set Y) n).toLinearMap

/-- `f_* [φ] = [f ∘ φ]`. -/
theorem mapCoeff_ofCocycle {n : ℕ} (φ : Simplex Y n → R)
    (hφ : φ ∈ relCocycles R (Set.univᶜ : Set Y) n) :
    mapCoeff f n (cohomologyWithSupports.ofCocycle R Y n φ hφ) =
      cohomologyWithSupports.ofCocycle S Y n (cochainMap f n φ)
        (cochainMap_mem_relCocycles f hφ) := by
  simp only [mapCoeff, cohomologyWithSupports.ofCocycle, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The change of coefficients preserves the unit: `f_* 1 = 1`. -/
@[simp]
theorem mapCoeff_one : mapCoeff f 0 (one R Y) = one S Y := by
  rw [one, CohomologyRing.oneNat, mapCoeff_ofCocycle, one, CohomologyRing.oneNat]
  exact cohomologyWithSupports.ofCocycle_congr (by ext; simp [PoincareAlexander.constCochain])
    _ _

end singularCohomology

section analytic

variable (R : Type) [CommRing R] {X : AlgebraicGeometry.Scheme.{0}}
  (sX : X ⟶ AlgebraicGeometry.Spec (.of ℂ))

/-- The singular cohomology `H^n(X; R) = H^n(X^an; R)` of a scheme `X` over `ℂ`: that of its
complex points with the analytic topology. -/
abbrev analyticSingularCohomology (n : ℕ) : ModuleCat R :=
  singularCohomology R (Analytification.space sX) n

end analytic

/-! ### Increments of logarithms along singular simplices -/

section logIncrement

open Complex

variable {Y : Type*} [TopologicalSpace Y]

/-- A standard simplex is preconnected. -/
lemma preconnectedSpace_stdSimplex (n : ℕ) : PreconnectedSpace (stdSimplex ℝ (Fin (n + 1))) :=
  Subtype.preconnectedSpace (convex_stdSimplex ℝ _).isPreconnected

/-- A nowhere vanishing continuous function on a standard simplex has a continuous logarithm. -/
lemma exists_continuous_log {n : ℕ} (g : C(stdSimplex ℝ (Fin (n + 1)), ℂ)) (hg : ∀ x, g x ≠ 0) :
    ∃ L : C(stdSimplex ℝ (Fin (n + 1)), ℂ), ∀ x, exp (L x) = g x := by
  have hne : (stdSimplex ℝ (Fin (n + 1))).Nonempty :=
    ⟨_, (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))).2⟩
  have : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ _).contractibleSpace hne
  have : LocallyPathConnectedSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ _).locallyPathConnectedSpace
  obtain ⟨F, ⟨-, hF⟩, -⟩ := isCoveringMapOn_exp.existsUnique_continuousMap_lifts g
    (a₀ := stdSimplex.vertex 0) (e₀ := log (g (stdSimplex.vertex 0)))
    (exp_log (hg _)) fun x ↦ hg x
  exact ⟨F, fun x ↦ congr_fun hF x⟩

/-- Two continuous logarithms of the same function on a standard simplex differ by a
constant. -/
lemma continuous_log_sub_eq {n : ℕ} {L L' : C(stdSimplex ℝ (Fin (n + 1)), ℂ)}
    (h : ∀ x, exp (L x) = exp (L' x)) (x y : stdSimplex ℝ (Fin (n + 1))) :
    L x - L y = L' x - L' y := by
  have := preconnectedSpace_stdSimplex n
  set c := L' y - L y
  have hc : exp c = 1 := by rw [exp_sub, h y, div_self (exp_ne_zero _)]
  have key : (fun z ↦ L' z) = fun z ↦ L z + c := by
    refine isCoveringMap_exp.eq_of_comp_eq L'.continuous (L.continuous.add continuous_const)
      ?_ y (by simp [c])
    funext z
    simp only [Function.comp_apply, Subtype.mk.injEq]
    rw [exp_add, hc, mul_one, h z]
  rw [congr_fun key x, congr_fun key y]
  ring

/-- The increment `L(1) - L(0)` of a continuous logarithm `L` of `f ∘ τ` along a singular
`1`-simplex `τ` (zero if `f ∘ τ` has no continuous logarithm); it does not depend on `L`. -/
def logIncrement (f : Y → ℂ) (τ : Simplex Y 1) : ℂ := by
  classical
  exact if h : ∃ L : C(stdSimplex ℝ (Fin 2), ℂ), ∀ x, exp (L x) = f (τ x) then
    h.choose (stdSimplex.vertex 1) - h.choose (stdSimplex.vertex 0) else 0

/-- `logIncrement f τ` is `L(1) - L(0)` for any continuous logarithm `L` of `f ∘ τ`. -/
lemma logIncrement_eq {f : Y → ℂ} {τ : Simplex Y 1} (L : C(stdSimplex ℝ (Fin 2), ℂ))
    (hL : ∀ x, exp (L x) = f (τ x)) :
    logIncrement f τ = L (stdSimplex.vertex 1) - L (stdSimplex.vertex 0) := by
  have h : ∃ L : C(stdSimplex ℝ (Fin 2), ℂ), ∀ x, exp (L x) = f (τ x) := ⟨L, hL⟩
  rw [logIncrement, dite_eq_left h]
  exact continuous_log_sub_eq (n := 1) (fun x ↦ by rw [h.choose_spec, hL]) _ _

/-- A function continuous and nowhere zero on a set containing the image of a simplex has a
continuous logarithm along the simplex. -/
lemma exists_continuous_log_comp {m : ℕ} (σ : Simplex Y m) {f : Y → ℂ} {S : Set Y}
    (hf : ContinuousOn f S) (h0 : ∀ y ∈ S, f y ≠ 0) (hσ : Set.range σ ⊆ S) :
    ∃ L : C(stdSimplex ℝ (Fin (m + 1)), ℂ), ∀ x, exp (L x) = f (σ x) :=
  exists_continuous_log ⟨f ∘ σ, hf.comp_continuous σ.continuous fun x ↦ hσ ⟨x, rfl⟩⟩
    fun x ↦ h0 _ (hσ ⟨x, rfl⟩)

/-- Along the `1`-simplex `σ ∘ g`, the increment is `L(g(1)) - L(g(0))` for any continuous
logarithm `L` of `f ∘ σ`. -/
lemma logIncrement_comp {m : ℕ} {f : Y → ℂ} (σ : Simplex Y m)
    (L : C(stdSimplex ℝ (Fin (m + 1)), ℂ)) (hL : ∀ x, exp (L x) = f (σ x))
    (g : C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin (m + 1)))) :
    logIncrement f (σ.comp g) = L (g (stdSimplex.vertex 1)) - L (g (stdSimplex.vertex 0)) :=
  logIncrement_eq (L.comp g) fun x ↦ hL (g x)

/-- If `f = g * h` along `τ` and `g ∘ τ`, `h ∘ τ` have continuous logarithms, the increment of
`f` along `τ` is the sum of those of `g` and `h`. -/
lemma logIncrement_mul {f g h : Y → ℂ} {τ : Simplex Y 1}
    (hfgh : ∀ x, f (τ x) = g (τ x) * h (τ x))
    (hg : ∃ L : C(stdSimplex ℝ (Fin 2), ℂ), ∀ x, exp (L x) = g (τ x))
    (hh : ∃ L : C(stdSimplex ℝ (Fin 2), ℂ), ∀ x, exp (L x) = h (τ x)) :
    logIncrement f τ = logIncrement g τ + logIncrement h τ := by
  obtain ⟨Lg, hLg⟩ := hg
  obtain ⟨Lh, hLh⟩ := hh
  rw [logIncrement_eq Lg hLg, logIncrement_eq Lh hLh, logIncrement_eq (Lg + Lh)
    fun x ↦ by simp [exp_add, hLg, hLh, hfgh]]
  simp only [ContinuousMap.add_apply]
  ring

/-- The `k`-th face map of the standard `2`-simplex sends the vertex `j` to the vertex
`k.succAbove j`. -/
lemma face_vertex (k : Fin 3) (j : Fin 2) :
    face 1 k (stdSimplex.vertex j) = stdSimplex.vertex (k.succAbove j) := by
  simp [face, stdSimplex.map_vertex]

/-- The increments of a continuous logarithm along the boundary of a `2`-simplex cancel. -/
lemma sum_logIncrement_face {f : Y → ℂ} (σ : Simplex Y 2)
    (hσ : ∃ L : C(stdSimplex ℝ (Fin 3), ℂ), ∀ x, exp (L x) = f (σ x)) :
    ∑ k : Fin 3, (-1 : ℂ) ^ (k : ℕ) * logIncrement f (σ.comp (face 1 k)) = 0 := by
  obtain ⟨L, hL⟩ := hσ
  simp only [logIncrement_comp σ L hL, face_vertex, Fin.sum_univ_three]
  have h0 : (0 : Fin 3).succAbove 0 = 1 := rfl
  have h1 : (0 : Fin 3).succAbove 1 = 2 := rfl
  have h2 : (1 : Fin 3).succAbove 0 = 0 := rfl
  have h3 : (1 : Fin 3).succAbove 1 = 2 := rfl
  have h4 : (2 : Fin 3).succAbove 0 = 0 := rfl
  have h5 : (2 : Fin 3).succAbove 1 = 1 := rfl
  simp only [h0, h1, h2, h3, h4, h5, Fin.val_zero, Fin.val_one, Fin.val_two]
  ring

end logIncrement

/-! ### Transition functions of a complex line bundle -/

namespace ComplexLineBundle

open Bundle FiberBundle Complex

variable {B : Type*} [TopologicalSpace B] (E : B → Type*) [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℂ (E b)] [TopologicalSpace (TotalSpace ℂ E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]

variable {E}

/-- The transition function `g_{e e'}(b) ∈ ℂ` between two trivializations of a complex line
bundle: the `e'`-coordinate of the vector with `e`-coordinate `1` over `b`. -/
def transition (e e' : Trivialization ℂ (π ℂ E)) (b : B) : ℂ := (e' ⟨b, e.symm b 1⟩).2

section

variable {e e' e'' : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
  [MemTrivializationAtlas e'] [MemTrivializationAtlas e'']

/-- On the overlap of the base sets, `transition e e' b` is the coordinate change from `e` to `e'`
at `b` applied to `1`. -/
lemma transition_eq_coordChangeL {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    transition e e' b = e.coordChangeL ℂ e' b 1 :=
  (e.coordChangeL_apply e' hb 1).symm

/-- On the overlap of the base sets, the coordinate change from `e` to `e'` is multiplication by
`transition e e'`. -/
lemma coordChangeL_eq_mul_transition {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : ℂ) :
    e.coordChangeL ℂ e' b v = v * transition e e' b := by
  rw [transition_eq_coordChangeL hb, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- The transition function does not vanish on the overlap of the base sets. -/
lemma transition_ne_zero {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) : transition e e' b ≠ 0 := by
  rw [transition_eq_coordChangeL hb]
  exact (map_ne_zero_iff _ (e.coordChangeL ℂ e' b).injective).2 one_ne_zero

/-- The transition function is continuous on the overlap of the base sets. -/
lemma continuousOn_transition : ContinuousOn (transition e e') (e.baseSet ∩ e'.baseSet) := by
  have h := (VectorBundle.continuousOn_coordChange' (R := ℂ) e e').clm_apply
    (continuousOn_const (c := (1 : ℂ)))
  exact h.congr fun b hb ↦ transition_eq_coordChangeL hb

/-- The cocycle condition `g_{e e''} = g_{e' e''} g_{e e'}` on a triple overlap. -/
lemma transition_trans {b : B} (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet)
    (hb'' : b ∈ e''.baseSet) :
    transition e e'' b = transition e' e'' b * transition e e' b := by
  have hcomp : e'.coordChangeL ℂ e'' b (e.coordChangeL ℂ e' b 1) = e.coordChangeL ℂ e'' b 1 := by
    rw [Trivialization.coe_coordChangeL e' e'' ⟨hb', hb''⟩,
      Trivialization.coe_coordChangeL e e' ⟨hb, hb'⟩,
      Trivialization.coe_coordChangeL e e'' ⟨hb, hb''⟩]
    simp [Trivialization.symm_apply_apply_mk e' hb']
  rw [transition_eq_coordChangeL ⟨hb, hb''⟩, ← hcomp, coordChangeL_eq_mul_transition ⟨hb', hb''⟩,
    transition_eq_coordChangeL ⟨hb, hb'⟩, mul_comm]

end

variable (E) in
/-- The base sets of the trivializations in the atlas, an open cover of the base. -/
def atlasCover : Set (Set B) := (fun e ↦ e.baseSet) '' trivializationAtlas ℂ E

omit [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [VectorBundle ℂ ℂ E] in
/-- Every member of `atlasCover E` is open. -/
lemma isOpen_of_mem_atlasCover {U : Set B} (hU : U ∈ atlasCover E) : IsOpen U := by
  obtain ⟨e, -, rfl⟩ := hU
  exact e.open_baseSet

omit [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [VectorBundle ℂ ℂ E] in
/-- The base sets of the trivializations in the atlas cover `B`. -/
lemma sUnion_atlasCover : ⋃₀ atlasCover E = Set.univ :=
  Set.eq_univ_of_forall fun b ↦ ⟨_, ⟨_, trivialization_mem_atlas ℂ E b, rfl⟩,
    mem_baseSet_trivializationAt ℂ E b⟩

/-- A trivialization of the atlas over the image of a simplex, when there is one. -/
def simplexTriv {n : ℕ} (σ : Simplex B n) : Trivialization ℂ (π ℂ E) := by
  classical
  exact if h : ∃ e ∈ trivializationAtlas ℂ E, Set.range σ ⊆ e.baseSet then h.choose
    else trivializationAt ℂ E (σ (stdSimplex.vertex 0))

omit [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [VectorBundle ℂ ℂ E] in
/-- The trivialization `simplexTriv σ` belongs to the atlas. -/
lemma simplexTriv_mem {n : ℕ} (σ : Simplex B n) :
    simplexTriv (E := E) σ ∈ trivializationAtlas ℂ E := by
  rw [simplexTriv]
  split_ifs with h
  · exact h.choose_spec.1
  · exact trivialization_mem_atlas ℂ E _

/-- The trivialization `simplexTriv σ` is a trivialization of the atlas. -/
instance {n : ℕ} (σ : Simplex B n) : MemTrivializationAtlas (simplexTriv (E := E) σ) :=
  ⟨simplexTriv_mem σ⟩

omit [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [VectorBundle ℂ ℂ E] in
/-- If the image of `σ` lies in the base set of a trivialization of the atlas, it lies in the
base set of `simplexTriv σ`. -/
lemma range_subset_simplexTriv {n : ℕ} {σ : Simplex B n} {e : Trivialization ℂ (π ℂ E)}
    (he : e ∈ trivializationAtlas ℂ E) (hσ : Set.range σ ⊆ e.baseSet) :
    Set.range σ ⊆ (simplexTriv (E := E) σ).baseSet := by
  have h : ∃ e ∈ trivializationAtlas ℂ E, Set.range σ ⊆ e.baseSet := ⟨e, he, hσ⟩
  rw [simplexTriv, dite_eq_left h]
  exact h.choose_spec.2

/-- The `e`-coordinate of the reference vector over `y`, the vector of coordinate `1` in the
trivialization `trivializationAt y`. -/
def vertexCoord (e : Trivialization ℂ (π ℂ E)) (y : B) : ℂ :=
  transition (trivializationAt ℂ E y) e y

/-- The `e`-coordinate of the reference vector over a point of `e.baseSet` is nonzero. -/
lemma vertexCoord_ne_zero {e : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e] {y : B}
    (hy : y ∈ e.baseSet) : vertexCoord e y ≠ 0 :=
  transition_ne_zero ⟨mem_baseSet_trivializationAt ℂ E y, hy⟩

/-- The coordinates of the reference vector in two trivializations differ by the transition
function: `vertexCoord e' y = transition e e' y * vertexCoord e y`. -/
lemma vertexCoord_eq {e e' : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'] {y : B} (hy : y ∈ e.baseSet) (hy' : y ∈ e'.baseSet) :
    vertexCoord e' y = transition e e' y * vertexCoord e y :=
  transition_trans (mem_baseSet_trivializationAt ℂ E y) hy hy'

/-- The logarithm of the ratio of the reference coordinates at the ends of a `1`-simplex, in
its trivialization: the class of a path of nonzero vectors over the simplex joining the
reference vectors. -/
def edgeLog (τ : Simplex B 1) : ℂ :=
  log (vertexCoord (simplexTriv (E := E) τ) (τ (stdSimplex.vertex 1)) /
    vertexCoord (simplexTriv (E := E) τ) (τ (stdSimplex.vertex 0)))

/-- The increment of the logarithm of the coordinate of the reference path over `τ`, in the
trivialization `e`. -/
def edgePhase (e : Trivialization ℂ (π ℂ E)) (τ : Simplex B 1) : ℂ :=
  edgeLog (E := E) τ + logIncrement (transition (simplexTriv (E := E) τ) e) τ

/-- For a trivialization `e` of the atlas over `τ`, the exponential of the edge phase of `τ` in
`e` is the ratio of the `e`-coordinates of the reference vectors at the ends of `τ`. -/
lemma exp_edgePhase {e : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e] {τ : Simplex B 1}
    (hτ : Set.range τ ⊆ e.baseSet) :
    exp (edgePhase e τ) = vertexCoord e (τ (stdSimplex.vertex 1)) /
      vertexCoord e (τ (stdSimplex.vertex 0)) := by
  have hτ' := range_subset_simplexTriv (E := E) (MemTrivializationAtlas.out (e := e)) hτ
  have hS : Set.range τ ⊆ (simplexTriv (E := E) τ).baseSet ∩ e.baseSet :=
    Set.subset_inter hτ' hτ
  obtain ⟨L, hL⟩ := exists_continuous_log_comp τ continuousOn_transition
    (fun y hy ↦ transition_ne_zero hy) hS
  have h1 : τ (stdSimplex.vertex 1) ∈ Set.range τ := ⟨_, rfl⟩
  have h0 : τ (stdSimplex.vertex 0) ∈ Set.range τ := ⟨_, rfl⟩
  rw [edgePhase, edgeLog, logIncrement_eq L hL, exp_add, exp_sub, hL, hL,
    exp_log (div_ne_zero (vertexCoord_ne_zero (hτ' h1)) (vertexCoord_ne_zero (hτ' h0))),
    vertexCoord_eq (hτ' h1) (hτ h1), vertexCoord_eq (hτ' h0) (hτ h0)]
  have := vertexCoord_ne_zero (hτ' h0)
  have := transition_ne_zero (hS h0)
  field_simp

/-- The obstruction phase of a singular `2`-simplex `σ`: the alternating sum, over the edges of
`σ`, of the increments of the logarithm of the reference section in the trivialization of `σ`.
It is `2πi` times the winding number of the reference section around `∂σ`. -/
def obstructionPhase (σ : Simplex B 2) : ℂ :=
  ∑ k : Fin 3, (-1 : ℂ) ^ (k : ℕ) * edgePhase (simplexTriv (E := E) σ) (σ.comp (face 1 k))

/-- In any trivialization `e` of the atlas over `σ`, the obstruction phase is the coboundary of
the edge phases in `e`. -/
lemma obstructionPhase_eq_coboundary {e : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
    {σ : Simplex B 2} (hσ : Set.range σ ⊆ e.baseSet) :
    obstructionPhase (E := E) σ = coboundary ℂ 1 (edgePhase (E := E) e) σ := by
  have hσ' := range_subset_simplexTriv (E := E) (MemTrivializationAtlas.out (e := e)) hσ
  have hS : Set.range σ ⊆ e.baseSet ∩ (simplexTriv (E := E) σ).baseSet := Set.subset_inter hσ hσ'
  have hlift := exists_continuous_log_comp σ
    (continuousOn_transition (e := e) (e' := (simplexTriv (E := E) σ)))
    (fun y hy ↦ transition_ne_zero hy) hS
  have hsum := sum_logIncrement_face σ hlift
  have hedge : ∀ k : Fin 3, edgePhase (simplexTriv (E := E) σ) (σ.comp (face 1 k)) =
      edgePhase e (σ.comp (face 1 k)) +
        logIncrement (transition e (simplexTriv (E := E) σ)) (σ.comp (face 1 k)) := by
    intro k
    set τ := σ.comp (face 1 k)
    have hτσ : Set.range τ ⊆ Set.range σ := fun _ ⟨t, ht⟩ ↦ ⟨_, ht⟩
    have hτ' := range_subset_simplexTriv (E := E) (MemTrivializationAtlas.out (e := e))
      (hτσ.trans hσ)
    rw [edgePhase, edgePhase, add_assoc,
      logIncrement_mul (g := transition e (simplexTriv (E := E) σ))
      (h := transition (simplexTriv (E := E) τ) e)]
    · ring
    · intro x
      exact transition_trans (hτ' ⟨x, rfl⟩) (hσ (hτσ ⟨x, rfl⟩)) (hσ' (hτσ ⟨x, rfl⟩))
    · exact exists_continuous_log_comp τ continuousOn_transition
        (fun y hy ↦ transition_ne_zero hy) (hτσ.trans hS)
    · exact exists_continuous_log_comp τ continuousOn_transition
        (fun y hy ↦ transition_ne_zero hy) (Set.subset_inter hτ' (hτσ.trans hσ))
  rw [obstructionPhase, coboundary_apply]
  simp only [hedge, mul_add, Finset.sum_add_distrib, hsum, add_zero]

/-- The obstruction phase of a simplex inside a trivializing open is `2πi` times an integer. -/
lemma exists_obstructionPhase_eq {e : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
    {σ : Simplex B 2} (hσ : Set.range σ ⊆ e.baseSet) :
    ∃ m : ℤ, obstructionPhase (E := E) σ = m * (2 * Real.pi * I) := by
  rw [← exp_eq_one_iff, obstructionPhase_eq_coboundary hσ, coboundary_apply]
  have hv : ∀ k : Fin 3, ∀ j : Fin 2, Set.range (σ.comp (face 1 k)) ⊆ e.baseSet :=
    fun k _ ↦ fun _ ⟨t, ht⟩ ↦ hσ ⟨_, ht⟩
  change exp (∑ i : Fin 3, (-1 : ℂ) ^ (i : ℕ) * edgePhase e (σ.comp (face 1 i))) = 1
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, one_mul,
    pow_one, neg_one_mul, neg_one_sq, exp_add, exp_neg,
    exp_edgePhase (hv 0 0), exp_edgePhase (hv 1 0), exp_edgePhase (hv 2 0)]
  simp only [ContinuousMap.comp_apply, face_vertex]
  have h0 : (0 : Fin 3).succAbove 0 = 1 := rfl
  have h1 : (0 : Fin 3).succAbove 1 = 2 := rfl
  have h2 : (1 : Fin 3).succAbove 0 = 0 := rfl
  have h3 : (1 : Fin 3).succAbove 1 = 2 := rfl
  have h4 : (2 : Fin 3).succAbove 0 = 0 := rfl
  have h5 : (2 : Fin 3).succAbove 1 = 1 := rfl
  simp only [h0, h1, h2, h3, h4, h5]
  have := vertexCoord_ne_zero (e := e) (hσ ⟨stdSimplex.vertex 0, rfl⟩)
  have := vertexCoord_ne_zero (e := e) (hσ ⟨stdSimplex.vertex 1, rfl⟩)
  have := vertexCoord_ne_zero (e := e) (hσ ⟨stdSimplex.vertex 2, rfl⟩)
  field_simp

/-- The obstruction cochain: the winding number `obstructionPhase σ / 2πi` of the reference
section around the boundary of a singular `2`-simplex `σ` lying in a trivializing open (and `0`
on the other simplices). -/
def obstructionCochain (σ : Simplex B 2) : ℤ := by
  classical
  exact if h : ∃ m : ℤ, obstructionPhase (E := E) σ = m * (2 * Real.pi * I) then h.choose else 0

/-- On a `2`-simplex lying in a trivializing open, `2πi` times the obstruction cochain is the
obstruction phase. -/
lemma obstructionCochain_mul {e : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
    {σ : Simplex B 2} (hσ : Set.range σ ⊆ e.baseSet) :
    (obstructionCochain (E := E) σ : ℂ) * (2 * Real.pi * I) = obstructionPhase (E := E) σ := by
  have h := exists_obstructionPhase_eq (E := E) hσ
  rw [obstructionCochain, dite_eq_left h]
  exact h.choose_spec.symm

/-- The obstruction cochain is a cocycle on the simplices lying in a trivializing open. -/
lemma coboundary_obstructionCochain {e : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
    {ρ : Simplex B 3} (hρ : Set.range ρ ⊆ e.baseSet) :
    coboundary ℤ 2 (obstructionCochain (E := E)) ρ = 0 := by
  have hface : ∀ j : Fin 4, Set.range (ρ.comp (face 2 j)) ⊆ e.baseSet :=
    fun _ ↦ fun _ ⟨t, ht⟩ ↦ hρ ⟨_, ht⟩
  have key : ((coboundary ℤ 2 (obstructionCochain (E := E)) ρ : ℤ) : ℂ) *
      (2 * Real.pi * I) = 0 := by
    rw [coboundary_apply]
    push_cast
    rw [Finset.sum_mul]
    have hj : ∀ j : Fin (2 + 2), (-1 : ℂ) ^ (j : ℕ) *
        (obstructionCochain (E := E) (ρ.comp (face 2 j)) : ℂ) * (2 * Real.pi * I) =
          (-1 : ℂ) ^ (j : ℕ) * coboundary ℂ 1 (edgePhase (E := E) e) (ρ.comp (face 2 j)) :=
      fun j ↦ by
        rw [mul_assoc, obstructionCochain_mul (hface j), obstructionPhase_eq_coboundary (hface j)]
    rw [Finset.sum_congr rfl fun j _ ↦ hj j]
    have := congr_fun (coboundary_coboundary 1 (edgePhase (E := E) e)) ρ
    rw [coboundary_apply] at this
    exact this
  exact_mod_cast (mul_eq_zero.1 key).resolve_right two_pi_I_ne_zero

/-- A cochain vanishing on the `𝒰`-small simplices vanishes on every `𝒰`-small chain. -/
lemma eval_eq_zero_of_mem_small {n : ℕ} {φ : Simplex B n → ℤ} {𝒰 : Set (Set B)}
    (hφ : ∀ σ : Simplex B n, (∃ U ∈ 𝒰, Set.range σ ⊆ U) → φ σ = 0) {c : Chain ℤ B n}
    (hc : c ∈ small ℤ n 𝒰) : SingularCochain.eval φ c = 0 := by
  rw [Finsupp.mem_supported] at hc
  rw [SingularCochain.eval, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_eq_zero fun σ hσ ↦ by rw [hφ σ (hc hσ), smul_zero]

variable (E) in
/-- The obstruction cocycle on all singular `2`-simplices: the obstruction cochain on the
atlas-small simplices, transported to all simplices by the small-chains map `ρ`. -/
def obstructionCocycle : Simplex B 2 → ℤ :=
  SingularCochain.pullback (smallChainMap ℤ (atlasCover E) 2) (obstructionCochain (E := E))

/-- The obstruction cocycle is a cocycle. -/
lemma coboundary_obstructionCocycle : coboundary ℤ 2 (obstructionCocycle E) = 0 := by
  rw [obstructionCocycle, coboundary_pullback_smallChainMap]
  funext σ
  refine eval_eq_zero_of_mem_small (𝒰 := atlasCover E) ?_
    (smallChainMap_single_mem_small (fun _ hU ↦ isOpen_of_mem_atlasCover hU) 3
      (by rw [sUnion_atlasCover]; exact Set.subset_univ _))
  rintro ρ ⟨_, ⟨e, he, rfl⟩, hρ⟩
  have : MemTrivializationAtlas e := ⟨he⟩
  exact coboundary_obstructionCochain hρ

/-- On a simplex lying in a trivializing open, the obstruction cocycle is the winding number
`obstructionPhase σ / 2πi`. -/
lemma obstructionCocycle_mul {e : Trivialization ℂ (π ℂ E)} [MemTrivializationAtlas e]
    {σ : Simplex B 2} (hσ : Set.range σ ⊆ e.baseSet) :
    (obstructionCocycle E σ : ℂ) * (2 * Real.pi * I) = obstructionPhase (E := E) σ := by
  have hfix := smallChainMap_single_of_subset (R := ℤ) (𝒰 := atlasCover E)
    ⟨_, ⟨e, MemTrivializationAtlas.out, rfl⟩, hσ⟩
  have : obstructionCocycle E σ = obstructionCochain (E := E) σ := by
    simp [obstructionCocycle, SingularCochain.pullback, hfix]
  rw [this, obstructionCochain_mul hσ]

end ComplexLineBundle

section firstChernClass

open Bundle FiberBundle ComplexLineBundle

variable {B : Type} [TopologicalSpace B] (E : B → Type*) [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℂ (E b)] [TopologicalSpace (TotalSpace ℂ E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]

/-- The obstruction cocycle is a cocycle relative to the empty set `Set.univᶜ`. -/
lemma obstructionCocycle_mem_relCocycles :
    obstructionCocycle E ∈ relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2 :=
  ⟨fun σ hσ ↦ absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp),
    LinearMap.mem_ker.2 (coboundary_obstructionCocycle (E := E))⟩

/-- The first Chern class `c₁(E) ∈ H²(B; ℤ)` of a complex topological line bundle `E` on `B`:
the class of the obstruction cocycle, whose value on a singular `2`-simplex in a trivializing
open is the winding number around its boundary of a nowhere vanishing section over the edges. -/
@[mmp "def_pab_topological_chern_class"]
def firstChernClass : singularCohomology ℤ (TopCat.of B) 2 :=
  cohomologyWithSupports.ofCocycle ℤ (TopCat.of B) 2 (obstructionCocycle E)
    (obstructionCocycle_mem_relCocycles E)

variable {X : AlgebraicGeometry.Scheme.{0}} {sX : X ⟶ AlgebraicGeometry.Spec (.of ℂ)}
  (L : Analytification.space sX → Type*) [∀ x, AddCommGroup (L x)] [∀ x, Module ℂ (L x)]
  [TopologicalSpace (TotalSpace ℂ L)] [∀ x, TopologicalSpace (L x)] [FiberBundle ℂ L]
  [VectorBundle ℂ ℂ L]

/-- The first Chern class `c₁(L) ∈ H²(X; ℤ) = H²(X^an; ℤ)` of a complex topological line
bundle `L` on the analytic space `X^an` of a scheme `X` over `ℂ`. -/
@[mmp "def_pab_topological_chern_class"]
abbrev analyticFirstChernClass : analyticSingularCohomology ℤ sX 2 :=
  firstChernClass L

end firstChernClass

/-! ### The topological line bundle of an invertible module -/

namespace InvertibleModule

open AlgebraicGeometry Opposite

variable {X : Scheme.{0}} (L : X.Modules)

/-- The restriction `L(W) → L(V)` of sections of an `𝒪_X`-module. -/
def sectionRes {V W : X.Opens} (h : V ≤ W) (a : Γ(L, W)) : Γ(L, V) :=
  L.val.map (homOfLE h).op a

variable {L}

/-- Restriction is semilinear: `(c • a)|_V = c|_V • a|_V`. -/
lemma sectionRes_smul {V W : X.Opens} (h : V ≤ W) (c : Γ(X, W)) (a : Γ(L, W)) :
    sectionRes L h (c • a) = (X.presheaf.map (homOfLE h).op c) • sectionRes L h a :=
  PresheafOfModules.map_smul _ _ _ _

/-- Restriction of sections of `L` is transitive: `(a|_V)|_U = a|_U`. -/
lemma sectionRes_sectionRes {U V W : X.Opens} (h : V ≤ W) (h' : U ≤ V) (a : Γ(L, W)) :
    sectionRes L h' (sectionRes L h a) = sectionRes L (h'.trans h) a :=
  (PresheafOfModules.map_comp_apply L.val (homOfLE h).op (homOfLE h').op a).symm

/-- Restriction of sections of `𝒪_X` is transitive: `(c|_V)|_U = c|_U`. -/
lemma presheaf_map_map {U V W : X.Opens} (h : V ≤ W) (h' : U ≤ V) (c : Γ(X, W)) :
    X.presheaf.map (homOfLE h').op (X.presheaf.map (homOfLE h).op c) =
      X.presheaf.map (homOfLE (h'.trans h)).op c := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable (L) in
/-- A *local generator* of `L`: a section `a ∈ L(W)` such that for every open `V ⊆ W` the map
`𝒪_X(V) → L(V)`, `c ↦ c • a|_V`, is bijective, i.e. `a` trivializes `L` over `W`. -/
structure Generator where
  /-- The open over which the generator is defined. -/
  W : X.Opens
  /-- The generating section. -/
  a : Γ(L, W)
  bijective : ∀ (V : X.Opens) (h : V ≤ W),
    Function.Bijective fun c : Γ(X, V) ↦ c • sectionRes L h a

/-- Every point of `X` lies in the open of a local generator of an invertible module. -/
lemma exists_generator [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (x : X) :
    ∃ s : Generator L, x ∈ s.W := by
  have : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  have : ∀ z : X.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace z) :=
    fun z ↦ X.isLocalRing z
  obtain ⟨W, hx, a, ha⟩ :=
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := X.toRingedSpace) L x
  exact ⟨⟨W, a, ha⟩, hx⟩

namespace Generator

variable (s : Generator L)

/-- The coefficient `c ∈ 𝒪_X(V)` of a section `t ∈ L(V)`, `V ⊆ W`: `t = c • a|_V`. -/
def coeff {V : X.Opens} (h : V ≤ s.W) (t : Γ(L, V)) : Γ(X, V) :=
  (Equiv.ofBijective _ (s.bijective V h)).symm t

/-- A section `t ∈ L(V)` is its coefficient times the generator: `t = s.coeff h t • a|_V`. -/
lemma coeff_smul {V : X.Opens} (h : V ≤ s.W) (t : Γ(L, V)) :
    s.coeff h t • sectionRes L h s.a = t :=
  (Equiv.ofBijective _ (s.bijective V h)).apply_symm_apply t

/-- If `c • a|_V = t`, then `c` is the coefficient of `t`. -/
lemma coeff_eq {V : X.Opens} (h : V ≤ s.W) {t : Γ(L, V)} {c : Γ(X, V)}
    (hc : c • sectionRes L h s.a = t) : s.coeff h t = c :=
  (Equiv.ofBijective _ (s.bijective V h)).symm_apply_eq.2 hc.symm

end Generator

/-- The transition function `g ∈ 𝒪_X(W ∩ W')` of two local generators: `a|_{W ∩ W'} = g • a'`. -/
def transitionSection (s s' : Generator L) : Γ(X, s.W ⊓ s'.W) :=
  s'.coeff inf_le_right (sectionRes L inf_le_left s.a)

/-- The defining relation `g • a'|_{W ∩ W'} = a|_{W ∩ W'}` of the transition function. -/
lemma transitionSection_smul (s s' : Generator L) :
    transitionSection s s' • sectionRes L inf_le_right s'.a = sectionRes L inf_le_left s.a :=
  s'.coeff_smul _ _

/-- The transition function of a local generator with itself is `1`. -/
lemma transitionSection_self (s : Generator L) : transitionSection s s = 1 :=
  s.coeff_eq _ (one_smul _ _)

/-- Restricted to a triple overlap, the transition functions satisfy `g₁₃ = g₁₂ g₂₃`. -/
lemma transitionSection_trans (s₁ s₂ s₃ : Generator L) {T : X.Opens} (h₁₂ : T ≤ s₁.W ⊓ s₂.W)
    (h₂₃ : T ≤ s₂.W ⊓ s₃.W) (h₁₃ : T ≤ s₁.W ⊓ s₃.W) :
    X.presheaf.map (homOfLE h₁₃).op (transitionSection s₁ s₃) =
      X.presheaf.map (homOfLE h₁₂).op (transitionSection s₁ s₂) *
        X.presheaf.map (homOfLE h₂₃).op (transitionSection s₂ s₃) := by
  have hT₃ : T ≤ s₃.W := h₁₃.trans inf_le_right
  have hT₂ : T ≤ s₂.W := h₁₂.trans inf_le_right
  have hT₁ : T ≤ s₁.W := h₁₂.trans inf_le_left
  have e₁₃ := congrArg (sectionRes L h₁₃) (transitionSection_smul s₁ s₃)
  have e₁₂ := congrArg (sectionRes L h₁₂) (transitionSection_smul s₁ s₂)
  have e₂₃ := congrArg (sectionRes L h₂₃) (transitionSection_smul s₂ s₃)
  rw [sectionRes_smul, sectionRes_sectionRes, sectionRes_sectionRes] at e₁₃ e₁₂ e₂₃
  have key : (X.presheaf.map (homOfLE h₁₂).op (transitionSection s₁ s₂) *
      X.presheaf.map (homOfLE h₂₃).op (transitionSection s₂ s₃)) • sectionRes L hT₃ s₃.a =
        sectionRes L hT₁ s₁.a := by
    rw [mul_smul, e₂₃, e₁₂]
  exact (s₃.coeff_eq hT₃ e₁₃).symm.trans (s₃.coeff_eq hT₃ key)

open ComplexPoints

variable [X.Over (Spec (.of ℂ))]

/-- `(U ∩ V)(ℂ) = U(ℂ) ∩ V(ℂ)`. -/
lemma chart_inf (U V : X.Opens) :
    chart (sX := X ↘ Spec (.of ℂ)) (U ⊓ V) = chart U ∩ chart V := by
  ext x
  simp only [Set.mem_inter_iff, mem_chart_iff]
  rfl

/-- For an open `U ⊆ X`, `U(ℂ)` is open in `X^an`. -/
lemma isOpen_chart (U : X.Opens) : IsOpen (chart (sX := X ↘ Spec (.of ℂ)) U) := by
  rw [show chart (sX := X ↘ Spec (.of ℂ)) U = toScheme ⁻¹' (U : Set X) from
    Set.ext fun _ ↦ mem_chart_iff]
  exact U.isOpen.preimage continuous_toScheme

/-- The value at a `ℂ`-point of a section over `U`, extended by `0` off `U(ℂ)`. -/
def evalExt (U : X.Opens) (g : Γ(X, U)) (x : ComplexPoints (X ↘ Spec (.of ℂ))) : ℂ := by
  classical
  exact if hx : x ∈ chart U then eval U g ⟨x, hx⟩ else 0

/-- On `U(ℂ)`, `evalExt U g` is the value of `g`. -/
lemma evalExt_of_mem {U : X.Opens} (g : Γ(X, U)) {x : ComplexPoints (X ↘ Spec (.of ℂ))}
    (hx : x ∈ chart U) :
    evalExt U g x = eval U g ⟨x, hx⟩ := by
  rw [evalExt, dite_eq_left hx]

/-- Evaluation of a section over `U` is continuous on `U(ℂ) ⊆ X^an`. -/
lemma continuousOn_evalExt (U : X.Opens) (g : Γ(X, U)) :
    ContinuousOn (evalExt U g) (chart (sX := X ↘ Spec (.of ℂ)) U) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let φ : chart (sX := X ↘ Spec (.of ℂ)) U →
      {p : MMP.UnderlyingSpace ℂ X // ⊤ ≤ p.toHom ⁻¹ᵁ U} :=
    fun y ↦ ⟨toUnderlyingSpace y.1, top_le_preimage_of_mem_chart y⟩
  have h : (chart (sX := X ↘ Spec (.of ℂ)) U).domRestrict (evalExt U g) =
      (fun p : {p : MMP.UnderlyingSpace ℂ X // ⊤ ≤ p.toHom ⁻¹ᵁ U} ↦
        MMP.UnderlyingSpace.eval p.1 p.2 g) ∘ φ := by
    funext y
    change evalExt U g y.1 = _
    rw [evalExt_of_mem g y.2]
    exact eval_eq g y
  rw [h]
  exact (MMP.UnderlyingSpace.continuous_eval U g).comp
    ((continuous_toUnderlyingSpace.comp continuous_subtype_val).subtype_mk _)

/-- For `V ⊆ U`, the restriction `g|_V` and `g` have the same value at a point of `V(ℂ)`. -/
lemma evalExt_res {U V : X.Opens} (h : V ≤ U) (g : Γ(X, U))
    {x : ComplexPoints (X ↘ Spec (.of ℂ))} (hx : x ∈ chart V) :
    evalExt V (X.presheaf.map (homOfLE h).op g) x = evalExt U g x := by
  rw [evalExt_of_mem _ hx, evalExt_of_mem _ (chart_mono h hx), ← evalHom_apply, ← evalHom_apply,
    evalHom_res h ⟨x, hx⟩]

/-- On `U(ℂ)`, the value of a product of sections is the product of the values. -/
lemma evalExt_mul {U : X.Opens} (g g' : Γ(X, U)) {x : ComplexPoints (X ↘ Spec (.of ℂ))}
    (hx : x ∈ chart U) :
    evalExt U (g * g') x = evalExt U g x * evalExt U g' x := by
  simp only [evalExt_of_mem _ hx, ← evalHom_apply, map_mul]

/-- On `U(ℂ)`, the value of the section `1` is `1`. -/
lemma evalExt_one {U : X.Opens} {x : ComplexPoints (X ↘ Spec (.of ℂ))} (hx : x ∈ chart U) :
    evalExt U (1 : Γ(X, U)) x = 1 := by
  simp only [evalExt_of_mem _ hx, ← evalHom_apply, map_one]

variable (L) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

/-- The topological complex line bundle on `X^an` underlying an invertible `𝒪_X`-module `L`, as
a vector bundle core: its charts are the local generators `a ∈ L(W)` of `L`, over `W(ℂ)`, and
the change of coordinates from `a` to `a'` is multiplication by the value at `x` of the
transition function `g`, `a = g • a'`. -/
def lineBundleCore : VectorBundleCore ℂ (ComplexPoints (X ↘ Spec (.of ℂ))) ℂ (Generator L) where
  baseSet s := chart s.W
  isOpen_baseSet s := isOpen_chart s.W
  indexAt x := (exists_generator x.toScheme).choose
  mem_baseSet_at x := mem_chart_iff.2 (exists_generator x.toScheme).choose_spec
  coordChange s s' x := evalExt _ (transitionSection s s') x • ContinuousLinearMap.id ℂ ℂ
  coordChange_self s x hx v := by
    have hx' : x ∈ chart (s.W ⊓ s.W) := by rw [chart_inf]; exact ⟨hx, hx⟩
    simp [transitionSection_self, evalExt_one hx']
  continuousOn_coordChange s s' := by
    rw [← chart_inf]
    exact (continuousOn_evalExt _ _).smul continuousOn_const
  coordChange_comp s₁ s₂ s₃ x hx v := by
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hx
    have hT : x ∈ chart (s₁.W ⊓ s₂.W ⊓ s₃.W) := by
      rw [chart_inf, chart_inf]; exact ⟨⟨h₁, h₂⟩, h₃⟩
    have e := congrArg (fun g ↦ evalExt _ g x) (transitionSection_trans s₁ s₂ s₃
      (T := s₁.W ⊓ s₂.W ⊓ s₃.W) inf_le_left (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
    simp only [evalExt_mul _ _ hT, evalExt_res _ _ hT] at e
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, e]
    ring

/-- The complex topological line bundle `L^top` on `X^an` underlying an invertible
`𝒪_X`-module `L`. -/
abbrev topologicalLineBundle : ComplexPoints (X ↘ Spec (.of ℂ)) → Type := (lineBundleCore L).Fiber

end InvertibleModule

open InvertibleModule in
/-- The first Chern class `c₁(L) ∈ H²(X; ℤ) = H²(X^an; ℤ)` of an invertible `𝒪_X`-module `L` on
a scheme `X` over `ℂ`: the first Chern class of the underlying complex topological line bundle
on `X^an`. -/
@[mmp "def_pab_topological_chern_class"]
def algebraicFirstChernClass {X : AlgebraicGeometry.Scheme.{0}}
    [X.Over (AlgebraicGeometry.Spec (.of ℂ))] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    analyticSingularCohomology ℤ (X ↘ AlgebraicGeometry.Spec (.of ℂ)) 2 :=
  analyticFirstChernClass (topologicalLineBundle L)

/-! ### Comparison of first Chern classes, and invariance under isomorphism -/

section Comparison

open Bundle FiberBundle Complex ComplexLineBundle

variable {B : Type} [TopologicalSpace B]

private theorem mem_vanishing_compl_univ {n : ℕ} (φ : Simplex B n → ℤ) :
    φ ∈ vanishing ℤ n (Set.univᶜ : Set (TopCat.of B)) :=
  fun σ hσ => absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp)

/-- Cocycles differing by a coboundary have the same class. -/
private theorem ofCocycle_eq_of_sub_eq_coboundary {φ φ' : Simplex B 2 → ℤ}
    (hφ : φ ∈ relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2)
    (hφ' : φ' ∈ relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2) (m : Simplex B 1 → ℤ)
    (h : φ - φ' = coboundary ℤ 1 m) :
    cohomologyWithSupports.ofCocycle ℤ (TopCat.of B) 2 φ hφ =
      cohomologyWithSupports.ofCocycle ℤ (TopCat.of B) 2 φ' hφ' := by
  unfold cohomologyWithSupports.ofCocycle
  congr 1
  refine (Submodule.Quotient.eq _).2 ?_
  change φ - φ' ∈ relCoboundaries ℤ (Set.univᶜ : Set (TopCat.of B)) (1 + 1)
  rw [h]
  exact ⟨m, mem_vanishing_compl_univ m, rfl⟩

private theorem ofCocycle_add {φ φ' : Simplex B 2 → ℤ}
    (hφ : φ ∈ relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2)
    (hφ' : φ' ∈ relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2)
    (hφφ' : φ + φ' ∈ relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2) :
    cohomologyWithSupports.ofCocycle ℤ (TopCat.of B) 2 (φ + φ') hφφ' =
      cohomologyWithSupports.ofCocycle ℤ (TopCat.of B) 2 φ hφ +
        cohomologyWithSupports.ofCocycle ℤ (TopCat.of B) 2 φ' hφ' := by
  unfold cohomologyWithSupports.ofCocycle
  rw [← LinearEquiv.map_add, ← Submodule.Quotient.mk_add]
  rfl

/-- Evaluation of a cochain on the image of a chain under a linear map. -/
private theorem eval_linearMap {n k : ℕ} (T : Chain ℤ B n →ₗ[ℤ] Chain ℤ B k) (ψ : Simplex B k → ℤ)
    (c : Chain ℤ B n) : eval ψ (T c) = eval (fun τ => eval ψ (T (Finsupp.single τ 1))) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, map_smul, map_smul]
    simp

/-- Evaluation only sees the simplices of the support. -/
private theorem eval_eq_of_eqOn_small {n : ℕ} {𝒰 : Set (Set B)} {φ φ' : Simplex B n → ℤ}
    (h : ∀ σ : Simplex B n, (∃ U ∈ 𝒰, Set.range σ ⊆ U) → φ σ = φ' σ) {c : Chain ℤ B n}
    (hc : c ∈ small ℤ n 𝒰) : eval φ c = eval φ' c := by
  have e : ∀ c : Chain ℤ B n, eval (φ - φ') c = eval φ c - eval φ' c := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]; ring
    | single σ a => simp [mul_sub]
  rw [← sub_eq_zero, ← e c]
  refine ComplexLineBundle.eval_eq_zero_of_mem_small (fun σ hσ => ?_) hc
  simp [h σ hσ]

/-- Pulling a cocycle back along the small-chains map changes it by a coboundary. -/
private theorem pullback_smallChainMap_sub (𝒰 : Set (Set B)) {ψ : Simplex B 2 → ℤ}
    (hδ : coboundary ℤ 2 ψ = 0) :
    pullback (smallChainMap ℤ 𝒰 2) ψ - ψ =
      coboundary ℤ 1 (fun τ => -eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))) := by
  funext σ
  have e1 : eval ψ (bd ℤ 2 (smallHomotopy ℤ 𝒰 2 (Finsupp.single σ 1))) = 0 := by
    rw [← eval_coboundary, hδ]
    simp
  have e2 : eval ψ (smallHomotopy ℤ 𝒰 1 (bd ℤ 1 (Finsupp.single σ 1))) =
      coboundary ℤ 1 (fun τ => eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))) σ := by
    rw [eval_linearMap, ← eval_coboundary]
    simp
  change eval ψ (smallChainMap ℤ 𝒰 (1 + 1) (Finsupp.single σ 1)) - ψ σ = _
  have hneg : (fun τ => -eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))) =
      -(fun τ => eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))) := rfl
  rw [smallChainMap_succ, map_sub, map_sub, e1, e2, hneg, map_neg]
  simp

/-- A cocycle which is a coboundary on the small simplices of an open cover is a coboundary. -/
private theorem exists_coboundary_of_small {𝒰 : Set (Set B)} (h𝒰 : ∀ U ∈ 𝒰, IsOpen U)
    (hcov : ∀ y : B, ∃ U ∈ 𝒰, y ∈ U) {ψ : Simplex B 2 → ℤ} (hδ : coboundary ℤ 2 ψ = 0)
    (m : Simplex B 1 → ℤ)
    (hm : ∀ σ : Simplex B 2, (∃ U ∈ 𝒰, Set.range σ ⊆ U) → ψ σ = coboundary ℤ 1 m σ) :
    ∃ m' : Simplex B 1 → ℤ, ψ = coboundary ℤ 1 m' := by
  have hρ : pullback (smallChainMap ℤ 𝒰 2) ψ =
      coboundary ℤ 1 (pullback (smallChainMap ℤ 𝒰 1) m) := by
    funext σ
    have hsmall := smallChainMap_single_mem_small (R := ℤ) h𝒰 2 (σ := σ)
      (fun y _ => Set.mem_sUnion.2 (hcov y))
    change eval ψ (smallChainMap ℤ 𝒰 (1 + 1) (Finsupp.single σ 1)) = _
    rw [eval_eq_of_eqOn_small hm hsmall, eval_coboundary, bd_smallChainMap, ← eval_pullback,
      ← eval_coboundary]
    simp
  refine ⟨pullback (smallChainMap ℤ 𝒰 1) m -
    (fun τ => -eval ψ (smallHomotopy ℤ 𝒰 1 (Finsupp.single τ 1))), ?_⟩
  rw [map_sub, ← hρ, ← pullback_smallChainMap_sub 𝒰 hδ, sub_sub_cancel]

/-- Local phase data over an open cover `𝒱`: edge phases `Φ V`, reference coordinates `v V` and
transition functions `g V W`, related as the edge phases, reference coordinates and transition
functions of a line bundle in a system of local frames. -/
private structure PhaseSystem (𝒱 : Set (Set B)) where
  /-- The edge phases in the frame over `V`. -/
  Φ : Set B → Simplex B 1 → ℂ
  /-- The reference coordinates in the frame over `V`. -/
  v : Set B → B → ℂ
  /-- The transition functions. -/
  g : Set B → Set B → B → ℂ
  v_ne : ∀ V ∈ 𝒱, ∀ y ∈ V, v V y ≠ 0
  g_cont : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ContinuousOn (g V W) (V ∩ W)
  g_ne : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ y ∈ V ∩ W, g V W y ≠ 0
  exp_Φ : ∀ V ∈ 𝒱, ∀ τ : Simplex B 1, Set.range τ ⊆ V →
    exp (Φ V τ) = v V (τ (stdSimplex.vertex 1)) / v V (τ (stdSimplex.vertex 0))
  Φ_change : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ τ : Simplex B 1, Set.range τ ⊆ V ∩ W →
    Φ W τ = Φ V τ + logIncrement (g V W) τ
  v_change : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ y ∈ V ∩ W, v W y = g V W y * v V y

/-- The coboundary of a `0`-cochain read off at the initial vertex is the difference of its
values at the two endpoints of a `1`-simplex. -/
theorem coboundary_zero_apply_vertex (f : B → ℂ) (τ : Simplex B 1) :
    coboundary ℂ 0 (fun p : Simplex B 0 => f (p (stdSimplex.vertex 0))) τ =
      f (τ (stdSimplex.vertex 1)) - f (τ (stdSimplex.vertex 0)) := by
  rw [coboundary_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, neg_one_mul,
    ContinuousMap.comp_apply]
  have e0 : face 0 0 (stdSimplex.vertex 0) = stdSimplex.vertex 1 := by
    simp [face, stdSimplex.map_vertex]
  have e1 : face 0 1 (stdSimplex.vertex 0) = stdSimplex.vertex 0 := by
    simp [face, stdSimplex.map_vertex]
  rw [e0, e1]
  ring

/-- If on each face of a `2`-simplex `σ` a `1`-cochain `Φ` is `m · z` plus a coboundary, then
its coboundary at `σ` is `(δm)(σ) · z`. -/
theorem coboundary_one_eq_of_faces {Φ : Simplex B 1 → ℂ} {m : Simplex B 1 → ℤ}
    {c : Simplex B 0 → ℂ} {z : ℂ} (σ : Simplex B 2)
    (e : ∀ i : Fin 3, Φ (σ.comp (face 1 i)) =
      (m (σ.comp (face 1 i)) : ℂ) * z + coboundary ℂ 0 c (σ.comp (face 1 i))) :
    coboundary ℂ 1 Φ σ = ((coboundary ℤ 1 m σ : ℤ) : ℂ) * z := by
  rw [coboundary_apply, coboundary_apply]
  simp only [e, mul_add, Finset.sum_add_distrib]
  have hδδ := congr_fun (coboundary_coboundary 0 c) σ
  rw [coboundary_apply] at hδδ
  rw [hδδ]
  push_cast
  rw [Finset.sum_mul]
  simp only [add_zero, Pi.zero_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

namespace PhaseSystem

variable {𝒱 : Set (Set B)}

/-- `n` is the obstruction cochain of the phase system on `𝒱`-small simplices. -/
private def IsPhase (S : PhaseSystem 𝒱) (n : Simplex B 2 → ℤ) : Prop :=
  ∀ V ∈ 𝒱, ∀ σ : Simplex B 2, Set.range σ ⊆ V →
    (n σ : ℂ) * (2 * Real.pi * I) = coboundary ℂ 1 (S.Φ V) σ

/-- The quotient of two phase systems. -/
private def sub (S₁ S₂ : PhaseSystem 𝒱) : PhaseSystem 𝒱 where
  Φ V := S₁.Φ V - S₂.Φ V
  v V y := S₁.v V y / S₂.v V y
  g V W y := S₁.g V W y / S₂.g V W y
  v_ne V hV y hy := div_ne_zero (S₁.v_ne V hV y hy) (S₂.v_ne V hV y hy)
  g_cont V hV W hW := (S₁.g_cont V hV W hW).div (S₂.g_cont V hV W hW)
    (fun y hy => S₂.g_ne V hV W hW y hy)
  g_ne V hV W hW y hy := div_ne_zero (S₁.g_ne V hV W hW y hy) (S₂.g_ne V hV W hW y hy)
  exp_Φ V hV τ hτ := by
    have h1 := S₂.v_ne V hV _ (hτ ⟨stdSimplex.vertex 1, rfl⟩)
    have h0 := S₂.v_ne V hV _ (hτ ⟨stdSimplex.vertex 0, rfl⟩)
    have h0' := S₁.v_ne V hV _ (hτ ⟨stdSimplex.vertex 0, rfl⟩)
    simp only [Pi.sub_apply, exp_sub, S₁.exp_Φ V hV τ hτ, S₂.exp_Φ V hV τ hτ]
    field_simp
  Φ_change V hV W hW τ hτ := by
    have hlog : logIncrement (S₁.g V W) τ =
        logIncrement (fun y => S₁.g V W y / S₂.g V W y) τ + logIncrement (S₂.g V W) τ := by
      refine logIncrement_mul (fun x => ?_) ?_ ?_
      · rw [div_mul_cancel₀ _ (S₂.g_ne V hV W hW _ (hτ ⟨x, rfl⟩))]
      · exact exists_continuous_log_comp τ ((S₁.g_cont V hV W hW).div (S₂.g_cont V hV W hW)
          (fun y hy => S₂.g_ne V hV W hW y hy))
          (fun y hy => div_ne_zero (S₁.g_ne V hV W hW y hy) (S₂.g_ne V hV W hW y hy)) hτ
      · exact exists_continuous_log_comp τ (S₂.g_cont V hV W hW)
          (fun y hy => S₂.g_ne V hV W hW y hy) hτ
    simp only [Pi.sub_apply, S₁.Φ_change V hV W hW τ hτ, S₂.Φ_change V hV W hW τ hτ, hlog]
    ring
  v_change V hV W hW y hy := by
    have := S₂.v_ne V hV y hy.1
    have := S₂.g_ne V hV W hW y hy
    simp only [S₁.v_change V hV W hW y hy, S₂.v_change V hV W hW y hy]
    field_simp

private theorem IsPhase.sub {S₁ S₂ : PhaseSystem 𝒱} {n₁ n₂ : Simplex B 2 → ℤ} (h₁ : S₁.IsPhase n₁)
    (h₂ : S₂.IsPhase n₂) : (S₁.sub S₂).IsPhase (n₁ - n₂) := by
  intro V hV σ hσ
  change ((n₁ σ - n₂ σ : ℤ) : ℂ) * _ = coboundary ℂ 1 (S₁.Φ V - S₂.Φ V) σ
  rw [map_sub, Pi.sub_apply, ← h₁ V hV σ hσ, ← h₂ V hV σ hσ]
  push_cast
  ring

private theorem logIncrement_eq_zero_of_eqOn {f : B → ℂ} {τ : Simplex B 1}
    (h : ∀ x, f (τ x) = 1) : logIncrement f τ = 0 := by
  rw [logIncrement_eq (0 : C(stdSimplex ℝ (Fin 2), ℂ)) fun x => by simp [h x]]
  simp

/-- **A trivial phase system has a coboundary as obstruction.** -/
private theorem exists_coboundary_of_trivial (S : PhaseSystem 𝒱) (hcov : ∀ y : B, ∃ V ∈ 𝒱, y ∈ V)
    (hg : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ y ∈ V ∩ W, S.g V W y = 1) {n : Simplex B 2 → ℤ}
    (hn : S.IsPhase n) :
    ∃ m : Simplex B 1 → ℤ, ∀ σ : Simplex B 2, (∃ V ∈ 𝒱, Set.range σ ⊆ V) →
      n σ = coboundary ℤ 1 m σ := by
  classical
  choose Vp hVp hpV using hcov
  let c : Simplex B 0 → ℂ := fun p => log (S.v (Vp (p (stdSimplex.vertex 0)))
    (p (stdSimplex.vertex 0)))
  let Φs : Simplex B 1 → ℂ := fun τ =>
    if h : ∃ V ∈ 𝒱, Set.range τ ⊆ V then S.Φ h.choose τ else 0
  have hΦs : ∀ V ∈ 𝒱, ∀ τ : Simplex B 1, Set.range τ ⊆ V → Φs τ = S.Φ V τ := by
    intro V hV τ hτ
    have h : ∃ V ∈ 𝒱, Set.range τ ⊆ V := ⟨V, hV, hτ⟩
    simp only [Φs, dite_eq_left h]
    rw [S.Φ_change _ h.choose_spec.1 V hV τ (Set.subset_inter h.choose_spec.2 hτ),
      logIncrement_eq_zero_of_eqOn (fun x => hg _ h.choose_spec.1 V hV _
        ⟨h.choose_spec.2 ⟨x, rfl⟩, hτ ⟨x, rfl⟩⟩), add_zero]
  have hv : ∀ V ∈ 𝒱, ∀ y ∈ V, S.v V y = S.v (Vp y) y := by
    intro V hV y hy
    rw [S.v_change (Vp y) (hVp y) V hV y ⟨hpV y, hy⟩, hg _ (hVp y) V hV y ⟨hpV y, hy⟩, one_mul]
  have hint : ∀ τ : Simplex B 1, ∃ k : ℤ, (∃ V ∈ 𝒱, Set.range τ ⊆ V) →
      Φs τ - coboundary ℂ 0 c τ = k * (2 * Real.pi * I) := by
    intro τ
    by_cases h : ∃ V ∈ 𝒱, Set.range τ ⊆ V
    · obtain ⟨V, hV, hτ⟩ := h
      have hτ1 := hτ ⟨stdSimplex.vertex 1, rfl⟩
      have hτ0 := hτ ⟨stdSimplex.vertex 0, rfl⟩
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 (show exp (Φs τ - coboundary ℂ 0 c τ) = 1 by
        rw [coboundary_zero_apply_vertex (fun y => log (S.v (Vp y) y)) τ, hΦs V hV τ hτ, exp_sub,
          exp_sub, S.exp_Φ V hV τ hτ,
          exp_log (S.v_ne _ (hVp _) _ (hpV _)), exp_log (S.v_ne _ (hVp _) _ (hpV _)),
          ← hv V hV _ hτ1, ← hv V hV _ hτ0]
        have := S.v_ne V hV _ hτ1
        have := S.v_ne V hV _ hτ0
        field_simp)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose m hm using hint
  refine ⟨m, fun σ ⟨V, hV, hσ⟩ => ?_⟩
  have hfaces : ∀ i : Fin 3, Set.range (σ.comp (face 1 i)) ⊆ V :=
    fun i _ ⟨x, hx⟩ => hσ ⟨_, hx⟩
  have key : (n σ : ℂ) * (2 * Real.pi * I) =
      ((coboundary ℤ 1 m σ : ℤ) : ℂ) * (2 * Real.pi * I) := by
    rw [hn V hV σ hσ]
    refine coboundary_one_eq_of_faces (c := c) σ fun i => ?_
    rw [← hΦs V hV _ (hfaces i), ← hm _ ⟨V, hV, hfaces i⟩]
    ring
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero key

end PhaseSystem

section Bundle

variable {B' : Type} [TopologicalSpace B'] {E : B → Type*} [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℂ (E b)] [TopologicalSpace (TotalSpace ℂ E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]

/-- A system of frames of `E` along `f` over the members of `𝒱`. -/
private def IsFrameSystem (𝒱 : Set (Set B')) (f : C(B', B))
    (e : Set B' → Trivialization ℂ (π ℂ E)) : Prop :=
  ∀ V ∈ 𝒱, e V ∈ trivializationAtlas ℂ E ∧ ∀ y ∈ V, f y ∈ (e V).baseSet

/-- The phase system of a line bundle pulled back along `f`, in a system of frames. -/
private def bundleSystem {𝒱 : Set (Set B')} {f : C(B', B)} {e : Set B' → Trivialization ℂ (π ℂ E)}
    (he : IsFrameSystem 𝒱 f e) : PhaseSystem (B := B') 𝒱 where
  Φ V τ := edgePhase (E := E) (e V) (f.comp τ)
  v V y := vertexCoord (E := E) (e V) (f y)
  g V W y := transition (e V) (e W) (f y)
  v_ne V hV y hy := by
    have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
    exact vertexCoord_ne_zero ((he V hV).2 y hy)
  g_cont V hV W hW := by
    have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
    have : MemTrivializationAtlas (e W) := ⟨(he W hW).1⟩
    exact (continuousOn_transition (e := e V) (e' := e W)).comp f.continuous.continuousOn
      (fun y hy => ⟨(he V hV).2 y hy.1, (he W hW).2 y hy.2⟩)
  g_ne V hV W hW y hy := by
    have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
    have : MemTrivializationAtlas (e W) := ⟨(he W hW).1⟩
    exact transition_ne_zero ⟨(he V hV).2 y hy.1, (he W hW).2 y hy.2⟩
  exp_Φ V hV τ hτ := by
    have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
    exact exp_edgePhase fun _ ⟨x, hx⟩ => hx ▸ (he V hV).2 _ (hτ ⟨x, rfl⟩)
  Φ_change V hV W hW τ hτ := by
    have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
    have : MemTrivializationAtlas (e W) := ⟨(he W hW).1⟩
    have hV' : Set.range (f.comp τ) ⊆ (e V).baseSet :=
      fun _ ⟨x, hx⟩ => hx ▸ (he V hV).2 _ (hτ ⟨x, rfl⟩).1
    have hW' : Set.range (f.comp τ) ⊆ (e W).baseSet :=
      fun _ ⟨x, hx⟩ => hx ▸ (he W hW).2 _ (hτ ⟨x, rfl⟩).2
    have hs := range_subset_simplexTriv (E := E) (he V hV).1 hV'
    simp only [edgePhase]
    rw [add_assoc, logIncrement_mul (g := transition (simplexTriv (E := E) (f.comp τ)) (e V))
      (h := transition (e V) (e W))]
    · rfl
    · intro x
      rw [transition_trans (hs ⟨x, rfl⟩) (hV' ⟨x, rfl⟩) (hW' ⟨x, rfl⟩), mul_comm]
    · exact exists_continuous_log_comp (f.comp τ) continuousOn_transition
        (fun y hy => transition_ne_zero hy) (Set.subset_inter hs hV')
    · exact exists_continuous_log_comp (f.comp τ) continuousOn_transition
        (fun y hy => transition_ne_zero hy) (Set.subset_inter hV' hW')
  v_change V hV W hW y hy := by
    have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
    have : MemTrivializationAtlas (e W) := ⟨(he W hW).1⟩
    exact vertexCoord_eq ((he V hV).2 y hy.1) ((he W hW).2 y hy.2)

private theorem isPhase_bundleSystem {𝒱 : Set (Set B')} {f : C(B', B)}
    {e : Set B' → Trivialization ℂ (π ℂ E)} (he : IsFrameSystem 𝒱 f e) :
    (bundleSystem he).IsPhase (fun σ => obstructionCocycle E (f.comp σ)) := by
  intro V hV σ hσ
  have : MemTrivializationAtlas (e V) := ⟨(he V hV).1⟩
  have hfσ : Set.range (f.comp σ) ⊆ (e V).baseSet :=
    fun _ ⟨x, hx⟩ => hx ▸ (he V hV).2 _ (hσ ⟨x, rfl⟩)
  rw [obstructionCocycle_mul hfσ, obstructionPhase_eq_coboundary hfσ]
  rfl

omit [∀ b, Module ℂ (E b)] [VectorBundle ℂ ℂ E] in
private theorem coboundary_obstructionCocycle_comp [∀ b, Module ℂ (E b)] [VectorBundle ℂ ℂ E]
    (f : C(B', B)) :
    coboundary ℤ 2 (fun σ : Simplex B' 2 => obstructionCocycle E (f.comp σ)) = 0 := by
  funext σ
  exact congr_fun (coboundary_obstructionCocycle (E := E)) (f.comp σ)

variable {E' : B' → Type*} [∀ b, AddCommGroup (E' b)]
  [∀ b, Module ℂ (E' b)] [TopologicalSpace (TotalSpace ℂ E')] [∀ b, TopologicalSpace (E' b)]
  [FiberBundle ℂ E'] [VectorBundle ℂ ℂ E']

/-- **Comparison of first Chern classes.** If, over an open cover of `B'`, the line bundle `E'`
and the pullback of `E` along `f` have frames with the same transition functions, then
`c₁(E')` is the class of the pullback along `f` of the obstruction cocycle of `E`. -/
private theorem firstChernClass_eq_ofCocycle_comp {𝒱 : Set (Set B')} (h𝒱 : ∀ V ∈ 𝒱, IsOpen V)
    (hcov : ∀ y : B', ∃ V ∈ 𝒱, y ∈ V) (f : C(B', B))
    {e : Set B' → Trivialization ℂ (π ℂ E)} {e' : Set B' → Trivialization ℂ (π ℂ E')}
    (he : IsFrameSystem 𝒱 f e) (he' : IsFrameSystem 𝒱 (ContinuousMap.id B') e')
    (htr : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ y ∈ V ∩ W,
      transition (e' V) (e' W) y = transition (e V) (e W) (f y)) :
    firstChernClass E' = cohomologyWithSupports.ofCocycle ℤ (TopCat.of B') 2
      (fun σ => obstructionCocycle E (f.comp σ))
      ⟨mem_vanishing_compl_univ _, coboundary_obstructionCocycle_comp f⟩ := by
  let T := (bundleSystem he').sub (bundleSystem he)
  have hT := (isPhase_bundleSystem he').sub (isPhase_bundleSystem he)
  have hg : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ y ∈ V ∩ W, T.g V W y = 1 := by
    intro V hV W hW y hy
    change transition (e' V) (e' W) y / transition (e V) (e W) (f y) = 1
    rw [htr V hV W hW y hy]
    exact div_self ((bundleSystem he).g_ne V hV W hW y hy)
  obtain ⟨m, hm⟩ := T.exists_coboundary_of_trivial hcov hg hT
  obtain ⟨m', hm'⟩ := exists_coboundary_of_small h𝒱 hcov (by
    rw [map_sub, coboundary_obstructionCocycle_comp, coboundary_obstructionCocycle_comp,
      sub_zero]) m hm
  exact ofCocycle_eq_of_sub_eq_coboundary _ _ m' hm'

/-- **Additivity of first Chern classes.** If, over an open cover of `B`, the line bundles `E`,
`E₁`, `E₂` have frames whose transition functions satisfy `g = g₁ g₂`, then
`c₁(E) = c₁(E₁) + c₁(E₂)`. -/
private theorem firstChernClass_eq_add {E₁ E₂ : B → Type*} [∀ b, AddCommGroup (E₁ b)]
    [∀ b, Module ℂ (E₁ b)] [TopologicalSpace (TotalSpace ℂ E₁)] [∀ b, TopologicalSpace (E₁ b)]
    [FiberBundle ℂ E₁] [VectorBundle ℂ ℂ E₁] [∀ b, AddCommGroup (E₂ b)]
    [∀ b, Module ℂ (E₂ b)] [TopologicalSpace (TotalSpace ℂ E₂)] [∀ b, TopologicalSpace (E₂ b)]
    [FiberBundle ℂ E₂] [VectorBundle ℂ ℂ E₂] {𝒱 : Set (Set B)} (h𝒱 : ∀ V ∈ 𝒱, IsOpen V)
    (hcov : ∀ y : B, ∃ V ∈ 𝒱, y ∈ V)
    {e : Set B → Trivialization ℂ (π ℂ E)} {e₁ : Set B → Trivialization ℂ (π ℂ E₁)}
    {e₂ : Set B → Trivialization ℂ (π ℂ E₂)}
    (he : IsFrameSystem 𝒱 (ContinuousMap.id B) e) (he₁ : IsFrameSystem 𝒱 (ContinuousMap.id B) e₁)
    (he₂ : IsFrameSystem 𝒱 (ContinuousMap.id B) e₂)
    (htr : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ y ∈ V ∩ W,
      transition (e V) (e W) y = transition (e₁ V) (e₁ W) y * transition (e₂ V) (e₂ W) y) :
    firstChernClass E = firstChernClass E₁ + firstChernClass E₂ := by
  let T := ((bundleSystem he).sub (bundleSystem he₁)).sub (bundleSystem he₂)
  have hT := ((isPhase_bundleSystem he).sub (isPhase_bundleSystem he₁)).sub
    (isPhase_bundleSystem he₂)
  have hg : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ y ∈ V ∩ W, T.g V W y = 1 := by
    intro V hV W hW y hy
    change transition (e V) (e W) y / transition (e₁ V) (e₁ W) y /
      transition (e₂ V) (e₂ W) y = 1
    have h₁ : transition (e₁ V) (e₁ W) y ≠ 0 := (bundleSystem he₁).g_ne V hV W hW y hy
    have h₂ : transition (e₂ V) (e₂ W) y ≠ 0 := (bundleSystem he₂).g_ne V hV W hW y hy
    rw [htr V hV W hW y hy]
    field_simp
  obtain ⟨m, hm⟩ := T.exists_coboundary_of_trivial hcov hg hT
  obtain ⟨m', hm'⟩ := exists_coboundary_of_small h𝒱 hcov (by
    rw [map_sub, map_sub, coboundary_obstructionCocycle_comp,
      coboundary_obstructionCocycle_comp, coboundary_obstructionCocycle_comp, sub_zero,
      sub_zero]) m hm
  have hmem : obstructionCocycle E₁ + obstructionCocycle E₂ ∈
      relCocycles ℤ (Set.univᶜ : Set (TopCat.of B)) 2 :=
    Submodule.add_mem _ (obstructionCocycle_mem_relCocycles E₁)
      (obstructionCocycle_mem_relCocycles E₂)
  unfold firstChernClass
  rw [← ofCocycle_add _ _ hmem]
  refine ofCocycle_eq_of_sub_eq_coboundary _ _ m' ?_
  rwa [← sub_sub]

end Bundle

end Comparison

namespace InvertibleModule

open AlgebraicGeometry Opposite

variable {X : Scheme.{0}} {L M : X.Modules}

private theorem sectionRes_app (φ : L ⟶ M) {V W : X.Opens} (h : V ≤ W) (a : Γ(L, W)) :
    sectionRes M h (φ.app W a) = φ.app V (sectionRes L h a) :=
  (PresheafOfModules.naturality_apply φ.val (homOfLE h).op a).symm

/-- The image of a local generator under an isomorphism. -/
private def Generator.map (e : L ≅ M) (s : Generator L) : Generator M where
  W := s.W
  a := e.hom.app s.W s.a
  bijective V h := by
    have hb : Function.Bijective (e.hom.app V) := by
      refine ⟨fun x y hxy => ?_, fun y => ⟨e.inv.app V y, ?_⟩⟩
      · have := congrArg (e.inv.app V) hxy
        rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          ← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app] at this
      · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id,
          Scheme.Modules.Hom.id_app]
        rfl
    have : (fun c : Γ(X, V) => c • sectionRes M h (e.hom.app s.W s.a)) =
        e.hom.app V ∘ fun c : Γ(X, V) => c • sectionRes L h s.a := by
      funext c
      simp only [Function.comp_apply, Scheme.Modules.Hom.app_smul, sectionRes_app]
    rw [this]
    exact hb.comp (s.bijective V h)

private theorem transitionSection_map (e : L ≅ M) (s s' : Generator L) :
    transitionSection (s.map e) (s'.map e) = transitionSection s s' := by
  refine (s'.map e).coeff_eq inf_le_right ?_
  have h1 := sectionRes_app e.hom (inf_le_right : s.W ⊓ s'.W ≤ s'.W) s'.a
  have h2 := sectionRes_app e.hom (inf_le_left : s.W ⊓ s'.W ≤ s.W) s.a
  have h3 := Scheme.Modules.Hom.app_smul e.hom (transitionSection s s')
    (sectionRes L (inf_le_right : s.W ⊓ s'.W ≤ s'.W) s'.a)
  rw [transitionSection_smul] at h3
  exact (congrArg (transitionSection s s' • ·) h1).trans (h3.symm.trans h2.symm)

variable [X.Over (Spec (.of ℂ))]

open ComplexPoints ComplexLineBundle in
private theorem transition_localTriv (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (s s' : Generator L)
    {y : ComplexPoints (X ↘ Spec (.of ℂ))} (hy : y ∈ chart s.W ∩ chart s'.W) :
    transition ((lineBundleCore L).localTriv s) ((lineBundleCore L).localTriv s') y =
      evalExt _ (transitionSection s s') y := by
  have : MemTrivializationAtlas ((lineBundleCore L).localTriv s) := ⟨⟨s, rfl⟩⟩
  have : MemTrivializationAtlas ((lineBundleCore L).localTriv s') := ⟨⟨s', rfl⟩⟩
  rw [transition_eq_coordChangeL hy,
    VectorBundleCore.localTriv_coordChange_eq (R := ℂ) _ _ _ ⟨hy.1, hy.2⟩]
  change evalExt _ (transitionSection s s') y • (1 : ℂ) = _
  rw [smul_eq_mul, mul_one]

end InvertibleModule

open InvertibleModule ComplexPoints ComplexLineBundle AlgebraicGeometry in
/-- **Invariance of `c₁` under isomorphism.** Isomorphic invertible modules have the same first
Chern class. -/
theorem algebraicFirstChernClass_eq_of_iso {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    {L M : X.Modules} [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (e : L ≅ M) :
    algebraicFirstChernClass L = algebraicFirstChernClass M := by
  classical
  rcases isEmpty_or_nonempty (ComplexPoints (X ↘ Spec (.of ℂ))) with hB | ⟨⟨x₀⟩⟩
  · exact ofCocycle_eq_of_sub_eq_coboundary _ _ 0
      (funext fun σ => (hB.false (σ (stdSimplex.vertex 0))).elim)
  let s₀ : Generator L := (exists_generator x₀.toScheme).choose
  let 𝒱 : Set (Set (ComplexPoints (X ↘ Spec (.of ℂ)))) :=
    Set.range fun s : Generator L => chart s.W
  let gen : Set (ComplexPoints (X ↘ Spec (.of ℂ))) → Generator L :=
    fun V => if h : V ∈ 𝒱 then h.choose else s₀
  have hgen : ∀ V ∈ 𝒱, chart (gen V).W = V := fun V hV => by
    simp only [gen, dite_eq_left hV]
    exact hV.choose_spec
  have h𝒱 : ∀ V ∈ 𝒱, IsOpen V := by
    rintro _ ⟨s, rfl⟩
    exact isOpen_chart s.W
  have hcov : ∀ y : ComplexPoints (X ↘ Spec (.of ℂ)), ∃ V ∈ 𝒱, y ∈ V := fun y =>
    ⟨_, ⟨_, rfl⟩, mem_chart_iff.2 (exists_generator y.toScheme).choose_spec⟩
  have hfr : IsFrameSystem 𝒱 (ContinuousMap.id _)
      (fun V => (lineBundleCore L).localTriv (gen V)) := fun V hV =>
    ⟨⟨gen V, rfl⟩, fun y hy => by rwa [← hgen V hV] at hy⟩
  have hfr' : IsFrameSystem 𝒱 (ContinuousMap.id _)
      (fun V => (lineBundleCore M).localTriv ((gen V).map e)) := fun V hV =>
    ⟨⟨(gen V).map e, rfl⟩, fun y hy => by rwa [← hgen V hV] at hy⟩
  have htr : ∀ V ∈ 𝒱, ∀ W ∈ 𝒱, ∀ y ∈ V ∩ W,
      transition ((lineBundleCore M).localTriv ((gen V).map e))
          ((lineBundleCore M).localTriv ((gen W).map e)) y =
        transition ((lineBundleCore L).localTriv (gen V))
          ((lineBundleCore L).localTriv (gen W)) ((ContinuousMap.id _) y) := by
    intro V hV W hW y hy
    have hy' : y ∈ chart (gen V).W ∩ chart (gen W).W := by
      rwa [hgen V hV, hgen W hW]
    change _ = transition ((lineBundleCore L).localTriv (gen V))
      ((lineBundleCore L).localTriv (gen W)) y
    rw [transition_localTriv L _ _ hy', transition_localTriv M _ _ hy', transitionSection_map]
    rfl
  exact (firstChernClass_eq_ofCocycle_comp h𝒱 hcov (ContinuousMap.id _) hfr hfr' htr).symm

/-! ### Additivity and naturality of `c₁` -/

/-- On an empty space all degree-two classes agree. -/
private theorem singularCohomology_two_eq_of_isEmpty {B : Type} [TopologicalSpace B] [IsEmpty B]
    (c c' : singularCohomology ℤ (TopCat.of B) 2) : c = c' := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq 2 c
  obtain ⟨φ', hφ', rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq 2 c'
  exact ofCocycle_eq_of_sub_eq_coboundary hφ hφ' 0
    (funext fun σ => isEmptyElim (σ (stdSimplex.vertex 0)))

namespace InvertibleModule

open AlgebraicGeometry Opposite ComplexPoints

variable {X : Scheme.{0}} {L M : X.Modules}

/-- A local generator, as a generating section in the sense of `Stacks.SheafOfModules`. -/
private def Generator.toSections (s : Generator L) :
    Stacks.SheafOfModules.GeneratorSections X.toRingedSpace L s.W :=
  ⟨s.a, s.bijective⟩

/-- A generating section in the sense of `Stacks.SheafOfModules`, as a local generator. -/
private def Generator.ofSections {W : X.Opens}
    (s : Stacks.SheafOfModules.GeneratorSections X.toRingedSpace L W) : Generator L :=
  ⟨W, s.val, s.property⟩

/-- The tensor product of two `𝒪_X`-modules, as an `𝒪_X`-module. -/
private abbrev tens (L M : X.Modules) : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj L).obj M

/-- The elementary tensor `a ⊗ b` of two local generators, over the intersection of their opens. -/
private def tensorGen (s : Generator L) (t : Generator M) : Generator (tens L M) :=
  Generator.ofSections (Stacks.SheafOfModules.tmulGenerator
    (Stacks.SheafOfModules.generatorRestrict L inf_le_left s.toSections)
    (Stacks.SheafOfModules.generatorRestrict M inf_le_right t.toSections))

open Stacks.SheafOfModules in
private theorem sectionRes_tensorGen_a (s : Generator L) (t : Generator M) {V : X.Opens}
    (h : V ≤ s.W ⊓ t.W) :
    sectionRes (tens L M) h (tensorGen s t).a =
      (tmulGenerator (generatorRestrict L (h.trans inf_le_left) s.toSections)
        (generatorRestrict M (h.trans inf_le_right) t.toSections)).val := by
  have := congrArg Subtype.val (tmulGenerator_restrict
    (generatorRestrict L inf_le_left s.toSections)
    (generatorRestrict M inf_le_right t.toSections) h)
  refine this.trans ?_
  congr 2 <;> exact generatorRestrict_trans _ _ _ _

open Stacks.SheafOfModules in
private theorem smul_sectionRes_tensorGen_a (s : Generator L) (t : Generator M) {V : X.Opens}
    (h : V ≤ s.W ⊓ t.W) (c : Γ(X, V)) :
    c • sectionRes (tens L M) h (tensorGen s t).a =
      c • (show Γ(tens L M, V) from (tmulGenerator (generatorRestrict L (h.trans inf_le_left)
        s.toSections) (generatorRestrict M (h.trans inf_le_right) t.toSections)).val) :=
  congrArg (c • ·) (sectionRes_tensorGen_a s t h)

open Stacks.SheafOfModules in
/-- The transition function of two elementary tensors of generators is the product of the
transition functions of the factors. -/
private theorem transitionSection_tensorGen (s s' : Generator L) (t t' : Generator M) :
    transitionSection (tensorGen s t) (tensorGen s' t') =
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
          (inf_le_right.trans inf_le_left))).op (transitionSection s s') *
        X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right)
          (inf_le_right.trans inf_le_right))).op (transitionSection t t') := by
  refine (tensorGen s' t').coeff_eq inf_le_right ?_
  refine Eq.trans ?_ (sectionRes_tensorGen_a s t _).symm
  refine Eq.trans (smul_sectionRes_tensorGen_a s' t' _ _) ?_
  refine (tmulGenerator_smul _ _ _ _ _ _ ?_ ?_).symm
  · have e := congrArg (sectionRes L (V := s.W ⊓ t.W ⊓ (s'.W ⊓ t'.W))
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)))
      (transitionSection_smul s s')
    rw [sectionRes_smul, sectionRes_sectionRes, sectionRes_sectionRes] at e
    exact e.symm
  · have e := congrArg (sectionRes M (V := s.W ⊓ t.W ⊓ (s'.W ⊓ t'.W))
      (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)))
      (transitionSection_smul t t')
    rw [sectionRes_smul, sectionRes_sectionRes, sectionRes_sectionRes] at e
    exact e.symm

private theorem transitionSection_eq_generatorRatio (s s' : Generator L) :
    transitionSection s s' = Stacks.SheafOfModules.generatorRatio L (s.W ⊓ s'.W)
      (Stacks.SheafOfModules.generatorRestrict L inf_le_right s'.toSections)
      (Stacks.SheafOfModules.generatorRestrict L inf_le_left s.toSections) :=
  s'.coeff_eq inf_le_right (Stacks.SheafOfModules.generatorRatio_spec L _ _ _).symm

section Pullback

variable {X' : Scheme.{0}} (f : X' ⟶ X)
  (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property L)

/-- The pullback `f^* a` of a local generator `a`, a local generator of `f^* L` over `f⁻¹(W)`. -/
private def pullbackGen (s : Generator L) : Generator ((Scheme.Modules.pullback f).obj L) :=
  Generator.ofSections (Stacks.SheafOfModules.pullbackGenerator f L hL s.W s.toSections)

open Stacks.SheafOfModules in
private theorem sectionRes_pullbackGen_a (s : Generator L) {V : X.Opens} (h : V ≤ s.W) :
    sectionRes ((Scheme.Modules.pullback f).obj L) (f.preimage_mono h) (pullbackGen f hL s).a =
      (pullbackGenerator f L hL V (generatorRestrict L h s.toSections)).val :=
  congrArg Subtype.val (pullbackGenerator_restrict f L hL h s.toSections)

open Stacks.SheafOfModules in
/-- The transition function of two pulled-back generators is the pullback of the transition
function. -/
private theorem transitionSection_pullbackGen (s s' : Generator L) :
    transitionSection (pullbackGen f hL s) (pullbackGen f hL s') =
      f.app (s.W ⊓ s'.W) (transitionSection s s') := by
  refine (pullbackGen f hL s').coeff_eq inf_le_right ?_
  have e1 := sectionRes_pullbackGen_a f hL s (inf_le_left : s.W ⊓ s'.W ≤ s.W)
  have e2 := sectionRes_pullbackGen_a f hL s' (inf_le_right : s.W ⊓ s'.W ≤ s'.W)
  have e3 := congrArg Units.val (generatorRatioUnit_pullbackGenerator f L hL (s.W ⊓ s'.W)
    (generatorRestrict L inf_le_right s'.toSections) (generatorRestrict L inf_le_left s.toSections))
  have e4 := generatorRatio_spec _ _ (pullbackGenerator f L hL (s.W ⊓ s'.W)
    (generatorRestrict L inf_le_right s'.toSections))
    (pullbackGenerator f L hL (s.W ⊓ s'.W) (generatorRestrict L inf_le_left s.toSections))
  have e3' : generatorRatio _ _ (pullbackGenerator f L hL (s.W ⊓ s'.W)
      (generatorRestrict L inf_le_right s'.toSections))
      (pullbackGenerator f L hL (s.W ⊓ s'.W) (generatorRestrict L inf_le_left s.toSections)) =
      f.app (s.W ⊓ s'.W) (transitionSection s s') := by
    rw [transitionSection_eq_generatorRatio]
    exact e3
  refine (e1.trans (e4.trans ?_)).symm
  erw [e3', e2]
  rfl

variable [X'.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))]
  {g : Analytification.space (X' ↘ Spec (.of ℂ)) ⟶ Analytification.space (X ↘ Spec (.of ℂ))}

omit hL in
private theorem mem_chart_of_hom_eq (hg : ∀ x, (g x).hom = x.hom ≫ f) {U : X.Opens}
    {y : ComplexPoints (X' ↘ Spec (.of ℂ))} (hy : y ∈ chart (f ⁻¹ᵁ U)) : g y ∈ chart U := by
  change (g y).hom ⁻¹ᵁ U = ⊤
  rw [hg y]
  exact hy

omit hL in
private theorem appLE_eq_of_eq {A B : Scheme.{0}} {a b : A ⟶ B} (h : a = b) (U : B.Opens)
    (V : A.Opens) (e : V ≤ a ⁻¹ᵁ U) : a.appLE U V e = b.appLE U V (h ▸ e) := by
  subst h
  rfl

omit hL in
/-- The value of a pulled-back function at a `ℂ`-point is the value at its image. -/
private theorem evalExt_app (hg : ∀ x, (g x).hom = x.hom ≫ f) (U : X.Opens) (a : Γ(X, U))
    {y : ComplexPoints (X' ↘ Spec (.of ℂ))} (hy : y ∈ chart (f ⁻¹ᵁ U)) :
    evalExt (f ⁻¹ᵁ U) (f.app U a) y = evalExt U a (g y) := by
  rw [evalExt_of_mem _ hy, evalExt_of_mem _ (mem_chart_of_hom_eq f hg hy)]
  simp only [ComplexPoints.eval]
  rw [appLE_eq_of_eq (hg y), Scheme.Hom.comp_appLE]
  rfl

open ComplexLineBundle in
/-- The transition function between the local trivializations of two pulled-back generators is
the pullback of the transition function of the generators. -/
private theorem transition_localTriv_pullbackGen
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj L)]
    (hg : ∀ x, (g x).hom = x.hom ≫ f) (s s' : Generator L)
    {y : ComplexPoints (X' ↘ Spec (.of ℂ))} (hy : y ∈ chart (f ⁻¹ᵁ s.W))
    (hy' : y ∈ chart (f ⁻¹ᵁ s'.W)) :
    transition ((lineBundleCore ((Scheme.Modules.pullback f).obj L)).localTriv
        (pullbackGen f hL s))
        ((lineBundleCore ((Scheme.Modules.pullback f).obj L)).localTriv (pullbackGen f hL s')) y =
      transition ((lineBundleCore L).localTriv s) ((lineBundleCore L).localTriv s') (g.hom y) := by
  have hT : y ∈ chart (f ⁻¹ᵁ (s.W ⊓ s'.W)) := by
    rw [Scheme.Hom.preimage_inf, chart_inf]
    exact ⟨hy, hy'⟩
  rw [transition_localTriv _ _ _ ⟨hy, hy'⟩,
    transition_localTriv _ _ _ ⟨mem_chart_of_hom_eq f hg hy, mem_chart_of_hom_eq f hg hy'⟩,
    transitionSection_pullbackGen]
  exact evalExt_app f hg _ _ hT

end Pullback

open ComplexLineBundle in
/-- The transition function between the local trivializations of two elementary tensors of
generators is the product of the transition functions of the factors. -/
private theorem transition_localTriv_tensorGen [X.Over (Spec (.of ℂ))]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (tens L M)]
    (s s' : Generator L) (t t' : Generator M) {y : ComplexPoints (X ↘ Spec (.of ℂ))}
    (hy : y ∈ chart s.W ∩ chart t.W) (hy' : y ∈ chart s'.W ∩ chart t'.W) :
    transition ((lineBundleCore (tens L M)).localTriv (tensorGen s t))
        ((lineBundleCore (tens L M)).localTriv (tensorGen s' t')) y =
      transition ((lineBundleCore L).localTriv s) ((lineBundleCore L).localTriv s') y *
        transition ((lineBundleCore M).localTriv t) ((lineBundleCore M).localTriv t') y := by
  have hT : y ∈ chart (s.W ⊓ t.W ⊓ (s'.W ⊓ t'.W)) := by
    rw [chart_inf, chart_inf, chart_inf]
    exact ⟨hy, hy'⟩
  have hT' : y ∈ chart (tensorGen s t).W ∩ chart (tensorGen s' t').W := by
    rwa [← chart_inf]
  rw [transition_localTriv _ _ _ hT', transition_localTriv _ _ _ ⟨hy.1, hy'.1⟩,
    transition_localTriv _ _ _ ⟨hy.2, hy'.2⟩, transitionSection_tensorGen]
  have e := evalExt_mul (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
    (inf_le_right.trans inf_le_left))).op (transitionSection s s'))
    (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right)
    (inf_le_right.trans inf_le_right))).op (transitionSection t t')) hT
  rwa [evalExt_res _ _ hT, evalExt_res _ _ hT] at e

end InvertibleModule

open InvertibleModule ComplexPoints ComplexLineBundle AlgebraicGeometry in
/-- **Additivity of `c₁`.** For invertible `𝒪_X`-modules `L` and `M` on a scheme `X` over `ℂ`,
`c₁(L ⊗ M) = c₁(L) + c₁(M)` in `H²(X^an; ℤ)`, the tensor product being the sheaf tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor`. -/
theorem algebraicFirstChernClass_sheafTensor {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    (L M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj L).obj M)] :
    algebraicFirstChernClass
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj L).obj M) =
      algebraicFirstChernClass L + algebraicFirstChernClass M := by
  classical
  rcases isEmpty_or_nonempty (ComplexPoints (X ↘ Spec (.of ℂ))) with hB | ⟨⟨x₀⟩⟩
  · exact singularCohomology_two_eq_of_isEmpty _ _
  let p₀ : Generator L × Generator M :=
    ((exists_generator x₀.toScheme).choose, (exists_generator x₀.toScheme).choose)
  let 𝒱 : Set (Set (ComplexPoints (X ↘ Spec (.of ℂ)))) :=
    Set.range fun p : Generator L × Generator M => chart (p.1.W ⊓ p.2.W)
  let gen : Set (ComplexPoints (X ↘ Spec (.of ℂ))) → Generator L × Generator M :=
    fun V => if h : V ∈ 𝒱 then h.choose else p₀
  have hgen : ∀ V ∈ 𝒱, chart ((gen V).1.W ⊓ (gen V).2.W) = V := fun V hV => by
    simp only [gen, dite_eq_left hV]
    exact hV.choose_spec
  have h𝒱 : ∀ V ∈ 𝒱, IsOpen V := by
    rintro _ ⟨p, rfl⟩
    exact isOpen_chart _
  have hcov : ∀ y : ComplexPoints (X ↘ Spec (.of ℂ)), ∃ V ∈ 𝒱, y ∈ V := fun y =>
    ⟨_, ⟨((exists_generator y.toScheme).choose, (exists_generator y.toScheme).choose), rfl⟩, by
      change y ∈ chart (_ ⊓ _)
      rw [chart_inf]
      exact ⟨mem_chart_iff.2 (exists_generator y.toScheme).choose_spec,
        mem_chart_iff.2 (exists_generator y.toScheme).choose_spec⟩⟩
  have hmem : ∀ V ∈ 𝒱, ∀ y ∈ V, y ∈ chart (gen V).1.W ∩ chart (gen V).2.W := by
    intro V hV y hy
    rwa [← hgen V hV, chart_inf] at hy
  have hfr : IsFrameSystem 𝒱 (ContinuousMap.id _)
      (fun V => (lineBundleCore (tens L M)).localTriv (tensorGen (gen V).1 (gen V).2)) :=
    fun V hV => ⟨⟨_, rfl⟩, fun y hy => by
      change y ∈ chart ((gen V).1.W ⊓ (gen V).2.W)
      rwa [hgen V hV]⟩
  have hfr₁ : IsFrameSystem 𝒱 (ContinuousMap.id _)
      (fun V => (lineBundleCore L).localTriv (gen V).1) :=
    fun V hV => ⟨⟨_, rfl⟩, fun y hy => (hmem V hV y hy).1⟩
  have hfr₂ : IsFrameSystem 𝒱 (ContinuousMap.id _)
      (fun V => (lineBundleCore M).localTriv (gen V).2) :=
    fun V hV => ⟨⟨_, rfl⟩, fun y hy => (hmem V hV y hy).2⟩
  exact firstChernClass_eq_add h𝒱 hcov hfr hfr₁ hfr₂ fun V hV W hW y hy =>
    transition_localTriv_tensorGen _ _ _ _ (hmem V hV y hy.1) (hmem W hW y hy.2)

open InvertibleModule ComplexPoints ComplexLineBundle AlgebraicGeometry in
/-- **Naturality of `c₁` under pullback.** Let `f : X' ⟶ X` be a morphism of schemes over `ℂ`,
realized on `ℂ`-points by the continuous map `g : X'^an ⟶ X^an`, `g(x) = f ∘ x`. For an
invertible `𝒪_X`-module `L`, `c₁(f^* L) = g^* c₁(L)` in `H²(X'^an; ℤ)`. -/
theorem algebraicFirstChernClass_pullback {X' X : Scheme.{0}} [X'.Over (Spec (.of ℂ))]
    [X.Over (Spec (.of ℂ))] (f : X' ⟶ X)
    (g : Analytification.space (X' ↘ Spec (.of ℂ)) ⟶ Analytification.space (X ↘ Spec (.of ℂ)))
    (hg : ∀ x, (g x).hom = x.hom ≫ f) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj L)] :
    algebraicFirstChernClass ((Scheme.Modules.pullback f).obj L) =
      (relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) g (A' := Set.univᶜ) (A := Set.univᶜ)
        (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2).hom (algebraicFirstChernClass L) := by
  classical
  have hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  rcases isEmpty_or_nonempty (ComplexPoints (X' ↘ Spec (.of ℂ))) with hB | ⟨⟨x₀⟩⟩
  · exact singularCohomology_two_eq_of_isEmpty _ _
  let s₀ : Generator L := (exists_generator (g x₀).toScheme).choose
  let 𝒱 : Set (Set (ComplexPoints (X' ↘ Spec (.of ℂ)))) :=
    Set.range fun s : Generator L => chart (f ⁻¹ᵁ s.W)
  let gen : Set (ComplexPoints (X' ↘ Spec (.of ℂ))) → Generator L :=
    fun V => if h : V ∈ 𝒱 then h.choose else s₀
  have hgen : ∀ V ∈ 𝒱, chart (f ⁻¹ᵁ (gen V).W) = V := fun V hV => by
    simp only [gen, dite_eq_left hV]
    exact hV.choose_spec
  have h𝒱 : ∀ V ∈ 𝒱, IsOpen V := by
    rintro _ ⟨s, rfl⟩
    exact isOpen_chart _
  have hcov : ∀ y : ComplexPoints (X' ↘ Spec (.of ℂ)), ∃ V ∈ 𝒱, y ∈ V := fun y => by
    refine ⟨_, ⟨(exists_generator (L := L) (g y).toScheme).choose, rfl⟩, ?_⟩
    change y ∈ chart (f ⁻¹ᵁ _)
    have h := mem_chart_iff.2 (exists_generator (L := L) (g y).toScheme).choose_spec
    change (g y).hom ⁻¹ᵁ _ = ⊤ at h
    rwa [hg y] at h
  have hfr : IsFrameSystem 𝒱 g.hom
      (fun V => (lineBundleCore L).localTriv (gen V)) := fun V hV =>
    ⟨⟨_, rfl⟩, fun y hy => by
      rw [← hgen V hV] at hy
      exact mem_chart_of_hom_eq f hg hy⟩
  have hfr' : IsFrameSystem 𝒱 (ContinuousMap.id _)
      (fun V => (lineBundleCore ((Scheme.Modules.pullback f).obj L)).localTriv
        (pullbackGen f hL (gen V))) := fun V hV =>
    ⟨⟨_, rfl⟩, fun y hy => by rwa [← hgen V hV] at hy⟩
  have key := firstChernClass_eq_ofCocycle_comp h𝒱 hcov g.hom hfr hfr' fun V hV W hW y hy =>
    transition_localTriv_pullbackGen f hL hg (gen V) (gen W)
      (by rw [hgen V hV]; exact hy.1) (by rw [hgen W hW]; exact hy.2)
  unfold algebraicFirstChernClass analyticFirstChernClass
  rw [key]
  unfold firstChernClass cohomologyWithSupports.ofCocycle
  apply (relativeSingularCohomologyEquiv ℤ (Set.univᶜ : Set (TopCat.of
    (ComplexPoints (X' ↘ Spec (.of ℂ))))) 2).injective
  erw [LinearEquiv.apply_symm_apply]
  refine Eq.trans ?_ (relativeSingularCohomologyEquiv_map (g := g) (n := 2) (x := _) _).symm
  erw [LinearEquiv.apply_symm_apply]
  rfl

end MMP.Analytic
