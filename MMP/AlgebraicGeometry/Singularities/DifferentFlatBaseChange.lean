module

public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.RingTheory.DualizingComplex.FlatLocalExtension
public import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.MMP.Fourfold.ConvexGeography
import MMP.RingTheory.DiscreteValuationRing.Integrality

/-!
# Flat base change of local invariants, and rationality of restricted boundaries

This file collects three results used along the terminal chain of the minimal model program,
each a comparison of an invariant across a base change or a limit.

**The different along a regular branch.** Let `A → R` be a flat local homomorphism of
two-dimensional Noetherian normal local domains with `𝔪_A R = 𝔪_R`, and let `I ⊆ A` be a
height-one prime such that `C = A ⧸ I` and `C_R = R ⧸ I R` are discrete valuation rings. Let
`ω_A = H^{-2}(K_A)` and `ω_R = H^{-2}(K_R)` be the canonical modules of normalized dualizing
complexes and `M = Hom_A(I, ω_A)`. The canonical adjunction identifies `ω_C` with the cokernel of
the restriction `ω_A → M`, `x ↦ (a ↦ a • x)`. If the reflexive power `M^[n] = (⨂ⁿ M)^{∨∨}` is
free, the product map `⨂ⁿ M → M^[n]` induces a `C`-linear map `δ_n : ⨂ⁿ_C ω_C → C ⊗_A M^[n]`;
it is injective with cokernel of finite length, and that length (divided by `n`, the local
coefficient of the different at the closed point of `Spec C`) is the same for the map `δ_n`
formed over `R`.

**Regular surface models over the completed strict henselization.** Let `A` be a normal
two-dimensional local domain essentially of finite type over a field `k` of characteristic
zero, `H = A^{sh}` a strict henselization and `R = Ĥ` its `𝔪_H`-adic completion. For a proper
birational `q : W ⟶ Spec A` from a regular scheme, the base change `W_R = W ×_{Spec A} Spec R`
is an integral Noetherian regular scheme of dimension two, proper and birational over `Spec R`.
Over the generic point `η` of an exceptional prime curve of `W`, every generic point `ξ` of a
component of its preimage in `W_R` has a discrete valuation ring as local ring, the local map
`𝒪_{W,η} → 𝒪_{W_R,ξ}` is flat and carries the maximal ideal onto the maximal ideal, orders of
rational functions are unchanged, and the canonical comparison
`MMP.flatHomologyTensorComparison` in degree `-1` preserves the `𝔪`-adic order of every element
of the canonical module.

**Rationality of the clipped boundary of a restricted series.** Assume the birational
finite-generation property `F(d)`, and let `V` be a graded restricted series on a smooth complex
`d`-fold `S`, projective and birational over `T`, finite over `Spec A`, satisfying the
section-lifting inequality. Then the clipped boundary `Θ = Ω - Ω ∧ F` is a `ℚ`-divisor; for
every sufficiently divisible `k > 0`, multiplication by the canonical section `σ_{k(Ω - Θ)}`
identifies `H⁰(S, 𝒪_S(k(K_S + Θ)))` with `V_k`; and the graded algebra `⊕_m V_m tᵐ ⊆ K(S)[t]`
is a finitely generated `A`-algebra.

## Main results

* `MMP.Flips.length_cokernel_eq_of_flat_of_isDiscreteValuationRing`: the maps `δ_n` over `A`
  and over `R` are injective, and their cokernels have the same finite length.
* `MMP.Foundations.isRegular_pullback_strictHenselization_adicCompletion`: regular surface
  models base change to regular surface models over `R`, preserving orders and canonical frames
  along the geometric components of exceptional curves.
* `MMP.Fourfold.exists_qDivisor_eq_restrictedClippedBoundary_of_hasRestrictedLiftingProperty`:
  restricted-boundary rationality from the lifting inequality.

## Implementation notes

The canonical module of `C` is not formed as `H^{-1}` of the derived Hom complex
`RHom_A(C, K_A)`. Instead it is any `C`-module `W` with an `A`-linear surjection `ρ : M → W`
whose kernel is the image of the restriction `ω_A → M`. Since `Ext¹_A(A, ω_A) = 0`, the
connecting map `Hom_A(I, ω_A) → Ext¹_A(C, ω_A) = ω_C` of `0 → I → A → C → 0` is such a pair, and
any two such pairs are uniquely isomorphic, compatibly with `ρ`. The map `δ_n` is pinned by its
values `δ_n(ρ m₁ ⊗ ⋯ ⊗ ρ mₙ) = 1 ⊗ (m₁ ⊗ ⋯ ⊗ mₙ)^{∨∨}`, which span its source. The complex `K_R`
is any normalized dualizing complex of `R`; by uniqueness of normalized dualizing complexes over
a local ring this covers the derived base change `K_A ⊗^L_A R`. The statement reads cohomology
in the locally small model of `D(ModuleCat A)`, while the duality theory is stated in the
standard model; the two cohomology modules of an object are compared by an explicit
isomorphism.

The strict henselization is given abstractly, as an `A`-algebra `H` with
`IsLocalRing.IsHenselization A κsep H` for a separable closure `κsep` of the residue field of
`A`, and `R` is `AdicCompletion (maximalIdeal H) H`. The geometric components of an exceptional
curve on `W_R` are the points of the preimage of the closure of `η` that are not proper
specializations of another of its points. The coefficient of a rational section of a tensor
power of the canonical module along a codimension-one point is the order of a numerator in the
canonical module minus the order of a denominator in the local ring; its invariance is
therefore the conjunction of the order clause for rational functions and the order clause for
the canonical comparison.

Sections of `𝒪_S(D)` are rational functions (`MMP.Fourfold.divisorialSections`), and the
canonical section of an effective divisor is the function `1`; so multiplication by
`σ_{k(Ω - Θ)}` is the identity of `K(S)`, and the identification of section spaces is the
equality of `V_k` with `H⁰(S, 𝒪_S(kK + ⌊kΘ⌋))` as subsets of `K(S)`. The graded algebra is the
set of polynomials in `K(S)[t]` whose `m`-th coefficient lies in `V_m`, and finite generation
over `A` is generation as a ring by the image of `A` (through
`MMP.Fourfold.restrictedSeriesBaseMap`) and finitely many elements.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], §16
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KM98]
* The fourfold source, *Restricted rationality*, the theorem on restricted-boundary rationality
  from the lifting inequality.
-/

@[expose] public section

universe u

/-! ## The different along a regular branch under flat local extension

The argument has three parts.

* **The canonical adjunction is a line.** Since `A` is Cohen–Macaulay, `ω_A` is a dualizing
  module: it is torsion free, isomorphic to a nonzero ideal, and of depth two. Depth two makes
  the uniformizer of `C` a nonzerodivisor on `W`, so `W` is free over the discrete valuation ring
  `C`. Over the discrete valuation ring `A_I` the modules `I`, `ω_A` and `M` become free of rank
  one, the restriction `ω → M` lands in `𝔪 M`, and so `W` is free of rank one.
* **`δ_n` at the generic point.** A generator `ρ m₀` of `W` makes `1 ⊗ m₀` a generator of
  `A_I ⊗ M`; the flat base change of the reflexive power along `A → A_I` carries
  `1 ⊗ (m₀ ⊗ ⋯ ⊗ m₀)^{∨∨}` to a basis vector of a line over `κ(I) = Frac C`. Hence `δ_n` is
  injective and its cokernel is torsion, so of finite length over `C`.
* **The flat comparison.** Since normalized dualizing complexes are unique, `ω_R ≅ R ⊗ ω_A`, and
  flat base change of `Hom` out of a finitely presented module, of duals and of tensor powers
  identifies `R ⊗ M^[n]` with the reflexive power over `R`, compatibly with the products. The
  ranges of the two maps `δ_n` are spanned by the images of these products, so
  `C_R ⊗_C coker δ_n ≅ coker δ_n^R`; these identifications are used only as abstract
  isomorphisms. Flat base change along `C → C_R`, whose closed fibre is the residue field,
  preserves length.
-/

namespace MMP.Flips

open CategoryTheory IsLocalRing TensorProduct PiTensorProduct

/- The statements use `ModuleCat.hasDerivedCategory` as the derived category of
modules; another instance is in scope here, so it is preferred explicitly. -/
attribute [local instance 2000] ModuleCat.hasDerivedCategory

/-! ### Base change of tensor powers, duals and cokernels -/

private theorem exists_tensorPower_baseChange (R S P : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup P] [Module R P] (n : ℕ) :
    ∃ e : S ⊗[R] (⨂[R]^n P) ≃ₗ[S] ⨂[S]^n (S ⊗[R] P),
      ∀ p : Fin n → P, e (1 ⊗ₜ tprod R p) = tprod S (fun i => (1 : S) ⊗ₜ[R] p i) := by
  induction n with
  | zero =>
    refine ⟨(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (TensorPower.algebraMap₀ (R := R) (M := P)).symm) ≪≫ₗ
        TensorProduct.AlgebraTensorModule.rid R S S ≪≫ₗ TensorPower.algebraMap₀, fun p => ?_⟩
    have h1 : tprod R p = TensorPower.algebraMap₀ (1 : R) := by
      rw [TensorPower.algebraMap₀_one, TensorPower.gOne_def]; congr 1; funext i; exact i.elim0
    have h2 : tprod S (fun i => (1 : S) ⊗ₜ[R] p i) = TensorPower.algebraMap₀ (1 : S) := by
      rw [TensorPower.algebraMap₀_one, TensorPower.gOne_def]; congr 1; funext i; exact i.elim0
    rw [h1, h2]
    simp
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    let e1 : S ⊗[R] (⨂[R]^1 P) ≃ₗ[S] ⨂[S]^1 (S ⊗[R] P) :=
      ((PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 => P) 0).baseChange
        R S _ _) ≪≫ₗ
        (PiTensorProduct.subsingletonEquiv (R := S) (s := fun _ : Fin 1 => S ⊗[R] P) 0).symm
    have he1 : ∀ q : Fin 1 → P, e1 (1 ⊗ₜ tprod R q) = tprod S (fun i => (1 : S) ⊗ₜ[R] q i) := by
      intro q
      simp only [e1, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
        PiTensorProduct.subsingletonEquiv_apply_tprod]
      rw [LinearEquiv.symm_apply_eq, PiTensorProduct.subsingletonEquiv_apply_tprod]
    refine ⟨(TensorPower.mulEquiv (R := R) (M := P) (n := n) (m := 1)).symm.baseChange R S _ _ ≪≫ₗ
      TensorProduct.AlgebraTensorModule.distribBaseChange R S _ _ ≪≫ₗ
      TensorProduct.congr e e1 ≪≫ₗ TensorPower.mulEquiv, fun p => ?_⟩
    have hp : tprod R p = TensorPower.mulEquiv
        (tprod R (fun i : Fin n => p (Fin.castAdd 1 i)) ⊗ₜ
          tprod R (fun i : Fin 1 => p (Fin.natAdd n i))) := by
      rw [← TensorPower.gMul_def, TensorPower.tprod_mul_tprod, Fin.append_castAdd_natAdd]
    have hq : tprod S (fun i => (1 : S) ⊗ₜ[R] p i) = TensorPower.mulEquiv
        (tprod S (fun i : Fin n => (1 : S) ⊗ₜ[R] p (Fin.castAdd 1 i)) ⊗ₜ
          tprod S (fun i : Fin 1 => (1 : S) ⊗ₜ[R] p (Fin.natAdd n i))) := by
      rw [← TensorPower.gMul_def, TensorPower.tprod_mul_tprod]
      congr 1
      exact (Fin.append_castAdd_natAdd (f := fun i => (1 : S) ⊗ₜ[R] p i)).symm
    rw [hp, hq]
    simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_apply,
      TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul, he, he1]

section

variable (B B' : Type*) [CommRing B] [CommRing B'] [Algebra B B'] [Module.Flat B B']

/-- For a flat `B`-algebra `B'` and a finitely presented `B`-module `P`, the canonical
isomorphism `B' ⊗_B Hom_B(P, B) ≅ Hom_{B'}(B' ⊗_B P, B')`. -/
private noncomputable def dualBaseChange (P : Type*) [AddCommGroup P] [Module B P]
    [Module.FinitePresentation B P] :
    B' ⊗[B] Module.Dual B P ≃ₗ[B'] Module.Dual B' (B' ⊗[B] P) :=
  (Module.FinitePresentation.isBaseChange_map B P B B').equiv ≪≫ₗ
    LinearEquiv.congrRight (AlgebraTensorModule.rid B B' B')

/-- `dualBaseChange` sends `b ⊗ f` to `b' ⊗ p ↦ b b' f(p)`. -/
private theorem dualBaseChange_tmul_tmul (P : Type*) [AddCommGroup P] [Module B P]
    [Module.FinitePresentation B P] (b b' : B') (f : Module.Dual B P) (p : P) :
    dualBaseChange B B' P (b ⊗ₜ f) (b' ⊗ₜ p) = b * (b' * algebraMap B B' (f p)) := by
  simp only [dualBaseChange, LinearEquiv.trans_apply, IsBaseChange.equiv_tmul]
  change AlgebraTensorModule.rid B B' B' ((b • (LinearMap.baseChangeHom B B' P B f)) (b' ⊗ₜ p)) = _
  simp [Algebra.smul_def]
  ring

/-- Flat base change of the double dual of a finite module over a Noetherian ring, compatibly
with the evaluation maps. -/
private theorem exists_doubleDual_baseChange [IsNoetherianRing B] (T T' : Type*) [AddCommGroup T]
    [Module B T] [Module.Finite B T] [AddCommGroup T'] [Module B' T'] (e : B' ⊗[B] T ≃ₗ[B'] T') :
    ∃ Φ : B' ⊗[B] Module.Dual B (Module.Dual B T) ≃ₗ[B'] Module.Dual B' (Module.Dual B' T'),
      ∀ t : T, Φ (1 ⊗ₜ Module.Dual.eval B T t) = Module.Dual.eval B' T' (e (1 ⊗ₜ t)) := by
  have := Module.finitePresentation_of_finite B T
  have := Module.finitePresentation_of_finite B (Module.Dual B T)
  refine ⟨dualBaseChange B B' (Module.Dual B T) ≪≫ₗ (dualBaseChange B B' T).dualMap.symm ≪≫ₗ
    e.dualMap.dualMap, fun t => ?_⟩
  ext φ
  obtain ⟨x, rfl⟩ := ((dualBaseChange B B' T).trans e.symm.dualMap).surjective φ
  simp only [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply, Module.Dual.eval_apply]
  rw [show e.dualMap (e.symm.dualMap (dualBaseChange B B' T x)) = dualBaseChange B B' T x by
    ext y; simp]
  rw [LinearEquiv.dualMap_symm, LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b f => simp [dualBaseChange_tmul_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

end

/-- The range of a map out of `⨂ⁿ W` pinned on the products of a surjection `M → W` is spanned by
the values `1 ⊗ L t`. -/
private theorem range_eq_span_tmul {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    {M X W : Type*} [AddCommGroup M] [Module A M] [AddCommGroup X] [Module A X]
    [AddCommGroup W] [Module C W] [Module A W] [IsScalarTower A C W] {n : ℕ}
    (ρ : M →ₗ[A] W) (hρ : Function.Surjective ρ) (L : ⨂[A]^n M →ₗ[A] X)
    (δ : ⨂[C]^n W →ₗ[C] C ⊗[A] X)
    (hδ : ∀ m : Fin n → M, δ (PiTensorProduct.tprod C fun i => ρ (m i)) =
      1 ⊗ₜ L (PiTensorProduct.tprod A m)) :
    LinearMap.range δ = Submodule.span C (Set.range fun t => (1 : C) ⊗ₜ[A] L t) := by
  apply le_antisymm
  · rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span_le]
    rintro _ ⟨w, rfl⟩
    choose m hm using fun i => hρ (w i)
    have : w = fun i => ρ (m i) := funext fun i => (hm i).symm
    rw [this, hδ]
    exact Submodule.subset_span ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    dsimp only
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      refine ⟨algebraMap A C r • PiTensorProduct.tprod C fun i => ρ (m i), ?_⟩
      rw [map_smul, hδ, map_smul, TensorProduct.tmul_smul, algebraMap_smul]
    | add x y hx hy =>
      rw [map_add, TensorProduct.tmul_add]
      exact Submodule.add_mem _ hx hy

/-- The cokernel of the map `δ_n` formed after a base change `A → R` is the base change along
`C → C_R` of the cokernel of `δ_n`, as soon as the targets are identified compatibly with the
products. -/
private theorem nonempty_quotient_range_equiv_of_baseChange
    {A R C CR : Type*} [CommRing A] [CommRing R] [CommRing C] [CommRing CR] [Algebra A R]
    [Algebra A C] [Algebra C CR] [Algebra A CR] [Algebra R CR] [IsScalarTower A C CR]
    [IsScalarTower A R CR]
    {M X W : Type*} [AddCommGroup M] [Module A M] [AddCommGroup X] [Module A X]
    [AddCommGroup W] [Module C W] [Module A W] [IsScalarTower A C W]
    {MR XR WR : Type*} [AddCommGroup MR] [Module R MR] [AddCommGroup XR] [Module R XR]
    [AddCommGroup WR] [Module CR WR] [Module R WR] [IsScalarTower R CR WR] {n : ℕ}
    (L : ⨂[A]^n M →ₗ[A] X) (LR : ⨂[R]^n MR →ₗ[R] XR)
    (E : R ⊗[A] ⨂[A]^n M ≃ₗ[R] ⨂[R]^n MR) (Φ : R ⊗[A] X ≃ₗ[R] XR)
    (hΦ : ∀ t, Φ (1 ⊗ₜ L t) = LR (E (1 ⊗ₜ t)))
    (ρ : M →ₗ[A] W) (hρ : Function.Surjective ρ) (δ : ⨂[C]^n W →ₗ[C] C ⊗[A] X)
    (hδ : ∀ m : Fin n → M, δ (PiTensorProduct.tprod C fun i => ρ (m i)) =
      1 ⊗ₜ L (PiTensorProduct.tprod A m))
    (ρR : MR →ₗ[R] WR) (hρR : Function.Surjective ρR) (δR : ⨂[CR]^n WR →ₗ[CR] CR ⊗[R] XR)
    (hδR : ∀ m : Fin n → MR, δR (PiTensorProduct.tprod CR fun i => ρR (m i)) =
      1 ⊗ₜ LR (PiTensorProduct.tprod R m)) :
    Nonempty (CR ⊗[C] (_ ⧸ LinearMap.range δ) ≃ₗ[CR] (_ ⧸ LinearMap.range δR)) := by
  let Ψ : CR ⊗[C] (C ⊗[A] X) ≃ₗ[CR] CR ⊗[R] XR :=
    AlgebraTensorModule.cancelBaseChange A C CR CR X ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange A R CR CR X).symm ≪≫ₗ Φ.baseChange R CR _ _
  have hΨ : ∀ (c : CR) (x : X), Ψ (c ⊗ₜ (1 ⊗ₜ x)) = c ⊗ₜ Φ (1 ⊗ₜ x) := by
    intro c x
    simp [Ψ]
  have hA := range_eq_span_tmul ρ hρ L δ hδ
  have hR := range_eq_span_tmul ρR hρR LR δR hδR
  have hgen : ∀ t, Ψ (1 ⊗ₜ (1 ⊗ₜ L t)) ∈ LinearMap.range δR := by
    intro t
    rw [hΨ, hΦ, hR]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hone : ∀ s ∈ LinearMap.range δ, Ψ (1 ⊗ₜ s) ∈ LinearMap.range δR := by
    intro s hs
    rw [hA] at hs
    induction hs using Submodule.span_induction with
    | mem x hx => obtain ⟨t, rfl⟩ := hx; exact hgen t
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul CR a, map_smul]
      exact Submodule.smul_mem _ _ hx
  refine ⟨AlgebraTensorModule.tensorQuotientEquiv CR C CR (LinearMap.range δ) ≪≫ₗ
    Submodule.Quotient.equiv _ _ Ψ ?_⟩
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c s =>
      simp only [Submodule.mem_comap, LinearEquiv.coe_coe]
      rw [AlgebraTensorModule.lTensor_tmul]
      rw [show c ⊗ₜ[C] ((LinearMap.restrictScalars C (LinearMap.range δ).subtype) s) =
        c • ((1 : CR) ⊗ₜ[C] (s : C ⊗[A] X)) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl]
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hone _ s.2)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · rw [hR, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := E.surjective y
    dsimp only
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | tmul r t =>
      have h1 : (1 : C) ⊗ₜ[A] L t ∈ LinearMap.range δ := by
        rw [hA]; exact Submodule.subset_span ⟨t, rfl⟩
      refine ⟨(AlgebraTensorModule.lTensor CR CR ((LinearMap.range δ).subtype.restrictScalars C))
        (algebraMap R CR r ⊗ₜ ⟨_, h1⟩), ⟨_, rfl⟩, ?_⟩
      rw [show r ⊗ₜ[A] t = r • ((1 : R) ⊗ₜ[A] t) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul, map_smul, TensorProduct.tmul_smul, ← hΦ, ← hΨ, ← algebraMap_smul CR r,
        ← map_smul, AlgebraTensorModule.lTensor_tmul, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
      rfl
    | add x y hx hy =>
      rw [map_add, map_add, TensorProduct.tmul_add]
      exact Submodule.add_mem _ hx hy

/-- If `ω` is torsion free of depth two along every nonzero element of the maximal ideal, the
cokernel `W` of the restriction `ω → Hom_B(J, ω)` is torsion free over the discrete valuation
ring `B ⧸ J`. -/
private theorem isTorsionFree_of_exact {B : Type*} [CommRing B] [IsDomain B] [IsLocalRing B]
    (J : Ideal B) [IsDomain (B ⧸ J)] [IsDiscreteValuationRing (B ⧸ J)]
    {ω : Type*} [AddCommGroup ω] [Module B ω] [Module.IsTorsionFree B ω]
    (hdepth : ∀ x ∈ maximalIdeal B, x ≠ 0 → ∀ e : ω,
      (∀ b ∈ maximalIdeal B, ∃ e' : ω, b • e = x • e') → ∃ e' : ω, e = x • e')
    (W : Type*) [AddCommGroup W] [Module (B ⧸ J) W] [Module B W] [IsScalarTower B (B ⧸ J) W]
    (ρ : (J →ₗ[B] ω) →ₗ[B] W) (hρ : Function.Surjective ρ)
    (hρex : Function.Exact
      (LinearMap.lcomp B _ J.subtype ∘ₗ (LinearMap.ringLmapEquivSelf B B ω).symm.toLinearMap) ρ) :
    Module.IsTorsionFree (B ⧸ J) W := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (B ⧸ J)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective π
  have hx0 : x ≠ 0 := by rintro rfl; exact hπ.ne_zero (map_zero _)
  have hxm : x ∈ maximalIdeal B := by
    by_contra h
    exact hπ.not_isUnit ((IsLocalRing.notMem_maximalIdeal.mp h).map _)
  have hmJ : ∀ b ∈ maximalIdeal B, ∃ c : B, b - c * x ∈ J := by
    intro b hb
    have hb' : Ideal.Quotient.mk J b ∈ maximalIdeal (B ⧸ J) := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
      exact Ideal.mem_map_of_mem _ hb
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπ,
      Ideal.mem_span_singleton'] at hb'
    obtain ⟨a, ha⟩ := hb'
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨c, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    rw [map_sub, map_mul, ha, sub_self]
  have hr : ∀ e : ω, ∀ a : J,
      (LinearMap.lcomp B _ J.subtype ∘ₗ (LinearMap.ringLmapEquivSelf B B ω).symm.toLinearMap) e a =
        (a : B) • e := by
    intro e a; simp
  have hxreg : ∀ e e' : ω, x • e = x • e' → e = e' := fun e e' h =>
    Module.IsTorsionFree.isSMulRegular (isRegular_iff_ne_zero.mpr hx0) h
  have hinj : ∀ w : W, Ideal.Quotient.mk J x • w = 0 → w = 0 := by
    intro w hw
    obtain ⟨φ, rfl⟩ := hρ w
    have h1 : Ideal.Quotient.mk J x • ρ φ = ρ (x • φ) := by
      rw [map_smul, ← algebraMap_smul (B ⧸ J) x, Ideal.Quotient.algebraMap_eq]
    rw [h1] at hw
    obtain ⟨e, he⟩ := (hρex (x • φ)).mp hw
    have hea : ∀ a : J, (a : B) • e = x • φ a := by
      intro a
      rw [← hr, he, LinearMap.smul_apply]
    obtain ⟨e', rfl⟩ := hdepth x hxm hx0 e (by
      intro b hb
      obtain ⟨c, hc⟩ := hmJ b hb
      refine ⟨φ ⟨_, hc⟩ + c • e, ?_⟩
      have := hea ⟨_, hc⟩
      simp only at this
      rw [smul_add, ← this, smul_comm x c e, smul_smul, ← add_smul, sub_add_cancel])
    apply (hρex φ).mpr
    refine ⟨e', LinearMap.ext fun a => ?_⟩
    rw [hr]
    apply hxreg
    rw [← hea, smul_comm]
  have hpow : ∀ (k : ℕ) (w : W), (Ideal.Quotient.mk J x) ^ k • w = 0 → w = 0 := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ', mul_smul] at hw
      exact ih w (hinj _ hw)
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro c w hcw
  by_cases hc : c = 0
  · exact Or.inl hc
  right
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hπ
  rw [mul_smul] at hcw
  apply hpow k
  have := congrArg (fun v => (↑u⁻¹ : B ⧸ J) • v) hcw
  simpa [smul_smul] using this

/-- A finite module over a discrete valuation ring killed by a nonzero element has finite
length. -/
private theorem length_lt_top_of_mem_annihilator {C Q : Type*} [CommRing C] [IsDomain C]
    [IsDiscreteValuationRing C] [AddCommGroup Q] [Module C Q] [Module.Finite C Q]
    {c : C} (hc : c ≠ 0) (hcQ : ∀ q : Q, c • q = 0) : Module.length C Q < ⊤ := by
  have hart : IsArtinianRing (C ⧸ Ideal.span {c}) := by
    have hx : c ∈ nonZeroDivisors C := mem_nonZeroDivisors_of_ne_zero hc
    rw [isArtinianRing_iff_krullDimLE_zero, Ring.KrullDimLE, Order.krullDimLE_iff,
      ← ENat.WithBot.add_le_add_one_right_iff, Nat.cast_zero, zero_add]
    exact (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx).trans
      (Order.KrullDimLE.krullDim_le)
  have htor : Module.IsTorsionBySet C Q (Ideal.span {c} : Set C) := by
    intro x a
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp a.2
    rw [← hd, mul_smul, hcQ, smul_zero]
  let := htor.module
  have : Module.Finite (C ⧸ Ideal.span {c}) Q := Module.Finite.of_restrictScalars_finite C _ Q
  have : IsArtinian C Q := isArtinian_of_surjective_algebraMap (R := C ⧸ Ideal.span {c})
    (S := C) Ideal.Quotient.mk_surjective
  exact lt_top_iff_ne_top.mpr Module.length_ne_top

/-- A map from a cyclic module over a discrete valuation ring `C` into a finite module whose
generic fibre is a line, nonzero at the generic point, is injective with finite length
cokernel. -/
private theorem injective_and_length_lt_top_of_finrank_eq_one {C F S N : Type*} [CommRing C]
    [IsDomain C] [IsDiscreteValuationRing C] [Field F] [Algebra C F] [IsFractionRing C F]
    [AddCommGroup S] [Module C S] [AddCommGroup N] [Module C N] [Module.Finite C N]
    (δ : S →ₗ[C] N) (g : S) (hg : ∀ s, ∃ c : C, s = c • g)
    (hN : Module.finrank F (F ⊗[C] N) = 1) (hy : (1 : F) ⊗ₜ[C] δ g ≠ 0) :
    Function.Injective δ ∧ Module.length C (N ⧸ LinearMap.range δ) < ⊤ := by
  have hinjF : Function.Injective (algebraMap C F) := IsFractionRing.injective C F
  refine ⟨fun s s' h => ?_, ?_⟩
  · rw [← sub_eq_zero, ← map_sub] at h
    rw [← sub_eq_zero]
    obtain ⟨c, hc⟩ := hg (s - s')
    rw [hc, map_smul] at h
    rw [hc]
    have h2 : algebraMap C F c • ((1 : F) ⊗ₜ[C] δ g) = 0 := by
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, h, TensorProduct.tmul_zero]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · rw [(map_eq_zero_iff _ hinjF).mp h3, zero_smul]
    · exact absurd h3 hy
  · set Q := N ⧸ LinearMap.range δ
    have hQ : Subsingleton (F ⊗[C] Q) := by
      have : FiniteDimensional F (F ⊗[C] N) := Module.finite_of_finrank_eq_succ hN
      have hspan : ∀ z : F ⊗[C] N, ∃ a : F, z = a • ((1 : F) ⊗ₜ[C] δ g) := by
        intro z
        obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hy).mp hN z
        exact ⟨a, ha.symm⟩
      refine ⟨fun z z' => ?_⟩
      have hsurj : Function.Surjective ((LinearMap.range δ).mkQ.baseChange F) :=
        LinearMap.baseChange_surjective _ (Submodule.mkQ_surjective _)
      suffices h0 : ∀ z : F ⊗[C] Q, z = 0 by rw [h0 z, h0 z']
      intro z
      obtain ⟨w, rfl⟩ := hsurj z
      obtain ⟨a, rfl⟩ := hspan w
      rw [map_smul, LinearMap.baseChange_tmul, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self δ g), tmul_zero,
        smul_zero]
    have hloc : IsLocalizedModule (nonZeroDivisors C) (TensorProduct.mk C F Q 1) :=
      (isLocalizedModule_iff_isBaseChange (nonZeroDivisors C) F _).mpr
        (TensorProduct.isBaseChange C Q F)
    have htors : Module.IsTorsion C Q := by
      intro q
      obtain ⟨r, hr, hrq⟩ := (IsLocalizedModule.subsingleton_iff (nonZeroDivisors C)
        (TensorProduct.mk C F Q 1)).mp hQ q
      exact ⟨⟨r, hr⟩, hrq⟩
    obtain ⟨c, hcann, hcnz⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htors
    exact length_lt_top_of_mem_annihilator (nonZeroDivisors.ne_zero hcnz)
      fun q => Submodule.mem_annihilator.mp hcann q Submodule.mem_top

/-- The localization of a Noetherian integrally closed domain at a height-one prime is a discrete
valuation ring. -/
private theorem isDiscreteValuationRing_localization_of_height_eq_one (B : Type*) [CommRing B]
    [IsDomain B]
    [IsNoetherianRing B] [IsIntegrallyClosed B] (J : Ideal B) [J.IsPrime] (hJ : J.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime J) := by
  have : IsDomain (Localization.AtPrime J) :=
    IsLocalization.isDomain_localization J.primeCompl_le_nonZeroDivisors
  have h1 : ringKrullDim (Localization.AtPrime J) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height J, hJ]; rfl
  have : Ring.KrullDimLE 1 (Localization.AtPrime J) := Ring.krullDimLE_iff.mpr h1.le
  have : IsIntegrallyClosed (Localization.AtPrime J) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime J) J.primeCompl
      J.primeCompl_le_nonZeroDivisors
  have hnf : ¬ IsField (Localization.AtPrime J) := by
    intro hf
    have := ringKrullDim_eq_zero_of_isField hf
    rw [h1] at this; exact absurd this (by decide)
  have key := (IsDiscreteValuationRing.TFAE (Localization.AtPrime J) hnf).out 1 4
  refine key.mpr ⟨inferInstance, ⟨IsLocalRing.maximalIdeal _, ⟨fun h => hnf ?_, inferInstance⟩,
    fun P ⟨hP0, hP⟩ => ?_⟩⟩
  · exact (IsLocalRing.isField_iff_maximalIdeal_eq).mpr h
  · rcases Ring.krullDimLE_one_iff.mp inferInstance P hP with h | h
    · rw [IsDomain.minimalPrimes_eq_singleton_bot] at h; exact absurd h hP0
    · exact IsLocalRing.eq_maximalIdeal h

/-- For a flat algebra `B → D` and an ideal `Ω` of `B`, `D ⊗_B Ω ≅ Ω D`. -/
private theorem nonempty_tensor_ideal_equiv_map {B D : Type*} [CommRing B] [CommRing D]
    [Algebra B D] [Module.Flat B D] (Ω : Ideal B) :
    Nonempty (D ⊗[B] Ω ≃ₗ[D] Ω.map (algebraMap B D)) := by
  let μ : D ⊗[B] Ω →ₗ[D] D := ((Algebra.linearMap B D).comp Ω.subtype).liftBaseChange D
  have hμ : Function.Injective μ := by
    have h1 : μ = (AlgebraTensorModule.rid B D D).toLinearMap ∘ₗ (Ω.subtype.baseChange D) := by
      ext x; simp [μ, Algebra.smul_def]
    rw [h1, LinearMap.coe_comp, LinearEquiv.coe_coe]
    exact (AlgebraTensorModule.rid B D D).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype Ω))
  have hrange : LinearMap.range μ = Ω.map (algebraMap B D) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul d a =>
        simp only [μ, LinearMap.liftBaseChange_tmul, LinearMap.coe_comp, Function.comp_apply,
          Submodule.coe_subtype, Algebra.linearMap_apply, smul_eq_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ a.2)
      | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact ⟨1 ⊗ₜ ⟨a, ha⟩, by simp [μ]⟩
  exact ⟨LinearEquiv.ofInjective μ hμ ≪≫ₗ LinearEquiv.ofEq _ _ hrange⟩

/-- For an injective flat algebra `B → D` into a principal ideal domain, `D ⊗_B Ω ≅ D` for
every nonzero ideal `Ω` of `B`. -/
private theorem nonempty_tensor_ideal_equiv {B D : Type*} [CommRing B] [CommRing D] [IsDomain D]
    [IsPrincipalIdealRing D] [Algebra B D] [Module.Flat B D]
    (hinj : Function.Injective (algebraMap B D)) (Ω : Ideal B) (hΩ : Ω ≠ ⊥) :
    Nonempty (D ⊗[B] Ω ≃ₗ[D] D) := by
  obtain ⟨e⟩ := nonempty_tensor_ideal_equiv_map (D := D) Ω
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hΩ
  obtain ⟨t, ht⟩ := (IsPrincipalIdealRing.principal (Ω.map (algebraMap B D))).principal
  have ht0 : t ≠ 0 := by
    rintro rfl
    have : algebraMap B D a ∈ Ω.map (algebraMap B D) := Ideal.mem_map_of_mem _ ha
    rw [ht, Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at this
    exact ha0 (hinj (by rw [this, map_zero]))
  exact ⟨e ≪≫ₗ LinearEquiv.ofEq _ _ ht ≪≫ₗ (LinearEquiv.toSpanNonzeroSingleton D D t ht0).symm⟩

/-- The base change of `Hom_B(J, ω)` to the localization at `J` has values in `𝔪 X` on the image
of `ω`. -/
private theorem baseChange_restriction_mem_smul {B : Type*} [CommRing B] [IsNoetherianRing B]
    (J : Ideal B) [J.IsPrime] {ω : Type*} [AddCommGroup ω] [Module B ω]
    (z : Localization.AtPrime J ⊗[B] ω) (y : Localization.AtPrime J ⊗[B] J) :
    haveI := Module.finitePresentation_of_finite B J
    (Module.FinitePresentation.isBaseChange_map B J ω (Localization.AtPrime J)).equiv
      ((LinearMap.lcomp B _ J.subtype ∘ₗ
        (LinearMap.ringLmapEquivSelf B B ω).symm.toLinearMap).baseChange _ z) y ∈
      (maximalIdeal (Localization.AtPrime J)) •
        (⊤ : Submodule (Localization.AtPrime J) (Localization.AtPrime J ⊗[B] ω)) := by
  have := Module.finitePresentation_of_finite B J
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => rw [map_add, map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hz hz'
  | tmul d e =>
    rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, LinearMap.smul_apply,
      LinearMap.baseChangeHom_apply]
    refine Submodule.smul_of_tower_mem _ d ?_
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
    | tmul d' a =>
      rw [LinearMap.baseChange_tmul]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.ringLmapEquivSelf_symm_apply, LinearMap.lcomp_apply, Submodule.coe_subtype,
        LinearMap.smulRight_apply, Module.End.one_apply]
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, ← smul_eq_mul, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem_smul
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ J (a : B)).mpr a.2) Submodule.mem_top

/-- The cokernel `W` of the restriction `ω → Hom_B(J, ω)` is nonzero when `ω` is isomorphic to a
nonzero ideal and `B_J` is a discrete valuation ring. -/
private theorem nontrivial_of_exact {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (J : Ideal B) [J.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime J)] (hJ0 : J ≠ ⊥)
    {ω : Type*} [AddCommGroup ω] [Module B ω] (Ω : Ideal B) (hΩ : Ω ≠ ⊥) (eΩ : ω ≃ₗ[B] Ω)
    (W : Type*) [AddCommGroup W] [Module B W]
    (ρ : (J →ₗ[B] ω) →ₗ[B] W)
    (hρex : Function.Exact
      (LinearMap.lcomp B _ J.subtype ∘ₗ (LinearMap.ringLmapEquivSelf B B ω).symm.toLinearMap) ρ) :
    Nontrivial W := by
  have := Module.finitePresentation_of_finite B J
  by_contra hW
  rw [not_nontrivial_iff_subsingleton] at hW
  set r := LinearMap.lcomp B _ J.subtype ∘ₗ (LinearMap.ringLmapEquivSelf B B ω).symm.toLinearMap
  have hsurj : Function.Surjective r := fun φ => (hρex φ).mp (Subsingleton.elim _ _)
  let D := Localization.AtPrime J
  have hinj : Function.Injective (algebraMap B D) :=
    IsLocalization.injective D J.primeCompl_le_nonZeroDivisors
  obtain ⟨eY⟩ := nonempty_tensor_ideal_equiv (D := D) hinj J hJ0
  obtain ⟨eX0⟩ := nonempty_tensor_ideal_equiv (D := D) hinj Ω hΩ
  let eX : D ⊗[B] ω ≃ₗ[D] D := eΩ.baseChange B D _ _ ≪≫ₗ eX0
  let φ₀ : D ⊗[B] J →ₗ[D] D ⊗[B] ω := eX.symm.toLinearMap ∘ₗ eY.toLinearMap
  obtain ⟨z, hz⟩ := ((Module.FinitePresentation.isBaseChange_map B J ω D).equiv.surjective.comp
    (LinearMap.baseChange_surjective D hsurj)) φ₀
  have hmem := baseChange_restriction_mem_smul J z (eY.symm 1)
  simp only [Function.comp_apply] at hz
  rw [hz] at hmem
  simp only [φ₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply] at hmem
  have h1 : eX (eX.symm 1) ∈ (maximalIdeal D) • (⊤ : Submodule D D) :=
    Submodule.smul_top_le_comap_smul_top (maximalIdeal D) eX.toLinearMap hmem
  rw [LinearEquiv.apply_symm_apply, smul_eq_mul, Ideal.mul_top] at h1
  exact (maximalIdeal.isMaximal D).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- The map `δ_n` is injective with cokernel of finite length, once `W` is free of finite rank over
`B ⧸ J`, `ω` is isomorphic to a nonzero ideal and `B_J` is a discrete valuation ring. -/
private theorem injective_and_length_lt_top_of_linearEquiv {B : Type*} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] (J : Ideal B) [J.IsPrime]
    [IsDiscreteValuationRing (B ⧸ J)] [IsDiscreteValuationRing (Localization.AtPrime J)]
    (hJ0 : J ≠ ⊥) {ω : Type*} [AddCommGroup ω] [Module B ω] [Module.Finite B ω]
    (Ω : Ideal B) (hΩ : Ω ≠ ⊥) (eΩ : ω ≃ₗ[B] Ω)
    (W : Type*) [AddCommGroup W] [Module (B ⧸ J) W] [Module B W] [IsScalarTower B (B ⧸ J) W]
    [Module.Free (B ⧸ J) W] [Module.Finite (B ⧸ J) W]
    (ρ : (J →ₗ[B] ω) →ₗ[B] W) (hρ : Function.Surjective ρ)
    (hρex : Function.Exact
      (LinearMap.lcomp B _ J.subtype ∘ₗ (LinearMap.ringLmapEquivSelf B B ω).symm.toLinearMap) ρ)
    (n : ℕ)
    (δ : TensorPower (B ⧸ J) n W →ₗ[B ⧸ J] (B ⧸ J) ⊗[B] Module.Dual B (Module.Dual B
      (TensorPower B n (J →ₗ[B] ω))))
    (hδ : ∀ m : Fin n → (J →ₗ[B] ω),
      δ (PiTensorProduct.tprod (B ⧸ J) fun i => ρ (m i)) =
        (1 : B ⧸ J) ⊗ₜ[B] Module.Dual.eval B _ (PiTensorProduct.tprod B m)) :
    Function.Injective δ ∧ Module.length (B ⧸ J) (_ ⧸ LinearMap.range δ) < ⊤ := by
  classical
  have := Module.finitePresentation_of_finite B J
  let C := B ⧸ J
  let D := Localization.AtPrime J
  let F := J.ResidueField
  let M := J →ₗ[B] ω
  have hW : Nontrivial W := nontrivial_of_exact J hJ0 Ω hΩ eΩ W ρ hρex
  have hinj : Function.Injective (algebraMap B D) :=
    IsLocalization.injective D J.primeCompl_le_nonZeroDivisors
  obtain ⟨eY⟩ := nonempty_tensor_ideal_equiv (D := D) hinj J hJ0
  obtain ⟨eX0⟩ := nonempty_tensor_ideal_equiv (D := D) hinj Ω hΩ
  let eX : D ⊗[B] ω ≃ₗ[D] D := eΩ.baseChange B D _ _ ≪≫ₗ eX0
  let eH : D ⊗[B] M ≃ₗ[D] D := (Module.FinitePresentation.isBaseChange_map B J ω D).equiv ≪≫ₗ
    LinearEquiv.arrowCongr eY eX ≪≫ₗ LinearMap.ringLmapEquivSelf D D D
  -- `F ⊗_B M` is a line
  let εM : F ⊗[B] M ≃ₗ[F] F := (AlgebraTensorModule.cancelBaseChange B D F F M).symm ≪≫ₗ
    eH.baseChange D F _ _ ≪≫ₗ AlgebraTensorModule.rid D F F
  have : TensorProduct.CompatibleSMul B C F W :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective F W Ideal.Quotient.mk_surjective
  let εW : F ⊗[B] W ≃ₗ[F] F ⊗[C] W := TensorProduct.equivOfCompatibleSMul C B F F W
  have : Module.Finite F (F ⊗[B] M) := Module.Finite.equiv εM.symm
  have hrank : Module.finrank C W = 1 := by
    apply le_antisymm
    · rw [← Module.finrank_baseChange (R := F), ← εW.finrank_eq, ← εM.finrank_eq.trans
        (Module.finrank_self F)]
      exact LinearMap.finrank_le_finrank_of_surjective (LinearMap.baseChange_surjective F hρ)
    · exact Module.finrank_pos
  let b : Module.Basis (Fin 1) C W := Module.finBasisOfFinrankEq C W hrank
  obtain ⟨m₀, hm₀⟩ := hρ (b 0)
  -- `1 ⊗ m₀` generates the line `D ⊗_B M`
  have hu : IsUnit (eH (1 ⊗ₜ m₀)) := by
    by_contra hu
    have hmem : eH (1 ⊗ₜ m₀) ∈ maximalIdeal D := hu
    let Θ : F ⊗[D] (D ⊗[B] M) →ₗ[F] F ⊗[C] W := εW.toLinearMap ∘ₗ (ρ.baseChange F) ∘ₗ
      (AlgebraTensorModule.cancelBaseChange B D F F M).toLinearMap
    have h1 : Θ (1 ⊗ₜ (1 ⊗ₜ m₀)) = (1 : F) ⊗ₜ[C] b 0 := by
      simp [Θ, εW, hm₀]
      rfl
    have h2 : (1 : F) ⊗ₜ[D] ((1 : D) ⊗ₜ[B] m₀) = 0 := by
      have : (1 : D) ⊗ₜ[B] m₀ = eH (1 ⊗ₜ m₀) • eH.symm 1 := by
        rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
      rw [this, TensorProduct.tmul_smul, ← algebraMap_smul F,
        IsLocalRing.ResidueField.algebraMap_eq,
        (IsLocalRing.residue_eq_zero_iff _).mpr hmem, zero_smul]
    have h3 := (b.baseChange F).ne_zero 0
    rw [Module.Basis.baseChange_apply, ← h1, h2, map_zero] at h3
    exact h3 rfl
  -- the reflexive power of the line `D ⊗_B M`
  let bP : Module.Basis (Fin 1) D (D ⊗[B] M) :=
    ((Module.Basis.singleton (Fin 1) D).map eH.symm).unitsSMul fun _ => hu.unit
  have hbP : ∀ i, bP i = 1 ⊗ₜ m₀ := fun i => by
    rw [Module.Basis.unitsSMul_apply, Module.Basis.map_apply, Module.Basis.singleton_apply,
      Units.smul_def, IsUnit.unit_spec, ← map_smul, smul_eq_mul, mul_one,
      LinearEquiv.symm_apply_apply]
  let T' := ⨂[D]^n (D ⊗[B] M)
  let bT : Module.Basis (Fin n → Fin 1) D T' := Basis.piTensorProduct fun _ => bP
  have : Module.Free D T' := Module.Free.of_basis bT
  have : Module.Finite D T' := Module.Finite.of_basis bT
  let bDD := bT.map (Module.evalEquiv D T')
  let bF := bDD.baseChange F
  have hbF : bF (fun _ => 0) =
      1 ⊗ₜ Module.Dual.eval D T' (PiTensorProduct.tprod D fun _ => (1 : D) ⊗ₜ[B] m₀) := by
    rw [Module.Basis.baseChange_apply, Module.Basis.map_apply, Basis.piTensorProduct_apply]
    simp_rw [hbP]
    rfl
  -- transport to `F ⊗_C (C ⊗_B M^[n])`
  obtain ⟨e, he⟩ := exists_tensorPower_baseChange B D M n
  obtain ⟨Φ, hΦ⟩ := exists_doubleDual_baseChange B D (⨂[B]^n M) T' e
  let XB := Module.Dual B (Module.Dual B (⨂[B]^n M))
  let ε : F ⊗[C] (C ⊗[B] XB) ≃ₗ[F] F ⊗[D] Module.Dual D (Module.Dual D T') :=
    AlgebraTensorModule.cancelBaseChange B C F F XB ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange B D F F XB).symm ≪≫ₗ Φ.baseChange D F _ _
  have hε : ∀ x : XB, ε (1 ⊗ₜ (1 ⊗ₜ x)) = 1 ⊗ₜ Φ (1 ⊗ₜ x) := by
    intro x; simp [ε]
  have hN : Module.finrank F (F ⊗[C] (C ⊗[B] XB)) = 1 := by
    rw [ε.finrank_eq, Module.finrank_eq_card_basis bF, Fintype.card_unique]
  let bW := Basis.piTensorProduct (R := C) fun _ : Fin n => b
  have hg : ∀ s : ⨂[C]^n W, ∃ c : C, s = c • PiTensorProduct.tprod C (fun _ => b 0) := by
    intro s
    refine ⟨bW.repr s (fun _ => 0), ?_⟩
    conv_lhs => rw [← bW.sum_repr s]
    have hd : (default : Fin n → Fin 1) = fun _ => 0 := Subsingleton.elim _ _
    rw [Fintype.sum_unique, hd, Basis.piTensorProduct_apply]
  have hδg : δ (PiTensorProduct.tprod C fun _ => b 0) =
      1 ⊗ₜ Module.Dual.eval B _ (PiTensorProduct.tprod B fun _ => m₀) := by
    rw [← hδ]; simp_rw [hm₀]; rfl
  have hy : (1 : F) ⊗ₜ[C] δ (PiTensorProduct.tprod C fun _ => b 0) ≠ 0 := by
    intro h0
    have := congrArg ε h0
    rw [hδg, hε, hΦ, he, map_zero, ← hbF] at this
    exact bF.ne_zero _ this
  exact injective_and_length_lt_top_of_finrank_eq_one δ _ hg hN hy

/-! ### The canonical module of a two-dimensional normal local domain -/

/-- On a finite module of depth at least two over a Noetherian local ring, an element `e` with
`𝔪 e ⊆ x M` for a regular `x ∈ 𝔪` lies in `x M`. -/
private theorem exists_eq_smul_of_two_le_depth {B : Type*} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] {ω : Type*} [AddCommGroup ω] [Module B ω] [Module.Finite B ω]
    [Nontrivial ω] (h : 2 ≤ Module.depth B (maximalIdeal B) ω) (x : B) (hx : x ∈ maximalIdeal B)
    (hreg : IsSMulRegular ω x) (e : ω) (he : ∀ b ∈ maximalIdeal B, ∃ e' : ω, b • e = x • e') :
    ∃ e' : ω, e = x • e' := by
  have hne : (maximalIdeal B) • (⊤ : Submodule B ω) ≠ ⊤ := by
    intro htop
    have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal B) ⊤
      (Module.finite_def.mp inferInstance) htop.ge (IsLocalRing.maximalIdeal_le_jacobson _)
    exact top_ne_bot this
  have hds : 2 ≤ Module.depthSup B (maximalIdeal B) ω := by
    refine h.trans ?_
    simp only [Module.depth, hne, ↓reduceIte]
    exact iSup₂_le fun rs hrs => le_sSup ⟨rs, rfl, hrs⟩
  have hq := depth_quotient_succ_of_isSMulRegular x hx hreg
  have h1 : 1 ≤ Module.depthSup B (maximalIdeal B) (QuotSMulTop x ω) := by
    by_contra hlt
    push Not at hlt
    have h0 : Module.depthSup B (maximalIdeal B) (QuotSMulTop x ω) = 0 := Order.lt_one_iff.mp hlt
    rw [h0, zero_add] at hq
    rw [← hq] at hds
    exact absurd hds (by decide)
  obtain ⟨y, hy, hyreg⟩ : ∃ y ∈ maximalIdeal B, IsSMulRegular (QuotSMulTop x ω) y := by
    by_contra hno
    push Not at hno
    apply absurd h1
    push Not
    rw [Module.depthSup, Order.lt_one_iff]
    refine le_antisymm (sSup_le ?_) bot_le
    rintro _ ⟨rs, rfl, hrs, hreg'⟩
    cases rs with
    | nil => simp
    | cons y rs =>
      exact absurd ((RingTheory.Sequence.isRegular_cons_iff _ y rs).mp hreg').1
        (hno y (hrs y (List.mem_cons_self ..)))
  have hmk : y • (Submodule.Quotient.mk e : QuotSMulTop x ω) = 0 := by
    obtain ⟨e', he'⟩ := he y hy
    rw [← Submodule.Quotient.mk_smul, he', Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  have h0 : (Submodule.Quotient.mk e : QuotSMulTop x ω) = 0 :=
    hyreg (show y • _ = y • _ by rw [hmk, smul_zero])
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at h0
  obtain ⟨e', -, he'⟩ := h0
  exact ⟨e', he'.symm⟩

/-- A prime of a two-dimensional local domain with a discrete valuation ring as quotient is
nonzero of height one. -/
private theorem ne_bot_and_height_eq_one {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] (hB : ringKrullDim B = 2) (J : Ideal B) [J.IsPrime]
    [IsDiscreteValuationRing (B ⧸ J)] : J ≠ ⊥ ∧ J.height = 1 := by
  have hJ0 : J ≠ ⊥ := by
    intro hJ
    have h :=
      ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hJ).trans (RingEquiv.quotientBot B))
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one, hB] at h
    exact absurd h (by decide)
  refine ⟨hJ0, ?_⟩
  have hlt : J < IsLocalRing.maximalIdeal B := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    intro h
    have hmax : J.IsMaximal := h ▸ IsLocalRing.maximalIdeal.isMaximal B
    exact IsDiscreteValuationRing.not_isField (B ⧸ J)
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mp hmax)
  have h2 : (IsLocalRing.maximalIdeal B).height = 2 := by
    have h1 : ((IsLocalRing.maximalIdeal B).height : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := by
      rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hB]; rfl
    exact WithBot.coe_injective h1
  have h3 := Ideal.height_strict_mono_of_isPrime hlt
  rw [h2] at h3
  have h4 : J.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    exact hJ0
  have h5 : J.height ≤ 1 := by simpa using h3
  exact le_antisymm h5 (Order.one_le_iff_ne_zero.mpr h4)

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- The canonical module `H^{-2}(K)` of a two-dimensional normal local domain is a dualizing
module: the ring is Cohen–Macaulay, so `K` is that module placed in degree `-2`. -/
private theorem isDualizingRingModule_canonicalModule {B : Type u} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [IsLocalRing B] [IsIntegrallyClosed B] (hB : ringKrullDim B = 2)
    (K : DerivedCategory (ModuleCat.{u} B)) (hK : Dualizing.IsNormalizedDualizingComplex.{u, u} K) :
    Stacks.Duality.IsDualizingRingModule B
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-2)).obj K) := by
  have hN : IsNormalRing B := fun p _ =>
    ⟨inferInstance, isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl
      p.primeCompl_le_nonZeroDivisors⟩
  have hCM :=
    AlgebraicGeometry.isCohenMacaulayLocalRing_of_isNormalRing_of_ringKrullDim_eq_two hN hB
  obtain ⟨e⟩ := ((Dualizing.isCohenMacaulay_tfae_dualizingComplex K
    (MMP.Flips.isNormalizedDualizingComplex_ulift_zero hK)).out 1 3).mp hCM
  have hdim : Dualizing.localRingDimension B = 2 := by
    have h1 : ((IsLocalRing.maximalIdeal B).height : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := by
      rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hB]; rfl
    have h2 : (IsLocalRing.maximalIdeal B).height = 2 := WithBot.coe_injective h1
    simp [Dualizing.localRingDimension, h2]
  rw [Dualizing.dualizingModule, hdim, show (-((2 : ℕ) : ℤ)) = -2 by norm_num] at e
  exact ⟨hK.1.finiteCohomology _, _, (Dualizing.isDualizingComplex_iff_of_iso e).mp hK.1⟩

end

/-- The cohomology of an object of `D(R)` read in the locally small model and in the standard
model. -/
private noncomputable def moduleHomologyLsIsoStd {R : Type u} [CommRing R]
    (Y : @DerivedCategory (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj Y ≅
      (@DerivedCategory.homologyFunctor (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)
        n).obj Y :=
  let Qs := @DerivedCategory.Q (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)
  let e : Qs.obj (Qs.objPreimage Y) ≅ Y := Qs.objObjPreimageIso Y
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).mapIso
      ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R)).functor.mapIso e).symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app (Qs.objPreimage Y) ≪≫
    ((@DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)
      n).app (Qs.objPreimage Y)).symm ≪≫
    (@DerivedCategory.homologyFunctor (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)
      n).mapIso e

/-- The canonical module `H^{-2}(K)` of a dualizing complex is a finite module. -/
private theorem finite_canonicalModule {B : Type u} [CommRing B] [IsNoetherianRing B]
    [IsLocalRing B]
    (K : DerivedCategory (ModuleCat.{u} B)) (hK : Dualizing.IsNormalizedDualizingComplex.{u, u} K) :
    Module.Finite B ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-2)).obj K) :=
  have := @Dualizing.IsDualizingComplex.finiteCohomology B _ _ (HasDerivedCategory.standard _)
    K hK.1 (-2)
  Module.Finite.equiv (moduleHomologyLsIsoStd K (-2)).toLinearEquiv.symm

set_option backward.isDefEq.respectTransparency false in
/-- Extension of scalars along an algebra map is the tensor product. -/
private noncomputable def extendScalarsEquiv {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (N : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap A B)).obj N ≃ₗ[B] B ⊗[A] N := by
  let e : (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≃ₗ[A] B :=
    { Equiv.refl B with
      map_add' := fun _ _ => rfl
      map_smul' := fun a b => by
        rw [ModuleCat.restrictScalars.smul_def]
        simp only [RingHom.id_apply, smul_eq_mul, Algebra.smul_def]; rfl }
  let t := TensorProduct.congr e (LinearEquiv.refl A N)
  refine { t.toAddEquiv with map_smul' := ?_ }
  intro b z
  change t (b • z) = b • t z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c n => rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The canonical module of a normalized dualizing complex of `R` is the base change of that of
`A`, for a flat local map `A → R` with `𝔪_A R = 𝔪_R`. -/
private theorem nonempty_canonicalModule_baseChange {A R : Type u} [CommRing A] [CommRing R]
    [Algebra A R]
    [IsNoetherianRing A] [IsNoetherianRing R] [IsLocalRing A] [IsLocalRing R]
    [Module.Flat A R] [IsLocalHom (algebraMap A R)] (hA : ringKrullDim A = 2)
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A R) = IsLocalRing.maximalIdeal R)
    (KA : DerivedCategory (ModuleCat.{u} A))
    (hKA : Dualizing.IsNormalizedDualizingComplex.{u, u} KA)
    (KR : DerivedCategory (ModuleCat.{u} R))
    (hKR : Dualizing.IsNormalizedDualizingComplex.{u, u} KR) :
    Nonempty (R ⊗[A] (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj KA ≃ₗ[R]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-2)).obj KR) := by
  obtain ⟨hK', -, hiso, -⟩ :=
    MMP.canonicalModule_derivedExtensionScalars_iso_of_flat.{u, u, u} hmax KA hKA
  have := hiso 2 (by rw [hA]; rfl)
  obtain ⟨e2⟩ := Dualizing.IsNormalizedDualizingComplex.nonempty_iso hK' hKR
  let e1 := asIso ((MMP.flatHomologyTensorComparison.{u, u, u} (algebraMap A R)
    (RingHom.flat_algebraMap_iff.mpr inferInstance) (-((2 : ℕ) : ℤ))).app KA)
  let e3 := e1 ≪≫ (@DerivedCategory.homologyFunctor (ModuleCat.{u} R) _ _
    (HasDerivedCategory.standard _) (-((2 : ℕ) : ℤ))).mapIso e2
  let i1 := (ModuleCat.extendScalars (algebraMap A R)).mapIso (moduleHomologyLsIsoStd KA (-2))
  let i := i1 ≪≫ e3 ≪≫ (moduleHomologyLsIsoStd KR (-2)).symm
  exact ⟨(extendScalarsEquiv _).symm ≪≫ₗ i.toLinearEquiv⟩

/-! ### The two maps `δ_n` and their cokernels -/

/-- Lengths of finite length modules are preserved by a flat local map of local rings whose
closed fibre is the residue field. -/
private theorem length_baseChange_of_map_maximalIdeal {C D Q : Type*} [CommRing C] [CommRing D]
    [IsLocalRing C] [IsLocalRing D] [Algebra C D] [Module.Flat C D]
    (h : (IsLocalRing.maximalIdeal C).map (algebraMap C D) = IsLocalRing.maximalIdeal D)
    [AddCommGroup Q] [Module C Q] :
    Module.length D (D ⊗[C] Q) = Module.length C Q := by
  have : IsLocalHom (algebraMap C D) := ((IsLocalRing.local_hom_TFAE _).out 3 1).mp h.le
  have h1 : Module.length D (D ⧸ IsLocalRing.maximalIdeal D) = 1 :=
    Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal D).out)
  rw [IsLocalRing.length_baseChange, h, h1, mul_one]

/-- The maximal ideal of `A ⧸ I` extends to that of `R ⧸ I R` when `𝔪_A R = 𝔪_R`. -/
private theorem map_maximalIdeal_quotient {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
    [IsLocalRing A] [IsLocalRing R]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A R) = IsLocalRing.maximalIdeal R)
    (I : Ideal A) [IsLocalRing (A ⧸ I)] [IsLocalRing (R ⧸ I.map (algebraMap A R))] :
    (IsLocalRing.maximalIdeal (A ⧸ I)).map (algebraMap (A ⧸ I) (R ⧸ I.map (algebraMap A R))) =
      IsLocalRing.maximalIdeal (R ⧸ I.map (algebraMap A R)) := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective,
    ← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (I.map (algebraMap A R)))
      Ideal.Quotient.mk_surjective, ← hmax, Ideal.map_map, Ideal.map_map]
  rfl

/-- Over a two-dimensional Noetherian normal local domain `B` with a prime `J` such that `B ⧸ J`
is a discrete valuation ring, the map `δ_n : ⨂ⁿ ω_{B/J} → (B ⧸ J) ⊗ (⨂ⁿ M)^{∨∨}` induced by the
products, `M = Hom_B(J, ω_B)`, is injective with cokernel of finite length. -/
private theorem injective_and_length_lt_top {B : Type u} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [IsLocalRing B] [IsIntegrallyClosed B] (hB : ringKrullDim B = 2)
    (J : Ideal B) [IsDomain (B ⧸ J)] [IsDiscreteValuationRing (B ⧸ J)]
    (K : DerivedCategory (ModuleCat.{u} B)) (hK : Dualizing.IsNormalizedDualizingComplex.{u, u} K)
    {n : ℕ} (W : Type u) [AddCommGroup W] [Module (B ⧸ J) W] [Module B W]
    [IsScalarTower B (B ⧸ J) W]
    (ρ : (J →ₗ[B] (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-2)).obj K) →ₗ[B] W)
    (hρ : Function.Surjective ρ)
    (hρex : Function.Exact
      (LinearMap.lcomp B _ J.subtype ∘ₗ
        (LinearMap.ringLmapEquivSelf B B
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-2)).obj K)).symm.toLinearMap) ρ)
    (δ : TensorPower (B ⧸ J) n W →ₗ[B ⧸ J] (B ⧸ J) ⊗[B] Module.Dual B (Module.Dual B
      (TensorPower B n (J →ₗ[B] (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-2)).obj K))))
    (hδ : ∀ m : Fin n → (J →ₗ[B] (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-2)).obj K),
      δ (PiTensorProduct.tprod (B ⧸ J) fun i => ρ (m i)) =
        (1 : B ⧸ J) ⊗ₜ[B] Module.Dual.eval B _ (PiTensorProduct.tprod B m)) :
    Function.Injective δ ∧ Module.length (B ⧸ J) (_ ⧸ LinearMap.range δ) < ⊤ := by
  have : J.IsPrime := (Ideal.Quotient.isDomain_iff_prime J).mp inferInstance
  obtain ⟨hJ0, hJ⟩ := ne_bot_and_height_eq_one hB J
  have := isDiscreteValuationRing_localization_of_height_eq_one B J hJ
  -- the canonical module, read in the standard model of `D(B)`
  let ωs := (@DerivedCategory.homologyFunctor (ModuleCat.{u} B) _ _
    (HasDerivedCategory.standard _) (-2)).obj K
  let eω := (moduleHomologyLsIsoStd K (-2)).toLinearEquiv
  have hdual : Stacks.Duality.IsDualizingRingModule B ωs :=
    isDualizingRingModule_canonicalModule hB K hK
  have : Module.Finite B ωs := hdual.1
  have : Module.IsTorsionFree B ωs := Stacks.Duality.IsDualizingRingModule.isTorsionFree hdual
  obtain ⟨Ω, hΩ, ⟨eΩ⟩⟩ := Dualizing.exists_linearEquiv_ideal_of_isDualizingRingModule hdual
  have : Nontrivial ωs := by
    have : Nontrivial Ω := Submodule.nontrivial_iff_ne_bot.mpr hΩ
    exact eΩ.toEquiv.nontrivial
  have hdepth2 : 2 ≤ Module.depth B (maximalIdeal B) ωs := by
    have := Dualizing.min_two_le_depth_canonicalModule 2 K hK (by rw [hB]; rfl)
    simpa using this
  -- transport to the canonical module of the statement
  have := finite_canonicalModule K hK
  have : Module.IsTorsionFree B ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-2)).obj K) :=
    ⟨fun r hr x y hxy => eω.injective (Module.IsTorsionFree.isSMulRegular hr
      (show r • eω x = r • eω y by rw [← map_smul, ← map_smul]; exact congrArg eω hxy))⟩
  have hdepth : ∀ x ∈ maximalIdeal B, x ≠ 0 →
      ∀ e : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-2)).obj K,
      (∀ b ∈ maximalIdeal B, ∃ e', b • e = x • e') → ∃ e', e = x • e' := by
    intro x hx hx0 e he
    obtain ⟨e', he'⟩ := exists_eq_smul_of_two_le_depth hdepth2 x hx
      (Module.IsTorsionFree.isSMulRegular (isRegular_iff_ne_zero.mpr hx0)) (eω e) (by
        intro b hb
        obtain ⟨e'', he''⟩ := he b hb
        exact ⟨eω e'', by rw [← map_smul, he'', map_smul]⟩)
    refine ⟨eω.symm e', eω.injective ?_⟩
    rw [map_smul, LinearEquiv.apply_symm_apply, he']
  have : Module.IsTorsionFree (B ⧸ J) W := isTorsionFree_of_exact J hdepth W ρ hρ hρex
  have : Module.Finite B W := Module.Finite.of_surjective ρ hρ
  have : Module.Finite (B ⧸ J) W := Module.Finite.of_restrictScalars_finite B _ W
  have : Module.Free (B ⧸ J) W := Module.free_of_finite_type_torsion_free'
  exact injective_and_length_lt_top_of_linearEquiv J hJ0 Ω hΩ (eω ≪≫ₗ eΩ) W ρ hρ hρex n δ hδ

/-- The flat comparison: for a flat map `A → R` of Noetherian rings, an ideal `I ⊆ A` and an
identification `R ⊗_A ω_A ≅ ω_R`, the cokernel of `δ_n` formed over `R` is the base change along
`A ⧸ I → R ⧸ I R` of the cokernel of `δ_n` formed over `A`. -/
private theorem nonempty_baseChange_quotient_range_equiv
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] [IsNoetherianRing A] [Module.Flat A R]
    (I : Ideal A) {ωA ωR : Type*} [AddCommGroup ωA] [Module A ωA] [Module.Finite A ωA]
    [AddCommGroup ωR] [Module R ωR] (eω : R ⊗[A] ωA ≃ₗ[R] ωR) {n : ℕ}
    {W : Type*} [AddCommGroup W] [Module (A ⧸ I) W] [Module A W] [IsScalarTower A (A ⧸ I) W]
    (ρ : (I →ₗ[A] ωA) →ₗ[A] W) (hρ : Function.Surjective ρ)
    {WR : Type*} [AddCommGroup WR] [Module (R ⧸ I.map (algebraMap A R)) WR] [Module R WR]
    [IsScalarTower R (R ⧸ I.map (algebraMap A R)) WR]
    (ρR : (I.map (algebraMap A R) →ₗ[R] ωR) →ₗ[R] WR) (hρR : Function.Surjective ρR)
    (δ : TensorPower (A ⧸ I) n W →ₗ[A ⧸ I]
      (A ⧸ I) ⊗[A] Module.Dual A (Module.Dual A (TensorPower A n (I →ₗ[A] ωA))))
    (hδ : ∀ m : Fin n → (I →ₗ[A] ωA), δ (PiTensorProduct.tprod (A ⧸ I) fun i => ρ (m i)) =
      (1 : A ⧸ I) ⊗ₜ[A] Module.Dual.eval A _ (PiTensorProduct.tprod A m))
    (δR : TensorPower (R ⧸ I.map (algebraMap A R)) n WR →ₗ[R ⧸ I.map (algebraMap A R)]
      (R ⧸ I.map (algebraMap A R)) ⊗[R]
        Module.Dual R (Module.Dual R (TensorPower R n (I.map (algebraMap A R) →ₗ[R] ωR))))
    (hδR : ∀ m : Fin n → (I.map (algebraMap A R) →ₗ[R] ωR),
      δR (PiTensorProduct.tprod (R ⧸ I.map (algebraMap A R)) fun i => ρR (m i)) =
        (1 : R ⧸ I.map (algebraMap A R)) ⊗ₜ[R] Module.Dual.eval R _ (PiTensorProduct.tprod R m)) :
    Nonempty ((R ⧸ I.map (algebraMap A R)) ⊗[A ⧸ I] (_ ⧸ LinearMap.range δ)
      ≃ₗ[R ⧸ I.map (algebraMap A R)] (_ ⧸ LinearMap.range δR)) := by
  have := Module.finitePresentation_of_finite A I
  obtain ⟨eI⟩ := nonempty_tensor_ideal_equiv_map (D := R) I
  obtain ⟨e, -⟩ := exists_tensorPower_baseChange A R (I →ₗ[A] ωA) n
  let E := e ≪≫ₗ PiTensorProduct.congr fun _ =>
    (Module.FinitePresentation.isBaseChange_map A I ωA R).equiv ≪≫ₗ LinearEquiv.arrowCongr eI eω
  obtain ⟨Φ, hΦ⟩ := exists_doubleDual_baseChange A R _ _ E
  exact nonempty_quotient_range_equiv_of_baseChange (Module.Dual.eval A _) (Module.Dual.eval R _)
    E Φ hΦ ρ hρ δ hδ ρR hρR δR hδR

/-- Let `A → R` be a flat local map of two-dimensional Noetherian normal local domains with
`𝔪_A R = 𝔪_R`, and let `I ⊆ A` be a height-one prime with `A ⧸ I` and `R ⧸ I R` discrete
valuation rings. Let `ω_A`, `ω_R` be the canonical modules `H^{-2}` of normalized dualizing
complexes, `M = Hom_A(I, ω_A)`, and suppose `(⨂ⁿ M)^{∨∨}` is free for some `n ≥ 1`. Let
`ρ : M → W` and `ρR : Hom_R(I R, ω_R) → WR` be the canonical adjunctions onto the canonical
modules of `A ⧸ I` and `R ⧸ I R`, that is, surjections whose kernels are the images of the
restrictions `x ↦ (a ↦ a • x)`. Let `δ` and `δR` be the maps induced by the products into the
reflexive powers. Then both are injective, and their cokernels have the same finite length. -/
@[mmp "lem_mmp_foundation_regular_branch_different_flat_comparison"]
public theorem length_cokernel_eq_of_flat_of_isDiscreteValuationRing
    {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
    [IsDomain A] [IsDomain R] [IsNoetherianRing A] [IsNoetherianRing R]
    [IsLocalRing A] [IsLocalRing R] [IsIntegrallyClosed A] [IsIntegrallyClosed R]
    [Module.Flat A R] [IsLocalHom (algebraMap A R)]
    (hA : ringKrullDim A = 2) (hR : ringKrullDim R = 2)
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A R) = IsLocalRing.maximalIdeal R)
    (I : Ideal A) [I.IsPrime] (hI : I.height = 1)
    [IsDomain (A ⧸ I)] [IsDiscreteValuationRing (A ⧸ I)]
    [IsDomain (R ⧸ I.map (algebraMap A R))]
    [IsDiscreteValuationRing (R ⧸ I.map (algebraMap A R))]
    (KA : DerivedCategory (ModuleCat.{u} A))
    (hKA : Dualizing.IsNormalizedDualizingComplex.{u, u} KA)
    (KR : DerivedCategory (ModuleCat.{u} R))
    (hKR : Dualizing.IsNormalizedDualizingComplex.{u, u} KR)
    (n : ℕ) (hn : 1 ≤ n)
    (hfree : Module.Free A (Module.Dual A (Module.Dual A
      (TensorPower A n (I →ₗ[A] (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj KA)))))
    -- the canonical adjunction onto the canonical module `W` of `A ⧸ I`
    (W : Type u) [AddCommGroup W] [Module (A ⧸ I) W] [Module A W] [IsScalarTower A (A ⧸ I) W]
    (ρ : (I →ₗ[A] (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj KA) →ₗ[A] W)
    (hρ : Function.Surjective ρ)
    (hρex : Function.Exact
      (LinearMap.lcomp A _ I.subtype ∘ₗ
        (LinearMap.ringLmapEquivSelf A A
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj KA)).symm.toLinearMap) ρ)
    -- the canonical adjunction onto the canonical module `WR` of `R ⧸ I R`
    (WR : Type u) [AddCommGroup WR] [Module (R ⧸ I.map (algebraMap A R)) WR] [Module R WR]
    [IsScalarTower R (R ⧸ I.map (algebraMap A R)) WR]
    (ρR : (I.map (algebraMap A R) →ₗ[R]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-2)).obj KR) →ₗ[R] WR)
    (hρR : Function.Surjective ρR)
    (hρRex : Function.Exact
      (LinearMap.lcomp R _ (I.map (algebraMap A R)).subtype ∘ₗ
        (LinearMap.ringLmapEquivSelf R R
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-2)).obj KR)).symm.toLinearMap) ρR)
    -- the maps `δ_n` induced by the products into the reflexive powers
    (δ : TensorPower (A ⧸ I) n W →ₗ[A ⧸ I] (A ⧸ I) ⊗[A] Module.Dual A (Module.Dual A
      (TensorPower A n (I →ₗ[A] (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj KA))))
    (hδ : ∀ m : Fin n → (I →ₗ[A] (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj KA),
      δ (PiTensorProduct.tprod (A ⧸ I) fun i => ρ (m i)) =
        (1 : A ⧸ I) ⊗ₜ[A] Module.Dual.eval A _ (PiTensorProduct.tprod A m))
    (δR : TensorPower (R ⧸ I.map (algebraMap A R)) n WR →ₗ[R ⧸ I.map (algebraMap A R)]
      (R ⧸ I.map (algebraMap A R)) ⊗[R] Module.Dual R (Module.Dual R
        (TensorPower R n (I.map (algebraMap A R) →ₗ[R]
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-2)).obj KR))))
    (hδR : ∀ m : Fin n → (I.map (algebraMap A R) →ₗ[R]
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-2)).obj KR),
      δR (PiTensorProduct.tprod (R ⧸ I.map (algebraMap A R)) fun i => ρR (m i)) =
        (1 : R ⧸ I.map (algebraMap A R)) ⊗ₜ[R] Module.Dual.eval R _ (PiTensorProduct.tprod R m)) :
    Function.Injective δ ∧ Function.Injective δR ∧
      Module.length (A ⧸ I) (_ ⧸ LinearMap.range δ) < ⊤ ∧
      Module.length (R ⧸ I.map (algebraMap A R)) (_ ⧸ LinearMap.range δR) =
        Module.length (A ⧸ I) (_ ⧸ LinearMap.range δ) := by
  obtain ⟨hinj, hlen⟩ := injective_and_length_lt_top hA I KA hKA W ρ hρ hρex δ hδ
  obtain ⟨hinjR, -⟩ :=
    injective_and_length_lt_top hR (I.map (algebraMap A R)) KR hKR WR ρR hρR hρRex δR hδR
  refine ⟨hinj, hinjR, hlen, ?_⟩
  obtain ⟨eω⟩ := nonempty_canonicalModule_baseChange hA hmax KA hKA KR hKR
  have := finite_canonicalModule KA hKA
  obtain ⟨e⟩ := nonempty_baseChange_quotient_range_equiv I eω ρ hρ ρR hρR δ hδ δR hδR
  have : Module.Flat (A ⧸ I) (R ⧸ I.map (algebraMap A R)) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I).toLinearEquiv
  rw [← e.length_eq, length_baseChange_of_map_maximalIdeal (map_maximalIdeal_quotient hmax I)]

end MMP.Flips

/-! ## Regular surface models over the completed strict henselization

The projection `W_R ⟶ W` is dominant because it is a base change of the surjective morphism
`Spec R ⟶ Spec A` of the faithfully flat map `A → R`. The dimension of `W_R` is that of `Spec R`
by birationality, and `dim R = dim A` because `A → H → R` are flat local maps with trivial
closed fibres.

The morphism `q` is an isomorphism over a dense open `V ⊆ Spec A` (Stacks 0BAJ), so `W_R ⟶ Spec R`
is an isomorphism over the nonempty open `g⁻¹(V)`. Its preimage `O ⊆ W_R` is therefore
irreducible, and it is dense: generalizations lift along the flat projection `W_R ⟶ W`, and the
generic point of `W` lies over `V`. Hence `W_R` is irreducible, and integral because it is
regular. The same open exhibits `W_R ⟶ Spec R` as birational.

At a point `ξ` of `W_R` minimal over the generic point `η` of an exceptional curve, the stalk map
`𝒪_{W,η} → 𝒪_{W_R,ξ}` is a localization of the regular map `C → R ⊗_A C` on an affine chart,
hence regular. Its closed fibre is therefore a regular ring, and it has a single prime by
minimality of `ξ`, so it is a field: the maximal ideal of `𝒪_{W,η}` generates that of
`𝒪_{W_R,ξ}`.
-/

namespace MMP.Foundations

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped ChangeOfRings TensorProduct

/-- A flat local homomorphism of Noetherian local rings whose closed fibre is the residue field
of the target preserves the Krull dimension. -/
private theorem ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Module.Flat A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)]
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim B = ringKrullDim A := by
  have : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal A) (maximalIdeal B)
  rw [hmax, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h]

/-- The completed strict henselization of `A` has the same Krull dimension as `A`. -/
private theorem ringKrullDim_adicCompletion_strictHenselization
    (k : Type u) [Field k] (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A κsep H] :
    ringKrullDim (AdicCompletion (maximalIdeal H) H) = ringKrullDim A := by
  have : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing k A
  obtain ⟨⟨_, -, -⟩, ⟨_, hAH, hmAH⟩, _, ⟨_, -, -⟩, ⟨_, hHR, hmHR⟩, -⟩ :=
    MMP.Foundations.isNoetherianRing_strictHenselization_adicCompletion k A κsep H
  have := hAH.toFlat
  have := hHR.toFlat
  rw [ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq hmHR,
    ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq hmAH]

/-- The map `Spec R ⟶ Spec A` is flat and surjective, because `A → H → R` is faithfully flat. -/
private theorem flat_and_surjective_specMap_adicCompletion
    (k : Type u) [Field k] (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A κsep H] :
    Flat (Spec.map (CommRingCat.ofHom
        ((algebraMap H (AdicCompletion (maximalIdeal H) H)).comp (algebraMap A H)))) ∧
      Surjective (Spec.map (CommRingCat.ofHom
        ((algebraMap H (AdicCompletion (maximalIdeal H) H)).comp (algebraMap A H)))) := by
  obtain ⟨-, ⟨-, hAH, -⟩, _, -, ⟨-, hHR, -⟩, -⟩ :=
    MMP.Foundations.isNoetherianRing_strictHenselization_adicCompletion k A κsep H
  exact (flat_and_surjective_SpecMap_iff _).mpr <|
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hAH).comp
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hHR)

/-- The projection `W_R ⟶ W` is dominant. -/
private theorem isDominant_pullback_fst
    (k : Type u) [Field k] (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A κsep H]
    (W : Scheme.{u}) (q : W ⟶ Spec (.of A)) :
    let R := AdicCompletion (maximalIdeal H) H
    let g : Spec (.of R) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom ((algebraMap H R).comp (algebraMap A H)))
    let WR : Scheme.{u} := pullback q g
    let p : WR ⟶ W := pullback.fst q g
    IsDominant p := by
  intro R g WR p
  have : Surjective g := (flat_and_surjective_specMap_adicCompletion k A κsep H).2
  have : Surjective (pullback.fst q g) := inferInstance
  exact inferInstanceAs (IsDominant (pullback.fst q g))

/-- If `q : X ⟶ S` is an isomorphism over an open `V` of `S`, then its base change along
`g : Y ⟶ S` is an isomorphism over `g ⁻¹ᵁ V`. -/
private theorem isIso_morphismRestrict_pullback_snd {X Y S : Scheme.{u}}
    (q : X ⟶ S) (g : Y ⟶ S) (V : S.Opens) [IsIso (q ∣_ V)] :
    IsIso (pullback.snd q g ∣_ (g ⁻¹ᵁ V)) := by
  let UT : Y.Opens := g ⁻¹ᵁ V
  have hsq := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback q g)
    (US := V) (UT := UT) (UX := q ⁻¹ᵁ V) le_rfl le_rfl
    (UY := pullback.fst q g ⁻¹ᵁ (q ⁻¹ᵁ V) ⊓ pullback.snd q g ⁻¹ᵁ UT) rfl
  have : IsIso (q.resLE V (q ⁻¹ᵁ V) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  have hiso := hsq.isIso_snd_of_isIso
  have hUY : pullback.fst q g ⁻¹ᵁ (q ⁻¹ᵁ V) ⊓ pullback.snd q g ⁻¹ᵁ UT =
      pullback.snd q g ⁻¹ᵁ UT := by
    refine inf_eq_right.mpr ?_
    intro x hx
    change (pullback.fst q g ≫ q) x ∈ V
    rw [pullback.condition]
    exact hx
  have key : ∀ (W' : (pullback q g).Opens) (_ : W' = pullback.snd q g ⁻¹ᵁ UT)
      (h' : W' ≤ pullback.snd q g ⁻¹ᵁ UT),
      IsIso ((pullback.snd q g).resLE UT W' h') → IsIso (pullback.snd q g ∣_ UT) := by
    rintro _ rfl _ h
    rwa [← Scheme.Hom.resLE_eq_morphismRestrict]
  exact key _ hUY _ hiso

/-- With `q`, `g`, `V` as above, `Y` irreducible, `g` flat and `g ⁻¹ᵁ V` nonempty, the fibre
product `X ×_S Y` is irreducible as soon as `X` is: the open `snd ⁻¹ᵁ (g ⁻¹ᵁ V)` is irreducible,
being isomorphic to `g ⁻¹ᵁ V`, and it is dense, because generalizations lift along the flat
projection to `X` and the generic point of `X` lies over `V`. -/
private theorem irreducibleSpace_pullback_of_isIso_morphismRestrict {X Y S : Scheme.{u}}
    (q : X ⟶ S) (g : Y ⟶ S) (V : S.Opens) [IsIso (q ∣_ V)] [Flat g]
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (hV : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty) : IrreducibleSpace ↥(pullback q g) := by
  let UT : Y.Opens := g ⁻¹ᵁ V
  let O : (pullback q g).Opens := pullback.snd q g ⁻¹ᵁ UT
  have := isIso_morphismRestrict_pullback_snd q g V
  obtain ⟨y, hy⟩ := hV
  have hUT : IsIrreducible (UT : Set Y) :=
    ⟨⟨y, hy⟩, (IrreducibleSpace.isIrreducible_univ Y).2.open_subset UT.isOpen (Set.subset_univ _)⟩
  have : IrreducibleSpace UT.toScheme := Subtype.irreducibleSpace hUT
  let φ : UT.toScheme ⟶ pullback q g := inv (pullback.snd q g ∣_ UT) ≫ O.ι
  have hφ : φ '' Set.univ = (O : Set ↥(pullback q g)) := by
    apply subset_antisymm
    · rintro _ ⟨u, -, rfl⟩
      exact ((inv (pullback.snd q g ∣_ UT)) u).2
    · intro w hw
      let w' : O.toScheme := ⟨w, hw⟩
      refine ⟨(pullback.snd q g ∣_ UT) w', trivial, ?_⟩
      change (inv (pullback.snd q g ∣_ UT) ≫ O.ι) ((pullback.snd q g ∣_ UT) w') = w
      rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (pullback.snd q g ∣_ UT),
        IsIso.hom_inv_id]
      rfl
  have hO : IsIrreducible (O : Set ↥(pullback q g)) := by
    rw [← hφ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ φ.continuous.continuousOn
  -- The generic point of `X` lies in `q ⁻¹ᵁ V`.
  have hx : genericPoint X ∈ q ⁻¹ᵁ V := by
    let x : (q ⁻¹ᵁ V).toScheme := inv (q ∣_ V) ⟨g y, hy⟩
    exact ((genericPoint_spec X).mem_open_set_iff (q ⁻¹ᵁ V).isOpen).mpr ⟨x.1, trivial, x.2⟩
  have hdense : closure (O : Set ↥(pullback q g)) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨z', hz', hz'p⟩ := Flat.generalizingMap (pullback.fst q g)
      (genericPoint_specializes (pullback.fst q g z))
    have : z' ∈ O := by
      change (pullback.snd q g ≫ g) z' ∈ V
      rw [← pullback.condition, Scheme.Hom.comp_apply, hz'p]
      exact hx
    exact closure_mono (Set.singleton_subset_iff.mpr this) (specializes_iff_mem_closure.mp hz')
  have h := hO.closure
  rw [hdense] at h
  exact (irreducibleSpace_def _).mpr h

/-- The map `g : Spec R ⟶ Spec A` is flat, and `q` is an isomorphism over an open of `Spec A`
whose preimage in `Spec R` is nonempty. -/
private theorem flat_and_exists_isIso_morphismRestrict
    (k : Type u) [Field k] [CharZero k] (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    (hA : ringKrullDim A = 2)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A κsep H]
    (W : Scheme.{u}) [IsIntegral W] (q : W ⟶ Spec (.of A)) [IsProper q] (hq : IsBirational q)
    (hW : IsRegular W) :
    let R := AdicCompletion (maximalIdeal H) H
    let g : Spec (.of R) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom ((algebraMap H R).comp (algebraMap A H)))
    Flat g ∧ ∃ V : (Spec (.of A)).Opens, IsIso (q ∣_ V) ∧ ((g ⁻¹ᵁ V : (Spec (.of R)).Opens) :
      Set (Spec (.of R))).Nonempty := by
  intro R g
  have : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing k A
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian W := ⟨⟩
  have : Finite (irreducibleComponents W) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := W)).to_subtype
  have : Finite (irreducibleComponents (Spec (.of A))) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
      (α := Spec (.of A))).to_subtype
  obtain ⟨V, hVd, hVi⟩ := exists_dense_open_isIso_morphismRestrict_of_isBirational q hq
    (Or.inl inferInstance) (Or.inl ⟨inferInstance, inferInstance⟩)
  obtain ⟨hgf, hg⟩ : Flat g ∧ Surjective g := flat_and_surjective_specMap_adicCompletion k A κsep H
  obtain ⟨v, hv⟩ := hVd.nonempty
  obtain ⟨y, hy⟩ := hg.surj v
  exact ⟨hgf, V, hVi, y, by simpa [hy] using hv⟩

/-- The map `A → R` to the completed strict henselization is a regular ring map: `A → H` is
ind-étale, hence regular, and `H → R` is regular because `H` is a G-ring. -/
private theorem isRegularRingHom_strictHenselization_adicCompletion
    (k : Type u) [Field k] (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A κsep H] :
    IsRegularRingHom ((algebraMap H (AdicCompletion (maximalIdeal H) H)).comp
      (algebraMap A H)) := by
  have : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing k A
  obtain ⟨⟨_, -, -⟩, -, _, ⟨_, -, -⟩, -, -⟩ :=
    MMP.Foundations.isNoetherianRing_strictHenselization_adicCompletion k A κsep H
  have hGA : IsGRing A := isGRing_of_essFiniteType (isGRing_basic_examples.{_, 0}.1 k)
  obtain ⟨Ah, _, _, _, _⟩ := IsLocalRing.exists_isHenselization_residueField A
  have hGH : IsGRing H := (isGRing_henselization_and_strictHenselization A Ah H κsep hGA).2
  have hHR := (isGRing_iff_isRegularRingHom_completion H).mp hGH
  have hAH : IsRegularRingHom (algebraMap A H) := by
    obtain ⟨J, _, _, pres, hpres⟩ :=
      IsHenselization.ind_etale_of_universe_le.{u, u, u} (R := A) κsep (Rh := H)
    obtain ⟨ι, _, _, _, F, _⟩ := IsFiltered.exists_directed J
    let pres' := pres.reindex F
    exact isRegularRingHom_of_filteredColimit_smooth pres'.diag pres'.cocone pres'.isColimit
      (fun i => by
        have : Algebra.Etale A (pres.diag.obj (F.obj i)) := hpres (F.obj i)
        change Algebra.Smooth A (pres.diag.obj (F.obj i))
        infer_instance)
      (fun p _ => p.isNoetherianRing_fiber H)
  exact isRegularRingHom_comp _ _ hAH hHR (fun p _ => by
    let : Algebra A (AdicCompletion (maximalIdeal H) H) :=
      ((algebraMap H (AdicCompletion (maximalIdeal H) H)).comp (algebraMap A H)).toAlgebra
    exact p.isNoetherianRing_fiber _)

/-- If `A → Λ` is a regular ring map with `Λ` Noetherian and `W` is a regular scheme locally of
finite type over `Spec A`, then `W ×_{Spec A} Spec Λ` is regular: on the chart over an affine
open `Spec C` of `W` it is `Spec (Λ ⊗_A C)`, and `C → Λ ⊗_A C` is regular. -/
private theorem isRegular_pullback_of_isRegularRingHom {A Λ : Type u} [CommRing A] [CommRing Λ]
    [Algebra A Λ] [IsNoetherianRing Λ]
    (hφ : IsRegularRingHom (algebraMap A Λ)) {W : Scheme.{u}} (q : W ⟶ Spec (.of A))
    [LocallyOfFiniteType q] (hW : IsRegular W) :
    IsRegular (pullback q (Spec.map (CommRingCat.ofHom (algebraMap A Λ)))) := by
  let g : Spec (.of Λ) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Λ))
  let p := pullback.fst q g
  refine ((isRegular_tfae_cover (pullback q g)).out 1 4).mpr ?_
  refine ⟨W.affineOpens, fun U => p ⁻¹ᵁ (U : W.Opens), ?_, fun U => ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top W, Scheme.Hom.preimage_top]
  let C := Γ(W, (U : W.Opens))
  let e : Spec (.of C) ≅ (U : W.Opens).toScheme := U.2.isoSpec.symm
  let m : Spec (.of C) ⟶ Spec (.of A) := e.hom ≫ (U : W.Opens).ι ≫ q
  letI : Algebra A C := (Spec.preimage m).hom.toAlgebra
  have hm : Spec.map (CommRingCat.ofHom (algebraMap A C)) = m := Spec.map_preimage m
  have : Algebra.FiniteType A C := by
    have : LocallyOfFiniteType m := inferInstance
    rw [← hm, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
    exact this
  have : IsRegularRing C := ((isRegular_tfae_cover W).out 1 2 rfl rfl).mp hW U
  have : IsNoetherianRing (Λ ⊗[A] C) := Algebra.FiniteType.isNoetherianRing Λ _
  have : IsRegularRing (Λ ⊗[A] C) :=
    isRegularRing_of_isRegularRingHom _ (isRegularRingHom_baseChange (R' := C) hφ)
  let iso : Spec (.of (Λ ⊗[A] C)) ≅ (p ⁻¹ᵁ (U : W.Opens)).toScheme :=
    (pullbackSpecIso A Λ C).symm ≪≫ pullbackSymmetry _ _ ≪≫ pullback.congrHom hm rfl ≪≫
      asIso (pullback.map m g ((U : W.Opens).ι ≫ q) g e.hom (𝟙 _) (𝟙 _)
        (by simp [m]) (by simp)) ≪≫
      (pullbackRightPullbackFstIso q g (U : W.Opens).ι).symm ≪≫ pullbackSymmetry _ _ ≪≫
      pullbackRestrictIsoRestrict p (U : W.Opens)
  exact IsRegular.of_iso iso.symm ((isRegular_spec_iff _).mpr this)

/-- The base change `W_R` is regular: on affine charts `W_R` is the base change of a chart of `W`
along the regular ring map `A → R`, and regularity ascends along regular ring maps. -/
private theorem isRegular_pullback
    (k : Type u) [Field k] (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A κsep H]
    (W : Scheme.{u}) (q : W ⟶ Spec (.of A)) [LocallyOfFiniteType q] (hW : IsRegular W) :
    let R := AdicCompletion (maximalIdeal H) H
    let g : Spec (.of R) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom ((algebraMap H R).comp (algebraMap A H)))
    let WR : Scheme.{u} := pullback q g
    IsRegular WR := by
  intro R g WR
  obtain ⟨-, -, _, ⟨_, -, -⟩, -, -⟩ :=
    MMP.Foundations.isNoetherianRing_strictHenselization_adicCompletion k A κsep H
  letI : Algebra A R := ((algebraMap H R).comp (algebraMap A H)).toAlgebra
  exact isRegular_pullback_of_isRegularRingHom
    (isRegularRingHom_strictHenselization_adicCompletion k A κsep H) q hW

/-- If `q : X ⟶ S` is an isomorphism over an open `V` of `S` whose preimage under `g : Y ⟶ S` is
nonempty, and `X ×_S Y` and `Y` are irreducible, then `pullback.snd q g` is birational. -/
private theorem isBirational_pullback_snd_of_isIso_morphismRestrict {X Y S : Scheme.{u}}
    (q : X ⟶ S) (g : Y ⟶ S) (V : S.Opens) [IsIso (q ∣_ V)]
    [IrreducibleSpace ↥(pullback q g)] [IrreducibleSpace Y]
    (hV : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty) : IsBirational (pullback.snd q g) := by
  let UT : Y.Opens := g ⁻¹ᵁ V
  have hres : IsIso (pullback.snd q g ∣_ UT) := isIso_morphismRestrict_pullback_snd q g V
  obtain ⟨y, hy⟩ := hV
  let x : (pullback.snd q g ⁻¹ᵁ UT).toScheme := inv (pullback.snd q g ∣_ UT) ⟨y, hy⟩
  refine isBirational_of_isIso_morphismRestrict _ UT hres ?_ ?_
  · intro z hz
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hz
    subst hz
    exact ((genericPoint_spec ↥(pullback q g)).mem_open_set_iff
      (pullback.snd q g ⁻¹ᵁ UT).isOpen).mpr ⟨x.1, trivial, x.2⟩
  · intro z hz
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hz
    subst hz
    exact ((genericPoint_spec Y).mem_open_set_iff UT.isOpen).mpr ⟨y, trivial, hy⟩

/-- The global part: `W_R` is integral, Noetherian, regular of dimension two and birational
over `Spec R`. -/
private theorem isIntegral_isRegular_pullback
    (k : Type u) [Field k] [CharZero k] (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    (hA : ringKrullDim A = 2)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A κsep H]
    (W : Scheme.{u}) [IsIntegral W] (q : W ⟶ Spec (.of A)) [IsProper q] (hq : IsBirational q)
    (hW : IsRegular W) :
    let R := AdicCompletion (maximalIdeal H) H
    let g : Spec (.of R) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom ((algebraMap H R).comp (algebraMap A H)))
    let WR : Scheme.{u} := pullback q g
    ∃ (_ : IsIntegral WR) (_ : IsLocallyNoetherian WR),
      IsNoetherian WR ∧ IsRegular WR ∧ topologicalKrullDim WR = 2 ∧
        IsBirational (pullback.snd q g) := by
  intro R g WR
  have : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing k A
  obtain ⟨-, -, _, ⟨_, _, -⟩, -, -⟩ :=
    MMP.Foundations.isNoetherianRing_strictHenselization_adicCompletion k A κsep H
  have : IsIntegral (Spec (.of R)) := inferInstanceAs (IsIntegral (Spec (.of R)))
  have : IsLocallyNoetherian WR := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd q g)
  have : CompactSpace WR := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q g)
  obtain ⟨hgf, V, hVi, hne⟩ := flat_and_exists_isIso_morphismRestrict k A hA κsep H W q hq hW
  have := hgf
  have : IrreducibleSpace WR := irreducibleSpace_pullback_of_isIso_morphismRestrict q g V hne
  have : IsIntegral WR := isIntegral_of_isRegular (isRegular_pullback k A κsep H W q hW)
  have hbir := isBirational_pullback_snd_of_isIso_morphismRestrict q g V hne
  refine ⟨inferInstance, inferInstance, ⟨⟩,
    isRegular_pullback k A κsep H W q hW, ?_, hbir⟩
  rw [IsBirational.topologicalKrullDim_eq_of_isClosedMap hbir (pullback.snd q g).isClosedMap]
  change topologicalKrullDim (PrimeSpectrum R) = 2
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ringKrullDim_adicCompletion_strictHenselization k A κsep H, hA]

/-- If `p` is flat, `ξ` lies over the closure of `η` and is minimal among such points, then `ξ`
lies over `η`: a generalization of `ξ` over `η` exists because generalizations lift along `p`. -/
private theorem base_eq_of_forall_specializes_eq {X Y : Scheme.{u}} (p : Y ⟶ X) [Flat p]
    {η : X} {ξ : Y} (hξ : p.base ξ ∈ closure {η})
    (hmin : ∀ ζ : Y, p.base ζ ∈ closure {η} → ζ ⤳ ξ → ζ = ξ) : p.base ξ = η := by
  obtain ⟨ζ, hζ, hζp⟩ := Flat.generalizingMap p (specializes_iff_mem_closure.mpr hξ)
  have hζη : p.base ζ ∈ closure {η} := by
    rw [hζp]; exact subset_closure rfl
  rw [← hζp, hmin ζ hζη hζ]

/-- The base change of `I • ⊤` is `(I B') • ⊤`. -/
private theorem baseChange_ideal_smul_top {B B' M : Type*} [CommRing B] [CommRing B'] [Algebra B B']
    [AddCommGroup M] [Module B M] (I : Ideal B) :
    (I • (⊤ : Submodule B M)).baseChange B' = I.map (algebraMap B B') • ⊤ := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun x y hx hy => ?_)
    · change (1 : B') ⊗ₜ[B] (a • y) ∈ _
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, ← mul_one (algebraMap B B' a),
        ← smul_eq_mul (a := algebraMap B B' a), ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
    · simp only [map_add]
      exact add_mem hx hy
  · rw [Submodule.smul_le]
    intro r hr n _
    clear ‹n ∈ ⊤›
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      induction n using TensorProduct.induction_on with
      | zero => simp
      | tmul b m =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, ← Algebra.smul_def,
          TensorProduct.smul_tmul]
        exact Submodule.tmul_mem_baseChange_of_mem _ (Submodule.smul_mem_smul ha trivial)
      | add x y hx hy => rw [smul_add]; exact add_mem hx hy
    | zero => simp
    | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ c hx

/-- Along a faithfully flat algebra `B'`, `1 ⊗ m ∈ (I B') • (B' ⊗ M)` exactly when `m ∈ I • M`. -/
private theorem one_tmul_mem_ideal_smul_top_iff {B B' M : Type*} [CommRing B] [CommRing B']
    [Algebra B B']
    [Module.FaithfullyFlat B B'] [AddCommGroup M] [Module B M] (I : Ideal B) (m : M) :
    (1 : B') ⊗ₜ[B] m ∈ I.map (algebraMap B B') • (⊤ : Submodule B' (B' ⊗[B] M)) ↔
      m ∈ I • (⊤ : Submodule B M) := by
  rw [← baseChange_ideal_smul_top, ← Submodule.span_singleton_le_iff_mem,
    ← Submodule.span_singleton_le_iff_mem m,
    ← Submodule.baseChange_le_iff (A := B') (p := Submodule.span B {m}),
    Submodule.baseChange_span, Set.image_singleton]
  rfl

/-- A linear equivalence preserves `J • ⊤`. -/
private theorem mem_smul_top_iff_of_linearEquiv {S P Q : Type*} [CommRing S] [AddCommGroup P]
    [AddCommGroup Q] [Module S P] [Module S Q] (e : P ≃ₗ[S] Q) (J : Ideal S) (x : P) :
    e x ∈ J • (⊤ : Submodule S Q) ↔ x ∈ J • (⊤ : Submodule S P) :=
  ⟨fun h => by simpa using Submodule.smul_top_le_comap_smul_top J e.symm.toLinearMap h,
    fun h => Submodule.smul_top_le_comap_smul_top J e.toLinearMap h⟩

/-- Along a flat local map `φ : B → B'` of one-dimensional Noetherian local rings with
`𝔪_B B' = 𝔪_{B'}`, the canonical comparison `ω_B ⊗ B' ≅ ω_{B'}` of a normalized dualizing
complex identifies the `𝔪^n`-adic filtrations. -/
private theorem mem_maximalIdeal_pow_smul_top_iff_flatHomologyTensorComparison {B B' : Type u}
    [CommRing B] [CommRing B'] [IsLocalRing B] [IsLocalRing B'] [IsNoetherianRing B]
    [IsNoetherianRing B'] (φ : B →+* B') [IsLocalHom φ]
    (hφ : φ.Flat) (hmax : (maximalIdeal B).map φ = maximalIdeal B')
    (hdim : ringKrullDim B = 1) :
    ∀ (D : DerivedCategory (ModuleCat.{u} B))
      (_ : Dualizing.IsNormalizedDualizingComplex.{u, u} D)
      (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-1)).obj D) (n : ℕ),
      m ∈ (maximalIdeal B ^ n) •
          (⊤ : Submodule B ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-1)).obj D)) ↔
        ((MMP.flatHomologyTensorComparison φ hφ (-1)).app D).hom
            ((1 : B') ⊗ₜ[B, φ] m) ∈ (maximalIdeal B' ^ n) •
          (⊤ : Submodule B' ((DerivedCategory.homologyFunctor (ModuleCat.{u} B') (-1)).obj
            ((StacksDraft.PseudoCoherence.derivedExtensionScalars φ).obj D))) := by
  intro D hD m n
  letI : Algebra B B' := φ.toAlgebra
  haveI : Module.Flat B B' := hφ
  haveI : IsLocalHom (algebraMap B B') := ‹IsLocalHom φ›
  haveI : Module.FaithfullyFlat B B' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨-, -, hiso, -⟩ :=
    MMP.canonicalModule_derivedExtensionScalars_iso_of_flat.{u, u, u} (B := B') hmax D hD
  have hi := hiso 1 (by rw [hdim]; rfl)
  have h1 : (-((1 : ℕ) : ℤ)) = -1 := by norm_num
  rw [h1] at hi
  let e := (asIso ((MMP.flatHomologyTensorComparison φ hφ (-1)).app D)).toLinearEquiv
  have h2 := one_tmul_mem_ideal_smul_top_iff (B' := B') (maximalIdeal B ^ n) m
  have h3 := mem_smul_top_iff_of_linearEquiv e (maximalIdeal B' ^ n) ((1 : B') ⊗ₜ[B, φ] m)
  rw [Ideal.map_pow, show (maximalIdeal B).map (algebraMap B B') = maximalIdeal B' from hmax]
    at h2
  exact h2.symm.trans h3.symm

/-- A point of a scheme whose stalk has Krull dimension one has coheight one. -/
private theorem coheight_eq_one_of_ringKrullDim_stalk_eq_one {X : Scheme.{u}} {x : X}
    (h : ringKrullDim (X.presheaf.stalk x) = 1) : Order.coheight x = 1 := by
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-- On a locally Noetherian integral scheme whose stalk at `x` is a discrete valuation ring, the
order at `x` of `u ϖ ^ n`, with `u` a unit and `ϖ` a uniformizer of the stalk, is `n`. -/
private theorem ord_algebraMap_unit_mul_pow {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] (hx : Order.coheight x = 1)
    {v ϖ : X.presheaf.stalk x} (hv : IsUnit v) (hϖ : Irreducible ϖ) (n : ℕ) :
    Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField (v * ϖ ^ n)) x = n := by
  have hne : algebraMap (X.presheaf.stalk x) X.functionField (v * ϖ ^ n) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact mul_ne_zero hv.ne_zero (pow_ne_zero _ hϖ.ne_zero)
  rw [Scheme.ord_eq_iff hx hne]
  change Ring.ordFrac (X.presheaf.stalk x) _ = _
  rw [map_mul, map_pow, map_mul, map_pow, Ring.ordFrac_of_isUnit hv, Ring.ordFrac_irreducible hϖ,
    one_mul, ← WithZero.exp_nsmul, nsmul_one]
  rfl

/-- If `p : Y ⟶ X` is a dominant morphism of locally Noetherian integral schemes whose stalks at
`y` and `p y` are discrete valuation rings and whose stalk map at `y` sends the maximal ideal onto
the maximal ideal, then orders of rational functions at `p y` and at `y` agree. -/
private theorem ord_functionFieldMap_eq_of_map_maximalIdeal_eq {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (p : Y ⟶ X) [IsDominant p] (y : Y) [IsDiscreteValuationRing (X.presheaf.stalk (p y))]
    [IsDiscreteValuationRing (Y.presheaf.stalk y)]
    (hX : Order.coheight (p y) = 1) (hY : Order.coheight y = 1)
    (hmax : (maximalIdeal (X.presheaf.stalk (p y))).map (p.stalkMap y).hom =
      maximalIdeal (Y.presheaf.stalk y)) (f : X.functionField) :
    Scheme.ord (functionFieldMap p f) y = Scheme.ord f (p y) := by
  by_cases hf : f = 0
  · subst hf; simp
  let φ := (p.stalkMap y).hom
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk (p y))
  have hϖ' : Irreducible (φ ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmax,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  -- the order of `algebraMap r` is preserved for `r ≠ 0` in the stalk
  have key : ∀ r : X.presheaf.stalk (p y), r ≠ 0 →
      Scheme.ord (algebraMap _ Y.functionField (φ r)) y =
        Scheme.ord (algebraMap _ X.functionField r) (p y) := by
    intro r hr
    obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
    rw [ord_algebraMap_unit_mul_pow (p y) hX v.isUnit hϖ n, map_mul, map_pow,
      ord_algebraMap_unit_mul_pow y hY (v.isUnit.map φ) hϖ' n]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (p y)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hf
  have hbK : algebraMap _ X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  have hbK' : algebraMap _ Y.functionField (φ b) ≠ 0 := by
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk]; exact (map_ne_zero _).mpr hbK
  have e1 := Scheme.ord_mul (x := p y) hf hbK
  rw [div_mul_cancel₀ _ hbK] at e1
  have hf' : functionFieldMap p (algebraMap _ X.functionField a / algebraMap _ X.functionField b)
      ≠ 0 := (map_ne_zero _).mpr hf
  have e2 := Scheme.ord_mul (x := y) hf' ((map_ne_zero (functionFieldMap p)).mpr hbK)
  rw [← map_mul, div_mul_cancel₀ _ hbK, MMP.Mori.functionFieldMap_algebraMap_stalk,
    MMP.Mori.functionFieldMap_algebraMap_stalk, key a ha0, key b hb0] at e2
  omega

/-- A regular local homomorphism `B → B'` with Noetherian target whose closed fibre has a single
point sends the maximal ideal onto the maximal ideal: the closed fibre `B' ⧸ 𝔪_B B'` is a regular
ring with a single prime, hence a field. -/
private theorem map_maximalIdeal_eq_of_isRegularRingHom {B B' : Type*} [CommRing B]
    [CommRing B'] [IsLocalRing B] [IsLocalRing B'] [IsNoetherianRing B'] [Algebra B B']
    [IsLocalHom (algebraMap B B')] (hφ : IsRegularRingHom (algebraMap B B'))
    (hfib : ∀ Q : Ideal B', Q.IsPrime → Q.comap (algebraMap B B') = maximalIdeal B →
      Q = maximalIdeal B') :
    (maximalIdeal B).map (algebraMap B B') = maximalIdeal B' := by
  set I := (maximalIdeal B).map (algebraMap B B')
  have hIle : I ≤ maximalIdeal B' := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  obtain ⟨-, hfibre⟩ := isRegularRingHom_algebraMap_iff.mp hφ
  obtain ⟨-, hG⟩ := hfibre (maximalIdeal B)
  have hreg : IsRegularRing ((maximalIdeal B).Fiber B') := by
    haveI := hG
    exact IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.lid (maximalIdeal B).ResidueField
        ((maximalIdeal B).Fiber B')).toRingEquiv
  let e1 : (B ⧸ maximalIdeal B) ≃ₐ[B] (maximalIdeal B).ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom B _ _)
      (Ideal.bijective_algebraMap_quotient_residueField _)
  let e : (maximalIdeal B).Fiber B' ≃+* B' ⧸ I :=
    ((Algebra.TensorProduct.congr e1.symm (AlgEquiv.refl : B' ≃ₐ[B] B')).trans
      (Algebra.TensorProduct.comm B _ B')).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B' (maximalIdeal B)).symm.toRingEquiv
  haveI : IsRegularRing (B' ⧸ I) := IsRegularRing.of_ringEquiv e
  have hne : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal B').ne_top hIle
  haveI : Nontrivial (B' ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI : IsLocalRing (B' ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  refine le_antisymm hIle fun x hx => ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hnil : IsNilpotent (Ideal.Quotient.mk I x) := by
    rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
    intro (P : Ideal (B' ⧸ I)) hP
    haveI : P.IsPrime := hP
    have hc : P.comap (Ideal.Quotient.mk I) = maximalIdeal B' := by
      refine hfib _ (Ideal.comap_isPrime _ _) (le_antisymm ?_ ?_)
      · exact IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime _ _).ne_top
      · rw [← Ideal.map_le_iff_le_comap]
        intro y hy
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
        exact P.zero_mem
    have : x ∈ P.comap (Ideal.Quotient.mk I) := hc ▸ hx
    exact this
  let M := maximalIdeal (B' ⧸ I)
  haveI : IsDomain (Localization.AtPrime M) := IsRegularLocalRing.isDomain _
  have hinj : Function.Injective (algebraMap (B' ⧸ I) (Localization.AtPrime M)) :=
    IsLocalization.injective (M := M.primeCompl) _ fun s (hs : s ∈ M.primeCompl) =>
      (IsLocalRing.notMem_maximalIdeal.mp hs).mem_nonZeroDivisors
  apply hinj
  rw [map_zero]
  exact (hnil.map _).eq_zero

/-- If `ξ` lies over `η` and is minimal among the points of `Y` over the closure of `η`, then the
only prime of `𝒪_{Y,ξ}` lying over the maximal ideal of `𝒪_{X,η}` is the maximal ideal: such a
prime is a generalization of `ξ` lying over `η`. -/
private theorem eq_maximalIdeal_of_comap_stalkMap_eq {X Y : Scheme.{u}} (p : Y ⟶ X) {η : X}
    {ξ : Y} (hbase : p.base ξ = η) (hmin : ∀ ζ : Y, p.base ζ ∈ closure {η} → ζ ⤳ ξ → ζ = ξ)
    (Q : Ideal (Y.presheaf.stalk ξ)) [Q.IsPrime]
    (hQ : Q.comap (p.stalkMap ξ).hom = maximalIdeal (X.presheaf.stalk (p.base ξ))) :
    Q = maximalIdeal (Y.presheaf.stalk ξ) := by
  let z : Spec (Y.presheaf.stalk ξ) := ⟨Q, inferInstance⟩
  have hz : (Spec.map (p.stalkMap ξ)) z = IsLocalRing.closedPoint (X.presheaf.stalk (p.base ξ)) :=
    PrimeSpectrum.ext hQ
  have hp : p.base (Y.fromSpecStalk ξ z) = η := by
    have := congrArg (fun f => f z) (Scheme.SpecMap_stalkMap_fromSpecStalk p (x := ξ))
    simp only [Scheme.Hom.comp_apply] at this
    rw [← this, hz, Scheme.fromSpecStalk_closedPoint, hbase]
  have hsp : Y.fromSpecStalk ξ z ⤳ ξ := by
    have : Y.fromSpecStalk ξ z ∈ Set.range (Y.fromSpecStalk ξ) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have heq := hmin _ (by rw [hp]; exact subset_closure rfl) hsp
  have := (Y.fromSpecStalk ξ).isEmbedding.injective
    (heq.trans (Scheme.fromSpecStalk_closedPoint (x := ξ)).symm)
  exact congrArg PrimeSpectrum.asIdeal this

/-- Regularity of a ring homomorphism transports along an isomorphism of arrows in
`CommRingCat`. -/
private theorem isRegularRingHom_of_arrowIso
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R' →+* S')
    (e : Arrow.mk (CommRingCat.ofHom f) ≅ Arrow.mk (CommRingCat.ofHom g))
    (h : IsRegularRingHom f) : IsRegularRingHom g := by
  let eR : R ≃+* R' := (asIso e.hom.left).commRingCatIsoToRingEquiv
  let eS : S ≃+* S' := (asIso e.hom.right).commRingCatIsoToRingEquiv
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R' S' := g.toAlgebra
  have hcompat : ∀ r, eS (algebraMap R S r) = algebraMap R' S' (eR r) := fun r =>
    (congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of S' => m.hom r) (Arrow.w e.hom)).symm
  exact Stacks.RegularRingHom.isRegularRingHom_of_ringEquiv eR eS hcompat h

/-- If `A → Λ` is a regular ring map with `Λ` Noetherian and `W` is locally of finite type over
`Spec A`, then the stalk maps of the projection `W ×_{Spec A} Spec Λ ⟶ W` are regular: over an
affine open `Spec C` of `W` the projection is `Spec (Λ ⊗_A C) ⟶ Spec C`, whose stalk maps are
localizations of the regular map `C → Λ ⊗_A C`. -/
private theorem isRegularRingHom_stalkMap_pullback_fst {A Λ : Type u} [CommRing A]
    [CommRing Λ] [Algebra A Λ] [IsNoetherianRing Λ]
    (hφ : IsRegularRingHom (algebraMap A Λ)) {W : Scheme.{u}} (q : W ⟶ Spec (.of A))
    [LocallyOfFiniteType q]
    (ξ : ↥(pullback q (Spec.map (CommRingCat.ofHom (algebraMap A Λ))))) :
    IsRegularRingHom
      ((pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap A Λ)))).stalkMap ξ).hom := by
  let g : Spec (.of Λ) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Λ))
  let p := pullback.fst q g
  obtain ⟨U, hU, hxU, -⟩ : ∃ U : W.Opens, U ∈ W.affineOpens ∧ p ξ ∈ U ∧ U ≤ ⊤ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (p ξ))
  let C := Γ(W, U)
  let e : Spec (.of C) ≅ U.toScheme := (show IsAffineOpen U from hU).isoSpec.symm
  let g' : Spec (.of C) ⟶ W := e.hom ≫ U.ι
  let m : Spec (.of C) ⟶ Spec (.of A) := g' ≫ q
  letI : Algebra A C := (Spec.preimage m).hom.toAlgebra
  have hm : Spec.map (CommRingCat.ofHom (algebraMap A C)) = m := Spec.map_preimage m
  have : Algebra.FiniteType A C := by
    have : LocallyOfFiniteType m := inferInstance
    rw [← hm, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
    exact this
  have : IsNoetherianRing (Λ ⊗[A] C) := Algebra.FiniteType.isNoetherianRing Λ _
  let inl := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := Λ) (B := C)))
  let inr := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := A) (A := Λ) (B := C)).toRingHom)
  have houter : IsPullback inl inr g m := by
    rw [← hm]
    exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A Λ C)
  let fst' : Spec (.of (Λ ⊗[A] C)) ⟶ pullback q g :=
    pullback.lift (inr ≫ g') inl (by rw [Category.assoc]; exact houter.w.symm)
  have hpb : IsPullback fst' inr p g' := by
    refine IsPullback.of_right (h₁₂ := pullback.snd q g) (v₁₃ := g) (h₂₂ := q) ?_
      (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback q g).flip
    rw [pullback.lift_snd]
    exact houter
  obtain ⟨y', hy'⟩ : p ξ ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hxU
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := g') ξ
    (e.inv y') (by
      rw [← hy']
      change _ = (e.inv ≫ g') y'
      simp [g'])
  let pt := hpb.isoPullback.inv z
  have hpt : fst' pt = ξ := by
    rw [← hz1, ← hpb.isoPullback_inv_fst]
    rfl
  let a1 := Scheme.stalkMapIsoOfIsPullback hpb pt ξ hpt
  let a2 := Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := A) (A := Λ) (B := C)).toRingHom) pt
  refine isRegularRingHom_of_arrowIso _ _ (a1 ≪≫ a2).symm ?_
  have key := (isRegularRingHom_tfae_localizations
    (Algebra.TensorProduct.includeRight (R := A) (A := Λ) (B := C)).toRingHom).out 1 2
  haveI := pt.isPrime
  haveI := (PrimeSpectrum.comap (CommRingCat.Hom.hom (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := A) (A := Λ) (B := C)).toRingHom)) pt).isPrime
  exact key.mp (isRegularRingHom_baseChange (R' := C) hφ) _ _ _

/-- The geometric step at a point `ξ` of `W_R` lying over the generic point `η` of an exceptional
curve and minimal in its preimage: `𝔪_η` generates the maximal ideal of `𝒪_{W_R, ξ}`. The stalk
map is regular, being a localization of the base change of the regular map `A → R`, and by
minimality of `ξ` its closed fibre has a single prime. -/
private theorem map_maximalIdeal_stalkMap_of_base_eq
    (k : Type u) [Field k] [CharZero k] (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    (hA : ringKrullDim A = 2)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A κsep H]
    (W : Scheme.{u}) [IsIntegral W] (q : W ⟶ Spec (.of A)) [IsProper q] (hq : IsBirational q)
    (hW : IsRegular W)
    [IsIntegral (pullback q (Spec.map (CommRingCat.ofHom ((algebraMap H
      (AdicCompletion (maximalIdeal H) H)).comp (algebraMap A H)))))]
    [IsDominant (pullback.fst q (Spec.map (CommRingCat.ofHom ((algebraMap H
      (AdicCompletion (maximalIdeal H) H)).comp (algebraMap A H)))))]
    [IsLocallyNoetherian W]
    [IsLocallyNoetherian (pullback q (Spec.map (CommRingCat.ofHom ((algebraMap H
      (AdicCompletion (maximalIdeal H) H)).comp (algebraMap A H)))))] :
    let R := AdicCompletion (maximalIdeal H) H
    let g : Spec (.of R) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom ((algebraMap H R).comp (algebraMap A H)))
    let WR : Scheme.{u} := pullback q g
    let p : WR ⟶ W := pullback.fst q g
    ∀ η : W, ringKrullDim (W.presheaf.stalk η) = 1 →
      q.base η = IsLocalRing.closedPoint A →
      ∀ ξ : WR, p.base ξ ∈ closure {η} →
        (∀ ζ : WR, p.base ζ ∈ closure {η} → ζ ⤳ ξ → ζ = ξ) →
        p.base ξ = η →
        let B := W.presheaf.stalk (p.base ξ)
        let B' := WR.presheaf.stalk ξ
        let φ : B →+* B' := (p.stalkMap ξ).hom
        (maximalIdeal B).map φ = maximalIdeal B' := by
  intro R g WR p η hη hqη ξ hξ hmin hbase B B' φ
  obtain ⟨-, -, _, ⟨_, -, -⟩, -, -⟩ :=
    MMP.Foundations.isNoetherianRing_strictHenselization_adicCompletion k A κsep H
  letI : Algebra A R := ((algebraMap H R).comp (algebraMap A H)).toAlgebra
  have hreg : IsRegularRingHom φ := isRegularRingHom_stalkMap_pullback_fst
    (isRegularRingHom_strictHenselization_adicCompletion k A κsep H) q ξ
  letI : Algebra B B' := φ.toAlgebra
  haveI : IsLocalHom (algebraMap B B') := inferInstanceAs (IsLocalHom φ)
  exact map_maximalIdeal_eq_of_isRegularRingHom (B := B) (B' := B') hreg
    fun Q _ hc => eq_maximalIdeal_of_comap_stalkMap_eq p hbase hmin Q hc

/-- The local part at a point `ξ` of `W_R` lying over the generic point `η` of an exceptional
curve and minimal in its preimage: the stalk is a discrete valuation ring, multiplicity is one,
and orders and canonical frames are preserved. -/
private theorem isDiscreteValuationRing_stalk_pullback_fst_of_base_eq
    (k : Type u) [Field k] [CharZero k] (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    (hA : ringKrullDim A = 2)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A κsep H]
    (W : Scheme.{u}) [IsIntegral W] (q : W ⟶ Spec (.of A)) [IsProper q] (hq : IsBirational q)
    (hW : IsRegular W)
    [IsIntegral (pullback q (Spec.map (CommRingCat.ofHom ((algebraMap H
      (AdicCompletion (maximalIdeal H) H)).comp (algebraMap A H)))))]
    [IsDominant (pullback.fst q (Spec.map (CommRingCat.ofHom ((algebraMap H
      (AdicCompletion (maximalIdeal H) H)).comp (algebraMap A H)))))]
    [IsLocallyNoetherian W]
    [IsLocallyNoetherian (pullback q (Spec.map (CommRingCat.ofHom ((algebraMap H
      (AdicCompletion (maximalIdeal H) H)).comp (algebraMap A H)))))] :
    let R := AdicCompletion (maximalIdeal H) H
    let g : Spec (.of R) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom ((algebraMap H R).comp (algebraMap A H)))
    let WR : Scheme.{u} := pullback q g
    let p : WR ⟶ W := pullback.fst q g
    ∀ η : W, ringKrullDim (W.presheaf.stalk η) = 1 →
      q.base η = IsLocalRing.closedPoint A →
      ∀ ξ : WR, p.base ξ ∈ closure {η} →
        (∀ ζ : WR, p.base ζ ∈ closure {η} → ζ ⤳ ξ → ζ = ξ) →
        p.base ξ = η →
        let B := W.presheaf.stalk (p.base ξ)
        let B' := WR.presheaf.stalk ξ
        let φ : B →+* B' := (p.stalkMap ξ).hom
        IsDiscreteValuationRing B' ∧
        (maximalIdeal B).map φ = maximalIdeal B' ∧
        (∀ f : W.functionField, Scheme.ord (functionFieldMap p f) ξ = Scheme.ord f η) ∧
        ∃ hφ : φ.Flat,
          ∀ (D : DerivedCategory (ModuleCat.{u} B))
            (_ : Dualizing.IsNormalizedDualizingComplex.{u, u} D)
            (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-1)).obj D) (n : ℕ),
            m ∈ (maximalIdeal B ^ n) •
                (⊤ : Submodule B ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-1)).obj D)) ↔
              ((MMP.flatHomologyTensorComparison φ hφ (-1)).app D).hom
                  ((1 : B') ⊗ₜ[B, φ] m) ∈ (maximalIdeal B' ^ n) •
                (⊤ : Submodule B' ((DerivedCategory.homologyFunctor (ModuleCat.{u} B') (-1)).obj
                  ((StacksDraft.PseudoCoherence.derivedExtensionScalars φ).obj D))) := by
  intro R g WR p η hη hqη ξ hξ hmin hbase B B' φ
  have hmax :=
    map_maximalIdeal_stalkMap_of_base_eq k A hA κsep H W q hq hW η hη hqη ξ hξ hmin hbase
  obtain ⟨hgf, -⟩ := flat_and_exists_isIso_morphismRestrict k A hA κsep H W q hq hW
  have : Flat p := inferInstance
  have hφ : φ.Flat := Flat.stalkMap p ξ
  have hdimB : ringKrullDim B = 1 := by
    change ringKrullDim (W.presheaf.stalk (p.base ξ)) = 1
    rw [hbase]; exact hη
  letI : Algebra B B' := φ.toAlgebra
  haveI : Module.Flat B B' := hφ
  haveI : IsLocalHom (algebraMap B B') := inferInstanceAs (IsLocalHom φ)
  have hdimB' : ringKrullDim B' = 1 := by
    rw [ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq hmax, hdimB]
  have hst : IsLocallyNoetherian WR ∧ ∀ x : WR, IsRegularLocalRing (WR.presheaf.stalk x) :=
    ((isRegular_tfae WR).out 1 2).mp (isRegular_pullback k A κsep H W q hW)
  have hstW : IsLocallyNoetherian W ∧ ∀ x : W, IsRegularLocalRing (W.presheaf.stalk x) :=
    ((isRegular_tfae W).out 1 2).mp hW
  haveI : IsRegularLocalRing B' := hst.2 ξ
  haveI : IsRegularLocalRing B := hstW.2 _
  haveI : IsDiscreteValuationRing B :=
    (MMP.Resolution.Kollar.isDiscreteValuationRing_of_ringKrullDim_eq_one hdimB).2
  haveI : IsDiscreteValuationRing B' :=
    (MMP.Resolution.Kollar.isDiscreteValuationRing_of_ringKrullDim_eq_one hdimB').2
  have hord : ∀ f : W.functionField, Scheme.ord (functionFieldMap p f) ξ = Scheme.ord f η :=
    fun f => hbase ▸ ord_functionFieldMap_eq_of_map_maximalIdeal_eq p ξ
      (coheight_eq_one_of_ringKrullDim_stalk_eq_one hdimB)
      (coheight_eq_one_of_ringKrullDim_stalk_eq_one hdimB') hmax f
  exact ⟨‹IsDiscreteValuationRing B'›, hmax, hord, hφ,
    mem_maximalIdeal_pow_smul_top_iff_flatHomologyTensorComparison φ hφ hmax hdimB⟩

/-- The local part: along the geometric components of an exceptional curve, multiplicity is one
and orders and canonical frames are preserved. -/
private theorem base_eq_and_isDiscreteValuationRing_stalk_pullback_fst
    (k : Type u) [Field k] [CharZero k] (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    (hA : ringKrullDim A = 2)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A κsep H]
    (W : Scheme.{u}) [IsIntegral W] (q : W ⟶ Spec (.of A)) [IsProper q] (hq : IsBirational q)
    (hW : IsRegular W)
    [IsIntegral (pullback q (Spec.map (CommRingCat.ofHom ((algebraMap H
      (AdicCompletion (maximalIdeal H) H)).comp (algebraMap A H)))))]
    [IsDominant (pullback.fst q (Spec.map (CommRingCat.ofHom ((algebraMap H
      (AdicCompletion (maximalIdeal H) H)).comp (algebraMap A H)))))]
    [IsLocallyNoetherian W]
    [IsLocallyNoetherian (pullback q (Spec.map (CommRingCat.ofHom ((algebraMap H
      (AdicCompletion (maximalIdeal H) H)).comp (algebraMap A H)))))] :
    let R := AdicCompletion (maximalIdeal H) H
    let g : Spec (.of R) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom ((algebraMap H R).comp (algebraMap A H)))
    let WR : Scheme.{u} := pullback q g
    let p : WR ⟶ W := pullback.fst q g
    ∀ η : W, ringKrullDim (W.presheaf.stalk η) = 1 →
      q.base η = IsLocalRing.closedPoint A →
      ∀ ξ : WR, p.base ξ ∈ closure {η} →
        (∀ ζ : WR, p.base ζ ∈ closure {η} → ζ ⤳ ξ → ζ = ξ) →
        let B := W.presheaf.stalk (p.base ξ)
        let B' := WR.presheaf.stalk ξ
        let φ : B →+* B' := (p.stalkMap ξ).hom
        p.base ξ = η ∧ IsDiscreteValuationRing B' ∧
        (maximalIdeal B).map φ = maximalIdeal B' ∧
        (∀ f : W.functionField, Scheme.ord (functionFieldMap p f) ξ = Scheme.ord f η) ∧
        ∃ hφ : φ.Flat,
          ∀ (D : DerivedCategory (ModuleCat.{u} B))
            (_ : Dualizing.IsNormalizedDualizingComplex.{u, u} D)
            (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-1)).obj D) (n : ℕ),
            m ∈ (maximalIdeal B ^ n) •
                (⊤ : Submodule B ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-1)).obj D)) ↔
              ((MMP.flatHomologyTensorComparison φ hφ (-1)).app D).hom
                  ((1 : B') ⊗ₜ[B, φ] m) ∈ (maximalIdeal B' ^ n) •
                (⊤ : Submodule B' ((DerivedCategory.homologyFunctor (ModuleCat.{u} B') (-1)).obj
                  ((StacksDraft.PseudoCoherence.derivedExtensionScalars φ).obj D))) := by
  intro R g WR p η hη hqη ξ hξ hmin B B' φ
  obtain ⟨hgf, -⟩ := flat_and_exists_isIso_morphismRestrict k A hA κsep H W q hq hW
  have hbase : p.base ξ = η := base_eq_of_forall_specializes_eq p hξ hmin
  exact ⟨hbase, isDiscreteValuationRing_stalk_pullback_fst_of_base_eq k A hA κsep H W q hq hW η hη hqη
    ξ hξ hmin hbase⟩

/-- Let `A` be a normal two-dimensional local domain essentially of finite type over a field `k`
of characteristic zero, `H` a strict henselization of `A` and `R = Ĥ` its `𝔪_H`-adic
completion. Let `q : W ⟶ Spec A` be proper birational with `W` integral and regular, and let
`W_R` be the base change of `W` along `Spec R ⟶ Spec A`. Then `W_R` is integral, Noetherian,
regular of dimension two, and proper birational over `Spec R`. If `η` is the generic point of an
exceptional prime curve of `W` and `ξ` is the generic point of an irreducible component of its
preimage in `W_R`, then `ξ` lies over `η`, its local ring is a discrete valuation ring, the local
map `𝒪_{W,η} → 𝒪_{W_R,ξ}` is flat and carries the maximal ideal onto the maximal ideal, orders
of rational functions are unchanged, and for every normalized dualizing complex `D` of `𝒪_{W,η}`
the canonical comparison `MMP.flatHomologyTensorComparison` in degree `-1` preserves the
`𝔪`-adic order of every element of `H^{-1}(D)`. -/
@[mmp "lem_mmp_foundation_regular_models_over_strict_completion"]
public theorem isRegular_pullback_strictHenselization_adicCompletion
    (k : Type u) [Field k] [CharZero k] (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra k A] [Algebra.EssFiniteType k A]
    (hA : ringKrullDim A = 2)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsHenselization A κsep H]
    (W : Scheme.{u}) [IsIntegral W] (q : W ⟶ Spec (.of A)) [IsProper q] (hq : IsBirational q)
    (hW : IsRegular W) :
    let R := AdicCompletion (maximalIdeal H) H
    let g : Spec (.of R) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom ((algebraMap H R).comp (algebraMap A H)))
    let WR : Scheme.{u} := pullback q g
    let p : WR ⟶ W := pullback.fst q g
    ∃ (_ : IsLocallyNoetherian W) (_ : IsIntegral WR) (_ : IsLocallyNoetherian WR)
      (_ : IsDominant p),
      (IsNoetherian WR ∧ IsRegular WR ∧ topologicalKrullDim WR = 2 ∧
        IsProper (pullback.snd q g) ∧ IsBirational (pullback.snd q g)) ∧
      ∀ η : W, ringKrullDim (W.presheaf.stalk η) = 1 →
        q.base η = IsLocalRing.closedPoint A →
        ∀ ξ : WR, p.base ξ ∈ closure {η} →
          (∀ ζ : WR, p.base ζ ∈ closure {η} → ζ ⤳ ξ → ζ = ξ) →
          let B := W.presheaf.stalk (p.base ξ)
          let B' := WR.presheaf.stalk ξ
          let φ : B →+* B' := (p.stalkMap ξ).hom
          p.base ξ = η ∧ IsDiscreteValuationRing B' ∧
          (maximalIdeal B).map φ = maximalIdeal B' ∧
          (∀ f : W.functionField, Scheme.ord (functionFieldMap p f) ξ = Scheme.ord f η) ∧
          ∃ hφ : φ.Flat,
            ∀ (D : DerivedCategory (ModuleCat.{u} B))
              (_ : Dualizing.IsNormalizedDualizingComplex.{u, u} D)
              (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-1)).obj D) (n : ℕ),
              m ∈ (maximalIdeal B ^ n) •
                  (⊤ : Submodule B
                    ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-1)).obj D)) ↔
                ((MMP.flatHomologyTensorComparison φ hφ (-1)).app D).hom
                    ((1 : B') ⊗ₜ[B, φ] m) ∈ (maximalIdeal B' ^ n) •
                  (⊤ : Submodule B' ((DerivedCategory.homologyFunctor (ModuleCat.{u} B') (-1)).obj
                    ((StacksDraft.PseudoCoherence.derivedExtensionScalars φ).obj D))) := by
  have hWN : IsLocallyNoetherian W :=
    haveI := Algebra.EssFiniteType.isNoetherianRing k A
    LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨hI, hN, hNoeth, hReg, hdim, hbir⟩ :=
    isIntegral_isRegular_pullback k A hA κsep H W q hq hW
  have hD := isDominant_pullback_fst k A κsep H W q
  exact ⟨hWN, hI, hN, hD, ⟨hNoeth, hReg, hdim, inferInstance, hbir⟩,
    base_eq_and_isDiscreteValuationRing_stalk_pullback_fst k A hA κsep H W q hq hW⟩

end MMP.Foundations

/-! ## Rationality of the clipped boundary of a restricted series

The proof has three steps.

1. The clipped boundary `Θ = Ω - Ω ∧ F` is rational. No component of `Θ` is a stable base
   prime of `K + Θ`: such a prime would persist to the boundaries `Θ_{q n!}` close to `Θ`,
   whose components are not stable base primes. If `Θ` were irrational, a one-sided
   rational approximation `Φ` of `Θ` in its smallest rational affine hull, overshooting
   `Θ` at an irrational component `G`, would satisfy the clipping bounds for `P = Ω - Φ`.
   The lifting property then makes `G` a fixed component of `|k(K + Φ)|`, and so a stable
   base prime of `K + Θ`, which is impossible.
2. For sufficiently divisible `k`, `V_k = H⁰(S, 𝒪_S(kK + ⌊kΘ⌋))`. The lifting property at
   `P₀ = Ω - Θ` gives `⊇`. For `⊆`, every section of `V_k` vanishes along `kF ≥ kP₀`.
3. The floor-section algebra of `K + Θ` is finitely generated by the rational clause of
   `F(d)`. By step 2 a Veronese of `⊕_m V_m tᵐ` is finitely generated, and hence, by
   `MMP.Fourfold.finiteType_iff_veroneseSubalgebra_fg`, so is the whole algebra.
-/

namespace MMP.Fourfold

open CategoryTheory AlgebraicGeometry MMP.Mori
open scoped ENNReal

/-- The smooth variety underlying a graded restricted series is `ℚ`-factorial: every Weil
divisor is already Cartier. -/
private theorem isQFactorial_of_isGradedRestrictedSeries
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hR : IsGradedRestrictedSeries sS sT g f d K Ω q V) : IsQFactorial sS :=
  ⟨hR.isNormalVariety_source, fun _ =>
    ⟨1, one_pos, isCartier_of_isSmoothScheme hR.isSmoothScheme _⟩⟩

/-- Adding an effective `ℝ`-divisor on a smooth variety does not increase a log discrepancy. -/
private theorem exists_isLogDiscrepancy_add_le_of_nonneg {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hsm : IsSmoothScheme sX) {n : ℕ} {D : DivisorOver k sX} (Δ : RDivisor X)
    (hΔ : ∀ P, 0 ≤ Δ.coeff P) {B : RDivisor X} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) :
    ∃ a' : ℝ, a' ≤ a ∧ MMP.Intersection.IsLogDiscrepancy sX n (B + Δ) D a' := by
  classical
  suffices H : ∀ Δ : MMP.Mori.PrimeDivisor X →₀ ℝ, (∀ P, 0 ≤ Δ P) → ∀ (B : RDivisor X) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n B D a → ∃ a' : ℝ, a' ≤ a ∧
        MMP.Intersection.IsLogDiscrepancy sX n (B + Δ) D a' from H Δ hΔ B a h
  intro Δ
  induction Δ using Finsupp.induction with
  | zero => exact fun _ B a h => ⟨a, le_rfl, by rwa [add_zero]⟩
  | single_add P c f hP hc ih =>
    intro hnn B a h
    have hc0 : 0 ≤ c := by
      have := hnn P
      rwa [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp hP,
        add_zero] at this
    have hf0 : ∀ Q, 0 ≤ f Q := fun Q => by
      have := hnn Q
      by_cases hQ : P = Q
      · subst hQ; rw [Finsupp.notMem_support_iff.mp hP]
      · simpa [Finsupp.single_apply, hQ] using this
    obtain ⟨a₁, ha₁, h₁⟩ := exists_isLogDiscrepancy_add_single_le hsm h P hc0
    obtain ⟨a₂, ha₂, h₂⟩ := ih hf0 _ a₁ h₁
    exact ⟨a₂, ha₂.trans ha₁, by rwa [← add_assoc]⟩

/-- On a smooth variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isRCartier_of_isSmoothScheme {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hsm : IsSmoothScheme sX) (D : RDivisor X) : RDivisor.IsRCartier D := by
  classical
  let e := D.support.equivFin
  refine ⟨D.support.card, fun i => D (e.symm i), fun i => Finsupp.single (e.symm i).1 1,
    fun i => isCartier_of_isSmoothScheme hsm _, fun Γ => ?_⟩
  change D Γ = _
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
  rw [e.symm.sum_comp (fun x : D.support => D x.1 * (((if x.1 = Γ then 1 else 0 : ℤ)) : ℝ)),
    Finset.sum_coe_sort D.support (fun x => D x * (((if x = Γ then 1 else 0 : ℤ)) : ℝ))]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · exact not_not.mp h

/-- On a smooth variety, the log discrepancies of a real boundary `B ≤ Ω`, for a klt pair
`(X, Ω)`, are positive. -/
private theorem pos_of_isLogDiscrepancy_of_le {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hsm : IsSmoothScheme sX) {Ω : QDivisor X} (hΩ : IsKltPair sX Ω) {B : RDivisor X}
    (hB : B ≤ QDivisor.toRDivisor Ω) {n : ℕ} {D : DivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) : 0 < a := by
  obtain ⟨a', ha', h'⟩ := exists_isLogDiscrepancy_add_le_of_nonneg hsm
    (QDivisor.toRDivisor Ω - B) (fun P => by
      change (0 : ℝ) ≤ (QDivisor.toRDivisor Ω - B) P
      rw [Finsupp.sub_apply, sub_nonneg]
      exact hB P) h
  rw [add_sub_cancel] at h'
  exact (hΩ.2 n D a' h').trans_le ha'

/-- On a smooth variety over a perfect field, every coefficient of the boundary of a klt pair is
less than one: the log discrepancy of a prime divisor `P` of `X` is `1 - Ω_P`. -/
private theorem coeff_lt_one_of_isKltPair {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (hsm : IsSmoothScheme sX) {Ω : QDivisor X} (hΩ : IsKltPair sX Ω)
    (P : MMP.Mori.PrimeDivisor X) : (Ω.coeff P : ℝ) < 1 := by
  obtain ⟨hX, n, K, hK, -⟩ := hΩ.1.isPair
  have hn := hK.topologicalKrullDim_eq
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hrel⟩ := isRCartier_of_isSmoothScheme hsm
    (Divisor.toRDivisor K + QDivisor.toRDivisor Ω)
  let E := DivisorOver.ofPrimeDivisor k hX P
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : CompactSpace E.Y := inferInstanceAs (CompactSpace X)
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hC j)
  have hco : ∀ j, ((L' j).coeff E.E : ℝ) = (C j).coeff P := by
    intro j
    obtain ⟨U, hU, φ, hφ⟩ := hC j P.genericPoint
    have h1 := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hL' j) hφ E.E hU
      (MMP.Mori.pointComponent P.genericPoint)
    have hPU : (P.support ∩ U).Nonempty := (P.genericPoint_mem_iff U).mp hU
    have h2 := hφ P hPU
    rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at h2
    have hZ : P.component = MMP.Mori.pointComponent P.genericPoint := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
    rw [hZ] at h2
    change (L' j).coeff P = X.ord (functionFieldMap (𝟙 X) _) P.genericPoint at h1
    rw [functionFieldMap_id_apply] at h1
    exact_mod_cast h1.trans h2.symm
  have hord : E.ordPullback ω = P.ordForm ω := DivisorOver.ordPullback_ofPrimeDivisor hX hn P ω
  have hrel' : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) +
      (QDivisor.toRDivisor Ω).coeff Γ = ∑ i, r i * (C i).coeff Γ := fun Γ => by
    rw [← hrel Γ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, hωK Γ]
  have hlog : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Ω) E
      (1 + (E.ordPullback ω : ℝ) - ∑ i, r i * (L' i).coeff E.E) :=
    ⟨hX, (inferInstance : IsProper (𝟙 X)), ω, hω0, ⟨K, hK, fun Γ => (hωK Γ).symm⟩, m, r, C, L',
      hC, hrel', fun j => ⟨_, hL' j⟩, rfl⟩
  have hpos := hΩ.2 n E _ hlog
  have hP := hrel' P
  simp_rw [hco, hord] at hpos
  rw [QDivisor.coeff_toRDivisor] at hP
  linarith

/-- **Klt is preserved by lowering a real boundary on a smooth variety.** If `(X, Ω)` is klt
and `B ≤ Ω` is an `ℝ`-divisor on a smooth variety `X` over a perfect field, then `(X, B)` is a
real klt pair. -/
private theorem isRealKltPair_of_le {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (hsm : IsSmoothScheme sX) {Ω : QDivisor X} (hΩ : IsKltPair sX Ω) {B : RDivisor X}
    (hB : B ≤ QDivisor.toRDivisor Ω) : IsRealKltPair sX B := by
  obtain ⟨hX, n, K, hK, -⟩ := hΩ.1.isPair
  refine ⟨hX, fun P => ?_, ⟨n, K, hK, isRCartier_of_isSmoothScheme hsm _⟩,
    fun n D a h => pos_of_isLogDiscrepancy_of_le hsm hΩ hB h⟩
  have h1 : B.coeff P ≤ (QDivisor.toRDivisor Ω).coeff P := hB P
  rw [QDivisor.coeff_toRDivisor] at h1
  exact h1.trans_lt (coeff_lt_one_of_isKltPair hsm hΩ P)

/-- The clipped boundary `Θ = Ω - Ω ∧ F` of a graded restricted series is a real klt boundary. -/
private theorem isRealKltPair_restrictedClippedBoundary
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hR : IsGradedRestrictedSeries sS sT g f d K Ω q V) :
    IsRealKltPair sS (restrictedClippedBoundary K Ω q V) :=
  isRealKltPair_of_le hR.isSmoothScheme hR.isKltPair restrictedClippedBoundary_le

/-- On an affine `T`, a section over `f⁻¹U` of `𝒪_S(E)`, for `U` a neighbourhood of `f(η_G)`,
becomes a global section after multiplication by a power of a function pulled back from `T`
that is a unit along `G`: the order along `G` is unchanged. -/
private theorem exists_unit_forall_nonneg_of_preimage {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S] [IsAffine T]
    (f : S ⟶ T) (E : Divisor S) (G : MMP.Mori.PrimeDivisor S) {U : T.Opens}
    (hU : f G.genericPoint ∈ U) (χ : (RationalFunctions S)ˣ)
    (hχ : ∀ P : MMP.Mori.PrimeDivisor S, (P.support ∩ (f ⁻¹ᵁ U : Set S)).Nonempty →
      0 ≤ E.coeff P + P.ord χ) :
    ∃ χ' : (RationalFunctions S)ˣ, (∀ P : MMP.Mori.PrimeDivisor S, 0 ≤ E.coeff P + P.ord χ') ∧
      G.ord χ' = G.ord χ := by
  classical
  obtain ⟨h, hhU, hGh⟩ := (isAffineOpen_top T).exists_basicOpen_le
    (⟨f G.genericPoint, hU⟩ : U) trivial
  set a : Γ(S, ⊤) := f.app ⊤ h with ha_def
  have hbas : S.basicOpen a = f ⁻¹ᵁ T.basicOpen h := (Scheme.preimage_basicOpen f h).symm
  have hGa : G.genericPoint ∈ S.basicOpen a := by rw [hbas]; exact hGh
  have hgen : ∀ Z : irreducibleComponents S, componentGenericPoint S Z ∈ S.basicOpen a := by
    intro Z
    exact (genericPoint_mem_iff Z (S.basicOpen a)).mpr
      ⟨G.genericPoint, hGa, mem_irreducibleComponent_of_irreducibleSpace Z _⟩
  have ha : ∀ (Z : irreducibleComponents S) (hZ : componentGenericPoint S Z ∈ (⊤ : S.Opens)),
      (S.presheaf.germ ⊤ _ hZ).hom a ≠ 0 := fun Z hZ =>
    ((Scheme.mem_basicOpen S a _ hZ).mp (hgen Z)).ne_zero
  set u := MMP.Threefold.Resolution.sectionUnit a ha
  have hu0 : ∀ P : MMP.Mori.PrimeDivisor S, 0 ≤ P.ord u := fun P =>
    MMP.Threefold.Resolution.ord_sectionUnit_nonneg a ha P trivial
  have huG : G.ord u = 0 := MMP.Threefold.Resolution.ord_sectionUnit_eq_zero a ha G trivial
    ((Scheme.mem_basicOpen S a _ trivial).mp hGa)
  have hu1 : ∀ P : MMP.Mori.PrimeDivisor S, ¬ (P.support ∩ (f ⁻¹ᵁ U : Set S)).Nonempty →
      1 ≤ P.ord u := by
    intro P hP
    refine MMP.Threefold.Resolution.one_le_ord_sectionUnit a ha P trivial fun hunit => hP ?_
    have hPa : P.genericPoint ∈ S.basicOpen a := (Scheme.mem_basicOpen S a _ trivial).mpr hunit
    rw [hbas] at hPa
    exact (P.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp (hhU hPa)
  set N : ℕ := ∑ P ∈ (E + principalDivisor χ).support, (E.coeff P + P.ord χ).natAbs with hN
  refine ⟨u ^ N * χ, fun P => ?_, ?_⟩
  · rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_pow, nsmul_eq_mul]
    by_cases hP : 0 ≤ E.coeff P + P.ord χ
    · have := hu0 P
      nlinarith
    · have hPU : ¬ (P.support ∩ (f ⁻¹ᵁ U : Set S)).Nonempty := fun h' => hP (hχ P h')
      have h1 := hu1 P hPU
      have hmem : P ∈ (E + principalDivisor χ).support := by
        rw [Finsupp.mem_support_iff]
        intro h0
        apply hP
        have : (E + principalDivisor χ).coeff P = 0 := h0
        rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor] at this
        omega
      have h2 : (E.coeff P + P.ord χ).natAbs ≤ N :=
        Finset.single_le_sum (f := fun P => (E.coeff P + P.ord χ).natAbs)
          (fun _ _ => Nat.zero_le _) hmem
      have h3 : ((E.coeff P + P.ord χ).natAbs : ℤ) ≤ N := by exact_mod_cast h2
      have h4 : -(E.coeff P + P.ord χ) ≤ ((E.coeff P + P.ord χ).natAbs : ℤ) := by
        rw [Int.natCast_natAbs]; exact neg_le_abs _
      have h5 : (N : ℤ) ≤ N * P.ord u := le_mul_of_one_le_right (by positivity) h1
      linarith
  · rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_pow, huG]
    simp

/-- On an affine `T`, if every global section of `𝒪_S(E)` vanishes along `G`, then the relative
fixed multiplicity of `E` along `G` over `T` is positive. -/
private theorem pos_relativeFixedMultiplicity_of_forall {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S] [IsAffine T]
    (f : S ⟶ T) (E : Divisor S) (G : MMP.Mori.PrimeDivisor S)
    (h : ∀ χ : (RationalFunctions S)ˣ, (∀ P : MMP.Mori.PrimeDivisor S, 0 ≤ E.coeff P + P.ord χ) →
      0 < E.coeff G + G.ord χ) :
    0 < relativeFixedMultiplicity f E G := by
  refine lt_of_lt_of_le zero_lt_one (le_iInf fun U => le_iInf fun hU => le_iInf fun σ =>
    le_iInf fun hσ => ?_)
  have hne := support_inter_preimage_nonempty f hU
  obtain ⟨χ, hχσ, hχ⟩ := exists_unit_of_divisorialSubmodule_ne_zero
    (hne.mono Set.inter_subset_right) σ hσ
  rw [sectionVanishingOrder_eq_toNat _ σ χ
    (hχσ G.component (G.componentGenericPoint_mem_of_nonempty hne))]
  obtain ⟨χ', hχ'0, hχ'G⟩ := exists_unit_forall_nonneg_of_preimage f E G hU χ hχ
  have := h χ' hχ'0
  rw [hχ'G] at this
  exact_mod_cast (show 1 ≤ (E.coeff G + G.ord χ).toNat by omega)

/-- A finite family of positive reals has a positive lower bound. -/
private theorem exists_pos_forall_le {ι : Type*} [Finite ι] (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ c i := by
  have h : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i, δ ≤ c i :=
    Filter.eventually_all.2 fun i =>
      Filter.mem_of_superset (Ioo_mem_nhdsGT (hc i)) fun _ hx => hx.2.le
  obtain ⟨δ, h1, h2⟩ := (h.and self_mem_nhdsWithin).exists
  exact ⟨δ, h2, h1⟩

/-- A `ℚ`-divisor with integral coefficients is a divisor. -/
private theorem exists_toQDivisor_eq {X : Scheme.{0}} (E : QDivisor X)
    (h : ∀ P, ∃ z : ℤ, E.coeff P = z) : ∃ D : Divisor X, Divisor.toQDivisor D = E := by
  refine ⟨DivisorWithCoeffs.roundDown E, ?_⟩
  ext P
  obtain ⟨z, hz⟩ := h P
  change ((DivisorWithCoeffs.roundDown E).coeff P : ℚ) = E.coeff P
  rw [DivisorWithCoeffs.coeff_roundDown, hz, Int.floor_intCast]

open Classical in
/-- The `ℚ`-divisor supported on `Z` with coefficients `φ` in the coordinates `Z ≃ Fin |Z|`. -/
private noncomputable def finCoordDivisor {X : Scheme.{0}} (Z : Finset (MMP.Mori.PrimeDivisor X))
    (φ : Fin Z.card → ℚ) : QDivisor X :=
  Finsupp.onFinset Z (fun P => if h : P ∈ Z then φ (Z.equivFin ⟨P, h⟩) else 0) fun P hP => by
    by_contra h
    exact hP (dif_neg h)

private theorem coeff_finCoordDivisor_of_mem {X : Scheme.{0}}
    {Z : Finset (MMP.Mori.PrimeDivisor X)} (φ : Fin Z.card → ℚ) {P : MMP.Mori.PrimeDivisor X}
    (h : P ∈ Z) : (finCoordDivisor Z φ).coeff P = φ (Z.equivFin ⟨P, h⟩) := by
  classical
  change (if h : P ∈ Z then φ (Z.equivFin ⟨P, h⟩) else 0) = _
  rw [dif_pos h]

private theorem coeff_finCoordDivisor_of_notMem {X : Scheme.{0}}
    {Z : Finset (MMP.Mori.PrimeDivisor X)} (φ : Fin Z.card → ℚ) {P : MMP.Mori.PrimeDivisor X}
    (h : P ∉ Z) : (finCoordDivisor Z φ).coeff P = 0 := by
  classical
  change (if h : P ∈ Z then φ (Z.equivFin ⟨P, h⟩) else 0) = _
  rw [dif_neg h]

/-- A rational linear form `∑ c_P x_P` on the divisors supported on a finite set `Z` of prime
divisors, written in the coordinates `Z ≃ Fin |Z|`. -/
private theorem sum_mul_coeff_eq_sum_equivFin {X : Scheme.{0}}
    (Z : Finset (MMP.Mori.PrimeDivisor X)) (c : MMP.Mori.PrimeDivisor X →₀ ℚ) (B : RDivisor X)
    (hB : ∀ P, P ∉ Z → B.coeff P = 0) :
    (c.sum fun P cP => (cP : ℝ) * B.coeff P) =
      ∑ j, (c (Z.equivFin.symm j).1 : ℝ) * B.coeff (Z.equivFin.symm j).1 := by
  classical
  rw [Z.equivFin.symm.sum_comp (fun x : Z => (c x.1 : ℝ) * B.coeff x.1),
    Finset.sum_coe_sort Z (fun P => (c P : ℝ) * B.coeff P), Finsupp.sum]
  have h1 : ∑ P ∈ c.support, (c P : ℝ) * B.coeff P = ∑ P ∈ c.support ∪ Z, (c P : ℝ) * B.coeff P :=
    Finset.sum_subset Finset.subset_union_left (fun P _ hP => by
      rw [Finsupp.notMem_support_iff.mp hP]; simp)
  have h2 : ∑ P ∈ Z, (c P : ℝ) * B.coeff P = ∑ P ∈ c.support ∪ Z, (c P : ℝ) * B.coeff P :=
    Finset.sum_subset Finset.subset_union_right (fun P _ hP => by rw [hB P hP, mul_zero])
  rw [h1, ← h2]

/-- A point of the rational affine hull of `θ` satisfies every rational linear equation that `θ`
satisfies. -/
private theorem sum_mul_eq_of_mem_rationalAffineHull {n : ℕ} {θ x : Fin n → ℝ}
    (hx : x ∈ rationalAffineHull θ) (c : Fin n → ℚ) (q₀ : ℚ)
    (h : ∑ j, (c j : ℝ) * θ j = q₀) : ∑ j, (c j : ℝ) * x j = q₀ := by
  have := mem_rationalAffineHull.mp hx (c, -q₀) (by
    simp only [ratAffineForm]
    push_cast
    linarith)
  simp only [ratAffineForm] at this
  push_cast at this
  linarith

/-- A point of the rational affine hull of `θ` agrees with `θ` at every rational coordinate. -/
private theorem eq_of_mem_rationalAffineHull {n : ℕ} {θ x : Fin n → ℝ}
    (hx : x ∈ rationalAffineHull θ) (j : Fin n) (q₀ : ℚ) (h : θ j = q₀) : x j = q₀ := by
  have := sum_mul_eq_of_mem_rationalAffineHull hx (Pi.single j 1) q₀ (by
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
    simpa using h)
  rwa [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp), Pi.single_eq_same,
    Rat.cast_one, one_mul] at this

/-- The coordinates of an `ℝ`-divisor that is not a `ℚ`-divisor are not all rational. -/
private theorem coeff_equivFin_notMem_range_ratCast {X : Scheme.{0}} (Θ : RDivisor X)
    (h : ∀ D : QDivisor X, QDivisor.toRDivisor D ≠ Θ) :
    (fun j => Θ.coeff (Θ.support.equivFin.symm j).1) ∉
      Set.range (fun (t : Fin Θ.support.card → ℚ) (j : Fin Θ.support.card) => (t j : ℝ)) := by
  rintro ⟨t, ht⟩
  apply h (finCoordDivisor Θ.support t)
  ext P
  change ((finCoordDivisor Θ.support t).coeff P : ℝ) = Θ.coeff P
  by_cases hP : P ∈ Θ.support
  · rw [coeff_finCoordDivisor_of_mem t hP]
    simpa using congrFun ht (Θ.support.equivFin ⟨P, hP⟩)
  · have h0 : Θ.coeff P = 0 := Finsupp.notMem_support_iff.mp hP
    rw [coeff_finCoordDivisor_of_notMem t hP, Rat.cast_zero, h0]

/-- A `ℚ`-divisor on the components of `Θ` whose coordinates satisfy every rational affine
equation satisfied by those of `Θ` lies in the smallest rational affine hull of `Θ`. -/
private theorem isInSmallestRationalAffineHull_finCoordDivisor {X : Scheme.{0}} (Θ : RDivisor X)
    (φ : Fin Θ.support.card → ℚ)
    (h : ∀ c : Fin Θ.support.card → ℚ, ∀ q₀ : ℚ,
      ∑ j, (c j : ℝ) * Θ.coeff (Θ.support.equivFin.symm j).1 = q₀ →
        ∑ j, (c j : ℝ) * (φ j : ℝ) = q₀) :
    IsInSmallestRationalAffineHull Θ (QDivisor.toRDivisor (finCoordDivisor Θ.support φ)) := by
  classical
  have hout : ∀ P, P ∉ Θ.support →
      (QDivisor.toRDivisor (finCoordDivisor Θ.support φ)).coeff P = 0 := fun P hP => by
    rw [QDivisor.coeff_toRDivisor, coeff_finCoordDivisor_of_notMem φ hP, Rat.cast_zero]
  refine ⟨fun P hP => by_contra fun hZ => Finsupp.mem_support_iff.mp hP (hout P hZ),
    fun c q₀ hcq => ?_⟩
  rw [sum_mul_coeff_eq_sum_equivFin _ c Θ fun P hP => Finsupp.notMem_support_iff.mp hP] at hcq
  rw [sum_mul_coeff_eq_sum_equivFin _ c _ hout]
  convert h (fun j => c (Θ.support.equivFin.symm j).1) q₀ hcq using 2 with j
  simp [QDivisor.coeff_toRDivisor, coeff_finCoordDivisor_of_mem φ (Θ.support.equivFin.symm j).2]

/-- **The asymptotic fixed part bounds the order of every section of `V_k`.** For `q ∣ k`, a
section `χ ∈ V_k` vanishes along `G` to order at least `k F_G`, where `F` is the asymptotic fixed
part: `k F_G ≤ (kK + ⌊kΩ⌋)_G + ord_G χ`. -/
private theorem mul_toReal_restrictedAsymptoticFixedPart_le
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hR : IsGradedRestrictedSeries sS sT g f d K Ω q V) {k : ℕ} (hk : 0 < k) (hqk : q ∣ k)
    {χ : (RationalFunctions S)ˣ} (hχ : (χ : RationalFunctions S) ∈ V k)
    (G : MMP.Mori.PrimeDivisor S) :
    (k : ℝ) * (restrictedAsymptoticFixedPart K Ω q V G).toReal ≤
      (((seriesDivisor K Ω k).coeff G + G.ord χ : ℤ) : ℝ) := by
  have : IsDomain (RationalFunctions S) :=
    (rationalFunctionsEquivFunctionField S).toMulEquiv.isDomain
  have hs := hR.mem_divisorialSections' hqk hχ
  obtain ⟨χ₁, hχ₁, ht0⟩ := exists_unit_of_mem_divisorialSections hs χ.ne_zero
  obtain rfl : χ₁ = χ := Units.ext hχ₁
  set t : ℤ := (seriesDivisor K Ω k).coeff G + G.ord χ₁
  have hM : restrictedAsymptoticFixedPart K Ω q V G ≤ (t.toNat : ℝ≥0∞) / k := by
    refine (restrictedAsymptoticFixedPart_le_normalizedFixedPart hR hk hqk G).trans ?_
    unfold restrictedNormalizedFixedPart
    gcongr
    exact_mod_cast restrictedFixedMultiplicity_le_toNat hχ hs χ₁.ne_zero rfl G
  have hMr := ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (by exact_mod_cast hk.ne')) hM
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    show ((t.toNat : ℕ) : ℝ) = (t : ℝ) by exact_mod_cast Int.toNat_of_nonneg (ht0 G),
    le_div_iff₀ (by exact_mod_cast hk)] at hMr
  linarith

/-- **No component of the clipped boundary is a stable base prime of `K + Θ`.** Such a prime
would, by the persistence clause of `F(d)`, be a stable base prime of `K + Θ_{q n!}` for `n`
large, where `Θ_{q n!}` is close to `Θ` and still positive along it; but no component of
`Θ_{q n!}` is a stable base prime. -/
private theorem not_isInRelativeDivisorialStableBase_of_pos_coeff_restrictedClippedBoundary
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hF : BirationalFiniteGenerationProperty d)
    (hR : IsGradedRestrictedSeries sS sT g f d K Ω q V) {G : MMP.Mori.PrimeDivisor S}
    (hG : 0 < (restrictedClippedBoundary K Ω q V).coeff G) :
    ¬ IsInRelativeDivisorialStableBase f (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K +
      restrictedClippedBoundary K Ω q V) G := by
  classical
  have := hR.isAffine_target
  set Θ := restrictedClippedBoundary K Ω q V
  obtain ⟨-, ⟨ε₁, hε₁, hpers⟩, -⟩ := hF.2 S sS T sT f
    (isQFactorial_of_isGradedRestrictedSeries hR) hR.isCanonicalDivisor.topologicalKrullDim_eq
    hR.isNormalVariety_target hR.isAffine_target hR.comp_eq hR.isProjectiveMorphism
    hR.isBirationalMorphism Θ (fun P => Finsupp.le_def.mp (zero_le_restrictedClippedBoundary hR) P)
    (isRealKltPair_restrictedClippedBoundary hR) K hR.isCanonicalDivisor
  intro hst
  have hpos : ∀ n : ℕ, 0 < q * n.factorial := fun n => Nat.mul_pos hR.q_pos (Nat.factorial_pos n)
  have hev1 : ∀ᶠ n : ℕ in Filter.atTop, ∀ P ∈ Θ.support,
      |(restrictedClippedBoundaryAt K Ω V (q * n.factorial)).coeff P - Θ.coeff P| < ε₁ := by
    rw [Filter.eventually_all_finset]
    intro P _
    filter_upwards [(Metric.tendsto_nhds.mp
      (tendsto_restrictedClippedBoundaryAt_factorial hR P)) ε₁ hε₁] with n hn
    rwa [Real.dist_eq] at hn
  have hev2 : ∀ᶠ n : ℕ in Filter.atTop,
      0 < (restrictedClippedBoundaryAt K Ω V (q * n.factorial)).coeff G :=
    (tendsto_restrictedClippedBoundaryAt_factorial hR G).eventually (lt_mem_nhds hG)
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  have hsupp := support_restrictedClippedBoundaryAt_subset hR (hpos n) (dvd_mul_right q _)
  apply not_isInRelativeDivisorialStableBase_restrictedClippedBoundaryAt hR (hpos n)
    (dvd_mul_right q _) G hn2
  refine hpers _ hsupp
    (fun P => Finsupp.le_def.mp (zero_le_restrictedClippedBoundaryAt hR _) P)
    (isRealKltPair_of_le hR.isSmoothScheme hR.isKltPair
      (restrictedClippedBoundaryAt_le (K := K) (Ω := Ω) (V := V) _)) (fun P => ?_) G hst
  by_cases hP : P ∈ Θ.support
  · exact hn1 P hP
  · have h1 : Θ.coeff P = 0 := Finsupp.notMem_support_iff.mp hP
    have h2 : (restrictedClippedBoundaryAt K Ω V (q * n.factorial)).coeff P = 0 :=
      Finsupp.notMem_support_iff.mp (fun h => hP (hsupp h))
    rw [h1, h2]
    simpa using hε₁

/-- Cancelling the factor `r ≠ 0` from `r c x = r z`. -/
private theorem natCast_mul_eq_of_mul_eq {r c : ℕ} (hr : 0 < r) {x : ℚ} {z : ℤ}
    (h : ((r * c : ℕ) : ℚ) * x = r * z) : (c : ℚ) * x = z := by
  have : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast at h
  exact mul_left_cancel₀ this (by rw [← h]; ring)

/-- A coefficient within `δ / k` of `θ = ω - F`, with `δ ≤ εF`, `ε < 1` and `k ≥ 1`, lies below
`ω` and at distance at least `(1 - ε / k) F` from it. -/
private theorem le_and_le_sub_of_abs_sub_lt {x θ ω F δ ε k : ℝ} (hx : |x - θ| < δ / k)
    (hθ : θ = ω - F) (hδF : δ ≤ ε * F) (hε : ε < 1) (hk : 1 ≤ k) (hF : 0 < F) (hδ : 0 ≤ δ) :
    x ≤ ω ∧ (1 - ε / k) * F ≤ ω - x := by
  rw [abs_lt] at hx
  have h₁ : δ / k ≤ ε * F / k := div_le_div_of_nonneg_right hδF (by linarith)
  have h₂ : ε * F / k ≤ ε * F := div_le_self (hδ.trans hδF) hk
  have h₃ : ε * F < F := by nlinarith
  refine ⟨by linarith, ?_⟩
  rw [show (1 - ε / k) * F = F - ε * F / k by ring]
  linarith

/-- If `k Φ` has coefficients in `r ℤ` and `r ∣ k`, then `k K + ⌊k Φ⌋ = r D` for a divisor `D`
with `(k / r) (K + Φ) = D`. -/
private theorem exists_smul_eq_seriesDivisor {S : Scheme.{0}} [IsIntegral S] [CompactSpace S]
    [IsLocallyNoetherian S] [IsNormal S] (K : Divisor S) (Φ : QDivisor S) {r k : ℕ} (hr : 0 < r)
    (hrk : r ∣ k) (hkΦ : ∀ P, ∃ z : ℤ, (k : ℚ) * Φ.coeff P = r * z) :
    ∃ D : Divisor S, (r : ℤ) • D = seriesDivisor K Φ k ∧ ∀ P, (k : ℝ) / r *
      (DivisorWithCoeffs.coeff (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K) P +
      (QDivisor.toRDivisor Φ).coeff P) = D.coeff P := by
  obtain ⟨c, hc⟩ := hrk
  have hcΦ : ∀ P, ∃ z : ℤ, ((c : ℤ) • Φ).coeff P = z := by
    intro P
    obtain ⟨z, hz⟩ := hkΦ P
    refine ⟨z, ?_⟩
    rw [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, Int.cast_natCast]
    exact natCast_mul_eq_of_mul_eq hr (hc ▸ hz)
  obtain ⟨Dφ, hDφ⟩ := exists_toQDivisor_eq _ hcΦ
  have hDφc : ∀ P, (Dφ.coeff P : ℚ) = c * Φ.coeff P := fun P => by
    have := congrArg (fun E : QDivisor S => E.coeff P) hDφ
    simpa [DivisorWithCoeffs.coeff_smul] using this
  refine ⟨(c : ℤ) • K + Dφ, ?_, fun P => ?_⟩
  · ext P
    rw [coeff_seriesDivisor]
    obtain ⟨z, hz⟩ := hkΦ P
    have hz' : ((k : ℚ) * Φ.coeff P) = ((r * z : ℤ) : ℚ) := by
      rw [hz]
      push_cast
      ring
    rw [hz', Int.floor_intCast]
    have h1 : (Dφ.coeff P : ℚ) = z := by
      rw [hDφc]
      exact natCast_mul_eq_of_mul_eq hr (hc ▸ hz)
    have h2 : Dφ.coeff P = z := by exact_mod_cast h1
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, smul_eq_mul, h2, hc]
    push_cast
    ring
  · have h1 : (((c : ℤ) • K + Dφ).coeff P : ℝ) = c * K.coeff P + c * Φ.coeff P := by
      have : (((c : ℤ) • K + Dφ).coeff P : ℚ) = c * K.coeff P + c * Φ.coeff P := by
        rw [← hDφc]
        simp [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add]
      exact_mod_cast this
    rw [h1, QDivisor.coeff_toRDivisor]
    change (k : ℝ) / r * ((K.coeff P : ℝ) + _) = _
    have : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [hc]
    push_cast
    field_simp

/-- If `Φ ≤ Ω` is a `ℚ`-divisor with `k Φ` integral, `0 ≤ Φ` and
`Ω ∧ (1 - ε / k) F ≤ Ω - Φ`, then a unit section of `kK + ⌊kΦ⌋` vanishes along any `G` with
`Ω_G - F_G < Φ_G`. -/
private theorem pos_coeff_seriesDivisor_add_ord_of_lt
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hR : IsGradedRestrictedSeries sS sT g f d K Ω q V) {ε : ℚ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hlift : ∀ k : ℕ, 0 < k → q ∣ k → ∀ P : QDivisor S,
      ((k : ℤ) • P).IsCartierDivisor →
      coeffwiseMin Ω (fun G => ENNReal.ofReal (1 - (ε : ℝ) / k) *
          restrictedAsymptoticFixedPart K Ω q V G) ≤ QDivisor.toRDivisor P →
      P ≤ Ω →
      ∀ s ∈ divisorialSections (k • K + DivisorWithCoeffs.roundDown ((k : ℚ) • (Ω - P))),
        s ∈ V k)
    {k r : ℕ} (hkpos : 0 < k) (hqk : q ∣ k) (Φ : QDivisor S)
    (hkΦ : ∀ P, ∃ z : ℤ, (k : ℚ) * Φ.coeff P = r * z) (hΦ0 : ∀ P, (0 : ℝ) ≤ Φ.coeff P)
    (hlow : ∀ P, min (Ω.coeff P : ℝ) ((1 - (ε : ℝ) / k) *
      (restrictedAsymptoticFixedPart K Ω q V P).toReal) ≤ Ω.coeff P - Φ.coeff P)
    {G : MMP.Mori.PrimeDivisor S}
    (hG : (Ω.coeff G : ℝ) - (restrictedAsymptoticFixedPart K Ω q V G).toReal < Φ.coeff G)
    (χ : (RationalFunctions S)ˣ) (hχ : ∀ P, 0 ≤ (seriesDivisor K Φ k).coeff P + P.ord χ) :
    0 < (seriesDivisor K Φ k).coeff G + G.ord χ := by
  classical
  have := hR.isAffine_target
  have : IsDomain (RationalFunctions S) :=
    (rationalFunctionsEquivFunctionField S).toMulEquiv.isDomain
  have hFr : ∀ P, ENNReal.ofReal (restrictedAsymptoticFixedPart K Ω q V P).toReal =
      restrictedAsymptoticFixedPart K Ω q V P := fun P =>
    ENNReal.ofReal_toReal (restrictedAsymptoticFixedPart_ne_top hR P)
  have hFr0 : ∀ P, 0 ≤ (restrictedAsymptoticFixedPart K Ω q V P).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hΩ0 : ∀ P, (0 : ℝ) ≤ Ω.coeff P := fun P => by exact_mod_cast hR.coeff_nonneg P
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
  have hs : (χ : RationalFunctions S) ∈
      divisorialSections (k • K + DivisorWithCoeffs.roundDown ((k : ℚ) • (Ω - (Ω - Φ)))) := by
    rw [sub_sub_cancel, mem_divisorialSections]
    exact isDivisorialSection_of_unit χ fun P _ => hχ P
  have hCart : ((k : ℤ) • (Ω - Φ)).IsCartierDivisor := by
    obtain ⟨D', hD'⟩ := exists_toQDivisor_eq ((k : ℤ) • (Ω - Φ)) (fun P => by
      obtain ⟨z, hz⟩ := hkΦ P
      obtain ⟨w, hw⟩ := hR.exists_int_eq_mul_coeff hqk P
      refine ⟨w - r * z, ?_⟩
      rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub, zsmul_eq_mul]
      push_cast
      rw [mul_sub, hw, hz])
    exact ⟨D', hD', isCartier_of_isSmoothScheme hR.isSmoothScheme D'⟩
  have hlowR : coeffwiseMin Ω (fun G => ENNReal.ofReal (1 - (ε : ℝ) / k) *
      restrictedAsymptoticFixedPart K Ω q V G) ≤ QDivisor.toRDivisor (Ω - Φ) := by
    refine Finsupp.le_def.mpr fun P => ?_
    change (coeffwiseMin Ω _).coeff P ≤ (QDivisor.toRDivisor (Ω - Φ)).coeff P
    have hεk : (0 : ℝ) ≤ 1 - (ε : ℝ) / k := by
      have : (ε : ℝ) / k ≤ ε := div_le_self (by exact_mod_cast hε0.le) hkR
      have hε1' : (ε : ℝ) < 1 := by exact_mod_cast hε1
      linarith
    rw [coeff_coeffwiseMin, QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_sub, ← hFr P,
      ← ENNReal.ofReal_mul hεk, ENNReal.toReal_min ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (hΩ0 P), ENNReal.toReal_ofReal (mul_nonneg hεk (hFr0 P))]
    push_cast
    exact hlow P
  have hleΩ : Ω - Φ ≤ Ω := Finsupp.le_def.mpr fun P => by
    change (Ω - Φ).coeff P ≤ Ω.coeff P
    rw [DivisorWithCoeffs.coeff_sub]
    have : (0 : ℚ) ≤ Φ.coeff P := by exact_mod_cast hΦ0 P
    linarith
  have hsV := hlift k hkpos hqk (Ω - Φ) hCart hlowR hleΩ _ hs
  have h0 : (χ : RationalFunctions S) ≠ 0 := χ.ne_zero
  have hMr := mul_toReal_restrictedAsymptoticFixedPart_le hR hkpos hqk hsV G
  obtain ⟨z, hz⟩ := hkΦ G
  have hzR : ((r * z : ℤ) : ℝ) = k * Φ.coeff G := by exact_mod_cast hz.symm
  have hfl : (⌊(k : ℚ) * Ω.coeff G⌋ : ℝ) ≤ k * Ω.coeff G := by
    exact_mod_cast Int.floor_le ((k : ℚ) * Ω.coeff G)
  rw [coeff_seriesDivisor] at hMr
  rw [coeff_seriesDivisor, hz, show (r : ℚ) * z = ((r * z : ℤ) : ℚ) by push_cast; ring,
    Int.floor_intCast]
  have : (0 : ℝ) < ((k * K.coeff G + r * z + G.ord χ : ℤ) : ℝ) := by
    push_cast at hMr hzR ⊢
    nlinarith
  exact_mod_cast this

/-- Step 1: the clipped boundary is a `ℚ`-divisor. -/
private theorem exists_qDivisor_eq_restrictedClippedBoundary
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hF : BirationalFiniteGenerationProperty d)
    (hV : HasRestrictedLiftingProperty sS sT g f d K Ω q V) :
    ∃ Θ : QDivisor S, QDivisor.toRDivisor Θ = restrictedClippedBoundary K Ω q V := by
  classical
  obtain ⟨hR, ε, hε0, hε1, hlift⟩ := hV
  have := hR.isAffine_target
  have : IsDomain (RationalFunctions S) :=
    (rationalFunctionsEquivFunctionField S).toMulEquiv.isDomain
  set Θ := restrictedClippedBoundary K Ω q V with hΘdef
  have hΘ0 : ∀ P, 0 ≤ Θ.coeff P := fun P =>
    Finsupp.le_def.mp (zero_le_restrictedClippedBoundary hR) P
  obtain ⟨-, -, ⟨ε₂, hε₂, r, hr, hunif⟩⟩ := hF.2 S sS T sT f
    (isQFactorial_of_isGradedRestrictedSeries hR) hR.isCanonicalDivisor.topologicalKrullDim_eq
    hR.isNormalVariety_target hR.isAffine_target hR.comp_eq hR.isProjectiveMorphism
    hR.isBirationalMorphism Θ hΘ0 (isRealKltPair_restrictedClippedBoundary hR) K
    hR.isCanonicalDivisor
  -- suppose `Θ` is irrational
  by_contra hirr
  push Not at hirr
  set Z := Θ.support
  set s := Z.card
  set e := Z.equivFin
  set θ : Fin s → ℝ := fun j => Θ.coeff (e.symm j).1 with hθdef
  have hlift_in : ∀ φ P (h : P ∈ Z), (finCoordDivisor Z φ).coeff P = φ (e ⟨P, h⟩) :=
    fun φ _ h => coeff_finCoordDivisor_of_mem φ h
  have hlift_out : ∀ φ P, P ∉ Z → (finCoordDivisor Z φ).coeff P = 0 :=
    fun φ _ h => coeff_finCoordDivisor_of_notMem φ h
  have hθP : ∀ P (h : P ∈ Z), θ (e ⟨P, h⟩) = Θ.coeff P := fun P h => by
    simp [hθdef]
  -- the coefficients of `F`
  set Fr : MMP.Mori.PrimeDivisor S → ℝ := fun P => (restrictedAsymptoticFixedPart K Ω q V P).toReal
  have hFr : ∀ P, ENNReal.ofReal (Fr P) = restrictedAsymptoticFixedPart K Ω q V P := fun P =>
    ENNReal.ofReal_toReal (restrictedAsymptoticFixedPart_ne_top hR P)
  have hFr0 : ∀ P, 0 ≤ Fr P := fun _ => ENNReal.toReal_nonneg
  have hΩ0 : ∀ P, (0 : ℝ) ≤ Ω.coeff P := fun P => by exact_mod_cast hR.coeff_nonneg P
  have hΘcoeff : ∀ P, Θ.coeff P = Ω.coeff P - min (Ω.coeff P : ℝ) (Fr P) := by
    intro P
    rw [hΘdef, coeff_restrictedClippedBoundary, ← hFr P, ENNReal.toReal_min ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (hΩ0 P), ENNReal.toReal_ofReal (hFr0 P)]
  have hZpos : ∀ P ∈ Z, 0 < Θ.coeff P := fun P h =>
    lt_of_le_of_ne (hΘ0 P) (Ne.symm (Finsupp.mem_support_iff.mp h))
  have hZF : ∀ P ∈ Z, Fr P < Ω.coeff P ∧ Θ.coeff P = Ω.coeff P - Fr P := by
    intro P h
    have h1 := hZpos P h
    rw [hΘcoeff P] at h1 ⊢
    by_cases hle : (Ω.coeff P : ℝ) ≤ Fr P
    · rw [min_eq_left hle] at h1; simp at h1
    · push Not at hle
      exact ⟨hle, by rw [min_eq_right hle.le]⟩
  -- the error bound
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_pos_forall_le
    (fun j : Fin s => min (θ j) (if 0 < Fr (e.symm j).1 then (ε : ℝ) * Fr (e.symm j).1 else 1))
    (fun j => lt_min (hZpos _ (e.symm j).2) (by
      split_ifs with h
      · exact mul_pos (by exact_mod_cast hε0) h
      · exact one_pos))
  set δ := min δ₀ (ε₂ / 2)
  have hδ : 0 < δ := lt_min hδ₀ (half_pos hε₂)
  have hδε₂ : δ < ε₂ := (min_le_right _ _).trans_lt (half_lt_self hε₂)
  have hδθ : ∀ P ∈ Z, δ ≤ Θ.coeff P := fun P h => by
    have : δ ≤ θ (e ⟨P, h⟩) :=
      (min_le_left δ₀ (ε₂ / 2)).trans ((hδ₀le (e ⟨P, h⟩)).trans (min_le_left _ _))
    exact this.trans_eq (hθP P h)
  have hδF : ∀ P ∈ Z, 0 < Fr P → δ ≤ ε * Fr P := fun P h hF0 => by
    have := (min_le_left δ₀ (ε₂ / 2)).trans ((hδ₀le (e ⟨P, h⟩)).trans (min_le_right _ _))
    rwa [Equiv.symm_apply_apply, if_pos hF0] at this
  -- the one-sided rational approximation
  obtain ⟨k, hkpos, hqrk, φ, hφW, hφint, hφnorm, j₀, hj₀irr, hj₀lt⟩ :=
    exists_rat_approx_one_sided (isRationalAffineSubspace_rationalAffineHull θ)
      (self_mem_rationalAffineHull θ) (coeff_equivFin_notMem_range_ratCast Θ hirr) hr
      (Nat.mul_pos hR.q_pos hr) hδ 0
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
  have hqk : q ∣ k := (dvd_mul_right q r).trans hqrk
  have hδk : δ / k ≤ δ := div_le_self hδ.le hkR
  set Φq := finCoordDivisor Z φ
  have hφj : ∀ j, |(φ j : ℝ) - θ j| < δ / k := fun j => by
    simpa [Real.norm_eq_abs] using (pi_norm_lt_iff (by positivity)).mp hφnorm j
  have hΦZ : ∀ P (h : P ∈ Z), |(Φq.coeff P : ℝ) - Θ.coeff P| < δ / k := fun P h => by
    rw [hlift_in φ P h, ← hθP P h]; exact hφj _
  have hF0eq : ∀ P (h : P ∈ Z), Fr P = 0 → (Φq.coeff P : ℝ) = Ω.coeff P := by
    intro P h hF0
    rw [hlift_in φ P h]
    refine eq_of_mem_rationalAffineHull hφW (e ⟨P, h⟩) (Ω.coeff P) ?_
    rw [hθP P h, hΘcoeff P, hF0, min_eq_right (hΩ0 P)]
    simp
  -- bounds on `Φ`
  have hΦ0 : ∀ P, (0 : ℝ) ≤ Φq.coeff P := by
    intro P
    by_cases h : P ∈ Z
    · have h1 := hΦZ P h
      have h2 := hδθ P h
      rw [abs_lt] at h1
      linarith
    · rw [hlift_out φ P h]; simp
  have hΦΩ : ∀ P, (Φq.coeff P : ℝ) ≤ Ω.coeff P := by
    intro P
    by_cases h : P ∈ Z
    · by_cases hF0 : Fr P = 0
      · exact (hF0eq P h hF0).le
      · have hFp : 0 < Fr P := lt_of_le_of_ne (hFr0 P) (Ne.symm hF0)
        exact (le_and_le_sub_of_abs_sub_lt (hΦZ P h) (hZF P h).2 (hδF P h hFp)
          (by exact_mod_cast hε1) hkR hFp hδ.le).1
    · rw [hlift_out φ P h]; simpa using hΩ0 P
  have hlow : ∀ P, min (Ω.coeff P : ℝ) ((1 - (ε : ℝ) / k) * Fr P) ≤
      Ω.coeff P - Φq.coeff P := by
    intro P
    by_cases h : P ∈ Z
    · by_cases hF0 : Fr P = 0
      · rw [hF0eq P h hF0, hF0, mul_zero, sub_self]
        exact min_le_right _ _
      · have hFp : 0 < Fr P := lt_of_le_of_ne (hFr0 P) (Ne.symm hF0)
        exact (min_le_right _ _).trans (le_and_le_sub_of_abs_sub_lt (hΦZ P h) (hZF P h).2
          (hδF P h hFp) (by exact_mod_cast hε1) hkR hFp hδ.le).2
    · rw [hlift_out φ P h]
      simp
  -- integrality
  have hkΦ : ∀ P, ∃ z : ℤ, (k : ℚ) * Φq.coeff P = r * z := by
    intro P
    by_cases h : P ∈ Z
    · obtain ⟨z, hz⟩ := hφint (e ⟨P, h⟩)
      refine ⟨z, ?_⟩
      rw [hlift_in φ P h, ← hz]
      have : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
    · exact ⟨0, by rw [hlift_out φ P h]; simp⟩
  obtain ⟨D, hE, hDcoeff⟩ :=
    exists_smul_eq_seriesDivisor K Φq hr ((dvd_mul_left r q).trans hqrk) hkΦ
  have hΦhull : IsInSmallestRationalAffineHull Θ (QDivisor.toRDivisor Φq) :=
    isInSmallestRationalAffineHull_finCoordDivisor Θ φ fun c q₀ =>
      sum_mul_eq_of_mem_rationalAffineHull hφW c q₀
  have hΦle : QDivisor.toRDivisor Φq ≤ QDivisor.toRDivisor Ω :=
    Finsupp.le_def.mpr hΦΩ
  have hclose : ∀ P, |(QDivisor.toRDivisor Φq).coeff P - Θ.coeff P| < ε₂ := by
    intro P
    rw [QDivisor.coeff_toRDivisor]
    by_cases h : P ∈ Z
    · exact (hΦZ P h).trans_le (hδk.trans hδε₂.le)
    · have h0 : Θ.coeff P = 0 := Finsupp.notMem_support_iff.mp h
      rw [hlift_out φ P h, h0]
      simpa using hε₂
  -- the irrational component `G`
  set G : MMP.Mori.PrimeDivisor S := (e.symm j₀).1 with hGdef
  have hGZ : G ∈ Z := (e.symm j₀).2
  have hθG : θ j₀ = Θ.coeff G := rfl
  have hΦG : (Φq.coeff G : ℝ) = φ j₀ := by
    rw [hlift_in φ G hGZ]
    simp [hGdef]
  have hstab := (hunif (QDivisor.toRDivisor Φq) hΦhull hΦ0
    (isRealKltPair_of_le hR.isSmoothScheme hR.isKltPair hΦle) hclose k hkpos D
    (isCartier_of_isSmoothScheme hR.isSmoothScheme D) hDcoeff).2 G
  refine not_isInRelativeDivisorialStableBase_of_pos_coeff_restrictedClippedBoundary hF hR
    (hZpos G hGZ) (hstab ?_)
  rw [hE]
  have hG' : (Ω.coeff G : ℝ) - Fr G < Φq.coeff G := by
    rw [← (hZF G hGZ).2, hΦG, ← hθG]
    exact hj₀lt
  exact pos_relativeFixedMultiplicity_of_forall f _ G fun χ hχ =>
    pos_coeff_seriesDivisor_add_ord_of_lt hR hε0 hε1 hlift hkpos hqk Φq hkΦ hΦ0 hlow hG' χ hχ

/-- The lifting property at `P₀ = Ω - Θ`: when `k(Ω - Θ)` is integral, every section of
`kK + ⌊kΘ⌋` lies in `V_k`. -/
private theorem mem_of_mem_divisorialSections_clippedBoundary
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hV : HasRestrictedLiftingProperty sS sT g f d K Ω q V) (Θ : QDivisor S)
    (hΘ : QDivisor.toRDivisor Θ = restrictedClippedBoundary K Ω q V) {k : ℕ} (hk : 0 < k)
    (hqk : q ∣ k) {D : Divisor S} (hD : Divisor.toQDivisor D = (k : ℤ) • (Ω - Θ))
    {s : RationalFunctions S}
    (hs : s ∈ divisorialSections (k • K + DivisorWithCoeffs.roundDown ((k : ℚ) • Θ))) :
    s ∈ V k := by
  obtain ⟨hR, ε, hε0, hε1, hlift⟩ := hV
  have hP : QDivisor.toRDivisor (Ω - Θ) =
      coeffwiseMin Ω (restrictedAsymptoticFixedPart K Ω q V) := by
    rw [map_sub, hΘ, restrictedClippedBoundary, sub_sub_cancel]
  refine hlift k hk hqk (Ω - Θ) ⟨D, hD, isCartier_of_isSmoothScheme hR.isSmoothScheme D⟩ ?_ ?_
    s (by rwa [sub_sub_cancel])
  · rw [hP]
    refine Finsupp.le_def.mpr fun G => ?_
    change (coeffwiseMin Ω _).coeff G ≤ (coeffwiseMin Ω _).coeff G
    rw [coeff_coeffwiseMin, coeff_coeffwiseMin]
    refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _))
      (min_le_min_left _ (mul_le_of_le_one_left zero_le ?_))
    exact ENNReal.ofReal_le_one.mpr (by
      have : (0 : ℝ) ≤ (ε : ℝ) / k := div_nonneg (by exact_mod_cast hε0.le) (Nat.cast_nonneg k)
      linarith)
  · refine Finsupp.le_def.mpr fun G => ?_
    have h0 := Finsupp.le_def.mp (zero_le_restrictedClippedBoundary hR) G
    rw [← hΘ] at h0
    change (0 : ℝ) ≤ (QDivisor.toRDivisor Θ).coeff G at h0
    rw [QDivisor.coeff_toRDivisor] at h0
    change (Ω - Θ).coeff G ≤ Ω.coeff G
    rw [DivisorWithCoeffs.coeff_sub]
    have : (0 : ℚ) ≤ Θ.coeff G := by exact_mod_cast h0
    linarith

/-- Every section of `V_k`, for `q ∣ k`, vanishes along `kF ≥ k(Ω - Θ)`, so it is a section of
`kK + ⌊kΘ⌋`: along every prime divisor `G`, `(kK + ⌊kΘ⌋)_G + ord_G χ` is at least
`(kK + ⌊kΩ⌋)_G + ord_G χ - k F_G ≥ 0`. -/
private theorem mem_divisorialSections_clippedBoundary_of_mem
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hV : HasRestrictedLiftingProperty sS sT g f d K Ω q V) (Θ : QDivisor S)
    (hΘ : QDivisor.toRDivisor Θ = restrictedClippedBoundary K Ω q V) {k : ℕ} (hk : 0 < k)
    (hqk : q ∣ k) {D : Divisor S} (hD : Divisor.toQDivisor D = (k : ℤ) • (Ω - Θ))
    {s : RationalFunctions S} (hs : s ∈ V k) :
    s ∈ divisorialSections (k • K + DivisorWithCoeffs.roundDown ((k : ℚ) • Θ)) := by
  obtain ⟨hR, -⟩ := hV
  by_cases h0 : s = 0
  · rw [h0]; exact zero_mem _
  have hs1 := hR.mem_divisorialSections' hqk hs
  obtain ⟨χ, hχ, -⟩ := exists_unit_of_mem_divisorialSections hs1 h0
  rw [← hχ, mem_divisorialSections]
  refine isDivisorialSection_of_unit χ fun G _ => ?_
  subst hχ
  have hMr := mul_toReal_restrictedAsymptoticFixedPart_le hR hk hqk hs G
  have hDG : (D.coeff G : ℚ) = k * (Ω.coeff G - Θ.coeff G) := by
    have := congrArg (fun E : QDivisor S => E.coeff G) hD
    simpa [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub] using this
  have hΘG : (Θ.coeff G : ℝ) = Ω.coeff G -
      (min (ENNReal.ofReal (Ω.coeff G : ℝ)) (restrictedAsymptoticFixedPart K Ω q V G)).toReal := by
    have := congrArg (fun E : RDivisor S => E.coeff G) hΘ
    simpa only [QDivisor.coeff_toRDivisor, coeff_restrictedClippedBoundary] using this
  have hmin := ENNReal.toReal_mono (restrictedAsymptoticFixedPart_ne_top hR G)
    (min_le_right (ENNReal.ofReal (Ω.coeff G : ℝ)) (restrictedAsymptoticFixedPart K Ω q V G))
  set t : ℤ := (seriesDivisor K Ω k).coeff G + G.ord χ with ht
  have hkpos : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hDt : (D.coeff G : ℝ) ≤ t := by
    have hDG' : (D.coeff G : ℝ) = k * (Ω.coeff G - Θ.coeff G : ℝ) := by exact_mod_cast hDG
    rw [hDG', hΘG]
    nlinarith
  have hDt' : D.coeff G ≤ t := by exact_mod_cast hDt
  have hfloor : ⌊(k : ℚ) * Ω.coeff G⌋ = ⌊(k : ℚ) * Θ.coeff G⌋ + D.coeff G := by
    rw [← Int.floor_add_intCast, hDG]
    ring_nf
  have h1 : t = (seriesDivisor K Θ k).coeff G + D.coeff G + G.ord χ := by
    rw [ht, coeff_seriesDivisor, coeff_seriesDivisor, hfloor]
    ring
  change 0 ≤ (seriesDivisor K Θ k).coeff G + G.ord χ
  linarith

/-- Step 2: for sufficiently divisible `k`, `V_k` is the complete section space of
`kK + ⌊kΘ⌋`. -/
private theorem exists_forall_dvd_mem_iff_mem_divisorialSections
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hV : HasRestrictedLiftingProperty sS sT g f d K Ω q V) (Θ : QDivisor S)
    (hΘ : QDivisor.toRDivisor Θ = restrictedClippedBoundary K Ω q V) :
    ∃ N : ℕ, 0 < N ∧ ∀ k : ℕ, 0 < k → N ∣ k → ∀ s : RationalFunctions S,
      s ∈ V k ↔ s ∈ divisorialSections (k • K + DivisorWithCoeffs.roundDown ((k : ℚ) • Θ)) := by
  obtain ⟨N₀, hN₀, D₀, hD₀⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor (Ω - Θ)
  have hq := hV.1.q_pos
  refine ⟨q * N₀, Nat.mul_pos hq hN₀, fun k hk hNk s => ?_⟩
  obtain ⟨j, rfl⟩ := hNk
  have hD : Divisor.toQDivisor (((q * j : ℕ) : ℤ) • D₀) = ((q * N₀ * j : ℕ) : ℤ) • (Ω - Θ) := by
    rw [map_zsmul, hD₀, smul_smul]
    congr 1
    push_cast
    ring
  have hqk : q ∣ q * N₀ * j := (dvd_mul_right q N₀).mul_right j
  exact ⟨mem_divisorialSections_clippedBoundary_of_mem hV Θ hΘ hk hqk hD,
    mem_of_mem_divisorialSections_clippedBoundary hV Θ hΘ hk hqk hD⟩

/-- The rational clause of `F(d)` at the clipped boundary `Θ`: the floor-section algebra of
`K + Θ` is generated over `Γ(T, 𝒪_T)` by finitely many elements. -/
private theorem exists_finset_canonicalRing_eq_closure
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hF : BirationalFiniteGenerationProperty d)
    (hR : IsGradedRestrictedSeries sS sT g f d K Ω q V) (Θ : QDivisor S)
    (hΘ : QDivisor.toRDivisor Θ = restrictedClippedBoundary K Ω q V) :
    ∃ G : Finset (Polynomial ((rationalFunctionsPresheaf S).obj (Opposite.op ⊤))),
      (K.canonicalRing sS hR.isCanonicalDivisor Θ :
          Set (Polynomial ((rationalFunctionsPresheaf S).obj (Opposite.op ⊤)))) =
        Subring.closure (Set.range (relativeConstantsMap f) ∪ ↑G) :=
  (hF.2 S sS T sT f (isQFactorial_of_isGradedRestrictedSeries hR)
    hR.isCanonicalDivisor.topologicalKrullDim_eq hR.isNormalVariety_target hR.isAffine_target
    hR.comp_eq hR.isProjectiveMorphism hR.isBirationalMorphism _
    (fun P => Finsupp.le_def.mp (zero_le_restrictedClippedBoundary hR) P)
    (isRealKltPair_restrictedClippedBoundary hR) K hR.isCanonicalDivisor).1 Θ hΘ

/-- If `ρ : R₀ → R₁` is finite, a subring of `M` generated by the image of `ψ : R₁ → M` and a set
`s` is also generated by the image of `ψ ∘ ρ`, the set `s` and finitely many elements. -/
private theorem exists_finset_closure_range_union_eq {R₀ R₁ M : Type*} [CommRing R₀]
    [CommRing R₁] [CommRing M] (ρ : R₀ →+* R₁) (hρ : ρ.Finite) (ψ : R₁ →+* M) (s : Set M) :
    ∃ E : Finset M, Subring.closure (Set.range ψ ∪ s) =
      Subring.closure (Set.range (ψ.comp ρ) ∪ (s ∪ ↑E)) := by
  classical
  let := ρ.toAlgebra
  obtain ⟨T, hT⟩ := (hρ : Module.Finite R₀ R₁).fg_top
  refine ⟨T.image ψ, le_antisymm (Subring.closure_le.mpr (Set.union_subset ?_ ?_))
    (Subring.closure_le.mpr (Set.union_subset ?_ (Set.union_subset ?_ ?_)))⟩
  · rintro _ ⟨t, rfl⟩
    have ht : t ∈ Submodule.span R₀ (T : Set R₁) := hT ▸ Submodule.mem_top
    induction ht using Submodule.span_induction with
    | mem x hx => exact Subring.subset_closure (Or.inr (Or.inr (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem ψ hx))))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨a, rfl⟩)) hx
  · exact fun x hx => Subring.subset_closure (Or.inr (Or.inl hx))
  · rintro _ ⟨a, rfl⟩; exact Subring.subset_closure (Or.inl ⟨ρ a, rfl⟩)
  · exact fun x hx => Subring.subset_closure (Or.inr hx)
  · intro x hx
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    exact Subring.subset_closure (Or.inl ⟨t, rfl⟩)

/-- The rational clause of `F(d)` at `Θ`, in `ℂ(S)[t]`: the section algebra
`⊕_m H⁰(S, mK + ⌊mΘ⌋) tᵐ` is generated by the constants coming from `Γ(T, 𝒪_T)` and finitely
many polynomials. -/
private theorem exists_finset_sections_eq_subring_closure
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hF : BirationalFiniteGenerationProperty d)
    (hR : IsGradedRestrictedSeries sS sT g f d K Ω q V) (Θ : QDivisor S)
    (hΘ : QDivisor.toRDivisor Θ = restrictedClippedBoundary K Ω q V) :
    ∃ G : Finset (Polynomial (RationalFunctions S)),
      {p : Polynomial (RationalFunctions S) | ∀ m : ℕ, p.coeff m ∈
          divisorialSections (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Θ))} =
        Subring.closure (Set.range (Polynomial.C.comp
          (globalSectionsToRationalFunctions.comp f.appTop.hom)) ∪ ↑G) := by
  classical
  obtain ⟨G₀, hG₀⟩ := exists_finset_canonicalRing_eq_closure hF hR Θ hΘ
  let E := Polynomial.mapEquiv (rationalFunctionsPresheafTopEquiv S)
  refine ⟨G₀.image E, ?_⟩
  have hL : {p : Polynomial (RationalFunctions S) | ∀ m : ℕ, p.coeff m ∈
      divisorialSections (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Θ))} =
      E '' (K.canonicalRing sS hR.isCanonicalDivisor Θ :
        Set (Polynomial ((rationalFunctionsPresheaf S).obj (Opposite.op ⊤)))) := by
    ext p
    constructor
    · intro hp
      refine ⟨E.symm p, fun m => ?_, E.apply_symm_apply p⟩
      change (Polynomial.map (rationalFunctionsPresheafTopEquiv S).symm.toRingHom p).coeff m ∈ _
      rw [Polynomial.coeff_map]
      exact hp m
    · rintro ⟨r, hr, rfl⟩ m
      change (Polynomial.map (rationalFunctionsPresheafTopEquiv S).toRingHom r).coeff m ∈ _
      rw [Polynomial.coeff_map]
      exact hr m
  have hC : E '' Set.range (relativeConstantsMap f) = Set.range (Polynomial.C.comp
      (globalSectionsToRationalFunctions.comp f.appTop.hom)) := by
    rw [← Set.range_comp]
    congr 1
    ext x
    simp [E, relativeConstantsMap, globalSectionsToRationalFunctions_apply]
  rw [hL, hG₀]
  change (((Subring.closure (Set.range (relativeConstantsMap f) ∪ ↑G₀)).map
    (E : Polynomial ((rationalFunctionsPresheaf S).obj (Opposite.op ⊤)) →+*
      Polynomial (RationalFunctions S)) : Subring (Polynomial (RationalFunctions S))) :
        Set (Polynomial (RationalFunctions S))) = _
  rw [RingHom.map_closure, Set.image_union, Finset.coe_image]
  simp only [RingEquiv.coe_toRingHom]
  rw [hC]

/-- `Γ(T, 𝒪_T)` is finite over `A`. -/
private theorem finite_appTop_comp_ΓSpecIso_inv
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hR : IsGradedRestrictedSeries sS sT g f d K Ω q V) :
    (g.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom).Finite := by
  have := hR.isFinite
  exact (((isFinite_iff g).mp this).2 ⊤ (isAffineOpen_top _)).comp
    (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm.surjective)

/-- The constants of `L[t]` coming from the range of `φ : R → L` are those coming from `R`. -/
private theorem range_algebraMap_polynomial_range {R L : Type*} [CommRing R] [CommRing L]
    (φ : R →+* L) :
    Set.range (algebraMap φ.range (Polynomial L)) = Set.range (Polynomial.C.comp φ) := by
  ext p
  constructor
  · rintro ⟨⟨_, a, rfl⟩, rfl⟩; exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩; exact ⟨⟨_, a, rfl⟩, rfl⟩

/-- The section algebra `⊕_m H⁰(S, mK + ⌊mΘ⌋) tᵐ` is generated by the constants coming from
`A` and finitely many polynomials, since `Γ(T, 𝒪_T)` is finite over `A`. -/
private theorem exists_finset_sections_eq_subring_closure_restrictedSeriesBaseMap
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hF : BirationalFiniteGenerationProperty d)
    (hR : IsGradedRestrictedSeries sS sT g f d K Ω q V) (Θ : QDivisor S)
    (hΘ : QDivisor.toRDivisor Θ = restrictedClippedBoundary K Ω q V) :
    ∃ G : Finset (Polynomial (RationalFunctions S)),
      {p : Polynomial (RationalFunctions S) | ∀ m : ℕ, p.coeff m ∈
          divisorialSections (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Θ))} =
        Subring.closure (Set.range (Polynomial.C.comp (restrictedSeriesBaseMap g f)) ∪ ↑G) := by
  classical
  obtain ⟨G₁, hG₁⟩ := exists_finset_sections_eq_subring_closure hF hR Θ hΘ
  obtain ⟨E, hE⟩ := exists_finset_closure_range_union_eq _ (finite_appTop_comp_ΓSpecIso_inv hR)
    (Polynomial.C.comp (globalSectionsToRationalFunctions.comp f.appTop.hom)) ↑G₁
  refine ⟨G₁ ∪ E, ?_⟩
  rw [hG₁, hE, Finset.coe_union]
  rfl

/-! ### The algebra of polynomials with coefficients in a graded family of submodules -/

section CoeffSubalgebra

open Polynomial

variable {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]

/-- The `A`-subalgebra `⊕_m W_m tᵐ` of `L[t]` of the polynomials whose coefficient of `tᵐ` lies
in `W_m`, for a family of `A`-submodules `W_m ⊆ L` with `1 ∈ W_0` and `W_m W_n ⊆ W_{m+n}`. -/
private def coeffSubalgebra (W : ℕ → Submodule A L) (h1 : (1 : L) ∈ W 0)
    (hmul : ∀ m n, ∀ x ∈ W m, ∀ y ∈ W n, x * y ∈ W (m + n)) : Subalgebra A L[X] where
  carrier := {p | ∀ m, p.coeff m ∈ W m}
  mul_mem' {p q} hp hq m := by
    simp only [Set.mem_setOf_eq, coeff_mul] at *
    refine Submodule.sum_mem _ fun x hx => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hx]
    exact hmul _ _ _ (hp _) _ (hq _)
  add_mem' {p q} hp hq m := by
    simp only [Set.mem_setOf_eq, coeff_add] at *
    exact Submodule.add_mem _ (hp m) (hq m)
  algebraMap_mem' a m := by
    simp only [Set.mem_setOf_eq, Polynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h; rw [Algebra.algebraMap_eq_smul_one]; exact Submodule.smul_mem _ a h1
    · exact Submodule.zero_mem _

variable (W : ℕ → Submodule A L) (h1 : (1 : L) ∈ W 0)
    (hmul : ∀ m n, ∀ x ∈ W m, ∀ y ∈ W n, x * y ∈ W (m + n))

private theorem mem_coeffSubalgebra {p : L[X]} :
    p ∈ coeffSubalgebra W h1 hmul ↔ ∀ m, p.coeff m ∈ W m := Iff.rfl

private theorem monomial_mem_coeffSubalgebra {m : ℕ} {x : L} (hx : x ∈ W m) :
    monomial m x ∈ coeffSubalgebra W h1 hmul := fun i => by
  rw [coeff_monomial]; split_ifs with h
  · exact h ▸ hx
  · exact Submodule.zero_mem _

/-- The degree-`m` piece `W_m tᵐ` of `coeffSubalgebra W`. -/
private def coeffGrade (m : ℕ) : Submodule A (coeffSubalgebra W h1 hmul) where
  carrier := {p | ∀ i, i ≠ m → (p : L[X]).coeff i = 0}
  add_mem' hp hq i hi := by simp [hp i hi, hq i hi]
  zero_mem' i _ := by simp
  smul_mem' a p hp i hi := by
    change ((a • p : coeffSubalgebra W h1 hmul) : L[X]).coeff i = 0
    rw [Subalgebra.coe_smul, coeff_smul, hp i hi, smul_zero]

private theorem coe_eq_monomial_of_mem_coeffGrade {m : ℕ} {p : coeffSubalgebra W h1 hmul}
    (hp : p ∈ coeffGrade W h1 hmul m) : (p : L[X]) = monomial m ((p : L[X]).coeff m) := by
  ext i; rw [coeff_monomial]; split_ifs with h
  · rw [h]
  · exact hp i (Ne.symm h)

private theorem gradedMonoid_coeffGrade : SetLike.GradedMonoid (coeffGrade W h1 hmul) where
  one_mem i hi := by
    change (1 : L[X]).coeff i = 0
    rw [coeff_one, if_neg hi]
  mul_mem {m n} p q hp hq i hi := by
    change ((p : L[X]) * q).coeff i = 0
    rw [coe_eq_monomial_of_mem_coeffGrade W h1 hmul hp,
      coe_eq_monomial_of_mem_coeffGrade W h1 hmul hq, monomial_mul_monomial,
      coeff_monomial, if_neg (Ne.symm hi)]

private theorem coeff_coeLinearMap_coeffGrade
    (x : DirectSum ℕ fun m => coeffGrade W h1 hmul m) (i : ℕ) :
    ((DirectSum.coeLinearMap (coeffGrade W h1 hmul) x : coeffSubalgebra W h1 hmul) :
      L[X]).coeff i = ((x i : coeffSubalgebra W h1 hmul) : L[X]).coeff i := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    rw [DirectSum.coeLinearMap_of, DirectSum.of_apply]
    split_ifs with h
    · subst h; rfl
    · simpa using y.2 i (Ne.symm h)
  | add x y hx hy => simp [map_add, Polynomial.coeff_add, hx, hy]

private theorem isInternal_coeffGrade : DirectSum.IsInternal (coeffGrade W h1 hmul) := by
  classical
  constructor
  · intro x y hxy
    change DirectSum.coeLinearMap _ x = DirectSum.coeLinearMap _ y at hxy
    ext m i
    have hx := coeff_coeLinearMap_coeffGrade W h1 hmul x m
    have hy := coeff_coeLinearMap_coeffGrade W h1 hmul y m
    rw [coe_eq_monomial_of_mem_coeffGrade W h1 hmul (x m).2,
      coe_eq_monomial_of_mem_coeffGrade W h1 hmul (y m).2, coeff_monomial,
      coeff_monomial, ← hx, ← hy, hxy]
  · intro p
    refine ⟨∑ m ∈ (p : L[X]).support, DirectSum.of (fun m => coeffGrade W h1 hmul m) m
      ⟨⟨monomial m ((p : L[X]).coeff m), monomial_mem_coeffSubalgebra W h1 hmul (p.2 m)⟩,
        fun i hi => by simp [coeff_monomial, Ne.symm hi]⟩, ?_⟩
    apply Subtype.ext
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (as_sum_support _).symm

/-- The grading of `coeffSubalgebra W` by the degree in `t`. -/
private noncomputable abbrev coeffGradedAlgebra : GradedAlgebra (coeffGrade W h1 hmul) :=
  { gradedMonoid_coeffGrade W h1 hmul, (isInternal_coeffGrade W h1 hmul).chooseDecomposition with }

attribute [local instance] coeffGradedAlgebra

private theorem coe_decompose_coeffGrade (p : coeffSubalgebra W h1 hmul) (n : ℕ) :
    ((DirectSum.decompose (coeffGrade W h1 hmul) p n : coeffSubalgebra W h1 hmul) : L[X]) =
      monomial n ((p : L[X]).coeff n) := by
  rw [coe_eq_monomial_of_mem_coeffGrade W h1 hmul (DirectSum.decompose _ p n).2,
    ← coeff_coeLinearMap_coeffGrade W h1 hmul]
  congr 3
  exact congrArg Subtype.val (DirectSum.Decomposition.left_inv (ℳ := coeffGrade W h1 hmul) p)

private theorem mem_veroneseSubalgebra_coeffGrade_iff {N : ℕ} {p : coeffSubalgebra W h1 hmul} :
    p ∈ veroneseSubalgebra (coeffGrade W h1 hmul) N ↔ ∀ n, ¬ N ∣ n → (p : L[X]).coeff n = 0 := by
  rw [mem_veroneseSubalgebra_iff]
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  rw [← Subtype.coe_inj, coe_decompose_coeffGrade, ZeroMemClass.coe_zero]
  exact monomial_eq_zero_iff _ _

/-- The family `W` with its pieces of degree not divisible by `N` replaced by `0`. -/
private def veroneseFamily (N : ℕ) (m : ℕ) : Submodule A L := if N ∣ m then W m else ⊥

private theorem one_mem_veroneseFamily (h1 : (1 : L) ∈ W 0) (N : ℕ) :
    (1 : L) ∈ veroneseFamily W N 0 := by
  simpa [veroneseFamily] using h1

private theorem mul_mem_veroneseFamily
    (hmul : ∀ m n, ∀ x ∈ W m, ∀ y ∈ W n, x * y ∈ W (m + n)) (N : ℕ) :
    ∀ m n, ∀ x ∈ veroneseFamily W N m, ∀ y ∈ veroneseFamily W N n,
      x * y ∈ veroneseFamily W N (m + n) := by
  intro m n x hx y hy
  unfold veroneseFamily at *
  split_ifs at hx hy with hm hn
  · rw [if_pos (dvd_add hm hn)]; exact hmul _ _ _ hx _ hy
  all_goals first
    | (rw [Submodule.mem_bot] at hx; rw [hx, zero_mul]; exact Submodule.zero_mem _)
    | (rw [Submodule.mem_bot] at hy; rw [hy, mul_zero]; exact Submodule.zero_mem _)

/-- The `N`-th Veronese subalgebra of `⊕_m W_m tᵐ` is `⊕_{N ∣ m} W_m tᵐ`. -/
private theorem map_veroneseSubalgebra_coeffGrade (N : ℕ) :
    (veroneseSubalgebra (coeffGrade W h1 hmul) N).map (coeffSubalgebra W h1 hmul).val =
      coeffSubalgebra (veroneseFamily W N) (one_mem_veroneseFamily W h1 N)
        (mul_mem_veroneseFamily W hmul N) := by
  ext p
  simp only [Subalgebra.mem_map, Subalgebra.coe_val, mem_coeffSubalgebra, veroneseFamily]
  constructor
  · rintro ⟨p, hp, rfl⟩ m
    rw [mem_veroneseSubalgebra_coeffGrade_iff] at hp
    split_ifs with h
    · exact p.2 m
    · rw [hp m h]; exact Submodule.zero_mem _
  · intro hp
    have hW : ∀ m, p.coeff m ∈ W m := fun m => by
      have := hp m
      split_ifs at this with h
      · exact this
      · rw [(Submodule.mem_bot A).mp this]; exact Submodule.zero_mem _
    refine ⟨⟨p, hW⟩, (mem_veroneseSubalgebra_coeffGrade_iff W h1 hmul).mpr fun n hn => ?_, rfl⟩
    have := hp n
    rw [if_neg hn] at this
    exact (Submodule.mem_bot A).mp this

/-- For `N ≥ 1`, `⊕_m W_m tᵐ` is finitely generated over a Noetherian `A` if and only if
`⊕_{N ∣ m} W_m tᵐ` is. -/
private theorem fg_coeffSubalgebra_iff [IsNoetherianRing A] [IsDomain L] {N : ℕ} (hN : 0 < N) :
    (coeffSubalgebra W h1 hmul).FG ↔
      (coeffSubalgebra (veroneseFamily W N) (one_mem_veroneseFamily W h1 N)
        (mul_mem_veroneseFamily W hmul N)).FG := by
  rw [Subalgebra.fg_iff_finiteType, finiteType_iff_veroneseSubalgebra_fg (coeffGrade W h1 hmul) hN,
    ← map_veroneseSubalgebra_coeffGrade W h1 hmul]
  exact ⟨fun h => h.map _, fun h => Subalgebra.fg_of_fg_map _ _ Subtype.val_injective h⟩

/-- A finitely generated `⊕_m W_m tᵐ` is the subring of `L[t]` generated by the constants
`C (algebraMap A L a)` and finitely many polynomials. -/
private theorem exists_finset_eq_subring_closure_of_fg (h : (coeffSubalgebra W h1 hmul).FG) :
    ∃ G : Finset L[X], {p : L[X] | ∀ m, p.coeff m ∈ W m} =
      Subring.closure (Set.range (Polynomial.C.comp (algebraMap A L)) ∪ ↑G) := by
  obtain ⟨G, hG⟩ := h
  refine ⟨G, ?_⟩
  have := congrArg (fun B : Subalgebra A L[X] => (B.toSubring : Set L[X])) hG
  simp only [Algebra.adjoin_eq_ring_closure] at this
  exact this.symm

/-- **Changing the degree-zero piece.** If `W'_m = W_m` for `m ≠ 0` and `W'_0 ⊆ W_0` with `W_0`
finitely generated, then `⊕_m W'_m tᵐ` is finitely generated over a Noetherian `A` whenever
`⊕_m W_m tᵐ` is: the latter is a finite module over the former (Artin–Tate). -/
private theorem fg_coeffSubalgebra_of_le_zero [IsNoetherianRing A] (W' : ℕ → Submodule A L)
    (h1' : (1 : L) ∈ W' 0) (hmul' : ∀ m n, ∀ x ∈ W' m, ∀ y ∈ W' n, x * y ∈ W' (m + n))
    (h0 : W' 0 ≤ W 0) (hpos : ∀ m, m ≠ 0 → W' m = W m) (hfg : (W 0).FG)
    (hW : (coeffSubalgebra W h1 hmul).FG) : (coeffSubalgebra W' h1' hmul').FG := by
  classical
  have hle : coeffSubalgebra W' h1' hmul' ≤ coeffSubalgebra W h1 hmul := fun p hp m => by
    by_cases hm : m = 0
    · subst hm; exact h0 (hp 0)
    · rw [← hpos m hm]; exact hp m
  let R' := coeffSubalgebra W' h1' hmul'
  let R := coeffSubalgebra W h1 hmul
  let : Algebra R' R := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower A R' R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let c : W 0 →ₗ[A] R :=
    { toFun := fun x => ⟨Polynomial.C (x : L), fun m => by
        rw [Polynomial.coeff_C]; split_ifs with h
        · subst h; exact x.2
        · exact Submodule.zero_mem _⟩
      map_add' := fun x y => by ext1; simp
      map_smul' := fun a x => by ext1; simp [Polynomial.smul_C] }
  have : Module.Finite A (W 0) := Module.Finite.iff_fg.mpr hfg
  obtain ⟨T, hT⟩ : (Submodule.map c ⊤).FG := (Module.Finite.fg_top (R := A) (M := W 0)).map c
  rw [← Subalgebra.fg_top] at hW ⊢
  refine fg_of_fg_of_fg A R' R hW ⟨insert 1 T, ?_⟩ (Subalgebra.inclusion_injective hle)
  refine eq_top_iff.mpr fun p _ => ?_
  have hp0 : c ⟨(p : L[X]).coeff 0, p.2 0⟩ ∈ Submodule.span R' (↑(insert 1 T) : Set R) := by
    refine Submodule.span_le_restrictScalars A R' _ ?_
    refine Submodule.span_mono (s := (T : Set R))
      (by rw [Finset.coe_insert]; exact Set.subset_insert _ _) ?_
    rw [hT]; exact ⟨_, Submodule.mem_top, rfl⟩
  have hrest : p - c ⟨(p : L[X]).coeff 0, p.2 0⟩ ∈ Submodule.span R' (↑(insert 1 T) : Set R) := by
    have hmem : (p : L[X]) - Polynomial.C ((p : L[X]).coeff 0) ∈ R' := fun m => by
      rw [Polynomial.coeff_sub, Polynomial.coeff_C]
      split_ifs with h
      · subst h; rw [sub_self]; exact Submodule.zero_mem _
      · rw [sub_zero, hpos m h]; exact p.2 m
    have : p - c ⟨(p : L[X]).coeff 0, p.2 0⟩ = (⟨_, hmem⟩ : R') • (1 : R) := by
      ext1
      change _ = (_ : L[X]) * 1
      rw [mul_one]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  simpa using add_mem hrest hp0

end CoeffSubalgebra

/-- The ring of regular functions `Γ(S, 𝒪_S) ⊆ K(S)` of the source of a graded restricted series
is a finitely generated module over the image of `A`: by Stein, `Γ(S, 𝒪_S) = f^* Γ(T, 𝒪_T)`, and
`Γ(T, 𝒪_T)` is finite over `A`. -/
private theorem exists_finset_globalSections_eq_span
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hR : IsGradedRestrictedSeries sS sT g f d K Ω q V) :
    ∃ E : Finset (RationalFunctions S), ∀ x : RationalFunctions S,
      x ∈ (globalSectionsToRationalFunctions (X := S)).range ↔
        x ∈ Submodule.span (restrictedSeriesBaseMap g f).range (E : Set (RationalFunctions S)) := by
  classical
  have : IsProper f := isProper_of_isProjectiveMorphism f hR.isProjectiveMorphism
  have hiso := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    sS sT hR.isNormalVariety_source.1 hR.isNormalVariety_target f hR.isBirationalMorphism).1 ⊤
  have hsurj : Function.Surjective f.appTop.hom :=
    (ConcreteCategory.bijective_of_isIso (f.app ⊤)).2
  let ρ := g.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom
  have hρ : ρ.Finite := finite_appTop_comp_ΓSpecIso_inv hR
  let := ρ.toAlgebra
  obtain ⟨T₀, hT₀⟩ := (hρ : Module.Finite A Γ(T, ⊤)).fg_top
  let φ : Γ(T, ⊤) →+* RationalFunctions S := globalSectionsToRationalFunctions.comp f.appTop.hom
  refine ⟨T₀.image φ, fun x => ⟨?_, fun hx => ?_⟩⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := hsurj s
    have ht : t ∈ Submodule.span A (T₀ : Set Γ(T, ⊤)) := hT₀ ▸ Submodule.mem_top
    change φ t ∈ _
    induction ht using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem φ hy))
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy =>
      rw [Algebra.smul_def, map_mul]
      exact Submodule.smul_mem _ (⟨restrictedSeriesBaseMap g f a, a, rfl⟩ :
        (restrictedSeriesBaseMap g f).range) hy
  · induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      exact ⟨_, rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul r y _ hy =>
      obtain ⟨_, a, rfl⟩ := r
      exact mul_mem ⟨_, rfl⟩ hy

/-- The `N`-th Veronese subalgebra of `⊕_m V_m tᵐ`, for `N` as in step 2, is finitely generated
over the image of `A`: in positive degrees its pieces are the section spaces of `kK + ⌊kΘ⌋`,
whose algebra is finitely generated by the rational clause of `F(d)`. -/
private theorem fg_coeffSubalgebra_veroneseFamily
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hF : BirationalFiniteGenerationProperty d)
    (hR : IsGradedRestrictedSeries sS sT g f d K Ω q V) (Θ : QDivisor S)
    (hΘ : QDivisor.toRDivisor Θ = restrictedClippedBoundary K Ω q V) {N : ℕ} (hN0 : 0 < N)
    (hN : ∀ k : ℕ, 0 < k → N ∣ k → ∀ s : RationalFunctions S,
      s ∈ V k ↔ s ∈ divisorialSections (k • K + DivisorWithCoeffs.roundDown ((k : ℚ) • Θ))) :
    (coeffSubalgebra (veroneseFamily V N) (one_mem_veroneseFamily V hR.one_mem N)
      (mul_mem_veroneseFamily V hR.mul_mem N)).FG := by
  classical
  have hq := hR.q_pos
  have := hR.isNoetherianRing
  have := isNoetherianRing_range (restrictedSeriesBaseMap g f)
  have : IsDomain (RationalFunctions S) :=
    (rationalFunctionsEquivFunctionField S).toMulEquiv.isDomain
  obtain ⟨G, hG⟩ := exists_finset_sections_eq_subring_closure_restrictedSeriesBaseMap hF hR Θ hΘ
  set P := Subring.closure (Set.range (Polynomial.C.comp (restrictedSeriesBaseMap g f)) ∪ ↑G)
    with hP
  have hz : ∀ B : QDivisor S, (0 : ℕ) • K + DivisorWithCoeffs.roundDown (((0 : ℕ) : ℚ) • B) = 0 :=
    fun B => by
      ext Q
      change (seriesDivisor K B 0).coeff Q = 0
      simp [coeff_seriesDivisor]
  -- membership in `P` of a polynomial and of its coefficients
  have hmemP : ∀ p : Polynomial (RationalFunctions S), p ∈ P ↔ ∀ m : ℕ, p.coeff m ∈
      divisorialSections (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Θ)) := fun p => by
    rw [← SetLike.mem_coe, ← hG]; rfl
  have hmon : ∀ {m : ℕ} {x : RationalFunctions S}, x ∈
      divisorialSections (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Θ)) →
      Polynomial.monomial m x ∈ P := fun {m x} hx => (hmemP _).mpr fun i => by
    rw [Polynomial.coeff_monomial]; split_ifs with h
    · exact h ▸ hx
    · exact zero_mem _
  have hmulW : ∀ m n : ℕ, ∀ x ∈
      divisorialSections (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Θ)), ∀ y ∈
      divisorialSections (n • K + DivisorWithCoeffs.roundDown ((n : ℚ) • Θ)), x * y ∈
      divisorialSections ((m + n) • K + DivisorWithCoeffs.roundDown (((m + n : ℕ) : ℚ) • Θ)) := by
    intro m n x hx y hy
    have := (hmemP _).mp (mul_mem (hmon hx) (hmon hy)) (m + n)
    rwa [Polynomial.monomial_mul_monomial, Polynomial.coeff_monomial_same] at this
  let W : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S) := fun m =>
    { carrier := divisorialSections (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Θ))
      add_mem' := fun hx hy => add_mem hx hy
      zero_mem' := zero_mem _
      smul_mem' := fun c x hx => by
        obtain ⟨_, a, rfl⟩ := c
        have hc : Polynomial.C (restrictedSeriesBaseMap g f a) ∈ P :=
          Subring.subset_closure (Or.inl ⟨a, rfl⟩)
        have := (hmemP _).mp (mul_mem hc (hmon hx)) m
        rwa [Polynomial.C_mul_monomial, Polynomial.coeff_monomial_same] at this }
  have hW : ∀ m x, x ∈ W m ↔
      x ∈ divisorialSections (m • K + DivisorWithCoeffs.roundDown ((m : ℚ) • Θ)) :=
    fun _ _ => Iff.rfl
  have h1 : (1 : RationalFunctions S) ∈ W 0 := by
    have := (hmemP 1).mp (one_mem P) 0
    rwa [Polynomial.coeff_one_zero] at this
  have hmul : ∀ m n, ∀ x ∈ W m, ∀ y ∈ W n, x * y ∈ W (m + n) := hmulW
  have hfgW : (coeffSubalgebra W h1 hmul).FG := by
    refine ⟨G, Subalgebra.ext fun p => ?_⟩
    rw [← Subalgebra.mem_toSubring, Algebra.adjoin_eq_ring_closure,
      range_algebraMap_polynomial_range, mem_coeffSubalgebra]
    exact hmemP p
  have hfgN := (fg_coeffSubalgebra_iff W h1 hmul hN0).mp hfgW
  obtain ⟨E, hE⟩ := exists_finset_globalSections_eq_span hR
  refine fg_coeffSubalgebra_of_le_zero (veroneseFamily W N) _ _ (veroneseFamily V N) _ _ ?_ ?_
    ?_ hfgN
  · intro s hs
    simp only [veroneseFamily, if_pos (dvd_zero N)] at hs ⊢
    have := hR.mem_divisorialSections 0 (dvd_zero q) s hs
    rw [hz] at this
    rw [hW, hz]
    exact this
  · intro m hm
    simp only [veroneseFamily]
    split_ifs with h
    · ext s
      exact hN m (Nat.pos_of_ne_zero hm) h s
    · rfl
  · simp only [veroneseFamily, if_pos (dvd_zero N)]
    refine ⟨E, Submodule.ext fun x => ?_⟩
    rw [hW, hz, mem_divisorialSections_zero_iff, hE]

/-- Step 3: the restricted algebra `⊕_m V_m tᵐ` is finitely generated over `A`. -/
private theorem exists_finset_eq_subring_closure
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hF : BirationalFiniteGenerationProperty d)
    (hV : HasRestrictedLiftingProperty sS sT g f d K Ω q V) (Θ : QDivisor S)
    (hΘ : QDivisor.toRDivisor Θ = restrictedClippedBoundary K Ω q V)
    (hN : ∃ N : ℕ, 0 < N ∧ ∀ k : ℕ, 0 < k → N ∣ k → ∀ s : RationalFunctions S,
      s ∈ V k ↔ s ∈ divisorialSections (k • K + DivisorWithCoeffs.roundDown ((k : ℚ) • Θ))) :
    ∃ G : Finset (Polynomial (RationalFunctions S)),
      {p : Polynomial (RationalFunctions S) | ∀ m, p.coeff m ∈ V m} =
        Subring.closure
          (Set.range (Polynomial.C.comp (restrictedSeriesBaseMap g f)) ∪ ↑G) := by
  obtain ⟨N, hN0, hN⟩ := hN
  have hR := hV.1
  have := hR.isNoetherianRing
  have := isNoetherianRing_range (restrictedSeriesBaseMap g f)
  have : IsDomain (RationalFunctions S) :=
    (rationalFunctionsEquivFunctionField S).toMulEquiv.isDomain
  obtain ⟨G, hG⟩ := exists_finset_eq_subring_closure_of_fg V hR.one_mem hR.mul_mem
    ((fg_coeffSubalgebra_iff V hR.one_mem hR.mul_mem hN0).mpr
      (fg_coeffSubalgebra_veroneseFamily hF hR Θ hΘ hN0 hN))
  rw [← range_algebraMap_polynomial_range]
  exact ⟨G, hG⟩

/-- **Restricted-boundary rationality from the lifting inequality.** Assume `F(d)` and let `V`
be a graded restricted series with the lifting property. Then the clipped boundary
`Θ = Ω - Ω ∧ F` is rational; for every sufficiently divisible `k > 0`,
`V_k = H⁰(S, 𝒪_S(k(K + Θ)))` inside `K(S)` (multiplication by `σ_{k(Ω - Θ)}`, which is the
function `1`); and `⊕_m V_m tᵐ ⊆ K(S)[t]` is generated as a ring by the image of `A` and
finitely many elements. -/
@[mmp "thm_fourfold_restricted_boundary_rationality"]
public theorem exists_qDivisor_eq_restrictedClippedBoundary_of_hasRestrictedLiftingProperty
    {A : Type} [CommRing A] [Algebra ℂ A] {S T : Scheme.{0}}
    [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g : T ⟶ Spec (.of A)} {f : S ⟶ T}
    {d : ℕ} {K : Divisor S} {Ω : QDivisor S} {q : ℕ}
    {V : ℕ → Submodule (restrictedSeriesBaseMap g f).range (RationalFunctions S)}
    (hF : BirationalFiniteGenerationProperty d)
    (hV : HasRestrictedLiftingProperty sS sT g f d K Ω q V) :
    ∃ Θ : QDivisor S, QDivisor.toRDivisor Θ = restrictedClippedBoundary K Ω q V ∧
      (∃ N : ℕ, 0 < N ∧ ∀ k : ℕ, 0 < k → N ∣ k → ∀ s : RationalFunctions S,
        s ∈ V k ↔ s ∈ divisorialSections (k • K + DivisorWithCoeffs.roundDown ((k : ℚ) • Θ))) ∧
      ∃ G : Finset (Polynomial (RationalFunctions S)),
        {p : Polynomial (RationalFunctions S) | ∀ m, p.coeff m ∈ V m} =
          Subring.closure
            (Set.range (Polynomial.C.comp (restrictedSeriesBaseMap g f)) ∪ ↑G) := by
  obtain ⟨Θ, hΘ⟩ := exists_qDivisor_eq_restrictedClippedBoundary hF hV
  have hN := exists_forall_dvd_mem_iff_mem_divisorialSections hV Θ hΘ
  exact ⟨Θ, hΘ, hN, exists_finset_eq_subring_closure hF hV Θ hΘ hN⟩

end MMP.Fourfold

end
