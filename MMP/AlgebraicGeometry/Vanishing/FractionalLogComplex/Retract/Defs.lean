module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.PullbackMap.Defs
public import MMP.RingTheory.Kaehler.FormsTrace
public import MMP.AlgebraicGeometry.FunctionField.FiniteCover

/-!
# The fractional logarithmic complex as a retract of the logarithmic complex of a cover

Let `π : V ⟶ Spec ℂ` carry the data of the fractional logarithmic complex
`C^• = 𝒪_V(-M) · Ω^•_V(log D)(-S)` with the connection `∇ = d - N⁻¹ (du/u) ∧`, and let
`g : V' ⟶ V` be a finite surjective cover by an integral smooth projective variety, on which the
reduced inverse image `S'` of `S` is a relative simple normal crossing divisor and `z^N = g^*ψ`.
The maps `i(θ) = g^*θ / z` and `r(ω') = [k(V') : k(V)]⁻¹ Tr(z ω')` exhibit `C^•` as a retract of
`g_* Ω^•_{V'}(log S')(-S')`, so the degeneration at `E₁` of the logarithmic Hodge-to-de Rham
spectral sequence of `V'` passes to `C^•`.

Sections of all these sheaves are forms on dense opens, determined by their rational forms, so
the two maps are pinned by rational identities, stated here; the sheaf maps and the comparison of
hypercohomology are built from them.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.RMapSpec`: the trace map carries
  `Ω^p_{V'}(log S')(-S')` into `C^p`, with the rational form `[k(V') : k(V)]⁻¹ Tr(z ω')`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.RatCompat`: the rational identities `i ∇ = d i`,
  `r d = ∇ r` and `r i = 1`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.IsCModel`: a complex `K` with `F`, `e`, `ι` is a model
  of `C^•` with the differential `∇`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.FracDegeneration`: every model of `C^•` satisfies
  `dim ℍ^k(V, K) = ∑_{p ≤ k} dim H^{k-p}(V, K^p)`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.RetractSpec`: the retract argument, from the
  pull-back map (`MMP.FourfoldProofs.FractionalLogComplexProof.IMapSpec`), the trace map and the
  rational identities to the degeneration.

## Implementation notes

* `IsCModel` and `FracDegeneration` are the predicate `IsC` and the degeneration clause of
  `MMP.Mori.Divisor.finrank_hypercohomology_eq_sum_of_fractionalLogComplex`, written with the
  opens `MMP.FourfoldProofs.FractionalLogComplexProof.cU`, `cU'` and `OO`, which unfold to the opens
  `U`, `U'` and `O W` of that statement.
* The rational identities are stated in the exterior algebra of `Ω_{K/ℂ}`, where the wedge with
  `dψ` is a product; the connection is multiplied out by `N ψ`, as in `IsCModel`.
* The relation `z^N = g^*ψ`, the identification of `u` with `ψ` on `U'`, and the hypotheses on
  `D`, `S`, `Bn`, `M` that make `RMapSpec` and `RatCompat` hold are not part of these statements:
  they are the hypotheses of the theorems proving them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

attribute [local instance] HasDerivedCategory.standard

namespace MMP.FourfoldProofs.FractionalLogComplexProof

/-- **The trace map `ω' ↦ [k(V') : k(V)]⁻¹ Tr(z ω')` lands in `C^p`.** For every open `W` of `V`
and every section `θ'` of `Ω^p_{V'}(log S')(-S')` over `g⁻¹ W`, there is a form `θ` on
`U ∩ W ∩ U'` satisfying `Cond`, a section of `C^p` over `W`, whose rational form, on every
non-empty affine open of `U ∩ W ∩ U'`, is `[k(V') : k(V)]⁻¹ Tr(z θ')`, `θ'` read on any non-empty
affine open of `(V' ∖ S') ∩ g⁻¹ W`. -/
def RMapSpec (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V)
    [Nonempty (cU D)]
    {V' : Scheme.{0}} (g : V' ⟶ V) [IsFinite g] [Surjective g] [IsIntegral V']
    [SmoothOfRelativeDimension n (g ≫ π)]
    (S' : MMP.Mori.Divisor V') (hS' : S'.IsRelativeSNC n (g ≫ π)) [Nonempty (cU S')]
    (z : V'.functionField) : Prop :=
  letI := MMP.Mori.functionFieldAlgebra π
  letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
  letI := MMP.Mori.functionFieldMapAlgebra g
  haveI := MMP.Mori.isScalarTower_functionFieldMap π g
  haveI := finiteDimensional_functionFieldMap g
  haveI := isSeparable_functionFieldMap π g
  ∀ (p : ℕ) (W : V.Opens)
    (θ' : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU S').ι ≫ g ≫ π)).piece
      (p : ℤ)).val.obj (op ((cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W)))),
    θ' ∈ MMP.Mori.Divisor.relativeLogForms n (g ≫ π) S' hS' S'.suppIdeal p (g ⁻¹ᵁ W) →
    ∃ θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W)),
      Cond n π D hD S M p W θ ∧
      ∀ (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W)
        [Nonempty (O : (cU D).toScheme.Opens)]
        (O' : (cU S').toScheme.affineOpens)
        (hO' : (O' : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W))
        [Nonempty (O' : (cU S').toScheme.Opens)],
        openFormsMap (cU D) π p (ratForm ((cU D).ι ≫ π) p O
            ((((cU D).ι ≫ π).relativeDifferentialForms (p : ℤ)).presheaf.map
              (homOfLE hO).op θ)) =
          ((Module.finrank V.functionField V'.functionField : V.functionField))⁻¹ •
            formsTrace ℂ V.functionField V'.functionField p
              (z • openFormsMap (cU S') (g ≫ π) p (ratForm ((cU S').ι ≫ g ≫ π) p O'
                ((((cU S').ι ≫ g ≫ π).relativeDifferentialForms (p : ℤ)).presheaf.map
                  (homOfLE hO').op θ')))

/-- **The rational identities of the retract.** For a finite separable extension `L / K` of
fields over `k`, `ψ ∈ K`, `z ∈ L` and `c = [L : K]`, write `∇β = dβ - N⁻¹ (dψ/ψ) ∧ β` for forms
of `K`, multiplied out: `β'` is `∇β` when `N ψ β' = N ψ dβ - dψ ∧ β`. Then

* `i ∇ = d i`: `d(z⁻¹ β) = z⁻¹ ∇β`;
* `r d = ∇ r`: `c⁻¹ Tr(z dγ) = ∇(c⁻¹ Tr(z γ))` for forms `γ` of `L`;
* `r i = 1`: `c⁻¹ Tr(z z⁻¹ β) = β`.

These hold when `z^N = ψ`, `ψ ≠ 0`, `N ≠ 0` and `k` has characteristic zero. -/
def RatCompat (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (N : ℕ) (ψ : K) (z : L) : Prop :=
  (∀ (p : ℕ) (β : ⋀[K]^p (Ω[K⁄k])) (β' : ⋀[K]^(p + 1) (Ω[K⁄k])),
    N • (ψ • (β' : ExteriorAlgebra K Ω[K⁄k])) =
      N • (ψ • (KaehlerDifferential.deRhamDifferential (A := k) p β :
        ExteriorAlgebra K Ω[K⁄k])) -
        ExteriorAlgebra.ι K (KaehlerDifferential.D k K ψ) * (β : ExteriorAlgebra K Ω[K⁄k]) →
    KaehlerDifferential.deRhamDifferential (A := k) p
        (z⁻¹ • KaehlerDifferential.mapExteriorPower k K L p β) =
      z⁻¹ • KaehlerDifferential.mapExteriorPower k K L (p + 1) β') ∧
  (∀ (p : ℕ) (γ : ⋀[L]^p (Ω[L⁄k])),
    N • (ψ • (((Module.finrank K L : K)⁻¹ • formsTrace k K L (p + 1)
        (z • KaehlerDifferential.deRhamDifferential (A := k) p γ) : ⋀[K]^(p + 1) (Ω[K⁄k])) :
          ExteriorAlgebra K Ω[K⁄k])) =
      N • (ψ • (KaehlerDifferential.deRhamDifferential (A := k) p
          ((Module.finrank K L : K)⁻¹ • formsTrace k K L p (z • γ)) :
        ExteriorAlgebra K Ω[K⁄k])) -
        ExteriorAlgebra.ι K (KaehlerDifferential.D k K ψ) *
          (((Module.finrank K L : K)⁻¹ • formsTrace k K L p (z • γ) : ⋀[K]^p (Ω[K⁄k])) :
            ExteriorAlgebra K Ω[K⁄k])) ∧
  (∀ (p : ℕ) (β : ⋀[K]^p (Ω[K⁄k])),
    (Module.finrank K L : K)⁻¹ •
        formsTrace k K L p (z • z⁻¹ • KaehlerDifferential.mapExteriorPower k K L p β) = β)

/-- **A model of `C^•` with the connection `∇`**: the predicate `IsC` of
`MMP.Mori.Divisor.finrank_hypercohomology_eq_sum_of_fractionalLogComplex`. The terms of the
complex `K` of sheaves of `π⁻¹𝒪`-modules are the `𝒪_V`-modules `F p` (through `e`), embedded by
the injective `𝒪_V`-linear maps `ι` into the forms on `U ∩ W ∩ U'` with image
`𝒪_V(-M) · Ω^p_V(log D)(-S)`, and the differential of `K` is carried by `ι` to
`∇ = d - N⁻¹ (du/u) ∧`, multiplied out by `N u`. -/
def IsCModel (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V) (N : ℕ)
    (u : Γ(V, cU' D M))
    (K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
    (F : ℕ → V.Modules)
    (e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p))
    (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W))) : Prop :=
  let U : V.Opens := D.supp.compl
  let U' : V.Opens := (D.supp ⊔ M.supp).compl
  let A := Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ π)
  let B := A.toPresheafGradedAlgebra
  let Ω := Scheme.Hom.deRhamComplex (U.ι ≫ π)
  let O : V.Opens → U.toScheme.Opens := fun W => U.ι ⁻¹ᵁ (W ⊓ U')
  let res : ∀ W : V.Opens, Γ(V, W) → Γ(U.toScheme, O W) := fun W a =>
    U.ι.app (W ⊓ U') (V.presheaf.map (homOfLE inf_le_left).op a)
  let dF : ∀ W : U.toScheme.Opens, Γ(U.toScheme, W) → (A.piece 1).val.obj (op W) := fun W a =>
    (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials (U.ι ≫ π))).val.app
      (op W) ((Scheme.Hom.universalRelativeDerivation (U.ι ≫ π)).d (X := op W) a)
  let uW : ∀ W : V.Opens, Γ(U.toScheme, O W) := fun W =>
    U.ι.app (W ⊓ U') (V.presheaf.map (homOfLE inf_le_right).op u)
  -- `ι` is an injective `𝒪_V`-linear map of sheaves `C^p ⟶ j_*Ω^p_{U'}`
  (∀ (p : ℕ) W, Function.Injective (ι p W)) ∧
  (∀ (p : ℕ) W x y, ι p W (x + y) = ι p W x + ι p W y) ∧
  (∀ (p : ℕ) W (r : V.ringCatSheaf.obj.obj (op W)) x,
    B.incl (p : ℤ) (ι p W (r • x)) =
      B.structureMap (op (O W)) (res W r) * B.incl (p : ℤ) (ι p W x)) ∧
  (∀ (p : ℕ) (W W' : V.Opens) (h : W' ≤ W) x,
    ι p W' ((F p).val.map (homOfLE h).op x) =
      (A.piece (p : ℤ)).val.map (homOfLE (Scheme.Hom.preimage_mono _
        (inf_le_inf_right U' h))).op (ι p W x)) ∧
  -- its image is `𝒪_V(-M) · Ω^p_V(log D)(-S)`
  (∀ (p : ℕ) W ω, ω ∈ Set.range (ι p W) ↔ ∀ x ∈ W, ∃ (W' : V.affineOpens)
      (h : (W' : V.Opens) ≤ W), x ∈ (W' : V.Opens) ∧
      ∃ (m : ℕ) (g : Fin m → Γ(V, (W' : V.Opens) ⊓ U'))
        (η : Fin m → (A.piece (p : ℤ)).val.obj (op (U.ι ⁻¹ᵁ (W' : V.Opens)))),
        (∀ i, ∃ a ∈ (-M).divisorialSubmodule (W' : V.Opens),
          (MMP.Mori.rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op a =
            (MMP.Mori.toRationalFunctionsPresheaf V).app (op ((W' : V.Opens) ⊓ U')) (g i)) ∧
        (∀ i, η i ∈ MMP.Mori.Divisor.relativeLogForms n π D hD S.suppIdeal p (W' : V.Opens)) ∧
        B.incl (p : ℤ) ((A.piece (p : ℤ)).val.map (homOfLE (Scheme.Hom.preimage_mono _
            (inf_le_inf_right U' h))).op ω) =
          ∑ i, B.structureMap (op (O W')) (U.ι.app ((W' : V.Opens) ⊓ U') (g i)) *
            B.incl (p : ℤ) ((A.piece (p : ℤ)).val.map (homOfLE (Scheme.Hom.preimage_mono _
              inf_le_left)).op (η i))) ∧
  -- the differential of `K` is `∇ = d - (1/N) dψ/ψ ∧ -`, multiplied out by `N ψ`
  (∀ (p : ℕ) W (x : (K.X p).val.obj (op W)),
    N • (B.structureMap (op (O W)) (uW W) *
        B.incl ((p + 1 : ℕ) : ℤ) (ι (p + 1) W ((e (p + 1)).hom.val.app (op W)
          ((K.d p (p + 1)).val.app (op W) x)))) =
      N • (B.structureMap (op (O W)) (uW W) *
        B.incl ((p + 1 : ℕ) : ℤ) ((Ω.d p (p + 1)).val.app (op (O W))
          (ι p W ((e p).hom.val.app (op W) x)))) -
      B.incl 1 (dF (O W) (uW W)) * B.incl (p : ℤ) (ι p W ((e p).hom.val.app (op W) x)))

/-- **`E₁`-degeneration for every model of `C^•`**: the degeneration clause of
`MMP.Mori.Divisor.finrank_hypercohomology_eq_sum_of_fractionalLogComplex`,
`dim_ℂ ℍ^k(V, K) = ∑_{p ≤ k} dim_ℂ H^{k-p}(V, K^p)` for every `k` and every model `K`. -/
def FracDegeneration (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V) (N : ℕ)
    (u : Γ(V, cU' D M)) : Prop :=
  -- `ℍ^j(V, L)` over `Γ(Spec ℂ, ⊤) = ℂ`, for a bounded below complex of `π⁻¹𝒪`-modules
  let H : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) →
      ℤ → ModuleCat.{0} Γ(Spec (CommRingCat.of ℂ), ⊤) := fun L j =>
    let Γd := (SheafOfModules.evaluation.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))
        (op ⊤)).rightDerivedFunctorPlus
    let Mj := (DerivedCategory.homologyFunctor _ j).obj
      (DerivedCategory.Plus.ι.obj (Γd.obj (DerivedCategory.Plus.Q.obj L)))
    (ModuleCat.restrictScalars.{0} (show Γ(Spec (CommRingCat.of ℂ), ⊤) →+*
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj
          (Spec (CommRingCat.of ℂ)).sheaf).obj.obj (op ⊤) from
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} π.base).unit.app
        (Spec (CommRingCat.of ℂ)).sheaf).hom.app (op ⊤)).hom)).obj Mj
  ∀ K F e ι, IsCModel n π D hD S M N u K F e ι →
  ∀ k : ℕ,
    Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (H ⟨K.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
      ∑ p ∈ Finset.range (k + 1), Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (H ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (K.X p), 0,
          (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
            HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩ ((k - p : ℕ) : ℤ))

/-- **The retract argument.** Let `V` be integral and smooth over `ℂ`, `g : V' ⟶ V` a finite
surjective cover by an integral smooth `V'` with a relative snc divisor `S'`, and `z` a rational
function of `V'`. If `V` and `V'` are projective over `ℂ`, `u` is `ψ` on `U'`, the pull-back
`θ ↦ g^*θ / z` lands in `Ω^•_{V'}(log S')(-S')` (`IMapSpec`), the trace map
`ω' ↦ [k(V') : k(V)]⁻¹ Tr(z ω')` lands in `C^•` (`RMapSpec`) and the rational identities
`i ∇ = d i`, `r d = ∇ r`, `r i = 1` hold (`RatCompat`), then every model of `C^•` is a retract of
`g_* Ω^•_{V'}(log S')(-S')` as a complex of sheaves of `π⁻¹𝒪`-modules, and degenerates at `E₁`
because `Ω^•_{V'}(log S')(-S')` does (`FracDegeneration`). -/
def RetractSpec (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V) (N : ℕ)
    (u : Γ(V, cU' D M)) (ψK : V.functionField) [Nonempty (cU D)] [Nonempty (cU' D M)]
    {V' : Scheme.{0}} (g : V' ⟶ V) [IsFinite g] [Surjective g] [IsIntegral V']
    [SmoothOfRelativeDimension n (g ≫ π)]
    (S' : MMP.Mori.Divisor V') (hS' : S'.IsRelativeSNC n (g ≫ π)) [Nonempty (cU S')]
    (z : V'.functionField) : Prop :=
  letI := MMP.Mori.functionFieldAlgebra π
  letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
  letI := MMP.Mori.functionFieldMapAlgebra g
  haveI := MMP.Mori.isScalarTower_functionFieldMap π g
  haveI := finiteDimensional_functionFieldMap g
  haveI := isSeparable_functionFieldMap π g
  IsProjective π → IsProjective (g ≫ π) →
  V.germToFunctionField (cU' D M) u = ψK →
  IMapSpec n π D hD S M g S' hS' z →
  RMapSpec n π D hD S M g S' hS' z →
  RatCompat ℂ V.functionField V'.functionField N ψK z →
  FracDegeneration n π D hD S M N u

end MMP.FourfoldProofs.FractionalLogComplexProof
