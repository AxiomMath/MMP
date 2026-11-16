module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.TraceMap.Complex
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Retract.Degeneration

/-!
# The retract argument for the fractional logarithmic complex

Let `π : V ⟶ Spec ℂ` carry the data of the fractional logarithmic complex
`C^• = 𝒪_V(-M) · Ω^•_V(log D)(-S)` with the connection `∇ = d - N⁻¹ (du/u) ∧`, and let
`g : V' ⟶ V` be a finite surjective cover by an integral smooth projective variety with a relative
simple normal crossing divisor `S'`. If the pull-back `θ ↦ g^*θ / z` lands in
`Ω^•_{V'}(log S')(-S')`, the trace `ω' ↦ [k(V') : k(V)]⁻¹ Tr(z ω')` lands in `C^•`, and the
rational identities `i ∇ = d i`, `r d = ∇ r`, `r i = 1` hold, then every model `K` of `C^•` is a
retract of `g_* Ω^•_{V'}(log S')(-S')` in the category of complexes of sheaves of
`π⁻¹𝒪`-modules: the two maps are morphisms of complexes `K ⟶ g_* Ω^•_{V'}(log S')(-S') ⟶ K`
whose composite is the identity. Degeneration at `E₁` of the logarithmic Hodge-to-de Rham
spectral sequence of `V'` passes to the direct image along the affine morphism `g`, and from there
to its retracts.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.retract_of_cover`: every model of `C^•` is a retract of
  `g_* Ω^•_{V'}(log S')(-S')`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.retractSpec`: the retract argument
  (`MMP.FourfoldProofs.FractionalLogComplexProof.RetractSpec`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

/-- **Every model of `C^•` is a retract of `g_* Ω^•_{V'}(log S')(-S')`.** Under the pull-back and
trace maps of `IMapSpec` and `RMapSpec` and the rational identities of `RatCompat`, for every model
`K` of `C^•` there are morphisms of complexes of sheaves of `π⁻¹𝒪`-modules
`i : K ⟶ g_* Ω^•_{V'}(log S')(-S')` and `r : g_* Ω^•_{V'}(log S')(-S') ⟶ K` with `i ≫ r = 𝟙`. -/
theorem retract_of_cover (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V) (N : ℕ)
    (u : Γ(V, cU' D M)) (ψK : V.functionField) [Nonempty (cU D)] [Nonempty (cU' D M)]
    {V' : Scheme.{0}} (g : V' ⟶ V) [IsFinite g] [Surjective g] [IsIntegral V']
    [SmoothOfRelativeDimension n (g ≫ π)]
    (S' : MMP.Mori.Divisor V') (hS' : S'.IsRelativeSNC n (g ≫ π)) [Nonempty (cU S')]
    (z : V'.functionField) (hψ : V.germToFunctionField (cU' D M) u = ψK)
    (hI : IMapSpec n π D hD S M g S' hS' z) (hR : RMapSpec n π D hD S M g S' hS' z)
    (hRC : letI := MMP.Mori.functionFieldAlgebra π
      letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
      letI := MMP.Mori.functionFieldMapAlgebra g
      haveI := MMP.Mori.isScalarTower_functionFieldMap π g
      haveI := finiteDimensional_functionFieldMap g
      haveI := isSeparable_functionFieldMap π g
      RatCompat ℂ V.functionField V'.functionField N ψK z)
    (K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
    (F : ℕ → V.Modules)
    (e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p))
    (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W)))
    (hK : IsCModel n π D hD S M N u K F e ι) :
    ∃ (i : K ⟶ ((relDirectImage g π).mapHomologicalComplex _).obj
        (MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal))
      (r : ((relDirectImage g π).mapHomologicalComplex _).obj
        (MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal) ⟶ K),
      i ≫ r = 𝟙 K :=
  ⟨iCx n π D hD S M N u g S' hS' z hK hI ψK hψ hRC,
    rCx n π D hD S M N u g S' hS' z hK hR ψK hψ hRC,
    iCx_comp_rCx n π D hD S M N u g S' hS' z hK hI hR ψK hψ hRC⟩

/-- **The retract argument.** If `V` and `V'` are projective over `ℂ`, then under the pull-back and
trace maps of `IMapSpec` and `RMapSpec` and the rational identities of `RatCompat`, the fractional
logarithmic complex `C^•` degenerates at `E₁` (`FracDegeneration`): every model of `C^•` is a
retract of the direct image `g_* Ω^•_{V'}(log S')(-S')`. -/
theorem retractSpec (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S M : MMP.Mori.Divisor V) (N : ℕ)
    (u : Γ(V, cU' D M)) (ψK : V.functionField) [Nonempty (cU D)] [Nonempty (cU' D M)]
    {V' : Scheme.{0}} (g : V' ⟶ V) [IsFinite g] [Surjective g] [IsIntegral V']
    [SmoothOfRelativeDimension n (g ≫ π)]
    (S' : MMP.Mori.Divisor V') (hS' : S'.IsRelativeSNC n (g ≫ π)) [Nonempty (cU S')]
    (z : V'.functionField) :
    RetractSpec n π D hD S M N u ψK g S' hS' z := by
  intro hπ hgπ hψ hI hR hRC
  exact fracDegeneration_of_retract n π D hD S M N u g S' hS' hπ hgπ fun K F e ι hK =>
    retract_of_cover n π D hD S M N u ψK g S' hS' z hψ hI hR hRC K F e ι hK

end MMP.FourfoldProofs.FractionalLogComplexProof
