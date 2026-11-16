module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Model
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Residue.Basic
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.SmoothComponentsDecomposition
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.RestrictedModel
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.IntegralRetract
public import MMP.AlgebraicGeometry.Singularities.Snc.RelativeSncRestrictClopen

/-!
# The fractional logarithmic complex of a root of `𝒪_V(NB)` degenerates at `E₁`

Let `V` be a smooth projective complex variety, `S + B` a simple normal crossing divisor with `S`
reduced and every coefficient of the `ℚ`-divisor `B = ∑ bⱼ Bⱼ` in `(0, 1)`, and `𝓛` a line bundle
with `𝓛^N ≅ 𝒪_V(NB)`. The root datum gives `𝓛⁻¹` a flat logarithmic connection `∇` with residue
`bⱼ` along `Bⱼ`: under `𝓛^{-N} ≅ 𝒪_V(-NB) ⊆ 𝒪_V` the connection `∇^{⊗N}` is the exterior
derivative. This connection preserves `C^• = Ω^•_V(log (S + Supp B)) ⊗ 𝓛⁻¹(-S)` and squares
to zero, so `C^•` with differential `∇` is a complex, and its residue along `Bⱼ` is `bⱼ`. The
Hodge-to-de Rham spectral sequence of `C^•` degenerates at `E₁`:
`dim ℍ^k(V, C^•) = ∑_{p+q=k} dim H^q(V, C^p)` for every `k`.

Write `D = S + Supp B`, `𝓛 = 𝒪_V(M)` for a divisor `M`, and let `ψ` be the rational function
with `NM = NB + div ψ`, so that `𝒪_V(NM) ≅ 𝒪_V(NB)` is multiplication by `ψ`. On
`U' = V ∖ (D ∪ Supp M)` the function `ψ` is a unit, and `C^p` is the subsheaf of the forms on
`U'` whose sections are, locally, sums `∑ aᵢ ηᵢ` with `aᵢ` a section of `𝒪_V(-M)` and `ηᵢ` a
section of `Ω^p_V(log D)(-S)`. The connection is `∇ω = dω - N⁻¹ (dψ/ψ) ∧ ω`. Locally,
`a = g` with `div g = M` and `g^N/ψ = v ∏ xⱼ^{N bⱼ}`, `v` a unit, so
`∇g = g ⊗ (∑ bⱼ dxⱼ/xⱼ + dv/(Nv))`, and the residue along `Bⱼ` is `bⱼ`.

## Main results

* `MMP.Mori.Divisor.finrank_hypercohomology_eq_sum_of_fractionalLogComplex`: the complex
  `C^•` with the connection `∇` exists and has residue `bⱼ` along `Bⱼ`, and every such complex
  is `E₁`-degenerate, as the equality of dimensions.

## Implementation notes

* The `ℚ`-divisor `B` is given by the integral divisor `Bn = NB`, with `0 ≤ Bn < N`
  coefficientwise; `D = S + Supp Bn` is reduced and relative snc over `Spec ℂ`
  (`MMP.Mori.Divisor.IsRelativeSNC`), which makes `S` reduced, the components of `S` and `B`
  distinct, and the coefficients `bⱼ = Bn(Bⱼ)/N` of `B` lie in `(0, 1)`.
* On the smooth variety `V` every line bundle is `𝒪_V(M)` for a divisor `M`, and an isomorphism
  `𝒪_V(NM) ≅ 𝒪_V(NB)` is multiplication by a rational function `ψ` with `NM = NB + div ψ`; the
  root datum `(𝓛, 𝓛^N ≅ 𝒪_V(NB))` is given as `(M, ψ)`. The unit `u` of `𝒪(U')` is `ψ`
  restricted to `U'`.
* The complex `C^•` is a complex `K` of sheaves of `π⁻¹𝒪_{Spec ℂ}`-modules, that is, of
  `ℂ`-vector spaces, whose terms are `𝒪_V`-modules `F p` read over `π⁻¹𝒪`, together with an
  injective `𝒪_V`-linear map `ι` from `F p` into the forms on `U'`, which are the sections of
  `Ω^p_U` (`U = V ∖ D`) over the open `U' ⊆ U`. The image of `ι` is `𝒪_V(-M) · Ω^p_V(log D)(-S)`,
  with `Ω^p_V(log D)(-S)` given by `MMP.Mori.Divisor.relativeLogForms` for the ideal of `S`, and
  the differential of `K` is carried by `ι` to `∇`. These conditions determine `K` up to unique
  isomorphism. The identity for `∇` is multiplied by `N u` so that it holds without dividing.
  The existence of such a `K` is the statement that `∇` preserves `C^•` and that `∇² = 0`.
* The residue of `∇` along a component `E` of `Supp B` is stated through a local equation `t`
  of `E` on an affine open `W` that meets no other component of `D`: for every section `a` of
  `C^0` on `W`, the form `N ∇a - Bn(E) · a · dt/t` is, locally on `W`, a sum `∑ aᵢ fᵢ dhᵢ` with
  `aᵢ` a section of `𝒪_V(-M)` and `fᵢ, hᵢ` regular functions. This says that the residue of
  `∇` along `E` is `Bn(E)/N = b_E`. The identity is multiplied by `t` so that it holds without
  dividing.
* Degeneration at `E₁` of the spectral sequence of the stupid filtration is stated as the
  equality `dim ℍ^k(V, K) = ∑_{p ≤ k} dim H^{k-p}(V, K^p)` over `ℂ`. All these spaces are finite
  dimensional because `V` is projective, so the equality is equivalent to the vanishing of all
  differentials `d_r`, `r ≥ 1`. Hypercohomology is the right derived functor of global sections,
  read over `Γ(Spec ℂ, ⊤) = ℂ`, as in
  `MMP.Mori.Divisor.exists_isRelativeSNC_model_finrank_hypercohomology_eq`.

## References

* [P. Deligne, L. Illusie,
  *Relèvements modulo p² et décomposition du complexe de de Rham*][DeligneIllusie1987]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

attribute [local instance] HasDerivedCategory.standard

namespace MMP.Mori.Divisor

/-- **The fractional logarithmic complex degenerates at `E₁`.** Let `π : V ⟶ Spec ℂ` be smooth
projective of relative dimension `n` and `D = S + Supp B` a relative snc divisor, with `S`
reduced and `B = Bn/N` a `ℚ`-divisor with coefficients in `(0, 1)`. Let `𝒪_V(M)` be an `N`-th
root of `𝒪_V(Bn)` through `NM = Bn + div ψ`, and let `u` be `ψ` on `U' = V ∖ (D ∪ Supp M)`.
Call a complex `K` of sheaves of `ℂ`-vector spaces on `V` a model of `C^•` if its terms are
`𝒪_V`-modules `F p`, embedded by `ι` into the forms on `U'` with image
`𝒪_V(-M) · Ω^p_V(log D)(-S)`, and its differential is `∇ = d - N⁻¹ (du/u) ∧`. Then a model
exists, and its connection `∇` has residue `Bn(E)/N` along every component `E` of `Supp Bn`;
and every model satisfies `dim_ℂ ℍ^k(V, K) = ∑_{p ≤ k} dim_ℂ H^{k-p}(V, K^p)` for every `k`. -/
@[mmp "lem_mmp_lc_bpf_fractional_log_complex"]
public theorem finrank_hypercohomology_eq_sum_of_fractionalLogComplex (n : ℕ) {V : Scheme.{0}}
    (π : V ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n π] (hπ : IsProjective π)
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (D : Divisor V) (hD : D.IsRelativeSNC n π) (S Bn : Divisor V) (hS : 0 ≤ S)
    (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1)
    (N : ℕ) (hN : 0 < N) (hB : ∀ E, 0 ≤ Bn E ∧ Bn E < N)
    (M : Divisor V) (ψ : (RationalFunctions V)ˣ) (hψ : (N : ℤ) • M = Bn + principalDivisor ψ)
    (u : Γ(V, (D.supp ⊔ M.supp).compl))
    (hu : (toRationalFunctionsPresheaf V).app (op (D.supp ⊔ M.supp).compl) u =
      (rationalFunctionsPresheaf V).map (homOfLE le_top).op
        ((rationalFunctionsPresheafTopEquiv V).symm ψ)) :
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
    -- the conditions pinning `K` as `C^•` with the connection `∇`, through `F`, `e` and `ι`
    let IsC : ∀ (K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
      (F : ℕ → V.Modules),
      (∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)) →
      (∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) → (A.piece (p : ℤ)).val.obj (op (O W))) →
      Prop := fun K F e ι =>
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
              (rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op a =
                (toRationalFunctionsPresheaf V).app (op ((W' : V.Opens) ⊓ U')) (g i)) ∧
            (∀ i, η i ∈ relativeLogForms n π D hD S.suppIdeal p (W' : V.Opens)) ∧
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
    -- the residue of `∇` along a component `E` of `Supp B` is `b_E = Bn E / N`: on an affine `W`
    -- meeting no other component of `D`, with `E = {t = 0}`, the form `N ∇a - Bn(E) a dt/t` is
    -- a regular `1`-form with coefficients in `𝒪_V(-M)`, multiplied out by `t`
    let HasRes : ∀ (K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
      (F : ℕ → V.Modules),
      (∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)) →
      (∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) → (A.piece (p : ℤ)).val.obj (op (O W))) →
      Prop := fun K F e ι =>
      ∀ E : PrimeDivisor V, Bn E ≠ 0 → ∀ (W : V.affineOpens) (t : Γ(V, (W : V.Opens))),
        E.idealSheaf.ideal W = Ideal.span {t} →
        (∀ E' ∈ D.support, E' ≠ E → ∀ y ∈ (W : V.Opens), y ∉ E'.support) →
        ∀ (x : (K.X 0).val.obj (op (W : V.Opens))), ∀ y ∈ (W : V.Opens),
          ∃ (W' : V.affineOpens) (h : (W' : V.Opens) ≤ W), y ∈ (W' : V.Opens) ∧
          ∃ (m : ℕ) (g : Fin m → Γ(V, (W' : V.Opens) ⊓ U')) (f h' : Fin m → Γ(V, (W' : V.Opens))),
            (∀ i, ∃ a ∈ (-M).divisorialSubmodule (W' : V.Opens),
              (rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op a =
                (toRationalFunctionsPresheaf V).app (op ((W' : V.Opens) ⊓ U')) (g i)) ∧
            let r := (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right U' h))).op
            let tW' := res W' (V.presheaf.map (homOfLE h).op t)
            B.structureMap (op (O W')) tW' *
                (N • B.incl ((1 : ℕ) : ℤ) ((A.piece ((1 : ℕ) : ℤ)).val.map r
                  (ι 1 W ((e 1).hom.val.app (op W) ((K.d 0 1).val.app (op W) x))))) -
              Bn E • (B.incl ((0 : ℕ) : ℤ) ((A.piece ((0 : ℕ) : ℤ)).val.map r
                  (ι 0 W ((e 0).hom.val.app (op W) x))) * B.incl 1 (dF (O W') tW')) =
            B.structureMap (op (O W')) tW' *
              ∑ i, B.structureMap (op (O W')) (U.ι.app ((W' : V.Opens) ⊓ U') (g i) * res W' (f i)) *
                B.incl 1 (dF (O W') (res W' (h' i)))
    -- `C^•` with `∇` exists and has these residues, and its spectral sequence degenerates at `E₁`:
    -- `dim ℍ^k(V, C^•) = ∑_{p+q=k} dim H^q(V, C^p)`
    (∃ K F e ι, IsC K F e ι ∧ HasRes K F e ι) ∧
    ∀ K F e ι, IsC K F e ι →
    ∀ k : ℕ,
      Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
          (H ⟨K.extend ComplexShape.embeddingUpNat, 0,
            CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
        ∑ p ∈ Finset.range (k + 1), Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
          (H ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (K.X p), 0,
            (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
              HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩ ((k - p : ℕ) : ℤ)) := by
  intro U U' A B Ω O res dF uW H IsC HasRes
  refine ⟨?_, ?_⟩
  · obtain ⟨cc, hcc, hst⟩ := MMP.FourfoldProofs.FractionalLogComplexProof.exists_modelData n π D hD S
      M hS Bn hSB N hN (fun E => (hB E).1) ψ hψ u hu
    have hloc : MMP.FourfoldProofs.FractionalLogComplexProof.LocMon n π D hD S M :=
      fun p W ω hω y hy =>
        MMP.FourfoldProofs.FractionalLogComplexProof.Cond.exists_monSet (hω := hω) (hy := hy)
    have hcu :=
      MMP.FourfoldProofs.FractionalLogComplexProof.δ_mul_δ_eq_zero_of_mul_natCast_mul_eq_one
        π D M N hcc
    exact ⟨MMP.FourfoldProofs.FractionalLogComplexProof.cCx n π D hD S M u cc hst hloc hcu,
      MMP.FourfoldProofs.FractionalLogComplexProof.cMod n π D hD S M, fun _ => Iso.refl _,
      fun p W x => MMP.FourfoldProofs.FractionalLogComplexProof.tr π D M (p : ℤ) W x.1,
      MMP.FourfoldProofs.FractionalLogComplexProof.isCModel_cCx n π D hD S M N u cc hcc hst hloc hcu,
      MMP.FourfoldProofs.FractionalLogComplexProof.residueSpec n π D hD S Bn hS hSB N hN
        (fun E => (hB E).1) M ψ hψ u cc hu hcc hst hloc hcu⟩
  · open MMP.FourfoldProofs.FractionalLogComplexProof in
    have hdeg : FracDegeneration n π D hD S M N u := by
      obtain ⟨ι₀, _, Ui, hcl, hdisj, hcov, hint⟩ := componentsDecomp n π hπ
      have hDU : ∀ i, IsRelativeSNC n ((Ui i).ι ≫ π) (restrictDivisor (Ui i) D) := fun i => by
        have := hint i
        exact isRelativeSNC_restrictDivisor n π D hD (Ui i) (hcl i).isClosed
      refine componentsReduction n π D hD S M N u hπ ι₀ Ui hcl hdisj hcov hDU
        fun i K F e ι' hK => ?_
      have := hint i
      have := compactSpace_of_isClosed (Ui i) (hcl i).isClosed
      have hφ := ι_componentGenericPoint_notMem_supp (Ui i) (principalDivisor ψ)
      exact retract_of_isIntegral n ((Ui i).ι ≫ π)
        (isProjective_opens_ι_comp (Ui i) π hπ (hcl i).isClosed)
        (restrictDivisor (Ui i) D) (hDU i) (restrictDivisor (Ui i) S) (restrictDivisor (Ui i) Bn)
        (restrictDivisor_nonneg (Ui i) hS)
        (fun E => by simp only [restrictDivisor_apply]; exact hSB _) N hN
        (fun E => by simp only [restrictDivisor_apply]; exact hB _)
        (restrictDivisor (Ui i) M) (pullbackRationalFunction (Ui i).ι ψ hφ)
        (zsmul_restrictDivisor_eq_add_principalDivisor (Ui i) hψ hφ)
        (restrictSection (Ui i) D M u)
        (toRationalFunctionsPresheaf_restrictSection (Ui i) D M ψ hφ u hu) K F e ι' hK
    exact hdeg

end MMP.Mori.Divisor
