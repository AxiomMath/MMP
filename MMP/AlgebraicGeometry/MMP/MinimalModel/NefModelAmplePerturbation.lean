module

public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.ChowForm.FibreChowForm
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTrace
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor

/-!
# An ample perturbation makes a fixed nef weak model a log minimal model with ample adjoint

Let `π : X ⟶ Z` be a projective morphism of projective complex varieties, with `X` normal and
`ℚ`-factorial, and let `H_1, …, H_s` be Cartier divisors on `X` whose classes form a basis of
`N¹(X/Z)`. Let `X = X₀ ⤏ X₁ ⤏ ⋯ ⤏ X_n = Y` be a finite program of elementary steps over `Z` between
projective varieties: each step is a divisorial contraction or a flip of a
`(K_{X_i} + Δ_i)`-negative extremal contraction `X_i ⟶ W_i` over `Z`, for some effective klt
boundary `Δ_i` on `X_i`, with `W_i` projective; the final model `Y` is `ℚ`-factorial. Let `B` be a
real klt boundary on `X` such that the composite `φ : X ⤏ Y` is a nef weak model of `(X, B)` over
`Z`. Suppose that for all sufficiently small `u ∈ ℝ^s` the perturbed boundary `B_u = B + ∑ uᵢ Hᵢ`
is effective and klt on `X`, and `φ_* B_u` is effective and klt on `Y`. Then for every `ε > 0`
there is `u` with all `|uᵢ| < ε` such that `(Y, φ_* B_u)` is a log minimal model of `(X, B_u)` over
`Z` and `K_Y + φ_* B_u` is ample over `Z`.

## Main results

* `MMP.Fourfold.exists_isRealLogMinimalModel_isRelativelyAmple_of_isNefWeakModel`

## Implementation notes

* The program is written out with the indexing of `MMP.Fourfold.RelativeDltProgram`:
  `X₀ = X`, `X_{i+1} = Y i` (`MMP.Fourfold.modelSeq`), structure morphisms
  `MMP.Fourfold.modelStr` over `ℂ` and `MMP.Fourfold.modelMap` over `Z`. Step `i < n` is a
  `(K_i + Δ_i)`-negative extremal contraction `f_i : X_i ⟶ W_i`
  (`MMP.Flips.IsNegativeExtremalContraction`) over `Z` by `g_i`, followed by
  `f_i⁺ : X_{i+1} ⟶ W_i` and the birational map `φ_i : X_i ⤏ X_{i+1}`: either `f_i` is
  divisorial and `f_i⁺` an isomorphism, or `(f_i⁺, φ_i)` is the flip of the small `f_i`
  (`MMP.Flips.IsFlip`).
* The composites `ψ_i : X ⤏ X_i` are given with `ψ_0 = id` and `ψ_{i+1} = φ_i ∘ ψ_i`, the
  composition being computed on representing partial isomorphisms (`Scheme.PartialIso.trans`);
  the program's composite is `φ = ψ_n`.
* The classes of the `Hᵢ` form a basis of `N¹(X/Z)`: every `ℝ`-Cartier divisor is numerically
  equivalent over `Z` to some `∑ uᵢ Hᵢ` (`MMP.Flips.IsNumericallyEquivalentOver`), and
  `∑ uᵢ Hᵢ ≡_Z 0` only for `u = 0`.
* On `Y` the canonical divisor is `φ_* K_X` and the boundary is `φ_* B_u`, as in
  `MMP.Fourfold.IsNefWeakModel`; a nef weak model is a birational contraction, so `Y` has no
  prime divisor exceptional over `X` and `φ_* B_u` is the boundary of
  `MMP.Fourfold.IsRealLogMinimalModel`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.31
* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC], Section 2
-/

@[expose] public noncomputable section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open CategoryTheory AlgebraicGeometry TopologicalSpace

open MMP.Fourfold MMP.Mori MMP.Flips

namespace MMP.NefModelAmplePerturbation

universe u

/-! ### Strict transforms on a common resolution -/

section StrictTransform

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- A scheme separated over `Spec k` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- **The strict transform on a resolution.** For a proper birational morphism `p : W ⟶ X` of
normal varieties with inverse `h` and a prime divisor `P` of `X`, `h` is defined at `η_P` by some
`h'`, and `h'(η_P)` is the generic point of a prime divisor `E` of `W` with `p(η_E) = η_P`. -/
private theorem exists_strictTransform {k : Type u} [Field k] {X W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hX : IsNormalVariety k sX) (p : W ⟶ X)
    (h : X.RationalMap W) [IsProper p] (hWnp : IsNormalVariety k (p ≫ sX))
    (hpb : IsBirationalMorphism p) (hinv : RationalMap.IsInverse p.toRationalMap h)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ (E : MMP.Mori.PrimeDivisor W) (h' : X.PartialMap W) (hP : P.genericPoint ∈ h'.domain),
      h'.toRationalMap = h ∧ E.genericPoint = h'.hom ⟨P.genericPoint, hP⟩ ∧
      p E.genericPoint = P.genericPoint ∧ IsIso (p.stalkMap E.genericPoint) := by
  have := hX.1
  have := hWnp.1
  have : IsDominant p := hpb.isDominant
  have := isSeparated_toTerminal sX
  have : IsSeparated p := IsSeparated.of_comp p sX
  obtain ⟨E, heq, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hWnp hpb P
  obtain ⟨e, he1, he2⟩ := id hinv
  have hhp : h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
    rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq p e he1, Iso.inv_hom_id_assoc, Category.comp_id]
  obtain ⟨h', hh'P, hh'⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p h hhp
      P.coheight_genericPoint.le)
  have hpw : p (h'.hom ⟨P.genericPoint, hh'P⟩) = P.genericPoint :=
    apply_hom_eq_of_isInverse p e he1 h' (hh'.trans he2.symm) hh'P
  exact ⟨E, h', hh'P, hh', Oai4C1.eq_of_map_eq_genericPoint hpb heq hpw, heq, hiso⟩

/-- **The inverse of a resolution sends a prime divisor to its strict transform.** -/
private theorem exists_transformPrimeDivisor_eq_some_of_isInverse {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hX : IsNormalVariety k sX) (p : W ⟶ X) (h : X.RationalMap W) [IsProper p]
    (hWnp : IsNormalVariety k (p ≫ sX)) (hpb : IsBirationalMorphism p)
    (hinv : RationalMap.IsInverse p.toRationalMap h) (P : MMP.Mori.PrimeDivisor X) :
    ∃ E : MMP.Mori.PrimeDivisor W, MMP.Mori.RationalMap.transformPrimeDivisor h P = some E ∧
      p E.genericPoint = P.genericPoint ∧ IsIso (p.stalkMap E.genericPoint) := by
  have := hX.1
  have := hWnp.1
  have := isSeparated_toTerminal (p ≫ sX)
  obtain ⟨E, h', hh'P, hh', hwE, heq, hiso⟩ := exists_strictTransform hX p h hWnp hpb hinv P
  exact ⟨E, MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq h' hh' hh'P hwE, heq, hiso⟩

end StrictTransform

/-! ### Transforms under a composite with a morphism -/

section CompHom

variable {X V Y : Scheme.{u}} [IsReduced X] [IsReduced V] [IsSeparated (V ↘ ⊤_ Scheme)]
  [IsSeparated (Y ↘ ⊤_ Scheme)]

private theorem transformPrimeDivisor_compHom {h : X.RationalMap V} {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor V} (hP : MMP.Mori.RationalMap.transformPrimeDivisor h P = some P')
    (q : V ⟶ Y) :
    MMP.Mori.RationalMap.transformPrimeDivisor (h.compHom q) P =
      MMP.Mori.RationalMap.transformPrimeDivisor (X := V) q.toRationalMap P' := by
  obtain ⟨hdef, -⟩ := MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hP
  obtain ⟨g', hg'P, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  have hη := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP g' hg' hg'P
  have hrep : (g'.compHom q).toRationalMap = h.compHom q := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg']
  refine Option.ext fun F => ?_
  rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff]
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · rw [MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h1 (g'.compHom q) hrep hg'P,
      hη]
    rfl
  · refine MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq (g'.compHom q) hrep hg'P ?_
    rw [← h1, hη]
    rfl

end CompHom

/-! ### Rational maps and morphisms -/

section RationalMaps

/-- If `h` is an inverse of the morphism `p : Y ⟶ X` and `h ∘ r = s` for morphisms `r`, `s`, then
`r = s ∘ p`. -/
private theorem eq_comp_of_isInverse_of_compHom_eq {X Y T : Scheme.{u}} [IsReduced X]
    [IsReduced Y] [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (T ↘ ⊤_ Scheme)] {p : Y ⟶ X}
    {h : X.RationalMap Y} (hinv : RationalMap.IsInverse p.toRationalMap h) (r : Y ⟶ T)
    (s : X ⟶ T) (hrs : h.compHom r = s.toRationalMap) : r = p ≫ s := by
  obtain ⟨e, he1, he2⟩ := id hinv
  have key : (e.iso.inv ≫ e.source.ι) ≫ r = e.target.ι ≫ s := by
    have h1 : (e.symm.toPartialMap.compHom r).toRationalMap = s.toRationalMap := by
      rw [Scheme.RationalMap.compHom_toRationalMap]
      change e.symm.toRationalMap.compHom r = _
      rw [he2, hrs]
    exact (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)
      (f := e.symm.toPartialMap.compHom r) (g := s)).mp
        (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)
  have hpe : e.source.ι ≫ p = e.iso.hom ≫ e.target.ι :=
    source_ι_comp_eq_of_toRationalMap_eq p e he1
  haveI : IsDominant e.source.ι := AlgebraicGeometry.Opens.isDominant_ι e.dense_source
  refine ext_of_isDominant_of_isSeparated (T ↘ ⊤_ Scheme) (Limits.terminal.hom_ext _ _)
    e.source.ι ?_
  rw [← Category.assoc e.source.ι p s, hpe, Category.assoc, ← key]
  simp

end RationalMaps

/-! ### Intersection numbers through normalizations -/

section Normalization

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_curveNormalization (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
  let p := C.ι ≫ sX
  have : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  have : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  have : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        have : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        have : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le⟩

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- For a presentation `D = ∑ⱼ rⱼ Lⱼ`, the number `∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)` is a value of `D · C`. -/
private theorem isRIntersectionNumber_sum_degreeOn (D : RDivisor X) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX) :
    IsRIntersectionNumber k sX D r L C (∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hL j)) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_curveNormalization C
  refine ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), hD, fun j => ?_, rfl⟩
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  have : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := (hL j).isInvertibleModule_divisorialSheaf
  exact (Oai4C1.Negativity.degreeOn_normalization C hν hdim _).symm

end Normalization

/-! ### The relative Kleiman criterion: nef plus ample is ample -/

section Classes

variable {k : Type} [Field k] {X Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (f : Y ⟶ X)

/-- Linear forms on `N₁(Y/X)` which agree on the classes of the contracted curves are equal. -/
private theorem linearMap_ext_relativeClass
    {φ ψ : RelativeNumericalCurveClasses sY f →ₗ[ℝ] ℝ}
    (h : ∀ (C : ProperCurve sY) (hC : C.IsContractedBy f),
      φ (C.relativeClass f hC) = ψ (C.relativeClass f hC)) : φ = ψ := by
  have hsp : relativeOneCycles sY f = Submodule.span ℝ
      ((fun C => Finsupp.single C (1 : ℝ)) '' {C : ProperCurve sY | C.IsContractedBy f}) := by
    rw [relativeOneCycles, Finsupp.supported_eq_span_single]
  have key : ∀ (x : OneCycle ℝ sY) (hx : x ∈ Submodule.span ℝ
      ((fun C => Finsupp.single C (1 : ℝ)) '' {C : ProperCurve sY | C.IsContractedBy f})),
      φ (relativeNumericalClass sY f ⟨x, hsp ▸ hx⟩) =
        ψ (relativeNumericalClass sY f ⟨x, hsp ▸ hx⟩) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨C, hC, rfl⟩ := hx
      exact h C hC
    | zero =>
      have : (⟨0, hsp ▸ Submodule.zero_mem _⟩ : relativeOneCycles sY f) = 0 := rfl
      rw [this, map_zero, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, hsp ▸ Submodule.add_mem _ hx hy⟩ : relativeOneCycles sY f) =
          ⟨x, hsp ▸ hx⟩ + ⟨y, hsp ▸ hy⟩ := rfl
      rw [this, map_add, map_add, map_add, ihx, ihy]
    | smul c x hx ih =>
      have : (⟨c • x, hsp ▸ Submodule.smul_mem _ c hx⟩ : relativeOneCycles sY f) =
          c • ⟨x, hsp ▸ hx⟩ := rfl
      rw [this, map_smul, map_smul, map_smul, ih]
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  obtain ⟨Z, hZ⟩ := Z
  exact key Z (hsp ▸ hZ)

variable [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The linear form `z ↦ (z · M)` on `N₁(Y/X)` of a Cartier divisor `M`, through `𝒪_Y(M)`. -/
private noncomputable def degFun (M : Divisor Y) (hM : M.IsCartier) :
    RelativeNumericalCurveClasses sY f →ₗ[ℝ] ℝ :=
  haveI := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := hM.isInvertibleModule_divisorialSheaf
  RelativeNumericalCurveClasses.degree sY f M.divisorialSheaf

/-- On the class of a contracted curve `C`, the form of `M` is `deg_C 𝒪_Y(M)`. -/
private theorem degFun_relativeClass (M : Divisor Y) (hM : M.IsCartier) (C : ProperCurve sY)
    (hC : C.IsContractedBy f) :
    degFun sY f M hM (C.relativeClass f hC) = (M.degreeOn k sY C.ι C.dim_le hM : ℝ) := by
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := hM.isInvertibleModule_divisorialSheaf
  exact OneCycle.degree_cycle ℝ _ C

/-- The linear form `z ↦ (z · ∑ⱼ rⱼ Lⱼ)` of a presentation. -/
private noncomputable def presFun {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) : RelativeNumericalCurveClasses sY f →ₗ[ℝ] ℝ :=
  ∑ j, r j • degFun sY f (L j) (hL j)

/-- On the class of a contracted curve `C`, the form of `∑ⱼ rⱼ Lⱼ` is `∑ⱼ rⱼ deg_C 𝒪_Y(Lⱼ)`. -/
private theorem presFun_relativeClass {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (C : ProperCurve sY) (hC : C.IsContractedBy f) :
    presFun sY f r L hL (C.relativeClass f hC) =
      ∑ j, r j * ((L j).degreeOn k sY C.ι C.dim_le (hL j) : ℝ) := by
  simp [presFun, degFun_relativeClass]

/-- Two presentations of the same `ℝ`-divisor give the same linear form on `N₁(Y/X)`. -/
private theorem presFun_eq_of_eq {m m' : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (r' : Fin m' → ℝ) (L' : Fin m' → Divisor Y)
    (hL' : ∀ j, (L' j).IsCartier)
    (h : ∑ j, r j • Divisor.toRDivisor (L j) = ∑ j, r' j • Divisor.toRDivisor (L' j)) :
    presFun sY f r L hL = presFun sY f r' L' hL' := by
  refine linearMap_ext_relativeClass sY f fun C hC => ?_
  rw [presFun_relativeClass, presFun_relativeClass]
  exact (IsRIntersectionNumber.eq_and_linear k sY C).1 _ r L r' L' _ _
    (isRIntersectionNumber_sum_degreeOn _ r L hL rfl C)
    (isRIntersectionNumber_sum_degreeOn _ r' L' hL' h C)

end Classes

section Ample

variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- If `𝒪_Y(W) ≅ 𝒪_Y(E)` and `W` is `f`-ample, then `𝒪_Y(E)` is `f`-ample. -/
private theorem isRelativelyAmple_sheaf_of_iso {f : Y ⟶ X} {W : Divisor Y}
    (hW : IsRelativelyAmpleCartier f W) {E : Y.CartierDivisor}
    (e : W.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E) :
    MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf E) := by
  have h := IsRelativelyAmpleCartier.isRelativelyAmple hW
  have := hW.1.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  exact ⟨V, hV, hyV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).mp
      hamp⟩

/-- If `𝒪_Y(W) ≅ 𝒪_Y(E)` and `𝒪_Y(E)` is `f`-ample, the Cartier divisor `W` is `f`-ample. -/
private theorem isRelativelyAmpleCartier_of_iso {f : Y ⟶ X} [QuasiCompact f] {D : Divisor Y}
    (hD : D.IsCartier) {E : Y.CartierDivisor}
    (e : D.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E)
    (h : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf E)) :
    IsRelativelyAmpleCartier f D := by
  have := hD.isInvertibleModule_divisorialSheaf
  refine MMP.Flips.isRelativelyAmpleCartier_of_isRelativelyAmple hD fun y => ?_
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  exact ⟨V, hV, hyV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso
      e.symm)).mp hamp⟩

end Ample

section Kleiman

variable {k : Type} [Field k] {X Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (f : Y ⟶ X)
  [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]

local notation "I" => RelativeNumericalCurveClasses.intersectionNumber

/-- A Cartier divisor `W` on an integral `Y` has `𝒪_Y(W) ≅ 𝒪_Y(E)` for a Cartier divisor `E`,
whose linear form on `N₁(Y/X)` is that of `W`. -/
private theorem exists_cartierDivisor_degFun [IsIntegral Y] (W : Divisor Y) (hW : W.IsCartier) :
    ∃ E : Y.CartierDivisor,
      Nonempty (W.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E) ∧
      I (KCartierDivisor.ofCartier ℝ E) = degFun sY f W hW := by
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := hW.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf W.divisorialSheaf
  refine ⟨E, ⟨e⟩, linearMap_ext_relativeClass sY f fun C hC => ?_⟩
  rw [degFun_relativeClass]
  change (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) = _
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  exact_mod_cast (degreeOn_eq_of_iso k sY C.ι C.dim_le e).symm

variable [CompactSpace Y] [IsAlgClosed k] [CharZero k] (sX : X ⟶ Spec (.of k))
  [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sY]
  (hfp : IsProjective f) (hfs : f ≫ sX = sY)

include hfp hfs in
/-- An `f`-ample Cartier divisor is positive on `NE̅(Y/X) ∖ 0`. -/
private theorem degFun_pos_of_isRelativelyAmpleCartier {W : Divisor Y}
    (hW : IsRelativelyAmpleCartier f W) :
    ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 → 0 < degFun sY f W hW.1 z := by
  have : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety k sY).toIsIntegral
  obtain ⟨E, ⟨e⟩, hE⟩ := exists_cartierDivisor_degFun sY f W hW.1
  have h := (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sX sY f
    hfp hfs E).mp (isRelativelyAmple_sheaf_of_iso hW e)
  intro z hz hz0
  rw [← hE]
  exact h z hz hz0

include hfp hfs in
/-- The relative Kleiman criterion for a Cartier divisor of `Y`. -/
private theorem isRelativelyAmpleCartier_of_degFun_pos {W : Divisor Y} (hW : W.IsCartier)
    (h : ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 → 0 < degFun sY f W hW z) :
    IsRelativelyAmpleCartier f W := by
  have : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety k sY).toIsIntegral
  have : IsProper f := hfp.isProper
  have : QuasiCompact f := inferInstance
  obtain ⟨E, ⟨e⟩, hE⟩ := exists_cartierDivisor_degFun sY f W hW
  refine isRelativelyAmpleCartier_of_iso hW e
    ((isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sX sY f
      hfp hfs E).mpr fun z hz hz0 => ?_)
  rw [hE]
  exact h z hz hz0

end Kleiman

section RealClauses

variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- A sum of two `f`-ample `ℝ`-divisors is `f`-ample. -/
private theorem isRelativelyAmple_add {f : Y ⟶ X} {A A' : RDivisor Y}
    (hA : IsRelativelyAmple f A) (hA' : IsRelativelyAmple f A') : IsRelativelyAmple f (A + A') := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := hA
  obtain ⟨m', r', L', -, hr', hL', rfl⟩ := hA'
  refine ⟨m + m', Fin.append r r', Fin.append L L', by omega, fun j => ?_, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hr j
    · simpa using hr' j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hL j
    · simpa using hL' j
  · rw [Fin.sum_univ_add]; simp

/-- A positive multiple of an `f`-ample `ℝ`-divisor is `f`-ample. -/
private theorem isRelativelyAmple_smul {f : Y ⟶ X} {A : RDivisor Y}
    (hA : IsRelativelyAmple f A) {c : ℝ} (hc : 0 < c) : IsRelativelyAmple f (c • A) := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := hA
  exact ⟨m, fun j => c * r j, L, hm, fun j => mul_pos hc (hr j), hL, by
    rw [Finset.smul_sum]; simp [smul_smul]⟩

/-- An `f`-ample Cartier divisor is `f`-ample as an `ℝ`-divisor. -/
private theorem isRelativelyAmple_toRDivisor {f : Y ⟶ X} {H : Divisor Y}
    (hH : IsRelativelyAmpleCartier f H) :
    IsRelativelyAmple f (Divisor.toRDivisor H) :=
  ⟨1, fun _ => 1, fun _ => H, le_rfl, fun _ => one_pos, fun _ => hH, by simp⟩

variable {k : Type} [Field k] (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] (f : Y ⟶ X)
  [IsAlgClosed k] [CharZero k] (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX]
  [AlgebraicGeometry.IsVariety k sY] (hfp : IsProjective f) (hfs : f ≫ sX = sY)

include hfp hfs in
/-- Every presentation of an `f`-ample `ℝ`-divisor is positive on `NE̅(Y/X) ∖ 0`. -/
private theorem presFun_pos_of_isRelativelyAmple {A : RDivisor Y} (hA : IsRelativelyAmple f A)
    {m : ℕ} (a : Fin m → ℝ) (M : Fin m → Divisor Y) (hM : ∀ j, (M j).IsCartier)
    (hAeq : A = ∑ j, a j • Divisor.toRDivisor (M j)) :
    ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 → 0 < presFun sY f a M hM z := by
  obtain ⟨n, r, L, hn, hr, hL, rfl⟩ := hA
  rw [presFun_eq_of_eq sY f a M hM r L (fun j => (hL j).1) hAeq.symm]
  intro z hz hz0
  simp only [presFun, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun j _ => mul_pos (hr j)
    (degFun_pos_of_isRelativelyAmpleCartier sY f sX hfp hfs (hL j) z hz hz0))
    Finset.univ_nonempty

include hfp hfs in
/-- Every presentation of an `f`-ample `ℝ`-divisor is nonnegative on `NE̅(Y/X)`. -/
private theorem presFun_nonneg_of_isRelativelyAmple {A : RDivisor Y}
    (hA : IsRelativelyAmple f A) {m : ℕ} (a : Fin m → ℝ) (M : Fin m → Divisor Y)
    (hM : ∀ j, (M j).IsCartier) (hAeq : A = ∑ j, a j • Divisor.toRDivisor (M j)) :
    ∀ z ∈ relativeClosedConeOfCurves sY f, 0 ≤ presFun sY f a M hM z := by
  intro z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · exact (presFun_pos_of_isRelativelyAmple sY f sX hfp hfs hA a M hM hAeq z hz hz0).le

end RealClauses

section Arithmetic

/-- If `h ± (δ/2) m ≥ 0` then `|m| ≤ (2/δ) h`. -/
private theorem abs_le_of_nonneg_add_half_smul {δ h m : ℝ} (hδ : 0 < δ)
    (h₁ : 0 ≤ h + δ / 2 * m) (h₂ : 0 ≤ h + -(δ / 2) * m) : |m| ≤ 2 / δ * h := by
  have e : 2 / δ * (δ / 2) = 1 := by field_simp
  have hδ' : 0 ≤ 2 / δ := by positivity
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hδ' h₁, mul_nonneg hδ' h₂]

/-- Every real number is an integer plus a remainder in `(0, 1]`. -/
private theorem exists_int_sub_mem_Ioc (x : ℝ) : ∃ c : ℤ, 0 < x - c ∧ x - c ≤ 1 :=
  ⟨⌈x⌉ - 1, by push_cast; linarith [Int.ceil_lt_add_one x], by push_cast; linarith [Int.le_ceil x]⟩

/-- The rearrangement `N ∑ sᵢ vᵢ = (∑ cᵢ vᵢ - κ h) + κ (h + ∑ (tᵢ/κ) vᵢ)` when
`cᵢ = N sᵢ - tᵢ`. -/
private theorem sum_smul_eq_smul_add_smul {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [Fintype ι] {s c t : ι → ℝ} (v : ι → V) (h : V) {N κ : ℝ} (hN : N ≠ 0) (hκ : κ ≠ 0)
    (hct : ∀ i, c i = N * s i - t i) :
    ∑ i, s i • v i =
      (1 / N) • (∑ i, c i • v i - κ • h) + (κ / N) • (h + ∑ i, (t i / κ) • v i) := by
  have hs : ∀ i, s i = 1 / N * c i + κ / N * (t i / κ) := fun i => by
    rw [hct]; field_simp; ring
  simp only [smul_sub, smul_add, Finset.smul_sum, smul_smul]
  rw [show 1 / N * κ = κ / N by ring]
  conv_lhs => simp only [hs, add_smul, Finset.sum_add_distrib]
  abel

/-- If `r h ≤ φ`, `|mᵢ| ≤ B h`, `0 < tᵢ ≤ 1` and `κ + p B < N r`, then `N φ - ∑ tᵢ mᵢ - κ h > 0`
for `h > 0`. -/
private theorem sub_sum_mul_sub_pos {p : ℕ} {N r κ B φ h : ℝ} {t m : Fin p → ℝ} (hN : 0 ≤ N)
    (hNr : κ + p * B < N * r) (hh : 0 < h) (hlow : r * h ≤ φ) (hm : ∀ i, |m i| ≤ B * h)
    (ht0 : ∀ i, 0 < t i) (ht1 : ∀ i, t i ≤ 1) : 0 < N * φ - ∑ i, t i * m i - κ * h := by
  have hb : ∑ i, t i * m i ≤ p * (B * h) := by
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      show t i * m i ≤ B * h by
        nlinarith [le_abs_self (m i), hm i, abs_nonneg (m i), ht0 i, ht1 i]
  nlinarith [mul_le_mul_of_nonneg_left hlow hN, mul_pos (sub_pos.2 hNr) hh]

end Arithmetic

section NumericalInvariance

variable {k : Type} [Field k] {X Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY]
  [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- `M ↦ deg_C 𝒪_Y(M)` as an additive map on Cartier divisors. -/
private noncomputable def degreeHom (C : ProperCurve sY) :
    Divisor.cartierSubgroup (X := Y) →+ ℤ where
  toFun L := (L : Divisor Y).degreeOn k sY C.ι C.dim_le L.2
  map_zero' := Divisor.degreeOn_zero' k sY C.ι C.dim_le
  map_add' L₁ L₂ := Divisor.degreeOn_add k sY C.ι C.dim_le L₁.1 L₂.1 L₁.2 L₂.2

/-- The Cartier divisor `∑ cᵢ Mᵢ - κ H` as an element of the Cartier subgroup. -/
private noncomputable def cartierComb {p : ℕ} (c : Fin p → ℤ) (M : Fin p → Divisor Y)
    (hM : ∀ i, (M i).IsCartier) (κ : ℤ) (H : Divisor Y) (hH : H.IsCartier) :
    Divisor.cartierSubgroup (X := Y) :=
  ∑ i, c i • (⟨M i, hM i⟩ : Divisor.cartierSubgroup (X := Y)) - κ • ⟨H, hH⟩

omit [CompactSpace Y] in
private theorem coe_cartierComb {p : ℕ} (c : Fin p → ℤ) (M : Fin p → Divisor Y)
    (hM : ∀ i, (M i).IsCartier) (κ : ℤ) (H : Divisor Y) (hH : H.IsCartier) :
    (cartierComb c M hM κ H hH : Divisor Y) = ∑ i, c i • M i - κ • H := by
  simp [cartierComb]

variable (f : Y ⟶ X)

omit [CompactSpace Y] in
/-- The linear form of `∑ cᵢ Mᵢ - κ H` is `∑ cᵢ (· Mᵢ) - κ (· H)`. -/
private theorem degFun_cartierComb {p : ℕ} (c : Fin p → ℤ) (M : Fin p → Divisor Y)
    (hM : ∀ i, (M i).IsCartier) (κ : ℤ) (H : Divisor Y) (hH : H.IsCartier) :
    degFun sY f _ (cartierComb c M hM κ H hH).2 =
      ∑ i, (c i : ℝ) • degFun sY f (M i) (hM i) - (κ : ℝ) • degFun sY f H hH :=
  linearMap_ext_relativeClass sY f fun C hC => by
    have e : (cartierComb c M hM κ H hH : Divisor Y).degreeOn k sY C.ι C.dim_le
        (cartierComb c M hM κ H hH).2 = degreeHom sY C (cartierComb c M hM κ H hH) := rfl
    refine (degFun_relativeClass sY f _ (cartierComb c M hM κ H hH).2 C hC).trans ?_
    rw [e]
    simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      degFun_relativeClass, cartierComb, map_sub, map_sum, map_zsmul]
    push_cast
    rfl

variable [IsAlgClosed k] [CharZero k] (sX : X ⟶ Spec (.of k))
  [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sY]
  (hfp : IsProjective f) (hfs : f ≫ sX = sY)

include hfp hfs in
/-- If `H + ∑ tᵢ Mᵢ` is `f`-ample whenever all `|tᵢ| < δ`, then on `NE̅(Y/X)` every `Mᵢ` is
bounded by `H`: `|(z · Mᵢ)| ≤ (2/δ) (z · H)`. -/
private theorem abs_degFun_le_of_isRelativelyAmple_add {p : ℕ} {H : Divisor Y}
    (hH : H.IsCartier) {M : Fin p → Divisor Y} (hM : ∀ i, (M i).IsCartier) {δ : ℝ} (hδ : 0 < δ)
    (hpert : ∀ t : Fin p → ℝ, (∀ i, |t i| < δ) →
      IsRelativelyAmple f (Divisor.toRDivisor H + ∑ i, t i • Divisor.toRDivisor (M i)))
    (i : Fin p) : ∀ z ∈ relativeClosedConeOfCurves sY f,
      |degFun sY f (M i) (hM i) z| ≤ 2 / δ * degFun sY f H hH z := by
  have hside : ∀ σ : ℝ, |σ| < δ → ∀ z ∈ relativeClosedConeOfCurves sY f,
      0 ≤ degFun sY f H hH z + σ * degFun sY f (M i) (hM i) z := by
    intro σ hσ z hz
    have h := hpert (Pi.single i σ) fun j => by
      by_cases hj : j = i
      · subst hj; simpa using hσ
      · simpa [Pi.single_apply, hj] using hδ
    have := presFun_nonneg_of_isRelativelyAmple sY f sX hfp hfs h ![1, σ] ![H, M i]
      (fun j => by fin_cases j; exacts [hH, hM i])
      (by simp [Fin.sum_univ_two, Pi.single_apply]) z hz
    simpa [presFun, Fin.sum_univ_two] using this
  intro z hz
  exact abs_le_of_nonneg_add_half_smul hδ
    (hside _ (by rw [abs_of_pos (by positivity)]; linarith) z hz)
    (hside _ (by rw [abs_neg, abs_of_pos (by positivity)]; linarith) z hz)

omit [IsAlgClosed k] [CharZero k] [AlgebraicGeometry.IsVariety k sX]
  [AlgebraicGeometry.IsVariety k sY] in
/-- A presentation of an `f`-nef `ℝ`-divisor is nonnegative on `NE̅(Y/X)`: it is nonnegative on
the classes of the contracted curves, hence on the cone they span, and by continuity on its
closure. -/
private theorem presFun_nonneg_of_isRelativelyNef {p : ℕ} (s : Fin p → ℝ) (M : Fin p → Divisor Y)
    (hM : ∀ i, (M i).IsCartier)
    (hnef : ∀ C : ProperCurve sY, C.IsContractedBy f →
      ∀ x : ℝ, IsRIntersectionNumber k sY (∑ i, s i • Divisor.toRDivisor (M i)) s M C x → 0 ≤ x) :
    ∀ z ∈ relativeClosedConeOfCurves sY f, 0 ≤ presFun sY f s M hM z := by
  have hcont : Continuous (presFun sY f s M hM) := by
    have := QuasiCompact.compactSpace_of_compactSpace sY
    have e : ⇑(presFun sY f s M hM) = fun z => ∑ i, s i * degFun sY f (M i) (hM i) z := by
      funext z
      simp [presFun]
    rw [e]
    refine continuous_finset_sum _ fun i _ => continuous_const.mul ?_
    haveI := (hM i).isInvertibleModule_divisorialSheaf
    exact RelativeNumericalCurveClasses.continuous_degree sY f _
  have hcl : IsClosed {z : RelativeNumericalCurveClasses sY f | 0 ≤ presFun sY f s M hM z} :=
    isClosed_le continuous_const hcont
  have hsub : (relativeConeOfCurves sY f : Set (RelativeNumericalCurveClasses sY f)) ⊆
      {z | 0 ≤ presFun sY f s M hM z} := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      change 0 ≤ presFun sY f s M hM (C.relativeClass f hC)
      rw [presFun_relativeClass]
      exact hnef C hC _ (isRIntersectionNumber_sum_degreeOn _ s M hM rfl C)
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
      exact add_nonneg hx hy
    | smul c x _ hx =>
      simp only [Set.mem_setOf_eq, LinearMap.map_smul_of_tower] at hx ⊢
      exact smul_nonneg c.2 hx
  intro z hz
  rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves] at hz
  exact closure_minimal hsub hcl hz

include hfp hfs in
/-- **Nef plus ample is ample, over a base.** Let `f : Y ⟶ X` be projective, `N` an `f`-nef
`ℝ`-Cartier divisor and `H` an `f`-ample Cartier divisor such that `H + ∑ tᵢ Mᵢ` is `f`-ample for
small real `tᵢ`, for every finite family of Cartier divisors `Mᵢ`. Then `N + c H` is `f`-ample for
every `c > 0`. Writing `N + c H = ∑ᵢ sᵢ Mᵢ`, its form on `N₁(Y/X)` is at least `c (· H)` on
`NE̅(Y/X)`; perturbing `H` in the directions `Mᵢ` bounds `|Mᵢ| ≤ (2/δ) H` there, and with
`K sᵢ = cᵢ + tᵢ` (`cᵢ ∈ ℤ`, `0 < tᵢ ≤ 1`) the identity
`K (N + c H) = (∑ cᵢ Mᵢ - κ H) + κ (H + ∑ (tᵢ/κ) Mᵢ)` exhibits it as a positive combination of an
`f`-ample Cartier divisor (relative Kleiman criterion) and an `f`-ample `ℝ`-divisor. -/
private theorem isRelativelyAmple_add_smul_of_isRelativelyNef {N : RDivisor Y}
    (hN : IsRelativelyNef k sY f N) {H : Divisor Y} (hHa : IsRelativelyAmpleCartier f H)
    (hpert : ∀ (p : ℕ) (M : Fin p → Divisor Y), (∀ i, (M i).IsCartier) → ∃ δ : ℝ, 0 < δ ∧
      ∀ t : Fin p → ℝ, (∀ i, |t i| < δ) →
        IsRelativelyAmple f (Divisor.toRDivisor H + ∑ i, t i • Divisor.toRDivisor (M i)))
    {c : ℝ} (hc : 0 < c) : IsRelativelyAmple f (N + c • Divisor.toRDivisor H) := by
  obtain ⟨p₀, s₀, M₀, hM₀, hN₀, hnef⟩ := hN
  -- the presentation `N + c H = ∑ sᵢ Mᵢ`
  set s : Fin (p₀ + 1) → ℝ := Fin.cons c s₀
  set M : Fin (p₀ + 1) → Divisor Y := Fin.cons H M₀
  have hM : ∀ i, (M i).IsCartier := Fin.cases hHa.1 hM₀
  have hD : N + c • Divisor.toRDivisor H = ∑ i, s i • Divisor.toRDivisor (M i) := by
    rw [Fin.sum_univ_succ, hN₀]
    simp only [s, M, Fin.cons_zero, Fin.cons_succ]
    abel
  -- the forms: `presFun s M = c (· H) + presFun s₀ M₀`, and the lower bound
  have hφ : presFun sY f s M hM = c • degFun sY f H hHa.1 + presFun sY f s₀ M₀ hM₀ := by
    simp only [presFun, s, M]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  have hlow : ∀ z ∈ relativeClosedConeOfCurves sY f,
      c * degFun sY f H hHa.1 z ≤ presFun sY f s M hM z := fun z hz => by
    rw [hφ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, le_add_iff_nonneg_right]
    exact presFun_nonneg_of_isRelativelyNef sY f s₀ M₀ hM₀ (hN₀ ▸ hnef) z hz
  -- perturbation of `H` in the directions `Mᵢ`
  obtain ⟨δ, hδ, hpert⟩ := hpert (p₀ + 1) M hM
  -- the integers `κ`, `K` and the splitting `K sᵢ = cᵢ + tᵢ`
  obtain ⟨κ, hκ⟩ := exists_nat_gt (1 / δ)
  have hκpos : (0 : ℝ) < κ := lt_trans (by positivity) hκ
  have hκδ : 1 < κ * δ := by rwa [div_lt_iff₀ hδ] at hκ
  obtain ⟨K, hK⟩ := exists_nat_gt ((κ + ((p₀ + 1 : ℕ) : ℝ) * (2 / δ)) / c)
  have hKr : κ + ((p₀ + 1 : ℕ) : ℝ) * (2 / δ) < K * c := by rwa [div_lt_iff₀ hc] at hK
  have hKpos : (0 : ℝ) < K :=
    pos_of_mul_pos_left (lt_of_le_of_lt (by positivity) hKr) hc.le
  choose c' ht0 ht1 using fun i => exists_int_sub_mem_Ioc ((K : ℝ) * s i)
  -- `G = ∑ cᵢ Mᵢ - κ H` is `f`-ample by the relative Kleiman criterion
  set G := cartierComb c' M hM κ H hHa.1
  have hGa : IsRelativelyAmpleCartier f G :=
    isRelativelyAmpleCartier_of_degFun_pos sY f sX hfp hfs G.2 fun z hz hz0 => by
      have hsum : ∑ i, (c' i : ℝ) * degFun sY f (M i) (hM i) z = K * presFun sY f s M hM z -
          ∑ i, (K * s i - c' i) * degFun sY f (M i) (hM i) z := by
        simp [sub_mul, presFun, Finset.mul_sum, mul_assoc]
      simp only [G, degFun_cartierComb, LinearMap.sub_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, hsum, Int.cast_natCast]
      exact sub_sum_mul_sub_pos hKpos.le hKr
        (degFun_pos_of_isRelativelyAmpleCartier sY f sX hfp hfs hHa z hz hz0) (hlow z hz)
        (fun i => abs_degFun_le_of_isRelativelyAmple_add sY f sX hfp hfs hHa.1 hM hδ hpert i z hz)
        ht0 ht1
  -- `A' = H + ∑ (tᵢ/κ) Mᵢ` is `f`-ample, and `N + c H = (1/K) G + (κ/K) A'`
  have hA'a := hpert (fun i => (K * s i - c' i) / κ) fun i => by
    rw [abs_of_pos (div_pos (ht0 i) hκpos), div_lt_iff₀ hκpos]
    linarith [ht1 i]
  have hGR : Divisor.toRDivisor (G : Divisor Y) =
      ∑ i, (c' i : ℝ) • Divisor.toRDivisor (M i) - (κ : ℝ) • Divisor.toRDivisor H := by
    rw [coe_cartierComb, map_sub, map_sum, map_zsmul]
    simp only [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast]
  rw [hD, sum_smul_eq_smul_add_smul _ (Divisor.toRDivisor H) hKpos.ne' hκpos.ne'
    (c := fun i => (c' i : ℝ)) (t := fun i => K * s i - c' i) (fun i => by ring), ← hGR]
  exact isRelativelyAmple_add (isRelativelyAmple_smul (isRelativelyAmple_toRDivisor hGa)
    (by positivity)) (isRelativelyAmple_smul hA'a (by positivity))

end NumericalInvariance

/-! ### Absolute and relative ampleness of Cartier divisors -/

section AbsoluteAmple

variable {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- A Cartier divisor with ample `𝒪_Y(L)` is ample over every quasi-compact morphism. -/
private theorem isRelativelyAmpleCartier_of_isAmple {T : Scheme.{0}} (g : Y ⟶ T) [QuasiCompact g]
    {L : Divisor Y} (hL : L.IsCartier)
    (hamp : haveI := hL.isInvertibleModule_divisorialSheaf
      Stacks.Ample.IsAmple Y L.divisorialSheaf) :
    IsRelativelyAmpleCartier g L :=
  MMP.Flips.isRelativelyAmpleCartier_of_isRelativelyAmple hL
    (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple_divisorialSheaf g hL hamp)

/-- A Cartier divisor ample over the point `Spec k` has ample `𝒪_Y(L)`. -/
private theorem isAmple_of_isRelativelyAmpleCartier {k : Type} [Field k] (s : Y ⟶ Spec (.of k))
    {L : Divisor Y} (h : IsRelativelyAmpleCartier s L) :
    haveI := h.1.isInvertibleModule_divisorialSheaf
    Stacks.Ample.IsAmple Y L.divisorialSheaf := by
  obtain ⟨hL, hamp⟩ := h
  haveI := hL.isInvertibleModule_divisorialSheaf
  exact Stacks.HProjective.isAmple_of_isAmple_restrictTop _ (hamp ⊤ (isAffineOpen_top _))

/-- A Cartier divisor ample over the point `Spec k` is ample over every quasi-compact morphism. -/
private theorem isRelativelyAmpleCartier_of_spec {k : Type} [Field k] {s : Y ⟶ Spec (.of k)}
    {T : Scheme.{0}} (g : Y ⟶ T) [QuasiCompact g] {L : Divisor Y}
    (h : IsRelativelyAmpleCartier s L) : IsRelativelyAmpleCartier g L :=
  isRelativelyAmpleCartier_of_isAmple g h.1 (isAmple_of_isRelativelyAmpleCartier s h)

/-- An `ℝ`-divisor ample over the point `Spec k` is ample over every quasi-compact morphism. -/
private theorem isRelativelyAmple_of_spec {k : Type} [Field k] {s : Y ⟶ Spec (.of k)}
    {T : Scheme.{0}} (g : Y ⟶ T) [QuasiCompact g] {D : RDivisor Y}
    (h : IsRelativelyAmple s D) : IsRelativelyAmple g D := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := h
  exact ⟨m, r, L, hm, hr, fun j => isRelativelyAmpleCartier_of_spec g (hL j), rfl⟩

/-- A projective variety carries a Cartier divisor which is ample over every quasi-compact
morphism out of it. -/
private theorem exists_isRelativelyAmpleCartier {k : Type} [Field k] [IsIntegral Y]
    {s : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsProjectiveVariety k s) :
    ∃ A : Divisor Y, IsRelativelyAmpleCartier s A := by
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hY
  obtain ⟨A, hA, ⟨e⟩⟩ := MMP.Mori.exists_isCartier_divisorialSheaf_iso H
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI : QuasiCompact s := hY.toIsVariety.toQuasiCompact
  exact ⟨A, isRelativelyAmpleCartier_of_isAmple s hA
    ((Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
      ((Stacks.AmpleBridge.isAmple_iff_isAmple _ H).mpr hHa))⟩

end AbsoluteAmple

/-! ### Nef plus ample is ample over a projective base -/

section NefPlusAmple

/-- **Nef plus ample is ample.** Let `f : Y ⟶ Z` be a morphism from a normal projective variety to
a variety over an algebraically closed field of characteristic zero, `N` an `f`-nef `ℝ`-Cartier
divisor and `A` an ample Cartier divisor on `Y`. Then `N + c A` is `f`-ample for every `c > 0`. -/
private theorem isRelativelyAmple_add_smul {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y Z : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} (hY : IsNormalVariety k sY)
    (hYp : MMP.Mori.IsProjectiveVariety k sY) [AlgebraicGeometry.IsVariety k sZ]
    (f : Y ⟶ Z) (hfs : f ≫ sZ = sY) {N : RDivisor Y} (hN : IsRelativelyNef k sY f N)
    {A : Divisor Y} (hA : IsRelativelyAmpleCartier sY A) {c : ℝ} (hc : 0 < c) :
    IsRelativelyAmple f (N + c • Divisor.toRDivisor A) := by
  haveI : AlgebraicGeometry.IsVariety k sY := hY.1
  haveI : IsProper sY :=
    isProper_of_isProjectiveMorphism sY (MMP.Mori.isProjectiveVariety_iff k sY |>.1 hYp).2
  haveI : IsProper (f ≫ sZ) := by rw [hfs]; infer_instance
  haveI : IsProper f := IsProper.of_comp f sZ
  haveI : QuasiCompact sY := inferInstance
  have hfp : IsProjective f := by
    haveI := hA.1.isInvertibleModule_divisorialSheaf
    exact MMP.isProjective_of_isProper_of_divisor_isRelativelyAmple k sY sZ f hfs A hA.1
      (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple_divisorialSheaf f hA.1
        (isAmple_of_isRelativelyAmpleCartier sY hA))
  refine isRelativelyAmple_add_smul_of_isRelativelyNef sY f sZ hfp hfs hN
    (isRelativelyAmpleCartier_of_spec f hA) (fun p M hM => ?_) hc
  obtain ⟨δ, hδ, h⟩ := MMP.Flips.exists_pos_isRelativelyAmple_add_sum_smul k sY
    (𝟙 (Spec (.of k))) hY MMP.Chow.DeterminantCurveForm.isNormalVariety_id_spec sY
    (Category.comp_id _) (isRelativelyAmple_toRDivisor hA) (fun i => Divisor.toRDivisor (M i))
    (fun i => ⟨1, fun _ => 1, fun _ => M i, fun _ => hM i, by simp; rfl⟩)
  exact ⟨δ, hδ, fun t ht => isRelativelyAmple_of_spec f (h t ht)⟩

end NefPlusAmple

/-! ### Numerical triviality and nefness of presentations -/

section NumericallyTrivial

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- The empty presentation of `0` computes `0 · C = 0`. -/
private theorem isRIntersectionNumber_zero (C : ProperCurve sX) :
    IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
  ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩

/-- Every value of `D · C` is `∑ r_j (L_j · C)` for any presentation `D = ∑ r_j L_j`. -/
private theorem eq_sum_degreeOn_of_isRIntersectionNumber (C : ProperCurve sX) {D : RDivisor X}
    {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) {m' : ℕ} {r' : Fin m' → ℝ}
    {L' : Fin m' → Divisor X} {x : ℝ} (hx : IsRIntersectionNumber k sX D r' L' C x) :
    x = ∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ) :=
  (IsRIntersectionNumber.eq_and_linear k sX C).1 _ r' L' r L _ _ hx
    (isRIntersectionNumber_sum_degreeOn D r L hL hD C)

/-- A Cartier combination, as a sum of Cartier divisors. -/
private theorem exists_eq_sum_of_isCartierCombination {N : RDivisor X}
    (hN : IsCartierCombination N) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X), (∀ j, (L j).IsCartier) ∧
      N = ∑ j, r j • Divisor.toRDivisor (L j) := by
  obtain ⟨m, r, L, hL, hN⟩ := hN
  exact ⟨m, r, L, hL, by rw [hN]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

private theorem isCartierCombination_of_eq_sum {N : RDivisor X} {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hN : N = ∑ j, r j • Divisor.toRDivisor (L j)) : IsCartierCombination N :=
  ⟨m, r, L, hL, by rw [hN]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

/-- A divisor `N = ∑ r_j L_j` is numerically trivial over `f` as soon as `∑ r_j (L_j · C) = 0`
for every curve `C` contracted by `f`. -/
private theorem isNumericallyTrivialOver_of_eq_sum (f : X ⟶ Y) {N : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hN : N = ∑ j, r j • Divisor.toRDivisor (L j))
    (h0 : ∀ C : ProperCurve sX, C.IsContractedBy f →
      ∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ) = 0) :
    IsNumericallyTrivialOver k sX f N := by
  refine ⟨isCartierCombination_of_eq_sum r L hL hN,
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  rw [eq_sum_degreeOn_of_isRIntersectionNumber C r L hL hN h₁, h0 C hC]
  exact ((IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ h₂
    (isRIntersectionNumber_zero C)).symm

/-- Along a numerically trivial divisor `N = ∑ r_j L_j`, `∑ r_j (L_j · C) = 0` for every curve
`C` contracted by `f`. -/
private theorem sum_degreeOn_eq_zero_of_isNumericallyTrivialOver {f : X ⟶ Y} {N : RDivisor X}
    (hN : IsNumericallyTrivialOver k sX f N) {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (hL : ∀ j, (L j).IsCartier) (hNL : N = ∑ j, r j • Divisor.toRDivisor (L j))
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    ∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ) = 0 :=
  hN.2.2 C hC _ r L _ 0 Fin.elim0 Fin.elim0 0 (isRIntersectionNumber_sum_degreeOn N r L hL hNL C)
    (isRIntersectionNumber_zero C)

/-- A real linear combination of numerically trivial divisors is numerically trivial. -/
private theorem isNumericallyTrivialOver_smul_add_smul {f : X ⟶ Y} {N₁ N₂ : RDivisor X}
    (h₁ : IsNumericallyTrivialOver k sX f N₁) (h₂ : IsNumericallyTrivialOver k sX f N₂)
    (a b : ℝ) : IsNumericallyTrivialOver k sX f (a • N₁ + b • N₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, hN₁⟩ := exists_eq_sum_of_isCartierCombination h₁.1
  obtain ⟨m₂, r₂, L₂, hL₂, hN₂⟩ := exists_eq_sum_of_isCartierCombination h₂.1
  have hL : ∀ j, (Fin.append L₁ L₂ j).IsCartier :=
    Fin.addCases (by simpa using hL₁) (by simpa using hL₂)
  refine isNumericallyTrivialOver_of_eq_sum f (Fin.append (a • r₁) (b • r₂)) (Fin.append L₁ L₂)
    hL ?_ fun C hC => ?_
  · rw [hN₁, hN₂, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.smul_sum, Pi.smul_apply, smul_eq_mul,
      mul_smul]
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul, mul_assoc,
      ← Finset.mul_sum]
    rw [sum_degreeOn_eq_zero_of_isNumericallyTrivialOver h₁ r₁ L₁ hL₁ hN₁ C hC,
      sum_degreeOn_eq_zero_of_isNumericallyTrivialOver h₂ r₂ L₂ hL₂ hN₂ C hC]
    ring

/-- `N₁ ≡_f N₂` gives that `N₁ - N₂` is numerically trivial over `f`. -/
private theorem isNumericallyTrivialOver_sub_of_isNumericallyEquivalentOver {f : X ⟶ Y}
    {N₁ N₂ : RDivisor X} (h : IsNumericallyEquivalentOver k sX f N₁ N₂) :
    IsNumericallyTrivialOver k sX f (N₁ - N₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, hN₁⟩ := exists_eq_sum_of_isCartierCombination h.1
  obtain ⟨m₂, r₂, L₂, hL₂, hN₂⟩ := exists_eq_sum_of_isCartierCombination h.2.1
  have hL : ∀ j, (Fin.append L₁ L₂ j).IsCartier :=
    Fin.addCases (by simpa using hL₁) (by simpa using hL₂)
  have hsub : N₁ - N₂ = ∑ j, Fin.append ((1 : ℝ) • r₁) ((-1 : ℝ) • r₂) j •
      Divisor.toRDivisor (Fin.append L₁ L₂ j) := by
    rw [hN₁, hN₂, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right, sub_eq_add_neg, Finset.sum_neg_distrib, neg_smul]
  refine isNumericallyTrivialOver_of_eq_sum f _ _ hL hsub fun C hC => ?_
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul, one_mul,
    neg_one_mul, neg_mul, Finset.sum_neg_distrib]
  rw [h.2.2 C hC _ r₁ L₁ _ _ r₂ L₂ _ (isRIntersectionNumber_sum_degreeOn N₁ r₁ L₁ hL₁ hN₁ C)
    (isRIntersectionNumber_sum_degreeOn N₂ r₂ L₂ hL₂ hN₂ C)]
  ring

/-- **Nef plus nef is nef.** -/
private theorem isRelativelyNef_add {f : X ⟶ Y} {D₁ D₂ : RDivisor X}
    (h₁ : IsRelativelyNef k sX f D₁) (h₂ : IsRelativelyNef k sX f D₂) :
    IsRelativelyNef k sX f (D₁ + D₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, hD₁, hnef₁⟩ := h₁
  obtain ⟨m₂, r₂, L₂, hL₂, hD₂, hnef₂⟩ := h₂
  have hL : ∀ j, (Fin.append L₁ L₂ j).IsCartier :=
    Fin.addCases (by simpa using hL₁) (by simpa using hL₂)
  have heq : D₁ + D₂ = ∑ j, Fin.append ((1 : ℝ) • r₁) ((1 : ℝ) • r₂) j •
      Divisor.toRDivisor (Fin.append L₁ L₂ j) := by
    rw [hD₁, hD₂, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  refine ⟨m₁ + m₂, _, _, hL, heq, fun C hC x hx => ?_⟩
  rw [eq_sum_degreeOn_of_isRIntersectionNumber C _ _ hL heq hx, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul, one_mul]
  exact add_nonneg (hnef₁ C hC _ (isRIntersectionNumber_sum_degreeOn D₁ r₁ L₁ hL₁ hD₁ C))
    (hnef₂ C hC _ (isRIntersectionNumber_sum_degreeOn D₂ r₂ L₂ hL₂ hD₂ C))

/-- **Numerically trivial divisors are nef.** -/
private theorem isRelativelyNef_of_isNumericallyTrivialOver {f : X ⟶ Y} {N : RDivisor X}
    (hN : IsNumericallyTrivialOver k sX f N) : IsRelativelyNef k sX f N := by
  obtain ⟨m, r, L, hL, hNL⟩ := exists_eq_sum_of_isCartierCombination hN.1
  refine ⟨m, r, L, hL, hNL, fun C hC x hx => ?_⟩
  rw [eq_sum_degreeOn_of_isRIntersectionNumber C r L hL hNL hx,
    sum_degreeOn_eq_zero_of_isNumericallyTrivialOver hN r L hL hNL C hC]

end NumericallyTrivial

/-! ### Prime divisors on a common resolution -/

section Resolution

/-- A prime divisor of `W` that is not exceptional over `Y` lies over a prime divisor `P` of `Y`,
`q` is a local isomorphism at its generic point, and the coefficient of `P` in a push-forward
`q_* D` is the coefficient of `E` in `D`. -/
private theorem exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor
    {k : Type u} [Field k] {W Y : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY)
    (q : W ⟶ Y) (hW : IsNormalVariety k (q ≫ sY)) [IsProper q] (hqb : IsBirationalMorphism q)
    (E : MMP.Mori.PrimeDivisor W) (hE : ¬ IsExceptionalPrimeDivisor sY q E) :
    ∃ P : MMP.Mori.PrimeDivisor Y, q E.genericPoint = P.genericPoint ∧
      IsIso (q.stalkMap E.genericPoint) ∧
      ∀ D : RDivisor W, MMP.Mori.RationalMap.transformDivisor q.toRationalMap D P = D E := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : IsSeparated q := IsSeparated.of_comp q sY
  haveI : IsDominant q := hqb.isDominant
  set DE : ProperDivisorOver k sY := ProperDivisorOver.mk ⟨W, q, hW, hqb, E⟩ inferInstance
  have hnot : ¬ DE.IsExceptional := fun h => hE ⟨hW, hqb, inferInstance, h⟩
  have hc : ¬ 2 ≤ codimension DE.toDivisorOver.center := by
    intro h2
    refine hnot ?_
    rw [MMP.Positivity.DivisorOver.codimension_center] at h2
    unfold ProperDivisorOver.IsExceptional
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint]
    have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
      (DE.toDivisorOver.f DE.toDivisorOver.E.genericPoint)
    rw [← hd]
    gcongr
    rw [← WithBot.coe_ofNat]
    exact WithBot.coe_le_coe.mpr h2
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hY] at hc
  simp only [not_forall, not_not] at hc
  obtain ⟨P, hv⟩ := hc
  have hEP : q E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hv
  obtain ⟨E', hE'P, hiso', htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hW hqb P
  have hbij := hqb.functionFieldMap_bijective
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (q E.genericPoint)) := by rw [hEP]; infer_instance
  have : ValuationRing (Y.presheaf.stalk (q E'.genericPoint)) := by rw [hE'P]; infer_instance
  have hiso := MMP.Positivity.isIso_stalkMap_of_valuationRing q hbij E.genericPoint
  have hEE' : E'.genericPoint = E.genericPoint :=
    MMP.Positivity.eq_of_isIso_stalkMap q hbij (hEP.trans hE'P.symm)
  have hEE : E' = E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hEE'
  subst hEE
  exact ⟨P, hEP, hiso, htr⟩

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier: each prime divisor `P` has a
Cartier multiple `m_P P`, and `D = ∑ (D_P / m_P) (m_P P)`. -/
private theorem isCartierCombination_of_isQFactorial {k : Type} [Field k] {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)}
    (hY : MMP.Fourfold.IsQFactorial sY) (D : RDivisor Y) : IsCartierCombination D := by
  classical
  choose m hm hc using fun P : MMP.Mori.PrimeDivisor Y => hY.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine isCartierCombination_of_eq_sum (fun j => D (e.symm j) / m (e.symm j))
    (fun j => ((m (e.symm j) : ℕ) : ℤ) • Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor Y) 1)
    (fun j => hc _) ?_
  have hterm : ∀ P : MMP.Mori.PrimeDivisor Y, (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)) =
        Finsupp.single P (D P) := by
    intro P
    ext Q
    have hm0 : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    by_cases hQ : P = Q
    · subst hQ
      simp [DivisorWithCoeffs.coeff_apply, div_mul_cancel₀ _ hm0]
    · simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hQ]
  rw [Equiv.sum_comp e.symm (fun P : D.support => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single (P : MMP.Mori.PrimeDivisor Y) 1 :
        Divisor Y)))]
  rw [Finset.sum_coe_sort D.support (fun P => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)))]
  simp_rw [hterm]
  exact (Finsupp.sum_single D).symm

/-- An `ℝ`-Cartier combination is `ℝ`-Cartier. -/
private theorem isRCartier_of_isCartierCombination {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : RDivisor X} (h : IsCartierCombination D) : RDivisor.IsRCartier D := by
  obtain ⟨m, r, C, hC, hD⟩ := h
  refine ⟨m, r, C, hC, fun Γ => ?_⟩
  rw [hD, ← MMP.Flips.coeff_sum_smul_toRDivisor]
  simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]

/-- A prime divisor contracted by a rational map has no transform. -/
private theorem transformPrimeDivisor_eq_none_of_isExceptional {X Y : Scheme.{u}}
    {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    (hP : MMP.Mori.RationalMap.IsExceptional φ P) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = none := by
  rcases h : MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | F
  · rfl
  · exfalso
    have hdef := (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
    have h2 := MMP.Mori.RationalMap.isExceptional_iff.mp hP hdef
    rw [MMP.Flips.le_closedsCodimension_iff_le_coheight] at h2
    have hmem : F.genericPoint ∈
        (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) := by
      rw [← MMP.Mori.RationalMap.support_transformPrimeDivisor h]
      exact MMP.Flips.primeDivisor_genericPoint_mem_support F
    have := h2 F.genericPoint hmem
    rw [F.coheight_genericPoint] at this
    exact absurd this (by decide)

end Resolution

/-- An ample Cartier divisor on a normal projective variety is nef over every base, and so are
its nonnegative real multiples. -/
private theorem isRelativelyNef_smul_toRDivisor {Y T : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY)
    (hYp : MMP.Mori.IsProjectiveVariety ℂ sY) (g : Y ⟶ T) {A : Divisor Y}
    (hA : IsRelativelyAmpleCartier sY A) {c : ℝ} (hc : 0 ≤ c) :
    IsRelativelyNef ℂ sY g (c • Divisor.toRDivisor A) := by
  haveI : IsProper sY :=
    isProper_of_isProjectiveMorphism sY (MMP.Mori.isProjectiveVariety_iff ℂ sY |>.1 hYp).2
  haveI : QuasiCompact sY := inferInstance
  have hS := MMP.Chow.DeterminantCurveForm.isNormalVariety_id_spec (k := ℂ)
  haveI : IsNormal (Spec (.of ℂ)) := hS.2
  haveI : IsLocallyNoetherian (Spec (.of ℂ)) := inferInstance
  have hpos := (MMP.Flips.relativelyAmple_basics sY (𝟙 (Spec (.of ℂ))) hY hS sY
    (Category.comp_id _)).2.2.1 A hA
  refine ⟨1, fun _ => c, fun _ => A, fun _ => hA.1, by simp, fun C hC x hx => ?_⟩
  obtain ⟨hL, d, -, hd, rfl⟩ := hx
  have h0 := hpos (hL 0) C (fun x _ => Subsingleton.elim _ _) (d 0) (hd 0)
  have : (0 : ℝ) ≤ d 0 := by exact_mod_cast h0.le
  simp only [Fin.sum_univ_one]
  positivity

/-! ### The perturbation on a fixed nef weak model -/

section Core

open MMP.Mori.RationalMap

/-- **Core of the perturbation lemma.** Let `π : X ⟶ Z` be a morphism to a projective complex
variety, `X` normal projective `ℚ`-factorial, `H : ι → Divisor X` Cartier with every `ℝ`-Cartier
divisor numerically equivalent over `Z` to a combination of the `Hᵢ`, and `φ : X ⤏ Y` a nef weak
model over `Z` of a klt pair `(X, B)` with `Y` `ℚ`-factorial. If every small perturbation
`B_u = B + ∑ uᵢ Hᵢ` is effective klt with effective klt transform, then for every `ε > 0` some
`u` with `|uᵢ| < ε` makes `(Y, φ_* B_u)` a log minimal model of `(X, B_u)` with `K_Y + φ_* B_u`
ample over `Z`. -/
private theorem exists_isRealLogMinimalModel_isRelativelyAmple_of_isQFactorial {X Z Y : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    (hZp : MMP.Mori.IsProjectiveVariety ℂ sZ) (hXq : IsQFactorial sX) {K : Divisor X}
    {ι : Type} [Fintype ι] (H : ι → Divisor X) (hH : ∀ i, (H i).IsCartier)
    (hspan : ∀ D : RDivisor X, IsCartierCombination D →
      ∃ u : ι → ℝ, IsNumericallyEquivalentOver ℂ sX π D (∑ i, u i • Divisor.toRDivisor (H i)))
    {sY : Y ⟶ Spec (.of ℂ)} [QuasiCompact sY] {πY : Y ⟶ Z} (hYq : IsQFactorial sY)
    {B : RDivisor X} {φ : X.RationalMap Y}
    (hweak : IsNefWeakModel sX sY sZ π πY K B φ)
    (hnbhd : ∃ ε₀ > 0, ∀ u : ι → ℝ, (∀ i, |u i| < ε₀) →
      (∀ P, 0 ≤ (B + ∑ i, u i • Divisor.toRDivisor (H i)).coeff P) ∧
      IsRealKltPair sX (B + ∑ i, u i • Divisor.toRDivisor (H i)) ∧
      (∀ Q, 0 ≤ (transformDivisor φ (B + ∑ i, u i • Divisor.toRDivisor (H i))).coeff Q) ∧
      IsRealKltPair sY (transformDivisor φ (B + ∑ i, u i • Divisor.toRDivisor (H i)))) :
    ∀ ε > 0, ∃ u : ι → ℝ, (∀ i, |u i| < ε) ∧
      IsRealLogMinimalModel sX sY sZ π πY K (B + ∑ i, u i • Divisor.toRDivisor (H i))
        (transformDivisor φ K) (transformDivisor φ (B + ∑ i, u i • Divisor.toRDivisor (H i))) φ ∧
      IsRelativelyAmple πY (logCanonicalDivisor (transformDivisor φ K)
          (transformDivisor φ (B + ∑ i, u i • Divisor.toRDivisor (H i)))) := by
  classical
  intro ε hε
  obtain ⟨ε₀, hε₀, hnb⟩ := hnbhd
  -- the varieties
  have hXn : IsNormalVariety ℂ sX := hweak.isNormalVariety_source
  have hXp := hweak.isProjectiveVariety_source
  have hYn : IsNormalVariety ℂ sY := hweak.isNormalVariety_target
  have hYp := hweak.isProjectiveVariety_target
  have hπ : π ≫ sZ = sX := hweak.comp_eq_source
  have hπY : πY ≫ sZ = sY := hweak.comp_eq_target
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZp.toIsVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hYn.1
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI : IsSeparated sZ := hZp.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : QuasiCompact πY := by
    haveI : QuasiCompact (πY ≫ sZ) := by rw [hπY]; infer_instance
    exact QuasiCompact.of_comp πY sZ
  have := isSeparated_toTerminal sX
  have := isSeparated_toTerminal sY
  have := isSeparated_toTerminal sZ
  -- the common resolution of the weak model
  obtain ⟨W, _, _, _, sW, p, q, h, hWv, hWsm, hpW, hqW, hpp, hqp, hpb, hqb, hinv, hφ,
    G₁, G₂, hG₁, hG₂, hG0, hGexc⟩ := hweak.exists_resolution
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI : LocallyOfFiniteType sW := hWv.toLocallyOfFiniteType
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsSeparated sW := hWv.toIsSeparated
  have := isSeparated_toTerminal sW
  haveI : IsSeparated p := by
    haveI : IsSeparated (p ≫ sX) := by rw [hpW]; infer_instance
    exact IsSeparated.of_comp p sX
  haveI : IsSeparated q := by
    haveI : IsSeparated (q ≫ sY) := by rw [hqW]; infer_instance
    exact IsSeparated.of_comp q sY
  have hWn : IsNormalVariety ℂ sW := ⟨hWv, inferInstance⟩
  have hWnp : IsNormalVariety ℂ (p ≫ sX) := by rw [hpW]; exact hWn
  have hWnq : IsNormalVariety ℂ (q ≫ sY) := by rw [hqW]; exact hWn
  have hWp : MMP.Mori.IsProjectiveVariety ℂ sW := by
    rw [MMP.Mori.isProjectiveVariety_iff] at hXp ⊢
    rw [← hpW]
    exact ⟨by rw [hpW]; exact hWv, hpp.comp hXp.2⟩
  have hpq : p ≫ π = q ≫ πY := by
    have h1 : h.compHom (q ≫ πY) = π.toRationalMap := by
      rw [← Oai4C1.Main.compHom_compHom, hφ]
      exact hweak.isOver
    exact (eq_comp_of_isInverse_of_compHom_eq hinv (q ≫ πY) π h1).symm
  /- the correspondence of prime divisors -/
  have hst : ∀ P : MMP.Mori.PrimeDivisor X, ∃ P' : MMP.Mori.PrimeDivisor W,
      transformPrimeDivisor h P = some P' ∧ p P'.genericPoint = P.genericPoint := fun P => by
    obtain ⟨P', h1, h2, -⟩ :=
      exists_transformPrimeDivisor_eq_some_of_isInverse hXn p h hWnp hpb hinv P
    exact ⟨P', h1, h2⟩
  have hp_uniq : ∀ {x y : W} {P : MMP.Mori.PrimeDivisor X}, p x = P.genericPoint →
      p y = P.genericPoint → x = y := fun hx hy =>
    Oai4C1.eq_of_map_eq_genericPoint hpb hx hy
  have hq_uniq : ∀ {x y : W} {F : MMP.Mori.PrimeDivisor Y}, q x = F.genericPoint →
      q y = F.genericPoint → x = y := fun hx hy =>
    Oai4C1.eq_of_map_eq_genericPoint hqb hx hy
  have hφP : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor W)
      (F : MMP.Mori.PrimeDivisor Y), p P'.genericPoint = P.genericPoint →
      (transformPrimeDivisor φ P = some F ↔ q P'.genericPoint = F.genericPoint) := by
    intro P P' F hP'
    obtain ⟨P'', h1, h2⟩ := hst P
    obtain rfl : P'' = P' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hp_uniq h2 hP')
    rw [← hφ, transformPrimeDivisor_compHom h1 q,
      MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff]
  have hinj : ∀ (P P' : MMP.Mori.PrimeDivisor X) (F : MMP.Mori.PrimeDivisor Y),
      transformPrimeDivisor φ P = some F → transformPrimeDivisor φ P' = some F → P' = P := by
    intro P P' F h1 h2
    obtain ⟨Q, -, hQ⟩ := hst P
    obtain ⟨Q', -, hQ'⟩ := hst P'
    obtain rfl : Q' = Q := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (hq_uniq ((hφP P' Q' F hQ').mp h2) ((hφP P Q F hQ).mp h1))
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hQ'.symm.trans hQ)
  have hC3 : ∀ F : MMP.Mori.PrimeDivisor Y, ∃ (P : MMP.Mori.PrimeDivisor X)
      (P' : MMP.Mori.PrimeDivisor W), p P'.genericPoint = P.genericPoint ∧
        q P'.genericPoint = F.genericPoint ∧ transformPrimeDivisor φ P = some F := by
    intro F
    obtain ⟨P, hP⟩ : ∃ P, transformPrimeDivisor φ P = some F := by
      by_contra hc
      push Not at hc
      exact hweak.not_isInverseExceptional F hc
    obtain ⟨P', -, hP'⟩ := hst P
    exact ⟨P, P', hP', (hφP P P' F hP').mp hP, hP⟩
  -- coefficients of push-forwards and of transforms
  have hpcoef : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor W),
      p P'.genericPoint = P.genericPoint → ∀ {R : Type} [AddCommMonoid R]
      (D : DivisorWithCoeffs R W), transformDivisor p.toRationalMap D P = D P' := by
    intro P P' hP' R _ D
    obtain ⟨E, hE, -, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hWnp hpb P
    obtain rfl : E = P' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hp_uniq hE hP')
    exact htr D
  have hqcoef : ∀ (F : MMP.Mori.PrimeDivisor Y) (F' : MMP.Mori.PrimeDivisor W),
      q F'.genericPoint = F.genericPoint → ∀ {R : Type} [AddCommMonoid R]
      (D : DivisorWithCoeffs R W), transformDivisor q.toRationalMap D F = D F' := by
    intro F F' hF' R _ D
    obtain ⟨E, hE, -, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hYn hWnq hqb F
    obtain rfl : E = F' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hq_uniq hE hF')
    exact htr D
  have hφcoef : ∀ (P : MMP.Mori.PrimeDivisor X) (F : MMP.Mori.PrimeDivisor Y),
      transformPrimeDivisor φ P = some F → ∀ {R : Type} [AddCommMonoid R]
      (D : DivisorWithCoeffs R X), transformDivisor φ D F = D P :=
    fun P F hPF R _ D => MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hPF
      (fun P' hP' => hinj P P' F hPF hP') D
  -- `φ_* D = q_* D_W` whenever `p_* D_W = D`
  have htrans : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X)
      (DW : DivisorWithCoeffs R W), transformDivisor p.toRationalMap DW = D →
      transformDivisor φ D = transformDivisor q.toRationalMap DW := by
    intro R _ D DW hD
    refine Finsupp.ext fun F => ?_
    obtain ⟨P, P', h1, h2, h3⟩ := hC3 F
    rw [hφcoef P F h3, hqcoef F P' h2, ← hD, hpcoef P P' h1]
  -- push-forwards of pull-backs
  have hppb : ∀ {D : RDivisor X} {G : RDivisor W}, IsRCartierPullback p D G →
      transformDivisor p.toRationalMap G = D := by
    intro D G hG
    refine Finsupp.ext fun P => ?_
    obtain ⟨P', -, hP'⟩ := hst P
    haveI := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hpb hP'
    rw [hpcoef P P' hP']
    exact MMP.Fourfold.coeff_eq_of_isRCartierPullback P' P hP' hG
  have hqpb : ∀ {D : RDivisor Y} {G : RDivisor W}, IsRCartierPullback q D G →
      transformDivisor q.toRationalMap G = D := by
    intro D G hG
    refine Finsupp.ext fun F => ?_
    obtain ⟨P, P', -, hF', -⟩ := hC3 F
    haveI := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hqb hF'
    rw [hqcoef F P' hF']
    exact MMP.Fourfold.coeff_eq_of_isRCartierPullback P' F hF' hG
  -- the prime divisors of `W` not exceptional over `Y`
  have hnexc : ∀ F' : MMP.Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sY q F' →
      ∃ (P : MMP.Mori.PrimeDivisor X) (F : MMP.Mori.PrimeDivisor Y),
        p F'.genericPoint = P.genericPoint ∧ q F'.genericPoint = F.genericPoint ∧
          transformPrimeDivisor φ P = some F := by
    intro F' hF'
    obtain ⟨F, hF, -, -⟩ :=
      exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor hYn q hWnq hqb F' hF'
    obtain ⟨P, P', h1, h2, h3⟩ := hC3 F
    obtain rfl : P' = F' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hq_uniq h2 hF)
    exact ⟨P, F, h1, h2, h3⟩

  /- an ample Cartier divisor `A` on `Y`, its pull-back `q^*A` and its trace `A_X = p_* q^* A` -/
  obtain ⟨A, hA⟩ := exists_isRelativelyAmpleCartier hYp
  have hAc := hA.1
  have hBA : ∀ Z' : irreducibleComponents W, q (componentGenericPoint W Z') ∉ A.supp :=
    fun Z' => MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' q A Z'
  set AW : Divisor W := A.pullback hAc hBA
  have hAW : IsRCartierPullback q (Divisor.toRDivisor A) (Divisor.toRDivisor AW) :=
    MMP.Fourfold.isRCartierPullback_toRDivisor hAc hBA (Divisor.isPullback_pullback hAc hBA)
  set AX : RDivisor X := transformDivisor p.toRationalMap (Divisor.toRDivisor AW) with hAXdef
  have hAXc : IsCartierCombination AX := isCartierCombination_of_isQFactorial hXq AX
  have hAnef : IsRelativelyNef ℂ sY πY (Divisor.toRDivisor A) := by
    simpa using isRelativelyNef_smul_toRDivisor hYn hYp πY hA zero_le_one
  /- the sum `E` of the prime divisors of `X` contracted by `φ` -/
  have hSfin : {P : MMP.Mori.PrimeDivisor X | transformPrimeDivisor φ P = none}.Finite := by
    obtain ⟨e, he, hinv'⟩ := hqb.isInverse_inverse
    obtain ⟨hfin, hiff⟩ := MMP.Flips.RationalMap.finite_setOf_isInverseExceptional hYn hWn
      (MMP.Mori.RationalMap.IsBirational.inverse hqb) ⟨e.symm, hinv'⟩
      (MMP.Flips.RationalMap.isMorphismInCodimOne_inverse hYn q hWnq.1 hqb)
    have hiff' := hiff q inferInstance hqW hqb.isInverse_inverse
    choose st hst1 hst2 using hst
    refine Set.Finite.of_finite_image (f := st) (hfin.subset ?_) ?_
    · rintro _ ⟨P, hP, rfl⟩
      rw [Set.mem_setOf_eq, hiff']
      by_contra hne
      obtain ⟨P₀, F, h1, -, h3⟩ := hnexc (st P) hne
      obtain rfl : P₀ = P :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h1.symm.trans (hst2 P))
      rw [Set.mem_setOf_eq.mp hP] at h3
      cases h3
    · intro P _ P' _ he
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((hst2 P).symm.trans (he ▸ hst2 P'))
  set S := hSfin.toFinset with hSdef
  set E : RDivisor X := ∑ P ∈ S, Finsupp.single P (1 : ℝ) with hEdef
  have hEcoef : ∀ P, E.coeff P = if transformPrimeDivisor φ P = none then 1 else 0 := by
    intro P
    rw [DivisorWithCoeffs.coeff_apply, hEdef, Finsupp.finset_sum_apply]
    by_cases hP : transformPrimeDivisor φ P = none
    · rw [Finset.sum_eq_single_of_mem P (by simpa [hSdef] using hP), if_pos hP,
        Finsupp.single_eq_same]
      intro Q _ hQ
      exact Finsupp.single_eq_of_ne hQ.symm
    · rw [if_neg hP]
      refine Finset.sum_eq_zero fun Q hQ => Finsupp.single_eq_of_ne ?_
      rintro rfl
      exact hP (by simpa [hSdef] using hQ)
  have hE0 : 0 ≤ E := by
    rw [← DivisorWithCoeffs.isEffective_iff_nonneg]
    intro P
    change 0 ≤ E.coeff P
    rw [hEcoef]
    split_ifs <;> norm_num
  have hφE : transformDivisor φ E = 0 := by
    rw [hEdef, map_sum]
    refine Finset.sum_eq_zero fun P hP => ?_
    exact transformDivisor_single_of_eq_none (by simpa [hSdef] using hP) _
  have hEc : IsCartierCombination E := isCartierCombination_of_isQFactorial hXq E
  /- the coefficients `u = δ a + δ e`, with `A_X ≡ ∑ aᵢ Hᵢ` and `E ≡ ∑ eᵢ Hᵢ` -/
  obtain ⟨a, ha⟩ := hspan AX hAXc
  obtain ⟨e, he⟩ := hspan E hEc
  set C₀ : ℝ := ∑ i, (|a i| + |e i|) + 1
  have hC₀ : 0 < C₀ := by positivity
  set δ : ℝ := min ε ε₀ / (2 * C₀) with hδdef
  have hmin : 0 < min ε ε₀ := lt_min hε hε₀
  have hδ : 0 < δ := by positivity
  set u : ι → ℝ := fun i => δ * a i + δ * e i with hudef
  have hu : ∀ i, |u i| < min ε ε₀ := by
    intro i
    have h1 : |a i| + |e i| ≤ C₀ := by
      have := Finset.single_le_sum (f := fun j => |a j| + |e j|)
        (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
      linarith
    have h2 : |u i| ≤ δ * C₀ := by
      calc |u i| ≤ |δ * a i| + |δ * e i| := abs_add_le _ _
        _ = δ * (|a i| + |e i|) := by rw [abs_mul, abs_mul, abs_of_pos hδ]; ring
        _ ≤ δ * C₀ := mul_le_mul_of_nonneg_left h1 hδ.le
    have h3 : δ * C₀ = min ε ε₀ / 2 := by rw [hδdef]; field_simp
    linarith
  obtain ⟨hBu0, hBuklt, hBYu0, hBYuklt⟩ := hnb u fun i => (hu i).trans_le (min_le_right _ _)
  refine ⟨u, fun i => (hu i).trans_le (min_le_left _ _), ?_⟩

  set Hu : RDivisor X := ∑ i, u i • Divisor.toRDivisor (H i) with hHudef
  set N : RDivisor X := Hu - (δ • AX + δ • E) with hNdef
  have hHuN : Hu = δ • AX + δ • E + N := by rw [hNdef]; abel
  have hNtriv : IsNumericallyTrivialOver ℂ sX π N := by
    have h1 := isNumericallyTrivialOver_sub_of_isNumericallyEquivalentOver ha
    have h2 := isNumericallyTrivialOver_sub_of_isNumericallyEquivalentOver he
    convert isNumericallyTrivialOver_smul_add_smul h1 h2 (-δ) (-δ) using 1
    rw [hNdef, hHudef]
    simp only [hudef, add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum]
    rw [neg_smul, neg_smul, smul_sub, smul_sub]
    abel
  /- pull-backs to `W` and the full trace of `N` -/
  obtain ⟨PA, hPA, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p hAXc
  obtain ⟨PE, hPE, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p hEc
  obtain ⟨PN, hPN, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p hNtriv.1
  obtain ⟨hNYtriv, hNYpb⟩ :=
    MMP.Fourfold.isNumericallyTrivialOver_transformDivisor_and_isRCartierPullback sW sX sY sZ
      hWn hWp hXn hXp hYq hYp hZp π πY hπ hπY p q hpW hqW hpq hpp hpb hqp hqb hNtriv hPN
  have hφN : transformDivisor φ N = transformDivisor q.toRationalMap PN := htrans N PN (hppb hPN)
  have hφA : transformDivisor φ AX = Divisor.toRDivisor A := by rw [htrans AX _ rfl, hqpb hAW]
  have hφHu : transformDivisor φ Hu =
      δ • Divisor.toRDivisor A + transformDivisor q.toRationalMap PN := by
    have hs : ∀ D : RDivisor X, transformDivisor φ (δ • D) = δ • transformDivisor φ D :=
      fun D => (transformDivisorₗ ℝ φ).map_smul δ D
    rw [hHuN, map_add, map_add, hs, hs, hφA, hφE, hφN, smul_zero, add_zero]
  have hPHu : IsRCartierPullback p Hu (δ • PA + δ • PE + PN) := by
    rw [hHuN]
    exact MMP.Fourfold.isRCartierPullback_add (MMP.Fourfold.isRCartierPullback_add
      (MMP.Fourfold.isRCartierPullback_smul δ hPA) (MMP.Fourfold.isRCartierPullback_smul δ hPE))
      hPN
  have hQHu : IsRCartierPullback q (transformDivisor φ Hu)
      (δ • Divisor.toRDivisor AW + PN) := by
    rw [hφHu]
    exact MMP.Fourfold.isRCartierPullback_add (MMP.Fourfold.isRCartierPullback_smul δ hAW) hNYpb
  /- the comparison for `B_u` -/
  have hlcX : logCanonicalDivisor K (B + Hu) = logCanonicalDivisor K B + Hu := by
    simp only [logCanonicalDivisor]
    abel
  have hlcY : logCanonicalDivisor (transformDivisor φ K) (transformDivisor φ (B + Hu)) =
      logCanonicalDivisor (transformDivisor φ K) (transformDivisor φ B) +
        transformDivisor φ Hu := by
    rw [map_add]
    simp only [logCanonicalDivisor]
    abel
  set GX : RDivisor W := G₁ + (δ • PA + δ • PE + PN) with hGXdef
  set GY : RDivisor W := G₂ + (δ • Divisor.toRDivisor AW + PN) with hGYdef
  have hGX : IsRCartierPullback p (logCanonicalDivisor K (B + Hu)) GX := by
    rw [hlcX]; exact MMP.Fourfold.isRCartierPullback_add hG₁ hPHu
  have hGY : IsRCartierPullback q
      (logCanonicalDivisor (transformDivisor φ K) (transformDivisor φ (B + Hu))) GY := by
    rw [hlcY]; exact MMP.Fourfold.isRCartierPullback_add hG₂ hQHu
  have hPA0 : 0 ≤ PA - Divisor.toRDivisor AW :=
    MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub sW sX sY hWn hWp hXn hXp hYn hYp
      π πY p q hpW hqW hpq hpp hpb hqp hqb hAXc hAnef hPA hAW
      (by rw [map_sub, hppb hPA, sub_self])
  have hPE0 : 0 ≤ PE :=
    (MMP.Fourfold.isEffective_of_isRCartierPullback p (isRCartier_of_isCartierCombination hEc)
      hE0).2 PE hPE
  have hPA0c : ∀ P, 0 ≤ (PA - Divisor.toRDivisor AW).coeff P :=
    DivisorWithCoeffs.isEffective_iff_nonneg.mpr hPA0
  have hPE0c : ∀ P, 0 ≤ PE.coeff P := DivisorWithCoeffs.isEffective_iff_nonneg.mpr hPE0
  have hdc : ∀ P, (GX - GY).coeff P = (G₁ - G₂).coeff P +
      δ * (PA - Divisor.toRDivisor AW).coeff P + δ * PE.coeff P := by
    intro P
    have : GX - GY = (G₁ - G₂) + δ • (PA - Divisor.toRDivisor AW) + δ • PE := by
      rw [hGXdef, hGYdef]; module
    rw [this]
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  have heff : ∀ P, 0 ≤ (GX - GY).coeff P := by
    intro P
    rw [hdc]
    have := hG0 P
    have := hPA0c P
    have := hPE0c P
    positivity
  have hexc : ∀ P, (GX - GY).coeff P ≠ 0 → IsExceptionalPrimeDivisor sY q P := by
    intro F' hF'
    by_contra hne
    apply hF'
    obtain ⟨P, F, h1, -, h3⟩ := hnexc F' hne
    haveI := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hpb h1
    have e1 : (G₁ - G₂).coeff F' = 0 := by
      by_contra hc
      exact hne (hGexc F' hc)
    have e2 : (PA - Divisor.toRDivisor AW).coeff F' = 0 := by
      rw [DivisorWithCoeffs.coeff_sub, MMP.Fourfold.coeff_eq_of_isRCartierPullback F' P h1 hPA,
        DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, hAXdef, hpcoef P F' h1,
        sub_self]
    have e3 : PE.coeff F' = 0 := by
      rw [MMP.Fourfold.coeff_eq_of_isRCartierPullback F' P h1 hPE, hEcoef, if_neg (by simp [h3])]
    rw [hdc, e1, e2, e3]
    ring
  have hpos : ∀ P : MMP.Mori.PrimeDivisor X, IsExceptional φ P →
      ∀ P' : MMP.Mori.PrimeDivisor W, transformPrimeDivisor h P = some P' →
        0 < (GX - GY).coeff P' := by
    intro P hP P' hP'
    obtain ⟨P'', h1, h2⟩ := hst P
    obtain rfl : P'' = P' := Option.some.inj (h1.symm.trans hP')
    haveI := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hpb h2
    have hE1 : PE.coeff P'' = 1 := by
      rw [MMP.Fourfold.coeff_eq_of_isRCartierPullback P'' P h2 hPE, hEcoef,
        if_pos (transformPrimeDivisor_eq_none_of_isExceptional hP)]
    rw [hdc, hE1]
    have := hG0 P''
    have := hPA0c P''
    positivity
  /- canonical divisors on `W` -/
  obtain ⟨nK, hK⟩ := hweak.isCanonicalDivisor
  haveI : MMP.Mori.IsVariety ℂ sX := hXn.1
  haveI : MMP.Mori.IsVariety ℂ (p ≫ sX) := hWnp.1
  haveI : MMP.Mori.IsVariety ℂ (q ≫ sY) := hWnq.1
  haveI : LocallyOfFiniteType (p ≫ sX) := hWnp.1.toLocallyOfFiniteType
  have hdimW : topologicalKrullDim W = nK := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb]
    exact hK.topologicalKrullDim_eq
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (p ≫ sX) hWnp hdimW
  obtain ⟨KW, hKW, hKWX⟩ :=
    Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hXn hWnp hpb hK hK₀
  have hKWY : transformDivisor q.toRationalMap KW = transformDivisor φ K :=
    (htrans K KW hKWX).symm
  have hKW' : KW.IsCanonicalDivisor sW nK := by rw [← hpW]; exact hKW
  have hR : IsLogComparisonResolution sX sY sW φ K (B + Hu) (transformDivisor φ K)
      (transformDivisor φ (B + Hu)) p q h GX GY :=
    { isVariety := hWv
      isSmoothScheme := hWsm
      comp_eq_left := hpW
      comp_eq_right := hqW
      isProjectiveMorphism_left := hpp
      isProjectiveMorphism_right := hqp
      isBirationalMorphism_left := hpb
      isBirationalMorphism_right := hqb
      isInverse := hinv
      compHom_eq := hφ
      exists_canonicalDivisor := ⟨nK, KW, hKW', hKWX, hKWY⟩
      isRCartierPullback_left := hGX
      isRCartierPullback_right := hGY
      effective := heff
      isExceptional := hexc }
  /- the target adjoint is ample -/
  have hnef' : IsRelativelyNef ℂ sY πY
      (logCanonicalDivisor (transformDivisor φ K) (transformDivisor φ B) +
        transformDivisor q.toRationalMap PN) :=
    isRelativelyNef_add hweak.isRelativelyNef (isRelativelyNef_of_isNumericallyTrivialOver hNYtriv)
  have hTeq : logCanonicalDivisor (transformDivisor φ K) (transformDivisor φ (B + Hu)) =
      (logCanonicalDivisor (transformDivisor φ K) (transformDivisor φ B) +
        transformDivisor q.toRationalMap PN) + δ • Divisor.toRDivisor A := by
    rw [hlcY, hφHu]
    abel
  have hamp : IsRelativelyAmple πY
      (logCanonicalDivisor (transformDivisor φ K) (transformDivisor φ (B + Hu))) := by
    rw [hTeq]
    exact isRelativelyAmple_add_smul hYn hYp πY hπY hnef' hA hδ
  have hTnef : IsRelativelyNef ℂ sY πY
      (logCanonicalDivisor (transformDivisor φ K) (transformDivisor φ (B + Hu))) := by
    rw [hTeq]
    exact isRelativelyNef_add hnef' (isRelativelyNef_smul_toRDivisor hYn hYp πY hA hδ.le)
  /- klt and dlt -/
  have hRCX : RDivisor.IsRCartier (Divisor.toRDivisor K + (B + Hu)) := by
    obtain ⟨m, r, L, -, hLc, hD, -, -⟩ := hGX
    refine ⟨m, r, L, hLc, fun Γ => ?_⟩
    rw [← MMP.Flips.coeff_sum_smul_toRDivisor, ← hD]
    rfl
  have hRCY : RDivisor.IsRCartier
      (Divisor.toRDivisor (transformDivisor φ K) + transformDivisor φ (B + Hu)) := by
    obtain ⟨m, r, L, -, hLc, hD, -, -⟩ := hGY
    refine ⟨m, r, L, hLc, fun Γ => ?_⟩
    rw [← MMP.Flips.coeff_sum_smul_toRDivisor, ← hD]
    rfl
  have hKY : Divisor.IsCanonicalDivisor sY nK (transformDivisor φ K) := by
    have hdimY : topologicalKrullDim Y = nK := by
      rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (q ≫ sY) hqb]
      exact hdimW
    obtain ⟨K₀', hK₀'⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sY hYn hdimY
    haveI : LocallyOfFiniteType (q ≫ sY) := hWnq.1.toLocallyOfFiniteType
    rw [← hKWY]
    exact Oai4C1.Main.isCanonicalDivisor_transformDivisor hYn hWnq hqb hK₀'
      (by rw [hqW]; exact hKW')
  have hYdlt : IsRealDltPair sY (transformDivisor φ (B + Hu)) := by
    have hE : ∀ x : Scheme.Opens.toScheme (X := Y) (⊤ : Closeds Y).compl, False :=
      fun x => x.2 trivial
    exact ⟨⟨hYn, hBYu0, ⟨nK, _, hKY, hRCY⟩, fun d E a ha => (hBYuklt.2.2.2 d E a ha).le⟩,
      fun F => (hBYuklt.2.1 F).le, ⊤, Opens.ext (Set.ext fun x => (hE x).elim),
      ⟨fun E _ => (hE E.genericPoint).elim, fun x => (hE x).elim⟩,
      fun d E _ a ha => hBYuklt.2.2.2 d E a ha⟩
  have hres : ∃ (W' : Scheme.{0}) (_ : IsIntegral W') (_ : IsLocallyNoetherian W')
      (_ : IsNormal W') (sW' : W' ⟶ Spec (.of ℂ)) (p' : W' ⟶ X) (q' : W' ⟶ Y)
      (h' : X.RationalMap W') (GX GY : RDivisor W'),
      IsLogComparisonResolution sX sY sW' φ K (B + Hu) (transformDivisor φ K)
        (transformDivisor φ (B + Hu)) p' q' h' GX GY :=
    ⟨W, inferInstance, inferInstance, inferInstance, sW, p, q, h, GX, GY, hR⟩
  refine ⟨{ isRealLcPair := ⟨hXn, hBu0, ⟨nK, K, hK, hRCX⟩,
              fun d E a ha => (hBuklt.2.2.2 d E a ha).le⟩
            isCanonicalDivisor := ⟨nK, hK⟩
            comp_eq := hπ
            isNormalVariety_model := hYn
            isCanonicalDivisor_model := ⟨nK, hKY⟩
            isProjectiveVariety_model := hYp
            comp_eq_model := hπY
            isQFactorial := hYq
            isRealDltPair := hYdlt
            isBirational := hweak.isBirational
            isOver := hweak.isOver
            coeff_boundary := fun F => by
              rw [if_neg (hweak.not_isInverseExceptional F), add_zero]
            isRelativelyNef := hTnef
            exists_resolution := hres
            exists_resolution_pos :=
              ⟨W, inferInstance, inferInstance, inferInstance, sW, p, q, h, GX, GY, hR, hpos⟩ },
    hamp⟩

end Core

end MMP.NefModelAmplePerturbation

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **An ample perturbation makes a fixed nef weak model strict.** Let `π : X ⟶ Z` be a
projective morphism of projective complex varieties, `X` normal `ℚ`-factorial with canonical
divisor `K`, and let `H : ι → Divisor X` be Cartier divisors whose classes form a basis of
`N¹(X/Z)`. Let `X = X₀ ⤏ ⋯ ⤏ X_n` be a finite program over `Z` of divisorial contractions and
flips of `(K_i + Δ_i)`-negative extremal contractions, `Δ_i` effective real klt, between projective
varieties, with composite `ψ_n : X ⤏ X_n` and `X_n` `ℚ`-factorial. Let `B` be real klt such that
`ψ_n` is a nef weak model of `(X, B)` over `Z`, and suppose that for some `ε₀ > 0` every
`B_u = B + ∑ uᵢ Hᵢ` with `|uᵢ| < ε₀` is effective and klt, with `ψ_n * B_u` effective and klt on
`X_n`. Then for every `ε > 0` there is `u` with `|uᵢ| < ε` such that `X_n` is a log minimal model
of `(X, B_u)` over `Z` via `ψ_n` and `K_{X_n} + (ψ_n)_* B_u` is ample over `Z`. -/
@[mmp "lem_fourfold_nef_model_ample_perturbation"]
public theorem exists_isRealLogMinimalModel_isRelativelyAmple_of_isNefWeakModel
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (sZ : Z ⟶ Spec (.of ℂ))
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (π : X ⟶ Z)
    (hπ : π ≫ sZ = sX) (hπp : IsProjectiveMorphism π) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXq : IsQFactorial sX) (K : Divisor X) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    {ι : Type} [Fintype ι] (H : ι → Divisor X) (hH : ∀ i, (H i).IsCartier)
    (hspan : ∀ D : RDivisor X, IsCartierCombination D →
      ∃ u : ι → ℝ, IsNumericallyEquivalentOver ℂ sX π D (∑ i, u i • Divisor.toRDivisor (H i)))
    (hind : ∀ u : ι → ℝ,
      IsNumericallyTrivialOver ℂ sX π (∑ i, u i • Divisor.toRDivisor (H i)) → u = 0)
    -- the program
    (n : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
    [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
    [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    (πY : ∀ i, Y i ⟶ Z) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
    (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
    (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i))
    (ψ : ∀ i, X.RationalMap (modelSeq X Y i))
    (hmodel : ∀ i ≤ n, modelMap π πY i ≫ sZ = modelStr sX sY i ∧
      MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i))
    (hstep : ∀ i < n,
      MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
      fp i ≫ g i = πY i ∧
      ∃ (Ki : Divisor (modelSeq X Y i)) (Δ : RDivisor (modelSeq X Y i)),
        (∃ m : ℕ, Ki.IsCanonicalDivisor (modelStr sX sY i) m) ∧ (∀ P, 0 ≤ Δ.coeff P) ∧
        IsRealKltPair (modelStr sX sY i) Δ ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor Ki Δ) (f i) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i) (logCanonicalDivisor Ki Δ)
            (f i) (fp i) (φ i)))
    (hψ0 : ψ 0 = Scheme.RationalMap.id X)
    (hψ : ∀ i < n, ∃ (a : X.PartialIso (modelSeq X Y i)) (b : (modelSeq X Y i).PartialIso (Y i)),
      a.toRationalMap = ψ i ∧ b.toRationalMap = φ i ∧ (a.trans b).toRationalMap = ψ (i + 1))
    (hYq : IsQFactorial (modelStr sX sY n))
    -- the boundary
    (B : RDivisor X) (hB : IsRealKltPair sX B)
    (hweak : IsNefWeakModel sX (modelStr sX sY n) sZ π (modelMap π πY n) K B (ψ n))
    (hnbhd : ∃ ε₀ > 0, ∀ u : ι → ℝ, (∀ i, |u i| < ε₀) →
      (∀ P, 0 ≤ (B + ∑ i, u i • Divisor.toRDivisor (H i)).coeff P) ∧
      IsRealKltPair sX (B + ∑ i, u i • Divisor.toRDivisor (H i)) ∧
      (∀ Q, 0 ≤ (MMP.Mori.RationalMap.transformDivisor (ψ n)
        (B + ∑ i, u i • Divisor.toRDivisor (H i))).coeff Q) ∧
      IsRealKltPair (modelStr sX sY n) (MMP.Mori.RationalMap.transformDivisor (ψ n)
        (B + ∑ i, u i • Divisor.toRDivisor (H i)))) :
    ∀ ε > 0, ∃ u : ι → ℝ, (∀ i, |u i| < ε) ∧
      IsRealLogMinimalModel sX (modelStr sX sY n) sZ π (modelMap π πY n) K
        (B + ∑ i, u i • Divisor.toRDivisor (H i))
        (MMP.Mori.RationalMap.transformDivisor (ψ n) K)
        (MMP.Mori.RationalMap.transformDivisor (ψ n) (B + ∑ i, u i • Divisor.toRDivisor (H i)))
        (ψ n) ∧
      IsRelativelyAmple (modelMap π πY n)
        (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor (ψ n) K)
          (MMP.Mori.RationalMap.transformDivisor (ψ n)
            (B + ∑ i, u i • Divisor.toRDivisor (H i)))) :=
  MMP.NefModelAmplePerturbation.exists_isRealLogMinimalModel_isRelativelyAmple_of_isQFactorial
    hZ hXq H hH hspan hYq hweak hnbhd

end MMP.Fourfold
