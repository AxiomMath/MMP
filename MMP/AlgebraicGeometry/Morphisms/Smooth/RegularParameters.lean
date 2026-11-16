/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.Derivative
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Curves.UniformizerDifferential
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.StandardSmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FibreRegularity
public import StacksFrontier.RingTheory.RegularLocalRing.RegularParameterFactorization

/-!
# Regular parameters and smoothness over a field

Three inputs about regularity that resolution of singularities uses.

* Over a perfect field `k`, a scheme locally of finite type over `k` is smooth exactly when all of
  its local rings are regular: at a point `y` the residue field `κ(y)` is separable over `k`, and
  smoothness at a point with separable residue field is regularity of the local ring there.
* Let `(R, 𝔪)` be a regular local ring and `h₁, …, h_k ∈ R`. Then `R / (h₁, …, h_k)` is a regular
  local ring of dimension `dim R - k` if and only if `h₁, …, h_k` is the beginning of a regular
  system of parameters `h₁, …, h_k, t₁, …, t_m` of `R`, and then the classes of the `tᵢ` are a
  regular system of parameters of the quotient. In particular the quotient of `R` by any subset
  of a regular system of parameters is regular, with the remaining parameters as parameters.
* On a smooth scheme `X` over a field `k`, every point `p` has an open neighbourhood `U` carrying
  local coordinates `x₁, …, x_n` in the sense of Kollár Def. 3.73: `dx₁, …, dx_n` is a basis of
  `Ω_{U/k}`. Here `n` is the rank of `Ω_{X/k}` at `p` and the local dimension `dim_p X`.

## Main results

* `MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk`: over a perfect field,
  smooth if and only if every local ring is regular.
* `MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff`: a quotient by
  `h₁, …, h_k` is regular of dimension `dim R - k` if and only if the `hᵢ` extend to a regular
  system of parameters;
  `MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_of_isRegularSystemOfParameters_append`:
  the remaining parameters are parameters of the quotient;
  `MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image`: the quotient by a
  subset of a regular system of parameters.
* `MMP.Flips.ResolutionInputs.exists_isLocalCoordinatesOn`: local coordinates exist near every
  point of a smooth scheme, as many as the rank of `Ω` and the local dimension at the point.

## Implementation notes

* A regular system of parameters is `MMP.Mori.IsRegularSystemOfParameters`: a family
  `Fin n → R` with `n = dim R` generating `𝔪`. A family `h : Fin k → R` is *part of* one when
  `Fin.append h t` is one for some `t : Fin m → R`; this keeps the given `hᵢ` themselves, not
  just the ideal they generate.
* "Regular of dimension `dim R - k`" is written `dim R / (h) + k = dim R` in `WithBot ℕ∞`, which
  is false when `k > dim R`, as the source's negative dimension is.
* The remaining parameters `z_j`, `j ∉ s`, are enumerated by `Finset.orderEmbOfFin`.
* The rank of `Ω_{X/k}` at `p` is the rank of the free `𝒪_{X,p}`-module `Ω_{𝒪_{X,p}/k}`, and the
  local dimension `dim_p X` is `topologicalKrullDimAt X p`, the infimum of the dimensions of the
  open neighbourhoods of `p`. Coordinates are read off a submersive presentation of `Γ(X, V)` on a
  standard smooth affine chart `V ∋ p`: the differentials of the free variables are a basis of
  `Ω_{Γ(X, V)/k}`, and since `Γ(X, V) → Γ(X, W)` is étale for every affine `W ⊆ V`, and
  `Γ(X, V) → 𝒪_{X,p}` is a localization, they stay a basis after restriction.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Def. 3.73]
* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
* [Stacks Project, Tag 00NR](https://stacks.math.columbia.edu/tag/00NR)
* [Stacks Project, Tag 00TV](https://stacks.math.columbia.edu/tag/00TV)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace MMP.Flips.ResolutionInputs

open MMP.Mori

/-! ### Smoothness and regularity over a perfect field -/

/-- **Over a perfect field, smooth means regular local rings.** A scheme `Y` locally of finite
type over a perfect field `k` is smooth over `k` if and only if every local ring `𝒪_{Y,y}` is a
regular local ring. -/
@[mmp "lem_mmp_foundation_kr_regular_iff_smooth_perfect"]
theorem smooth_iff_forall_isRegularLocalRing_stalk {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    Smooth f ↔ ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) := by
  rw [InfinitesimalLifting.smooth_iff_forall_smoothAt]
  refine forall_congr' fun y ↦ ?_
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  exact smoothAt_iff_isRegularLocalRing_stalk f y
    (Algebra.isSeparableExtension_of_perfectField _ _)

/-! ### Regular quotients and partial systems of parameters -/

section Parameters

variable {R : Type*} [CommRing R]

/-- The ideal generated by the list of values of a family is the span of its range. -/
theorem ofList_ofFn {k : ℕ} (h : Fin k → R) :
    Ideal.ofList (List.ofFn h) = Ideal.span (Set.range h) := by
  simp only [Ideal.ofList, List.mem_ofFn]
  rfl

/-- The range of `Fin.append h t` is the union of the ranges of `h` and `t`. -/
theorem range_append {α : Type*} {k m : ℕ} (h : Fin k → α) (t : Fin m → α) :
    Set.range (Fin.append h t) = Set.range h ∪ Set.range t := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left j => exact Or.inl ⟨j, by simp⟩
    | right j => exact Or.inr ⟨j, by simp⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd _ j, by simp⟩
    · exact ⟨Fin.natAdd _ j, by simp⟩

/-- The span of the range of `Fin.append h t` is the join of the spans of the two ranges. -/
theorem span_range_append {k m : ℕ} (h : Fin k → R) (t : Fin m → R) :
    Ideal.span (Set.range (Fin.append h t)) =
      Ideal.span (Set.range h) ⊔ Ideal.span (Set.range t) := by
  rw [range_append, Ideal.span_union]

variable [IsRegularLocalRing R]

/-- **Quotient by an initial segment of a regular system of parameters.** If `h₁, …, h_k,
t₁, …, t_m` is a regular system of parameters of a regular local ring `R`, then
`R / (h₁, …, h_k)` is a regular local ring, `dim R / (h₁, …, h_k) + k = dim R`, and the images of
`t₁, …, t_m` are a regular system of parameters of `R / (h₁, …, h_k)`. -/
@[mmp "lem_mmp_foundation_laz_regular_parameter_quotients"]
theorem isRegularLocalRing_quotient_of_isRegularSystemOfParameters_append {k m : ℕ}
    {h : Fin k → R} {t : Fin m → R} (hz : IsRegularSystemOfParameters (Fin.append h t)) :
    ∃ _ : IsRegularLocalRing (R ⧸ Ideal.span (Set.range h)),
      ringKrullDim (R ⧸ Ideal.span (Set.range h)) + k = ringKrullDim R ∧
        IsRegularSystemOfParameters
          (fun i ↦ Ideal.Quotient.mk (Ideal.span (Set.range h)) (t i)) := by
  set I := Ideal.span (Set.range h)
  have hgen : Ideal.ofList (List.ofFn h ++ List.ofFn t) = maximalIdeal R := by
    rw [Ideal.ofList_append, ofList_ofFn, ofList_ofFn, ← span_range_append, hz.1]
  have hfr : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ((k + m : ℕ) : WithBot ℕ∞) := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal, hz.2]
  have hlen : (List.ofFn h ++ List.ofFn t).length = (maximalIdeal R).spanFinrank := by
    simp only [List.length_append, List.length_ofFn]
    exact_mod_cast hfr.symm
  obtain ⟨-, hq⟩ :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).1
      _ hgen hlen
  obtain ⟨hreg, hdim⟩ := hq k (by simp)
  rw [List.take_left' List.length_ofFn, ofList_ofFn] at hreg hdim
  refine ⟨hreg, hdim, ?_, ?_⟩
  · rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← hz.1, span_range_append, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
      Ideal.map_span, ← Set.range_comp]
    rfl
  · have hN := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ I)
    rw [← hN, hz.2] at hdim
    rw [← hN]
    have : (maximalIdeal (R ⧸ I)).spanFinrank + k = k + m := by exact_mod_cast hdim
    exact_mod_cast (by omega : (maximalIdeal (R ⧸ I)).spanFinrank = m)

/-- **Regular quotients of complementary dimension are exactly quotients by partial regular
parameters.** Let `R` be a regular local ring and `h₁, …, h_k ∈ R`. Then `R / (h₁, …, h_k)` is a
regular local ring with `dim R / (h₁, …, h_k) + k = dim R` if and only if `h₁, …, h_k` extends to
a regular system of parameters `h₁, …, h_k, t₁, …, t_m` of `R`. In that case the images of the
`tᵢ` form a regular system of parameters of the quotient
(`isRegularLocalRing_quotient_of_isRegularSystemOfParameters_append`). -/
@[mmp "lem_mmp_foundation_laz_regular_parameter_quotients"]
theorem isRegularLocalRing_quotient_and_add_eq_iff {k : ℕ} (h : Fin k → R) :
    (IsRegularLocalRing (R ⧸ Ideal.span (Set.range h)) ∧
        ringKrullDim (R ⧸ Ideal.span (Set.range h)) + k = ringKrullDim R) ↔
      ∃ (m : ℕ) (t : Fin m → R), IsRegularSystemOfParameters (Fin.append h t) := by
  refine ⟨fun ⟨hreg, hdim⟩ ↦ ?_, fun ⟨_, _, hz⟩ ↦ ?_⟩
  · rw [← ofList_ofFn] at hreg hdim
    obtain ⟨ts, hsop, hgen⟩ :=
      IsRegularLocalRing.exists_isSystemOfParameters_append_of_isRegularLocalRing_quotient hreg
        (by simpa using hdim)
    have hfn : List.ofFn (Fin.append h fun i : Fin ts.length ↦ ts.get i) = List.ofFn h ++ ts := by
      rw [List.ofFn_fin_append, List.ofFn_get]
    refine ⟨ts.length, fun i ↦ ts.get i, ?_, ?_⟩
    · rw [← ofList_ofFn, hfn, hgen]
    · rw [hsop.2]
      simp
  · obtain ⟨hreg, hdim, -⟩ := isRegularLocalRing_quotient_of_isRegularSystemOfParameters_append hz
    exact ⟨hreg, hdim⟩

/-- **Quotient by a subset of a regular system of parameters.** If `z₁, …, z_n` is a regular
system of parameters of a regular local ring `R` and `s ⊆ {1, …, n}`, then `R / (zᵢ : i ∈ s)` is a
regular local ring of dimension `n - |s|`, with regular system of parameters the classes of the
`z_j`, `j ∉ s` (enumerated in increasing order). -/
@[mmp "lem_mmp_foundation_laz_regular_parameter_quotients"]
theorem isRegularSystemOfParameters_quotient_image {n : ℕ} {z : Fin n → R}
    (hz : IsRegularSystemOfParameters z) (s : Finset (Fin n)) :
    ∃ _ : IsRegularLocalRing (R ⧸ Ideal.span (z '' s)),
      ringKrullDim (R ⧸ Ideal.span (z '' s)) = (n - s.card : ℕ) ∧
        IsRegularSystemOfParameters
          (fun j : Fin sᶜ.card ↦ Ideal.Quotient.mk (Ideal.span (z '' s))
            (z (sᶜ.orderEmbOfFin rfl j))) := by
  set h : Fin s.card → R := z ∘ s.orderEmbOfFin rfl
  set t : Fin sᶜ.card → R := z ∘ sᶜ.orderEmbOfFin rfl
  have hh : Set.range h = z '' s := by
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  have ht : Set.range t = z '' (sᶜ : Finset (Fin n)) := by
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  have hz' : IsRegularSystemOfParameters (Fin.append h t) := by
    refine ⟨?_, ?_⟩
    · rw [range_append, hh, ht, ← Set.image_union, Finset.coe_compl,
        Set.union_compl_self, Set.image_univ, hz.1]
    · rw [hz.2, Finset.card_add_card_compl, Fintype.card_fin]
  have key := isRegularLocalRing_quotient_of_isRegularSystemOfParameters_append hz'
  rw [hh] at key
  obtain ⟨hreg, -, hsop⟩ := key
  refine ⟨hreg, ?_, hsop⟩
  rw [hsop.2, Finset.card_compl, Fintype.card_fin]

end Parameters

/-! ### Local coordinates on a smooth scheme -/

section Coordinates

open KaehlerDifferential

/-- A basis `(d a_i)_i` of `Ω_{S/R}` base-changes along a formally étale `S`-algebra `T` to the
basis `(d a_i)_i` of `Ω_{T/R}`. -/
theorem exists_basis_kaehler_of_formallyEtale {R S T ι : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale S T] (b : Module.Basis ι S Ω[S⁄R]) (a : ι → S)
    (hb : ∀ i, b i = D R S (a i)) :
    ∃ b' : Module.Basis ι T Ω[T⁄R], ∀ i, b' i = D R T (algebraMap S T (a i)) := by
  refine ⟨(b.baseChange T).map (tensorKaehlerEquivOfFormallyEtale R S T), fun i ↦ ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb,
    ← tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, LinearEquiv.apply_symm_apply]

/-- The restriction map `Γ(X, V) → Γ(X, W)` between affine opens `W ⊆ V` is étale. -/
theorem etale_presheaf_map {X : Scheme.{u}} (V W : X.affineOpens) (h : W.1 ≤ V.1) :
    RingHom.Etale (X.presheaf.map (homOfLE h).op).hom := by
  convert HasRingHomProperty.appLE @Etale (𝟙 X) inferInstance V W h using 2
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact (Category.id_comp (X.presheaf.map (homOfLE h).op)).symm

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The restriction `Γ(X, V) → Γ(X, W)` of a scheme over `k` is `k`-linear. -/
theorem isScalarTower_section_res {V W : X.Opens} (h : W ≤ V) :
    letI := sectionAlgebra sX V
    letI := sectionAlgebra sX W
    letI : Algebra Γ(X, V) Γ(X, W) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    IsScalarTower k Γ(X, V) Γ(X, W) := by
  let := sectionAlgebra sX V
  let := sectionAlgebra sX W
  let : Algebra Γ(X, V) Γ(X, W) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have := Scheme.Hom.appLE_map sX (U := ⊤) (V := V) (V' := W) (by simp) (homOfLE h).op
  exact (congrArg (fun t ↦ ((Scheme.ΓSpecIso (.of k)).inv ≫ t).hom) this).symm

/-- **Local coordinates exist on a smooth scheme, in the dimension of the smooth component.** Let
`X` be a smooth scheme over a field `k` and `p ∈ X`. There are an open neighbourhood `U` of `p`
and local coordinates `x_1, …, x_n` on `U` (`MMP.Resolution.IsLocalCoordinatesOn`: the `dx_i` are
a basis of `Ω_{U/k}`). Their number `n` is the rank `rank_p Ω_{X/k}` of the free
`𝒪_{X,p}`-module `Ω_{𝒪_{X,p}/k}`, and it is the local dimension `dim_p X` of `X` at `p`. -/
@[mmp "lem_mmp_foundation_kr_d_local_coordinate_existence"]
theorem exists_isLocalCoordinatesOn [Smooth sX] (p : X) :
    ∃ (U : X.Opens) (_ : p ∈ U) (n : ℕ) (x : Fin n → Γ(X, U)),
      MMP.Resolution.IsLocalCoordinatesOn sX U x ∧
        (letI := stalkAlgebra sX p;
          Module.finrank (X.presheaf.stalk p) (KaehlerDifferential k (X.presheaf.stalk p)) = n) ∧
        topologicalKrullDimAt X p = n := by
  classical
  obtain ⟨U₀, -, V, hV, hpV, e, hstd⟩ := Smooth.exists_isStandardSmooth sX p
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.mpr fun s _ ↦ ?_
    rw [Subsingleton.elim s (sX p)]
    exact e hpV
  subst hU₀
  let algAB : Algebra Γ(Spec (.of k), ⊤) Γ(X, V) := (sX.appLE ⊤ V e).hom.toAlgebra
  have hsm : Algebra.IsStandardSmooth Γ(Spec (.of k), ⊤) Γ(X, V) := hstd
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hsm.out
  have : Finite σ := hσ
  have : Finite ι := hι
  have hdim :=
    Stacks.RelativeDifferentialStalkMap.fiberDimensionAt_eq_of_submersivePresentation sX p ⟨V, hV⟩
    ⟨⊤, isAffineOpen_top _⟩ hpV e rfl P
  rw [topologicalKrullDimAt_fiber_eq] at hdim
  set n := Nat.card ι - Nat.card σ
  have hcard : Nat.card ((Set.range P.map)ᶜ : Set ι) = n :=
    Stacks.RelativeDifferentialStalkMap.natCard_compl_range_map P
  let eqv : ((Set.range P.map)ᶜ : Set ι) ≃ Fin n := (Finite.equivFin _).trans (finCongr hcard)
  let := sectionAlgebra sX V
  let : Algebra k Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).inv.hom.toAlgebra
  have : IsScalarTower k Γ(Spec (.of k), ⊤) Γ(X, V) := IsScalarTower.of_algebraMap_eq' rfl
  have hsurj : Function.Surjective (algebraMap k Γ(Spec (.of k), ⊤)) :=
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective
  let E := Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective k
    Γ(Spec (.of k), ⊤) Γ(X, V) hsurj
  let b : Module.Basis (Fin n) Γ(X, V) (KaehlerDifferential k Γ(X, V)) :=
    (P.basisKaehler.map E.symm).reindex eqv
  let x : Fin n → Γ(X, V) := fun i ↦ P.val (eqv.symm i)
  have hb : ∀ i, b i = D k Γ(X, V) (x i) := by
    intro i
    simp only [b, x, Module.Basis.reindex_apply, Module.Basis.map_apply,
      Algebra.SubmersivePresentation.basisKaehler_apply, LinearEquiv.symm_apply_eq]
    exact (Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective_D k _ _ hsurj _).symm
  refine ⟨V, hpV, n, x, ?_, ?_, hdim⟩
  · intro W h
    let := sectionAlgebra sX W.1
    let : Algebra Γ(X, V) Γ(X, W) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    have : IsScalarTower k Γ(X, V) Γ(X, W) := isScalarTower_section_res sX h
    have : Algebra.Etale Γ(X, V) Γ(X, W) := etale_presheaf_map ⟨V, hV⟩ W h
    exact exists_basis_kaehler_of_formallyEtale b x hb
  · let := stalkAlgebra sX p
    let : Algebra Γ(X, V) (X.presheaf.stalk p) := X.presheaf.algebra_section_stalk ⟨p, hpV⟩
    have : IsScalarTower k Γ(X, V) (X.presheaf.stalk p) :=
      isScalarTower_section_stalk sX V ⟨p, hpV⟩
    have : IsLocalization.AtPrime (X.presheaf.stalk p) (hV.primeIdealOf ⟨p, hpV⟩).asIdeal :=
      hV.isLocalization_stalk ⟨p, hpV⟩
    have : Algebra.FormallyEtale Γ(X, V) (X.presheaf.stalk p) :=
      Algebra.FormallyEtale.of_isLocalization (hV.primeIdealOf ⟨p, hpV⟩).asIdeal.primeCompl
    obtain ⟨b', -⟩ := exists_basis_kaehler_of_formallyEtale (T := X.presheaf.stalk p) b x hb
    rw [Module.finrank_eq_card_basis b', Fintype.card_fin]

end Coordinates

end MMP.Flips.ResolutionInputs
