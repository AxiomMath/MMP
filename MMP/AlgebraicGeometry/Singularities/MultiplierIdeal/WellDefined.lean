module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.Basic
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.IndependentOfResolution
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.PushforwardComparison
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalImagePushforward
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion

/-!
# Multiplier ideals are well defined

Let `X` be a non-singular variety over a field `k` of characteristic zero and `D` an
`ℝ`-divisor on `X`. A multiplier ideal of `D` is `𝒥_μ(X, D) = μ_*𝒪_{X'}(K_{X'/X} - ⌊μ^*D⌋)`
for some log resolution `μ : X' ⟶ X` of `D`. There is exactly one: a log resolution exists
(Hironaka), on it the relative canonical divisor `K_{X'/X}` (the divisor of the Jacobian section)
and its Weil divisor exist, and any two log resolutions give the same submodule of `K(X)`
(Esnault–Viehweg, Lazarsfeld Thm. 9.2.18). So `𝒥(X, D)` is a well-defined function of `D`.

## Main results

* `MMP.Intersection.existsUnique_isMultiplierIdeal`: the multiplier ideal is well defined.

## Implementation notes

Lazarsfeld works over `ℂ`; the multiplier ideal is treated over an arbitrary field of
characteristic zero, the generality of the existence of log resolutions
(`MMP.Intersection.exists_isLogResolution`). A non-singular variety over `k` is
`MMP.Mori.IsVariety k sX` together with `MMP.Mori.IsSmoothScheme sX`. A multiplier ideal is
recorded by its sections over the opens of `X` as subsets of `K(X)`, as in
`MMP.Intersection.IsMultiplierIdeal`.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry II*][lazarsfeld2004], Def. 9.2.1 and
  Thm. 9.2.18.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Intersection

section MultiplierIdeal

/-! ### Divisors of homomorphisms -/

section DivisorOfHom

variable {X : Scheme.{u}} {L M : X.Modules}

/-- Two trivializations of `L` and `M` near `p` represent a homomorphism `φ : L ⟶ M` by
functions whose germs at `p` differ by a unit of `𝒪_{X,p}`. -/
private theorem exists_germ_eq_mul_units (φ : L ⟶ M) {U U' : X.Opens} {e : Γ(L, U)}
    {e' : Γ(M, U)} {f : Γ(L, U')} {f' : Γ(M, U')}
    (he : IsTrivializingGenerator L U e) (he' : IsTrivializingGenerator M U e')
    (hf : IsTrivializingGenerator L U' f) (hf' : IsTrivializingGenerator M U' f')
    {r : Γ(X, U)} {s : Γ(X, U')} (hr : φ.app U e = r • e') (hs : φ.app U' f = s • f')
    {p : X} (hp : p ∈ U) (hp' : p ∈ U') :
    ∃ w : (X.presheaf.stalk p)ˣ, X.presheaf.germ U' p hp' s = X.presheaf.germ U p hp r * w := by
  let W : X.Opens := U ⊓ U'
  have hpW : p ∈ W := ⟨hp, hp'⟩
  let i : W ⟶ U := homOfLE inf_le_left
  let j : W ⟶ U' := homOfLE inf_le_right
  have heW := he.res (inf_le_left : W ≤ U)
  have he'W := he'.res (inf_le_left : W ≤ U)
  have hfW := hf.res (inf_le_right : W ≤ U')
  have hf'W := hf'.res (inf_le_right : W ≤ U')
  obtain ⟨a, ha⟩ := heW.bijective.2 (L.presheaf.map j.op f)
  obtain ⟨b, hb⟩ := hfW.bijective.2 (L.presheaf.map i.op e)
  obtain ⟨a', ha'⟩ := he'W.bijective.2 (M.presheaf.map j.op f')
  obtain ⟨b', hb'⟩ := hf'W.bijective.2 (M.presheaf.map i.op e')
  simp only at ha hb ha' hb'
  have hab' : a' * b' = 1 := by
    apply hf'W.bijective.1
    simp only
    rw [← smul_smul, hb', ha', one_smul]
  have hab : b * a = 1 := by
    apply heW.bijective.1
    simp only
    rw [← smul_smul, ha, hb, one_smul]
  have hnat : ∀ {Y Z : X.Opens} (k : Y ⟶ Z) (m : Γ(L, Z)),
      φ.app Y (L.presheaf.map k.op m) = M.presheaf.map k.op (φ.app Z m) := fun k m =>
    ConcreteCategory.congr_hom (φ.mapPresheaf.naturality k.op) m
  have key : a * X.presheaf.map i.op r = X.presheaf.map j.op s * a' := by
    apply he'W.bijective.1
    simp only
    rw [← smul_smul, ← smul_smul, ha', ← Scheme.Modules.map_smul, ← Scheme.Modules.map_smul,
      ← hr, ← hs, ← hnat, ← hnat, ← Scheme.Modules.Hom.app_smul, ha]
  have hu : IsUnit (X.presheaf.germ W p hpW (a * b')) := by
    refine IsUnit.of_mul_eq_one (X.presheaf.germ W p hpW (b * a')) ?_
    rw [← map_mul, show a * b' * (b * a') = (b * a) * (a' * b') by ring, hab, hab', mul_one,
      map_one]
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, ← TopCat.Presheaf.germ_res_apply X.presheaf j p hpW,
    ← TopCat.Presheaf.germ_res_apply X.presheaf i p hpW, ← map_mul]
  congr 1
  calc X.presheaf.map j.op s = X.presheaf.map j.op s * (a' * b') := by rw [hab', mul_one]
    _ = _ := by rw [← mul_assoc, ← key]; ring

/-- A homomorphism `φ` of line bundles is represented near every point by a function. -/
private theorem exists_isTrivializingGenerator_app_eq_smul [Stacks.Ample.IsInvertibleModule X L]
    [Stacks.Ample.IsInvertibleModule X M] (φ : L ⟶ M) (x : X) :
    ∃ (U : X.Opens) (e : Γ(L, U)) (e' : Γ(M, U)) (r : Γ(X, U)), x ∈ U ∧
      IsTrivializingGenerator L U e ∧ IsTrivializingGenerator M U e' ∧ φ.app U e = r • e' := by
  obtain ⟨U₁, -, e₁, hx₁, he₁⟩ := exists_isTrivializingGenerator L (V := ⊤) (x := x) trivial
  obtain ⟨U, hU, e', hx, he'⟩ := exists_isTrivializingGenerator M hx₁
  obtain ⟨r, hr⟩ := he'.bijective.2 (φ.app U (L.presheaf.map (homOfLE hU).op e₁))
  exact ⟨U, _, e', r, hx, he₁.res hU, he', hr.symm⟩

/-- **The divisor of a regular homomorphism of line bundles exists**: a regular `φ : L ⟶ M`
between invertible modules on a locally Noetherian scheme has a divisor `div(φ)`. -/
private theorem exists_isDivisorOfHom [IsLocallyNoetherian X]
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X M] {φ : L ⟶ M}
    (hφ : IsRegularHom φ) : ∃ D : X.CartierDivisor, IsDivisorOfHom φ D := by
  have hunit : ∀ (U : X.Opens) (e : Γ(L, U)) (e' : Γ(M, U)), IsTrivializingGenerator L U e →
      IsTrivializingGenerator M U e' → ∀ r : Γ(X, U), φ.app U e = r • e' →
        IsUnit (toTotalQuotient U r) := fun U e e' he he' r hr =>
    isUnit_toTotalQuotientSheaf_app X.sheaf U r (hφ U e e' he he' r hr)
  choose U e e' r hx he he' hr using exists_isTrivializingGenerator_app_eq_smul φ
  have hu := fun x => hunit (U x) (e x) (e' x) (he x) (he' x) (r x) (hr x)
  obtain ⟨D, hD⟩ := exists_isLocalEquationOn_of_germ_eq_mul U
    (eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩)
    (fun x => (hu x).unit) (fun i j p hi hj => by
      obtain ⟨w, hw⟩ := exists_germ_eq_mul_units φ (he i) (he' i) (he j) (he' j) (hr i) (hr j)
        hi hj
      refine ⟨w, ?_⟩
      simp only [IsUnit.unit_spec, germ_toTotalQuotient, hw, map_mul])
  refine ⟨D, hφ, fun x => ⟨U x, hx x, r x, hu x, hD x⟩, fun V f f' hf hf' s hs => ?_⟩
  have hsu := hunit V f f' hf hf' s hs
  refine ⟨hsu, isLocalEquationOn_of_forall_isLocalEquationAt fun p hp => ?_⟩
  obtain ⟨w, hw⟩ := exists_germ_eq_mul_units φ (he p) (he' p) hf hf' (hr p) hs (hx p) hp
  have := (show IsLocalEquationAt D p _ from ⟨U p, hx p, (hu p).unit, hD p, rfl⟩).mul_units w
  simpa only [IsUnit.unit_spec, germ_toTotalQuotient, hw, map_mul] using this

end DivisorOfHom

/-- An integral scheme locally of finite type over a field has finite Krull dimension. -/
private theorem exists_topologicalKrullDim_eq {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType f] :
    ∃ n : ℕ, topologicalKrullDim Y = n := by
  have h := Stacks.Chow.topologicalKrullDim_closure_singleton_eq k f (genericPoint Y)
  rw [(genericPoint_spec Y).def,
    (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq] at h
  exact ⟨_, h⟩

/-- The relative canonical divisor `K_{X'/X}` of a birational morphism of non-singular
varieties exists. -/
private theorem exists_isRelativeCanonicalDivisor {k : Type u} [Field k] {X V : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral V] [MMP.Mori.IsVariety k sX]
    (hX : MMP.Mori.IsSmoothScheme sX) {g : V ⟶ X} [MMP.Mori.IsVariety k (g ≫ sX)]
    (hV : MMP.Mori.IsSmoothScheme (g ≫ sX)) (hg : MMP.Mori.IsBirationalMorphism g) :
    ∃ K : V.CartierDivisor, IsRelativeCanonicalDivisor sX g K := by
  haveI : LocallyOfFiniteType sX := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (g ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : LocallyOfFinitePresentation (g ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff _).mp hX
  haveI : Smooth (g ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mp hV
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq (g ≫ sX)
  have hdX : topologicalKrullDim X = topologicalKrullDim V :=
    topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hg
  have := smoothOfRelativeDimension_of_isVariety sX n (hdX.trans hn)
  have := smoothOfRelativeDimension_of_isVariety (g ≫ sX) n hn
  have hiX := Stacks.Discriminant.isInvertible_relativeDifferentialForms sX n
  haveI : Stacks.Ample.IsInvertibleModule V (Scheme.Hom.relativeDifferentialForms (g ≫ sX) n) :=
    Stacks.Discriminant.isInvertible_relativeDifferentialForms (g ≫ sX) n
  haveI : Stacks.Ample.IsInvertibleModule V ((Scheme.Modules.pullback g).obj
      (Scheme.Hom.relativeDifferentialForms sX n)) :=
    @Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback _ _
      g.toLRSHom.toShHom _ hiX
  have hreg := isRegularHom_jacobianSection sX hg n
  obtain ⟨K, hK⟩ := exists_isDivisorOfHom hreg
  exact ⟨K, n, hn, Or.inl ⟨hreg, hK⟩⟩

/-- **The multiplier ideal is well defined** (Lazarsfeld Def. 9.2.1 with Thm. 9.2.18): an
`ℝ`-divisor `D` on a non-singular variety `X` over a field of characteristic zero has exactly one
multiplier ideal `𝒥(X, D)` in the sense of `MMP.Intersection.IsMultiplierIdeal`. -/
@[mmp "lem_p09a_multiplier_ideal_well_defined"]
theorem existsUnique_isMultiplierIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] (sX : X ⟶ Spec (.of k)) [hX : MMP.Mori.IsVariety k sX]
    (hXs : MMP.Mori.IsSmoothScheme sX) (D : RCartierDivisor X) :
    ∃! J : X.Opens → Set X.functionField, IsMultiplierIdeal sX D J := by
  obtain ⟨X', μ, hμ⟩ := exists_isLogResolution sX hX hXs D
  obtain ⟨-, hb, hv, hs, F, -, hF, -, -⟩ := id hμ
  haveI : MMP.Mori.IsVariety k (μ ≫ sX) := hv
  haveI : IsIntegral X' := AlgebraicGeometry.IsVariety.toIsIntegral (f := μ ≫ sX)
  haveI : LocallyOfFiniteType (μ ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact (μ ≫ sX) := AlgebraicGeometry.IsVariety.toQuasiCompact
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (μ ≫ sX)
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  haveI : IsNoetherian X' := ⟨⟩
  haveI : Smooth (μ ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mp hs
  haveI : IsNormal X' := isNormal_of_smooth_over_field (μ ≫ sX)
  haveI : IsDominant μ := hb.isDominant
  obtain ⟨K, hK⟩ := exists_isRelativeCanonicalDivisor hXs hs hb
  obtain ⟨wK, hwK⟩ := exists_isWeilDivisorOfCartier K
  have hJ₀ : IsMultiplierIdealOn sX D μ
      (multiplierIdealSections μ (wK - WeilRDivisor.roundDown F)) :=
    ⟨hμ, inferInstance, inferInstance, inferInstance, inferInstance, K, wK, F, hK, hwK, hF, rfl⟩
  exact ⟨_, ⟨X', μ, hJ₀⟩, fun J ⟨_, _, hJ⟩ => IsMultiplierIdealOn.unique hX hXs hJ hJ₀⟩

end MultiplierIdeal

end MMP.Intersection

end
