module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.Singularities.Surface.ArtinRationalityCriterion
import MMP.AlgebraicGeometry.Cohomology.FormalFunctionsDegreeZero
import MMP.AlgebraicGeometry.MMP.Fourfold.AffineBaseRegularGeneration
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Intersection.Surface.BlowupGenusDropAdjunction
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolution
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi

/-!
# Numerically trivial divisors near a rational surface singularity are principal

Let `f : Y ⟶ X` be the minimal resolution of a rational surface singularity `(X, P)` over an
algebraically closed field `k`, and let `D` be a Cartier divisor on `Y` with `(D · E) = 0` for
every exceptional curve `E`. Then `D = div(φ)` over a neighbourhood of `P` for a rational
function `φ`.

Write `L = 𝒪_Y(D)`, `A = 𝒪_{X,P}` with maximal ideal `𝔪`, and `X_n = Y ×_X Spec (A/𝔪ⁿ)` for
the thickenings of the fibre `f⁻¹(P)`; `X_1` is the scheme-theoretic fibre.

* If `f` has no exceptional curve, the fibre is at most one point (it is connected, `X` being
  normal), and a local frame of `L` at that point is a local equation of `D` on a neighbourhood
  of the fibre.
* Otherwise the exceptional curves are finitely many and cover the fibre, so every `X_n` is a
  closed subscheme of a cycle `N · ∑ Eᵢ`. Since `(R¹f_*𝒪_Y)_P = 0`, every nonzero exceptional
  cycle `Z` has `H¹(𝒪_Z) = 0`, hence `χ(𝒪_Z) = h⁰(𝒪_Z) ≥ 1`, and a line bundle of degree zero on
  every exceptional curve is trivial on every exceptional cycle. So `L|_{X_n}` has a nowhere
  vanishing section for every `n`.
* The modules `Γ(X_n, L|_{X_n})` are Artinian over `A`, so the images of the restriction maps
  into `Γ(X_1, L|_{X_1})` stabilize; their stable value contains a nowhere vanishing section,
  which by the Mittag-Leffler argument is the first component of a compatible family. By the
  theorem on formal functions this family comes from the `𝔪`-adic completion of `(f_* L)_P`,
  and, `𝔪` killing `Γ(X_1, L|_{X_1})`, its first component is the restriction of a section `s`
  of `L` over `f⁻¹(U₀)` for an open `U₀ ∋ P`.
* The section `s` vanishes nowhere on the fibre; its nonvanishing locus `W` is open, and a
  section of `L` vanishing nowhere on `W` trivializes `L|_W`, i.e. gives a local equation of `D`
  on `W`. The image under the proper `f` of the complement of `W` is closed and misses `P`;
  its complement is the required neighbourhood of `P`.

## Main results

* `MMP.Flips.IsMinimalGermResolution.exists_mem_isLocalEquation_preimage`: the principality of
  `D` over a neighbourhood of `P`.

## Implementation notes

Cycles `∑ nᵢ Eᵢ` are handled as multisets of prime divisors with ideal `∏ I_{Eᵢ}`. The
restriction maps of the tower `Γ(X_n, L|_{X_n})` are stated once for an arbitrary factorization
`a ≫ b = c` of morphisms of schemes and only then instantiated at the thickenings: their
compatibility with composition comes from the units of the closed immersions `X_n ⟶ Y` being
epimorphisms.

The positivity `χ(𝒪_Z) > 0` of the nonzero exceptional cycles is not read off a weighted dual
graph of `f` through Artin's criterion; it is the first step of the proof of that criterion:
`(R¹f_*𝒪_Y)_P = 0` kills `H¹(𝒪_Z)` by the theorem on formal functions, so
`χ(𝒪_Z) = h⁰(𝒪_Z) ≥ 1`. The Mittag-Leffler argument runs over the thickenings `X_n`, which are
cofinal with the cycles `n · ∑ Eᵢ`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 3.4
* [J. Lipman, *Rational singularities with applications to algebraic surfaces and unique
  factorization*][Lipman1969], §12
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori

/-! ### First cohomology along closed immersions into curves -/

section Descent

/-- **`H¹(G) ⟶ H¹(G / 𝓘ⁿ G)` is surjective when `H²(𝓘ⁿ G) = 0`**: the long exact sequence of
`0 ⟶ 𝓘ⁿ G ⟶ G ⟶ G / 𝓘ⁿ G ⟶ 0`. -/
private theorem surjective_rightDerived_one_map_cokernel_π {T : Scheme.{u}}
    (J : T.IdealSheafData) (n : ℕ) (G : T.Modules)
    (h : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived (1 + 1)).obj
      (Stacks.Algebraization.idealPowerMultiple J n G).toSheafOfModules)) :
    Function.Surjective (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived 1).map
      (cokernel.π (Stacks.Algebraization.idealPowerMultiple J n G).ι)) := by
  let S : ShortComplex T.Modules :=
    ShortComplex.mk _ _ (cokernel.condition (Stacks.Algebraization.idealPowerMultiple J n G).ι)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
      mono_f := by dsimp [S]; infer_instance
      epi_g := by dsimp [S]; first | exact coequalizer.π_epi | exact cokernel.π_epi _ }
  exact (ModuleCat.epi_iff_surjective _).1
    (Stacks.Cohomology.RightDerivedDelta.epi_rightDerived_map_g hS _ 1 h)

/-- **`H¹` descends along a closed immersion into a Noetherian scheme of dimension at most one.**
If `t : T ⟶ T'` is a closed immersion, `T'` is Noetherian of dimension at most one and `G` is
quasi-coherent on `T'` with `H¹(T', G) = 0`, then `H¹(T, t^* G) = 0`: the cokernel of
`H¹(T', G) ⟶ H¹(T', G / 𝓘 G)` lies in `H²(T', 𝓘 G) = 0`, and `G / 𝓘 G = t_* t^* G`. -/
private theorem subsingleton_rightDerived_one_pullback {T T' : Scheme.{u}} (t : T ⟶ T')
    [IsClosedImmersion t] [IsNoetherian T'] (hdim : topologicalKrullDim T' ≤ 1)
    (G : T'.Modules) [G.IsQuasicoherent]
    (h : Subsingleton
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections T').rightDerived 1).obj G)) :
    Subsingleton (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived 1).obj
      ((Scheme.Modules.pullback t).obj G)) := by
  have h3 := (surjective_rightDerived_one_map_cokernel_π t.ker 1 G
    ((Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      T'.ringCatSheaf ⊤ 2 _).2
      (Stacks.AlgebraicGeometry.FibreDimension.isZero_hgroup_of_topologicalKrullDim_le _
        (d := 1) (by exact_mod_cast hdim) (by norm_num)))).subsingleton
  have e := ((Stacks.Cohomology.AffineBase.moduleGlobalSections T').rightDerived 1).mapIso
      (Stacks.Algebraization.idealQuotientPushforwardIso t.ker 1 G t (pow_one _).symm) ≪≫
    Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward t
      ((Scheme.Modules.pullback t).obj G) 1
  exact @Equiv.subsingleton _ _ e.toLinearEquiv.toEquiv.symm h3

end Descent

/-! ### First cohomology of structure sheaves -/

section StructureSheaf

/-- The structure sheaf pulls back to the structure sheaf. -/
private def pullbackObjUnitIso {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (Scheme.Modules.pullback i).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
  Stacks.PullbackAlgebra.pullbackUnitIso i.toLRSHom.toShHom

/-- **`H¹(𝒪)` descends along a closed immersion into a Noetherian scheme of dimension at most
one.** -/
private theorem subsingleton_rightDerived_one_unit {T T' : Scheme.{u}} (t : T ⟶ T')
    [IsClosedImmersion t] [IsNoetherian T'] (hdim : topologicalKrullDim T' ≤ 1)
    (h : Subsingleton (((Stacks.Cohomology.AffineBase.moduleGlobalSections T').rightDerived 1).obj
      (SheafOfModules.unit T'.ringCatSheaf))) :
    Subsingleton (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived 1).obj
      (SheafOfModules.unit T.ringCatSheaf)) := by
  have h' := subsingleton_rightDerived_one_pullback t hdim (SheafOfModules.unit T'.ringCatSheaf) h
  exact @Equiv.subsingleton _ _ (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived
    1).mapIso (pullbackObjUnitIso t)).toLinearEquiv.toEquiv.symm h'

end StructureSheaf

/-! ### The theorem on formal functions at the closed point -/

section FormalFunctions

open Stacks.FormalFunctions Stacks.Cohomology.FormalFunctions Stacks.AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f] [IsLocallyNoetherian X] (P : X)

/-- **The fibres of `Y ×_X Spec 𝒪_{X,P} ⟶ Spec 𝒪_{X,P}` are no bigger than those of `f`.** The
projection to `Y` is a base change of the preimmersion `Spec 𝒪_{X,P} ⟶ X`, hence an embedding,
and it carries the fibre over `s` into the fibre of `f` over the image of `s`. -/
private theorem topologicalKrullDim_fiber_stalkBaseChangeStructure_le {d : ℕ}
    (hfib : ∀ x : X, topologicalKrullDim (f ⁻¹' {x}) ≤ d) (s : Spec (X.presheaf.stalk P)) :
    topologicalKrullDim ((stalkBaseChangeStructure f P).fiber s) ≤ d := by
  rw [IsHomeomorph.topologicalKrullDim_eq _
    ((stalkBaseChangeStructure f P).fiberHomeo s).isHomeomorph]
  have hemb : Topology.IsEmbedding (stalkBaseChangeι f P) :=
    IsPreimmersion.isEmbedding (stalkBaseChangeι f P)
  have hind : Topology.IsInducing
      (fun z : ((stalkBaseChangeStructure f P) ⁻¹' {s}) => stalkBaseChangeι f P z.1) :=
    hemb.isInducing.comp Topology.IsInducing.subtypeVal
  refine
    (Stacks.AlgebraicGeometry.FibreDimension.topologicalKrullDim_le_of_isInducing_of_range_subset
    hind (S := f ⁻¹' {X.fromSpecStalk P s}) ?_).trans (hfib _)
  rintro _ ⟨⟨z, hz⟩, rfl⟩
  have hz' : stalkBaseChangeStructure f P z = s := hz
  show f (stalkBaseChangeι f P z) = X.fromSpecStalk P s
  rw [← hz', ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

/-- **The first cohomology of every infinitesimal neighbourhood of the fibre vanishes when
`(R¹f_*𝒪_Y)_P` does**, provided all fibres of `f` have dimension at most one. The stalk is
`H¹(X', 𝒪_{X'})`, and `H¹(X', 𝒪_{X'}) ⟶ H¹(X', 𝒪_{X'} / 𝔪ᵐ)` is surjective because
`H²(X', 𝔪ᵐ 𝒪_{X'}) = 0` ([Stacks, Tag 02V7] over `Spec A`, all of whose fibres have dimension
at most one). -/
private theorem subsingleton_infinitesimalCohomology_of_subsingleton_stalk
    (hfib : ∀ x : X, topologicalKrullDim (f ⁻¹' {x}) ≤ 1)
    (h : Subsingleton ((((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit Y.ringCatSheaf)).presheaf.stalk P)) (m : ℕ) :
    Subsingleton (infinitesimalCohomology f (SheafOfModules.unit Y.ringCatSheaf) P 1 m) := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨e⟩ := nonempty_higherDirectImageStalkLinearEquiv f
    (SheafOfModules.unit Y.ringCatSheaf) P 1
  have hH := @Equiv.subsingleton _ _ e.toEquiv.symm h
  refine @Equiv.subsingleton _ _ (infinitesimalCohomologyEquiv f _ P 1 m).toEquiv.symm ?_
  haveI : (stalkBaseChangeModule f (SheafOfModules.unit Y.ringCatSheaf) P).IsCoherent :=
    isCoherent_pullback _ _
  set O' := stalkBaseChangeModule f (SheafOfModules.unit Y.ringCatSheaf) P
  haveI : (Stacks.Algebraization.idealPowerMultiple (infinitesimalBaseIdealSheaf f P) m
      O').toSheafOfModules.IsCoherent := Stacks.Algebraization.isCoherent_idealPowerMultiple _ _ _
  exact @Function.Surjective.subsingleton _ _ _ hH
    (surjective_rightDerived_one_map_cokernel_π _ m O'
      (FibreDimension.isZero_rightDerived_moduleGlobalSections_of_affine_base
        (stalkBaseChangeStructure f P) (d := 1)
        (topologicalKrullDim_fiber_stalkBaseChangeStructure_le f P hfib) _ (by norm_num)))

end FormalFunctions

/-! ### The thickenings of the closed point -/

section Thickening

open Stacks.FormalFunctions

variable {X : Scheme.{u}}

/-- A global section whose basic open is everything is a unit. -/
private theorem isUnit_of_basicOpen_eq_top {Z : Scheme.{u}} (f : Γ(Z, ⊤))
    (h : Z.basicOpen f = ⊤) : IsUnit f := by
  have hu := RingedSpace.isUnit_res_basicOpen Z.toRingedSpace f
  have e : Opposite.op (⊤ : Z.Opens) = Opposite.op (Z.toRingedSpace.basicOpen f) := by
    rw [show Z.toRingedSpace.basicOpen f = Z.basicOpen f from rfl, h]
  have : (homOfLE (RingedSpace.basicOpen_le Z.toRingedSpace f)).op = eqToHom e := rfl
  rw [this] at hu
  exact (isUnit_map_iff
    ((Z.toRingedSpace.presheaf.mapIso (eqToIso e)).commRingCatIsoToRingEquiv) f).1 hu

/-- `Spec (𝒪_{X,P}/𝔪ᵐ) ⟶ X` has image in `{P}`. -/
private theorem range_infinitesimalBase_subset (P : X) (m : ℕ) :
    Set.range (infinitesimalBase P m) ⊆ {P} := by
  rintro _ ⟨z, rfl⟩
  rw [infinitesimalBase, Scheme.Hom.comp_apply]
  have : (Spec.map (toStalkQuotient P m)) z = IsLocalRing.closedPoint (X.presheaf.stalk P) := by
    apply PrimeSpectrum.ext
    rw [IsLocalRing.closedPoint]
    refine ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
      (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    have h1 : stalkMaximalIdeal P ^ m ≤ ((Spec.map (toStalkQuotient P m)) z).asIdeal := by
      intro a ha
      show (toStalkQuotient P m).hom a ∈ z.asIdeal
      have : (toStalkQuotient P m).hom a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
      rw [this]
      exact z.asIdeal.zero_mem
    exact Ideal.IsPrime.le_of_pow_le h1
  rw [this, Scheme.fromSpecStalk_closedPoint]
  rfl

/-- **`Spec (𝒪_{X,P}/𝔪ᵐ) ⟶ X` is a closed immersion at a closed point**: it is a preimmersion
with closed image. -/
private theorem isClosedImmersion_infinitesimalBase {P : X} (hP : IsClosed ({P} : Set X))
    (m : ℕ) : IsClosedImmersion (infinitesimalBase P m) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rcases Set.subset_singleton_iff_eq.1 (range_infinitesimalBase_subset P m) with h | h <;>
    rw [h]
  · exact isClosed_empty
  · exact hP

/-- **A morphism from a quasi-compact scheme onto a closed point factors through a
thickening of the point.** If `h : Z ⟶ X` maps every point to the closed point `P` of the
locally Noetherian `X`, then `h` factors through `Spec (𝒪_{X,P}/𝔪ᵐ) ⟶ X` for some `m`: on an
affine neighbourhood `Spec R` of `P`, with `P` the prime `q`, elements outside `q` become units
on `Z` and elements of `q` nilpotent, so `R ⟶ Γ(Z, 𝒪_Z)` factors through `R_q / q^m R_q`. -/
private theorem exists_comp_infinitesimalBase_eq [IsLocallyNoetherian X] {P : X}
    {Z : Scheme.{u}} [CompactSpace Z] (h : Z ⟶ X) (hh : ∀ z, h z = P) :
    ∃ (m : ℕ) (L : Z ⟶ Spec (stalkQuotient P m)), L ≫ infinitesimalBase P m = h := by
  obtain ⟨U, hU, hPU, -⟩ := exists_isAffineOpen_mem_and_subset (x := P) (U := ⊤) trivial
  have hrange : Set.range h ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, hh z]
    exact hPU
  set h0 := IsOpenImmersion.lift U.ι h hrange
  have hh0 : h0 ≫ U.ι = h := IsOpenImmersion.lift_fac _ _ _
  set h1 := h0 ≫ hU.isoSpec.hom
  have hh1 : h1 ≫ hU.fromSpec = h := by
    rw [← hU.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc, hh0]
  set q := hU.primeIdealOf ⟨P, hPU⟩
  have hq : ∀ z, h1 z = q := fun z => hU.fromSpec.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hh1, hh z, hU.fromSpec_primeIdealOf])
  set φ : Γ(X, U) →+* Γ(Z, ⊤) := ((Scheme.ΓSpecIso Γ(X, U)).inv ≫ h1.appTop).hom with hφ
  have hmem : ∀ a z, z ∈ Z.basicOpen (φ a) ↔ a ∉ q.asIdeal := by
    intro a z
    have hb : Z.basicOpen (φ a) = h1 ⁻¹ᵁ (Spec Γ(X, U)).basicOpen ((Scheme.ΓSpecIso _).inv a) :=
      (Scheme.preimage_basicOpen h1 _).symm
    rw [hb, basicOpen_eq_of_affine]
    show h1 z ∈ PrimeSpectrum.basicOpen a ↔ _
    rw [hq z]
    rfl
  have hnil : ∀ a ∈ q.asIdeal, IsNilpotent (φ a) := fun a ha =>
    (Scheme.isNilpotent_iff_basicOpen_eq_bot _).2
      (eq_bot_iff.2 fun z hz => ((hmem a z).1 hz ha).elim)
  have hunit : ∀ s ∉ q.asIdeal, IsUnit (φ s) := fun s hs =>
    isUnit_of_basicOpen_eq_top _ (eq_top_iff.2 fun z _ => (hmem s z).2 hs)
  letI : Algebra Γ(X, U) (X.presheaf.stalk P) := (X.presheaf.germ U P hPU).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk P) q.asIdeal :=
    hU.isLocalization_stalk ⟨P, hPU⟩
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let φ' : X.presheaf.stalk P →+* Γ(Z, ⊤) :=
    IsLocalization.lift (M := q.asIdeal.primeCompl) (g := φ) (fun y => hunit y.1 y.2)
  have hφ' : ∀ a, φ' (algebraMap _ _ a) = φ a := IsLocalization.lift_eq _
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (I := Ideal.map φ q.asIdeal)
    (J := ⊥) (Ideal.map_le_iff_le_comap.2 fun a ha => by
      obtain ⟨n, hn⟩ := hnil a ha
      exact Ideal.mem_comap.2 ⟨n, hn ▸ Ideal.zero_mem _⟩)
    (Ideal.FG.map (IsNoetherian.noetherian q.asIdeal) φ)
  have hker : ∀ a ∈ stalkMaximalIdeal P ^ e, φ' a = 0 := by
    intro a ha
    have h1 : stalkMaximalIdeal P ^ e =
        Ideal.map (algebraMap Γ(X, U) (X.presheaf.stalk P)) (q.asIdeal ^ e) := by
      rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal]
    rw [h1] at ha
    have h2 := Ideal.mem_map_of_mem φ' ha
    rw [Ideal.map_map, IsLocalization.lift_comp, Ideal.map_pow] at h2
    exact Ideal.mem_bot.1 (he h2)
  let ψ : stalkQuotient P e ⟶ Γ(Z, ⊤) := CommRingCat.ofHom (Ideal.Quotient.lift _ φ' hker)
  refine ⟨e, Z.toSpecΓ ≫ Spec.map ψ, ?_⟩
  have hcomp : X.presheaf.germ U P hPU ≫ toStalkQuotient P e ≫ ψ =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ h1.appTop := by
    ext a
    exact hφ' a
  have hSpec : Z.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso Γ(X, U)).inv ≫ h1.appTop) = h1 := by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  rw [infinitesimalBase, ← hU.fromSpecStalk_eq_fromSpecStalk hPU, IsAffineOpen.fromSpecStalk,
    ← hh1, ← hSpec, ← hcomp, Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc]

/-- The `m`-th thickening `X_m ⟶ Y` of the fibre over a closed point is a closed immersion, the
base change of `Spec (𝒪_{X,P}/𝔪ᵐ) ⟶ X`. -/
private theorem isClosedImmersion_infinitesimalι {Y : Scheme.{u}} (f : Y ⟶ X) {P : X}
    (hP : IsClosed ({P} : Set X)) (m : ℕ) : IsClosedImmersion (infinitesimalι f P m) := by
  haveI := isClosedImmersion_infinitesimalBase hP m
  exact inferInstanceAs (IsClosedImmersion (pullback.fst f (infinitesimalBase P m)))

/-- The thickening `X_m` lies over `P`. -/
private theorem range_infinitesimalι_subset {Y : Scheme.{u}} (f : Y ⟶ X) (P : X) (m : ℕ) :
    Set.range (infinitesimalι f P m) ⊆ f.base ⁻¹' {P} := by
  rintro _ ⟨z, rfl⟩
  show f (infinitesimalι f P m z) ∈ ({P} : Set X)
  rw [← Scheme.Hom.comp_apply, infinitesimalι_comp, Scheme.Hom.comp_apply]
  exact range_infinitesimalBase_subset P m ⟨_, rfl⟩

/-- **A closed subscheme lying over a closed point lies in a thickening of the fibre.** If
`t : T ⟶ Y` is a closed immersion from a quasi-compact scheme with `f ∘ t` constant `P`, then
`t` factors through a closed immersion `T ⟶ X_m` for some `m`. -/
private theorem exists_isClosedImmersion_comp_infinitesimalι_eq [IsLocallyNoetherian X]
    {Y : Scheme.{u}} (f : Y ⟶ X) {P : X} (hP : IsClosed ({P} : Set X)) {T : Scheme.{u}}
    [CompactSpace T] (t : T ⟶ Y) [IsClosedImmersion t] (ht : ∀ z, f (t z) = P) :
    ∃ (m : ℕ) (t' : T ⟶ infinitesimalNeighbourhood f P m),
      IsClosedImmersion t' ∧ t' ≫ infinitesimalι f P m = t := by
  obtain ⟨m, L, hL⟩ := exists_comp_infinitesimalBase_eq (t ≫ f) ht
  have hfac : pullback.lift t L hL.symm ≫ infinitesimalι f P m = t := pullback.lift_fst _ _ _
  refine ⟨m, pullback.lift t L hL.symm, ?_, hfac⟩
  haveI := isClosedImmersion_infinitesimalι f hP m
  haveI : IsClosedImmersion (pullback.lift t L hL.symm ≫ infinitesimalι f P m) := by
    rw [hfac]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (infinitesimalι f P m)

end Thickening

/-! ### Cycles of exceptional curves -/

section Cycles

variable {Y : Scheme.{u}}

/-- The ideal sheaf `∏_{E ∈ m} I_E` of the cycle `∑_{E ∈ m} E`. -/
private def cycleIdeal (m : Multiset (MMP.Mori.PrimeDivisor Y)) : Y.IdealSheafData :=
  (m.map fun E => E.idealSheaf).prod

private theorem cycleIdeal_zero : cycleIdeal (0 : Multiset (MMP.Mori.PrimeDivisor Y)) = ⊤ := by
  simp [cycleIdeal, Scheme.IdealSheafData.one_eq_top]

private theorem cycleIdeal_cons (E : MMP.Mori.PrimeDivisor Y)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    cycleIdeal (E ::ₘ m) = E.idealSheaf * cycleIdeal m := by
  simp [cycleIdeal]

private theorem mem_support_cycleIdeal (m : Multiset (MMP.Mori.PrimeDivisor Y)) (x : Y) :
    x ∈ (cycleIdeal m).support ↔ ∃ E ∈ m, x ∈ E.idealSheaf.support := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [cycleIdeal_zero, Scheme.IdealSheafData.support_top, Multiset.notMem_zero,
      false_and, exists_false, iff_false]
    exact id
  | cons E m ih =>
    rw [cycleIdeal_cons, Scheme.IdealSheafData.support_mul, ← SetLike.mem_coe,
      TopologicalSpace.Closeds.coe_sup, Set.mem_union, SetLike.mem_coe, SetLike.mem_coe, ih]
    simp

/-- A cycle of curves has dimension at most one. -/
private theorem topologicalKrullDim_cycleIdeal_le (m : Multiset (MMP.Mori.PrimeDivisor Y))
    (hm : ∀ E ∈ m, topologicalKrullDim E.idealSheaf.subscheme ≤ 1) :
    topologicalKrullDim (cycleIdeal m).subscheme ≤ 1 := by
  classical
  rw [topologicalKrullDim_subscheme]
  have : ((cycleIdeal m).support : Set Y) =
      ⋃ E ∈ m.toFinset, ((E.idealSheaf.support : TopologicalSpace.Closeds Y) : Set Y) := by
    ext x
    simp only [Set.mem_iUnion, Multiset.mem_toFinset, exists_prop]
    exact mem_support_cycleIdeal m x
  rw [this]
  exact topologicalKrullDim_biUnion_le _ (fun E => E.idealSheaf.support.isClosed)
    fun E hE => by
      rw [← topologicalKrullDim_subscheme]
      exact hm E (Multiset.mem_toFinset.mp hE)

/-- The divisor `∑_{E ∈ m} E`. -/
private def cycleDivisor (m : Multiset (MMP.Mori.PrimeDivisor Y)) : Divisor Y :=
  (m.map fun E => Finsupp.single E (1 : ℤ)).sum

private theorem cycleDivisor_cons (E : MMP.Mori.PrimeDivisor Y)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    cycleDivisor (E ::ₘ m) = Finsupp.single E 1 + cycleDivisor m := by
  simp [cycleDivisor]

private theorem cycleDivisor_apply (m : Multiset (MMP.Mori.PrimeDivisor Y))
    (C : MMP.Mori.PrimeDivisor Y) [DecidableEq (MMP.Mori.PrimeDivisor Y)] :
    cycleDivisor m C = m.count C := by
  induction m using Multiset.induction_on with
  | empty => simp [cycleDivisor]
  | cons E m ih =>
    rw [cycleDivisor_cons, Finsupp.add_apply, ih, Finsupp.single_apply, Multiset.count_cons]
    by_cases h : E = C
    · subst h; simp [add_comm]
    · simp [h, Ne.symm h]

/-- **A multiset is the cycle of its multiplicities**: if `m` counts each prime divisor `C`
exactly `n C` times, then `∏_C I_C ^ {n C} = ∏_{E ∈ m} I_E`. -/
private theorem divisorIdeal_eq_cycleIdeal [DecidableEq (MMP.Mori.PrimeDivisor Y)]
    {n : MMP.Mori.PrimeDivisor Y → ℕ} {m : Multiset (MMP.Mori.PrimeDivisor Y)}
    (hm : ∀ C, m.count C = n C) : MMP.Resolution.divisorIdeal n = cycleIdeal m := by
  rw [cycleIdeal, Finset.prod_multiset_map_count, MMP.Resolution.divisorIdeal]
  refine (finprod_eq_prod_of_mulSupport_subset _ fun C hC => ?_).trans
    (Finset.prod_congr rfl fun C _ => by rw [hm])
  rw [Finset.mem_coe, Multiset.mem_toFinset, ← Multiset.count_ne_zero, hm]
  exact fun h0 => hC (by simp [h0])

/-- The ideal `∏ I_C^{n_C}` of the divisor `∑_{F ∈ m} F` is `∏_{F ∈ m} I_F`. -/
private theorem divisorIdeal_cycleDivisor (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    MMP.Resolution.divisorIdeal (fun C => (cycleDivisor m C).toNat) = cycleIdeal m := by
  classical
  exact divisorIdeal_eq_cycleIdeal fun C => by rw [cycleDivisor_apply, Int.toNat_natCast]

private theorem cycleDivisor_nonneg (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    0 ≤ cycleDivisor m := fun C => by
  classical
  rw [cycleDivisor_apply]
  exact Int.natCast_nonneg _

private theorem mem_of_mem_support_cycleDivisor {m : Multiset (MMP.Mori.PrimeDivisor Y)}
    {C : MMP.Mori.PrimeDivisor Y} (hC : C ∈ (cycleDivisor m).support) : C ∈ m := by
  classical
  rwa [Finsupp.mem_support_iff, cycleDivisor_apply, Nat.cast_ne_zero,
    Multiset.count_ne_zero] at hC

/-- The cycle `n · ∑_{E ∈ m} E` has ideal `(∏_{E ∈ m} I_E) ^ n`. -/
private theorem cycleIdeal_nsmul (m : Multiset (MMP.Mori.PrimeDivisor Y)) (n : ℕ) :
    cycleIdeal (n • m) = cycleIdeal m ^ n := by
  rw [cycleIdeal, cycleIdeal, Multiset.map_nsmul, Multiset.prod_nsmul]

end Cycles

/-! ### `h⁰` and `h¹` on proper schemes of dimension at most one -/

section Cohomology

variable {k : Type u} [Field k]

/-- On a proper scheme of dimension at most one over `k`, `χ(ℱ) = h⁰(ℱ) - h¹(ℱ)`. -/
private theorem eulerCharacteristic_eq_finrank_sub {C : Scheme.{u}} (g : C ⟶ Spec (.of k))
    [IsProper g] (hdim : topologicalKrullDim C ≤ 1) (F : C.Modules) [F.IsCoherent] :
    eulerCharacteristic k g F = (Module.finrank k (cohomologyOverField k g F 0) : ℤ) -
      (Module.finrank k (cohomologyOverField k g F 1) : ℤ) := by
  rw [eulerCharacteristic_eq_finsum]
  have hz : ∀ n : ℕ, 2 ≤ n → Module.finrank k (cohomologyOverField k g F n) = 0 := fun n hn =>
    have := ModuleCat.subsingleton_of_isZero
      (isZero_cohomologyOverField_of_topologicalKrullDim_le k g F (d := 1) (i := n) hdim hn)
    Module.finrank_zero_of_subsingleton
  rw [finsum_eq_sum_of_support_subset
    (f := fun m : ℕ => (-1 : ℤ) ^ m * (Module.finrank k (cohomologyOverField k g F m) : ℤ))
    (s := Finset.range 2) fun m hm => ?_]
  · rw [Finset.sum_range_succ, Finset.sum_range_one]; ring
  · by_contra hn
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hn
    simp [hz m hn] at hm

/-- **A nonempty proper scheme over `k` has `h⁰(𝒪) ≥ 1`**: its ring of global functions is a
nonzero finite-dimensional `k`-vector space, containing the constant `1`. -/
private theorem one_le_finrank_cohomologyOverField_zero_unit {C : Scheme.{u}}
    (g : C ⟶ Spec (.of k)) [IsProper g] [Nonempty C] :
    1 ≤ Module.finrank k (cohomologyOverField k g (SheafOfModules.unit C.ringCatSheaf) 0) := by
  letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
  haveI : Nontrivial Γ(C, ⊤) :=
    Stacks.EmptyLimitCounterexample.nontrivial_Γ_of_nonempty C (Classical.arbitrary C)
  haveI : Module.Finite k Γ(C, ⊤) := by
    have := forall_finiteDimensional_cohomologyOverField_unit k g 0
    exact Module.Finite.equiv (cohomologyOverFieldZeroIsoSections k g
      (SheafOfModules.unit C.ringCatSheaf)).toLinearEquiv
  exact Module.finrank_pos

end Cohomology

/-! ### The fibre over the singular point -/

section Fibre

open Stacks.FormalFunctions

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {P : X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The closed subscheme `∏ I_C^{Z_C}` cut out by an effective divisor `Z`. -/
private abbrev cyc (Z : Divisor Y) : Y.IdealSheafData :=
  MMP.Resolution.divisorIdeal fun C => (Z C).toNat

/-- An effective divisor `Z` is the cycle `∑_{C ∈ m} C` of the multiset `m` of its components
counted with multiplicity. -/
private theorem exists_cyc_eq_cycleIdeal (Z : Divisor Y) (hZ : 0 ≤ Z) :
    ∃ m : Multiset (MMP.Mori.PrimeDivisor Y), cyc Z = cycleIdeal m ∧
      ∀ C, C ∈ m ↔ C ∈ Z.support := by
  classical
  set A : MMP.Mori.PrimeDivisor Y →₀ ℕ := Finsupp.mapRange Int.toNat Int.toNat_zero Z with hA
  set m := Finsupp.toMultiset A with hm
  have hAapp : ∀ C, A C = (Z C).toNat := fun C => Finsupp.mapRange_apply
  have hcount : ∀ C, m.count C = (Z C).toNat := fun C => by
    rw [hm, Finsupp.count_toMultiset, hAapp]
  refine ⟨m, ?_, fun C => ?_⟩
  · exact divisorIdeal_eq_cycleIdeal hcount
  · rw [← Multiset.count_ne_zero, hcount, Finsupp.mem_support_iff, ne_eq, ne_eq,
      Int.toNat_eq_zero]
    exact ⟨fun h h0 => h h0.le, fun h h0 => h (le_antisymm h0 (hZ C))⟩

/-- **An exceptional cycle lies over `P`, has dimension at most one and is nonempty.** -/
private theorem cyc_support_subset_and (hf : IsGermResolution sX P f) {Z : Divisor Y}
    (hZ : 0 ≤ Z) (hZ0 : Z ≠ 0) (hZE : ∀ C ∈ Z.support, IsGermExceptionalCurve f P C) :
    ((cyc Z).support : Set Y) ⊆ f.base ⁻¹' {P} ∧
      topologicalKrullDim (cyc Z).subscheme ≤ 1 ∧ Nonempty (cyc Z).subscheme := by
  obtain ⟨m, hcyc, hm⟩ := exists_cyc_eq_cycleIdeal Z hZ
  have hsub : ((cyc Z).support : Set Y) ⊆ f.base ⁻¹' {P} := by
    intro x hx
    rw [hcyc, SetLike.mem_coe, mem_support_cycleIdeal] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    exact (hZE C ((hm C).1 hC)).1.prop.2 hxC
  refine ⟨hsub, ?_, ?_⟩
  · rw [hcyc]
    exact topologicalKrullDim_cycleIdeal_le m fun C hC =>
      (hZE C ((hm C).1 hC)).2.2.le
  · obtain ⟨C, hC⟩ := Finset.nonempty_of_ne_empty fun h => hZ0 (Finsupp.support_eq_empty.1 h)
    have : IsIntegral C.idealSheaf.subscheme := (hZE C hC).2.1
    obtain ⟨w⟩ := (inferInstance : Nonempty C.idealSheaf.subscheme)
    have hx : C.idealSheaf.subschemeι w ∈ ((cyc Z).support : Set Y) := by
      rw [hcyc, SetLike.mem_coe, mem_support_cycleIdeal]
      refine ⟨C, (hm C).2 hC, ?_⟩
      rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨w, rfl⟩
    rw [← Scheme.IdealSheafData.range_subschemeι] at hx
    obtain ⟨v, -⟩ := hx
    exact ⟨v⟩

/-! ### The fibre over `P` -/

private theorem isClosed_preimage_singleton (hf : IsGermResolution sX P f) :
    IsClosed (f.base ⁻¹' {P}) :=
  hf.isSurfaceGerm.2.2.1.preimage f.continuous

/-- The fibre over `P` is not all of `Y`: the generic point of `Y` maps to the generic point of
the surface `X`, which is not the closed point `P`. -/
private theorem preimage_singleton_ne_univ (hf : IsGermResolution sX P f) :
    f.base ⁻¹' {P} ≠ Set.univ := by
  intro h
  haveI : IsIntegral X := hf.isSurfaceGerm.1.1.toIsIntegral
  haveI : IsIntegral Y := hf.isIntegral sX
  haveI := hf.isSmoothResolution.isBirationalMorphism.isDominant
  have hη : f (genericPoint Y) = genericPoint X := map_genericPoint_of_isDominant f
  have hP : genericPoint X = P := by
    rw [← hη]
    exact (h ▸ Set.mem_univ (genericPoint Y) : genericPoint Y ∈ f.base ⁻¹' {P})
  have huniv : (Set.univ : Set X) = {P} := by
    rw [← hf.isSurfaceGerm.2.2.1.closure_eq, ← hP, (genericPoint_spec X).def]
  haveI : Subsingleton X := ⟨fun a b => by
    have ha : a ∈ ({P} : Set X) := huniv ▸ Set.mem_univ a
    have hb : b ∈ ({P} : Set X) := huniv ▸ Set.mem_univ b
    exact ha.trans hb.symm⟩
  have h2 := topologicalKrullDim_zero_of_discreteTopology X
  rw [hf.isSurfaceGerm.2.1] at h2
  exact absurd h2 (by decide)

/-- **The fibres of a resolution of a surface germ have dimension at most one**: over a point
other than `P` the resolution is an isomorphism, and the fibre over `P` is a proper closed subset
of the irreducible surface `Y`. -/
private theorem topologicalKrullDim_preimage_le_one (hf : IsGermResolution sX P f) (x : X) :
    topologicalKrullDim (f ⁻¹' {x}) ≤ 1 := by
  by_cases hx : x = P
  · subst hx
    haveI : IsIntegral Y := hf.isIntegral sX
    haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
    haveI : IsNoetherian Y := {}
    exact MMP.Mori.topologicalKrullDim_le_one_of_ne_univ hf.topologicalKrullDim_eq.le
      (isClosed_preimage_singleton hf) (preimage_singleton_ne_univ hf)
  · obtain ⟨U, hU, hiso⟩ := hf.isIso_away
    have hxU : x ∈ (U : Set X) := by rwa [hU]
    haveI : Subsingleton (f.base ⁻¹' {x}) := ⟨fun a b => Subtype.ext
      (Stacks.Models.eq_of_isIso_morphismRestrict f U (by rwa [show f a.1 = x from a.2])
        ((show f a.1 = x from a.2).trans (show f b.1 = x from b.2).symm))⟩
    haveI : DiscreteTopology (f.base ⁻¹' {x}) := Subsingleton.discreteTopology
    exact (topologicalKrullDim_zero_of_discreteTopology (f.base ⁻¹' {x})).trans zero_le_one

/-- **Every point of the fibre over `P` lies on an exceptional curve, unless the fibre is that
single point.** A non-closed point of the fibre specializing to `y` has a closure of dimension
one, so it has coheight one and is the generic point of an exceptional curve. Otherwise `y` is
closed and forms an irreducible component of the fibre by itself, hence an open and closed
point of it; the fibre is connected because `X` is normal, so it is `{y}`. -/
private theorem exists_isGermExceptionalCurve_mem_or (hf : IsGermResolution sX P f) {y : Y}
    (hy : f y = P) :
    (∃ C, IsGermExceptionalCurve f P C ∧ y ∈ C.support) ∨ f.base ⁻¹' {P} = {y} := by
  classical
  haveI : IsIntegral Y := hf.isIntegral sX
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : IsNoetherian Y := {}
  have hY := hf.isVariety
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.toLocallyOfFiniteType
  have hYd := hf.topologicalKrullDim_eq
  have hFc : IsClosed (f.base ⁻¹' {P}) := isClosed_preimage_singleton hf
  have hFne : f.base ⁻¹' {P} ≠ Set.univ := preimage_singleton_ne_univ hf
  have hyF : y ∈ f.base ⁻¹' {P} := hy
  by_cases hcase : ∃ e ∈ f.base ⁻¹' {P}, ¬ IsClosed ({e} : Set Y) ∧ e ⤳ y
  · left
    obtain ⟨e, heF, hecl, hey⟩ := hcase
    obtain ⟨c, -, hec, hne⟩ := MMP.Mori.exists_isClosed_singleton_specializes hecl
    have hW : closure ({e} : Set Y) ⊆ f.base ⁻¹' {P} :=
      closure_minimal (Set.singleton_subset_iff.2 heF) hFc
    have hWne : closure ({e} : Set Y) ≠ Set.univ := fun h =>
      hFne (Set.eq_univ_of_univ_subset (h ▸ hW))
    have hdim1 : topologicalKrullDim (closure ({e} : Set Y)) = 1 :=
      MMP.Mori.topologicalKrullDim_eq_one_of_ne_univ hYd.le isClosed_closure hWne
        (subset_closure rfl) (specializes_iff_mem_closure.1 hec) hec hne
    have hadd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (f ≫ sX) e
    rw [hdim1, hYd] at hadd
    have hcoh : Order.coheight e = 1 := by
      have h' : 1 + Order.coheight e = 2 :=
        WithBot.coe_injective (by rw [WithBot.coe_add]; exact hadd)
      generalize Order.coheight e = d at h' ⊢
      induction d using ENat.recTopCoe with
      | top => simp at h'
      | coe d => norm_cast at h' ⊢; omega
    have hDsupp : ((AlgebraicGeometry.PrimeDivisor.ofCoheightOne e hcoh).support : Set Y) =
        closure {e} := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne e hcoh,
      ⟨maximal_support_of_subset hFc hFne _ (hDsupp ▸ hW),
        isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hY hYd _⟩, ?_⟩
    show y ∈ ((AlgebraicGeometry.PrimeDivisor.ofCoheightOne e hcoh).support : Set Y)
    rw [hDsupp]
    exact specializes_iff_mem_closure.1 hey
  · right
    have hycl : IsClosed ({y} : Set Y) := by
      by_contra h
      exact hcase ⟨y, hyF, h, specializes_rfl⟩
    have hgen : ∀ e ∈ f.base ⁻¹' {P}, e ⤳ y → e = y := by
      intro e he hey
      by_cases hecl : IsClosed ({e} : Set Y)
      · have h := specializes_iff_mem_closure.1 hey
        rw [hecl.closure_eq] at h
        exact h.symm
      · exact absurd ⟨e, he, hecl, hey⟩ hcase
    obtain ⟨Z, hZf, hZc, hZirr, hZ⟩ :=
      TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hFc
    set G := ⋃₀ {W ∈ Z | y ∉ W} with hG
    have hGc : IsClosed G :=
      (hZf.subset fun W hW => hW.1).isClosed_sUnion fun W hW => hZc W hW.1
    have hyG : y ∉ G := by
      rintro ⟨W, ⟨-, hyW⟩, hyW'⟩
      exact hyW hyW'
    have hFG : f.base ⁻¹' {P} ⊆ {y} ∪ G := by
      intro x hx
      rw [hZ] at hx
      obtain ⟨W, hW, hxW⟩ := hx
      by_cases hyW : y ∈ W
      · left
        obtain ⟨g, hg⟩ := QuasiSober.sober (hZirr W hW) (hZc W hW)
        have hgF : g ∈ f.base ⁻¹' {P} := by rw [hZ]; exact ⟨W, hW, hg.mem⟩
        have hgy : g = y := hgen g hgF (hg.specializes hyW)
        have hx' : x ∈ closure ({g} : Set Y) := by rwa [hg.def]
        rw [hgy, hycl.closure_eq] at hx'
        exact hx'
      · right
        exact ⟨W, ⟨hW, hyW⟩, hxW⟩
    haveI : IsProper f := hf.isSmoothResolution.isProper
    have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
      (f ≫ sX) sX hY hf.isSurfaceGerm.1 f hf.isSmoothResolution.isBirationalMorphism).2 P
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hconn.isPreconnected {y} G hycl hGc
      hFG (by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨-, hx, hxG⟩
        rw [Set.mem_singleton_iff.1 hx] at hxG
        exact hyG hxG) with h | h
    · exact Set.Subset.antisymm h (Set.singleton_subset_iff.2 hyF)
    · exact absurd (h hyF) hyG

/-- **`(R¹f_*𝒪_Y)_P = 0` kills `H¹(𝒪_T)` for every closed subscheme `T` over `P`.** By the
theorem on formal functions every thickening `X_m` of the fibre has `H¹(𝒪_{X_m}) = 0`; the
quasi-compact `T` lies in some `X_m`, a Noetherian scheme of dimension at most one, and `H¹`
descends along the closed immersion. -/
private theorem subsingleton_rightDerived_one_unit_of_subsingleton_stalk
    (hf : IsGermResolution sX P f)
    (h : Subsingleton ((((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit Y.ringCatSheaf)).presheaf.stalk P))
    {T : Scheme.{u}} [CompactSpace T] (t : T ⟶ Y) [IsClosedImmersion t] (ht : ∀ z, f (t z) = P) :
    Subsingleton (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived 1).obj
      (SheafOfModules.unit T.ringCatSheaf)) := by
  haveI : IsProper f := hf.isSmoothResolution.isProper
  haveI : LocallyOfFiniteType sX := hf.isSurfaceGerm.1.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hP : IsClosed ({P} : Set X) := hf.isSurfaceGerm.2.2.1
  have hfib := topologicalKrullDim_preimage_le_one hf
  obtain ⟨m, t', ht', -⟩ := exists_isClosedImmersion_comp_infinitesimalι_eq f hP t ht
  haveI := ht'
  haveI := isClosedImmersion_infinitesimalι f hP m
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : CompactSpace (infinitesimalNeighbourhood f P m) :=
    (infinitesimalι f P m).isClosedEmbedding.compactSpace
  haveI : IsLocallyNoetherian (infinitesimalNeighbourhood f P m) :=
    LocallyOfFiniteType.isLocallyNoetherian (infinitesimalι f P m)
  haveI : IsNoetherian (infinitesimalNeighbourhood f P m) := {}
  have hdim : topologicalKrullDim (infinitesimalNeighbourhood f P m) ≤ 1 :=
    (Stacks.AlgebraicGeometry.FibreDimension.topologicalKrullDim_le_of_isInducing_of_range_subset
      (infinitesimalι f P m).isClosedEmbedding.isInducing
      (range_infinitesimalι_subset f P m)).trans (hfib P)
  have h1 := @Equiv.subsingleton _ _
    ((((Stacks.Cohomology.AffineBase.moduleGlobalSections _).rightDerived 1).mapIso
      (pullbackObjUnitIso (infinitesimalι f P m))).toLinearEquiv.toEquiv.symm)
    (subsingleton_infinitesimalCohomology_of_subsingleton_stalk f P hfib h m)
  exact subsingleton_rightDerived_one_unit t' hdim h1

/-- **Two minimal resolutions of a surface germ are isomorphic over `X`**: each dominates the
other, and the composites are the identities by uniqueness of the factorizations. -/
private theorem exists_isIso_comp_eq_of_isMinimalGermResolution {Y' : Scheme.{u}} {f' : Y' ⟶ X}
    [QuasiCompact (f' ≫ sX)] [IsLocallyNoetherian Y'] [IsNormal Y']
    (hf : IsMinimalGermResolution sX P f) (hf' : IsMinimalGermResolution sX P f') :
    ∃ b : Y ⟶ Y', IsIso b ∧ b ≫ f' = f := by
  have hX := hf.1.isSurfaceGerm
  have H := (MMP.Mori.IsMinimalSurfaceResolution.existsUnique_comp_eq sX f hX.1 hX.2.1
    hf.isMinimalSurfaceResolution).1
  have H' := (MMP.Mori.IsMinimalSurfaceResolution.existsUnique_comp_eq sX f' hX.1 hX.2.1
    hf'.isMinimalSurfaceResolution).1
  obtain ⟨a, ha, -⟩ := H Y' f' hf'.1.isSmoothResolution
  obtain ⟨b, hb, -⟩ := H' Y f hf.1.isSmoothResolution
  have hba : b ≫ a = 𝟙 Y := (H Y f hf.1.isSmoothResolution).unique
    (by rw [Category.assoc, ha, hb]) (Category.id_comp f)
  have hab : a ≫ b = 𝟙 Y' := (H' Y' f' hf'.1.isSmoothResolution).unique
    (by rw [Category.assoc, hb, ha]) (Category.id_comp f')
  exact ⟨b, ⟨⟨a, hba, hab⟩⟩, hb⟩

end Fibre

/-! ### Exceptional cycles at a rational singularity -/

section Rational

open Stacks.FormalFunctions

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {P : X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **At a rational singularity no exceptional cycle of the minimal resolution has an `H¹`.**
The vanishing of `(R¹f'_*𝒪)_P` for some minimal resolution `f'` transports to `f`, minimal
resolutions being isomorphic over `X`, and kills `H¹` of every closed subscheme over `P`. -/
private theorem subsingleton_cohomologyOverField_one_cyc (hrat : IsRationalSurfaceSingularity sX P)
    (hf : IsMinimalGermResolution sX P f) {Z : Divisor Y} (hZ : 0 ≤ Z) (hZ0 : Z ≠ 0)
    (hZE : ∀ C ∈ Z.support, IsGermExceptionalCurve f P C) :
    Subsingleton (cohomologyOverField k ((cyc Z).subschemeι ≫ f ≫ sX)
      (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf) 1) := by
  obtain ⟨Y', f', _, _, _, hf', hs⟩ := hrat
  obtain ⟨b, hb, hbf⟩ := exists_isIso_comp_eq_of_isMinimalGermResolution hf hf'
  obtain ⟨hsub, -, -⟩ := cyc_support_subset_and hf.1 hZ hZ0 hZE
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : CompactSpace (cyc Z).subscheme := (cyc Z).subschemeι.isClosedEmbedding.compactSpace
  exact subsingleton_rightDerived_one_unit_of_subsingleton_stalk hf'.1 hs
    ((cyc Z).subschemeι ≫ b) fun z => by
      rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply b f', hbf]
      exact hsub (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩)

/-- **At a rational singularity every nonzero exceptional cycle `Z` of the minimal resolution
has `χ(𝒪_Z) > 0`**: `χ(𝒪_Z) = h⁰(𝒪_Z) - h¹(𝒪_Z) = h⁰(𝒪_Z) ≥ 1`. -/
private theorem zero_lt_eulerCharacteristic_cyc (hrat : IsRationalSurfaceSingularity sX P)
    (hf : IsMinimalGermResolution sX P f) {Z : Divisor Y} (hZ : 0 ≤ Z) (hZ0 : Z ≠ 0)
    (hZE : ∀ C ∈ Z.support, IsGermExceptionalCurve f P C)
    (hp : IsProper ((cyc Z).subschemeι ≫ f ≫ sX)) :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((cyc Z).subschemeι ≫ f ≫ sX)
    0 < eulerCharacteristic k ((cyc Z).subschemeι ≫ f ≫ sX)
      (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf) := by
  obtain ⟨-, hdim, hne⟩ := cyc_support_subset_and hf.1 hZ hZ0 hZE
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    ((cyc Z).subschemeι ≫ f ≫ sX)
  haveI := subsingleton_cohomologyOverField_one_cyc hrat hf hZ hZ0 hZE
  have h0 : Module.finrank k (cohomologyOverField k ((cyc Z).subschemeι ≫ f ≫ sX)
      (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf) 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  have h1 := one_le_finrank_cohomologyOverField_zero_unit (k := k)
    ((cyc Z).subschemeι ≫ f ≫ sX)
  have h2 := eulerCharacteristic_eq_finrank_sub ((cyc Z).subschemeι ≫ f ≫ sX) hdim
    (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf)
  rw [h0] at h2
  show 0 < eulerCharacteristic k ((cyc Z).subschemeι ≫ f ≫ sX)
    (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf)
  omega

/-- **The exceptional curves of a resolution are finitely many**: their supports are
irreducible components of the closed fibre `f⁻¹(P)` of the Noetherian `Y`, and a prime divisor
is determined by its support. -/
private theorem exists_finset_isGermExceptionalCurve (hf : IsGermResolution sX P f) :
    ∃ S : Finset (MMP.Mori.PrimeDivisor Y), ∀ C, C ∈ S ↔ IsGermExceptionalCurve f P C := by
  classical
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : IsNoetherian Y := {}
  obtain ⟨Z, hZf, hZc, hZirr, hZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_preimage_singleton hf)
  have key : ∀ C, IsGermExceptionalCurve f P C → C.support ∈ Z := by
    intro C hC
    have hsub : C.support ⊆ ⋃₀ (hZf.toFinset : Set (Set Y)) := by
      rw [hZf.coe_toFinset, ← hZ]; exact hC.1.prop.2
    obtain ⟨W, hW, hCW⟩ := (isIrreducible_iff_sUnion_isClosed.1 hC.1.prop.1) hZf.toFinset
      (fun W hW => hZc W (hZf.mem_toFinset.1 hW)) hsub
    have hW' := hZf.mem_toFinset.1 hW
    have hWF : W ⊆ f.base ⁻¹' {P} := by rw [hZ]; exact Set.subset_sUnion_of_mem hW'
    rw [hC.1.eq_of_le ⟨hZirr W hW', hWF⟩ hCW]
    exact hW'
  have hfin : {C | IsGermExceptionalCurve f P C}.Finite :=
    Set.Finite.of_finite_image (hZf.subset (by rintro _ ⟨C, hC, rfl⟩; exact key C hC))
      (fun C _ C' _ h => AlgebraicGeometry.PrimeDivisor.eq_of_support_eq h)
  exact ⟨hfin.toFinset, fun C => hfin.mem_toFinset⟩

end Rational

/-! ### Triviality on the thickenings of the fibre -/

section Thickenings

open Stacks.FormalFunctions

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {P : X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]

/-- A module isomorphic to the structure sheaf has a nowhere vanishing global section. -/
private theorem exists_nonvanishingLocus_eq_univ_of_iso {Z : Scheme.{u}} {M : Z.Modules}
    (e : M ≅ SheafOfModules.unit Z.ringCatSheaf) :
    ∃ t : Γ(M, ⊤), Stacks.Ample.nonvanishingLocus M t = Set.univ :=
  ⟨e.inv.app ⊤ (show Γ(SheafOfModules.unit Z.ringCatSheaf, ⊤) from (1 : Γ(Z, ⊤))),
    (Stacks.Ample.nonvanishingLocus_congr e.symm _).trans
      (Set.eq_univ_of_forall fun x => Stacks.Ample.Γgerm_notMem_maximalSmul_of_eq_one Z x _ rfl)⟩

/-- The degree of `𝒪_Y(D)` on an exceptional curve is the intersection number `(D · E)`. -/
private theorem degreeOn_divisorialSheaf_eq_zero {D : Divisor Y} (hD : D.IsCartier)
    (hDE : ∀ E : MMP.Mori.PrimeDivisor Y, IsGermExceptionalCurve f P E →
      IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor D) E.idealSheaf 0)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 D.divisorialSheaf]
    (C : MMP.Mori.PrimeDivisor Y) (hC : IsGermExceptionalCurve f P C)
    (_ : IsProper (C.idealSheaf.subschemeι ≫ f ≫ sX))
    (hdim : topologicalKrullDim C.idealSheaf.subscheme ≤ 1) :
    degreeOn k (f ≫ sX) C.idealSheaf.subschemeι hdim D.divisorialSheaf = 0 := by
  obtain ⟨hp, hdim', hq, h0⟩ := hDE C hC
  rw [QDivisor.intersectionNumber_toQDivisor k (f ≫ sX) _ hdim' D hD hq] at h0
  exact_mod_cast h0

/-- **In the presence of an exceptional curve, a line bundle of degree zero on every exceptional
curve is trivial on every thickening `X_n` of the fibre.** The thickening lies in a cycle
`N · ∑ Eᵢ`, the exceptional curves covering the fibre, and the line bundle is trivial on every
exceptional cycle once all of them have positive Euler characteristic. -/
private theorem exists_nonvanishingLocus_infinitesimalModule_eq_univ
    (hrat : IsRationalSurfaceSingularity sX P) (hf : IsMinimalGermResolution sX P f)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hL : ∀ C, IsGermExceptionalCurve f P C → ∀ (_ : IsProper (C.idealSheaf.subschemeι ≫ f ≫ sX))
      (hdim : topologicalKrullDim C.idealSheaf.subscheme ≤ 1),
        degreeOn k (f ≫ sX) C.idealSheaf.subschemeι hdim L = 0)
    (hC₀ : ∃ C, IsGermExceptionalCurve f P C) (n : ℕ) :
    ∃ t : Γ(infinitesimalModule f L P n, ⊤),
      Stacks.Ample.nonvanishingLocus (infinitesimalModule f L P n) t = Set.univ := by
  classical
  haveI : IsProper f := hf.1.isSmoothResolution.isProper
  haveI : LocallyOfFiniteType sX := hf.1.isSurfaceGerm.1.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hP : IsClosed ({P} : Set X) := hf.1.isSurfaceGerm.2.2.1
  haveI := isClosedImmersion_infinitesimalι f hP n
  obtain ⟨S, hS⟩ := exists_finset_isGermExceptionalCurve hf.1
  obtain ⟨C₀, hC₀⟩ := hC₀
  have hcov : ∀ y ∈ f.base ⁻¹' {P}, ∃ C ∈ S.val, y ∈ C.idealSheaf.support := by
    intro y hy
    rcases exists_isGermExceptionalCurve_mem_or hf.1 hy with ⟨C, hC, hyC⟩ | hF
    · exact ⟨C, (hS C).2 hC, hyC⟩
    · exact absurd ((Set.subsingleton_singleton).anti (hF ▸ hC₀.1.prop.2))
        hC₀.2.not_subsingleton
  have hJK : cycleIdeal S.val ≤ (infinitesimalι f P n).ker.radical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro y hy
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker,
      (infinitesimalι f P n).isClosedEmbedding.isClosed_range.closure_eq] at hy
    exact (mem_support_cycleIdeal _ y).2 (hcov y (range_infinitesimalι_subset f P n hy))
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  obtain ⟨N, hN⟩ := Scheme.IdealSheafData.exists_pow_le_of_le_radical hJK
  set m' := N • S.val with hm'
  have hle : (cycleIdeal m').subschemeι.ker ≤ (infinitesimalι f P n).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hm', cycleIdeal_nsmul]; exact hN
  set t' := IsClosedImmersion.lift (cycleIdeal m').subschemeι (infinitesimalι f P n) hle
  have ht' : t' ≫ (cycleIdeal m').subschemeι = infinitesimalι f P n :=
    IsClosedImmersion.lift_fac _ _ hle
  have hm'E : ∀ C ∈ m', IsGermExceptionalCurve f P C := fun C hC =>
    (hS C).1 (Multiset.mem_of_mem_nsmul hC)
  have hZ : 0 ≤ cycleDivisor m' := cycleDivisor_nonneg m'
  have hZE : ∀ C ∈ (cycleDivisor m').support, IsGermExceptionalCurve f P C := fun C hC =>
    hm'E C (mem_of_mem_support_cycleDivisor hC)
  obtain ⟨e⟩ := hf.1.nonempty_pullback_divisorIdeal_iso_unit hZ hZE
    (fun Z' hZ' hZ'Z hZ'0 hp => zero_lt_eulerCharacteristic_cyc hrat hf hZ' hZ'0
      (fun C hC => hZE C (by
        rw [Finsupp.mem_support_iff] at hC ⊢
        exact fun h0 => hC (le_antisymm (h0 ▸ hZ'Z C) (hZ' C)))) hp)
    L (fun C hC => hL C (hZE C hC))
  have hcyc : MMP.Resolution.divisorIdeal (fun C => (cycleDivisor m' C).toNat) =
      cycleIdeal m' := divisorIdeal_cycleDivisor m'
  rw [hcyc] at e
  exact exists_nonvanishingLocus_eq_univ_of_iso
    (((Scheme.Modules.pullbackComp t' (cycleIdeal m').subschemeι).app L ≪≫
      (Scheme.Modules.pullbackCongr ht').app L).symm ≪≫
      (Scheme.Modules.pullback t').mapIso e ≪≫ pullbackObjUnitIso t')

end Thickenings

/-! ### Restriction of sections along a factorization -/

section Restriction

open Stacks.FormalFunctions

variable {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) {c : A ⟶ C} (hw : a ≫ b = c)
  (M : C.Modules)

/-- The restriction of a global section of `b^* M` along `a`, read as a global section of
`c^* M` for `a ≫ b = c`. -/
private def restrictTop (x : Γ((Scheme.Modules.pullback b).obj M, ⊤)) :
    Γ((Scheme.Modules.pullback c).obj M, ⊤) :=
  ((Scheme.Modules.pullbackComp a b).hom.app M ≫
      (Scheme.Modules.pullbackCongr hw).hom.app M).app ⊤
    ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) |>.presheaf.map
      (homOfLE (top_le_preimage_top a)).op
      (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
        ((Scheme.Modules.pullback b).obj M)).app ⊤ x))

/-- The defining formula of `restrictTop`. Stated once for arbitrary schemes, it is instantiated
rather than unfolded at the thickenings. -/
private theorem restrictTop_def (x : Γ((Scheme.Modules.pullback b).obj M, ⊤)) :
    restrictTop a b hw M x =
      ((Scheme.Modules.pullbackComp a b).hom.app M ≫
          (Scheme.Modules.pullbackCongr hw).hom.app M).app ⊤
        ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) |>.presheaf.map
          (homOfLE (top_le_preimage_top a)).op
          (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
            ((Scheme.Modules.pullback b).obj M)).app ⊤ x)) := rfl

/-- The restriction of a module along the canonical morphism `⊤ ⟶ g ⁻¹ᵁ ⊤` is the identity. -/
private theorem presheaf_map_top_eq_id {X' Y' : Scheme.{u}} (g : X' ⟶ Y')
    (e : (⊤ : X'.Opens) ⟶ g ⁻¹ᵁ ⊤) (N : X'.Modules) : N.presheaf.map e.op = 𝟙 _ :=
  have h : e.op = 𝟙 (Opposite.op (g ⁻¹ᵁ ⊤)) := Subsingleton.elim _ _
  Eq.trans (congrArg N.presheaf.map h) (N.presheaf.map_id _)

/-- The restriction of a section along the canonical morphism `⊤ ⟶ g ⁻¹ᵁ ⊤` is the section. -/
private theorem presheaf_map_top_apply {X' Y' : Scheme.{u}} (g : X' ⟶ Y')
    (e : (⊤ : X'.Opens) ⟶ g ⁻¹ᵁ ⊤) (N : X'.Modules) (y : Γ(N, g ⁻¹ᵁ ⊤)) :
    N.presheaf.map e.op y = y :=
  (ConcreteCategory.congr_hom (presheaf_map_top_eq_id g e N) y).trans (CategoryTheory.id_apply y)

/-- A morphism of modules into a pushforward, evaluated on global sections and followed by the
restriction to `⊤`, is semilinear over `g.appTop`. -/
private theorem appTop_map_smul {X' Y' : Scheme.{u}} (g : X' ⟶ Y') {M' : Y'.Modules}
    {N : X'.Modules} (φ : M' ⟶ (Scheme.Modules.pushforward g).obj N)
    (e : (⊤ : X'.Opens) ⟶ g ⁻¹ᵁ ⊤) (r : Γ(Y', ⊤)) (m : Γ(M', ⊤)) :
    N.presheaf.map e.op (φ.app ⊤ (r • m)) =
      g.appTop r • N.presheaf.map e.op (φ.app ⊤ m) := by
  simp only [presheaf_map_top_eq_id g e N, Scheme.Modules.Hom.app_smul]
  rfl

/-- The comparison of direct images along a factorization, on global sections. -/
private theorem pushforwardSectionComparison_app_top
    (z : Γ((Scheme.Modules.pullback b).obj M, ⊤)) :
    (Stacks.Algebraization.pushforwardSectionComparison a b hw M).app ⊤ z =
      ((Scheme.Modules.pullbackComp a b).hom.app M ≫
        (Scheme.Modules.pullbackCongr hw).hom.app M).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
          ((Scheme.Modules.pullback b).obj M)).app ⊤ z) := by
  simp only [Stacks.Algebraization.pushforwardSectionComparison, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  have h : ∀ {U : A.Opens} (i : U ⟶ U) (x : Γ((Scheme.Modules.pullback c).obj M, U)),
      ((Scheme.Modules.pullback c).obj M).presheaf.map i.op x = x := by
    intro U i x
    rw [Subsingleton.elim i (𝟙 U), op_id, CategoryTheory.Functor.map_id]
    rfl
  exact h _ _

/-- `restrictTop` is the comparison of the direct images to `C`. -/
private theorem restrictTop_eq_pushforwardSectionComparison
    (x : Γ((Scheme.Modules.pullback b).obj M, ⊤)) :
    restrictTop a b hw M x =
      (Stacks.Algebraization.pushforwardSectionComparison a b hw M).app ⊤ x := by
  rw [pushforwardSectionComparison_app_top]
  exact congrArg (fun z => (((Scheme.Modules.pullbackComp a b).hom.app M ≫
      (Scheme.Modules.pullbackCongr hw).hom.app M).app ⊤) z)
    (presheaf_map_top_apply a (homOfLE (top_le_preimage_top a)) _ _)

private theorem restrictTop_add (x y : Γ((Scheme.Modules.pullback b).obj M, ⊤)) :
    restrictTop a b hw M (x + y) = restrictTop a b hw M x + restrictTop a b hw M y := by
  rw [restrictTop_eq_pushforwardSectionComparison, restrictTop_eq_pushforwardSectionComparison,
    restrictTop_eq_pushforwardSectionComparison]
  exact map_add _ x y

private theorem restrictTop_smul (r : Γ(B, ⊤)) (x : Γ((Scheme.Modules.pullback b).obj M, ⊤)) :
    restrictTop a b hw M (r • x) = a.appTop r • restrictTop a b hw M x := by
  rw [restrictTop, restrictTop, appTop_map_smul, Scheme.Modules.Hom.app_smul]

/-- The nonvanishing locus of a restricted section is the preimage of the nonvanishing locus. -/
private theorem nonvanishingLocus_restrictTop (x : Γ((Scheme.Modules.pullback b).obj M, ⊤)) :
    Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback c).obj M) (restrictTop a b hw M x) =
      a.base ⁻¹' Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback b).obj M) x := by
  rw [restrictTop_eq_pushforwardSectionComparison]
  subst hw
  refine Eq.trans (congrArg (Stacks.Ample.nonvanishingLocus
    ((Scheme.Modules.pullback (a ≫ b)).obj M))
    (pushforwardSectionComparison_app_top a b rfl M x)) ?_
  refine (Stacks.Ample.nonvanishingLocus_congr
    ((Scheme.Modules.pullbackComp a b).app M ≪≫ (Scheme.Modules.pullbackCongr rfl).app M)
    _).trans ?_
  exact (Stacks.NonvanishingPullback.preimage_nonvanishingLocus a _ x).symm

end Restriction

section RestrictionComp

variable {Z Z' W X : Scheme.{u}} (t : Z ⟶ Z') (i : Z' ⟶ W) (ι : W ⟶ X) {c : Z' ⟶ X}
  {c' : Z ⟶ X} {k : Z ⟶ W} (hn : i ≫ ι = c) (hm : t ≫ c = c') (hkc : k ≫ ι = c')
  (M : X.Modules)

/-- **Restriction of sections along factorizations through a closed immersion is transitive**:
restricting along `i` and then along `t` is restricting along `k`, as the comparisons of direct
images compose, the unit of the closed immersion `ι` being an epimorphism. -/
private theorem restrictTop_restrictTop [IsClosedImmersion ι]
    (x : Γ((Scheme.Modules.pullback ι).obj M, ⊤)) :
    restrictTop t c hm M (restrictTop i ι hn M x) = restrictTop k ι hkc M x := by
  have hcomp : Stacks.Algebraization.pushforwardSectionComparison i ι hn M ≫
      Stacks.Algebraization.pushforwardSectionComparison t c hm M =
      Stacks.Algebraization.pushforwardSectionComparison k ι hkc M := by
    haveI := Stacks.ClosedImmersion.epi_unit_app ι M
    rw [← cancel_epi ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M),
      ← Category.assoc, Stacks.Algebraization.unit_comp_pushforwardSectionComparison,
      Stacks.Algebraization.unit_comp_pushforwardSectionComparison,
      Stacks.Algebraization.unit_comp_pushforwardSectionComparison]
  rw [restrictTop_eq_pushforwardSectionComparison, restrictTop_eq_pushforwardSectionComparison,
    restrictTop_eq_pushforwardSectionComparison, ← hcomp, Scheme.Modules.Hom.comp_app]
  exact (ConcreteCategory.comp_apply _ _ x).symm

end RestrictionComp

/-! ### The tower of sections on the thickenings -/

section Tower

open Stacks.FormalFunctions

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : Y.Modules) (P : X)

/-- `Γ(X_n, ℱ_n)` is a module over `𝒪_{X,P}` through `𝒪_{X,P} ⟶ Γ(X_n, 𝒪)`. -/
private abbrev sectionsModule (n : ℕ) :
    Module (X.presheaf.stalk P) Γ(infinitesimalModule f F P n, ⊤) :=
  Module.compHom _ (infinitesimalBaseRingHom f P n)

attribute [local instance] sectionsModule

/-- The restriction `Γ(X_n, ℱ_n) ⟶ Γ(X_m, ℱ_m)` along the transition `X_m ⟶ X_n`, `m ≤ n`, an
`𝒪_{X,P}`-linear map. -/
private def transition {m n : ℕ} (h : m ≤ n) :
    Γ(infinitesimalModule f F P n, ⊤) →ₗ[X.presheaf.stalk P]
      Γ(infinitesimalModule f F P m, ⊤) where
  toFun := restrictTop (infinitesimalTransition f P h) (infinitesimalι f P n)
    (infinitesimalTransition_ι f P h) F
  map_add' := restrictTop_add _ _ _ F
  map_smul' r x :=
    (restrictTop_smul (infinitesimalTransition f P h) (infinitesimalι f P n)
      (infinitesimalTransition_ι f P h) F (infinitesimalBaseRingHom f P n r) x).trans
      (congrArg (· • _) (infinitesimalBaseRingHom_transition f P h r))

private theorem transition_apply {m n : ℕ} (h : m ≤ n) (x : Γ(infinitesimalModule f F P n, ⊤)) :
    transition f F P h x = restrictTop (infinitesimalTransition f P h) (infinitesimalι f P n)
      (infinitesimalTransition_ι f P h) F x := rfl

/-- The restriction formula, from the spelling with `infinitesimalModule` to the spelling with
the pullback it abbreviates. -/
private theorem restriction_formula_eq_pullback {m n : ℕ} (h : m ≤ n)
    (x : Γ(infinitesimalModule f F P n, ⊤)) :
    ((Scheme.Modules.pullbackComp (infinitesimalTransition f P h)
          (infinitesimalι f P n)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (infinitesimalTransition_ι f P h)).hom.app F).app ⊤
      ((Scheme.Modules.pullback (infinitesimalTransition f P h)).obj
          (infinitesimalModule f F P n) |>.presheaf.map
        (homOfLE (top_le_preimage_top (infinitesimalTransition f P h))).op
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (infinitesimalTransition f P h)).unit.app (infinitesimalModule f F P n)).app ⊤
            x)) =
    ((Scheme.Modules.pullbackComp (infinitesimalTransition f P h)
          (infinitesimalι f P n)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (infinitesimalTransition_ι f P h)).hom.app F).app ⊤
      ((Scheme.Modules.pullback (infinitesimalTransition f P h)).obj
          ((Scheme.Modules.pullback (infinitesimalι f P n)).obj F) |>.presheaf.map
        (homOfLE (top_le_preimage_top (infinitesimalTransition f P h))).op
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (infinitesimalTransition f P h)).unit.app
            ((Scheme.Modules.pullback (infinitesimalι f P n)).obj F)).app ⊤
            x)) := by
  have e1 : ((Scheme.Modules.pullbackPushforwardAdjunction (infinitesimalTransition f P h)).unit.app
        (infinitesimalModule f F P n)).app ⊤ x =
      ((Scheme.Modules.pullbackPushforwardAdjunction (infinitesimalTransition f P h)).unit.app
        ((Scheme.Modules.pullback (infinitesimalι f P n)).obj F)).app ⊤ x := rfl
  have e2 : ∀ z, ((Scheme.Modules.pullback (infinitesimalTransition f P h)).obj
          (infinitesimalModule f F P n)).presheaf.map
        (homOfLE (top_le_preimage_top (infinitesimalTransition f P h))).op z =
      ((Scheme.Modules.pullback (infinitesimalTransition f P h)).obj
          ((Scheme.Modules.pullback (infinitesimalι f P n)).obj F)).presheaf.map
        (homOfLE (top_le_preimage_top (infinitesimalTransition f P h))).op z := fun z => rfl
  exact (congrArg (fun w => ((Scheme.Modules.pullbackComp (infinitesimalTransition f P h)
          (infinitesimalι f P n)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (infinitesimalTransition_ι f P h)).hom.app F).app ⊤
      (((Scheme.Modules.pullback (infinitesimalTransition f P h)).obj
          (infinitesimalModule f F P n)).presheaf.map
        (homOfLE (top_le_preimage_top (infinitesimalTransition f P h))).op w)) e1).trans
    (congrArg (fun w => ((Scheme.Modules.pullbackComp (infinitesimalTransition f P h)
          (infinitesimalι f P n)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (infinitesimalTransition_ι f P h)).hom.app F).app ⊤ w)
      (e2 _))

/-- The transition maps in the form the theorem on formal functions takes them. -/
private theorem transition_eq {m n : ℕ} (h : m ≤ n) (x : Γ(infinitesimalModule f F P n, ⊤)) :
    transition f F P h x =
      ((Scheme.Modules.pullbackComp (infinitesimalTransition f P h)
            (infinitesimalι f P n)).hom.app F ≫
          (Scheme.Modules.pullbackCongr (infinitesimalTransition_ι f P h)).hom.app F).app ⊤
        ((Scheme.Modules.pullback (infinitesimalTransition f P h)).obj
            (infinitesimalModule f F P n) |>.presheaf.map
          (homOfLE (top_le_preimage_top (infinitesimalTransition f P h))).op
          (((Scheme.Modules.pullbackPushforwardAdjunction
            (infinitesimalTransition f P h)).unit.app (infinitesimalModule f F P n)).app ⊤ x)) :=
  (transition_apply f F P h x).trans ((restrictTop_def _ _ _ _ x).trans
    (restriction_formula_eq_pullback f F P h x).symm)

private theorem sectionsModule_smul (n : ℕ) (r : X.presheaf.stalk P)
    (x : Γ(infinitesimalModule f F P n, ⊤)) : r • x = infinitesimalBaseRingHom f P n r • x :=
  rfl

/-- **The restriction maps of the tower compose.** -/
private theorem transition_transition {l m n : ℕ} [IsClosedImmersion (infinitesimalι f P n)]
    (h₁ : l ≤ m) (h₂ : m ≤ n) (x : Γ(infinitesimalModule f F P n, ⊤)) :
    transition f F P h₁ (transition f F P h₂ x) = transition f F P (h₁.trans h₂) x := by
  simp only [transition_apply]
  exact restrictTop_restrictTop (infinitesimalTransition f P h₁) (infinitesimalTransition f P h₂)
    (infinitesimalι f P n) (infinitesimalTransition_ι f P h₂) (infinitesimalTransition_ι f P h₁)
    (infinitesimalTransition_ι f P (h₁.trans h₂)) F x

/-- The restriction maps of the tower carry nowhere vanishing sections to nowhere vanishing
sections. -/
private theorem nonvanishingLocus_transition {m n : ℕ} (h : m ≤ n)
    (t : Γ(infinitesimalModule f F P n, ⊤))
    (ht : Stacks.Ample.nonvanishingLocus (infinitesimalModule f F P n) t = Set.univ) :
    Stacks.Ample.nonvanishingLocus (infinitesimalModule f F P m) (transition f F P h t) =
      Set.univ := by
  rw [transition_apply, nonvanishingLocus_restrictTop, ht, Set.preimage_univ]

end Tower

/-! ### The Mittag-Leffler argument -/

section MittagLeffler

open Stacks.IntertwinedFiltration

variable {A : Type*} [CommRing A] {H : ℕ → Type*} [∀ n, AddCommGroup (H n)] [∀ n, Module A (H n)]
  (ψ : ∀ m n, m ≤ n → H n →ₗ[A] H m)
  (hψ : ∀ l m n (h₁ : l ≤ m) (h₂ : m ≤ n) (x : H n), ψ l m h₁ (ψ m n h₂ x) = ψ l n (h₁.trans h₂) x)

include hψ in
/-- The images of the transition maps into a fixed term of the tower decrease. -/
private theorem range_le_range {n i j : ℕ} (hi : n ≤ i) (hij : i ≤ j) :
    LinearMap.range (ψ n j (hi.trans hij)) ≤ LinearMap.range (ψ n i hi) := by
  rintro _ ⟨w, rfl⟩
  exact ⟨ψ i j hij w, hψ n i j hi hij w⟩

include hψ in
/-- **The images of the transition maps into an Artinian term of the tower stabilize.** -/
private theorem exists_range_eq {n : ℕ} [IsArtinian A (H n)] :
    ∃ N, ∃ hN : n ≤ N, ∀ j (hj : N ≤ j),
      LinearMap.range (ψ n j (hN.trans hj)) = LinearMap.range (ψ n N hN) := by
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := A) (M := H n)
    ⟨fun j => OrderDual.toDual (LinearMap.range (ψ n (n + j) (Nat.le_add_right n j))),
      fun i j hij => range_le_range ψ hψ (Nat.le_add_right n i) (Nat.add_le_add_left hij n)⟩
  refine ⟨n + N, Nat.le_add_right n N, fun j hj => ?_⟩
  have h := hN (j - n) (by omega)
  have key : ∀ j' (_ : n + (j - n) = j') (h₁ : n ≤ j') (h₂ : n ≤ n + (j - n)),
      LinearMap.range (ψ n j' h₁) = LinearMap.range (ψ n (n + (j - n)) h₂) := by
    rintro _ rfl _ _; rfl
  rw [key j (by omega) _ (Nat.le_add_right n _)]
  exact (congrArg OrderDual.ofDual h).symm

/-- An element of a term of the tower lying in the image of every transition map into it. -/
private def IsStable (n : ℕ) (z : H n) : Prop :=
  ∀ j (h : n ≤ j), z ∈ LinearMap.range (ψ n j h)

include hψ in
/-- Stable elements are fixed by the transition from a term to itself. -/
private theorem IsStable.self {n : ℕ} {z : H n} (hz : IsStable ψ n z) : ψ n n le_rfl z = z := by
  obtain ⟨w, rfl⟩ := hz n le_rfl
  exact hψ n n n le_rfl le_rfl w

include hψ in
/-- **Stable elements lift to stable elements** when the next term of the tower is Artinian. -/
private theorem IsStable.exists_lift {n : ℕ} [IsArtinian A (H (n + 1))] {z : H n}
    (hz : IsStable ψ n z) :
    ∃ z' : H (n + 1), IsStable ψ (n + 1) z' ∧ ψ n (n + 1) (Nat.le_succ n) z' = z := by
  obtain ⟨N, hN, hst⟩ := exists_range_eq ψ hψ (n := n + 1)
  obtain ⟨w, hw⟩ := hz N (by omega)
  refine ⟨ψ (n + 1) N hN w, fun j hj => ?_, ?_⟩
  · rcases le_total j N with hjN | hNj
    · exact range_le_range ψ hψ hj hjN ⟨w, rfl⟩
    · rw [hst j hNj]; exact ⟨w, rfl⟩
  · rwa [hψ]

include hψ in
/-- **Mittag-Leffler for a tower of Artinian modules**: an element of the `k`-th term lying in the
image of every transition map into it is the `k`-th component of a compatible family. -/
private theorem exists_towerLimit_proj_eq {k : ℕ} (hart : ∀ n, k ≤ n → IsArtinian A (H n))
    {z : H k} (hz : IsStable ψ k z) :
    ∃ y : towerLimit H ψ, towerLimit.proj k y = z := by
  classical
  let lift : ∀ i, {w : H (k + i) // IsStable ψ (k + i) w} → {w : H (k + i + 1) //
      IsStable ψ (k + i + 1) w} := fun i w =>
    haveI := hart (k + i + 1) (by omega)
    ⟨(w.2.exists_lift ψ hψ).choose, (w.2.exists_lift ψ hψ).choose_spec.1⟩
  have hlift : ∀ i w, ψ (k + i) (k + i + 1) (Nat.le_succ _) (lift i w).1 = w.1 := fun i w =>
    haveI := hart (k + i + 1) (by omega)
    (w.2.exists_lift ψ hψ).choose_spec.2
  let T : ∀ i, {w : H (k + i) // IsStable ψ (k + i) w} := fun i =>
    Nat.rec (motive := fun i => {w : H (k + i) // IsStable ψ (k + i) w}) ⟨z, hz⟩
      (fun i w => lift i w) i
  have hT : ∀ i j (hij : i ≤ j), ψ (k + i) (k + j) (by omega) (T j).1 = (T i).1 := by
    intro i j hij
    induction j with
    | zero =>
      obtain rfl : i = 0 := by omega
      exact (T 0).2.self ψ hψ
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · exact (T (j + 1)).2.self ψ hψ
      · rw [← ih (by omega), ← hψ (k + i) (k + j) (k + (j + 1)) (by omega) (by omega)]
        exact congrArg _ (hlift j (T j))
  refine ⟨⟨fun n => ψ n (k + n) (Nat.le_add_left n k) (T n).1, fun m n hmn => ?_⟩, ?_⟩
  · show ψ m n hmn (ψ n (k + n) _ (T n).1) = ψ m (k + m) _ (T m).1
    rw [hψ, ← hT m n hmn, hψ]
  · show ψ k (k + k) _ (T k).1 = z
    exact hT 0 k (Nat.zero_le k)

end MittagLeffler

/-! ### The terms of the tower are Artinian -/

section Artinian

open Stacks.FormalFunctions

/-- **Global sections of a coherent module on a scheme proper over a Noetherian ring are a finite
module** ([Stacks, Tag 02O6] in degree zero). -/
private theorem moduleFinite_sections (R : Type u) [CommRing R] [IsNoetherianRing R]
    {W : Scheme.{u}} (g : W ⟶ Spec (.of R)) [IsProper g] (G : W.Modules)
    [SheafOfModules.IsCoherent G] :
    letI : Module R Γ(G, ⊤) :=
      Module.compHom _ (Stacks.Cohomology.FormalFunctions.baseRingHom R g)
    Module.Finite R Γ(G, ⊤) := by
  letI : Module R Γ(G, ⊤) :=
    Module.compHom _ (Stacks.Cohomology.FormalFunctions.baseRingHom R g)
  haveI := Stacks.Algebraization.moduleFinite_cohomologyOverBase R g G 0
  exact Module.Finite.equiv
    ((ModuleCat.restrictScalars (Stacks.Cohomology.FormalFunctions.baseRingHom R g)).mapIso
      ((Stacks.Cohomology.FormalFunctions.moduleGlobalSectionsRightDerivedZeroIso W).app
        G)).toLinearEquiv

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : Y.Modules) (P : X)

attribute [local instance] sectionsModule

/-- **The terms `Γ(X_n, ℱ_n)` of the tower are Artinian `𝒪_{X,P}`-modules** for `n ≥ 1`: they are
finite over the Artinian ring `𝒪_{X,P}/𝔪ⁿ`, `X_n` being proper over it. -/
private theorem isArtinian_sections [IsLocallyNoetherian X] [IsProper f] [F.IsCoherent] {n : ℕ}
    (hn : 1 ≤ n) : IsArtinian (X.presheaf.stalk P) Γ(infinitesimalModule f F P n, ⊤) := by
  haveI : IsArtinianRing (stalkQuotient P n) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _
      ⟨⟨(IsLocalRing.maximalIdeal.isMaximal _).isPrime, Ideal.pow_le_self (by omega)⟩,
        fun _ hp _ => hp.1.le_of_pow_le hp.2⟩
  letI : Module (stalkQuotient P n) Γ(infinitesimalModule f F P n, ⊤) :=
    Module.compHom _
      (Stacks.Cohomology.FormalFunctions.baseRingHom _ (infinitesimalStructure f P n))
  haveI : Module.Finite (stalkQuotient P n) Γ(infinitesimalModule f F P n, ⊤) :=
    moduleFinite_sections _ (infinitesimalStructure f P n) (infinitesimalModule f F P n)
  letI : Algebra (X.presheaf.stalk P) (stalkQuotient P n) := (toStalkQuotient P n).hom.toAlgebra
  have hST : IsScalarTower (X.presheaf.stalk P) (stalkQuotient P n)
      Γ(infinitesimalModule f F P n, ⊤) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact @isArtinian_of_surjective_algebraMap (stalkQuotient P n) Γ(infinitesimalModule f F P n, ⊤)
    _ _ _ (X.presheaf.stalk P) _ _ (sectionsModule f F P n) inferInstance hST
    fun z => Ideal.Quotient.mk_surjective (I := stalkMaximalIdeal P ^ n) z

end Artinian

/-! ### A formal generator lifts to a section near the fibre -/

section Formal

open Stacks.FormalFunctions Stacks.IntertwinedFiltration

attribute [local instance] sectionsModule

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : Y.Modules) (P : X)

/-- **A compatible system of trivializations of `ℱ` on the thickenings gives a section of `ℱ`
near the fibre generating it on the scheme-theoretic fibre.** If every `ℱ_n`, `n ≥ 1`, has a
nowhere vanishing section, the images of the transition maps into `Γ(X_1, ℱ_1)` stabilize (the
terms being Artinian) and contain a nowhere vanishing section, which by Mittag-Leffler is the
first component of a compatible family; by the theorem on formal functions this family is an
element of the completion of `(f_* ℱ)_P`, whose first component is that of a germ of `f_* ℱ`
at `P`, since `𝔪_P` kills `Γ(X_1, ℱ_1)`. -/
private theorem exists_res_nonvanishingLocus_eq_univ [IsLocallyNoetherian X] [IsProper f]
    [F.IsCoherent] (hP : IsClosed ({P} : Set X))
    (htriv : ∀ n, 1 ≤ n → ∃ t : Γ(infinitesimalModule f F P n, ⊤),
      Stacks.Ample.nonvanishingLocus (infinitesimalModule f F P n) t = Set.univ) :
    ∃ (U : X.Opens) (hU : P ∈ U) (s : Γ(F, f ⁻¹ᵁ U)),
      Stacks.Ample.nonvanishingLocus (infinitesimalModule f F P 1)
        ((infinitesimalModule f F P 1).presheaf.map
          (homOfLE (top_le_preimage_infinitesimalι f P 1 U hU)).op
          (((Scheme.Modules.pullbackPushforwardAdjunction (infinitesimalι f P 1)).unit.app F).app
            (f ⁻¹ᵁ U) s)) = Set.univ := by
  have hψ : ∀ l m n (h₁ : l ≤ m) (h₂ : m ≤ n) (x : Γ(infinitesimalModule f F P n, ⊤)),
      transition f F P h₁ (transition f F P h₂ x) = transition f F P (h₁.trans h₂) x :=
    fun l m n h₁ h₂ x =>
      haveI := isClosedImmersion_infinitesimalι f hP n
      transition_transition f F P h₁ h₂ x
  have hart : ∀ n, 1 ≤ n → IsArtinian (X.presheaf.stalk P) Γ(infinitesimalModule f F P n, ⊤) :=
    fun n hn => isArtinian_sections f F P hn
  haveI := hart 1 le_rfl
  obtain ⟨N, hN, hst⟩ := exists_range_eq (fun m n h => transition f F P h) hψ (n := 1)
  obtain ⟨t, ht⟩ := htriv N hN
  have hz : IsStable (fun m n h => transition f F P h) 1 (transition f F P hN t) := by
    intro j hj
    rcases le_total j N with hjN | hNj
    · exact range_le_range (fun m n h => transition f F P h) hψ hj hjN ⟨t, rfl⟩
    · rw [hst j hNj]; exact ⟨t, rfl⟩
  obtain ⟨y, hy⟩ := exists_towerLimit_proj_eq (fun m n h => transition f F P h) hψ hart hz
  obtain ⟨Φ, hΦ⟩ :=
    MMP.FormalFunctions.nonempty_adicCompletion_pushforwardStalk_linearEquiv_towerLimit_germ
      f F P (fun m n h => transition f F P h) (fun m n h x => transition_eq f F P h x)
  obtain ⟨g, hg⟩ := Submodule.mkQ_surjective _
    (AdicCompletion.eval (stalkMaximalIdeal P) _ 1 (Φ.symm y))
  have hker : Φ.symm y - AdicCompletion.of (stalkMaximalIdeal P) _ g ∈
      LinearMap.ker (AdicCompletion.eval (stalkMaximalIdeal P) _ 1) := by
    rw [LinearMap.mem_ker, map_sub, AdicCompletion.eval_of, hg, sub_self]
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian _), pow_one] at hker
  have hkill : ∀ w ∈ (stalkMaximalIdeal P • ⊤ : Submodule (X.presheaf.stalk P)
      (AdicCompletion (stalkMaximalIdeal P) _)), towerLimit.proj 1 (Φ w) = 0 := by
    intro w hw
    refine Submodule.smul_induction_on hw (fun r hr w _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul, map_smul, sectionsModule_smul,
        infinitesimalBaseRingHom_eq_zero f P 1 (by rwa [pow_one]), zero_smul]
    · rw [map_add, map_add, ha, hb, add_zero]
  have h1 : towerLimit.proj 1 (Φ (AdicCompletion.of (stalkMaximalIdeal P) _ g)) =
      transition f F P hN t := by
    have := hkill _ hker
    rw [map_sub, map_sub, sub_eq_zero, LinearEquiv.apply_symm_apply, hy] at this
    exact this.symm
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.germ_exist _ g
  exact ⟨U, hU, s, (congrArg (Stacks.Ample.nonvanishingLocus (infinitesimalModule f F P 1))
    ((hΦ 1 U hU s).symm.trans h1)).trans (nonvanishingLocus_transition f F P hN t ht)⟩

end Formal

/-! ### From the fibre to a neighbourhood of the fibre -/

section Principal

open Stacks.FormalFunctions Stacks.NonvanishingLocusRestrict

variable {X Y : Scheme.{u}}

/-- An invertible module with a nowhere vanishing global section is trivial. -/
private theorem nonempty_iso_unit_of_nonvanishingLocus_eq_univ {Z : Scheme.{u}} (M : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M] (t : Γ(M, ⊤))
    (ht : Stacks.Ample.nonvanishingLocus M t = Set.univ) :
    Nonempty (M ≅ SheafOfModules.unit Z.ringCatSheaf) := by
  have hiso := AlgebraicGeometry.isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ M
    ((Stacks.NonvanishingSpelling.sectionsEquiv Z M).symm t)
    ((Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq Z M t).trans ht)
  exact ⟨(asIso (M.unitHomEquiv.symm ((Stacks.NonvanishingSpelling.sectionsEquiv Z M).symm
    t))).symm⟩

/-- **A section of `𝒪_Y(D)` over `W` vanishing nowhere on `W` is a local equation of `D` on `W`**,
up to inverting it: it trivializes `𝒪_Y(D)|_W`. -/
private theorem exists_isLocalEquation_of_subset_nonvanishingLocusOn [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral Y] [CompactSpace Y] {D : Divisor Y} (hD : D.IsCartier)
    {W : Y.Opens} (s : Γ(D.divisorialSheaf, W))
    (hs : (W : Set Y) ⊆ nonvanishingLocusOn D.divisorialSheaf W s) :
    ∃ φ : (RationalFunctions Y)ˣ, D.IsLocalEquation W φ := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  have h1 : Stacks.Ample.nonvanishingLocus
      (Stacks.AmpleLocallyClosed.pullbackModule W.ι D.divisorialSheaf)
      (restrictSection W _ s) = Set.univ := by
    rw [nonvanishingLocus_restrictSection]
    exact Set.eq_univ_of_forall fun x => hs x.2
  obtain ⟨e⟩ := nonempty_iso_unit_of_nonvanishingLocus_eq_univ _ _ h1
  exact MMP.Fourfold.exists_isLocalEquation_of_restrict_iso_unit
    ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫ e)

/-- **A local equation on a neighbourhood of the fibre is one over a neighbourhood of `P`**: the
image of the closed complement is closed, `f` being proper, and misses `P`. -/
private theorem exists_isLocalEquation_preimage_of_subset [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} [IsProper f]
    {D : Divisor Y} {P : X} {W : Y.Opens} (hW : f.base ⁻¹' {P} ⊆ W)
    {φ : (RationalFunctions Y)ˣ} (hφ : D.IsLocalEquation W φ) :
    ∃ U : X.Opens, P ∈ U ∧ ∃ φ : (RationalFunctions Y)ˣ, D.IsLocalEquation (f ⁻¹ᵁ U) φ :=
  ⟨⟨(f.base '' (W : Set Y)ᶜ)ᶜ, (f.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩,
    fun ⟨y, hy, hyP⟩ => hy (hW hyP), φ,
    hφ.mono fun y hy => by_contra fun h => hy ⟨y, h, rfl⟩⟩

/-- **A section whose pullback does not vanish at a point does not vanish at its image.** -/
private theorem mem_nonvanishingLocusOn_of_mem_nonvanishingLocus {Z W : Scheme.{u}} (i : Z ⟶ W)
    (G : W.Modules) {U : W.Opens} (hU : ⊤ ≤ i ⁻¹ᵁ U) (s : Γ(G, U)) {z : Z}
    (hz : z ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback i).obj G)
      (((Scheme.Modules.pullback i).obj G).presheaf.map (homOfLE hU).op
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G).app U s))) :
    i z ∈ nonvanishingLocusOn G U s := by
  rw [← Set.mem_preimage, preimage_nonvanishingLocusOn]
  refine ⟨hU trivial, fun hmem => hz ?_⟩
  exact (congrArg (· ∈ Stacks.ModuleStalk.maximalSmul ((Scheme.Modules.pullback i).obj G) z)
    (TopCat.Presheaf.germ_res_apply ((Scheme.Modules.pullback i).obj G).presheaf (homOfLE hU) z
      trivial _)).mpr hmem

/-- **The fibre over `P` is the image of the first thickening `X_1`.** -/
private theorem mem_range_infinitesimalι_one (f : Y ⟶ X) (P : X) {y : Y} (hy : f y = P) :
    y ∈ Set.range (infinitesimalι f P 1) := by
  rw [infinitesimalι, Scheme.Pullback.range_fst]
  haveI : Nontrivial (stalkQuotient P 1) :=
    Ideal.Quotient.nontrivial_iff.2 (by
      rw [pow_one]
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
  obtain ⟨z⟩ : Nonempty (Spec (stalkQuotient P 1)) := inferInstance
  show f y ∈ Set.range (infinitesimalBase P 1)
  exact ⟨z, (Set.mem_singleton_iff.1 (range_infinitesimalBase_subset P 1 ⟨z, rfl⟩)).trans hy.symm⟩

end Principal

/-- **A numerically trivial divisor is principal near a rational surface singularity.** Let
`f : Y ⟶ X` be the minimal resolution of a rational surface singularity `(X, P)` over an
algebraically closed field `k`, and let `D` be a Cartier divisor on `Y` with `(D · E) = 0` for
every exceptional curve `E` of `f`. Then there are an open neighbourhood `U` of `P` and a
rational function `φ` on `Y` with `D = div(φ)` on `f⁻¹(U)`. -/
@[mmp "lem_mmp_foundation_fa3_numerically_trivial_line_bundle_principal"]
public theorem IsMinimalGermResolution.exists_mem_isLocalEquation_preimage {k : Type u}
    [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hrat : IsRationalSurfaceSingularity sX P) (hf : IsMinimalGermResolution sX P f)
    {D : Divisor Y} (hD : D.IsCartier)
    (hDE : ∀ E : Mori.PrimeDivisor Y, IsGermExceptionalCurve f P E →
      IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor D) E.idealSheaf 0) :
    ∃ U : X.Opens, P ∈ U ∧ ∃ φ : (RationalFunctions Y)ˣ, D.IsLocalEquation (f ⁻¹ᵁ U) φ := by
  haveI : IsProper f := hf.1.isSmoothResolution.isProper
  haveI : LocallyOfFiniteType sX := hf.1.isSurfaceGerm.1.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : IsIntegral Y := hf.1.isIntegral sX
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsCoherent D.divisorialSheaf :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Y _
  by_cases hC : ∃ C, IsGermExceptionalCurve f P C
  · obtain ⟨U₀, hU₀, s, hs⟩ := exists_res_nonvanishingLocus_eq_univ f D.divisorialSheaf P
      hf.1.isSurfaceGerm.2.2.1 fun n _ => exists_nonvanishingLocus_infinitesimalModule_eq_univ
        hrat hf _ (degreeOn_divisorialSheaf_eq_zero hD hDE) hC n
    let W := Stacks.SectionPowerOpen.nonvanishingOpenOn D.divisorialSheaf (f ⁻¹ᵁ U₀) s
    have hWle : W ≤ f ⁻¹ᵁ U₀ := Stacks.SectionPowerOpen.nonvanishingOpenOn_le _ _ s
    obtain ⟨φ, hφ⟩ := exists_isLocalEquation_of_subset_nonvanishingLocusOn hD
      (D.divisorialSheaf.presheaf.map (homOfLE hWle).op s)
      fun y hy => ⟨hy, by rw [TopCat.Presheaf.germ_res_apply]; exact hy.2⟩
    refine exists_isLocalEquation_preimage_of_subset (f := f) (fun y hy => ?_) hφ
    obtain ⟨w, rfl⟩ := mem_range_infinitesimalι_one f P hy
    exact mem_nonvanishingLocusOn_of_mem_nonvanishingLocus _ _ _ s
      (by rw [hs]; exact Set.mem_univ w)
  · by_cases hne : ∃ y, f y = P
    · obtain ⟨y₀, hy₀⟩ := hne
      have hF : f.base ⁻¹' {P} = {y₀} :=
        (exists_isGermExceptionalCurve_mem_or hf.1 hy₀).resolve_left
          fun ⟨C, hC', _⟩ => hC ⟨C, hC'⟩
      obtain ⟨V, hV, ⟨e⟩⟩ := (isInvertible_iff_exists_restrict_iso_unit Y
        D.divisorialSheaf).mp inferInstance y₀
      obtain ⟨φ, hφ⟩ := MMP.Fourfold.exists_isLocalEquation_of_restrict_iso_unit e
      exact exists_isLocalEquation_preimage_of_subset (f := f)
        (hF ▸ Set.singleton_subset_iff.2 hV) hφ
    · exact exists_isLocalEquation_preimage_of_subset (f := f) (D := D) (W := ⊥)
        (fun y hy => absurd ⟨y, hy⟩ hne) (φ := 1) fun _ ⟨_, _, hx⟩ => hx.elim

end MMP.Flips
