module

public import MMP.Analysis.Complex.Dolbeault.Resolution
public import MMP.Analysis.Complex.Dolbeault.Restriction
public import MMP.Topology.Sheaves.ExtRightDerived
public import MMP.Analysis.Complex.Dolbeault.DbarGlobal
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueAlternatingVanishing
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.EssentiallySurjective
public import MMP.Analysis.Complex.CauchyTransformRungeMontel
public import MMP.AlgebraicGeometry.Morphisms.Birational.IsoInCodimOne
public import MMP.Topology.Sheaves.GodementFlasqueResolution
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalSectionsDerived

/-!
# Inputs to GAGA: parameters, Dolbeault vanishing, Leray's theorem, resolutions on `ℙᴺ`

This file collects four results used in the comparison of algebraic and analytic coherent
cohomology.

*Differentials of regular parameters.* Let `X` be a smooth variety of dimension `n` over a field
`k` of characteristic `0`, `x ∈ X` a closed point and `z₁, …, zₙ` a regular system of parameters
of `𝒪_{X,x}`. Then `dz₁, …, dzₙ` is a basis of `Ω_{𝒪_{X,x}/k}`, `Ω¹_X` is locally free of rank
`n`, and `⋀ⁿ Ω_{𝒪_{X,x}/k}` is free on `dz₁ ∧ ⋯ ∧ dzₙ`. Since `κ(x)/k` is finite separable, the
cotangent space `𝔪/𝔪²` maps isomorphically onto `κ(x) ⊗ Ω_{𝒪_{X,x}/k}`, and Nakayama lifts the
basis of the fibre; the rank of `Ω_X` is constant on the irreducible scheme `X`.

*Dolbeault vanishing.* Let `D = D₁ × ⋯ × Dₙ ⊆ ℂⁿ` be a product of bounded open rectangles, open
discs (possibly `ℂ`) and open annuli. Then `H^q(D, 𝒪) = 0` for `q ≥ 1`. If `K ⊆ W` is a product
of closed rectangles inside an open `W`, every class in `H^q(W, 𝒪)`, `q ≥ 1`, vanishes on some
open product of bounded open rectangles `V` with `K ⊆ V ⊆ W`. The proof goes through the
Dolbeault resolution of `𝒪` by smooth `(0, q)`-forms, which are acyclic, and the solution of
`∂̄ u = f` on `D`, obtained from an exhaustion of `D` by products of compacts and Runge
approximation.

*Leray's theorem.* If a sheaf of abelian groups `S` on `T` has no higher cohomology on any
finite intersection of members of an open cover `𝒰` indexed by a linearly ordered set, the
ordered Čech complex `Č^•_<(𝒰, S)` computes `H^•(T, S)`, compatibly with maps of sheaves, with
monotone refinements, and with pullback along continuous maps followed by a map `f⁻¹ S ⟶ S'`.
Both are compared with the total complex of the double complex `Č^p_<(𝒰, J^q)` of an injective
resolution `J^•` of `S`: its rows are exact because injective sheaves are flasque, its columns
because `S` is acyclic on the intersections.

*Resolutions on `ℙᴺ_ℂ`.* Every coherent sheaf `𝒢` on `ℙᴺ_ℂ` has an exact resolution
`0 → ℰ_{N+1} → ⋯ → ℰ₀ → 𝒢 → 0` by finite direct sums of twisting sheaves `𝒪(d)`. By Serre's
correspondence `𝒢 = M~` for a finitely generated graded module `M` over `S = ℂ[x₀, …, x_N]`;
a graded free resolution of `M` of length at most `N + 1` is carried by the exact additive
functor `M ↦ M~`, which sends `S(d)` to `𝒪(d)`, to the required resolution.

## Main results

* `MMP.exists_basis_kaehlerDifferential_stalk_of_isRegularSystemOfParameters`: differentials of
  a regular system of parameters form a basis.
* `MMP.Analytic.isZero_sheafCohomology_holomorphic_of_isProductDomain`: Dolbeault vanishing on
  product domains, and vanishing of classes near a product of closed rectangles.
* `MMP.Analytic.exists_orderedCechComplex_homologyIso_sheafCohomology`: Leray's theorem for
  ordered Čech complexes, with its three compatibilities.
* `MMP.Analytic.exists_twistingSheaf_resolution_projectiveSpace`: finite resolutions of coherent
  sheaves on `ℙᴺ_ℂ` by sums of twisting sheaves.

## Implementation notes

* The stalk `Ω¹_{X,x}` is `Ω[𝒪_{X,x}⁄k]` for the `k`-algebra structure `MMP.Mori.stalkAlgebra`,
  and the sections of `Ω¹_X` over an affine open `V` are `Ω[Γ(X, V)⁄k]` for
  `MMP.Mori.sectionAlgebra`. "Locally free of rank `n`" is read as: every point has an affine
  open neighbourhood `V` with `Ω[Γ(X, V)⁄k]` free on `Fin n`. The source works over `ℂ`; any
  field of characteristic `0` suffices, which is what the comparison
  `𝔪/𝔪² ≅ Ω_{𝒪_{X,x}/k} ⊗ κ(x)` needs.
* `ℂⁿ` is `EuclideanSpace ℂ (Fin n)` with the sheaf `MMP.Analytic.holomorphicRingCatSheaf`; on an
  open `U` the sheaf is its inverse image along `Opens.inclusion' U`, and cohomology is
  `MMP.Analytic.sheafCohomology`. A rectangle is `Set.Ioo a b ×ℂ Set.Ioo c d`, a disc is
  `Metric.eball c R` with `R : ℝ≥0∞`, and an annulus is `{z | r < edist z c ∧ edist z c < R}`.
  "A class vanishes on `V ⊆ W`" means its image under `MMP.Analytic.sheafCohomologyPullback`
  along `V ⟶ W` is zero.
* The ordered Čech complex is `Stacks.Cech.orderedCechComplex`. The Leray isomorphisms are one
  family indexed by the index set, space, cover and sheaf, so that the compatibilities relate
  its members; each cochain map in a compatibility is given through its formula on sections.
* A resolution on `ℙᴺ_ℂ` is a chain complex `ℰ•` with an augmentation `ε : ℰ₀ ⟶ 𝒢` whose
  augmented complex is acyclic, with `ℰⱼ = 0` for `j > N + 1` and each `ℰⱼ` isomorphic to a
  finite coproduct `∐ᵢ 𝒪(dᵢ)`. The graded free module `⊕ⱼ S(-dⱼ)` is built on `Fin r → S`,
  graded coordinatewise, and identified with the biproduct of the `S(-dⱼ)`.

## References

* [R. Lazarsfeld, *Positivity in algebraic geometry I*][lazarsfeld2004]
* [Hörmander, *An introduction to complex analysis in several variables*, Ch. II]
* [Grauert–Remmert, *Theory of Stein spaces*]
* [Stacks Project, Tag 01EV and Tag 01FM]
* [Serre, *Géométrie algébrique et géométrie analytique*], §13
-/

@[expose] public section

universe u

namespace MMP

section ParameterDifferentials

open CategoryTheory AlgebraicGeometry IsLocalRing MMP.Flips.ResolutionInputs

/-- At a closed point of a smooth scheme over a field of characteristic zero, the differentials
of a regular system of parameters are a basis of `Ω_{𝒪_{X,x}/k}`: the linear-combination map
is bijective. -/
private theorem bijective_linearCombination_D {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (x : X) (hx : IsClosed ({x} : Set X))
    {n : ℕ} {z : Fin n → X.presheaf.stalk x} (hz : Mori.IsRegularSystemOfParameters z) :
    letI := Mori.stalkAlgebra sX x
    Function.Bijective (Finsupp.linearCombination (X.presheaf.stalk x)
      (fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (z i))) := by
  let := Mori.stalkAlgebra sX x
  obtain ⟨_, _, _⟩ := stalk_facts sX x
  have := finite_residueField_of_isClosed sX x hx
  have : Algebra.FormallyUnramified k (ResidueField (X.presheaf.stalk x)) :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  have : Module.Projective (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] :=
    ((Algebra.formallySmooth_iff _ _).mp ‹_›).1
  have : Module.Flat (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := .of_projective
  obtain ⟨hz0, hli, -⟩ := cotangent_basis_of_regular z hz.1 hz.2
  apply Module.IsLocalRing.linearCombination_bijective_of_flat
  refine ⟨linearIndependent_tmul_D k z hz0 hli, ?_⟩
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  exact top_le_iff.mp (span_tmul_D k z hz.1)

/-- Constancy of the rank of `Ω`: on an irreducible smooth scheme, if `Ω` is free on `Fin n` at
one point (given by germs whose differentials are a basis), then every point has an affine
neighbourhood on which `Ω` is free of rank `n`. -/
private theorem exists_affine_basis_of_bijective {k : Type u} [Field k] {X : Scheme.{u}}
    [IrreducibleSpace X] (sX : X ⟶ Spec (.of k)) [Smooth sX] (x : X) {n : ℕ}
    (z : Fin n → X.presheaf.stalk x)
    (hbij : letI := Mori.stalkAlgebra sX x
      Function.Bijective (Finsupp.linearCombination (X.presheaf.stalk x)
        (fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (z i))))
    (y : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : y ∈ V),
      letI := Mori.sectionAlgebra sX V
      Nonempty (Module.Basis (Fin n) Γ(X, V) Ω[Γ(X, V)⁄k]) := by
  obtain ⟨V, -, hxV, _, -, hbV⟩ := exists_affineOpen_basis_of_bijective sX x z hbij
  obtain ⟨U, hyU, m, t, ht, -, -⟩ := exists_isLocalCoordinatesOn sX y
  obtain ⟨w, hwU, hwV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen ⟨y, hyU⟩ ⟨x, hxV⟩
  obtain ⟨W, hW, hwW, hWUV⟩ :=
    exists_isAffineOpen_mem_and_subset (show w ∈ U ⊓ V from ⟨hwU, hwV⟩)
  obtain ⟨bW, -⟩ := ht ⟨W, hW⟩ (hWUV.trans inf_le_left)
  obtain ⟨bW', -⟩ := hbV W hW (hWUV.trans inf_le_right)
  let := Mori.sectionAlgebra sX W
  have : Nonempty W := ⟨⟨w, hwW⟩⟩
  obtain rfl : m = n := by
    simpa using (Module.finrank_eq_card_basis bW).symm.trans (Module.finrank_eq_card_basis bW')
  obtain ⟨W', hW', hyW', hW'U⟩ := exists_isAffineOpen_mem_and_subset hyU
  exact ⟨W', hW', hyW', ⟨(ht ⟨W', hW'⟩ hW'U).choose⟩⟩

/-- The top exterior power of a module with a basis indexed by `Fin n` is free on the wedge of
the basis vectors. -/
private theorem exists_basis_exteriorPower_top {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {n : ℕ} (b : Module.Basis (Fin n) R M) :
    ∃ β : Module.Basis Unit R (⋀[R]^n M), β () = exteriorPower.ιMulti R n b := by
  let s₀ : Set.powersetCard (Fin n) n := Set.powersetCard.ofFinEmbEquiv (RelEmbedding.refl (· ≤ ·))
  have hs : ∀ s : Set.powersetCard (Fin n) n, s = s₀ := fun s => Subtype.ext <| by
    rw [Finset.eq_univ_of_card _ ((Set.powersetCard.card_eq s).trans (Fintype.card_fin n).symm),
      Finset.eq_univ_of_card _ ((Set.powersetCard.card_eq s₀).trans (Fintype.card_fin n).symm)]
  let e : Set.powersetCard (Fin n) n ≃ Unit :=
    ⟨fun _ => (), fun _ => s₀, fun s => (hs s).symm, fun _ => rfl⟩
  refine ⟨(b.exteriorPower n).reindex e, ?_⟩
  rw [Module.Basis.reindex_apply, exteriorPower.basis_apply]
  change exteriorPower.ιMulti_family R n b s₀ = _
  simp [exteriorPower.ιMulti_family, s₀]

/-- **Differentials of regular parameters form a basis.** Let `X` be a smooth variety of
dimension `n` over a field `k` of characteristic `0`, `x` a closed point and `z₁, …, zₙ` a regular
system of parameters of `𝒪_{X,x}`. Then `dz₁, …, dzₙ` is an `𝒪_{X,x}`-basis of `Ω_{𝒪_{X,x}/k}`;
every point of `X` has an affine open neighbourhood `V` with `Ω_{Γ(X,V)/k}` free of rank `n`;
and `⋀ⁿ Ω_{𝒪_{X,x}/k}` is free with basis `dz₁ ∧ ⋯ ∧ dzₙ`. -/
@[mmp "lem_mmp_foundation_laz_parameter_differentials_basis"]
public theorem exists_basis_kaehlerDifferential_stalk_of_isRegularSystemOfParameters
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : Mori.IsVariety k sX) (hsm : Mori.IsSmoothScheme sX) {n : ℕ}
    (hdim : topologicalKrullDim X = n) (x : X) (hx : IsClosed ({x} : Set X))
    (z : Fin n → X.presheaf.stalk x) (hz : Mori.IsRegularSystemOfParameters z) :
    letI := Mori.stalkAlgebra sX x
    (∃ b : Module.Basis (Fin n) (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k],
        ∀ i, b i = KaehlerDifferential.D k (X.presheaf.stalk x) (z i)) ∧
      (∀ y : X, ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : y ∈ V),
        letI := Mori.sectionAlgebra sX V
        Nonempty (Module.Basis (Fin n) Γ(X, V) Ω[Γ(X, V)⁄k])) ∧
      ∃ β : Module.Basis Unit (X.presheaf.stalk x)
          (⋀[X.presheaf.stalk x]^n Ω[X.presheaf.stalk x⁄k]),
        β () = exteriorPower.ιMulti (X.presheaf.stalk x) n
          (fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (z i)) := by
  have : Smooth sX := (Mori.isSmoothScheme_iff sX).mp hsm
  have : IsIntegral X := hX.toIsIntegral
  have hbij := bijective_linearCombination_D sX x hx hz
  have hb := basisOfBijective_apply _ hbij
  refine ⟨⟨_, hb⟩, exists_affine_basis_of_bijective sX x z hbij, ?_⟩
  obtain ⟨β, hβ⟩ := exists_basis_exteriorPower_top (basisOfBijective _ hbij)
  exact ⟨β, hβ.trans (congrArg _ (funext hb))⟩

end ParameterDifferentials

end MMP

namespace MMP.Analytic

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

/-! ### Sections over an open and restriction to it -/

section Restriction

variable {T : TopCat.{u}}

attribute [local instance] globalSections_additive

/-- Sections over an open, as a functor on sheaves. -/
private noncomputable abbrev sectionsOver (V : Opens T) :
    TopCat.Sheaf AddCommGrpCat.{u} T ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{u}).obj (op V)

private instance (V : Opens T) : PreservesFiniteLimits (sectionsOver V) :=
  inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology T)
    AddCommGrpCat.{u} ⋙ (evaluation (Opens T)ᵒᵖ AddCommGrpCat.{u}).obj (op V)))

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms in
private lemma pullback_preservesFiniteLimits {T' : TopCat.{u}} (f : T' ⟶ T) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  unfold TopCat.Sheaf.pullback
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

private lemma pullback_preservesHomology {T' : TopCat.{u}} (f : T' ⟶ T) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).PreservesHomology := by
  have := pullback_preservesFiniteLimits f
  have :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).leftAdjoint_preservesColimits
  infer_instance

/-- Sections of the restriction to `V` are sections over `V`. -/
private noncomputable def sectionsPullbackIso (V : Opens T) :
    TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' V) ⋙
      globalSections ((Opens.toTopCat T).obj V) ≅ sectionsOver V :=
  Functor.isoWhiskerRight (V.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}) _ ≪≫
    NatIso.ofComponents (fun F => F.obj.mapIso (eqToIso (Opens.isOpenEmbedding_obj_top V).symm).op)
      (fun a => (a.hom.naturality _).symm)

end Restriction

/-! ### Dolbeault vanishing on product domains -/

section Dolbeault

open scoped ENNReal Manifold ContDiff

attribute [local instance] globalSections_additive

/-- **Acyclicity of smooth forms.** On an open `D ⊆ ℂⁿ`, the restriction of the sheaf of smooth
`(0, q)`-forms has no higher right derived functors of global sections: it is a retract of a sum of
copies of the sheaf of smooth functions on `D`, which is acyclic
(`MMP.Analytic.subsingleton_H'_smoothSheafModule`). -/
private lemma isZero_rightDerived_dolbeault {n : ℕ}
    (D : Opens (TopCat.of (EuclideanSpace ℂ (Fin n)))) (q k : ℕ) (hk : 0 < k) :
    IsZero ((Functor.rightDerived
        (globalSections ((Opens.toTopCat (TopCat.of (EuclideanSpace ℂ (Fin n)))).obj D)) k).obj
          ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' D)).obj
            (dolbeaultSheaf n q))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [zero_add]
  have : HasExt.{1} (Sheaf (Opens.grothendieckTopology (TopCat.of D)) AddCommGrpCat.{0}) :=
    hasExt_of_enoughInjectives.{1} _
  have : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of D)) := ‹_›
  have : HasExt.{1} (Sheaf (Opens.grothendieckTopology
      ((Opens.toTopCat (TopCat.of (EuclideanSpace ℂ (Fin n)))).obj D)) AddCommGrpCat.{0}) := ‹_›
  have hsm := subsingleton_H'_smoothSheafModule.{1} 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (M := D)
    (R := ℂ) (SheafOfModules.unit _) ⊤ k
  have hN : Subsingleton (Sheaf.H' (dolbeaultRestrictSheaf D q) (k + 1) ⊤) :=
    subsingleton_ext_of_sum_comp_eq_id Finset.univ (dolbeaultCoeff D q) (dolbeaultOfCoeff D q)
      (sum_dolbeaultCoeff_comp_dolbeaultOfCoeff D q) (k + 1) hsm
  have h1 := isZero_rightDerived_globalSections_of_subsingleton_H'.{1}
    (X := (Opens.toTopCat (TopCat.of (EuclideanSpace ℂ (Fin n)))).obj D)
    (dolbeaultRestrictSheaf D q) k hN
  exact h1.of_iso (((globalSections
    ((Opens.toTopCat (TopCat.of (EuclideanSpace ℂ (Fin n)))).obj D)).rightDerived (k + 1)).mapIso
    ((D.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{0}).app _))

/-- **Reduction of part (a) to two statements about `∂̄`.** If closed forms are locally exact
(the local `∂̄`-lemma) and every `∂̄`-closed form of positive degree on `D` is `∂̄`-exact on `D`,
then `𝒪` has no higher cohomology on `D`. -/
private lemma isZero_sheafCohomology_of_dbar_exact {n : ℕ}
    (D : Opens (TopCat.of (EuclideanSpace ℂ (Fin n))))
    (hloc : ∀ (q : ℕ) (U : Opens (EuclideanSpace ℂ (Fin n))) (s : dolbeaultSections n (q + 1) U),
      dbarSections n (q + 1) U s = 0 → ∀ x ∈ U, ∃ (V : Opens (EuclideanSpace ℂ (Fin n)))
        (_ : x ∈ V) (hVU : V ≤ U) (t : dolbeaultSections n q V),
        dbarSections n q V t = dolbeaultRestrict n (q + 1) hVU s)
    (hglob : ∀ (q : ℕ) (s : dolbeaultSections n (q + 1) (D : Set (EuclideanSpace ℂ (Fin n)))),
      dbarSections n (q + 1) D s = 0 → ∃ t, dbarSections n q D t = s)
    (q : ℤ) (hq : 0 < q) :
    IsZero ((sheafCohomology ((Opens.toTopCat (TopCat.of (EuclideanSpace ℂ (Fin n)))).obj D) q).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' D)).obj
        (holomorphicSheafAb n))) := by
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, q = ((p + 1 : ℕ) : ℤ) := ⟨q.toNat - 1, by omega⟩
  let T := (Opens.toTopCat (TopCat.of (EuclideanSpace ℂ (Fin n)))).obj D
  let R := TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' D)
  have tk := sheafCohomology_toolkit.{0, 0, 0, 0, 0} T
  let A := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj (dolbeaultComplex n)
  let ι' : (CochainComplex.single₀ _).obj (R.obj (holomorphicSheafAb n)) ⟶ A :=
    (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℕ) 0).inv.app _ ≫
      (R.mapHomologicalComplex _).map (dolbeaultAugmentation n)
  have hι' : QuasiIso ι' := by
    have := pullback_preservesHomology (Opens.inclusion' D)
    have := quasiIso_dolbeaultAugmentation hloc
    infer_instance
  obtain ⟨e, -⟩ := tk.2.1.2.2.1 A ι' hι'
    (fun q k hk => isZero_rightDerived_dolbeault D q k hk) (p + 1)
  refine IsZero.of_iso ?_ ((sheafCohomologyIso T (p + 1)).app _)
  refine IsZero.of_iso ?_ e.symm
  have : (sectionsOver D).PreservesZeroMorphisms :=
    inferInstanceAs ((sheafToPresheaf (Opens.grothendieckTopology _) AddCommGrpCat.{0} ⋙
      (evaluation (Opens _)ᵒᵖ AddCommGrpCat.{0}).obj (op D)).PreservesZeroMorphisms)
  refine IsZero.of_iso ?_ (HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex (sectionsPullbackIso D) (ComplexShape.up ℕ)).app
      (dolbeaultComplex n)) (p + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro x hx
  have hx' : dbarSections n (p + 1) D x = 0 := by
    change ((dolbeaultComplex n).d (p + 1) (p + 1 + 1)).hom.app (op D) x = 0 at hx
    rwa [dolbeaultComplex_d] at hx
  obtain ⟨t, ht⟩ := hglob p x hx'
  refine ⟨t, ?_⟩
  change ((dolbeaultComplex n).d p (p + 1)).hom.app (op D) t = x
  rwa [dolbeaultComplex_d]

/-- Holomorphic functions on open subsets of `ℂⁿ` are smooth (Osgood's lemma). -/
private lemma contDiffOn_of_differentiableOn_euclidean {n : ℕ}
    {Ω : Set (EuclideanSpace ℂ (Fin n))}
    {h : EuclideanSpace ℂ (Fin n) → ℂ} (hΩ : IsOpen Ω) (hh : DifferentiableOn ℂ h Ω) :
    ContDiffOn ℝ ∞ h Ω := by
  let e := EuclideanSpace.equiv (Fin n) ℂ
  have hΩ' : IsOpen (e.symm ⁻¹' Ω) := hΩ.preimage e.symm.continuous
  have hg : DifferentiableOn ℂ (h ∘ e.symm) (e.symm ⁻¹' Ω) :=
    hh.comp e.symm.differentiableOn (fun _ hz => hz)
  obtain ⟨-, hAn, -⟩ := (MMP.SeveralComplex.cauchy_osgood_laurent.{0, 0} ℂ).2.2.1 n _ _ hΩ'
    hg.continuousOn fun ζ hζ j =>
      (hg.differentiableAt (hΩ'.mem_nhds (by simpa using hζ))).comp (ζ j)
        (hasFDerivAt_update (i := j) ζ (ζ j)).differentiableAt
  have h1 : ContDiffOn ℂ ∞ ((h ∘ e.symm) ∘ e) Ω :=
    (hAn.contDiffOn hΩ'.uniqueDiffOn).comp e.contDiff.contDiffOn fun z hz => by simpa using hz
  exact (h1.congr fun z _ => by simp).restrict_scalars ℝ

/-- Locally uniform limits of holomorphic functions on open subsets of `ℂⁿ` are holomorphic. -/
private lemma differentiableOn_of_tendstoLocallyUniformlyOn_euclidean {n : ℕ}
    {Ω : Set (EuclideanSpace ℂ (Fin n))} (F : ℕ → EuclideanSpace ℂ (Fin n) → ℂ)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hΩ : IsOpen Ω) (hF : ∀ k, DifferentiableOn ℂ (F k) Ω)
    (hlim : TendstoLocallyUniformlyOn F f Filter.atTop Ω) : DifferentiableOn ℂ f Ω := by
  let e := EuclideanSpace.equiv (Fin n) ℂ
  have hΩ' : IsOpen (e.symm ⁻¹' Ω) := hΩ.preimage e.symm.continuous
  have h := (MMP.SeveralComplex.cauchy_osgood_laurent.{0, 0} ℂ).2.2.2.2.2 n Filter.atTop
    (e.symm ⁻¹' Ω) (fun k => F k ∘ e.symm) (f ∘ e.symm) hΩ'
    (Filter.Eventually.of_forall fun k => (hF k).comp e.symm.differentiableOn fun _ hz => hz)
    (hlim.comp e.symm (fun _ hz => hz) e.symm.continuous.continuousOn)
  have h1 : DifferentiableOn ℂ ((f ∘ e.symm) ∘ e) Ω :=
    h.comp e.differentiableOn fun z hz => by simpa using hz
  exact h1.congr fun z _ => by simp

private lemma dist_le_toReal_iff_edist_le (c z : ℂ) {ρ : ℝ≥0∞} (hρ : ρ ≠ ⊤) :
    dist z c ≤ ρ.toReal ↔ edist z c ≤ ρ := by
  rw [← edist_le_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hρ]

private lemma dist_lt_toReal_iff_edist_lt (c z : ℂ) {ρ : ℝ≥0∞} (hρ : ρ ≠ ⊤) :
    dist z c < ρ.toReal ↔ edist z c < ρ := by
  rw [← edist_lt_ofReal, ENNReal.ofReal_toReal hρ]

open Filter Set in
/-- A nonempty bounded open rectangle is exhausted by closed rectangles, each in the interior of
the next. -/
private lemma exists_exhaustion_rectangle {a b c d : ℝ} (hne : (Ioo a b ×ℂ Ioo c d).Nonempty) :
    ∃ Kf : ℕ → Set ℂ, (∀ m, IsCompact (Kf m)) ∧ (∀ m, Kf m ⊆ Ioo a b ×ℂ Ioo c d) ∧
      (∀ m, Kf m ⊆ interior (Kf (m + 1))) ∧ (∀ z ∈ Ioo a b ×ℂ Ioo c d, ∀ᶠ m in atTop, z ∈ Kf m) ∧
      ∀ m, ∃ a b a' b' : ℝ, a < b ∧ a' < b' ∧
        Kf m = Complex.re ⁻¹' Icc a b ∩ Complex.im ⁻¹' Icc a' b' := by
  obtain ⟨z₀, ⟨ha, hb⟩, hc, hd⟩ := hne
  obtain ⟨M, hM1, hM2⟩ := exists_between (ha.trans hb)
  obtain ⟨N, hN1, hN2⟩ := exists_between (hc.trans hd)
  obtain ⟨al, hal, hal', hal_t⟩ := exists_seq_strictAnti_tendsto' hM1
  obtain ⟨bl, hbl, hbl', hbl_t⟩ := exists_seq_strictMono_tendsto' hM2
  obtain ⟨cl, hcl, hcl', hcl_t⟩ := exists_seq_strictAnti_tendsto' hN1
  obtain ⟨dl, hdl, hdl', hdl_t⟩ := exists_seq_strictMono_tendsto' hN2
  refine ⟨fun m => Icc (al m) (bl m) ×ℂ Icc (cl m) (dl m), fun m => ?_, fun m => ?_,
    fun m => ?_, fun z hz => ?_, fun m => ⟨al m, bl m, cl m, dl m,
      (hal' m).2.trans (hbl' m).1, (hcl' m).2.trans (hdl' m).1, rfl⟩⟩
  · exact isCompact_Icc.reProdIm isCompact_Icc
  · rintro z ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨(hal' m).1.trans_le h1, h2.trans_lt (hbl' m).2⟩,
      (hcl' m).1.trans_le h3, h4.trans_lt (hdl' m).2⟩
  · refine interior_maximal
      (t := Ioo (al (m + 1)) (bl (m + 1)) ×ℂ Ioo (cl (m + 1)) (dl (m + 1)))
      ?_ (isOpen_Ioo.reProdIm isOpen_Ioo) |>.trans' ?_
    · rintro z ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩
    · rintro z ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨(hal (Nat.lt_succ_self m)).trans_le h1, h2.trans_lt (hbl (Nat.lt_succ_self m))⟩,
        (hcl (Nat.lt_succ_self m)).trans_le h3, h4.trans_lt (hdl (Nat.lt_succ_self m))⟩
  · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
    filter_upwards [(tendsto_order.1 hal_t).2 _ h1, (tendsto_order.1 hbl_t).1 _ h2,
      (tendsto_order.1 hcl_t).2 _ h3, (tendsto_order.1 hdl_t).1 _ h4] with m e1 e2 e3 e4
    exact ⟨⟨e1.le, e2.le⟩, e3.le, e4.le⟩

open Filter Set in
/-- A nonempty open annulus is exhausted by closed annuli with the same centre, each in the
interior of the next. -/
private lemma exists_exhaustion_annulus {c : ℂ} {r R : ℝ≥0∞}
    (hne : {z : ℂ | r < edist z c ∧ edist z c < R}.Nonempty) :
    ∃ Kf : ℕ → Set ℂ, (∀ m, IsCompact (Kf m)) ∧
      (∀ m, Kf m ⊆ {z | r < edist z c ∧ edist z c < R}) ∧
      (∀ m, Kf m ⊆ interior (Kf (m + 1))) ∧
      (∀ z ∈ {z : ℂ | r < edist z c ∧ edist z c < R}, ∀ᶠ m in atTop, z ∈ Kf m) ∧
      (∀ z ∈ {z : ℂ | r < edist z c ∧ edist z c < R}, z ≠ c) ∧ ∀ m, ∃ r R : ℝ, 0 < r ∧ r < R ∧
        Kf m = Metric.closedBall c R \ Metric.ball c r := by
  obtain ⟨z₀, hz₁, hz₂⟩ := hne
  obtain ⟨M, hM1, hM2⟩ := exists_between (hz₁.trans hz₂)
  obtain ⟨ρ, hρ, hρ', hρ_t⟩ := exists_seq_strictMono_tendsto' hM2
  obtain ⟨σ, hσ, hσ', hσ_t⟩ := exists_seq_strictAnti_tendsto' hM1
  have hρt : ∀ m, ρ m ≠ ⊤ := fun m => ((hρ' m).2.trans_le le_top).ne
  have hσt : ∀ m, σ m ≠ ⊤ := fun m => ((hσ' m).2.trans (hρ' m).1).ne_top
  have hσ0 : ∀ m, σ m ≠ 0 := fun m => (lt_of_le_of_lt zero_le (hσ' m).1).ne'
  refine ⟨fun m => Metric.closedBall c (ρ m).toReal \ Metric.ball c (σ m).toReal,
    fun m => (isCompact_closedBall _ _).diff Metric.isOpen_ball, fun m z hz => ?_, fun m => ?_,
    fun z hz => ?_, fun z hz h => ?_, fun m => ⟨(σ m).toReal, (ρ m).toReal,
      ENNReal.toReal_pos (hσ0 m) (hσt m),
      ENNReal.toReal_strict_mono (hρt m) ((hσ' m).2.trans (hρ' m).1), rfl⟩⟩
  · obtain ⟨h1, h2⟩ := hz
    rw [Metric.mem_ball, not_lt] at h2
    refine ⟨(hσ' m).1.trans_le ?_,
      ((dist_le_toReal_iff_edist_le c z (hρt m)).1 h1).trans_lt (hρ' m).2⟩
    exact not_lt.1 fun h => (not_lt.2 h2) ((dist_lt_toReal_iff_edist_lt c z (hσt m)).2 h)
  · have hopen : IsOpen (Metric.ball c (ρ (m + 1)).toReal \
        Metric.closedBall c (σ (m + 1)).toReal) :=
      Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
    refine (interior_maximal (Set.sdiff_subset_sdiff Metric.ball_subset_closedBall
      Metric.ball_subset_closedBall) hopen).trans' ?_
    rintro z ⟨h1, h2⟩
    rw [Metric.mem_closedBall] at h1
    rw [Metric.mem_ball, not_lt] at h2
    refine ⟨Metric.mem_ball.2 (h1.trans_lt (ENNReal.toReal_strict_mono (hρt _)
      (hρ (Nat.lt_succ_self m)))), fun h => ?_⟩
    rw [Metric.mem_closedBall] at h
    exact absurd (h.trans_lt' (lt_of_lt_of_le (ENNReal.toReal_strict_mono (hσt _)
      (hσ (Nat.lt_succ_self m))) h2)) (lt_irrefl _)
  · obtain ⟨h1, h2⟩ := hz
    filter_upwards [(tendsto_order.1 hρ_t).1 _ h2, (tendsto_order.1 hσ_t).2 _ h1] with m e1 e2
    refine ⟨(dist_le_toReal_iff_edist_le c z (hρt m)).2 e1.le, fun h => ?_⟩
    exact absurd ((dist_lt_toReal_iff_edist_lt c z (hσt m)).1 (Metric.mem_ball.1 h))
      (not_lt.2 e2.le)
  · subst h
    simp at hz

open Filter Set in
/-- **Exhaustion of a factor.** A nonempty bounded open rectangle, open disc or open annulus is
exhausted by standard compacts (closed rectangles, closed discs, closed annuli with the same
centre), each in the interior of the next. -/
private lemma exists_exhaustion_factor (F : Set ℂ)
    (hF : (∃ a b c d : ℝ, F = Set.Ioo a b ×ℂ Set.Ioo c d) ∨
      (∃ (c : ℂ) (R : ℝ≥0∞), F = Metric.eball c R) ∨
      (∃ (c : ℂ) (r R : ℝ≥0∞), F = {z | r < edist z c ∧ edist z c < R}))
    (hne : F.Nonempty) :
    ∃ Kf : ℕ → Set ℂ, (∀ m, IsCompact (Kf m)) ∧ (∀ m, Kf m ⊆ F) ∧
      (∀ m, Kf m ⊆ interior (Kf (m + 1))) ∧ (∀ z ∈ F, ∀ᶠ m in atTop, z ∈ Kf m) ∧
      ((∃ c : ℂ, (∀ z ∈ F, z ≠ c) ∧ ∀ m, ∃ r R : ℝ, 0 < r ∧ r < R ∧
          Kf m = Metric.closedBall c R \ Metric.ball c r) ∨
        (∀ m, (∃ a b a' b' : ℝ, a < b ∧ a' < b' ∧
            Kf m = Complex.re ⁻¹' Icc a b ∩ Complex.im ⁻¹' Icc a' b') ∨
          (∃ (w : ℂ) (r : ℝ), 0 < r ∧ Kf m = Metric.closedBall w r))) := by
  rcases hF with ⟨a, b, c, d, rfl⟩ | ⟨c, R, rfl⟩ | ⟨c, r, R, rfl⟩
  · obtain ⟨Kf, h₁, h₂, h₃, h₄, h₅⟩ := exists_exhaustion_rectangle hne
    exact ⟨Kf, h₁, h₂, h₃, h₄, Or.inr fun m => Or.inl (h₅ m)⟩
  · obtain ⟨z₀, hz₀⟩ := hne
    have hR : 0 < R := lt_of_le_of_lt zero_le hz₀
    obtain ⟨ρ, hρ, hρ', hρ_t⟩ := exists_seq_strictMono_tendsto' hR
    have hρt : ∀ m, ρ m ≠ ⊤ := fun m => ((hρ' m).2.trans_le le_top).ne
    refine ⟨fun m => Metric.closedBall c (ρ m).toReal, fun m => isCompact_closedBall _ _,
      fun m z hz => ?_, fun m => ?_, fun z hz => ?_,
      Or.inr fun m => Or.inr ⟨c, (ρ m).toReal, ENNReal.toReal_pos (hρ' m).1.ne' (hρt m), rfl⟩⟩
    · exact ((dist_le_toReal_iff_edist_le c z (hρt m)).1 hz).trans_lt (hρ' m).2
    · refine (interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball).trans' ?_
      intro z hz
      exact Metric.mem_ball.2 (lt_of_le_of_lt hz
        (ENNReal.toReal_strict_mono (hρt _) (hρ (Nat.lt_succ_self m))))
    · filter_upwards [(tendsto_order.1 hρ_t).1 _ (show edist z c < R from hz)] with m hm
      exact (dist_le_toReal_iff_edist_le c z (hρt m)).2 hm.le
  · obtain ⟨Kf, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_exhaustion_annulus hne
    exact ⟨Kf, h₁, h₂, h₃, h₄, Or.inl ⟨c, h₅, h₆⟩⟩

/-- **Global solvability of `∂̄` on a product domain.** On a product `D` of bounded open
rectangles, open discs and open annuli, every `∂̄`-closed smooth `(0, q + 1)`-form is the `∂̄` of
a smooth `(0, q)`-form on `D`. -/
private lemma exists_dbarSections_eq_of_isProductDomain {n : ℕ}
    (D : Opens (TopCat.of (EuclideanSpace ℂ (Fin n)))) (F : Fin n → Set ℂ)
    (hF : ∀ j, (∃ a b c d : ℝ, F j = Set.Ioo a b ×ℂ Set.Ioo c d) ∨
      (∃ (c : ℂ) (R : ℝ≥0∞), F j = Metric.eball c R) ∨
      (∃ (c : ℂ) (r R : ℝ≥0∞), F j = {z | r < edist z c ∧ edist z c < R}))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) = {z | ∀ j, z j ∈ F j}) (q : ℕ)
    (s : dolbeaultSections n (q + 1) (D : Set (EuclideanSpace ℂ (Fin n))))
    (hs : dbarSections n (q + 1) D s = 0) : ∃ t, dbarSections n q D t = s := by
  classical
  by_cases hne : ∀ j, (F j).Nonempty
  swap
  · push Not at hne
    obtain ⟨j, hj⟩ := hne
    refine ⟨0, ?_⟩
    rw [map_zero]
    refine Subtype.ext (funext fun I => funext fun z => ?_)
    have hz : z ∉ (D : Set (EuclideanSpace ℂ (Fin n))) := by
      rw [hD]
      intro h
      simpa [hj] using h j
    exact (s.2.2.2 I z hz).symm
  choose Kf hKc hKF hKint hKcov hshape using fun j => exists_exhaustion_factor (F j) (hF j) (hne j)
  let K : ℕ → Fin n → Set ℂ := fun m j => Kf j m
  have hKD : ∀ m, {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j} ⊆ D := fun m z hz => by
    rw [hD]
    exact fun j => hKF j m (hz j)
  have hKK : ∀ m, {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j} ⊆
      interior {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K (m + 1) j} := fun m z hz =>
    interior_maximal (t := {w : EuclideanSpace ℂ (Fin n) | ∀ j, w j ∈ interior (K (m + 1) j)})
      (fun w hw j => interior_subset (hw j)) (isOpen_setOf_forall_mem fun j => isOpen_interior)
      (fun j => hKint j m (hz j))
  have hcov : ∀ z ∈ (D : Set (EuclideanSpace ℂ (Fin n))), ∃ m, ∀ j, z j ∈ K m j := by
    intro z hz
    rw [hD] at hz
    exact (Filter.eventually_all.2 fun j => hKcov j (z j) (hz j)).exists
  let A : Set (Fin n) := {j | ∃ c : ℂ, (∀ z ∈ F j, z ≠ c) ∧ ∀ m, ∃ r R : ℝ, 0 < r ∧ r < R ∧
    Kf j m = Metric.closedBall c R \ Metric.ball c r}
  let c : Fin n → ℂ := fun j => if h : j ∈ A then h.choose else 0
  have hcA : ∀ j (h : j ∈ A), c j = h.choose := fun j h => dite_eq_left h
  have hRunge : ∀ (m : ℕ) (V : Set (EuclideanSpace ℂ (Fin n))) (h : EuclideanSpace ℂ (Fin n) → ℂ),
      IsOpen V → {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j} ⊆ V →
      DifferentiableOn ℂ h V → ∀ ε : ℝ, 0 < ε → ∃ H : EuclideanSpace ℂ (Fin n) → ℂ,
        DifferentiableOn ℂ H D ∧ ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j},
          ‖h z - H z‖ < ε := by
    intro m V h hV hKV hh ε hε
    let e := EuclideanSpace.equiv (Fin n) ℂ
    have hV' : IsOpen (e.symm ⁻¹' V) := hV.preimage e.symm.continuous
    obtain ⟨S, a, hβ, happrox⟩ := (MMP.Gaga.cauchyTransform_runge_montel).2.1 n
      (fun j => K m j) A c
      (fun j hj => by rw [hcA j hj]; exact hj.choose_spec.2 m)
      (fun j hj => (hshape j).resolve_left hj m) (e.symm ⁻¹' V) (h ∘ e.symm) hV'
      (fun y hy => hKV fun j => hy j (Set.mem_univ _))
      (hh.comp e.symm.differentiableOn fun _ hz => hz) ε hε
    refine ⟨fun z => ∑ β ∈ S, a β * ∏ j, (z j - c j) ^ β j, fun z hz => ?_, fun z hz => ?_⟩
    · refine DifferentiableAt.differentiableWithinAt ?_
      refine DifferentiableAt.fun_sum fun β hβS => (differentiableAt_const _).mul ?_
      have hterm : ∀ j, DifferentiableAt ℂ
          (fun w : EuclideanSpace ℂ (Fin n) => (w j - c j) ^ β j) z := by
        intro j
        refine ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).differentiableAt.sub
          (differentiableAt_const _)).zpow ?_
        by_cases hj : j ∈ A
        · left
          have hzF : z j ∈ F j := by
            have : z ∈ (D : Set (EuclideanSpace ℂ (Fin n))) := hz
            rw [hD] at this
            exact this j
          change z j - c j ≠ 0
          rw [hcA j hj, sub_ne_zero]
          exact hj.choose_spec.1 _ hzF
        · exact Or.inr (hβ β hβS j hj)
      have hprod : ∀ T : Finset (Fin n), DifferentiableAt ℂ
          (fun w : EuclideanSpace ℂ (Fin n) => ∏ j ∈ T, (w j - c j) ^ β j) z := by
        intro T
        induction T using Finset.induction_on with
        | empty => simp
        | insert j T hj ih =>
          simp only [Finset.prod_insert hj]
          exact (hterm j).mul ih
      exact hprod Finset.univ
    · simpa [e] using happrox (e z) fun j _ => by simpa [e] using hz j
  have hcl : ∀ I, ∀ z ∈ (D : Set (EuclideanSpace ℂ (Fin n))), dbarForm s.1 I z = 0 := by
    intro I z hz
    simpa [dbarSections_apply, Set.indicator_of_mem hz] using
      congrArg (fun t : dolbeaultSections n (q + 1 + 1) D => t.1 I z) hs
  obtain ⟨u, hudeg, hus, hueq⟩ := exists_dbarForm_eq_of_exhaustion
    (MMP.Gaga.cauchyTransform_runge_montel.1 n) D.isOpen K (fun m j => hKc j m) hKD hKK hcov
    (fun Ω h hΩ hh => contDiffOn_of_differentiableOn_euclidean hΩ hh)
    (fun Ω F f hΩ hF hl => differentiableOn_of_tendstoLocallyUniformlyOn_euclidean F f hΩ hF hl)
    hRunge q s.2.2.1 (fun I hI z _ => by rw [s.2.1 I hI]; rfl) hcl
  have hmem : (fun I => (D : Set (EuclideanSpace ℂ (Fin n))).indicator (u I)) ∈
      dolbeaultSections n q D :=
    ⟨fun I hI => by simp [hudeg I hI],
      fun I => (hus I).congr fun z hz => Set.indicator_of_mem hz _,
      fun I z hz => Set.indicator_of_notMem hz _⟩
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  funext I z
  change (D : Set (EuclideanSpace ℂ (Fin n))).indicator
    (dbarForm (fun J => (D : Set (EuclideanSpace ℂ (Fin n))).indicator (u J)) I) z = s.1 I z
  by_cases hz : z ∈ (D : Set (EuclideanSpace ℂ (Fin n)))
  · rw [Set.indicator_of_mem hz, dbarForm_indicator D.isOpen _ I hz, hueq I z hz]
  · rw [Set.indicator_of_notMem hz, s.2.2.2 I z hz]

/-- **Part (a).** `H^q(D, 𝒪) = 0` for `q > 0` on a product domain `D`. -/
private lemma isZero_sheafCohomology_of_isProductDomain {n : ℕ}
    (D : Opens (TopCat.of (EuclideanSpace ℂ (Fin n)))) (F : Fin n → Set ℂ)
    (hF : ∀ j, (∃ a b c d : ℝ, F j = Set.Ioo a b ×ℂ Set.Ioo c d) ∨
      (∃ (c : ℂ) (R : ℝ≥0∞), F j = Metric.eball c R) ∨
      (∃ (c : ℂ) (r R : ℝ≥0∞), F j = {z | r < edist z c ∧ edist z c < R}))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) = {z | ∀ j, z j ∈ F j}) (q : ℤ) (hq : 0 < q) :
    IsZero ((sheafCohomology ((Opens.toTopCat (TopCat.of (EuclideanSpace ℂ (Fin n)))).obj D) q).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' D)).obj
        (holomorphicSheafAb n))) :=
  isZero_sheafCohomology_of_dbar_exact D
    (exists_dbarSections_eq_of_dbarSections_eq_zero (MMP.Gaga.cauchyTransform_runge_montel.1 n))
    (exists_dbarSections_eq_of_isProductDomain D F hF hD) q hq

private lemma abs_sub_max_min_lt {a b x η : ℝ} (hab : a ≤ b) (h1 : a - η < x) (h2 : x < b + η)
    (hη : 0 < η) : |x - max a (min b x)| < η := by
  rw [abs_lt]
  constructor <;> simp only [max_def, min_def] <;> split_ifs <;> linarith

/-- A product of closed rectangles inside an open `W ⊆ ℂⁿ` has a neighbourhood inside `W` which
is a product of open rectangles. -/
private lemma exists_ioo_rectangles {n : ℕ} (a b c d : Fin n → ℝ)
    {W : Set (EuclideanSpace ℂ (Fin n))} (hW : IsOpen W)
    (hKW : {z : EuclideanSpace ℂ (Fin n) |
      ∀ j, z j ∈ Set.Icc (a j) (b j) ×ℂ Set.Icc (c j) (d j)} ⊆ W) :
    ∃ a' b' c' d' : Fin n → ℝ,
      {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ Set.Icc (a j) (b j) ×ℂ Set.Icc (c j) (d j)} ⊆
        {z | ∀ j, z j ∈ Set.Ioo (a' j) (b' j) ×ℂ Set.Ioo (c' j) (d' j)} ∧
      {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ Set.Ioo (a' j) (b' j) ×ℂ Set.Ioo (c' j) (d' j)}
        ⊆ W := by
  by_cases hne : ∀ j, a j ≤ b j ∧ c j ≤ d j
  swap
  · push Not at hne
    obtain ⟨j, hj⟩ := hne
    refine ⟨a, b, c, d, fun z hz => ?_, fun z hz => ?_⟩
    · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz j
      exact absurd (hj (h1.trans h2)) (not_lt.2 (h3.trans h4))
    · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz j
      exact absurd (hj (h1.trans h2).le) (not_lt.2 (h3.trans h4).le)
  let K' : Set (Fin n → ℂ) := Set.univ.pi fun j => Set.Icc (a j) (b j) ×ℂ Set.Icc (c j) (d j)
  have hK' : IsCompact K' := isCompact_univ_pi fun j => isCompact_Icc.reProdIm isCompact_Icc
  let W' : Set (Fin n → ℂ) := (fun y => (WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n))) ⁻¹' W
  have hW' : IsOpen W' := hW.preimage (PiLp.continuous_toLp 2 _)
  have hK'W' : K' ⊆ W' := fun y hy => hKW fun j => hy j (Set.mem_univ _)
  obtain ⟨δ, hδ, hth⟩ := hK'.exists_thickening_subset_open hW' hK'W'
  set η := δ / 3 with hη
  have hη0 : 0 < η := by positivity
  refine ⟨fun j => a j - η, fun j => b j + η, fun j => c j - η, fun j => d j + η,
    fun z hz j => ?_, fun z hz => ?_⟩
  · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz j
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · let p : Fin n → ℂ := fun j =>
      ⟨max (a j) (min (b j) (z j).re), max (c j) (min (d j) (z j).im)⟩
    have hp : p ∈ K' := fun j _ =>
      ⟨⟨le_max_left _ _, max_le (hne j).1 (min_le_left _ _)⟩,
        le_max_left _ _, max_le (hne j).2 (min_le_left _ _)⟩
    have hdist : dist (WithLp.ofLp z) p < δ := by
      rw [dist_pi_lt_iff hδ]
      intro j
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz j
      rw [dist_eq_norm]
      calc ‖z j - p j‖ ≤ |(z j - p j).re| + |(z j - p j).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ < η + η := by
            refine add_lt_add ?_ ?_
            · exact abs_sub_max_min_lt (hne j).1 h1 h2 hη0
            · exact abs_sub_max_min_lt (hne j).2 h3 h4 hη0
        _ < δ := by rw [hη]; linarith
    simpa [W'] using hth (Metric.mem_thickening_iff.2 ⟨p, hp, hdist⟩)

/-- The pullback of sheaves along a composition. -/
private noncomputable def pullbackCompIso {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullback AddCommGrpCat.{0} (f ≫ g) ≅
      TopCat.Sheaf.pullback AddCommGrpCat.{0} g ⋙ TopCat.Sheaf.pullback AddCommGrpCat.{0} f :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction _ (f ≫ g)).leftAdjointUniq
    ((TopCat.Sheaf.pullbackPushforwardAdjunction _ g).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction _ f))

/-- **Dolbeault vanishing on product domains.** Let `D ⊆ ℂⁿ` be a product of bounded open
rectangles, open discs (possibly `ℂ`) and open annuli. Then `H^q(D, 𝒪) = 0` for `q > 0`.
If `K ⊆ W` is a product of closed rectangles inside an open `W`, every class in
`H^q(W, 𝒪)`, `q > 0`, vanishes on some open product of bounded open rectangles `V` with
`K ⊆ V ⊆ W`. -/
@[mmp "lem_mmp_gaga_dolbeault_product_domains"]
public theorem isZero_sheafCohomology_holomorphic_of_isProductDomain (n : ℕ) :
    let E := TopCat.of (EuclideanSpace ℂ (Fin n))
    let O : TopCat.Sheaf AddCommGrpCat.{0} E :=
      (SheafOfModules.toSheaf _).obj
        (SheafOfModules.unit (holomorphicRingCatSheaf n (EuclideanSpace ℂ (Fin n))))
    (∀ (D : Opens E) (F : Fin n → Set ℂ),
      (∀ j, (∃ a b c d : ℝ, F j = Set.Ioo a b ×ℂ Set.Ioo c d) ∨
        (∃ (c : ℂ) (R : ℝ≥0∞), F j = Metric.eball c R) ∨
        (∃ (c : ℂ) (r R : ℝ≥0∞), F j = {z | r < edist z c ∧ edist z c < R})) →
      (D : Set (EuclideanSpace ℂ (Fin n))) = {z | ∀ j, z j ∈ F j} →
      ∀ q : ℤ, 0 < q →
        IsZero ((sheafCohomology ((Opens.toTopCat E).obj D) q).obj
          ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' D)).obj O))) ∧
    (∀ (a b c d : Fin n → ℝ) (W : Opens E),
      {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ Set.Icc (a j) (b j) ×ℂ Set.Icc (c j) (d j)} ⊆
        (W : Set (EuclideanSpace ℂ (Fin n))) →
      ∀ (q : ℤ), 0 < q →
      ∀ x : (sheafCohomology ((Opens.toTopCat E).obj W) q).obj
          ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' W)).obj O),
        ∃ (a' b' c' d' : Fin n → ℝ) (V : Opens E) (hVW : V ≤ W),
          (V : Set (EuclideanSpace ℂ (Fin n))) =
            {z | ∀ j, z j ∈ Set.Ioo (a' j) (b' j) ×ℂ Set.Ioo (c' j) (d' j)} ∧
          {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ Set.Icc (a j) (b j) ×ℂ Set.Icc (c j) (d j)} ⊆
            (V : Set (EuclideanSpace ℂ (Fin n))) ∧
          sheafCohomologyPullback ((Opens.toTopCat E).map (homOfLE hVW))
            ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' W)).obj O) q x = 0) := by
  intro E O
  refine ⟨isZero_sheafCohomology_of_isProductDomain, ?_⟩
  intro a b c d W hKW q hq x
  obtain ⟨a', b', c', d', hKV, hVW⟩ := exists_ioo_rectangles a b c d W.isOpen hKW
  have hVo : IsOpen {z : EuclideanSpace ℂ (Fin n) |
      ∀ j, z j ∈ Set.Ioo (a' j) (b' j) ×ℂ Set.Ioo (c' j) (d' j)} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j =>
      (isOpen_Ioo.reProdIm isOpen_Ioo).preimage
        (EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).continuous
  let V : Opens E := ⟨_, hVo⟩
  have hVW' : V ≤ W := hVW
  refine ⟨a', b', c', d', V, hVW', rfl, hKV, ?_⟩
  have hz := isZero_sheafCohomology_of_isProductDomain V
    (fun j => Set.Ioo (a' j) (b' j) ×ℂ Set.Ioo (c' j) (d' j))
    (fun j => Or.inl ⟨_, _, _, _, rfl⟩) rfl q hq
  exact (AddCommGrpCat.isZero_iff_subsingleton.1 (hz.of_iso
    ((sheafCohomology ((Opens.toTopCat E).obj V) q).mapIso
      ((pullbackCompIso ((Opens.toTopCat E).map (homOfLE hVW')) (Opens.inclusion' W)).app
        O).symm))).elim _ _

end Dolbeault

/-! ### Leray's theorem for acyclic covers -/

section Leray

attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

open CechCochains

section OrdMap

variable {T T' : TopCat.{u}} (f : T' ⟶ T) {I I' : Type u} [LinearOrder I] [LinearOrder I']
  (U : I → Opens T) (U' : I' → Opens T') (ρ : I' → I)
  (hle : ∀ i, U' i ≤ (Opens.map f).obj (U (ρ i)))

include hle in
private lemma inter_le_map_inter {p : ℕ} (J : Fin p → I') :
    inter U' J ≤ (Opens.map f).obj (inter U (ρ ∘ J)) := by
  intro x hx
  have hx' : x ∈ ((⨅ k, U' (J k) : Opens T') : Set T') := hx
  rw [Opens.coe_iInf, Set.mem_iInter] at hx'
  change f x ∈ ((⨅ k, U (ρ (J k)) : Opens T) : Set T)
  rw [Opens.coe_iInf, Set.mem_iInter]
  exact fun k => hle (J k) (hx' k)

variable {A : TopCat.Presheaf AddCommGrpCat.{u} T} {B : TopCat.Presheaf AddCommGrpCat.{u} T'}
  (ψ : A ⟶ (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj B)

private lemma app_restr {V W : Opens T} (i : W ≤ V) (x : A.obj (op V)) :
    (ψ.app (op W)).hom (restr A i x) =
      restr B ((Opens.map f).monotone i) ((ψ.app (op V)).hom x) :=
  ConcreteCategory.congr_hom (ψ.naturality (homOfLE i).op) x

/-- The ordered Čech cochain map attached to a monotone reindexing `ρ`, a cover comparison and a
map `ψ : A ⟶ f_* B`, on one cochain. -/
private noncomputable def ordMapFun (p : ℕ) (c : OrdCochain U A p) : OrdCochain U' B p :=
  fun J => if h : StrictMono (ρ ∘ J.1) then
    restr B (inter_le_map_inter f U U' ρ hle J.1)
      ((ψ.app (op (inter U (ρ ∘ J.1)))).hom (c ⟨ρ ∘ J.1, h⟩))
  else 0

private lemma ordMapFun_apply_of_strictMono (p : ℕ) (c : OrdCochain U A p)
    (J : OrdIndex (I := I') p) (h : StrictMono (ρ ∘ J.1)) :
    ordMapFun f U U' ρ hle ψ p c J = restr B (inter_le_map_inter f U U' ρ hle J.1)
      ((ψ.app (op (inter U (ρ ∘ J.1)))).hom (c ⟨ρ ∘ J.1, h⟩)) :=
  dif_pos h

private lemma ordMapFun_apply_of_not_strictMono (p : ℕ) (c : OrdCochain U A p)
    (J : OrdIndex (I := I') p) (h : ¬ StrictMono (ρ ∘ J.1)) :
    ordMapFun f U U' ρ hle ψ p c J = 0 :=
  dif_neg h

/-- The ordered Čech cochain map, as a group homomorphism. -/
private noncomputable def ordMap (p : ℕ) : OrdCochain U A p →+ OrdCochain U' B p where
  toFun := ordMapFun f U U' ρ hle ψ p
  map_zero' := by
    funext J
    by_cases h : StrictMono (ρ ∘ J.1) <;> simp [ordMapFun, h]
  map_add' c d := by
    funext J
    by_cases h : StrictMono (ρ ∘ J.1) <;> simp [ordMapFun, h]

private lemma restr_app_congr {p : ℕ} (c : OrdCochain U A p) {L₁ L₂ : Fin (p + 1) → I}
    (e : L₁ = L₂) (h₁ : StrictMono L₁) (h₂ : StrictMono L₂) {W : Opens T'}
    (w₁ : W ≤ (Opens.map f).obj (inter U L₁)) (w₂ : W ≤ (Opens.map f).obj (inter U L₂)) :
    restr B w₁ ((ψ.app (op (inter U L₁))).hom (c ⟨L₁, h₁⟩)) =
      restr B w₂ ((ψ.app (op (inter U L₂))).hom (c ⟨L₂, h₂⟩)) := by
  subst e
  rfl

/-- The value of `ordMapFun` on a tuple depends, after restriction, only on its image under `ρ`. -/
private lemma restr_ordMapFun_congr {p : ℕ} (c : OrdCochain U A p) {K₁ K₂ : OrdIndex (I := I') p}
    (e : ρ ∘ K₁.1 = ρ ∘ K₂.1) {W : Opens T'} (w₁ : W ≤ inter U' K₁.1) (w₂ : W ≤ inter U' K₂.1) :
    restr B w₁ (ordMapFun f U U' ρ hle ψ p c K₁) =
      restr B w₂ (ordMapFun f U U' ρ hle ψ p c K₂) := by
  by_cases h : StrictMono (ρ ∘ K₁.1)
  · rw [ordMapFun_apply_of_strictMono f U U' ρ hle ψ p c K₁ h,
      ordMapFun_apply_of_strictMono f U U' ρ hle ψ p c K₂ (e ▸ h), restr_restr, restr_restr]
    exact restr_app_congr f U ψ c e _ _ _ _
  · rw [ordMapFun_apply_of_not_strictMono f U U' ρ hle ψ p c K₁ h,
      ordMapFun_apply_of_not_strictMono f U U' ρ hle ψ p c K₂ (e ▸ h), map_zero, map_zero]

/-- The two faces of a tuple at the positions of a collapsed adjacent pair agree after `ρ`. -/
private lemma comp_succAbove_castSucc_eq {p : ℕ} (L : Fin (p + 2) → I) (m : Fin (p + 1))
    (hm : L m.castSucc = L m.succ) :
    L ∘ m.castSucc.succAbove = L ∘ m.succ.succAbove := by
  funext i
  simp only [Function.comp_apply, Fin.succAbove]
  rcases lt_trichotomy i m with h | rfl | h
  · have h1 : i.castSucc < m.castSucc := Fin.castSucc_lt_castSucc_iff.mpr h
    have h2 : i.castSucc < m.succ := Fin.castSucc_lt_succ_iff.mpr h.le
    rw [if_pos h1, if_pos h2]
  · rw [if_neg (lt_irrefl _), if_pos (Fin.castSucc_lt_succ_iff.mpr le_rfl)]
    exact hm.symm
  · have h1 : ¬ i.castSucc < m.castSucc := fun h' => (Fin.castSucc_lt_castSucc_iff.mp h').not_gt h
    have h2 : ¬ i.castSucc < m.succ := fun h' => (Fin.castSucc_lt_succ_iff.mp h').not_gt h
    rw [if_neg h1, if_neg h2]

include hle in
private lemma ordMap_ordD (hρ : Monotone ρ) (p : ℕ) (c : OrdCochain U A p) :
    ordMap f U U' ρ hle ψ (p + 1) (ordD U A p c) = ordD U' B p (ordMap f U U' ρ hle ψ p c) := by
  funext J
  change ordMapFun f U U' ρ hle ψ (p + 1) (ordD U A p c) J =
    ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      restr B (inter_le_omit U' J.1 j)
        (ordMapFun f U U' ρ hle ψ p c ⟨J.1 ∘ j.succAbove, strictMono_omit J.2 j⟩)
  by_cases h : StrictMono (ρ ∘ J.1)
  · rw [ordMapFun_apply_of_strictMono f U U' ρ hle ψ _ _ J h]
    change restr B _ ((ψ.app _).hom (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      restr A (inter_le_omit U (ρ ∘ J.1) j) (c ⟨(ρ ∘ J.1) ∘ j.succAbove, _⟩))) = _
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul, app_restr, restr_restr,
      ordMapFun_apply_of_strictMono f U U' ρ hle ψ _ _ _
        (show StrictMono (ρ ∘ (J.1 ∘ j.succAbove)) from h.comp (Fin.strictMono_succAbove j)),
      restr_restr]
    congr 1
  · rw [ordMapFun_apply_of_not_strictMono f U U' ρ hle ψ _ _ J h]
    have hmono : Monotone (ρ ∘ J.1) := hρ.comp J.2.monotone
    obtain ⟨m, hm⟩ : ∃ m : Fin (p + 1), ρ (J.1 m.castSucc) = ρ (J.1 m.succ) := by
      by_contra hne
      push Not at hne
      exact h (Fin.strictMono_iff_lt_succ.mpr fun m =>
        lt_of_le_of_ne (hmono (Fin.castSucc_lt_succ).le) (hne m))
    have hne : m.castSucc ≠ m.succ := (Fin.castSucc_lt_succ).ne
    rw [Finset.sum_eq_add m.castSucc m.succ hne ?_ (fun h' => absurd (Finset.mem_univ _) h')
      (fun h' => absurd (Finset.mem_univ _) h')]
    · rw [restr_ordMapFun_congr f U U' ρ hle ψ c (K₁ := ⟨_, strictMono_omit J.2 m.castSucc⟩)
        (K₂ := ⟨_, strictMono_omit J.2 m.succ⟩) (comp_succAbove_castSucc_eq (ρ ∘ J.1) m hm)
        (inter_le_omit U' J.1 m.castSucc) (inter_le_omit U' J.1 m.succ), Fin.val_succ,
        Fin.val_castSucc, pow_succ, mul_neg_one, neg_smul, add_neg_cancel]
    · intro k _ hk
      have hns : ¬ StrictMono (ρ ∘ (J.1 ∘ k.succAbove)) := by
        intro hs
        obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hk.1.symm
        obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hk.2.symm
        have hab : a < b := by
          rw [← (Fin.strictMono_succAbove k).lt_iff_lt, ha, hb]
          exact Fin.castSucc_lt_succ
        have := hs hab
        simp only [Function.comp_apply, ha, hb] at this
        exact (lt_irrefl _) (hm ▸ this)
      rw [ordMapFun_apply_of_not_strictMono f U U' ρ hle ψ _ _ _ hns, map_zero, smul_zero]

/-- The ordered Čech cochain map, as a map of complexes. -/
private noncomputable def ordChainMap (hρ : Monotone ρ) :
    Stacks.Cech.orderedCechComplex U A ⟶ Stacks.Cech.orderedCechComplex U' B where
  f p := AddCommGrpCat.ofHom (ordMap f U U' ρ hle ψ p)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [Stacks.Cech.orderedCechComplex_d, Stacks.Cech.orderedCechComplex_d]
    exact AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun c =>
      (ordMap_ordD f U U' ρ hle ψ hρ i c).symm

end OrdMap

section Functor

variable {T : TopCat.{u}} {I : Type u} [LinearOrder I] (U : I → Opens T)

/-- Postcomposition of ordered Čech cochains with a map of presheaves. -/
private noncomputable def ordPost {A A' : TopCat.Presheaf AddCommGrpCat.{u} T} (φ : A ⟶ A') :
    Stacks.Cech.orderedCechComplex U A ⟶ Stacks.Cech.orderedCechComplex U A' where
  f p := AddCommGrpCat.ofHom
    { toFun := fun c J => (φ.app _).hom (c J)
      map_zero' := funext fun J => map_zero _
      map_add' := fun c d => funext fun J => map_add _ _ _ }
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [Stacks.Cech.orderedCechComplex_d, Stacks.Cech.orderedCechComplex_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro c
    funext J
    change ∑ k : Fin (i + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      restr A' (inter_le_omit U J.1 k)
        ((φ.app _).hom (c ⟨J.1 ∘ k.succAbove, strictMono_omit J.2 k⟩))
      = (φ.app _).hom (∑ k : Fin (i + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      restr A (inter_le_omit U J.1 k) (c ⟨J.1 ∘ k.succAbove, strictMono_omit J.2 k⟩))
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    congr 1
    exact (ConcreteCategory.congr_hom (φ.naturality (homOfLE (inter_le_omit U J.1 k)).op) _).symm

/-- The ordered Čech complex, as a functor of the presheaf. -/
private noncomputable def ordCechFunctor :
    TopCat.Presheaf AddCommGrpCat.{u} T ⥤ CochainComplex AddCommGrpCat.{u} ℕ where
  obj A := Stacks.Cech.orderedCechComplex U A
  map φ := ordPost U φ
  map_id A := by
    ext p c
    rfl
  map_comp φ φ' := by
    ext p c
    rfl

private instance : (ordCechFunctor U).PreservesZeroMorphisms where
  map_zero A A' := by
    ext p c
    rfl

/-- The ordered Čech complex of the underlying presheaf, as a functor of the sheaf. -/
private noncomputable abbrev ordCechSheafFunctor :
    TopCat.Sheaf AddCommGrpCat.{u} T ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} ⋙ ordCechFunctor U

private instance : (ordCechSheafFunctor U).PreservesZeroMorphisms where
  map_zero A A' := by
    ext p c
    rfl

/-- The double complex `Č^p_<(U, K^q)` of a complex of sheaves; its `q`-th row is the ordered
Čech complex of `K^q`. -/
private noncomputable abbrev cechDouble (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ) :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ((ordCechSheafFunctor U).mapHomologicalComplex _).obj K

end Functor

section Augment

/-- Exactness of an augmented complex of abelian groups, checked on elements. -/
private lemma acyclic_augment {C : CochainComplex AddCommGrpCat.{u} ℕ} {X : AddCommGrpCat.{u}}
    (φ : X ⟶ C.X 0) (w : φ ≫ C.d 0 1 = 0) (h0 : Function.Injective φ)
    (h1 : ∀ x, C.d 0 1 x = 0 → ∃ y, φ y = x)
    (h2 : ∀ (p : ℕ) (x : C.X (p + 1)), C.d (p + 1) (p + 2) x = 0 → ∃ y, C.d p (p + 1) y = x) :
    (C.augment φ w).Acyclic := by
  intro n
  rcases n with _ | _ | n
  · rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp), ShortComplex.ab_exact_iff]
    intro x hx
    have hx0 : x = 0 := h0 (hx.trans (map_zero (ConcreteCategory.hom φ)).symm)
    exact ⟨0, by rw [hx0, map_zero]⟩
  · rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp), ShortComplex.ab_exact_iff]
    exact h1
  · rw [HomologicalComplex.exactAt_iff' _ (n + 1) (n + 2) (n + 3) (by simp) (by simp),
      ShortComplex.ab_exact_iff]
    exact h2 n

/-- Positive-degree exactness of a complex of abelian groups whose homology vanishes. -/
private lemma exists_d_eq_of_isZero_homology {C : CochainComplex AddCommGrpCat.{u} ℕ} (p : ℕ)
    (h : IsZero (C.homology (p + 1))) (x : C.X (p + 1)) (hx : C.d (p + 1) (p + 2) x = 0) :
    ∃ y, C.d p (p + 1) y = x := by
  have hex : C.ExactAt (p + 1) := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr h
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at hex
  exact hex x hx

end Augment

section Rows

variable {T : TopCat.{u}} {I : Type u} [LinearOrder I] (U : I → Opens T)

/-- The one-term tuple `(i)`. -/
private def singleIndex (i : I) : OrdIndex (I := I) 0 :=
  ⟨fun _ => i, fun a b h => by simp [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b] at h⟩

private lemma top_le_iSup_inter (hU : (⨆ i, U i) = ⊤) :
    ⊤ ≤ ⨆ j : OrdIndex (I := I) 0, inter U j.1 := by
  rw [← hU]
  exact iSup_le fun i => le_iSup_of_le (singleIndex i) (le_iInf fun _ => le_rfl)

/-- The restriction of global sections to the members of the cover. -/
private noncomputable def toOrdZero (F : TopCat.Presheaf AddCommGrpCat.{u} T) :
    F.obj (op ⊤) ⟶ (Stacks.Cech.orderedCechComplex U F).X 0 :=
  AddCommGrpCat.ofHom
    { toFun := fun s j => restr F le_top s
      map_zero' := funext fun j => map_zero _
      map_add' := fun s t => funext fun j => map_add _ _ _ }

private lemma toOrdZero_comp_d (F : TopCat.Presheaf AddCommGrpCat.{u} T) :
    toOrdZero U F ≫ (Stacks.Cech.orderedCechComplex U F).d 0 1 = 0 := by
  rw [Stacks.Cech.orderedCechComplex_d]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  funext J
  change ∑ k : Fin 2, ((-1 : ℤ) ^ (k : ℕ)) •
    restr F (inter_le_omit U J.1 k) (restr F le_top s) = 0
  rw [Fin.sum_univ_two, restr_restr, restr_restr]
  simp

private lemma restr_index_congr {F : TopCat.Presheaf AddCommGrpCat.{u} T} {p : ℕ}
    (c : OrdCochain U F p) {L₁ L₂ : Fin (p + 1) → I} (e : L₁ = L₂) (h₁ : StrictMono L₁)
    (h₂ : StrictMono L₂) {W : Opens T} (w₁ : W ≤ inter U L₁) (w₂ : W ≤ inter U L₂) :
    restr F w₁ (c ⟨L₁, h₁⟩) = restr F w₂ (c ⟨L₂, h₂⟩) := by
  subst e
  rfl

/-- A degree-zero ordered cocycle is compatible on an ordered pair of members of the cover. -/
private lemma restr_eq_of_ordD_eq_zero {F : TopCat.Presheaf AddCommGrpCat.{u} T}
    (c : OrdCochain U F 0) (hc : ordD U F 0 c = 0) (j k : OrdIndex (I := I) 0)
    (hjk : j.1 0 < k.1 0) {W : Opens T} (wj : W ≤ inter U j.1) (wk : W ≤ inter U k.1) :
    restr F wj (c j) = restr F wk (c k) := by
  let pair : Fin 2 → I := ![j.1 0, k.1 0]
  have hpair : StrictMono pair := Fin.strictMono_iff_lt_succ.mpr fun i => by
    rw [Fin.fin_one_eq_zero i]
    exact hjk
  have hZ : W ≤ inter U pair := by
    refine le_iInf fun t => ?_
    refine Fin.cases ?_ (fun t' => ?_) t
    · exact wj.trans (iInf_le _ 0)
    · rw [Fin.fin_one_eq_zero t']
      exact wk.trans (iInf_le _ 0)
  have e0 : pair ∘ (0 : Fin 2).succAbove = k.1 := by
    funext x
    rw [Fin.fin_one_eq_zero x]
    rfl
  have e1 : pair ∘ (1 : Fin 2).succAbove = j.1 := by
    funext x
    rw [Fin.fin_one_eq_zero x]
    rfl
  have h := congrFun hc ⟨pair, hpair⟩
  change ∑ t : Fin 2, ((-1 : ℤ) ^ (t : ℕ)) •
    restr F (inter_le_omit U pair t) (c ⟨pair ∘ t.succAbove, strictMono_omit hpair t⟩) = 0 at h
  rw [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    one_smul, add_neg_eq_zero] at h
  calc restr F wj (c j)
      = restr F (hZ.trans (inter_le_omit U pair 1))
          (c ⟨pair ∘ (1 : Fin 2).succAbove, strictMono_omit hpair 1⟩) :=
        restr_index_congr U c e1.symm j.2 _ _ _
    _ = restr F hZ (restr F (inter_le_omit U pair 1)
          (c ⟨pair ∘ (1 : Fin 2).succAbove, strictMono_omit hpair 1⟩)) := (restr_restr _ _ _ _).symm
    _ = restr F hZ (restr F (inter_le_omit U pair 0)
          (c ⟨pair ∘ (0 : Fin 2).succAbove, strictMono_omit hpair 0⟩)) := by rw [h]
    _ = restr F (hZ.trans (inter_le_omit U pair 0))
          (c ⟨pair ∘ (0 : Fin 2).succAbove, strictMono_omit hpair 0⟩) := restr_restr _ _ _ _
    _ = restr F wk (c k) :=
        restr_index_congr U c e0 _ k.2 _ _

private lemma ordIndex_zero_ext {j k : OrdIndex (I := I) 0} (h : j.1 0 = k.1 0) : j = k :=
  Subtype.ext <| funext fun x => by rwa [Fin.fin_one_eq_zero x]

/-- **Rows.** For a flasque sheaf and an open cover, the ordered Čech complex augmented by the
global sections is exact. -/
private lemma acyclic_augment_row (hU : (⨆ i, U i) = ⊤) (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    [F.IsFlasque] :
    ((Stacks.Cech.orderedCechComplex U F.obj).augment (toOrdZero U F.obj)
      (toOrdZero_comp_d U F.obj)).Acyclic := by
  refine acyclic_augment _ _ ?_ ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro s hs
    refine TopCat.Sheaf.eq_of_locally_eq' F (fun j : OrdIndex (I := I) 0 =>
      inter U j.1) ⊤ (fun j : OrdIndex (I := I) 0 =>
      (homOfLE le_top : inter U j.1 ⟶ ⊤)) (top_le_iSup_inter U hU) s 0 fun j => ?_
    rw [map_zero]
    exact congrFun hs j
  · intro x hx
    rw [Stacks.Cech.orderedCechComplex_d] at hx
    change ordD U F.obj 0 x = 0 at hx
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' F (fun j : OrdIndex (I := I) 0 =>
      inter U j.1) ⊤ (fun j => homOfLE le_top) (top_le_iSup_inter U hU) x (fun j k => by
        rcases lt_trichotomy (j.1 0) (k.1 0) with h | h | h
        · exact restr_eq_of_ordD_eq_zero U x hx j k h inf_le_left inf_le_right
        · obtain rfl := ordIndex_zero_ext h
          rfl
        · exact (restr_eq_of_ordD_eq_zero U x hx k j h inf_le_right inf_le_left).symm)
    exact ⟨s, funext hs⟩
  · intro p x hx
    have hz : IsZero ((Stacks.Cech.orderedCechComplex U F.obj).homology (p + 1)) :=
      (Stacks.Cech.isZero_alternatingCechComplex_homology_of_isFlasque U F (p + 1)
        (Nat.succ_pos p)).of_iso
        (HomologicalComplex.homologyMapIso (Stacks.Cech.orderedIsoAlternatingCechComplex U F.obj)
          (p + 1))
    exact exists_d_eq_of_isZero_homology p hz x hx

end Rows

section Columns

variable {T : TopCat.{u}}

attribute [local instance] globalSections_additive

/-- **Columns.** If `S` has no higher cohomology on `V`, the sections over `V` of an injective
resolution of `S` form a resolution of `S(V)`. -/
private lemma column_exact (V : Opens T) (S : TopCat.Sheaf AddCommGrpCat.{u} T)
    (J : InjectiveResolution S)
    (hV : ∀ q : ℤ, 0 < q → IsZero ((sheafCohomology ((Opens.toTopCat T).obj V) q).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' V)).obj S))) :
    Function.Injective ((sectionsOver V).map (J.ι.f 0)) ∧
    (∀ x, (sectionsOver V).map (J.cocomplex.d 0 1) x = 0 →
      ∃ y, (sectionsOver V).map (J.ι.f 0) y = x) ∧
    (∀ (q : ℕ) x, (sectionsOver V).map (J.cocomplex.d (q + 1) (q + 2)) x = 0 →
      ∃ y, (sectionsOver V).map (J.cocomplex.d q (q + 1)) y = x) := by
  let G := sectionsOver V
  have hex : (ShortComplex.mk _ _ J.ι_f_zero_comp_complex_d).Exact :=
    ShortComplex.exact_of_f_is_kernel _ J.isLimitKernelFork
  have hexG := hex.map_of_mono_of_preservesKernel G (inferInstance : Mono (J.ι.f 0))
    inferInstance
  refine ⟨(AddCommGrpCat.mono_iff_injective _).mp (G.map_mono (J.ι.f 0)),
    (ShortComplex.ab_exact_iff _).mp hexG, fun q x hx => ?_⟩
  let Vt := (Opens.toTopCat T).obj V
  let R := TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' V)
  have tkT := sheafCohomology_toolkit.{u, 0, 0, 0, 0} T
  have tk := sheafCohomology_toolkit.{u, 0, 0, 0, 0} Vt
  let A := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  let ι' : (CochainComplex.single₀ _).obj (R.obj S) ⟶ A :=
    (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℕ) 0).inv.app S ≫
      (R.mapHomologicalComplex _).map J.ι
  have hι' : QuasiIso ι' := by
    have := pullback_preservesHomology (Opens.inclusion' V)
    infer_instance
  have hacyc : ∀ (q n : ℕ), 0 < n →
      IsZero (((globalSections Vt).rightDerived n).obj (A.X q)) := fun q n hn =>
    tkT.1.2.2.2.2.2 (J.cocomplex.X q) (tkT.1.2.2.1 _ inferInstance) V n hn
  obtain ⟨e, -⟩ := tk.2.1.2.2.1 A ι' hι' hacyc (q + 1)
  have hR : IsZero (((globalSections Vt).rightDerived (q + 1)).obj (R.obj S)) :=
    (hV ((q + 1 : ℕ) : ℤ) (by omega)).of_iso ((sheafCohomologyIso Vt (q + 1)).app (R.obj S)).symm
  have hA : IsZero ((((globalSections Vt).mapHomologicalComplex _).obj A).homology (q + 1)) :=
    hR.of_iso e
  have hz : IsZero (((G.mapHomologicalComplex _).obj J.cocomplex).homology (q + 1)) :=
    hA.of_iso (HomologicalComplex.homologyMapIso
      ((NatIso.mapHomologicalComplex (sectionsPullbackIso V) (ComplexShape.up ℕ)).app
        J.cocomplex) (q + 1)).symm
  exact exists_d_eq_of_isZero_homology q hz x hx

end Columns

section Edge

variable {T : TopCat.{u}} {I : Type u} [LinearOrder I] (U : I → Opens T)
  {S : TopCat.Sheaf AddCommGrpCat.{u} T} (J : InjectiveResolution S)

/-- The augmentation `Γ(T, J^•) ⟶ Č^0_<(U, J^•)` of the Čech double complex. -/
private noncomputable def augRow :
    ((globalSections T).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex ⟶
      (cechDouble U J.cocomplex).flip.X 0 where
  f q := toOrdZero U (J.cocomplex.X q).obj
  comm' q q' _ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    funext j
    change ((J.cocomplex.d q q').hom.app (op (inter U j.1))).hom
        (restr (J.cocomplex.X q).obj le_top s) =
      restr (J.cocomplex.X q').obj le_top (((J.cocomplex.d q q').hom.app (op ⊤)).hom s)
    have h := ConcreteCategory.congr_hom ((J.cocomplex.d q q').hom.naturality
      (homOfLE (le_top : inter U j.1 ≤ ⊤)).op) s
    rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h

private lemma augRow_comp_d (q : ℕ) :
    (augRow U J).f q ≫ ((cechDouble U J.cocomplex).X q).d 0 1 = 0 :=
  toOrdZero_comp_d U (J.cocomplex.X q).obj

/-- The augmentation `Č^•_<(U, S) ⟶ Č^•_<(U, J^0)` of the Čech double complex. -/
private noncomputable def augCol :
    Stacks.Cech.orderedCechComplex U S.obj ⟶ (cechDouble U J.cocomplex).X 0 :=
  ordPost U (J.ι.f 0).hom

private lemma augCol_comp_d (p : ℕ) :
    (augCol U J).f p ≫ ((cechDouble U J.cocomplex).flip.X p).d 0 1 = 0 :=
  AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun c => funext fun j =>
    ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op (inter U j.1)))
      J.ι_f_zero_comp_complex_d) (c j)

variable {U} in
private lemma acyclic_augRow (hU : (⨆ i, U i) = ⊤) (q : ℕ) :
    (CochainComplex.augment ((cechDouble U J.cocomplex).X q) ((augRow U J).f q)
      (augRow_comp_d U J q)).Acyclic := by
  have : (J.cocomplex.X q).IsFlasque :=
    (sheafCohomology_toolkit.{u, 0, 0, 0, 0} T).1.2.2.1 _ inferInstance
  exact acyclic_augment_row U hU (J.cocomplex.X q)

variable {U} in
private lemma acyclic_augCol
    (hS : ∀ (p : ℕ) (K : OrdIndex (I := I) p) (q : ℤ), 0 < q →
      IsZero ((sheafCohomology ((Opens.toTopCat T).obj (inter U K.1)) q).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' (inter U K.1))).obj S)))
    (p : ℕ) :
    (CochainComplex.augment ((cechDouble U J.cocomplex).flip.X p) ((augCol U J).f p)
      (augCol_comp_d U J p)).Acyclic := by
  have hc := fun K : OrdIndex (I := I) p => column_exact (inter U K.1) S J (hS p K)
  refine acyclic_augment _ _ ?_ ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro c hc0
    funext K
    exact (hc K).1 ((congrFun hc0 K).trans (map_zero _).symm)
  · intro x hx
    exact ⟨fun K => ((hc K).2.1 (x K) (congrFun hx K)).choose,
      funext fun K => ((hc K).2.1 (x K) (congrFun hx K)).choose_spec⟩
  · intro q x hx
    exact ⟨fun K => ((hc K).2.2 q (x K) (congrFun hx K)).choose,
      funext fun K => ((hc K).2.2 q (x K) (congrFun hx K)).choose_spec⟩

variable {U} in
/-- The two edge quasi-isomorphisms into the total complex of the Čech double complex. -/
private lemma exists_edge (hU : (⨆ i, U i) = ⊤)
    (hS : ∀ (p : ℕ) (K : OrdIndex (I := I) p) (q : ℤ), 0 < q →
      IsZero ((sheafCohomology ((Opens.toTopCat T).obj (inter U K.1)) q).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' (inter U K.1))).obj S))) :
    (∃ fA : ((globalSections T).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex ⟶
        (cechDouble U J.cocomplex).total (ComplexShape.up ℕ),
      (∀ q, fA.f q = (augRow U J).f q ≫
        (cechDouble U J.cocomplex).ιTotal (ComplexShape.up ℕ) q 0 q (add_zero q)) ∧
      QuasiIso fA) ∧
    ∃ gB : Stacks.Cech.orderedCechComplex U S.obj ⟶
        (cechDouble U J.cocomplex).total (ComplexShape.up ℕ),
      (∀ p, gB.f p = (augCol U J).f p ≫
        (cechDouble U J.cocomplex).ιTotal (ComplexShape.up ℕ) 0 p p (zero_add p)) ∧
      QuasiIso gB :=
  MMP.Homology.exists_quasiIso_total_of_acyclic_augment (cechDouble U J.cocomplex) _ (augRow U J)
    (augRow_comp_d U J) (acyclic_augRow J hU) _ (augCol U J) (augCol_comp_d U J)
    (acyclic_augCol J hS)

end Edge

section Key

variable {T T' : TopCat.{u}} (f : T' ⟶ T) {I I' : Type u} [LinearOrder I] [LinearOrder I']
  {U : I → Opens T} {U' : I' → Opens T'} (ρ : I' → I) (hρ : Monotone ρ)
  (hle : ∀ i, U' i ≤ (Opens.map f).obj (U (ρ i)))
  {S : TopCat.Sheaf AddCommGrpCat.{u} T} {S' : TopCat.Sheaf AddCommGrpCat.{u} T'}
  (J : InjectiveResolution S) (J' : InjectiveResolution S')
  (g : J.cocomplex ⟶
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj J'.cocomplex)

/-- The map of Čech double complexes induced by a map `J^• ⟶ f_* J'^•`. -/
private noncomputable def cechDoubleMap :
    cechDouble U J.cocomplex ⟶ cechDouble U' J'.cocomplex where
  f q := ordChainMap f U U' ρ hle (g.f q).hom hρ
  comm' q q' _ := by
    ext p c
    funext K
    symm
    change ordMapFun f U U' ρ hle (g.f q').hom p
        (fun K => ((J.cocomplex.d q q').hom.app _).hom (c K)) K =
      ((J'.cocomplex.d q q').hom.app _).hom (ordMapFun f U U' ρ hle (g.f q).hom p c K)
    by_cases h : StrictMono (ρ ∘ K.1)
    · dsimp only [ordMapFun]
      rw [dif_pos h, dif_pos h]
      have h1 := ConcreteCategory.congr_hom ((J'.cocomplex.d q q').hom.naturality
        (homOfLE (inter_le_map_inter f U U' ρ hle K.1)).op)
        (((g.f q).hom.app (op (inter U (ρ ∘ K.1)))).hom (c ⟨ρ ∘ K.1, h⟩))
      have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op (inter U (ρ ∘ K.1))))
        (g.comm q q')) (c ⟨ρ ∘ K.1, h⟩)
      refine (congrArg (restr (J'.cocomplex.X q').obj (inter_le_map_inter f U U' ρ hle K.1))
        h2.symm).trans ?_
      exact h1.symm
    · dsimp only [ordMapFun]
      rw [dif_neg h, dif_neg h, map_zero]

private lemma augCol_comp_cechDoubleMap
    (ψ : S ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj S')
    (hg : J.ι.f 0 ≫ g.f 0 = ψ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J'.ι.f 0))
    (χ : Stacks.Cech.orderedCechComplex U S.obj ⟶ Stacks.Cech.orderedCechComplex U' S'.obj)
    (hχ₁ : ∀ (p : ℕ) (c : OrdCochain U S.obj p) (K : OrdIndex (I := I') p)
      (hK : StrictMono (ρ ∘ K.1)) (h : inter U' K.1 ≤ (Opens.map f).obj (inter U (ρ ∘ K.1))),
      ((χ.f p).hom c : OrdCochain U' S'.obj p) K = (S'.obj.map (homOfLE h).op).hom
        ((ψ.hom.app (op (inter U (ρ ∘ K.1)))).hom (c ⟨ρ ∘ K.1, hK⟩)))
    (hχ₀ : ∀ (p : ℕ) (c : OrdCochain U S.obj p) (K : OrdIndex (I := I') p),
      ¬ StrictMono (ρ ∘ K.1) → ((χ.f p).hom c : OrdCochain U' S'.obj p) K = 0)
    (p : ℕ) :
    (augCol U J).f p ≫ ((cechDoubleMap f ρ hρ hle J J' g).f 0).f p =
      χ.f p ≫ (augCol U' J').f p := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  funext K
  change ordMapFun f U U' ρ hle (g.f 0).hom p (fun K => ((J.ι.f 0).hom.app _).hom (c K)) K =
    ((J'.ι.f 0).hom.app _).hom (((χ.f p).hom c : OrdCochain U' S'.obj p) K)
  by_cases h : StrictMono (ρ ∘ K.1)
  · refine Eq.trans ?_ (congrArg ((J'.ι.f 0).hom.app _).hom
      (hχ₁ p c K h (inter_le_map_inter f U U' ρ hle K.1))).symm
    dsimp only [ordMapFun]
    rw [dif_pos h]
    have h1 := ConcreteCategory.congr_hom ((J'.ι.f 0).hom.naturality
      (homOfLE (inter_le_map_inter f U U' ρ hle K.1)).op)
      ((ψ.hom.app (op (inter U (ρ ∘ K.1)))).hom (c ⟨ρ ∘ K.1, h⟩))
    have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op (inter U (ρ ∘ K.1))))
      hg) (c ⟨ρ ∘ K.1, h⟩)
    refine (congrArg (restr (J'.cocomplex.X 0).obj (inter_le_map_inter f U U' ρ hle K.1))
      h2).trans ?_
    exact h1.symm
  · refine Eq.trans ?_ (congrArg ((J'.ι.f 0).hom.app _).hom (hχ₀ p c K h)).symm
    refine Eq.trans ?_ (map_zero _).symm
    dsimp only [ordMapFun]
    rw [dif_neg h]

private lemma augRow_comp_cechDoubleMap (q : ℕ) :
    (augRow U J).f q ≫ ((cechDoubleMap f ρ hρ hle J J' g).f q).f 0 =
      (((globalSections T).mapHomologicalComplex _).map g).f q ≫ (augRow U' J').f q := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  funext K
  have hK : StrictMono (ρ ∘ K.1) := fun a b hab => by
    simp [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b] at hab
  change ordMapFun f U U' ρ hle (g.f q).hom 0 (fun _ => restr (J.cocomplex.X q).obj le_top s) K =
    restr (J'.cocomplex.X q).obj le_top (((g.f q).hom.app (op ⊤)).hom s)
  dsimp only [ordMapFun]
  rw [dif_pos hK]
  have h1 := ConcreteCategory.congr_hom ((g.f q).hom.naturality
    (homOfLE (le_top : inter U (ρ ∘ K.1) ≤ ⊤)).op) s
  refine (congrArg (restr (J'.cocomplex.X q).obj (inter_le_map_inter f U U' ρ hle K.1))
    h1).trans ?_
  exact restr_restr _ _ _ _

set_option backward.isDefEq.respectTransparency false in
include hρ hle in
/-- **The key compatibility.** The map of ordered Čech complexes with the given formula and the map
`Γ(T, J^•) ⟶ Γ(T', J'^•)` correspond under the edge quasi-isomorphisms. -/
private theorem homologyMap_comp_edge
    (ψ : S ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj S')
    (hg : J.ι.f 0 ≫ g.f 0 = ψ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J'.ι.f 0))
    (χ : Stacks.Cech.orderedCechComplex U S.obj ⟶ Stacks.Cech.orderedCechComplex U' S'.obj)
    (hχ₁ : ∀ (p : ℕ) (c : OrdCochain U S.obj p) (K : OrdIndex (I := I') p)
      (hK : StrictMono (ρ ∘ K.1)) (h : inter U' K.1 ≤ (Opens.map f).obj (inter U (ρ ∘ K.1))),
      ((χ.f p).hom c : OrdCochain U' S'.obj p) K = (S'.obj.map (homOfLE h).op).hom
        ((ψ.hom.app (op (inter U (ρ ∘ K.1)))).hom (c ⟨ρ ∘ K.1, hK⟩)))
    (hχ₀ : ∀ (p : ℕ) (c : OrdCochain U S.obj p) (K : OrdIndex (I := I') p),
      ¬ StrictMono (ρ ∘ K.1) → ((χ.f p).hom c : OrdCochain U' S'.obj p) K = 0)
    (fA : ((globalSections T).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex ⟶
        (cechDouble U J.cocomplex).total (ComplexShape.up ℕ))
    (gB : Stacks.Cech.orderedCechComplex U S.obj ⟶
        (cechDouble U J.cocomplex).total (ComplexShape.up ℕ))
    (hfA : ∀ q, fA.f q = (augRow U J).f q ≫
        (cechDouble U J.cocomplex).ιTotal (ComplexShape.up ℕ) q 0 q (add_zero q))
    (hgB : ∀ p, gB.f p = (augCol U J).f p ≫
        (cechDouble U J.cocomplex).ιTotal (ComplexShape.up ℕ) 0 p p (zero_add p))
    (fA' : ((globalSections T').mapHomologicalComplex (ComplexShape.up ℕ)).obj J'.cocomplex ⟶
        (cechDouble U' J'.cocomplex).total (ComplexShape.up ℕ))
    (gB' : Stacks.Cech.orderedCechComplex U' S'.obj ⟶
        (cechDouble U' J'.cocomplex).total (ComplexShape.up ℕ))
    (hfA' : ∀ q, fA'.f q = (augRow U' J').f q ≫
        (cechDouble U' J'.cocomplex).ιTotal (ComplexShape.up ℕ) q 0 q (add_zero q))
    (hgB' : ∀ p, gB'.f p = (augCol U' J').f p ≫
        (cechDouble U' J'.cocomplex).ιTotal (ComplexShape.up ℕ) 0 p p (zero_add p))
    (hqA : QuasiIso fA) (hqA' : QuasiIso fA') (n : ℕ) :
    HomologicalComplex.homologyMap χ n ≫ HomologicalComplex.homologyMap gB' n ≫
        inv (HomologicalComplex.homologyMap fA' n) =
      HomologicalComplex.homologyMap gB n ≫ inv (HomologicalComplex.homologyMap fA n) ≫
        HomologicalComplex.homologyMap (((globalSections T).mapHomologicalComplex _).map g) n := by
  let TM := HomologicalComplex₂.total.map (cechDoubleMap f ρ hρ hle J J' g) (ComplexShape.up ℕ)
  have h1 : gB ≫ TM = χ ≫ gB' := by
    ext p : 1
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hgB, hgB', Category.assoc,
      HomologicalComplex₂.ιTotal_map, ← Category.assoc,
      augCol_comp_cechDoubleMap f ρ hρ hle J J' g ψ hg χ hχ₁ hχ₀ p, Category.assoc]
  have h2 : fA ≫ TM = ((globalSections T).mapHomologicalComplex _).map g ≫ fA' := by
    ext q : 1
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hfA, hfA', Category.assoc,
      HomologicalComplex₂.ιTotal_map, ← Category.assoc,
      augRow_comp_cechDoubleMap f ρ hρ hle J J' g q, Category.assoc]
  have H1 := congrArg (fun φ => HomologicalComplex.homologyMap φ n) h1
  have H2 := congrArg (fun φ => HomologicalComplex.homologyMap φ n) h2
  simp only [HomologicalComplex.homologyMap_comp] at H1 H2
  rw [← Category.assoc, ← H1, Category.assoc]
  congr 1
  rw [IsIso.eq_inv_comp, ← Category.assoc, H2, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end Key

section Iso

attribute [local instance] globalSections_additive

variable {T : TopCat.{u}} {I : Type u} [LinearOrder I] {U : I → Opens T}
  {S : TopCat.Sheaf AddCommGrpCat.{u} T} (J : InjectiveResolution S) (hU : (⨆ i, U i) = ⊤)
  (hS : ∀ (p : ℕ) (K : OrdIndex (I := I) p) (q : ℤ), 0 < q →
      IsZero ((sheafCohomology ((Opens.toTopCat T).obj (inter U K.1)) q).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' (inter U K.1))).obj S)))

/-- The edge map from `Γ(T, J^•)`. -/
private noncomputable def edgeA :
    ((globalSections T).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex ⟶
      (cechDouble U J.cocomplex).total (ComplexShape.up ℕ) :=
  (exists_edge J hU hS).1.choose

/-- The edge map from the ordered Čech complex. -/
private noncomputable def edgeB :
    Stacks.Cech.orderedCechComplex U S.obj ⟶
      (cechDouble U J.cocomplex).total (ComplexShape.up ℕ) :=
  (exists_edge J hU hS).2.choose

private lemma edgeA_f (q : ℕ) : (edgeA J hU hS).f q = (augRow U J).f q ≫
    (cechDouble U J.cocomplex).ιTotal (ComplexShape.up ℕ) q 0 q (add_zero q) :=
  (exists_edge J hU hS).1.choose_spec.1 q

private lemma edgeA_quasiIso : QuasiIso (edgeA J hU hS) :=
  (exists_edge J hU hS).1.choose_spec.2

private lemma edgeB_f (p : ℕ) : (edgeB J hU hS).f p = (augCol U J).f p ≫
    (cechDouble U J.cocomplex).ιTotal (ComplexShape.up ℕ) 0 p p (zero_add p) :=
  (exists_edge J hU hS).2.choose_spec.1 p

private lemma edgeB_quasiIso : QuasiIso (edgeB J hU hS) :=
  (exists_edge J hU hS).2.choose_spec.2

/-- The cohomology of the ordered Čech complex is that of `Γ(T, J^•)`. -/
private noncomputable def cechIso (n : ℕ) :
    (Stacks.Cech.orderedCechComplex U S.obj).homology n ≅
      (((globalSections T).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).homology n :=
  have := edgeA_quasiIso J hU hS
  have := edgeB_quasiIso J hU hS
  asIso (HomologicalComplex.homologyMap (edgeB J hU hS) n) ≪≫
    (asIso (HomologicalComplex.homologyMap (edgeA J hU hS) n)).symm

private lemma cechIso_hom (n : ℕ) : (cechIso J hU hS n).hom =
    HomologicalComplex.homologyMap (edgeB J hU hS) n ≫
      (have := edgeA_quasiIso J hU hS
       inv (HomologicalComplex.homologyMap (edgeA J hU hS) n)) := rfl

/-- The Leray isomorphism. -/
private noncomputable def lerayIso (n : ℕ) :
    (Stacks.Cech.orderedCechComplex U S.obj).homology n ≅ (sheafCohomology T n).obj S :=
  cechIso (injectiveResolution S) hU hS n ≪≫
    ((injectiveResolution S).isoRightDerivedObj (globalSections T) n).symm ≪≫
    ((sheafCohomologyIso T n).app S).symm

private lemma lerayIso_hom (n : ℕ) : (lerayIso hU hS n).hom =
    (cechIso (injectiveResolution S) hU hS n).hom ≫
      ((injectiveResolution S).isoRightDerivedObj (globalSections T) n).inv ≫
      (sheafCohomologyIso T n).inv.app S := rfl

end Iso

private lemma restr_self {T : TopCat.{u}} (F : TopCat.Presheaf AddCommGrpCat.{u} T) {V : Opens T}
    (x : F.obj (op V)) : restr F (le_refl V) x = x := by
  change (F.map (𝟙 (op V))).hom x = x
  rw [F.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] globalSections_additive in
private theorem leray_naturality_sheaf (I : Type u) [LinearOrder I] (T : TopCat.{u})
    (U : I → Opens T) (hU : (⨆ i, U i) = ⊤) (S S₂ : TopCat.Sheaf AddCommGrpCat.{u} T)
    (hS : ∀ (p : ℕ) (K : OrdIndex (I := I) p) (q : ℤ), 0 < q →
      IsZero ((sheafCohomology ((Opens.toTopCat T).obj (inter U K.1)) q).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' (inter U K.1))).obj S)))
    (hS₂ : ∀ (p : ℕ) (K : OrdIndex (I := I) p) (q : ℤ), 0 < q →
      IsZero ((sheafCohomology ((Opens.toTopCat T).obj (inter U K.1)) q).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' (inter U K.1))).obj S₂)))
    (φ : S ⟶ S₂)
    (χ : Stacks.Cech.orderedCechComplex U S.obj ⟶ Stacks.Cech.orderedCechComplex U S₂.obj)
    (hχ : ∀ (p : ℕ) (c : OrdCochain U S.obj p) (K : OrdIndex (I := I) p),
      ((χ.f p).hom c : OrdCochain U S₂.obj p) K = (φ.hom.app (op (inter U K.1))).hom (c K))
    (n : ℕ) :
    HomologicalComplex.homologyMap χ n ≫ (lerayIso hU hS₂ n).hom =
      (lerayIso hU hS n).hom ≫ (sheafCohomology T n).map φ := by
  let J := injectiveResolution S
  let J₂ := injectiveResolution S₂
  let g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 T)).mapHomologicalComplex
      _).obj J₂.cocomplex := InjectiveResolution.desc φ J₂ J
  have hg : J.ι.f 0 ≫ g.f 0 = (φ : S ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 T)).obj S₂) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 T)).map (J₂.ι.f 0) := by
    have h := congrArg (fun t => HomologicalComplex.Hom.f t 0)
      (InjectiveResolution.desc_commutes φ J₂ J)
    simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] at h
    exact h
  have key := homologyMap_comp_edge (𝟙 T) id monotone_id (fun i => le_rfl) J J₂ g φ hg χ
    (fun p c K hK h => (hχ p c K).trans (restr_self _ _).symm)
    (fun p c K hK => absurd K.2 hK)
    (edgeA J hU hS) (edgeB J hU hS) (edgeA_f J hU hS) (edgeB_f J hU hS)
    (edgeA J₂ hU hS₂) (edgeB J₂ hU hS₂) (edgeA_f J₂ hU hS₂) (edgeB_f J₂ hU hS₂)
    (edgeA_quasiIso J hU hS) (edgeA_quasiIso J₂ hU hS₂) n
  have hR := Functor.rightDerived_map_eq (globalSections T) n φ (P := J) (Q := J₂)
    (InjectiveResolution.desc φ J₂ J) (InjectiveResolution.desc_commutes φ J₂ J)
  have hE := (sheafCohomologyIso T n).inv.naturality φ
  rw [lerayIso_hom, lerayIso_hom, cechIso_hom, cechIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% key, ← hE, hR]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] globalSections_additive in
private theorem leray_naturality_refinement (I I' : Type u) [LinearOrder I] [LinearOrder I']
    (T : TopCat.{u}) (U : I → Opens T) (U' : I' → Opens T) (hU : (⨆ i, U i) = ⊤)
    (hU' : (⨆ i, U' i) = ⊤) (ρ : I' → I) (hρ : Monotone ρ) (hle : ∀ i, U' i ≤ U (ρ i))
    (S : TopCat.Sheaf AddCommGrpCat.{u} T)
    (hS : ∀ (p : ℕ) (K : OrdIndex (I := I) p) (q : ℤ), 0 < q →
      IsZero ((sheafCohomology ((Opens.toTopCat T).obj (inter U K.1)) q).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' (inter U K.1))).obj S)))
    (hS' : ∀ (p : ℕ) (K : OrdIndex (I := I') p) (q : ℤ), 0 < q →
      IsZero ((sheafCohomology ((Opens.toTopCat T).obj (inter U' K.1)) q).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' (inter U' K.1))).obj S)))
    (χ : Stacks.Cech.orderedCechComplex U S.obj ⟶ Stacks.Cech.orderedCechComplex U' S.obj)
    (hχ₁ : ∀ (p : ℕ) (c : OrdCochain U S.obj p) (K : OrdIndex (I := I') p)
      (hK : StrictMono (ρ ∘ K.1)) (h : inter U' K.1 ≤ inter U (ρ ∘ K.1)),
      ((χ.f p).hom c : OrdCochain U' S.obj p) K = (S.obj.map (homOfLE h).op).hom (c ⟨ρ ∘ K.1, hK⟩))
    (hχ₀ : ∀ (p : ℕ) (c : OrdCochain U S.obj p) (K : OrdIndex (I := I') p),
      ¬ StrictMono (ρ ∘ K.1) → ((χ.f p).hom c : OrdCochain U' S.obj p) K = 0)
    (n : ℕ) :
    HomologicalComplex.homologyMap χ n ≫ (lerayIso hU' hS' n).hom = (lerayIso hU hS n).hom := by
  let J := injectiveResolution S
  let g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 T)).mapHomologicalComplex
      _).obj J.cocomplex := 𝟙 J.cocomplex
  have hg : J.ι.f 0 ≫ g.f 0 = (𝟙 S : S ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 T)).obj S) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 T)).map (J.ι.f 0) := by
    change J.ι.f 0 ≫ 𝟙 _ = 𝟙 _ ≫ J.ι.f 0
    rw [Category.comp_id, Category.id_comp]
  have key := homologyMap_comp_edge (𝟙 T) ρ hρ hle J J g (𝟙 S) hg χ
    (fun p c K hK h => hχ₁ p c K hK h) hχ₀
    (edgeA J hU hS) (edgeB J hU hS) (edgeA_f J hU hS) (edgeB_f J hU hS)
    (edgeA J hU' hS') (edgeB J hU' hS') (edgeA_f J hU' hS') (edgeB_f J hU' hS')
    (edgeA_quasiIso J hU hS) (edgeA_quasiIso J hU' hS') n
  have hid : HomologicalComplex.homologyMap
      (((globalSections T).mapHomologicalComplex (ComplexShape.up ℕ)).map g) n = 𝟙 _ := by
    change HomologicalComplex.homologyMap
      (((globalSections T).mapHomologicalComplex (ComplexShape.up ℕ)).map (𝟙 J.cocomplex)) n = _
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  rw [lerayIso_hom, lerayIso_hom, cechIso_hom, cechIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% key, hid, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] globalSections_additive in
private theorem leray_pullback (I : Type u) [LinearOrder I] (T T' : TopCat.{u}) (f : T' ⟶ T)
    (U : I → Opens T) (U' : I → Opens T') (hU : (⨆ i, U i) = ⊤) (hU' : (⨆ i, U' i) = ⊤)
    (hle : ∀ i, U' i ≤ (Opens.map f).obj (U i))
    (S : TopCat.Sheaf AddCommGrpCat.{u} T) (S' : TopCat.Sheaf AddCommGrpCat.{u} T')
    (hS : ∀ (p : ℕ) (K : OrdIndex (I := I) p) (q : ℤ), 0 < q →
      IsZero ((sheafCohomology ((Opens.toTopCat T).obj (inter U K.1)) q).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' (inter U K.1))).obj S)))
    (hS' : ∀ (p : ℕ) (K : OrdIndex (I := I) p) (q : ℤ), 0 < q →
      IsZero ((sheafCohomology ((Opens.toTopCat T').obj (inter U' K.1)) q).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Opens.inclusion' (inter U' K.1))).obj S')))
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj S ⟶ S')
    (χ : Stacks.Cech.orderedCechComplex U S.obj ⟶ Stacks.Cech.orderedCechComplex U' S'.obj)
    (hχ : ∀ (p : ℕ) (c : OrdCochain U S.obj p) (K : OrdIndex (I := I) p)
      (h : inter U' K.1 ≤ (Opens.map f).obj (inter U K.1)),
      ((χ.f p).hom c : OrdCochain U' S'.obj p) K =
        (S'.obj.map (homOfLE h).op).hom
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv
            S S' θ).hom.app (op (inter U K.1))).hom (c K)))
    (n : ℕ) :
    (lerayIso hU hS n).hom ≫ sheafCohomologyPullback f S n ≫ (sheafCohomology T' n).map θ =
      HomologicalComplex.homologyMap χ n ≫ (lerayIso hU' hS' n).hom := by
  let J := injectiveResolution S
  let J' := injectiveResolution S'
  let P := TopCat.Sheaf.pullback AddCommGrpCat.{u} f
  let Q := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f
  let A := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  let ι' : (CochainComplex.single₀ _).obj (P.obj S) ⟶ A :=
    (HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℕ) 0).inv.app S ≫
      (P.mapHomologicalComplex _).map J.ι
  have hι' : QuasiIso ι' := by
    have := pullback_preservesHomology f
    infer_instance
  obtain ⟨g', hg'⟩ := (sheafCohomology_toolkit.{u, 0, 0, 0, 0} T').2.1.1 θ A ι' hι' J'
  let g : J.cocomplex ⟶ (Q.mapHomologicalComplex _).obj J'.cocomplex :=
    { f := fun q => adj.unit.app (J.cocomplex.X q) ≫ Q.map (g'.f q)
      comm' := fun q q' _ => by
        have h1 := adj.unit.naturality (J.cocomplex.d q q')
        have h2 := g'.comm q q'
        simp only [Functor.id_map, Functor.comp_map] at h1
        change (adj.unit.app (J.cocomplex.X q) ≫ Q.map (g'.f q)) ≫ Q.map (J'.cocomplex.d q q') =
          J.cocomplex.d q q' ≫ adj.unit.app (J.cocomplex.X q') ≫ Q.map (g'.f q')
        rw [Category.assoc, ← Functor.map_comp, h2, ← Category.assoc, h1]
        change _ = (adj.unit.app (J.cocomplex.X q) ≫ Q.map (P.map (J.cocomplex.d q q'))) ≫ _
        rw [Category.assoc, ← Functor.map_comp]
        rfl }
  have h0 : P.map (J.ι.f 0) ≫ g'.f 0 = θ ≫ J'.ι.f 0 := by
    have h := congrArg (fun t => HomologicalComplex.Hom.f t 0) hg'
    simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero, ι',
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      Functor.mapHomologicalComplex_map_f, Category.assoc] at h
    dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq] at h
    simp only [CategoryTheory.Functor.map_id] at h
    exact (Category.id_comp _).symm.trans h
  have hg : J.ι.f 0 ≫ g.f 0 =
      (adj.unit.app S ≫ Q.map θ) ≫ Q.map (J'.ι.f 0) := by
    change J.ι.f 0 ≫ adj.unit.app (J.cocomplex.X 0) ≫ Q.map (g'.f 0) = _
    have h1 := adj.unit.naturality (J.ι.f 0)
    simp only [Functor.id_map, Functor.comp_map] at h1
    rw [← Category.assoc]
    erw [h1]
    rw [Category.assoc, ← Functor.map_comp, h0, Functor.map_comp, Category.assoc]
    rfl
  have hgK : J.ι.f 0 ≫ g.f 0 = (adj.homEquiv S S' θ) ≫ Q.map (J'.ι.f 0) := by
    rw [Adjunction.homEquiv_unit]
    exact hg
  have key := homologyMap_comp_edge f id monotone_id hle J J' g (adj.homEquiv S S' θ) hgK χ
    (fun p c K hK h => hχ p c K h) (fun p c K hK => absurd K.2 hK)
    (edgeA J hU hS) (edgeB J hU hS) (edgeA_f J hU hS) (edgeB_f J hU hS)
    (edgeA J' hU' hS') (edgeB J' hU' hS') (edgeA_f J' hU' hS') (edgeB_f J' hU' hS')
    (edgeA_quasiIso J hU hS) (edgeA_quasiIso J' hU' hS') n
  have tk := sheafCohomologyIso_pullback f S S' θ J J' g hg n
  have tk2 : sheafCohomologyPullback f S n ≫ (sheafCohomology T' n).map θ =
      (sheafCohomologyIso T n).hom.app S ≫ (J.isoRightDerivedObj (globalSections T) n).hom ≫
        HomologicalComplex.homologyMap
          (((globalSections T).mapHomologicalComplex _).map g) n ≫
        (J'.isoRightDerivedObj (globalSections T') n).inv ≫
        (sheafCohomologyIso T' n).inv.app S' := by
    haveI : Mono ((sheafCohomologyIso T' n).hom.app S') :=
      IsIso.mono_of_iso ((sheafCohomologyIso T' n).app S').hom
    rw [← cancel_mono ((sheafCohomologyIso T' n).hom.app S'), Category.assoc, tk]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [lerayIso_hom, lerayIso_hom, cechIso_hom, cechIso_hom]
  simp only [Category.assoc]
  rw [tk2, reassoc_of% key]
  erw [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_assoc]

/-- **Leray's theorem for ordered Čech complexes.** Let `S` be a sheaf of abelian groups on
`T` with no higher cohomology on any finite intersection of members of an open cover `U`
indexed by a linearly ordered set. Then the cohomology of the ordered Čech complex
`Stacks.Cech.orderedCechComplex U S` is `sheafCohomology T n` of `S`. The family of these
isomorphisms is compatible with maps of sheaves, with monotone refinements of covers, and with
pullback along continuous maps followed by a map `f⁻¹ S ⟶ S'`. -/
@[mmp "lem_mmp_gaga_leray_acyclic_cover"]
public theorem exists_orderedCechComplex_homologyIso_sheafCohomology :
    ∃ e : ∀ (I : Type u) [LinearOrder I] (T : TopCat.{u}) (U : I → Opens T)
        (S : TopCat.Sheaf AddCommGrpCat.{u} T), (⨆ i, U i) = ⊤ →
        (∀ (p : ℕ) (J : CechCochains.OrdIndex (I := I) p) (q : ℤ), 0 < q →
          IsZero ((sheafCohomology ((Opens.toTopCat T).obj (CechCochains.inter U J.1)) q).obj
            ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
              (Opens.inclusion' (CechCochains.inter U J.1))).obj S))) →
        ∀ n : ℕ, (Stacks.Cech.orderedCechComplex U S.obj).homology n ≅
          (sheafCohomology T n).obj S,
      -- naturality in the sheaf
      (∀ (I : Type u) [LinearOrder I] (T : TopCat.{u}) (U : I → Opens T)
        (hU : (⨆ i, U i) = ⊤) (S S₂ : TopCat.Sheaf AddCommGrpCat.{u} T) (hS) (hS₂)
        (φ : S ⟶ S₂)
        (χ : Stacks.Cech.orderedCechComplex U S.obj ⟶ Stacks.Cech.orderedCechComplex U S₂.obj),
        (∀ (p : ℕ) (c : CechCochains.OrdCochain U S.obj p) (J : CechCochains.OrdIndex (I := I) p),
          ((χ.f p).hom c : CechCochains.OrdCochain U S₂.obj p) J =
            (φ.hom.app (op (CechCochains.inter U J.1))).hom (c J)) →
        ∀ n : ℕ, HomologicalComplex.homologyMap χ n ≫ (e I T U S₂ hU hS₂ n).hom =
          (e I T U S hU hS n).hom ≫ (sheafCohomology T n).map φ) ∧
      -- naturality for monotone refinements
      (∀ (I I' : Type u) [LinearOrder I] [LinearOrder I'] (T : TopCat.{u}) (U : I → Opens T)
        (U' : I' → Opens T) (hU : (⨆ i, U i) = ⊤) (hU' : (⨆ i, U' i) = ⊤)
        (ρ : I' → I) (_ : Monotone ρ) (_ : ∀ i, U' i ≤ U (ρ i))
        (S : TopCat.Sheaf AddCommGrpCat.{u} T) (hS) (hS')
        (χ : Stacks.Cech.orderedCechComplex U S.obj ⟶ Stacks.Cech.orderedCechComplex U' S.obj),
        (∀ (p : ℕ) (c : CechCochains.OrdCochain U S.obj p)
          (J : CechCochains.OrdIndex (I := I') p) (hJ : StrictMono (ρ ∘ J.1))
          (h : CechCochains.inter U' J.1 ≤ CechCochains.inter U (ρ ∘ J.1)),
          ((χ.f p).hom c : CechCochains.OrdCochain U' S.obj p) J =
            (S.obj.map (homOfLE h).op).hom (c ⟨ρ ∘ J.1, hJ⟩)) →
        (∀ (p : ℕ) (c : CechCochains.OrdCochain U S.obj p)
          (J : CechCochains.OrdIndex (I := I') p), ¬ StrictMono (ρ ∘ J.1) →
          ((χ.f p).hom c : CechCochains.OrdCochain U' S.obj p) J = 0) →
        ∀ n : ℕ, HomologicalComplex.homologyMap χ n ≫ (e I' T U' S hU' hS' n).hom =
          (e I T U S hU hS n).hom) ∧
      -- compatibility with pullback along a continuous map
      (∀ (I : Type u) [LinearOrder I] (T T' : TopCat.{u}) (f : T' ⟶ T) (U : I → Opens T)
        (U' : I → Opens T') (hU : (⨆ i, U i) = ⊤) (hU' : (⨆ i, U' i) = ⊤)
        (_ : ∀ i, U' i ≤ (Opens.map f).obj (U i))
        (S : TopCat.Sheaf AddCommGrpCat.{u} T) (S' : TopCat.Sheaf AddCommGrpCat.{u} T')
        (hS) (hS') (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj S ⟶ S')
        (χ : Stacks.Cech.orderedCechComplex U S.obj ⟶ Stacks.Cech.orderedCechComplex U' S'.obj),
        (∀ (p : ℕ) (c : CechCochains.OrdCochain U S.obj p) (J : CechCochains.OrdIndex (I := I) p)
          (h : CechCochains.inter U' J.1 ≤ (Opens.map f).obj (CechCochains.inter U J.1)),
          ((χ.f p).hom c : CechCochains.OrdCochain U' S'.obj p) J =
            (S'.obj.map (homOfLE h).op).hom
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv
                S S' θ).hom.app (op (CechCochains.inter U J.1))).hom (c J))) →
        ∀ n : ℕ, (e I T U S hU hS n).hom ≫ sheafCohomologyPullback f S n ≫
            (sheafCohomology T' n).map θ =
          HomologicalComplex.homologyMap χ n ≫ (e I T' U' S' hU' hS' n).hom) :=
  ⟨fun _ _ _ _ _ hU hS n => lerayIso hU hS n, leray_naturality_sheaf,
    leray_naturality_refinement, leray_pullback⟩

end Leray

/-! ### Resolutions of coherent sheaves on `ℙᴺ_ℂ` -/

section ProjectiveSpaceResolutions

open AlgebraicGeometry MvPolynomial Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistGrading integerGrading)
open scoped Stacks.GradedLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

variable {N : ℕ}

local notation "R" N => MvPolynomial (Fin (N + 1)) ℂ
local notation "𝒮" N => Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N

/-- A polynomial which is homogeneous of integer degree `n` for the unit weights lies in the
degree `n` part of the grading extended by zero. -/
private theorem mem_integerGrading_of_mem {p : R N} {n : ℤ}
    (h : p ∈ weightedHomogeneousSubmodule ℂ (fun _ : Fin (N + 1) ↦ (1 : ℤ)) n) :
    p ∈ integerGrading (𝒮 N) n := by
  have hw : ∀ m : Fin (N + 1) →₀ ℕ,
      Finsupp.weight (fun _ : Fin (N + 1) ↦ (1 : ℤ)) m =
        ((Finsupp.weight (1 : Fin (N + 1) → ℕ) m : ℕ) : ℤ) := by
    intro m
    simp [Finsupp.weight_apply, Finsupp.sum]
  by_cases hn : 0 ≤ n
  · simp only [integerGrading, hn, if_true,
      AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_homogeneousSubmodule, mem_homogeneousSubmodule]
    intro m hm
    have := h hm
    rw [hw] at this
    omega
  · simp only [integerGrading, hn, if_false, Submodule.mem_bot]
    ext m
    by_contra hm
    have := h (by simpa using hm)
    rw [hw] at this
    omega

/-- The degree `e` part of `⊕ⱼ S(-dⱼ)` on `Fin r → S`: the vectors whose `j`-th entry lies in
degree `e - dⱼ`. -/
private def freeGrade {r : ℕ} (d : Fin r → ℤ) (e : ℤ) : AddSubgroup (Fin r → R N) :=
  AddSubgroup.pi Set.univ fun j => (twistGrading (𝒮 N) (-d j) e).toAddSubgroup

private theorem mem_freeGrade {r : ℕ} {d : Fin r → ℤ} {e : ℤ} {v : Fin r → R N} :
    v ∈ freeGrade d e ↔ ∀ j, v j ∈ integerGrading (𝒮 N) (e - d j) := by
  simp [freeGrade, AddSubgroup.mem_pi, sub_eq_add_neg]

/-- The inclusion of the `j`-th summand in degree `e`. -/
private def singleGrade {r : ℕ} (d : Fin r → ℤ) (j : Fin r) (e : ℤ) :
    twistGrading (𝒮 N) (-d j) e →+ freeGrade (N := N) d e where
  toFun y := ⟨Pi.single j y.1, by
    rw [mem_freeGrade]; intro k
    by_cases hk : k = j
    · subst hk; simpa [sub_eq_add_neg] using y.2
    · simp [Pi.single_apply, hk, zero_mem]⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [Pi.single_add]

private def freeDecompose {r : ℕ} (d : Fin r → ℤ) :
    (Fin r → R N) →+ DirectSum ℤ fun e => freeGrade (N := N) d e :=
  ∑ j, (DirectSum.toAddMonoid fun e => (DirectSum.of (fun e => freeGrade (N := N) d e) e).comp
      (singleGrade d j e)).comp
    ((DirectSum.decomposeAddEquiv (twistGrading (𝒮 N) (-d j))).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun _ => R N) j))

private theorem coe_toAddMonoid_singleGrade {r : ℕ} (d : Fin r → ℤ) (j : Fin r)
    (x : DirectSum ℤ fun e => twistGrading (𝒮 N) (-d j) e) :
    DirectSum.coeAddMonoidHom (fun e => freeGrade (N := N) d e)
      (DirectSum.toAddMonoid (fun e => (DirectSum.of (fun e => freeGrade (N := N) d e) e).comp
        (singleGrade d j e)) x) =
      Pi.single j (DirectSum.coeAddMonoidHom (twistGrading (𝒮 N) (-d j)) x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of e y => simp [singleGrade]
  | add x y hx hy => simp [hx, hy, Pi.single_add]

@[instance_reducible]
private def freeDecomposition {r : ℕ} (d : Fin r → ℤ) :
    DirectSum.Decomposition fun e => freeGrade (N := N) d e :=
  DirectSum.Decomposition.ofAddHom _ (freeDecompose d)
    (by
      refine AddMonoidHom.ext fun v => ?_
      simp only [freeDecompose, AddMonoidHom.comp_apply, AddMonoidHom.finset_sum_apply, map_sum,
        AddMonoidHom.id_apply, coe_toAddMonoid_singleGrade]
      conv_rhs => rw [← Finset.univ_sum_single v]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      exact DirectSum.Decomposition.left_inv _)
    (by
      refine DirectSum.addHom_ext fun e y => ?_
      simp only [freeDecompose, AddMonoidHom.coe_comp, Function.comp_apply,
        AddMonoidHom.finset_sum_apply, AddMonoidHom.id_apply]
      have hy : ∀ j, y.1 j ∈ twistGrading (𝒮 N) (-d j) e := fun j => by
        have := mem_freeGrade.1 y.2 j
        simpa [sub_eq_add_neg] using this
      simp only [DirectSum.coeAddMonoidHom_of, Pi.evalAddMonoidHom_apply,
        AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, DirectSum.decomposeAddEquiv_apply]
      simp_rw [fun j => DirectSum.decompose_of_mem (twistGrading (𝒮 N) (-d j)) (hy j),
        DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, ← map_sum]
      congr 1
      ext k : 2
      simp [singleGrade, AddSubgroup.val_finset_sum, Finset.sum_apply, Pi.single_apply])

private theorem mul_mem_integerGrading {a b : R N} {m n : ℤ}
    (ha : a ∈ integerGrading (𝒮 N) m) (hb : b ∈ integerGrading (𝒮 N) n) :
    a * b ∈ integerGrading (𝒮 N) (m + n) := by
  by_cases hm : 0 ≤ m
  · by_cases hn : 0 ≤ n
    · simp only [integerGrading, hm, hn, if_true,
        AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_homogeneousSubmodule] at ha hb
      simp only [integerGrading, show 0 ≤ m + n by omega, if_true,
        AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_homogeneousSubmodule]
      rw [show (m + n).toNat = m.toNat + n.toNat by omega]
      exact SetLike.mul_mem_graded ha hb
    · simp only [integerGrading, hn, if_false, Submodule.mem_bot] at hb
      simp [hb, zero_mem]
  · simp only [integerGrading, hm, if_false, Submodule.mem_bot] at ha
    simp [ha, zero_mem]

attribute [local instance] freeDecomposition

@[instance_reducible]
private def twistDecomposition (n : ℤ) :
    DirectSum.Decomposition fun i => (twistGrading (𝒮 N) n i).toAddSubgroup where
  decompose' := DirectSum.Decomposition.decompose' (ℳ := twistGrading (𝒮 N) n)
  left_inv := DirectSum.Decomposition.left_inv (ℳ := twistGrading (𝒮 N) n)
  right_inv := DirectSum.Decomposition.right_inv (ℳ := twistGrading (𝒮 N) n)

attribute [local instance] twistDecomposition

/-- The functor `M ↦ M~` from graded `S`-modules to `𝒪_{ℙᴺ}`-modules. -/
private def sheafFunctor (N : ℕ) :
    GradedModuleCat.{0, 0, 0} (𝒮 N) ⥤ (AlgebraicGeometry.Proj (𝒮 N)).Modules :=
  associatedModuleSheafFunctor (𝒮 N)

private theorem additive_sheafFunctor : (sheafFunctor N).Additive :=
  instAdditiveAssociatedModuleSheafFunctor (𝒮 N)

attribute [local instance] additive_sheafFunctor

private theorem preservesHomology_sheafFunctor : (sheafFunctor N).PreservesHomology :=
  preservesHomology_associatedModuleSheafFunctor (𝒮 N)

attribute [local instance] preservesHomology_sheafFunctor

/-- The graded module `S(n)`. -/
private def twistObj (N : ℕ) (n : ℤ) : GradedModuleCat.{0, 0, 0} (𝒮 N) where
  carrier := R N
  grade i := (twistGrading (𝒮 N) n i).toAddSubgroup
  gradedSMul := ⟨fun {_ _} {_ _} ha hb =>
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGradingGradedSMul (𝒮 N) n).smul_mem ha hb⟩

/-- The graded module `⊕ⱼ S(-dⱼ)` on `Fin r → S`. -/
private def freeObj (N : ℕ) {r : ℕ} (d : Fin r → ℤ) : GradedModuleCat.{0, 0, 0} (𝒮 N) where
  carrier := Fin r → R N
  grade := freeGrade d
  gradedSMul := ⟨fun {i e} {a v} ha hv => by
    rw [mem_freeGrade] at hv ⊢
    intro k
    have ha' : a ∈ integerGrading (𝒮 N) (i : ℤ) := by simpa using ha
    have := mul_mem_integerGrading ha' (hv k)
    have he : ((i : ℤ) + (e - d k)) = (i +ᵥ e) - d k := by
      change _ = ((i : ℤ) + e) - d k; ring
    rw [he] at this
    exact this⟩

/-- A polynomial homogeneous of integer degree `n` moves the degree `e` part of a graded module
into degree `n + e`. -/
private theorem smul_mem_grade_of_mem_integerGrading (X : GradedModuleCat.{0, 0, 0} (𝒮 N))
    {a : R N} {m : X.carrier} {n e : ℤ} (ha : a ∈ integerGrading (𝒮 N) n) (hm : m ∈ X.grade e) :
    a • m ∈ X.grade (n + e) := by
  by_cases hn : 0 ≤ n
  · simp only [integerGrading, hn, if_true,
      AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_homogeneousSubmodule] at ha
    have := (X.gradedSMul).smul_mem ha hm
    rwa [show (n.toNat +ᵥ e : ℤ) = n + e by change (n.toNat : ℤ) + e = n + e; omega] at this
  · simp only [integerGrading, hn, if_false, Submodule.mem_bot] at ha
    simp [ha, zero_mem]

private theorem map_mem_of_mem_freeGrade {r : ℕ} (d : Fin r → ℤ)
    (X : GradedModuleCat.{0, 0, 0} (𝒮 N))
    (f : (Fin r → R N) →ₗ[R N] X.carrier) (hf : ∀ j, f (Pi.single j 1) ∈ X.grade (d j))
    {e : ℤ} {v : Fin r → R N} (hv : v ∈ freeGrade d e) : f v ∈ X.grade e := by
  rw [pi_eq_sum_univ' v, map_sum]
  refine sum_mem fun j _ => ?_
  rw [map_smul]
  simpa using smul_mem_grade_of_mem_integerGrading X (mem_freeGrade.1 hv j) (hf j)

/-- A linear map out of `⊕ⱼ S(-dⱼ)` sending each basis vector `eⱼ` into degree `dⱼ` is
degree-preserving. -/
private def freeHom {r : ℕ} (d : Fin r → ℤ) (X : GradedModuleCat.{0, 0, 0} (𝒮 N))
    (f : (Fin r → R N) →ₗ[R N] X.carrier) (hf : ∀ j, f (Pi.single j 1) ∈ X.grade (d j)) :
    freeObj N d ⟶ X :=
  ⟨f, fun _ _ hv => map_mem_of_mem_freeGrade d X f hf hv⟩

private theorem comp_eq_zero_of_range_eq_ker {X Y Z : GradedModuleCat.{0, 0, 0} (𝒮 N)}
    {f : X ⟶ Y} {g : Y ⟶ Z} (h : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap) :
    f ≫ g = 0 :=
  GradedModuleCat.hom_ext <| LinearMap.ext fun x => by
    simpa [h] using LinearMap.mem_range_self f.toLinearMap x

/-- A short complex of graded modules whose underlying linear maps are exact is exact. -/
private theorem exact_of_range_eq_ker {X Y Z : GradedModuleCat.{0, 0, 0} (𝒮 N)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    (h : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap) :
    (ShortComplex.mk f g w).Exact := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  let hk := GradedModuleCat.kernelForkIsLimit g
  let e : kernel g ≅ GradedModuleCat.kerObj g := (limit.isLimit _).conePointUniqueUpToIso hk
  let L : X ⟶ GradedModuleCat.kerObj g :=
    hk.lift (KernelFork.ofι f w)
  have hL : L ≫ GradedModuleCat.kerι g = f := hk.fac _ WalkingParallelPair.zero
  have hsurj : Function.Surjective L.toLinearMap := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ : y ∈ LinearMap.range f.toLinearMap := h ▸ hy
    refine ⟨x, Subtype.ext ?_⟩
    have := congrArg (fun φ => φ.toLinearMap x) hL
    simp only [GradedModuleCat.comp_toLinearMap, LinearMap.comp_apply] at this
    exact this.trans hx
  have he : e.inv ≫ kernel.ι g = GradedModuleCat.kerι g :=
    IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingParallelPair.zero
  have : kernel.lift g f w = L ≫ e.inv := by
    refine (cancel_mono (kernel.ι g)).1 ?_
    rw [kernel.lift_ι, Category.assoc, he, hL]
  rw [this]
  haveI := GradedModuleCat.epi_of_surjective hsurj
  haveI : Epi e.inv := IsIso.epi_of_iso _
  exact epi_comp L e.inv

/-- `⊕ⱼ S(-dⱼ)` as a biproduct of the `S(-dⱼ)`. -/
private def freeBicone {r : ℕ} (d : Fin r → ℤ) : Bicone fun k => twistObj N (-d k) where
  pt := freeObj N d
  π k := ⟨LinearMap.proj k, fun e (v : Fin r → R N) hv => by
    have := (mem_freeGrade (d := d) (e := e) (v := v)).1 hv k
    rw [sub_eq_add_neg] at this
    exact this⟩
  ι k := ⟨LinearMap.single (R N) (fun _ => R N) k, fun e y hy => (singleGrade d k e ⟨y, hy⟩).2⟩
  ι_π j k := by
    split_ifs with h
    · subst h
      exact GradedModuleCat.hom_ext (LinearMap.ext fun x =>
        Pi.single_eq_same (M := fun _ : Fin r => R N) j x)
    · exact GradedModuleCat.hom_ext (LinearMap.ext fun x =>
        Pi.single_eq_of_ne (M := fun _ : Fin r => R N) (Ne.symm h) x)

private def freeBiconeIsBilimit {r : ℕ} (d : Fin r → ℤ) : (freeBicone (N := N) d).IsBilimit :=
  isBilimitOfTotal _ <| GradedModuleCat.hom_ext <| by
    have := map_sum (AddMonoidHom.mk' (fun f : freeObj N d ⟶ freeObj N d => f.toLinearMap)
      GradedModuleCat.add_toLinearMap)
      (fun j => (freeBicone (N := N) d).π j ≫ (freeBicone (N := N) d).ι j) Finset.univ
    refine this.trans (LinearMap.ext fun v => ?_)
    rw [LinearMap.sum_apply]
    exact Finset.univ_sum_single (v : Fin r → R N)

/-- `(⊕ⱼ S(-dⱼ))~ ≅ ∐ⱼ 𝒪(-dⱼ)`; here `S(d)~` is `𝒪(d)` by definition. -/
private def freeObjIso {r : ℕ} (d : Fin r → ℤ) :
    (sheafFunctor N).obj (freeObj N d) ≅
      ∐ fun k => ProjectiveSpectrum.Proj.twistingSheaf (𝒮 N) (-d k) :=
  (isBilimitOfPreserves (sheafFunctor N)
    (freeBiconeIsBilimit (N := N) d)).isColimit.coconePointUniqueUpToIso (colimit.isColimit _)

private theorem isZero_freeObj {r : ℕ} (hr : r = 0) (d : Fin r → ℤ) :
    IsZero ((sheafFunctor N).obj (freeObj N d)) := by
  subst hr
  exact
  haveI : Subsingleton (freeObj N d).carrier := inferInstanceAs (Subsingleton (Fin 0 → R N))
  Functor.map_isZero _ <| (IsZero.iff_id_eq_zero _).2 <|
    GradedModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

/-- A finitely generated graded `S`-module has a resolution of length at most `N + 1` by graded
free modules `⊕ⱼ S(-dᵢⱼ)`, with degree-preserving differentials. -/
private theorem exists_freeObj_resolution (M : GradedModuleCat.{0, 0, 0} (𝒮 N))
    (hM : Module.Finite (R N) M.carrier) :
    ∃ (r : ℕ → ℕ) (d : ∀ i, Fin (r i) → ℤ)
      (δ : ∀ i, freeObj N (d (i + 1)) ⟶ freeObj N (d i)) (ε : freeObj N (d 0) ⟶ M),
      (∀ i, N + 1 < i → r i = 0) ∧ Function.Surjective ε.toLinearMap ∧
      LinearMap.range (δ 0).toLinearMap = LinearMap.ker ε.toLinearMap ∧
      ∀ i, LinearMap.range (δ (i + 1)).toLinearMap = LinearMap.ker (δ i).toLinearMap := by
  letI : Module ℂ M.carrier := Module.compHom M.carrier (algebraMap ℂ (R N))
  haveI : IsScalarTower ℂ (R N) M.carrier := ⟨fun c s m => by
    change (c • s) • m = (algebraMap ℂ (R N) c) • (s • m)
    rw [Algebra.smul_def, mul_smul]⟩
  let 𝓜 : ℤ → Submodule ℂ M.carrier := fun e =>
    { toAddSubmonoid := (M.grade e).toAddSubmonoid
      smul_mem' := fun c m hm => by
        change algebraMap ℂ (R N) c • m ∈ M.grade e
        have hc : algebraMap ℂ (R N) c ∈ (𝒮 N) 0 := SetLike.algebraMap_mem_graded _ _
        have := (M.gradedSMul).smul_mem hc hm
        have he : ((0 : ℕ) +ᵥ e : ℤ) = e := by change ((0 : ℕ) : ℤ) + e = e; simp
        rwa [he] at this }
  letI : DirectSum.Decomposition 𝓜 :=
    { decompose' := DirectSum.Decomposition.decompose' (ℳ := M.grade)
      left_inv := DirectSum.Decomposition.left_inv (ℳ := M.grade)
      right_inv := DirectSum.Decomposition.right_inv (ℳ := M.grade) }
  haveI : SetLike.GradedSMul (weightedHomogeneousSubmodule ℂ (fun _ : Fin (N + 1) ↦ (1 : ℤ)))
      𝓜 := ⟨fun {_ _} {_ _} ha hm =>
    smul_mem_grade_of_mem_integerGrading M (mem_integerGrading_of_mem ha) hm⟩
  obtain ⟨r, d, δ, ε, hr, hε, hδ, hεs, h0, hex⟩ :=
    MMP.GAGA.regularLocalRing_quotient_and_finite_free_resolutions.{0, 0}.2.2 N M.carrier 𝓜 hM
  refine ⟨r, d, fun i => freeHom (d (i + 1)) (freeObj N (d i)) (δ i) fun j =>
      mem_freeGrade.2 fun k => mem_integerGrading_of_mem (hδ i j k),
    freeHom (d 0) M ε hε, hr, LinearMap.range_eq_top.1 hεs, h0, hex⟩

private theorem map_comp_map_comp_eq_zero {X Y Z : GradedModuleCat.{0, 0, 0} (𝒮 N)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) {T : (AlgebraicGeometry.Proj (𝒮 N)).Modules}
    (φ : (sheafFunctor N).obj Z ⟶ T) :
    (sheafFunctor N).map f ≫ (sheafFunctor N).map g ≫ φ = 0 := by
  rw [← Functor.map_comp_assoc, w, Functor.map_zero, zero_comp]

/-- The image under `M ↦ M~` of an exact sequence of graded modules, followed by an isomorphism,
is exact. -/
private theorem exact_map_comp_iso {X Y Z : GradedModuleCat.{0, 0, 0} (𝒮 N)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    (h : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap)
    {T : (AlgebraicGeometry.Proj (𝒮 N)).Modules} (φ : (sheafFunctor N).obj Z ≅ T) :
    (ShortComplex.mk ((sheafFunctor N).map f) ((sheafFunctor N).map g ≫ φ.hom)
      (map_comp_map_comp_eq_zero f g w φ.hom)).Exact := by
  have hm := (exact_of_range_eq_ker f g w h).map (sheafFunctor N)
  refine (ShortComplex.exact_iff_of_iso ?_).1 hm
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) φ
    ((Category.id_comp _).trans (Category.comp_id _).symm) (Category.id_comp _)

/-- **Resolutions of coherent sheaves on `ℙᴺ_ℂ` by twisting sheaves.** Every coherent sheaf `G`
on `ℙᴺ_ℂ` has a resolution `0 → ℰ_{N+1} → ⋯ → ℰ₀ → G → 0`: a chain complex `ℰ•` with an
augmentation `ε : ℰ₀ → G` whose augmented complex is acyclic, with `ℰⱼ = 0` for `j > N + 1`
and every `ℰⱼ` isomorphic to a finite direct sum (coproduct) of twisting sheaves `𝒪(d)`. -/
@[mmp "lem_mmp_gaga_projective_space_graded_resolutions"]
public theorem exists_twistingSheaf_resolution_projectiveSpace (N : ℕ)
    (G : (AlgebraicGeometry.Proj (𝒮 N)).Modules)
    (hG : Stacks.SheafOfModules.IsCoherent G) :
    ∃ (E : ChainComplex (AlgebraicGeometry.Proj (𝒮 N)).Modules ℕ)
      (ε : E.X 0 ⟶ G) (hε : E.d 1 0 ≫ ε = 0),
      (E.augment ε hε).Acyclic ∧
      (∀ j, N + 1 < j → IsZero (E.X j)) ∧
      ∀ j, ∃ (p : ℕ) (d : Fin p → ℤ),
        Nonempty (E.X j ≅
          ∐ fun i => ProjectiveSpectrum.Proj.twistingSheaf (𝒮 N) (d i)) := by
  let Gc : SheafOfModules.CoherentModules
      (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf (𝒮 N)) := ⟨G, ⟨hG.1, hG.2⟩⟩
  let Mf :=
    (Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentTruncatedTwistedSectionsFunctor
      (𝒮 N) 0).obj Gc
  let eM : (sheafFunctor N).obj Mf.obj ≅ G := (ObjectProperty.ι _).mapIso
    (Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentTruncatedTwistedSectionsObj_iso
      (𝒮 N) 0 Gc)
  obtain ⟨r, d, δ, ε, hr, hεs, h0, hex⟩ := exists_freeObj_resolution Mf.obj Mf.property
  have hδδ : ∀ i, δ (i + 1) ≫ δ i = 0 := fun i => comp_eq_zero_of_range_eq_ker (hex i)
  have hδε : δ 0 ≫ ε = 0 := comp_eq_zero_of_range_eq_ker h0
  let C : ChainComplex (GradedModuleCat.{0, 0, 0} (𝒮 N)) ℕ :=
    ChainComplex.of (fun i => freeObj N (d i)) δ hδδ
  let E := ((sheafFunctor N).mapHomologicalComplex _).obj C
  have hd : ∀ i, E.d (i + 1) i = (sheafFunctor N).map (δ i) := fun i => by
    simp [E, C]
  let ε' : E.X 0 ⟶ G := (sheafFunctor N).map ε ≫ eM.hom
  have hε' : E.d 1 0 ≫ ε' = 0 := by
    rw [hd, ← Functor.map_comp_assoc, hδε, Functor.map_zero, zero_comp]
  refine ⟨E, ε', hε', fun i => ?_, fun j hj => isZero_freeObj (hr j hj) (d j),
    fun j => ⟨r j, fun k => -d j k, ⟨freeObjIso (d j)⟩⟩⟩
  rcases i with _ | _ | n
  · rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp)]
    refine (ShortComplex.exact_iff_epi _ rfl).2 ?_
    haveI := GradedModuleCat.epi_of_surjective hεs
    haveI : PreservesFiniteColimits (sheafFunctor N) :=
      Functor.preservesFiniteColimits_of_preservesHomology _
    change Epi ((sheafFunctor N).map ε ≫ eM.hom)
    infer_instance
  · rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
    refine (ShortComplex.exact_iff_of_iso ?_).2 (exact_map_comp_iso (δ 0) ε hδε h0 eM)
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans ((hd 0).symm.trans (Category.comp_id _).symm))
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  · rw [HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1) (by simp) (by simp)]
    refine (ShortComplex.exact_iff_of_iso ?_).2
      (exact_map_comp_iso (δ (n + 1)) (δ n) (hδδ n) (hex n) (Iso.refl _))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans ((hd (n + 1)).symm.trans (Category.comp_id _).symm))
      ((Category.id_comp _).trans ((hd n).symm.trans (Category.comp_id _).symm))

end

end ProjectiveSpaceResolutions

end MMP.Analytic

end
