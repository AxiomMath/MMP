module
public import MMP.AlgebraicGeometry.Variety.Basic
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.Derivative
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero
import StacksFrontier.Topology.Sheaves.Cohomology.GodementResolution.StalkHomotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportImmersion
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuasiProjectiveRegularSurface

/-!
# A proper birational morphism to a normal variety is an isomorphism in codimension one

Let `K` be a field and `μ : X' ⟶ X` a proper birational morphism over `K` of varieties over `K`,
that is, of integral schemes separated and of finite type over `K`, with `X` normal. Then there is
a closed subset `Z ⊆ X` whose codimension, in the sense of
`MMP.Intersection.Scheme.IdealSheafData.codim` of its reduced induced structure, is at least two,
such that `μ` restricts to an isomorphism `μ⁻¹(X ∖ Z) ⟶ X ∖ Z`.

## Main results

* `MMP.exists_isIso_morphismRestrict_of_isBirational`: the existence of such a `Z`.

## Implementation notes

A variety in Lazarsfeld's sense is a reduced irreducible scheme separated and of finite type over
the ground field: here `MMP.Intersection.IsSeparatedAlgebraicScheme K` together with
`IsIntegral`. Lazarsfeld works over `ℂ`; the statement is made over an arbitrary field `K`.
Birationality is `AlgebraicGeometry.IsBirational`: a bijection on generic points with
isomorphisms of the local rings there.

## References

* [R. Lazarsfeld, *Positivity in algebraic geometry I*][Lazarsfeld2004], Appendix B.
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Mori

namespace MMP.Proofs.lem_mmp_foundation_laz_proper_birational_codimension_one

/-- If `U ↪ X' ⟶ X` is an open immersion for a nonempty open `U` of an irreducible `X'` and
`μ` is separated, then `μ` is an isomorphism over the image of `U`. -/
private theorem isBiregular_opensRange {X' X : Scheme.{u}} [IsIntegral X'] (μ : X' ⟶ X)
    [IsSeparated μ] (U : X'.Opens) (hU : (U : Set X').Nonempty) [IsOpenImmersion (U.ι ≫ μ)] :
    IsBiregular μ (U.ι ≫ μ).opensRange := by
  set V := (U.ι ≫ μ).opensRange
  have hUV : U ≤ μ ⁻¹ᵁ V := fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩
  let e := (U.ι ≫ μ).isoOpensRange
  let s : V.toScheme ⟶ (μ ⁻¹ᵁ V).toScheme := e.inv ≫ X'.homOfLE hUV
  have hs : s ≫ μ ∣_ V = 𝟙 _ := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, Category.id_comp]
    simp only [s, Category.assoc, Scheme.homOfLE_ι_assoc]
    rw [Iso.inv_comp_eq]
    exact ((U.ι ≫ μ).isoOpensRange_hom_ι).symm
  haveI : IsClosedImmersion (s ≫ μ ∣_ V) := by
    rw [hs]
    infer_instance
  haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s (μ ∣_ V)
  obtain ⟨x, hx⟩ := hU
  haveI : Nonempty (μ ⁻¹ᵁ V).toScheme := ⟨⟨x, hUV hx⟩⟩
  haveI : IsIntegral (μ ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (μ ⁻¹ᵁ V).ι
  have hrange : Set.range s = Set.univ := by
    refine IsClopen.eq_univ ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpen_range⟩ ?_
    exact ⟨_, Set.mem_range_self (e.hom ⟨x, hx⟩)⟩
  haveI : IsIso s := (isIso_iff_isOpenImmersion_and_surjective s).mpr
    ⟨inferInstance, ⟨Set.range_eq_univ.mp hrange⟩⟩
  haveI : IsIso (s ≫ μ ∣_ V) := by
    rw [hs]
    infer_instance
  change IsIso (μ ∣_ V)
  exact IsIso.of_isIso_comp_left s (μ ∣_ V)

/-- At a point of codimension at most one of a normal locally Noetherian integral scheme, the
local ring is a valuation ring: the function field at the generic point, a discrete valuation ring
at a point of codimension one. -/
private theorem valuationRing_stalk_of_coheight_le_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {y : X} (hy : Order.coheight y ≤ 1) :
    ValuationRing (X.presheaf.stalk y) := by
  rcases hy.lt_or_eq with h0 | h1
  · obtain rfl : y = genericPoint X := (Specializes.antisymm
      (Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h0) (genericPoint_specializes y))
      (genericPoint_specializes y)).eq
    change ValuationRing X.functionField
    infer_instance
  · haveI := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk h1
    infer_instance

/-- A proper birational morphism of integral schemes to a normal locally Noetherian scheme is an
isomorphism over a neighbourhood of every point of codimension at most one. -/
private theorem mem_biregularLocus_of_coheight_le_one {X' X : Scheme.{u}} [IsIntegral X']
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (μ : X' ⟶ X) [IsProper μ]
    (hμ : IsBirational μ) {y : X} (hy : Order.coheight y ≤ 1) : y ∈ biregularLocus μ := by
  have hgen : genericPoint X' ∈ genericPoints X' := by simp [genericPoints_eq_singleton]
  have hηX : μ (genericPoint X') = genericPoint X := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hμ.1.1 hgen
  haveI : IsDominant μ := ⟨(dense_iff_closure_eq.mpr (genericPoint_spec X)).mono
    (Set.singleton_subset_iff.mpr ⟨_, hηX⟩)⟩
  haveI : IsIso (μ.stalkMap (genericPoint X')) := hμ.2 _ hgen
  have hbij : Function.Bijective (functionFieldMap μ) :=
    ConcreteCategory.bijective_of_isIso
      ((X.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant μ).symm)).hom ≫
        μ.stalkMap (genericPoint X'))
  haveI := valuationRing_stalk_of_coheight_le_one hy
  obtain ⟨x', hx', hiso⟩ := MMP.Intersection.exists_isIso_stalkMap_of_valuationRing μ hbij y
  have hfin : (irreducibleComponents X).Finite := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, hxU, hU⟩ := exists_isOpenImmersion_res_of_isIso_stalkMap μ x' hfin hiso
  exact le_biregularLocus (isBiregular_opensRange μ U ⟨x', hxU⟩) ⟨⟨x', hxU⟩, hx'⟩

end MMP.Proofs.lem_mmp_foundation_laz_proper_birational_codimension_one

namespace MMP

open MMP.Proofs.lem_mmp_foundation_laz_proper_birational_codimension_one in
/-- A proper birational morphism `μ : X' ⟶ X` over a field `K` of integral schemes separated and of
finite type over `K`, with `X` normal, is an isomorphism away from a closed subset `Z` of
codimension at least two: `μ ∣_ Zᶜ` is an isomorphism. -/
@[mmp "lem_mmp_foundation_laz_proper_birational_codimension_one"]
public theorem exists_isIso_morphismRestrict_of_isBirational (K : Type u) [Field K]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of K))] [X.Over (Spec (.of K))]
    [Intersection.IsSeparatedAlgebraicScheme K X'] [Intersection.IsSeparatedAlgebraicScheme K X]
    [IsIntegral X'] [IsIntegral X] [IsNormal X]
    (μ : X' ⟶ X) [μ.IsOver (Spec (.of K))] [IsProper μ] (hμ : IsBirational μ) :
    ∃ Z : Closeds X,
      2 ≤ Intersection.Scheme.IdealSheafData.codim (Scheme.IdealSheafData.vanishingIdeal Z) ∧
        IsIso (μ ∣_ Z.compl) := by
  haveI : LocallyOfFiniteType (X ↘ Spec (.of K)) :=
    ‹Intersection.IsSeparatedAlgebraicScheme K X›.locallyOfFiniteType
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  refine ⟨(biregularLocus μ).compl, le_iInf₂ fun η _ ↦ ?_, ?_⟩
  · rw [ringKrullDim_stalk_eq_coheight]
    have hmem := Set.mem_range_self (f :=
      ⇑(Scheme.IdealSheafData.vanishingIdeal (biregularLocus μ).compl).subschemeι) η
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem
    by_contra h
    exact hmem (mem_biregularLocus_of_coheight_le_one μ hμ
      (Order.le_of_lt_succ (WithBot.coe_lt_coe.mp (not_le.mp h))))
  · rw [Opens.compl_compl]
    exact isBiregular_biregularLocus μ

end MMP

end

/-!
# A polynomial lower bound for the Hilbert function of a projective closed subset

Let `k` be a field, `S = k[Xᵢ | i ∈ σ]` the polynomial ring with its standard grading, and
`Z ⊆ Proj S` a closed subset of dimension `d`. Let `I` be the homogeneous ideal of all forms
vanishing on `Z`. Then the Hilbert function of `S ⧸ I` grows at least like `c · nᵈ`: there are
a constant `c > 0` and a threshold `n₀` such that the degree-`n` part of `S ⧸ I` has
dimension at least `c · nᵈ` over `k` for all `n ≥ n₀`.

## Main results

* `MMP.exists_mul_pow_le_finrank_map_homogeneousSubmodule_vanishingIdeal`: the lower bound.

## Implementation notes

Projective space is `ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule σ k)`, the underlying
space of `Proj` of the polynomial ring. Its points are the relevant homogeneous primes, so
`ProjectiveSpectrum.vanishingIdeal Z` is the ideal of forms vanishing at every scheme-theoretic
point of `Z`, which is the ideal of all forms vanishing on `Z`. The dimension of `Z` is its
`topologicalKrullDim`. The degree-`n` part of `S ⧸ I` is the image of the degree-`n` forms
under the quotient map. The grading by total degree is `MvPolynomial.gradedAlgebra`, used as a
local instance as Mathlib intends; σ is only required to be finite.

## References

* [Lazarsfeld, *Positivity in Algebraic Geometry I*]
-/

section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MMP.Proofs.lem_mmp_foundation_projective_hilbert_function_lower

private lemma eq_zero_of_eval₂_mem {B R : Type*} [CommRing B] [CommRing R] (ψ : B →+* R)
    {P P' : Ideal R} [P.IsPrime] (hPP' : P ≤ P') {t : R} (ht : t ∈ P') (htP : t ∉ P)
    (hψ : ∀ b, ψ b ∈ P' → b = 0) (F : Polynomial B) (hF : F.eval₂ ψ t ∈ P) : F = 0 := by
  have key : ∀ F : Polynomial B, F.eval₂ ψ t ∈ P →
      F.coeff 0 = 0 ∧ F.divX.eval₂ ψ t ∈ P := by
    intro F hF
    have h := congrArg (Polynomial.eval₂ ψ t) (Polynomial.X_mul_divX_add F)
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    have h0 : F.coeff 0 = 0 := by
      apply hψ
      have : ψ (F.coeff 0) = F.eval₂ ψ t - t * F.divX.eval₂ ψ t := by rw [← h]; ring
      rw [this]
      exact P'.sub_mem (hPP' hF) (P'.mul_mem_right _ ht)
    refine ⟨h0, ?_⟩
    rw [h0, map_zero, add_zero] at h
    rw [← h] at hF
    exact (Ideal.IsPrime.mem_or_mem ‹_› hF).resolve_left htP
  ext n
  rw [Polynomial.coeff_zero]
  induction n generalizing F with
  | zero => exact (key F hF).1
  | succ n ih =>
    rw [← Polynomial.coeff_divX]
    exact ih _ (key F hF).2

/-- Evaluating at `g` factors through `finSuccEquiv`: the coefficients are evaluated at the
last `j` values of `g` and the polynomial variable at `g 0`. -/
private lemma aeval_eq_eval₂_finSuccEquiv {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]
    {j : ℕ} (g : Fin (j + 1) → S) (F : MvPolynomial (Fin (j + 1)) k) :
    aeval g F = (finSuccEquiv k j F).eval₂ (aeval (g ∘ Fin.succ)).toRingHom (g 0) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply, Polynomial.eval₂_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, Polynomial.eval₂_mul, hp, aeval_X]
    congr 1
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [finSuccEquiv_X_zero]
    · simp [finSuccEquiv_X_succ]

private lemma eq_zero_of_aeval_mem {k S : Type*} [Field k] [CommRing S] [Algebra k S] :
    ∀ (j : ℕ) (Q : Fin (j + 1) → Ideal S) (g : Fin j → S),
      (∀ i : Fin j, (Q i.castSucc).IsPrime) → (∀ i : Fin j, Q i.castSucc ≤ Q i.succ) →
      (∀ i : Fin j, g i ∈ Q i.succ) → (∀ i : Fin j, g i ∉ Q i.castSucc) →
      (∀ c : k, algebraMap k S c ∈ Q (Fin.last j) → c = 0) →
      ∀ F : MvPolynomial (Fin j) k, aeval g F ∈ Q 0 → F = 0
  | 0, Q, g, _, _, _, _, hc, F, hF => by
      obtain ⟨c, rfl⟩ : ∃ c, F = C c := ⟨_, (MvPolynomial.eq_C_of_isEmpty F)⟩
      rw [aeval_C] at hF
      rw [hc c hF, C_0]
  | j + 1, Q, g, hprime, hle, hmem, hnot, hc, F, hF => by
      have IH := eq_zero_of_aeval_mem j (Q ∘ Fin.succ) (g ∘ Fin.succ)
        (fun i => hprime i.succ) (fun i => hle i.succ) (fun i => hmem i.succ)
        (fun i => hnot i.succ) (by simpa using hc)
      have hP : (Q 0).IsPrime := hprime 0
      rw [aeval_eq_eval₂_finSuccEquiv] at hF
      have := eq_zero_of_eval₂_mem (aeval (g ∘ Fin.succ)).toRingHom (P := Q 0) (P' := Q 1)
        (hle 0) (hmem 0) (hnot 0) (fun b hb => IH b (by simpa using hb)) _ hF
      exact (finSuccEquiv k j).injective (by rw [this, map_zero])

private lemma exists_mul_pow_le_finrank_of_aeval_injective {k : Type*} [Field k] {σ : Type*}
    [Finite σ]
    (J P : Ideal (MvPolynomial σ k)) (hJP : J ≤ P) {d : ℕ}
    (g : Fin (d + 1) → MvPolynomial σ k) (e : Fin (d + 1) → ℕ)
    (hg : ∀ i, (g i).IsHomogeneous (e i)) (he : e (Fin.last d) = 1)
    (hinj : ∀ F : MvPolynomial (Fin (d + 1)) k, aeval g F ∈ P → F = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c * (n : ℝ) ^ d ≤
      Module.finrank k ((homogeneousSubmodule σ k n).map
        (Ideal.Quotient.mkₐ k J).toLinearMap) := by
  set E : ℕ := 1 + ∑ i : Fin d, e i.castSucc with hE
  have hE0 : 0 < E := by omega
  refine ⟨1 / (E : ℝ) ^ d, by positivity, fun n => ?_⟩
  set N := n / E
  set M := (homogeneousSubmodule σ k n).map (Ideal.Quotient.mkₐ k J).toLinearMap
  let b : (Fin d → Fin (N + 1)) → (Fin (d + 1) →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm
      (Fin.snoc (fun i => (a i : ℕ)) (n - ∑ i, (a i : ℕ) * e i.castSucc))
  have hb : Function.Injective b := by
    intro a a' h
    funext i
    have := congrArg (fun f => f i.castSucc) h
    simpa [b, Fin.snoc_castSucc, Fin.ext_iff] using this
  have hsum : ∀ a : Fin d → Fin (N + 1), ∑ i, (a i : ℕ) * e i.castSucc ≤ n := by
    intro a
    calc ∑ i, (a i : ℕ) * e i.castSucc ≤ ∑ i : Fin d, N * e i.castSucc :=
          Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp (a i).2)
      _ = N * (∑ i : Fin d, e i.castSucc) := by rw [Finset.mul_sum]
      _ ≤ N * E := Nat.mul_le_mul_left _ (by omega)
      _ ≤ n := Nat.div_mul_le_self n E
  have hmem : ∀ a, aeval g (monomial (b a) (1 : k)) ∈ homogeneousSubmodule σ k n := by
    intro a
    rw [mem_homogeneousSubmodule]
    rw [aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    have h := IsHomogeneous.prod (Finset.univ : Finset (Fin (d + 1))) (fun i => g i ^ b a i)
      (fun i => e i * b a i) (fun i _ => (hg i).pow _)
    convert h using 1
    rw [Fin.sum_univ_castSucc]
    simp only [b, Finsupp.equivFunOnFinite_symm_apply_apply, Fin.snoc_castSucc, Fin.snoc_last, he,
      one_mul]
    have := hsum a
    simp only [mul_comm (e _)]
    omega
  let w : (Fin d → Fin (N + 1)) → M := fun a =>
    ⟨Ideal.Quotient.mkₐ k J (aeval g (monomial (b a) (1 : k))),
      Submodule.mem_map_of_mem (hmem a)⟩
  have hli : LinearIndependent k w := by
    let f : MvPolynomial (Fin (d + 1)) k →ₗ[k] MvPolynomial σ k ⧸ P :=
      (Ideal.Quotient.mkₐ k P).toLinearMap ∘ₗ (aeval g).toLinearMap
    have hf : LinearMap.ker f = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro F hF
      exact hinj F (Ideal.Quotient.eq_zero_iff_mem.mp hF)
    have h1 : LinearIndependent k (fun a => monomial (b a) (1 : k)) := by
      have := (basisMonomials (Fin (d + 1)) k).linearIndependent.comp b hb
      rwa [coe_basisMonomials] at this
    exact .of_comp M.subtype (.of_comp (Ideal.Quotient.factorₐ k hJP).toLinearMap (h1.map' f hf))
  have : Module.Finite k M :=
    Module.Finite.iff_fg.mpr ((homogeneousSubmodule_fg (σ := σ) (R := k) n).map _)
  have hcard := hli.fintype_card_le_finrank
  simp only [Fintype.card_fun, Fintype.card_fin] at hcard
  have hlt : n < N * E + E := Nat.lt_div_mul_add hE0
  have hreal : (n : ℝ) / E ≤ (N + 1 : ℕ) := by
    rw [div_le_iff₀ (by exact_mod_cast hE0)]
    push_cast
    exact_mod_cast (by nlinarith : n ≤ (N + 1) * E)
  calc 1 / (E : ℝ) ^ d * (n : ℝ) ^ d = ((n : ℝ) / E) ^ d := by rw [div_pow]; ring
    _ ≤ ((N + 1 : ℕ) : ℝ) ^ d := pow_le_pow_left₀ (by positivity) hreal d
    _ ≤ _ := by exact_mod_cast hcard

section Spectrum

variable {k : Type*} [Field k] {σ : Type*}

private lemma isPrime_vanishingIdeal {C : Set (ProjectiveSpectrum (homogeneousSubmodule σ k))}
    (hC : IsIrreducible C) : (ProjectiveSpectrum.vanishingIdeal C).toIdeal.IsPrime := by
  obtain ⟨x, hx⟩ := hC.nonempty
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · have h1 : (1 : MvPolynomial σ k) ∈ (ProjectiveSpectrum.vanishingIdeal C).toIdeal := by
      rw [h]; trivial
    exact x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr
      ((ProjectiveSpectrum.mem_vanishingIdeal _ _).mp h1 x hx))
  · have hsub : C ⊆ ProjectiveSpectrum.zeroLocus _ {a} ∪ ProjectiveSpectrum.zeroLocus _ {b} := by
      rw [← ProjectiveSpectrum.zeroLocus_singleton_mul]
      exact (ProjectiveSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal _ _ _).mpr
        (Set.singleton_subset_iff.mpr hab)
    rcases isPreirreducible_iff_isClosed_union_isClosed.mp hC.isPreirreducible _ _
      (ProjectiveSpectrum.isClosed_zeroLocus _ _) (ProjectiveSpectrum.isClosed_zeroLocus _ _)
      hsub with h | h
    · left
      exact Set.singleton_subset_iff.mp
        ((ProjectiveSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal _ _ _).mp h)
    · right
      exact Set.singleton_subset_iff.mp
        ((ProjectiveSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal _ _ _).mp h)

private lemma exists_isHomogeneous_mem_vanishingIdeal_notMem
    {C C' : Set (ProjectiveSpectrum (homogeneousSubmodule σ k))} (hC : IsClosed C)
    (hCC' : C ⊂ C') : ∃ (f : MvPolynomial σ k) (e : ℕ), f.IsHomogeneous e ∧
      f ∈ (ProjectiveSpectrum.vanishingIdeal C).toIdeal ∧
      f ∉ (ProjectiveSpectrum.vanishingIdeal C').toIdeal := by
  obtain ⟨x, hxC', hxC⟩ := Set.exists_of_ssubset hCC'
  rw [← hC.closure_eq, ← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ProjectiveSpectrum.mem_zeroLocus, Set.not_subset] at hxC
  obtain ⟨p, hp, hpx⟩ := hxC
  change p ∉ x.asHomogeneousIdeal.toIdeal at hpx
  rw [mem_iff_homogeneousComponent_mem x.asHomogeneousIdeal.isHomogeneous] at hpx
  push Not at hpx
  obtain ⟨e, he⟩ := hpx
  refine ⟨homogeneousComponent e p, e, homogeneousComponent_isHomogeneous _ _,
    homogeneousComponent_mem_of_mem (ProjectiveSpectrum.vanishingIdeal C).isHomogeneous hp e,
    fun h => he ((ProjectiveSpectrum.mem_vanishingIdeal _ _).mp h x hxC')⟩

private lemma exists_X_notMem (x : ProjectiveSpectrum (homogeneousSubmodule σ k)) :
    ∃ v : σ, X v ∉ x.asHomogeneousIdeal.toIdeal := by
  by_contra! h
  apply x.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi p hp
  have hp' : p ∈ Ideal.span (X '' Set.univ : Set (MvPolynomial σ k)) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    have hdeg : Finsupp.weight 1 m = i :=
      (mem_homogeneousSubmodule _ _).mp hp (mem_support_iff.mp hm)
    by_contra! hm0
    have : m = 0 := Finsupp.ext fun j => hm0 j trivial
    rw [this, map_zero] at hdeg
    omega
  exact Ideal.span_le.mpr (by rintro _ ⟨v, -, rfl⟩; exact h v) hp'

private lemma constantCoeff_eq_zero_of_mem (x : ProjectiveSpectrum (homogeneousSubmodule σ k))
    {p : MvPolynomial σ k} (hp : p ∈ x.asHomogeneousIdeal.toIdeal) : constantCoeff p = 0 := by
  by_contra h
  have h0 := homogeneousComponent_mem_of_mem x.asHomogeneousIdeal.isHomogeneous hp 0
  rw [homogeneousComponent_zero] at h0
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit h).map C))

/-- A strict chain `C₀ ⊊ ⋯ ⊊ C_d` of irreducible closed subsets of `Proj k[X]` gives `d + 1`
forms of degrees `e`, the last one a variable, that are algebraically independent modulo the
ideal of `C_d`. -/
private lemma exists_isHomogeneous_aeval_injective {d : ℕ}
    (C : Fin (d + 1) → Set (ProjectiveSpectrum (homogeneousSubmodule σ k)))
    (hirr : ∀ i, IsIrreducible (C i)) (hcl : ∀ i, IsClosed (C i))
    (hCss : ∀ i : Fin d, C i.castSucc ⊂ C i.succ) :
    ∃ (g : Fin (d + 1) → MvPolynomial σ k) (e : Fin (d + 1) → ℕ),
      (∀ i, (g i).IsHomogeneous (e i)) ∧ e (Fin.last d) = 1 ∧
      ∀ F : MvPolynomial (Fin (d + 1)) k,
        aeval g F ∈ (ProjectiveSpectrum.vanishingIdeal (C (Fin.last d))).toIdeal → F = 0 := by
  let V : Fin (d + 1) → Ideal (MvPolynomial σ k) := fun i =>
    (ProjectiveSpectrum.vanishingIdeal (C i.rev)).toIdeal
  have hfe : ∀ i : Fin d, ∃ (f : MvPolynomial σ k) (e : ℕ), f.IsHomogeneous e ∧
      f ∈ V i.succ ∧ f ∉ V i.castSucc := by
    intro i
    have := hCss i.rev
    rw [← Fin.rev_succ, ← Fin.rev_castSucc] at this
    exact exists_isHomogeneous_mem_vanishingIdeal_notMem (hcl _) this
  choose f e hf using hfe
  obtain ⟨x, hx⟩ := (hirr 0).nonempty
  obtain ⟨v, hv⟩ := exists_X_notMem x
  have hVx : V (Fin.last d) ≤ x.asHomogeneousIdeal.toIdeal := by
    intro p hp
    simp only [V, Fin.rev_last] at hp
    exact (ProjectiveSpectrum.mem_vanishingIdeal _ _).mp hp x hx
  let m : Ideal (MvPolynomial σ k) := RingHom.ker (constantCoeff (σ := σ) (R := k))
  let Q : Fin (d + 2) → Ideal (MvPolynomial σ k) := Fin.snoc V m
  let g : Fin (d + 1) → MvPolynomial σ k := Fin.snoc f (X v)
  let e' : Fin (d + 1) → ℕ := Fin.snoc e 1
  have hinj := eq_zero_of_aeval_mem (k := k) (d + 1) Q g
    (fun i => by
      simp only [Q, Fin.snoc_castSucc]
      exact isPrime_vanishingIdeal (hirr _))
    (fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Q, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
        exact fun p hp => constantCoeff_eq_zero_of_mem x (hVx hp)
      · rw [Fin.succ_castSucc]
        simp only [Q, Fin.snoc_castSucc, V]
        rw [Fin.rev_castSucc, Fin.rev_succ]
        exact ProjectiveSpectrum.vanishingIdeal_anti_mono _ (hCss j.rev).le)
    (fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [Q, g, Fin.succ_last, m]
      · rw [Fin.succ_castSucc]
        simp only [Q, g, Fin.snoc_castSucc]
        exact (hf j).2.1)
    (fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Q, g, Fin.snoc_castSucc, Fin.snoc_last]
        exact fun h => hv (hVx h)
      · simp only [Q, g, Fin.snoc_castSucc]
        exact (hf j).2.2)
    (fun c hc => by simpa [Q, m] using hc)
  refine ⟨g, e', fun i => ?_, by simp [e'], fun F hF => hinj F (by simpa [Q, V] using hF)⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [g, e'] using isHomogeneous_X k v
  · simpa [g, e'] using (hf j).1

end Spectrum

end MMP.Proofs.lem_mmp_foundation_projective_hilbert_function_lower

namespace MMP

open MMP.Proofs.lem_mmp_foundation_projective_hilbert_function_lower in
/-- **Lower bound for the projective Hilbert function.** If `Z` is a closed subset of
`Proj k[Xᵢ | i ∈ σ]` of dimension `d`, then for some `c > 0` the degree-`n` part of
`k[X] ⧸ I(Z)` has dimension at least `c · nᵈ` over `k` for all large `n`. -/
@[mmp "lem_mmp_foundation_projective_hilbert_function_lower"]
public theorem exists_mul_pow_le_finrank_map_homogeneousSubmodule_vanishingIdeal
    {k : Type*} [Field k] {σ : Type*} [Finite σ]
    {Z : Set (ProjectiveSpectrum (homogeneousSubmodule σ k))} (hZ : IsClosed Z)
    {d : ℕ} (hdim : topologicalKrullDim Z = d) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      c * (n : ℝ) ^ d ≤
        Module.finrank k ((homogeneousSubmodule σ k n).map
          (Ideal.Quotient.mkₐ k (ProjectiveSpectrum.vanishingIdeal Z).toIdeal).toLinearMap) := by
  obtain ⟨l₀, hl₀⟩ := Order.le_krullDim_iff.mp (show (d : WithBot ℕ∞) ≤
    Order.krullDim (TopologicalSpace.IrreducibleCloseds Z) from hdim.symm.le)
  let l := l₀.map _ (TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing
    Topology.IsInducing.subtypeVal)
  have hl : l.length = d := hl₀
  subst hl
  set d := l.length
  let C : Fin (d + 1) → Set (ProjectiveSpectrum (homogeneousSubmodule σ k)) := fun i => l i
  have hCZ : C (Fin.last d) ⊆ Z := by
    change closure (Subtype.val '' _) ⊆ Z
    exact closure_minimal (by rintro _ ⟨z, -, rfl⟩; exact z.2) hZ
  have hCss : ∀ i : Fin d, C i.castSucc ⊂ C i.succ := l.step
  obtain ⟨g, e, hg, he, hinj⟩ := exists_isHomogeneous_aeval_injective C
    (fun i => (l i).isIrreducible) (fun i => (l i).isClosed) hCss
  obtain ⟨c, hc, hc'⟩ := exists_mul_pow_le_finrank_of_aeval_injective _ _
    (ProjectiveSpectrum.vanishingIdeal_anti_mono _ hCZ) g e hg he hinj
  exact ⟨c, hc, 0, fun n _ => hc' n⟩

end MMP

end

/-!
# Relative coordinates for a smooth morphism

Let `f : Y ⟶ X` be a smooth morphism of relative dimension `d` between smooth schemes over a
field `k`, let `y ∈ Y`, and let `x₁, …, xₙ` be local coordinates on an open `U ∋ f y` of `X`
(the differentials `dxᵢ` form a basis of `Ω_{U/k}`). Then there are an open `V ∋ y` with
`V ⊆ f⁻¹ U` and sections `t₁, …, t_d ∈ 𝒪_Y(V)` such that `f^*x₁, …, f^*xₙ, t₁, …, t_d` are
local coordinates on `V`. For `f` étale one has `d = 0`, and the pulled-back coordinates alone
are local coordinates near `y`.

## Main results

* `MMP.Resolution.exists_isLocalCoordinatesOn_append_of_smoothOfRelativeDimension`.

## Implementation notes

The structure maps are `sX : X ⟶ Spec k` and `sY : Y ⟶ Spec k` with `f ≫ sX = sY`. The pulled
back coordinate `f^*xᵢ` is `(f.appLE U V hV).hom (x i)`, and the combined tuple is
`Fin.append`, indexed by `Fin (n + d)`. The étale case is the instance
`SmoothOfRelativeDimension 0 f` of an étale `f`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Def. 3.73]
-/

section

universe u

open AlgebraicGeometry CategoryTheory KaehlerDifferential

namespace MMP.Proofs.lem_mmp_foundation_smooth_relative_differential_coordinates

/-- For `R → A → B` with `A → B` formally smooth, `B ⊗[A] Ω_{A/R} → Ω_{B/R}` is injective: its
kernel is the image of `H¹(L_{B/A})`, which vanishes. -/
private theorem injective_mapBaseChange_of_formallySmooth (R A B : Type u) [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] : Function.Injective (mapBaseChange R A B) := by
  have : Subsingleton (Algebra.H1Cotangent A B) :=
    ((Algebra.formallySmooth_iff A B).mp inferInstance).2
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro z hz
  obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B z).mp hz
  rw [Subsingleton.elim w 0, map_zero] at hw
  simp [← hw]

/-- Let `k → A → B` with `A → B` formally smooth. If the `d aᵢ` are a basis of `Ω_{A/k}` and the
`d tⱼ` are a basis of `Ω_{B/A}`, then the `d aᵢ` and the `d tⱼ` together are a basis of
`Ω_{B/k}`. -/
private theorem exists_basis_kaehler_sumElim {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B]
    {ι κ : Type*} (bA : Module.Basis ι A Ω[A⁄R]) (a : ι → A) (hA : ∀ i, bA i = D R A (a i))
    (bB : Module.Basis κ B Ω[B⁄A]) (t : κ → B) (hB : ∀ j, bB j = D A B (t j)) :
    ∃ b : Module.Basis (ι ⊕ κ) B Ω[B⁄R],
      ∀ i, b i = D R B (Sum.elim (fun i ↦ algebraMap A B (a i)) t i) := by
  have hinj := injective_mapBaseChange_of_formallySmooth R A B
  have hex := exact_mapBaseChange_map R A B
  have hsurj := map_surjective R A B
  let M' := LinearMap.range (mapBaseChange R A B)
  let bT := bA.baseChange B
  have hbT : ∀ i, mapBaseChange R A B (bT i) = D R B (algebraMap A B (a i)) := by
    intro i
    simp [bT, mapBaseChange_tmul, hA]
  let f : ι → M' := fun i ↦ ⟨mapBaseChange R A B (bT i), LinearMap.mem_range_self _ _⟩
  have hf : LinearIndependent B f := by
    have := bT.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hinj)
    exact LinearIndependent.of_comp M'.subtype this
  have hle : M' ≤ LinearMap.ker (map R A B B) := by
    rintro _ ⟨z, rfl⟩
    exact hex.apply_apply_eq_zero z
  let L := M'.liftQ (map R A B B) hle
  have hg : LinearIndependent B (Submodule.Quotient.mk (p := M') ∘ (fun j ↦ D R B (t j))) := by
    apply LinearIndependent.of_comp L
    have heq : (L ∘ (Submodule.Quotient.mk (p := M') ∘ fun j ↦ D R B (t j))) = ⇑bB := by
      funext j
      simp [L, hB]
    exact heq ▸ bB.linearIndependent
  have hli := hf.sumElim_of_quotient _ hg
  have hsp : ⊤ ≤ Submodule.span B (Set.range (Sum.elim (fun i ↦ (f i : Ω[B⁄R]))
      (fun j ↦ D R B (t j)))) := by
    intro ω _
    set S := Submodule.span B (Set.range (Sum.elim (fun i ↦ (f i : Ω[B⁄R]))
      (fun j ↦ D R B (t j))))
    have hM' : M' ≤ S := by
      rintro _ ⟨z, rfl⟩
      have hz : z ∈ Submodule.span B (Set.range bT) := bT.span_eq ▸ Submodule.mem_top
      have := Submodule.mem_map_of_mem (f := mapBaseChange R A B) hz
      rw [Submodule.map_span, ← Set.range_comp] at this
      refine Submodule.span_le.mpr ?_ this
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    let ω' := ∑ j ∈ (bB.repr (map R A B B ω)).support, bB.repr (map R A B B ω) j • D R B (t j)
    have hω' : ω' ∈ S := Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
    have hd : ω - ω' ∈ M' := by
      refine (hex _).mp ?_
      simp only [ω', map_sub, map_sum, map_smul, map_D]
      rw [sub_eq_zero]
      exact (bB.linearCombination_repr _).symm.trans (by simp [Finsupp.linearCombination_apply,
        Finsupp.sum, hB])
    simpa using S.add_mem (hM' hd) hω'
  refine ⟨Module.Basis.mk hli hsp, fun i ↦ ?_⟩
  rcases i with i | j
  · simp [f, hbT]
  · simp

/-- A chart of a morphism smooth of relative dimension `d` near `y`, with base inside a given open
neighbourhood `U` of `f y`. -/
private theorem exists_isStandardSmoothOfRelativeDimension_appLE {X Y : Scheme.{u}} (f : Y ⟶ X)
    {d : ℕ} [SmoothOfRelativeDimension d f] (y : Y) (U : X.Opens) (hfy : f y ∈ U) :
    ∃ (U' : X.Opens) (_ : IsAffineOpen U') (_ : U' ≤ U) (V : Y.Opens) (_ : IsAffineOpen V)
      (_ : y ∈ V) (e : V ≤ f ⁻¹ᵁ U'),
      RingHom.IsStandardSmoothOfRelativeDimension d (f.appLE U' V e).hom := by
  obtain ⟨U', hU', hfy', hU'U⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    X.isBasis_affineOpens hfy
  obtain ⟨V₁, hV₁, hy, e⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ f ⁻¹ᵁ U' from hfy')
  have hf := HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension d) f inferInstance
    ⟨U', hU'⟩ ⟨V₁, hV₁⟩ e
  rw [RingHom.locally_iff_isLocalization
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d))] at hf
  obtain ⟨s, hs, hfs⟩ := hf
  apply iSup_basicOpen_of_span_eq_top at hs
  have hmem : y ∈ (⨆ i ∈ (s : Set Γ(Y, V₁)), Y.basicOpen i) := by rw [hs]; exact hy
  rw [TopologicalSpace.Opens.mem_iSup] at hmem
  obtain ⟨r, hr⟩ := hmem
  rw [TopologicalSpace.Opens.mem_iSup] at hr
  obtain ⟨hr, hrs⟩ := hr
  refine ⟨U', hU', hU'U, Y.basicOpen r, hV₁.basicOpen r, hrs, (Y.basicOpen_le r).trans e, ?_⟩
  rw [← f.appLE_map e (homOfLE (Y.basicOpen_le r)).op]
  have : IsLocalization.Away r Γ(Y, Y.basicOpen r) := hV₁.isLocalization_basicOpen r
  exact hfs r hr _

/-- For `φ : Y ⟶ X` over `Spec k`, the map `φ.appLE` on sections is `k`-linear. -/
private theorem appLE_algebraMap {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} (φ : Y ⟶ X) (hφ : φ ≫ sX = sY)
    {W' : X.Opens} {W : Y.Opens} (hle : W ≤ φ ⁻¹ᵁ W') (c : k) :
    (φ.appLE W' W hle).hom (letI := MMP.Mori.sectionAlgebra sX W'; algebraMap k Γ(X, W') c) =
      (letI := MMP.Mori.sectionAlgebra sY W; algebraMap k Γ(Y, W) c) := by
  subst hφ
  have h := Scheme.Hom.appLE_comp_appLE φ sX ⊤ W' W (by simp) hle
  exact congrArg (fun t => ((Scheme.ΓSpecIso (.of k)).inv ≫ t).hom c) h

end MMP.Proofs.lem_mmp_foundation_smooth_relative_differential_coordinates

open MMP.Proofs.lem_mmp_foundation_smooth_relative_differential_coordinates in
/-- **Relative coordinates extend base coordinates.** If `f : Y ⟶ X` is smooth of relative
dimension `d` over `k` and `x : Fin n → Γ(X, U)` are local coordinates on an open `U ∋ f y`,
then on some open `V ∋ y` with `V ≤ f ⁻¹ᵁ U` there are `t : Fin d → Γ(Y, V)` such that the
pulled-back `f^*xᵢ` followed by the `tⱼ` are local coordinates on `V`. -/
@[mmp "lem_mmp_foundation_smooth_relative_differential_coordinates"]
public theorem MMP.Resolution.exists_isLocalCoordinatesOn_append_of_smoothOfRelativeDimension
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [Smooth sX] [Smooth sY]
    (f : Y ⟶ X) (hf : f ≫ sX = sY) (d : ℕ) [SmoothOfRelativeDimension d f]
    (y : Y) {U : X.Opens} {n : ℕ} (x : Fin n → Γ(X, U))
    (hx : MMP.Resolution.IsLocalCoordinatesOn sX U x) (hfy : f y ∈ U) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (hV : V ≤ f ⁻¹ᵁ U) (t : Fin d → Γ(Y, V)),
      MMP.Resolution.IsLocalCoordinatesOn sY V
        (Fin.append (fun i => (f.appLE U V hV).hom (x i)) t) := by
  classical
  obtain ⟨U', hU', hU'U, V, hV, hyV, e, hstd⟩ :=
    exists_isStandardSmoothOfRelativeDimension_appLE (d := d) f y U hfy
  have hVU : V ≤ f ⁻¹ᵁ U := e.trans (f.preimage_mono hU'U)
  letI := MMP.Mori.sectionAlgebra sX U'
  letI := MMP.Mori.sectionAlgebra sY V
  letI : Algebra Γ(X, U') Γ(Y, V) := (f.appLE U' V e).hom.toAlgebra
  have : IsScalarTower k Γ(X, U') Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq' (by ext c; exact (appLE_algebraMap f hf e c).symm)
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : Algebra.Smooth Γ(X, U') Γ(Y, V) :=
    HasRingHomProperty.appLE (P := @Smooth) f inferInstance ⟨U', hU'⟩ ⟨V, hV⟩ e
  have : Algebra.IsStandardSmoothOfRelativeDimension d Γ(X, U') Γ(Y, V) := hstd
  obtain ⟨ι, σ, _, _, P, hP⟩ := this.out
  have hcard : Nat.card ((Set.range P.map)ᶜ : Set ι) = d := by
    rw [Stacks.RelativeDifferentialStalkMap.natCard_compl_range_map P, ← hP]
    rfl
  let eqv : ((Set.range P.map)ᶜ : Set ι) ≃ Fin d := (Finite.equivFin _).trans (finCongr hcard)
  let bB := P.basisKaehler.reindex eqv
  let t : Fin d → Γ(Y, V) := fun j ↦ P.val (eqv.symm j)
  have hB : ∀ j, bB j = D Γ(X, U') Γ(Y, V) (t j) := by
    intro j
    simp [bB, t]
  obtain ⟨bA, hA⟩ := hx ⟨U', hU'⟩ hU'U
  obtain ⟨b, hb⟩ := exists_basis_kaehler_sumElim bA _ hA bB t hB
  let b' := b.reindex finSumFinEquiv
  have hb' : ∀ i, b' i = D k Γ(Y, V) (Fin.append (fun i => (f.appLE U V hVU).hom (x i)) t i) := by
    intro i
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    simp only [b', Module.Basis.reindex_apply, Equiv.symm_apply_apply, hb]
    rcases s with i | j
    · simp only [Sum.elim_inl, finSumFinEquiv_apply_left, Fin.append_left]
      congr 1
      rw [← f.map_appLE e (homOfLE hU'U).op]
      rfl
    · simp
  refine ⟨V, hyV, hVU, t, fun W hW ↦ ?_⟩
  exact MMP.Flips.ResolutionInputs.exists_basis_res sY hV W.2 hW _ b' hb'

end

/-!
# Smooth morphisms are locally open subschemes of one hypersurface

Let `A` be a finitely generated algebra over a field `k` and `h : Y ⟶ Spec A` a smooth
morphism. Near a point `y` where `h` has relative dimension `d`, `Y` is isomorphic over `Spec A`
to an open subscheme of the hypersurface `V(F) ⊆ 𝔸^{d+1}_A` cut out by one polynomial
`F ∈ A[z₀, …, z_d]`, on which the partial derivative `∂F/∂z_d` is invertible. All coefficients
of `F` lie in the given ring `A`: the base is not shrunk.

## Main results

* `MMP.exists_isOpenImmersion_spec_quotient_span_singleton_of_smooth`.

## Implementation notes

The relative dimension of `h` at `y` is expressed by an open neighbourhood `U` of `y` on which
`h` is smooth of relative dimension `d` (`AlgebraicGeometry.SmoothOfRelativeDimension`).
The hypersurface is `Spec (A[z₀, …, z_d] ⧸ (F))`, the open subscheme is the open immersion
`ι : Y₁ ⟶ Spec (A[z] ⧸ (F))`, and invertibility of `∂F/∂z_d` on it is invertibility of the
pullback of its class along `ι` in `Γ(Y₁, ⊤)`. The last variable `Fin.last d` plays the role
of `z_{d+1}`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, proof of 3.41]
-/

section

universe u

open AlgebraicGeometry CategoryTheory
open MvPolynomial

namespace MMP.Proofs.lem_mmp_foundation_smooth_locally_one_hypersurface

/-- `A[z₀, …, z_d] ≃ A[z₀, …, z_{d-1}][z_d]`, the last variable becoming the polynomial
variable. -/
private noncomputable def lastEquiv (A : Type*) [CommRing A] (d : ℕ) :
    MvPolynomial (Fin (d + 1)) A ≃ₐ[A] Polynomial (MvPolynomial (Fin d) A) :=
  (renameEquiv A (finRotate (d + 1))).trans (finSuccEquiv A d)

private lemma lastEquiv_X_last (A : Type*) [CommRing A] (d : ℕ) :
    lastEquiv A d (X (Fin.last d)) = Polynomial.X := by
  simp [lastEquiv, finRotate_last, finSuccEquiv_X_zero]

private lemma lastEquiv_X_castSucc (A : Type*) [CommRing A] (d : ℕ) (j : Fin d) :
    lastEquiv A d (X j.castSucc) = Polynomial.C (X j) := by
  simp [lastEquiv, finRotate_of_lt, Fin.castSucc_lt_last, finSuccEquiv_X_succ]

private lemma lastEquiv_pderiv_last (A : Type*) [CommRing A] (d : ℕ)
    (F : MvPolynomial (Fin (d + 1)) A) :
    lastEquiv A d (pderiv (Fin.last d) F) = Polynomial.derivative (lastEquiv A d F) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [show (C a : MvPolynomial (Fin (d + 1)) A) = algebraMap A _ a from rfl, AlgEquiv.commutes]
    simp [Polynomial.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    induction i using Fin.lastCases with
    | last => simp [hp, lastEquiv_X_last]; ring
    | cast j =>
      simp [hp, lastEquiv_X_castSucc, Pi.single_apply, Fin.castSucc_ne_last]; ring

/-- A standard étale algebra `T` over `A[t₁, …, t_d]` receives an open immersion of spectra
from one hypersurface `A[z₀, …, z_d] ⧸ (F)` along which `∂F/∂z_d` becomes a unit. -/
private lemma exists_hypersurface_of_isStandardEtale {A T : Type u} [CommRing A] [CommRing T]
    [Algebra A T] {d : ℕ} [Algebra (MvPolynomial (Fin d) A) T]
    [IsScalarTower A (MvPolynomial (Fin d) A) T]
    [Algebra.IsStandardEtale (MvPolynomial (Fin d) A) T] :
    ∃ (F : MvPolynomial (Fin (d + 1)) A)
      (ψ : (MvPolynomial (Fin (d + 1)) A ⧸ Ideal.span {F}) →ₐ[A] T),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) ∧
        IsUnit (ψ (Ideal.Quotient.mk _ (pderiv (Fin.last d) F))) := by
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation
    (R := MvPolynomial (Fin d) A) (S := T)
  set F : MvPolynomial (Fin (d + 1)) A := (lastEquiv A d).symm P.f
  let eq : (MvPolynomial (Fin (d + 1)) A ⧸ Ideal.span {F}) ≃ₐ[A] AdjoinRoot P.f :=
    Ideal.quotientEquivAlg _ _ (lastEquiv A d) (by
      rw [Ideal.map_span, Set.image_singleton]; simp [F])
  let S' := Localization.Away (AdjoinRoot.mk P.f P.g)
  let E : T ≃ₐ[A] S' := (P.equivRing.trans P.P.equivAwayAdjoinRoot).restrictScalars A
  let ψ : (MvPolynomial (Fin (d + 1)) A ⧸ Ideal.span {F}) →ₐ[A] T :=
    E.symm.toAlgHom.comp ((IsScalarTower.toAlgHom A (AdjoinRoot P.f) S').comp eq.toAlgHom)
  refine ⟨F, ψ, ?_, ?_⟩
  · have h1 : IsIso (CommRingCat.ofHom E.symm.toAlgHom.toRingHom) :=
      inferInstanceAs (IsIso E.symm.toRingEquiv.toCommRingCatIso.hom)
    have h2 : IsIso (CommRingCat.ofHom eq.toAlgHom.toRingHom) :=
      inferInstanceAs (IsIso eq.toRingEquiv.toCommRingCatIso.hom)
    have h3 := IsOpenImmersion.of_isLocalization (S := S') (AdjoinRoot.mk P.f P.g)
    have : ψ.toRingHom = E.symm.toAlgHom.toRingHom.comp
        ((algebraMap (AdjoinRoot P.f) S').comp eq.toAlgHom.toRingHom) := rfl
    rw [this, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp]
    infer_instance
  · have hF : eq (Ideal.Quotient.mk _ (pderiv (Fin.last d) F)) =
        AdjoinRoot.mk P.f (Polynomial.derivative P.f) := by
      change AdjoinRoot.mk P.f (lastEquiv A d (pderiv (Fin.last d) F)) = _
      rw [lastEquiv_pderiv_last, AlgEquiv.apply_symm_apply]
    change IsUnit (E.symm (algebraMap (AdjoinRoot P.f) S'
      (eq (Ideal.Quotient.mk _ (pderiv (Fin.last d) F)))))
    rw [hF]
    refine IsUnit.map _ ?_
    obtain ⟨p₁, p₂, n, e⟩ := P.cond
    have he := congr(algebraMap (AdjoinRoot P.f) S' (AdjoinRoot.mk P.f $e))
    simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_self, mul_zero, zero_mul,
      add_zero] at he
    have hg : IsUnit (algebraMap (AdjoinRoot P.f) S' (AdjoinRoot.mk P.f P.g) ^ n) :=
      (IsLocalization.Away.algebraMap_isUnit _).pow n
    rw [← he] at hg
    exact isUnit_of_mul_isUnit_left hg

/-- If `A → B` is standard smooth of relative dimension `d` and `q` is a prime of `B`, then some
`B_g` with `g ∉ q` receives an open immersion of spectra from one hypersurface
`A[z₀, …, z_d] ⧸ (F)` along which `∂F/∂z_d` becomes a unit. -/
private lemma exists_hypersurface_of_isStandardSmoothOfRelativeDimension {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] {d : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension d A B] (q : Ideal B) [q.IsPrime] :
    ∃ g ∉ q, ∃ (F : MvPolynomial (Fin (d + 1)) A)
      (ψ : (MvPolynomial (Fin (d + 1)) A ⧸ Ideal.span {F}) →ₐ[A] Localization.Away g),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) ∧
        IsUnit (ψ (Ideal.Quotient.mk _ (pderiv (Fin.last d) F))) := by
  obtain ⟨φ, hφ⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d A B
  algebraize [φ.toRingHom]
  have : IsScalarTower A (MvPolynomial (Fin d) A) B := .of_algebraMap_eq' φ.comp_algebraMap.symm
  have : Algebra.IsEtaleAt (MvPolynomial (Fin d) A) q := .of_isUnramifiedAt_of_flat q
  obtain ⟨g, hgq, hg⟩ := Algebra.IsEtaleAt.exists_isStandardEtale
    (R := MvPolynomial (Fin d) A) q
  have : IsScalarTower A (MvPolynomial (Fin d) A) (Localization.Away g) :=
    .of_algebraMap_eq' (by
      rw [IsScalarTower.algebraMap_eq A B (Localization.Away g),
        IsScalarTower.algebraMap_eq (MvPolynomial (Fin d) A) B (Localization.Away g),
        RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A (MvPolynomial (Fin d) A) B])
  exact ⟨g, hgq, exists_hypersurface_of_isStandardEtale⟩

/-- For `y ∈ W`, a section `g` over `W` is invertible near `y` iff `g` lies outside the prime of
`Γ(Y, W)` pulled back from the maximal ideal of the stalk at `y`. -/
private lemma mem_basicOpen_iff_notMem_comap {Y : Scheme.{u}} {W : Y.Opens} {y : Y}
    (hy : y ∈ W) (g : Γ(Y, W)) :
    y ∈ Y.basicOpen g ↔
      g ∉ (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap (Y.presheaf.germ W y hy).hom := by
  simp [Scheme.mem_basicOpen _ _ _ hy, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- The conclusion near `y`, given an affine open `W ∋ y` on which `Γ(Spec A) → Γ(Y, W)` is
standard smooth of relative dimension `d`. -/
private lemma exists_hypersurface_of_isAffineOpen {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of A)) {W : Y.Opens} (hW : IsAffineOpen W) (hWh : W ≤ h ⁻¹ᵁ ⊤) (y : Y)
    (hy : y ∈ W) {d : ℕ}
    (H : ((h.appLE ⊤ W hWh).hom.comp
      (Scheme.ΓSpecIso (.of A)).inv.hom).IsStandardSmoothOfRelativeDimension d) :
    ∃ (Y₁ : Y.Opens) (_ : y ∈ Y₁) (F : MvPolynomial (Fin (d + 1)) A)
      (ι : (Y₁ : Scheme) ⟶ Spec (.of (MvPolynomial (Fin (d + 1)) A ⧸ Ideal.span {F}))),
      IsOpenImmersion ι ∧
        ι ≫ Spec.map (CommRingCat.ofHom
            (algebraMap A (MvPolynomial (Fin (d + 1)) A ⧸ Ideal.span {F}))) = Y₁.ι ≫ h ∧
        IsUnit (ι.appTop ((Scheme.ΓSpecIso _).inv
          (Ideal.Quotient.mk _ (MvPolynomial.pderiv (Fin.last d) F)))) := by
  algebraize [(h.appLE ⊤ W hWh).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom]
  let q : Ideal Γ(Y, W) :=
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap (Y.presheaf.germ W y hy).hom
  obtain ⟨g, hgq, F, ψ, hψ, hunit⟩ := exists_hypersurface_of_isStandardSmoothOfRelativeDimension
    (A := A) (B := Γ(Y, W)) (d := d) q
  have hyg : y ∈ Y.basicOpen g := (mem_basicOpen_iff_notMem_comap hy g).mpr hgq
  have hWg := hW.basicOpen g
  have := hW.isLocalization_basicOpen g
  let e : Localization.Away g ≃ₐ[Γ(Y, W)] Γ(Y, Y.basicOpen g) :=
    IsLocalization.algEquiv (.powers g) _ _
  let ψ' := e.toRingEquiv.toRingHom.comp ψ.toRingHom
  refine ⟨Y.basicOpen g, hyg, F, hWg.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ'), ?_, ?_, ?_⟩
  · have h1 : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) :=
      inferInstanceAs (IsIso e.toRingEquiv.toCommRingCatIso.hom)
    rw [show CommRingCat.ofHom ψ' = CommRingCat.ofHom ψ.toRingHom ≫
      CommRingCat.ofHom e.toRingEquiv.toRingHom from rfl, Spec.map_comp]
    infer_instance
  · have hle : Y.basicOpen g ≤ h ⁻¹ᵁ ⊤ := by simp
    have hring : CommRingCat.ofHom (ψ'.comp
        (algebraMap A (MvPolynomial (Fin (d + 1)) A ⧸ Ideal.span {F}))) =
        (Scheme.ΓSpecIso (.of A)).inv ≫ h.appLE ⊤ (Y.basicOpen g) hle := by
      ext a
      change e (ψ (algebraMap A _ a)) = _
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A Γ(Y, W) (Localization.Away g),
        AlgEquiv.commutes]
      rw [← Scheme.Hom.appLE_map (i := (homOfLE (Y.basicOpen_le g)).op)]
      rfl
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring, Spec.map_comp,
      ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
      IsAffineOpen.SpecMap_appLE_fromSpec _ _ hWg, IsAffineOpen.isoSpec_hom_fromSpec_assoc]
  · rw [Scheme.Hom.comp_appTop]
    change IsUnit (hWg.isoSpec.hom.appTop
      ((Spec.map (CommRingCat.ofHom ψ')).appTop ((Scheme.ΓSpecIso _).inv _)))
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    exact ((hunit.map e).map _).map _

/-- A morphism `h : Y ⟶ Spec A` smooth of relative dimension `d` is, near any point, an open
subscheme of one hypersurface in `𝔸^{d+1}_A` on which `∂F/∂z_d` is invertible. -/
private lemma exists_hypersurface_of_smoothOfRelativeDimension {A : Type u} [CommRing A]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (.of A)) {d : ℕ} [SmoothOfRelativeDimension d h] (y : Y) :
    ∃ (Y₁ : Y.Opens) (_ : y ∈ Y₁) (F : MvPolynomial (Fin (d + 1)) A)
      (ι : (Y₁ : Scheme) ⟶ Spec (.of (MvPolynomial (Fin (d + 1)) A ⧸ Ideal.span {F}))),
      IsOpenImmersion ι ∧
        ι ≫ Spec.map (CommRingCat.ofHom
            (algebraMap A (MvPolynomial (Fin (d + 1)) A ⧸ Ideal.span {F}))) = Y₁.ι ≫ h ∧
        IsUnit (ι.appTop ((Scheme.ΓSpecIso _).inv
          (Ideal.Quotient.mk _ (MvPolynomial.pderiv (Fin.last d) F)))) := by
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have hle : W ≤ h ⁻¹ᵁ ⊤ := by simp
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d)
      (h.appLE ⊤ W hle).hom :=
    HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension d) h ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ hle
  have hloc' : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d)
      ((h.appLE ⊤ W hle).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom) := (RingHom.locally_respectsIso
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d))).right (h.appLE ⊤ W hle).hom
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv hloc
  rw [RingHom.locally_iff_isLocalization
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d))] at hloc'
  obtain ⟨s, hs, hst⟩ := hloc'
  let q : Ideal Γ(Y, W) :=
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap (Y.presheaf.germ W y hyW).hom
  obtain ⟨t, hts, htq⟩ : ∃ t ∈ s, t ∉ q := by
    by_contra! H
    exact Ideal.IsPrime.ne_top inferInstance (top_le_iff.mp (hs ▸ Ideal.span_le.mpr H))
  have hyt : y ∈ Y.basicOpen t := (mem_basicOpen_iff_notMem_comap hyW t).mpr htq
  have := hW.isLocalization_basicOpen t
  have H := hst t hts Γ(Y, Y.basicOpen t)
  refine exists_hypersurface_of_isAffineOpen h (hW.basicOpen t) ((Y.basicOpen_le t).trans hle) y hyt
    ?_
  convert H using 1
  rw [← Scheme.Hom.appLE_map h hle (homOfLE (Y.basicOpen_le t)).op]
  rfl

end MMP.Proofs.lem_mmp_foundation_smooth_locally_one_hypersurface

namespace MMP

open MMP.Proofs.lem_mmp_foundation_smooth_locally_one_hypersurface in
/-- A smooth morphism `h : Y ⟶ Spec A`, with `A` of finite type over a field, is near a point
`y` of relative dimension `d` an open subscheme of one hypersurface: there are an open
`Y₁ ∋ y`, `F ∈ A[z₀, …, z_d]` and an open immersion `ι : Y₁ ⟶ Spec (A[z] ⧸ (F))` over
`Spec A` along which `∂F/∂z_d` becomes a unit of `Γ(Y₁, ⊤)`. -/
@[mmp "lem_mmp_foundation_smooth_locally_one_hypersurface"]
public theorem exists_isOpenImmersion_spec_quotient_span_singleton_of_smooth
    (k : Type u) [Field k] {A : Type u} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (.of A)) [Smooth h] (y : Y) (d : ℕ) (U : Y.Opens)
    (hyU : y ∈ U) [SmoothOfRelativeDimension d (U.ι ≫ h)] :
    ∃ (Y₁ : Y.Opens) (_ : y ∈ Y₁) (F : MvPolynomial (Fin (d + 1)) A)
      (ι : (Y₁ : Scheme) ⟶ Spec (.of (MvPolynomial (Fin (d + 1)) A ⧸ Ideal.span {F}))),
      IsOpenImmersion ι ∧
        ι ≫ Spec.map (CommRingCat.ofHom
            (algebraMap A (MvPolynomial (Fin (d + 1)) A ⧸ Ideal.span {F}))) = Y₁.ι ≫ h ∧
        IsUnit (ι.appTop ((Scheme.ΓSpecIso _).inv
          (Ideal.Quotient.mk _ (MvPolynomial.pderiv (Fin.last d) F)))) := by
  obtain ⟨Y₁, hy₁, F, ι, hι, hcomm, hunit⟩ :=
    exists_hypersurface_of_smoothOfRelativeDimension (d := d) (U.ι ≫ h) ⟨y, hyU⟩
  refine ⟨U.ι ''ᵁ Y₁, ⟨⟨y, hyU⟩, hy₁, rfl⟩, F, (U.ι.isoImage Y₁).inv ≫ ι, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hcomm, Scheme.Hom.isoImage_inv_ι_assoc]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    exact hunit.map _

end MMP

end

/-!
# Smooth proper surfaces over a field are projective

Let `k` be a field and `X` a scheme with a smooth proper structure morphism `X ⟶ Spec k`,
of dimension two. Then `X` is projective over `k` in the fixed-projective-space sense:
there are `N` and a closed immersion `X ⟶ ℙᴺ_k` over `Spec k`. No hypothesis on `k`
(algebraic closedness, characteristic) is needed.

## Main results

* `MMP.isProjectiveMorphism_of_smooth_of_isProper_of_topologicalKrullDim_eq_two`

## Implementation notes

Projectivity is `AlgebraicGeometry.IsProjectiveMorphism`, a closed immersion into
`projectiveSpaceOver N (Spec k)` commuting with the structure maps. A surface is taken to be
a scheme of topological Krull dimension two; integrality is not assumed.

## References

* [Stacks, Tag 0C5P]
-/

section

open AlgebraicGeometry

namespace MMP

/-- A smooth proper scheme of dimension two over a field `k` is projective over `k`: it admits
a closed immersion into some projective space `ℙᴺ_k` over `Spec k`. -/
@[mmp "lem_mmp_foundation_smooth_proper_surface_projective"]
public theorem isProjectiveMorphism_of_smooth_of_isProper_of_topologicalKrullDim_eq_two
    {k : Type*} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f]
    (hdim : topologicalKrullDim X = 2) : IsProjectiveMorphism f := by
  have hreg : IsRegular X := (isRegular_iff_regular_stalks X).2
    ⟨LocallyOfFiniteType.isLocallyNoetherian f,
      fun x => isRegularLocalRing_stalk_of_smooth_over_field f x⟩
  exact isProjectiveMorphism_of_isProjective_of_isAffine f
    (isProjective_of_isRegular_of_topologicalKrullDim_le_two f hreg hdim.le)

end MMP

end

/-!
# Edge maps of a double complex with exact augmented rows and columns

Let `K` be a first-quadrant double complex in an abelian category, i.e. a
`HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)` whose objects
`(K.X p).X q` are the `C^{p,q}`. Its horizontal differential goes `C^{p,q} → C^{p+1,q}` and its
vertical differential goes `C^{p,q} → C^{p,q+1}`. Let `K.total (ComplexShape.up ℕ)` be its total
complex, with differential `d_h + (-1)^p d_v`. Let `A` be a cochain complex with a map
`φ : A ⟶ K.flip.X 0` to the bottom row such that every augmented column
`0 → A^p → C^{p,0} → C^{p,1} → ⋯` is exact. Let `B` be a cochain complex with a map
`ψ : B ⟶ K.X 0` to the left column such that every augmented row
`0 → B^q → C^{0,q} → C^{1,q} → ⋯` is exact. Then the composites of `φ` and `ψ` with the
inclusions into the total complex are quasi-isomorphisms. In particular,
`H^n(A) ≅ H^n(K.total) ≅ H^n(B)`.

## Main results

* `MMP.Homology.exists_quasiIso_total_of_acyclic_augment`.

## Implementation notes

The exactness of the augmented column `p` is the acyclicity of
`CochainComplex.augment (K.X p) (φ.f p) (hφ p)`, where `hφ p` says that the composite
`A^p → C^{p,0} → C^{p,1}` is zero. Its exactness in degree `0` is the injectivity of
`A^p → C^{p,0}`. Rows are handled in the same way through `K.flip`.

The maps to the total complex are given by their components `φ.f p ≫ K.ιTotal _ p 0 p _` and
`ψ.f q ≫ K.ιTotal _ 0 q q _`. So the cohomology isomorphism `H^n(A) ≅ H^n(B)` is induced by
explicit cochain maps, and it is natural for maps of the data by functoriality of
`HomologicalComplex.homologyMap`.

The source works with abelian groups; the statement is made in an arbitrary abelian category.

The total complex is formed with the `TotalComplexShape` that a `ComplexShape.TensorSigns`
structure on `ComplexShape.up ℕ` provides. Such a structure is unique: `ε 0 = 1` and
`ε (p + 1) = - ε p` force `ε p = (-1) ^ p`. It is therefore taken as an instance argument, and the
differential of the total complex is `d_h + (-1)^p d_v`.
-/

section

open CategoryTheory Limits HomologicalComplex₂

namespace MMP.Proofs.lem_mmp_gaga_double_complex_edge

section

variable {C : Type*} [Category C] [Abelian C] [(ComplexShape.up ℕ).TensorSigns]
  (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
  [K.HasTotal (ComplexShape.up ℕ)]

local notation "T" => K.total (ComplexShape.up ℕ)

/-- The projection of the total complex onto the summand `(p, q)`. -/
private noncomputable def pr (p q N : ℕ) : (T).X N ⟶ (K.X p).X q :=
  K.totalDesc fun p' q' _ =>
    if h : p' = p ∧ q' = q then eqToHom (by rw [h.1, h.2]) else 0

@[reassoc]
private lemma ι_pr (p q N : ℕ) (h : p + q = N) :
    K.ιTotal (ComplexShape.up ℕ) p q N h ≫ pr K p q N = 𝟙 _ := by
  simp [pr]

@[reassoc]
private lemma ι_pr_of_ne (p q p' q' N : ℕ) (h : p + q = N) (hpq : ¬ (p = p' ∧ q = q')) :
    K.ιTotal (ComplexShape.up ℕ) p q N h ≫ pr K p' q' N = 0 := by
  simp [pr, hpq]

/-- The formula for the differential of the total complex followed by a projection. -/
private lemma ι_d_pr (p q p' q' M : ℕ) (h : p + q = M) :
    K.ιTotal (ComplexShape.up ℕ) p q M h ≫ (T).d M (M + 1) ≫ pr K p' q' (M + 1) =
      (if hp : p + 1 = p' ∧ q = q' then
        (K.d p (p + 1)).f q ≫ eqToHom (by rw [hp.1, hp.2]) else 0) +
      (if hq : p = p' ∧ q + 1 = q' then
        (ComplexShape.up ℕ).ε p • ((K.X p).d q (q + 1) ≫ eqToHom (by rw [hq.1, hq.2])) else 0) := by
  rw [total_d, Preadditive.add_comp, Preadditive.comp_add, ι_D₁_assoc, ι_D₂_assoc,
    K.d₁_eq (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl) q (M + 1)
      (by simp; omega),
    K.d₂_eq (ComplexShape.up ℕ) p (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl) (M + 1)
      (by simp; omega)]
  congr 1
  · split_ifs with hp
    · obtain ⟨rfl, rfl⟩ := hp
      simp [ι_pr]
    · simp [ι_pr_of_ne K _ _ _ _ _ _ hp]
  · split_ifs with hq
    · obtain ⟨rfl, rfl⟩ := hq
      simp [ι_pr]
    · simp [ι_pr_of_ne K _ _ _ _ _ _ hq]

private lemma sum_pr_ι (N : ℕ) :
    ∑ i : Fin (N + 1), pr K i (N - i) N ≫ K.ιTotal (ComplexShape.up ℕ) i (N - i) N
      (by simp; omega) = 𝟙 _ := by
  ext p q h
  change p + q = N at h
  rw [Preadditive.comp_sum, Category.comp_id,
    Finset.sum_eq_single ⟨p, by omega⟩]
  · obtain rfl : q = N - p := by omega
    rw [← Category.assoc, ι_pr, Category.id_comp]
  · intro i _ hi
    rw [← Category.assoc, ι_pr_of_ne, zero_comp]
    rintro ⟨h1, -⟩
    exact hi (Fin.ext h1.symm)
  · simp

private lemma hom_ext_pr {X : C} {N : ℕ} {f g : X ⟶ (T).X N}
    (h : ∀ p q, p + q = N → f ≫ pr K p q N = g ≫ pr K p q N) : f = g := by
  rw [← Category.comp_id f, ← Category.comp_id g, ← sum_pr_ι, Preadditive.comp_sum,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Category.assoc, ← Category.assoc, h i (N - i) (by omega)]

private lemma d_pr (r q M : ℕ) (h : r + q = M) :
    (T).d M (M + 1) ≫ pr K r (q + 1) (M + 1) =
      (ComplexShape.up ℕ).ε r • (pr K r q M ≫ (K.X r).d q (q + 1)) +
        (if 0 < r then pr K (r - 1) (q + 1) M ≫ (K.d (r - 1) r).f (q + 1) else 0) := by
  ext p q' h'
  change p + q' = M at h'
  rw [ι_d_pr K p q' r (q + 1) M h', Preadditive.comp_add]
  by_cases hp : p = r
  · subst hp
    obtain rfl : q' = q := by omega
    simp [ι_pr_of_ne, ι_pr_of_ne_assoc, ι_pr_assoc]
    split_ifs
    · rw [ι_pr_of_ne_assoc K _ _ _ _ _ _ (by omega), zero_comp]
    · simp
  · by_cases hp' : p + 1 = r
    · subst hp'
      obtain rfl : q' = q + 1 := by omega
      simp [ι_pr_of_ne, ι_pr_of_ne_assoc, ι_pr_assoc]
    · simp [ι_pr_of_ne, ι_pr_of_ne_assoc, hp, hp']
      split_ifs
      · rw [ι_pr_of_ne_assoc K _ _ _ _ _ _ (by omega), zero_comp]
      · simp

private lemma ι_d_pr_h (p q M : ℕ) (h : p + q = M) :
    K.ιTotal (ComplexShape.up ℕ) p q M h ≫ (T).d M (M + 1) ≫ pr K (p + 1) q (M + 1) =
      (K.d p (p + 1)).f q := by
  simp [ι_d_pr]

private lemma ι_d_pr_v (p q M : ℕ) (h : p + q = M) :
    K.ιTotal (ComplexShape.up ℕ) p q M h ≫ (T).d M (M + 1) ≫ pr K p (q + 1) (M + 1) =
      (ComplexShape.up ℕ).ε p • (K.X p).d q (q + 1) := by
  simp [ι_d_pr]

private lemma ι_d_pr_eq_zero (p q p' q' M : ℕ) (h : p + q = M)
    (h₁ : ¬ (p + 1 = p' ∧ q = q')) (h₂ : ¬ (p = p' ∧ q + 1 = q')) :
    K.ιTotal (ComplexShape.up ℕ) p q M h ≫ (T).d M (M + 1) ≫ pr K p' q' (M + 1) = 0 := by
  simp [ι_d_pr, h₁, h₂]

/-- A morphism to `T^N` whose components in the columns `p < r` vanish. -/
private def ColGe {X : C} {N : ℕ} (r : ℕ) (t : X ⟶ (T).X N) : Prop :=
  ∀ p q, p < r → p + q = N → t ≫ pr K p q N = 0

variable (A : CochainComplex C ℕ) (φ : ∀ p, A.X p ⟶ (K.X p).X 0)
    (hφc : ∀ p, φ p ≫ (K.d p (p + 1)).f 0 = A.d p (p + 1) ≫ φ (p + 1))
    (hφ : ∀ p, φ p ≫ (K.X p).d 0 1 = 0)
    (hA : ∀ p, (CochainComplex.augment (K.X p) (φ p) (hφ p)).Acyclic)

include hA in
private lemma col_exact_succ (r q : ℕ) {X : C} (x : X ⟶ (K.X r).X (q + 1))
    (hx : x ≫ (K.X r).d (q + 1) (q + 2) = 0) :
    ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π) (s : X' ⟶ (K.X r).X q),
      π ≫ x = s ≫ (K.X r).d q (q + 1) := by
  have := hA r (q + 2)
  rw [HomologicalComplex.exactAt_iff_exact_up_to_refinements _ (q + 1) (q + 2) (q + 3)
    (by simp) (by simp)] at this
  exact this x hx

include hA in
private lemma col_exact_zero (r : ℕ) {X : C} (x : X ⟶ (K.X r).X 0)
    (hx : x ≫ (K.X r).d 0 1 = 0) :
    ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π) (a : X' ⟶ A.X r), π ≫ x = a ≫ φ r := by
  have := hA r 1
  rw [HomologicalComplex.exactAt_iff_exact_up_to_refinements _ 0 1 2
    (by simp) (by simp)] at this
  exact this x hx

include hA in
private lemma col_mono (r : ℕ) : Mono (φ r) := by
  have := hA r 0
  rw [HomologicalComplex.exactAt_iff_exact_up_to_refinements _ 0 0 1
    (by simp) (by simp)] at this
  refine Preadditive.mono_of_cancel_zero _ fun {X} x hx => ?_
  obtain ⟨X', π, hπ, y, hy⟩ := this x hx
  rw [← cancel_epi π, comp_zero]
  exact hy.trans (by rw [HomologicalComplex.shape _ 0 0 (by simp), comp_zero]; rfl)

include hA in
/-- One reduction step: the component of `t` of vertical degree `q + 1` in column `r` is
killed by subtracting a coboundary. -/
private lemma exists_colGe_succ_sub_comp_d {X : C} (r q M : ℕ) (h : r + q = M)
    (t : X ⟶ (T).X (M + 1)) (ht : ColGe K r t)
    (hdt : (t ≫ (T).d (M + 1) (M + 2)) ≫ pr K r (q + 2) (M + 2) = 0) :
    ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π) (s : X' ⟶ (T).X M),
      ColGe K (r + 1) (π ≫ t - s ≫ (T).d M (M + 1)) := by
  rw [Category.assoc, d_pr K r (q + 1) (M + 1) (by omega), Preadditive.comp_add] at hdt
  have hx : t ≫ pr K r (q + 1) (M + 1) ≫ (K.X r).d (q + 1) (q + 2) = 0 := by
    refine (smul_eq_zero_iff_eq ((ComplexShape.up ℕ).ε r)).1 ?_
    rw [← Linear.comp_units_smul]
    split_ifs at hdt with hr
    · rwa [← Category.assoc t, ht (r - 1) (q + 2) (by omega) (by omega), zero_comp,
        add_zero] at hdt
    · rwa [comp_zero, add_zero] at hdt
  obtain ⟨X', π, hπ, s₀, hs₀⟩ := col_exact_succ K A φ hφ hA r q _
    (by rw [Category.assoc]; exact hx)
  refine ⟨X', π, hπ, ((ComplexShape.up ℕ).ε r)⁻¹ •
    (s₀ ≫ K.ιTotal (ComplexShape.up ℕ) r q M h), fun p q' hp hpq => ?_⟩
  simp only [Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc]
  by_cases hpr : p = r
  · subst hpr
    obtain rfl : q' = q + 1 := by omega
    rw [ι_d_pr_v, Linear.comp_units_smul, smul_smul, inv_mul_cancel, one_smul,
      hs₀, sub_self]
  · rw [ht p q' (by omega) hpq, comp_zero, ι_d_pr_eq_zero K _ _ _ _ _ _ (by omega) (by omega),
      comp_zero, smul_zero, sub_zero]

include hA in
private lemma exists_colGe_sub_comp_d {X : C} (M : ℕ) (t : X ⟶ (T).X (M + 1))
    (hdt : ColGe K (M + 1) (t ≫ (T).d (M + 1) (M + 2))) :
    ∀ r ≤ M + 1, ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π) (s : X' ⟶ (T).X M),
      ColGe K r (π ≫ t - s ≫ (T).d M (M + 1)) := by
  intro r
  induction r with
  | zero => exact fun _ => ⟨X, 𝟙 X, inferInstance, 0, fun p _ hp _ => absurd hp (by omega)⟩
  | succ r ih =>
    intro hr
    obtain ⟨X', π, hπ, s, hs⟩ := ih (by omega)
    obtain ⟨X'', π', hπ', s', hs'⟩ :=
      exists_colGe_succ_sub_comp_d K A φ hφ hA r (M - r) M (by omega) _ hs (by
      rw [Preadditive.sub_comp, Category.assoc, Category.assoc, HomologicalComplex.d_comp_d,
        comp_zero, sub_zero, Category.assoc, hdt r (M - r + 2) (by omega) (by omega),
        comp_zero])
    refine ⟨X'', π' ≫ π, epi_comp _ _, π' ≫ s + s', ?_⟩
    convert hs' using 1
    simp only [Preadditive.comp_sub, Preadditive.add_comp, Category.assoc]
    abel

private lemma eq_of_colGe {X : C} {N : ℕ} (t : X ⟶ (T).X N) (ht : ColGe K N t) :
    t = (t ≫ pr K N 0 N) ≫ K.ιTotal (ComplexShape.up ℕ) N 0 N (add_zero N) := by
  apply hom_ext_pr K
  intro p q h
  by_cases hp : p < N
  · rw [ht p q hp h, Category.assoc, ι_pr_of_ne K _ _ _ _ _ _ (by omega), comp_zero]
  · obtain rfl : p = N := by omega
    obtain rfl : q = 0 := by omega
    rw [Category.assoc, ι_pr, Category.comp_id]

include hφc hφ in
/-- The map from `A` to the total complex through the bottom row. -/
private noncomputable def toTotal : A ⟶ T where
  f p := φ p ≫ K.ιTotal (ComplexShape.up ℕ) p 0 p (add_zero p)
  comm' := by
    rintro i _ rfl
    apply hom_ext_pr K
    intro p q h
    simp only [Category.assoc]
    by_cases h1 : p = i + 1
    · subst h1
      obtain rfl : q = 0 := by omega
      rw [ι_d_pr_h, ι_pr, Category.comp_id, hφc]
    · by_cases h2 : p = i
      · subst h2
        obtain rfl : q = 1 := by omega
        rw [ι_d_pr_v, Linear.comp_units_smul, hφ, smul_zero,
          ι_pr_of_ne K _ _ _ _ _ _ (by omega), comp_zero, comp_zero]
      · rw [ι_d_pr_eq_zero K _ _ _ _ _ _ (by omega) (by omega),
          ι_pr_of_ne K _ _ _ _ _ _ (by omega), comp_zero, comp_zero, comp_zero]

private lemma toTotal_f (p : ℕ) :
    (toTotal K A φ hφc hφ).f p = φ p ≫ K.ιTotal (ComplexShape.up ℕ) p 0 p (add_zero p) := rfl

private lemma comp_d_pr_v {X : C} (p q M : ℕ) (h : p + q = M) (z : X ⟶ (K.X p).X q)
    (hz : ((z ≫ K.ιTotal (ComplexShape.up ℕ) p q M h) ≫ (T).d M (M + 1)) ≫
      pr K p (q + 1) (M + 1) = 0) :
    z ≫ (K.X p).d q (q + 1) = 0 := by
  rw [Category.assoc, Category.assoc, ι_d_pr_v, Linear.comp_units_smul] at hz
  exact (smul_eq_zero_iff_eq _).1 hz

include hA in
private lemma exists_cocycle_lift_of_colGe {X : C} (n : ℕ) (t : X ⟶ (T).X n) (ht : ColGe K n t)
    (hdt : t ≫ (T).d n (n + 1) = 0) :
    ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π) (a : X' ⟶ A.X n),
      a ≫ A.d n (n + 1) = 0 ∧ π ≫ t = a ≫ (toTotal K A φ hφc hφ).f n := by
  have htz := eq_of_colGe K t ht
  rw [htz] at hdt
  have hv : (t ≫ pr K n 0 n) ≫ (K.X n).d 0 1 = 0 :=
    comp_d_pr_v K n 0 n _ _ (by rw [hdt, zero_comp])
  have hh : t ≫ pr K n 0 n ≫ (K.d n (n + 1)).f 0 = 0 := by
    have := congrArg (· ≫ pr K (n + 1) 0 (n + 1)) hdt
    simpa only [Category.assoc, ι_d_pr_h, zero_comp] using this
  obtain ⟨X', π, hπ, a, hb⟩ := col_exact_zero K A φ hφ hA n _ hv
  refine ⟨X', π, hπ, a, ?_, ?_⟩
  · have := col_mono K A φ hφ hA (n + 1)
    rw [← cancel_mono (φ (n + 1)), zero_comp, Category.assoc, ← hφc, ← reassoc_of% hb, hh,
      comp_zero]
  · rw [toTotal_f, ← Category.assoc a, ← hb]
    nth_rewrite 1 [htz]
    simp only [Category.assoc]

include hA in
private lemma exists_comp_d_eq_of_colGe {X : C} (m : ℕ) (u : X ⟶ (T).X m) (hu : ColGe K m u)
    (x : X ⟶ A.X (m + 1))
    (hux : u ≫ (T).d m (m + 1) = x ≫ (toTotal K A φ hφc hφ).f (m + 1)) :
    ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π) (b : X' ⟶ A.X m), π ≫ x = b ≫ A.d m (m + 1) := by
  have huw := eq_of_colGe K u hu
  rw [huw, toTotal_f] at hux
  have hv : (u ≫ pr K m 0 m) ≫ (K.X m).d 0 1 = 0 :=
    comp_d_pr_v K m 0 m _ _ (by
      rw [hux, Category.assoc, Category.assoc, ι_pr_of_ne K _ _ _ _ _ _ (by omega), comp_zero,
        comp_zero])
  have hh : u ≫ pr K m 0 m ≫ (K.d m (m + 1)).f 0 = x ≫ φ (m + 1) := by
    have := congrArg (· ≫ pr K (m + 1) 0 (m + 1)) hux
    simpa only [Category.assoc, ι_d_pr_h, ι_pr, Category.comp_id] using this
  obtain ⟨X', π, hπ, b, hb⟩ := col_exact_zero K A φ hφ hA m _ hv
  refine ⟨X', π, hπ, b, ?_⟩
  have := col_mono K A φ hφ hA (m + 1)
  rw [← cancel_mono (φ (m + 1))]
  simp only [Category.assoc]
  rw [← hh, ← hφc, ← reassoc_of% hb]

include hA in
private lemma quasiIso_toTotal : QuasiIso (toTotal K A φ hφc hφ) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hepi : Epi (HomologicalComplex.homologyMap (toTotal K A φ hφc hφ) n) := by
    rcases n with _ | m
    · rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements _ 0 0 1 (by simp) (by simp)]
      intro X y hy
      obtain ⟨X', π, hπ, a, ha, he⟩ :=
        exists_cocycle_lift_of_colGe K A φ hφc hφ hA 0 y (fun p _ hp _ => absurd hp (by omega)) hy
      exact ⟨X', π, hπ, a, ha, 0, by rw [he, zero_comp, add_zero]⟩
    · rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements _ m (m + 1) (m + 2)
        (by simp) (by simp)]
      intro X y hy
      obtain ⟨X', π, hπ, s, hs⟩ := exists_colGe_sub_comp_d K A φ hφ hA m y
        (by rw [hy]; intro p q _ _; exact zero_comp) (m + 1) le_rfl
      obtain ⟨X'', π', hπ', a, ha, he⟩ :=
        exists_cocycle_lift_of_colGe K A φ hφc hφ hA (m + 1) _ hs (by
        rw [Preadditive.sub_comp, Category.assoc, hy, comp_zero, Category.assoc,
          HomologicalComplex.d_comp_d, comp_zero, sub_zero])
      refine ⟨X'', π' ≫ π, epi_comp _ _, a, ha, π' ≫ s, ?_⟩
      rw [← he]
      simp only [Preadditive.comp_sub, Category.assoc]
      abel
  have hmono : Mono (HomologicalComplex.homologyMap (toTotal K A φ hφc hφ) n) := by
    rcases n with _ | m
    · rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements _ 0 0 1 (by simp) (by simp)]
      intro X x _ y hxy
      have := col_mono K A φ hφ hA 0
      refine ⟨X, 𝟙 X, inferInstance, 0, ?_⟩
      rw [zero_comp, Category.id_comp]
      rw [HomologicalComplex.shape _ 0 0 (by simp), comp_zero, toTotal_f] at hxy
      have h0 := congrArg (· ≫ pr K 0 0 0) hxy
      simp only [Category.assoc, ι_pr, Category.comp_id, zero_comp] at h0
      rwa [← cancel_mono (φ 0), zero_comp]
    · rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements _ m (m + 1) (m + 2)
        (by simp) (by simp)]
      intro X x _ y hxy
      rcases m with _ | M
      · exact exists_comp_d_eq_of_colGe K A φ hφc hφ hA 0 y
          (fun p _ hp _ => absurd hp (by omega)) x hxy.symm
      · obtain ⟨X', π, hπ, s, hs⟩ := exists_colGe_sub_comp_d K A φ hφ hA M y (by
          rw [← hxy, toTotal_f]
          intro p q hp _
          rw [Category.assoc, Category.assoc, ι_pr_of_ne K _ _ _ _ _ _ (by omega), comp_zero,
            comp_zero]) (M + 1) le_rfl
        obtain ⟨X'', π', hπ', b, hb⟩ :=
          exists_comp_d_eq_of_colGe K A φ hφc hφ hA (M + 1) _ hs (π ≫ x) (by
          rw [Preadditive.sub_comp, Category.assoc, Category.assoc, HomologicalComplex.d_comp_d,
            comp_zero, sub_zero, ← hxy, Category.assoc])
        exact ⟨X'', π' ≫ π, epi_comp _ _, b, by rw [Category.assoc, hb]⟩
  exact isIso_of_mono_of_epi _

private lemma exists_quasiIso_toTotal
    (A : CochainComplex C ℕ) (φ : A ⟶ K.flip.X 0)
    (hφ : ∀ p, φ.f p ≫ (K.X p).d 0 1 = 0)
    (hA : ∀ p, (CochainComplex.augment (K.X p) (φ.f p) (hφ p)).Acyclic) :
    ∃ f : A ⟶ K.total (ComplexShape.up ℕ),
      (∀ p, f.f p = φ.f p ≫ K.ιTotal (ComplexShape.up ℕ) p 0 p (add_zero p)) ∧ QuasiIso f :=
  ⟨toTotal K A φ.f (fun p => φ.comm p (p + 1)) hφ, fun _ => rfl,
    quasiIso_toTotal K A φ.f (fun p => φ.comm p (p + 1)) hφ hA⟩

end

end MMP.Proofs.lem_mmp_gaga_double_complex_edge

namespace MMP.Homology

open MMP.Proofs.lem_mmp_gaga_double_complex_edge in
/-- Suppose a cochain complex `A` maps to the bottom row of a first-quadrant double complex `K` so
that every augmented column `0 → A^p → K^{p,0} → K^{p,1} → ⋯` is exact. Suppose also that `B`
maps to the left column so that every augmented row `0 → B^q → K^{0,q} → K^{1,q} → ⋯` is exact.
Then the induced maps from `A` and from `B` to the total complex of `K` are
quasi-isomorphisms. -/
@[mmp "lem_mmp_gaga_double_complex_edge"]
public theorem exists_quasiIso_total_of_acyclic_augment {C : Type*} [Category C] [Abelian C]
    [(ComplexShape.up ℕ).TensorSigns]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    [K.HasTotal (ComplexShape.up ℕ)]
    (A : CochainComplex C ℕ) (φ : A ⟶ K.flip.X 0)
    (hφ : ∀ p, φ.f p ≫ (K.X p).d 0 1 = 0)
    (hA : ∀ p, (CochainComplex.augment (K.X p) (φ.f p) (hφ p)).Acyclic)
    (B : CochainComplex C ℕ) (ψ : B ⟶ K.X 0)
    (hψ : ∀ q, ψ.f q ≫ (K.flip.X q).d 0 1 = 0)
    (hB : ∀ q, (CochainComplex.augment (K.flip.X q) (ψ.f q) (hψ q)).Acyclic) :
    (∃ f : A ⟶ K.total (ComplexShape.up ℕ),
      (∀ p, f.f p = φ.f p ≫ K.ιTotal (ComplexShape.up ℕ) p 0 p (add_zero p)) ∧ QuasiIso f) ∧
    ∃ g : B ⟶ K.total (ComplexShape.up ℕ),
      (∀ q, g.f q = ψ.f q ≫ K.ιTotal (ComplexShape.up ℕ) 0 q q (zero_add q)) ∧ QuasiIso g := by
  refine ⟨exists_quasiIso_toTotal K A φ hφ hA, ?_⟩
  letI : TotalComplexShapeSymmetry (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) :=
    { symm := fun p q => add_comm q p
      σ := fun p q => (ComplexShape.up ℕ).ε (p * q)
      σ_ε₁ := by
        rintro p _ rfl q
        dsimp
        rw [mul_one, add_mul, one_mul, ComplexShape.ε_add,
          mul_comm ((ComplexShape.up ℕ).ε (p * q)), ← mul_assoc, Int.units_mul_self, one_mul]
      σ_ε₂ := by
        rintro p q _ rfl
        dsimp
        rw [one_mul, mul_add, mul_one, ComplexShape.ε_add] }
  obtain ⟨f, hf, hqf⟩ := exists_quasiIso_toTotal K.flip B ψ hψ hB
  refine ⟨f ≫ (K.totalFlipIso (ComplexShape.up ℕ)).hom, fun q => ?_, inferInstance⟩
  rw [HomologicalComplex.comp_f, hf]
  refine (Category.assoc _ _ _).trans ?_
  erw [K.ιTotal_totalFlipIso_f_hom (ComplexShape.up ℕ) 0 q q (add_zero q)]
  have hσ : TotalComplexShapeSymmetry.σ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) 0 q = 1 := by
    change (ComplexShape.up ℕ).ε (0 * q) = 1
    rw [zero_mul, ComplexShape.ε_zero]
  simp only [hσ, one_smul, Linear.comp_units_smul]
  rfl

end MMP.Homology

end

/-!
# Sheaves of modules over smooth functions are acyclic

Let `M` be a second countable Hausdorff `C^∞` manifold modelled on a finite-dimensional real
space, and let `ℰ_M` be its sheaf of smooth complex-valued functions. Every sheaf `𝒜` of
`ℰ_M`-modules has vanishing higher cohomology over every open subset `V` of `M`:
`H^q(V, 𝒜) = 0` for `q ≥ 1`. Smooth partitions of unity make every such `𝒜` "fine", and the
vanishing follows by dimension shifting along the canonical flasque embedding.

## Main results

* `MMP.Analytic.subsingleton_H'_smoothSheafModule`: for a sheaf `𝒜` of modules over
  `smoothSheafCommRing I 𝓘(ℝ, R) M R` (the source's case is `R = ℂ`), the cohomology
  `H^{q+1}(V, 𝒜)` of its underlying abelian sheaf is trivial for every open `V` and every `q`.

## Implementation notes

Cohomology over an open `V` is Mathlib's `CategoryTheory.Sheaf.H'`, the `Ext` group from the
free abelian sheaf on `V` into the underlying abelian sheaf `(SheafOfModules.toSheaf _).obj 𝒜`.
The coefficients are any commutative normed `ℝ`-algebra `R` with smooth multiplication
(`ContMDiffRing 𝓘(ℝ, R) ∞ R`); the argument only uses that real smooth partitions of unity act
on sections through `algebraMap ℝ R`. The source's case is `R = ℂ`, where the smoothness of
multiplication is a hypothesis to be discharged since Mathlib does not register it as an instance.
The manifold may have boundary and corners (any `ModelWithCorners ℝ E H`), since smooth
partitions of unity exist in that generality.

## References

* [Wells, *Differential Analysis on Complex Manifolds*, Ch. II, Prop. 3.5][wells2008]
-/

section

universe w v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
open scoped Manifold ContDiff

namespace MMP.Proofs.lem_mmp_gaga_smooth_module_sheaves_acyclic

section Abstract

variable {C : Type*} [Category C] [Abelian C] [HasExt.{v} C] (X : C)
  {S : ShortComplex C} (hS : S.ShortExact)

include hS in
/-- Dimension shifting in degrees `≥ 2`: if `Ext^{n+1}(X, S.X₂)` vanishes for all `n` and
`Ext^{q+1}(X, S.X₃)` vanishes, then so does `Ext^{q+2}(X, S.X₁)`. -/
private lemma subsingleton_ext_add_two_of_shortExact
    (h₂ : ∀ n : ℕ, Subsingleton (Abelian.Ext.{v} X S.X₂ (n + 1))) (q : ℕ)
    (h₃ : Subsingleton (Abelian.Ext.{v} X S.X₃ (q + 1))) :
    Subsingleton (Abelian.Ext.{v} X S.X₁ (q + 2)) := by
  refine subsingleton_of_forall_eq 0 fun x₁ => ?_
  obtain ⟨x₃, rfl⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS x₁
    (Subsingleton.elim (h := h₂ (q + 1)) _ _) (n₀ := q + 1) rfl
  rw [Subsingleton.elim x₃ 0, Abelian.Ext.zero_comp]

include hS in
/-- Dimension shifting in degree `1`: if `Ext¹(X, S.X₂)` vanishes and every morphism
`X ⟶ S.X₃` lifts along `S.g`, then `Ext¹(X, S.X₁)` vanishes. -/
private lemma subsingleton_ext_one_of_shortExact
    (h₂ : Subsingleton (Abelian.Ext.{v} X S.X₂ 1))
    (hg : ∀ φ : X ⟶ S.X₃, ∃ ψ : X ⟶ S.X₂, ψ ≫ S.g = φ) :
    Subsingleton (Abelian.Ext.{v} X S.X₁ 1) := by
  refine subsingleton_of_forall_eq 0 fun x₁ => ?_
  obtain ⟨x₃, rfl⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS x₁
    (Subsingleton.elim _ _) (n₀ := 0) rfl
  obtain ⟨φ, rfl⟩ := (Abelian.Ext.mk₀_bijective X S.X₃).2 x₃
  obtain ⟨ψ, rfl⟩ := hg φ
  rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.comp_assoc_of_second_deg_zero,
    hS.comp_extClass, Abelian.Ext.comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero component of a quasi-isomorphism out of a complex concentrated in degree `0`
is a monomorphism. -/
private lemma mono_f_zero_of_quasiIso {A : C} {K : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ι] : Mono (ι.f 0) := by
  have w : ι.f 0 ≫ K.d 0 1 = 0 := by
    rw [ι.comm 0 1]; simp
  have hl : IsLimit (KernelFork.ofι _ w) := by
    refine IsLimit.ofIsoLimit (K.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
    refine Fork.ext ((HomologicalComplex.singleObjHomologySelfIso _ _ _).symm ≪≫
      isoOfQuasiIsoAt ι 0 ≪≫ K.isoHomologyπ₀.symm) ?_
    rw [← cancel_epi (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) _ _).hom,
      ← cancel_epi (CochainComplex.isoHomologyπ₀ _).hom,
      ← cancel_epi (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) _ _).inv]
    simp
  exact mono_of_isLimit_fork hl

end Abstract

section Flasque

variable {X : TopCat.{0}} [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})]

/-- A morphism from the free abelian sheaf on an open `V` lifts along a morphism of abelian
sheaves which is surjective on sections over `V`. -/
private lemma exists_lift_of_surjective_app
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}} (g : F ⟶ G) (V : Opens X)
    (hg : Function.Surjective (g.hom.app (op V)))
    (φ : ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free) ⋙
      presheafToSheaf _ _).obj V ⟶ G) :
    ∃ ψ, ψ ≫ g = φ := by
  let e := ModuleSheafCohomology.evaluationRepresentation (Opens.grothendieckTopology X) V
  obtain ⟨t, ht⟩ := hg ((e.inv.app G).hom φ)
  refine ⟨(e.hom.app F).hom t, ?_⟩
  have h := congrArg (fun f => f.hom t) (e.hom.naturality g)
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  refine (h.symm.trans ?_)
  change (e.hom.app G).hom ((g.hom.app (op V)) t) = φ
  rw [ht]
  exact congrArg (fun f => f.hom φ) (e.inv_hom_id_app G)

/-- Every abelian sheaf is the first term of a short exact sequence with injective middle term. -/
private lemma exists_shortExact_injective
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :
    ∃ S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}),
      S.X₁ = F ∧ S.ShortExact ∧ Injective S.X₂ := by
  obtain ⟨p⟩ := EnoughInjectives.presentation F
  have := p.mono
  exact ⟨ShortComplex.mk p.f (cokernel.π p.f) (cokernel.condition _), rfl,
    { exact := ShortComplex.exact_cokernel p.f }, p.injective⟩

/-- The higher cohomology of a flasque abelian sheaf vanishes over every open. -/
private lemma subsingleton_H'_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (hF : TopCat.Sheaf.IsFlasque (X := X) F) (n : ℕ) (V : Opens X) :
    Subsingleton (F.H' (n + 1) V) := by
  induction n generalizing F with
  | zero =>
    obtain ⟨S, rfl, hS, hI⟩ := exists_shortExact_injective F
    exact subsingleton_ext_one_of_shortExact _ hS (Abelian.Ext.subsingleton_of_injective _ _ 0)
      (exists_lift_of_surjective_app _ V ((AddCommGrpCat.epi_iff_surjective _).1
        (TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := V) hS)))
  | succ n ih =>
    obtain ⟨S, rfl, hS, hI⟩ := exists_shortExact_injective F
    have : @Injective (TopCat.Sheaf AddCommGrpCat.{0} X) _ S.X₂ := hI
    have := Stacks.Cohomology.CechOne.isFlasque_of_injective (X := X) S.X₂
    exact subsingleton_ext_add_two_of_shortExact _ hS
      (Abelian.Ext.subsingleton_of_injective _ _) n
      (ih _ (TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS))

end Flasque

section LocallyFiniteSums

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)

/-- Restricting twice is restricting once. -/
private lemma res_res {U V W : Opens X} (f : V ⟶ U) (g : W ⟶ V) (h : W ⟶ U) (s : F.1.obj (op U)) :
    F.1.map g.op (F.1.map f.op s) = F.1.map h.op s := by
  rw [← ConcreteCategory.comp_apply, ← F.1.map_comp]
  rfl

variable {ι : Type} (U : ι → Opens X) (s : ∀ k, F.1.obj (op (U k)))

/-- The restriction of `s k` to `N` if `N ⊆ U k`, and zero otherwise. -/
private noncomputable def restrictOrZero (N : Opens X) (k : ι) : F.1.obj (op N) := by
  classical
  exact if h : N ≤ U k then F.1.map (homOfLE h).op (s k) else 0

/-- `N` lies in `U k` for every `k ∈ T`, and `s k` vanishes on `N ∩ U k` for every `k ∉ T`. -/
private def VanishesOff (N : Opens X) (T : Finset ι) : Prop :=
  (∀ k ∈ T, N ≤ U k) ∧ ∀ k ∉ T, F.1.map (homOfLE inf_le_right : N ⊓ U k ⟶ U k).op (s k) = 0

variable {F U s}

private lemma restrictOrZero_of_le {N : Opens X} {k : ι} (h : N ≤ U k) :
    restrictOrZero F U s N k = F.1.map (homOfLE h).op (s k) := by
  simp [restrictOrZero, h]

private lemma VanishesOff.mono {N N' : Opens X} {T : Finset ι} (hT : VanishesOff F U s N T)
    (h : N' ≤ N) :
    VanishesOff F U s N' T := by
  refine ⟨fun k hk => h.trans (hT.1 k hk), fun k hk => ?_⟩
  rw [← res_res F (homOfLE inf_le_right) (homOfLE (inf_le_inf_right _ h)), hT.2 k hk, map_zero]

private lemma VanishesOff.restrictOrZero_eq_zero {N : Opens X} {T : Finset ι}
    (hT : VanishesOff F U s N T)
    {k : ι} (hk : k ∉ T) :
    restrictOrZero F U s N k = 0 := by
  by_cases h : N ≤ U k
  · rw [restrictOrZero_of_le h,
      ← res_res F (homOfLE inf_le_right) (homOfLE (le_inf le_rfl h)), hT.2 k hk,
      map_zero]
  · simp [restrictOrZero, h]

private lemma VanishesOff.res_restrictOrZero {N N' : Opens X} {T : Finset ι}
    (hT : VanishesOff F U s N T)
    (h : N' ≤ N) (k : ι) :
    F.1.map (homOfLE h).op (restrictOrZero F U s N k) = restrictOrZero F U s N' k := by
  by_cases hk : k ∈ T
  · rw [restrictOrZero_of_le (hT.1 k hk), restrictOrZero_of_le (h.trans (hT.1 k hk)), res_res]
  · rw [hT.restrictOrZero_eq_zero hk, (hT.mono h).restrictOrZero_eq_zero hk, map_zero]

private lemma VanishesOff.sum_eq {N : Opens X} {T T' : Finset ι} (hT : VanishesOff F U s N T)
    (hT' : VanishesOff F U s N T') :
    ∑ k ∈ T, restrictOrZero F U s N k = ∑ k ∈ T', restrictOrZero F U s N k := by
  classical
  exact (Finset.sum_subset (Finset.subset_union_left (s₂ := T')) fun k _ hk =>
    hT.restrictOrZero_eq_zero hk).trans (Finset.sum_subset (Finset.subset_union_right (s₁ := T))
      fun k _ hk => hT'.restrictOrZero_eq_zero hk).symm

private lemma VanishesOff.res_sum {N N' : Opens X} {T : Finset ι} (hT : VanishesOff F U s N T)
    (h : N' ≤ N) :
    F.1.map (homOfLE h).op (∑ k ∈ T, restrictOrZero F U s N k) =
      ∑ k ∈ T, restrictOrZero F U s N' k := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => hT.res_restrictOrZero h k

/-- A locally finite family of sections, each vanishing off a closed subset of its domain, has a
sum over `W`: on any `N` where only the indices in `T` contribute, it is the finite sum over
`T`. -/
private lemma exists_sum (W : Opens X)
    (hloc : ∀ x ∈ W, ∃ N : Opens X, N ≤ W ∧ x ∈ N ∧ ∃ T, VanishesOff F U s N T) :
    ∃ e : F.1.obj (op W), ∀ (N : Opens X) (hN : N ≤ W) (T : Finset ι), VanishesOff F U s N T →
      F.1.map (homOfLE hN).op e = ∑ k ∈ T, restrictOrZero F U s N k := by
  choose N hNW hxN T hT using hloc
  let V : W → Opens X := fun x => N x.1 x.2
  obtain ⟨e, he, -⟩ := F.existsUnique_gluing' V W (fun x => homOfLE (hNW x.1 x.2))
    (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxN x hx⟩)
    (fun x => ∑ k ∈ T x.1 x.2, restrictOrZero F U s (V x) k) (fun x y => by
      change F.1.map (homOfLE inf_le_left).op _ = F.1.map (homOfLE inf_le_right).op _
      rw [(hT x.1 x.2).res_sum, (hT y.1 y.2).res_sum,
        ((hT x.1 x.2).mono inf_le_left).sum_eq ((hT y.1 y.2).mono inf_le_right)])
  refine ⟨e, fun N' hN' T' hT' => ?_⟩
  refine F.eq_of_locally_eq' (fun x : W => N' ⊓ V x) N'
    (fun x => homOfLE inf_le_left) (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hN' hx⟩,
      ⟨hx, hxN x (hN' hx)⟩⟩) _ _ fun x => ?_
  change F.1.map (homOfLE inf_le_left).op _ = F.1.map (homOfLE inf_le_left).op _
  rw [res_res F _ _ (homOfLE (inf_le_left.trans hN')), hT'.res_sum,
    ← res_res F (homOfLE (hNW x.1 x.2)) (homOfLE inf_le_right), he x,
    (hT x.1 x.2).res_sum, ((hT x.1 x.2).mono inf_le_right).sum_eq (hT'.mono inf_le_left)]

variable {𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}

/-- Restricting a section of a sheaf of rings twice is restricting once. -/
private lemma ring_res_res {U V W : Opens X} (f : V ⟶ U) (g : W ⟶ V) (h : W ⟶ U)
    (s : 𝒪.obj.obj (op U)) :
    𝒪.obj.map g.op (𝒪.obj.map f.op s) = 𝒪.obj.map h.op s := by
  rw [← ConcreteCategory.comp_apply, ← 𝒪.obj.map_comp]
  rfl

/-- Taking sections over an open is left exact on a short exact sequence of abelian sheaves. -/
private lemma injective_and_exact_app
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})}
    (hS : S.ShortExact) (U : Opens X) :
    Function.Injective (S.f.hom.app (op U)) ∧
      ∀ b, S.g.hom.app (op U) b = 0 → ∃ a, S.f.hom.app (op U) a = b := by
  have := hS.mono_f
  have : PreservesLimits ((sheafSections (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).obj (op U)) := preservesLimits_of_natIso
    (sheafSectionsNatIsoEvaluation (J := Opens.grothendieckTopology X)
      (A := AddCommGrpCat.{0})).symm
  exact ⟨(AddCommGrpCat.mono_iff_injective
      (((sheafSections _ _).obj (op U)).map S.f)).1 inferInstance, fun b hb =>
    (ShortComplex.ab_exact_iff _).1 (hS.exact.map_of_mono_of_preservesKernel
      ((sheafSections _ _).obj (op U)) inferInstance inferInstance) b hb⟩

/-- Sections over `V` surject onto the cokernel of an embedding of a sheaf of `𝒪`-modules, as soon
as every open cover of `V` has a locally finite partition of unity in `𝒪(V)` subordinate to it. -/
private lemma surjective_app_of_partition (𝒜 : SheafOfModules.{0} 𝒪)
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}))
    (hS : S.ShortExact) (h₁ : S.X₁ = (SheafOfModules.toSheaf _).obj 𝒜) (V : Opens X)
    (hρ : ∀ W : V → Opens X, (∀ k, W k ≤ V) → (∀ x, x.1 ∈ W x) →
      ∃ ρ : V → 𝒪.obj.obj (op V), ∀ x ∈ V, ∃ N : Opens X, ∃ hN : N ≤ V, x ∈ N ∧
        ∃ T : Finset V, (∀ k ∈ T, N ≤ W k) ∧ (∀ k ∉ T, 𝒪.obj.map (homOfLE hN).op (ρ k) = 0) ∧
          ∑ k ∈ T, 𝒪.obj.map (homOfLE hN).op (ρ k) = 1) :
    Function.Surjective (S.g.hom.app (op V)) := by
  have hex := fun U : Opens X => injective_and_exact_app hS U
  have hfg : ∀ (U : Opens X) a, S.g.hom.app (op U) (S.f.hom.app (op U) a) = 0 := fun U a => by
    change ((S.f ≫ S.g).hom.app (op U)) a = 0
    rw [S.zero]
    rfl
  have hloc : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 hS.epi_g
  cases S with | @mk X₁ B C f g w => ?_
  subst h₁
  dsimp only at *
  let A : TopCat.Sheaf AddCommGrpCat.{0} X := (SheafOfModules.toSheaf _).obj 𝒜
  let B' : TopCat.Sheaf AddCommGrpCat.{0} X := B
  let C' : TopCat.Sheaf AddCommGrpCat.{0} X := C
  intro c
  have hlift : ∀ x : V, ∃ (W : Opens X) (hW : W ≤ V), x.1 ∈ W ∧ ∃ b : B.obj.obj (op W),
      g.hom.app (op W) b = C.obj.map (homOfLE hW).op c := fun x => by
    obtain ⟨W, i, ⟨b, hb⟩, hx⟩ :=
      Presheaf.imageSieve_mem (Opens.grothendieckTopology X) g.hom c x.1 x.2
    exact ⟨W, i.le, hx, b, hb⟩
  choose W hWV hxW b hb using hlift
  obtain ⟨ρ, hρ⟩ := hρ W hWV hxW
  -- the differences of the local lifts come from `𝒜`
  have hd : ∀ i k : V, ∃ d : 𝒜.val.obj (op (W i ⊓ W k)), f.hom.app _ d =
      B.obj.map (homOfLE inf_le_right).op (b k) - B.obj.map (homOfLE inf_le_left).op (b i) :=
    fun i k => (hex _).2 _ (by
      rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, hb, hb,
        res_res C', res_res C' _ _ (homOfLE (inf_le_left.trans (hWV i))), sub_self])
  choose d hd using hd
  have hcov : V ≤ iSup W := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxW _⟩
  have hvan : ∀ {N N' : Opens X} (hN : N ≤ V) (h : N' ≤ N) (k : V),
      𝒪.obj.map (homOfLE hN).op (ρ k) = 0 → 𝒪.obj.map (homOfLE (h.trans hN)).op (ρ k) = 0 :=
    fun hN h k H => by rw [← ring_res_res (homOfLE hN) (homOfLE h), H, map_zero]
  have hone : ∀ {N N' : Opens X} (hN : N ≤ V) (h : N' ≤ N) (T : Finset V),
      ∑ k ∈ T, 𝒪.obj.map (homOfLE hN).op (ρ k) = 1 →
        ∑ k ∈ T, 𝒪.obj.map (homOfLE (h.trans hN)).op (ρ k) = 1 := fun hN h T H => by
    rw [← map_one (𝒪.obj.map (homOfLE h).op).hom, ← H, map_sum]
    exact Finset.sum_congr rfl fun k _ => (ring_res_res _ _ _ _).symm
  -- the corrections `e i = ∑ₖ ρₖ (b k - b i)`
  let U : V → V → Opens X := fun i k => W i ⊓ W k
  let s : ∀ i k : V, A.1.obj (op (U i k)) := fun i k =>
    (𝒪.obj.map (homOfLE (inf_le_left.trans (hWV i)) : W i ⊓ W k ⟶ V).op (ρ k) • d i k :
      𝒜.val.obj (op (W i ⊓ W k)))
  have hext : ∀ (i k : V) {N : Opens X} (h : N ≤ U i k),
      restrictOrZero A (U i) (s i) N k =
        (𝒪.obj.map (homOfLE (h.trans (inf_le_left.trans (hWV i)))).op (ρ k) •
        (𝒜.val.map (homOfLE h).op (d i k) : 𝒜.val.obj (op N)) : 𝒜.val.obj (op N)) :=
      fun i k N h => by
    rw [restrictOrZero_of_le h]
    change 𝒜.val.map (homOfLE h).op (_ • d i k) = _
    rw [PresheafOfModules.map_smul, ring_res_res]
  have hgood : ∀ (i : V) {N : Opens X} (hN : N ≤ V) (hNi : N ≤ W i) (T : Finset V),
      (∀ k ∈ T, N ≤ W k) → (∀ k ∉ T, 𝒪.obj.map (homOfLE hN).op (ρ k) = 0) →
        VanishesOff A (U i) (s i) N T := fun i N hN hNi T hT h0 => by
    refine ⟨fun k hk => le_inf hNi (hT k hk), fun k hk => ?_⟩
    change 𝒜.val.map (homOfLE inf_le_right).op (_ • d i k) = 0
    rw [PresheafOfModules.map_smul, ring_res_res _ _ (homOfLE (inf_le_left.trans hN)),
      hvan hN inf_le_left k (h0 k hk), zero_smul]
  have he : ∀ i : V, ∃ e : A.1.obj (op (W i)), ∀ (N : Opens X) (hN : N ≤ W i) (T : Finset V),
      VanishesOff A (U i) (s i) N T →
        A.1.map (homOfLE hN).op e = ∑ k ∈ T, restrictOrZero A (U i) (s i) N k :=
    fun i => exists_sum _ fun x hx => by
      obtain ⟨N, hN, hxN, T, hT, h0, -⟩ := hρ x (hWV i hx)
      exact ⟨N ⊓ W i, inf_le_right, ⟨hxN, hx⟩, T, hgood i (inf_le_left.trans hN) inf_le_right T
        (fun k hk => inf_le_left.trans (hT k hk)) fun k hk => hvan hN inf_le_left k (h0 k hk)⟩
  choose e he using he
  have hD : ∀ i j : V, A.1.map (homOfLE inf_le_left : W i ⊓ W j ⟶ W i).op (e i) -
      A.1.map (homOfLE inf_le_right : W i ⊓ W j ⟶ W j).op (e j) = d i j := fun i j => by
    refine A.eq_of_locally_eq' (fun x : (W i ⊓ W j : Opens X) =>
      (hρ x.1 (hWV i x.2.1)).choose ⊓ (W i ⊓ W j)) _ (fun _ => homOfLE inf_le_right)
      (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, (hρ x (hWV i hx.1)).choose_spec.choose_spec.1, hx⟩)
      _ _ fun x => ?_
    obtain ⟨hN, hxN, T, hT, h0, h1⟩ := (hρ x.1 (hWV i x.2.1)).choose_spec
    set N := (hρ x.1 (hWV i x.2.1)).choose
    have hN' : N ⊓ (W i ⊓ W j) ≤ V := inf_le_left.trans hN
    have hT' : ∀ k ∈ T, N ⊓ (W i ⊓ W j) ≤ W k := fun k hk => inf_le_left.trans (hT k hk)
    have h0' := fun k hk => hvan hN (inf_le_left : N ⊓ (W i ⊓ W j) ≤ N) k (h0 k hk)
    change A.1.map (homOfLE inf_le_right).op _ = A.1.map (homOfLE inf_le_right).op _
    rw [map_sub, res_res A _ _ (homOfLE (inf_le_right.trans inf_le_left)),
      res_res A _ _ (homOfLE (inf_le_right.trans inf_le_right)),
      he i _ _ T (hgood i hN' (inf_le_right.trans inf_le_left) T hT' h0'),
      he j _ _ T (hgood j hN' (inf_le_right.trans inf_le_right) T hT' h0'),
      ← Finset.sum_sub_distrib]
    have hkey : ∀ k ∈ T, restrictOrZero A (U i) (s i) (N ⊓ (W i ⊓ W j)) k -
        restrictOrZero A (U j) (s j) (N ⊓ (W i ⊓ W j)) k =
        (𝒪.obj.map (homOfLE hN').op (ρ k) •
          (𝒜.val.map (homOfLE inf_le_right).op (d i j) : 𝒜.val.obj (op (N ⊓ (W i ⊓ W j)))) :
            𝒜.val.obj (op (N ⊓ (W i ⊓ W j)))) := fun k hk => by
      rw [hext i k (le_inf (inf_le_right.trans inf_le_left) (hT' k hk)),
        hext j k (le_inf (inf_le_right.trans inf_le_right) (hT' k hk))]
      refine (smul_sub (A := ↑(𝒜.val.obj (op (N ⊓ (W i ⊓ W j))))) _ _ _).symm.trans ?_
      congr 1
      apply (hex _).1
      erw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply,
        NatTrans.naturality_apply]
      have hk' : N ⊓ (W i ⊓ W j) ≤ W k := hT' k hk
      rw [hd, hd, hd, map_sub, map_sub, map_sub, res_res B' _ _ (homOfLE hk'),
        res_res B' _ _ (homOfLE hk'), res_res B' _ _ (homOfLE (inf_le_right.trans inf_le_left)),
        res_res B' _ _ (homOfLE (inf_le_right.trans inf_le_right)),
        res_res B' _ _ (homOfLE (inf_le_right.trans inf_le_right)),
        res_res B' _ _ (homOfLE (inf_le_right.trans inf_le_left))]
      exact sub_sub_sub_cancel_left _ _ _
    rw [Finset.sum_congr rfl hkey]
    refine (Finset.sum_smul (M := ↑(𝒜.val.obj (op (N ⊓ (W i ⊓ W j))))) ..).symm.trans ?_
    rw [hone hN inf_le_left T h1]
    exact one_smul _ _
  obtain ⟨t, ht, -⟩ := B'.existsUnique_gluing' W V (fun i => homOfLE (hWV i)) hcov
    (fun i => b i + f.hom.app _ (e i)) (fun i j => by
      change B.obj.map (homOfLE inf_le_left).op _ = B.obj.map (homOfLE inf_le_right).op _
      have h := congrArg (f.hom.app (op (W i ⊓ W j))) (hD i j)
      rw [map_sub, hd] at h
      erw [NatTrans.naturality_apply, NatTrans.naturality_apply] at h
      rw [sub_eq_sub_iff_add_eq_add] at h
      rw [map_add, map_add, add_comm]
      exact h)
  refine ⟨t, C'.eq_of_locally_eq' W V (fun i => homOfLE (hWV i)) hcov _ _ fun i => ?_⟩
  erw [← NatTrans.naturality_apply]
  rw [ht i, map_add, hb, hfg, add_zero]

end LocallyFiniteSums

section Smooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {R : Type} [NormedCommRing R] [NormedAlgebra ℝ R] [ContMDiffRing 𝓘(ℝ, R) ∞ R]

/-- Every open cover of an open `V` of the manifold has a locally finite smooth partition of unity
subordinate to it, read as sections of the sheaf of smooth `R`-valued functions over `V`. -/
private lemma exists_smoothPartition (V : Opens (TopCat.of M)) (W : V → Opens (TopCat.of M))
    (hWV : ∀ k, W k ≤ V) (hxW : ∀ x, x.1 ∈ W x) :
    ∃ ρ : V → ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj
        (smoothSheafCommRing I 𝓘(ℝ, R) M R)).obj.obj (op V),
      ∀ x ∈ V, ∃ N : Opens (TopCat.of M), ∃ hN : N ≤ V, x ∈ N ∧
        ∃ T : Finset V, (∀ k ∈ T, N ≤ W k) ∧
          (∀ k ∉ T, ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj
            (smoothSheafCommRing I 𝓘(ℝ, R) M R)).obj.map (homOfLE hN).op (ρ k) = 0) ∧
          ∑ k ∈ T, ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj
            (smoothSheafCommRing I 𝓘(ℝ, R) M R)).obj.map (homOfLE hN).op (ρ k) = 1 := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  haveI : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  obtain ⟨ρ', hρ'⟩ := SmoothPartitionOfUnity.exists_isSubordinate I (M := V) isClosed_univ
    (fun k => ((↑) : V → M) ⁻¹' (W k : Set M))
    (fun k => (W k).isOpen.preimage continuous_subtype_val)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hxW y⟩)
  let one : C^∞⟮I, V; 𝓘(ℝ, R), R⟯ := 1
  refine ⟨fun k => (ρ' k • one : C^∞⟮I, V; 𝓘(ℝ, R), R⟯), fun x hx => ?_⟩
  set x' : V := ⟨x, hx⟩
  have hev : ∀ᶠ y in 𝓝 x', ρ'.fintsupport y ⊆ ρ'.fintsupport x' ∧
      ∀ k ∈ ρ'.fintsupport x', y.1 ∈ W k :=
    (ρ'.eventually_fintsupport_subset x').and ((Finset.eventually_all _).2 fun k hk =>
      ((W k).isOpen.preimage continuous_subtype_val).mem_nhds
        (hρ' k ((ρ'.mem_fintsupport_iff x' k).1 hk)))
  obtain ⟨O, hO, hOo, hxO⟩ := eventually_nhds_iff.1 hev
  let N : Opens (TopCat.of M) := ⟨Subtype.val '' O, V.isOpen.isOpenMap_subtype_val O hOo⟩
  have hN : N ≤ V := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hzero : ∀ z : N, ∀ k ∉ ρ'.fintsupport x', ρ' k ⟨z.1, hN z.2⟩ = 0 := by
    rintro ⟨_, y, hy, rfl⟩ k hk
    exact image_eq_zero_of_notMem_tsupport fun h =>
      hk ((hO y hy).1 ((ρ'.mem_fintsupport_iff _ k).2 h))
  refine ⟨N, hN, ⟨x', hxO, rfl⟩, ρ'.fintsupport x', fun k hk => ?_, fun k hk => ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hO y hy).2 k hk
  · refine ContMDiffMap.ext fun z => ?_
    change ρ' k ⟨z.1, hN z.2⟩ • (1 : R) = 0
    rw [hzero z k hk, zero_smul]
  · refine ContMDiffMap.ext fun z => ?_
    erw [← ContMDiffMap.coeFnRingHom_apply, map_sum, Finset.sum_apply]
    change ∑ k ∈ ρ'.fintsupport x', ρ' k ⟨z.1, hN z.2⟩ • (1 : R) = 1
    have hsupp : Function.support (fun k => ρ' k ⟨z.1, hN z.2⟩) ⊆ ↑(ρ'.fintsupport x') :=
      fun k hk => by_contra fun h => hk (hzero z k h)
    rw [← Finset.sum_smul, ← finsum_eq_sum_of_support_subset _ hsupp,
      ρ'.sum_eq_one (Set.mem_univ _), one_smul]

/-- **Step 1 (fineness).** If `0 → 𝒜 → ℬ → 𝒞 → 0` is a short exact sequence of abelian sheaves
whose first term is a sheaf of modules over the smooth functions, then sections of `ℬ` over every
open surject onto sections of `𝒞`: local lifts are corrected by a smooth partition of unity. -/
private lemma surjective_app_of_shortExact
    (𝒜 : SheafOfModules.{0}
      ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj
        (smoothSheafCommRing I 𝓘(ℝ, R) M R)))
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}))
    (hS : S.ShortExact) (h₁ : S.X₁ = (SheafOfModules.toSheaf _).obj 𝒜)
    (V : Opens (TopCat.of M)) :
    Function.Surjective (S.g.hom.app (op V)) :=
  surjective_app_of_partition 𝒜 S hS h₁ V (exists_smoothPartition I V)

/-- **Step 2 (Godement embedding).** Every sheaf of modules over the smooth functions embeds into
one whose underlying abelian sheaf is flasque, with a cokernel which is again a sheaf of modules:
take `U ↦ ∏_{x ∈ U} 𝒜_x` with the stalkwise module structure. -/
private lemma exists_shortExact_isFlasque
    (𝒜 : SheafOfModules.{0}
      ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj
        (smoothSheafCommRing I 𝓘(ℝ, R) M R))) :
    ∃ S : ShortComplex (SheafOfModules.{0}
      ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj
        (smoothSheafCommRing I 𝓘(ℝ, R) M R))),
      S.X₁ = 𝒜 ∧ (S.map (SheafOfModules.toSheaf _)).ShortExact ∧
        TopCat.Sheaf.IsFlasque (X := TopCat.of M) ((SheafOfModules.toSheaf _).obj S.X₂) := by
  let X : AlgebraicGeometry.RingedSpace.{0, 0} :=
    { carrier := TopCat.of M, presheaf := (smoothSheafCommRing I 𝓘(ℝ, R) M R).obj,
      IsSheaf := (smoothSheafCommRing I 𝓘(ℝ, R) M R).property }
  let ι := (AlgebraicGeometry.GodementResolution.godementAugmentation X).app 𝒜
  have : QuasiIso ι := AlgebraicGeometry.GodementResolution.quasiIso_godementAugmentation X 𝒜
  have : Mono (ι.f 0) := mono_f_zero_of_quasiIso ι
  have := ModuleSheafCohomology.toSheaf_preservesFiniteColimits _ (structureSheafRing X)
  have hS : (ShortComplex.mk (ι.f 0) (cokernel.π (ι.f 0)) (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  exact ⟨_, rfl, hS.map (SheafOfModules.toSheaf _),
    AlgebraicGeometry.GodementResolution.isFlasque_godementComplex X 𝒜 0⟩

end Smooth

end MMP.Proofs.lem_mmp_gaga_smooth_module_sheaves_acyclic

namespace MMP.Analytic

open MMP.Proofs.lem_mmp_gaga_smooth_module_sheaves_acyclic in
/-- **Sheaves of modules over smooth functions are acyclic.** On a second countable Hausdorff
`C^∞` manifold `M`, every sheaf `𝒜` of modules over the sheaf of smooth `R`-valued functions,
for `R` a commutative normed `ℝ`-algebra with smooth multiplication (for instance `ℂ`, the case
of smooth complex functions), has `H^{q+1}(V, 𝒜) = 0` for every open `V ⊆ M` and every `q : ℕ`. -/
@[mmp "lem_mmp_gaga_smooth_module_sheaves_acyclic"]
public theorem subsingleton_H'_smoothSheafModule
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {R : Type} [NormedCommRing R] [NormedAlgebra ℝ R] [ContMDiffRing 𝓘(ℝ, R) ∞ R]
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0})]
    (𝒜 : SheafOfModules
      ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj
        (smoothSheafCommRing I 𝓘(ℝ, R) M R)))
    (V : Opens (TopCat.of M)) (q : ℕ) :
    Subsingleton (((SheafOfModules.toSheaf _).obj 𝒜).H' (q + 1) V) := by
  induction q generalizing 𝒜 with
  | zero =>
    obtain ⟨S, rfl, hS, hfl⟩ := exists_shortExact_isFlasque I 𝒜
    exact subsingleton_ext_one_of_shortExact _ hS (subsingleton_H'_of_isFlasque _ hfl 0 V)
      (exists_lift_of_surjective_app _ V (surjective_app_of_shortExact I _ _ hS rfl V))
  | succ q ih =>
    obtain ⟨S, rfl, hS, hfl⟩ := exists_shortExact_isFlasque I 𝒜
    exact subsingleton_ext_add_two_of_shortExact _ hS
      (fun n => subsingleton_H'_of_isFlasque _ hfl n V) q (ih S.X₃)

end MMP.Analytic

end
