module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
import MMP.AlgebraicGeometry.Resolution.DivisorTuple.TransformationSequence
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.InvertibleToBaseIso
import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.GenerationRequired
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersionFactorization
import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraCopies
import StacksFrontier.AlgebraicGeometry.ReflexiveTorsionFree.Converse
import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DualTensorInternalHom
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# Common log resolutions of a birational map preserving an snc locus

Let `k` be a field of characteristic zero, `X` and `X'` normal projective varieties over `k`
with `ℚ`-boundaries `Δ` and `Δ'`, and `φ : X ⤏ X'` a birational map over `k`, given as an
isomorphism `φ.source ≅ φ.target` of dense opens. Let `U ⊆ φ.source` be an open subset smooth
over `k` with image `U' ⊆ φ.target`, such that `Supp Δ ∩ U` and `Supp Δ' ∩ U'` are snc divisors
and so is their union on `U`, `(Supp Δ ∪ φ⁻¹ Supp Δ') ∩ U`.
Then there is a smooth projective variety `Y` with projective log resolutions `p : Y ⟶ X` of
`(X, Δ)` and `q : Y ⟶ X'` of `(X', Δ')`, with `q = φ ∘ p` as maps, such that `p` is an
isomorphism over `U` and `q` is an isomorphism over `U'`.

Let `Γ` be the closure of the graph of `φ` in `X' ×_k X`, with projections `p₁ : Γ ⟶ X` and
`p₂ : Γ ⟶ X'`. Since `X` and `X'` are separated, `p₁` is an isomorphism over `φ.source` and `p₂`
over `φ.target`, so `W = p₁⁻¹(U) = p₂⁻¹(U')` is a smooth open of `Γ` isomorphic to `U`. A strong
resolution `f₁ : Y₁ ⟶ Γ` is an isomorphism over `W`. Let `T ⊆ Y₁` be the union of the inverse
images of `Supp Δ` and `Supp Δ'` and of the exceptional sets of `P₁ = f₁ ≫ p₁` and
`P₂ = f₁ ≫ p₂`, and `D` the finite set of prime divisors of `Y₁` contained in `T`. Over
`f₁⁻¹(W) ≅ U` the support of `D` is the snc divisor `Supp Δ ∪ φ⁻¹ Supp Δ'`, so the
snc-preserving log resolution `g : Y ⟶ Y₁` of `(Y₁, D)` is an isomorphism there, and
`Ex(g) ∪ g⁻¹(Supp D)` is an snc divisor. Every component of the strict transform of `Δ` under
`p = g ≫ P₁`, and every prime divisor exceptional over `X`, lies in `Ex(g)` or over a
codimension-one point of `T`, hence in `Ex(g) ∪ g⁻¹(Supp D)`; so `p` is a log resolution, and
likewise `q = g ≫ P₂`.

## Main results

* `MMP.Flips.exists_isLogResolution_isIso_restrict_of_partialIso`: common projective log
  resolutions which are isomorphisms over a given snc locus of the birational map.

## Implementation notes

The birational map is an `AlgebraicGeometry.Scheme.PartialIso` over `k`; "`q = φ ∘ p`" is the
equality `q = φ.iso.hom ∘ p` of morphisms on `p⁻¹(φ.source)`, which is dense since `p` is
birational. The open `U` on which `φ` is an isomorphism is any open of `φ.source`, its image
`U'` being the open of `φ.target` with the same preimage under `φ.iso`. A log resolution is
`MMP.Flips.IsLogResolution`; projectivity is `AlgebraicGeometry.IsProjectiveMorphism`.

A log resolution in the sense of `MMP.Flips.IsLogResolution` only asks the reduced divisor on
the strict transform and the exceptional prime divisors to be snc; it does not ask the
exceptional set to be a divisor. So the source's second step, which makes the exceptional loci
of both projections divisorial by order reduction of marked ideals, is not needed. The graph is
not normalized either: the strong resolution `f₁` of `Γ` is smooth, hence normal, and the
snc-preserving log resolution is applied to `Y₁`.

Resolutions of singularities are projective in the sense of EGA II; they are H-projective
(`AlgebraicGeometry.IsProjectiveMorphism`) since every scheme in sight is H-projective over `k`
and so carries an ample invertible sheaf.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §2.3
* [J. Kollár, *Lectures on resolution of singularities*], Thm. 3.36
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Flips

open MMP.Mori MMP.Resolution

/-! ### Prime divisors -/

private theorem genericPoint_mem_support {X : Scheme.{u}} (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∈ (P.support : Set X) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- The support of a prime divisor, as an irreducible closed subset. -/
private noncomputable def primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    IrreducibleCloseds X :=
  IrreducibleCloseds.closureSingleton E.genericPoint

private theorem coe_primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    (primeIrr E : Set X) = E.support := by
  rw [E.support_eq_closure]
  rfl

/-- On an irreducible noetherian scheme, only finitely many prime divisors lie in a closed subset
`T ≠ X`: each of them is an irreducible component of `T`. -/
private theorem finite_setOf_support_subset {X : Scheme.{u}} [IrreducibleSpace X]
    [NoetherianSpace X] {T : Set X} (hT : IsClosed T) (hTne : T ≠ Set.univ) :
    {P : MMP.Mori.PrimeDivisor X | (P.support : Set X) ⊆ T}.Finite := by
  refine ((Aux.finite_and_cover_componentsOf hT).1.preimage
    (f := fun P : MMP.Mori.PrimeDivisor X => (P.support : Set X))
    fun P _ Q _ hPQ =>
      MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hPQ.subset).subset ?_
  intro P hP
  refine ⟨⟨MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isIrreducible_support P, hP⟩,
    fun W' hW' hPW' => ?_⟩
  let Wc : IrreducibleCloseds X := ⟨closure W', hW'.1.closure, isClosed_closure⟩
  have hWcT : (Wc : Set X) ⊆ T := closure_minimal hW'.2 hT
  have hle : primeIrr P ≤ Wc := fun x hx => by
    change x ∈ (primeIrr P : Set X) at hx
    rw [coe_primeIrr] at hx
    exact subset_closure (hPW' hx)
  rcases eq_or_lt_of_le hle with heq | hlt
  · intro x hx
    change x ∈ (P.support : Set X)
    rw [← coe_primeIrr, heq]
    exact subset_closure hx
  · exfalso
    have h1 : Order.coheight (primeIrr P) = 1 := by
      rw [← codimension_eq_coheight]
      exact P.codimension_one
    have h := Order.coheight_add_one_le hlt
    rw [h1] at h
    have hmax : IsMax Wc := Order.coheight_eq_zero.mp (nonpos_iff_eq_zero.mp
      ((ENat.add_le_add_iff_right ENat.one_ne_top).mp (by simpa using h)))
    let Wu : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X,
      isClosed_univ⟩
    have hWu : Wu ≤ Wc := hmax (fun x _ => Set.mem_univ x)
    exact hTne (Set.eq_univ_of_univ_subset ((show (Set.univ : Set X) ⊆ Wc from hWu).trans hWcT))

/-! ### Snc divisors -/

/-- The reduced divisor with components a finite set `s` of prime divisors has support `s`. -/
private theorem support_sum_single {X : Scheme.{u}} (s : Finset (MMP.Mori.PrimeDivisor X)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).support = s := by
  classical
  ext E
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

private theorem coeff_sum_single {X : Scheme.{u}} (s : Finset (MMP.Mori.PrimeDivisor X))
    (P : MMP.Mori.PrimeDivisor X) [Decidable (P ∈ s)] :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = if P ∈ s then 1 else 0 := by
  classical
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- The reduced divisor with components `s` has coefficients `0` and `1`. -/
private theorem coeff_sum_single_eq_zero_or_eq_one {X : Scheme.{u}}
    (s : Finset (MMP.Mori.PrimeDivisor X)) (P : MMP.Mori.PrimeDivisor X) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = 0 ∨
      (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).coeff P = 1 := by
  classical
  rw [coeff_sum_single]
  split_ifs <;> simp

/-- An snc reduced divisor in the sense of `DivisorWithCoeffs.IsSNC` is an snc divisor in the
sense of *Flips and abundance*. -/
private theorem isSNCDivisor_sum_single {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (s : Finset (MMP.Mori.PrimeDivisor Y))
    (h : (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).IsSNC sY) :
    MMP.Flips.IsSNCDivisor sY (∑ P ∈ s, Finsupp.single P (1 : ℤ)) :=
  ⟨coeff_sum_single_eq_zero_or_eq_one s, h.1, fun p _ => h.2 p⟩

/-- **A reduced divisor whose components lie in an snc divisor is snc.** -/
private theorem exists_isSNCDivisor_of_isSNCSubset {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFinitePresentation sY] (hsm : IsSmoothScheme sY)
    {S : Closeds Y} (hS : IsSNCSubset sY S)
    (Q : MMP.Mori.PrimeDivisor Y → Prop) (hQ : ∀ P, Q P → (P.support : Set Y) ⊆ S) :
    ∃ G : Divisor Y, (∀ P, G.coeff P = 0 ∨ G.coeff P = 1) ∧ (∀ P, G.coeff P = 1 ↔ Q P) ∧
      MMP.Flips.IsSNCDivisor sY G := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · have hQ0 : ∀ P, ¬ Q P := fun P hP => hQ P hP (genericPoint_mem_support P)
    refine ⟨∑ P ∈ (∅ : Finset (MMP.Mori.PrimeDivisor Y)), Finsupp.single P (1 : ℤ),
      coeff_sum_single_eq_zero_or_eq_one _, fun P => ?_, isSNCDivisor_sum_single _ ?_⟩
    · rw [coeff_sum_single]
      simp [hQ0 P]
    · rw [Finset.sum_empty]
      exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme sY hsm
  · have hmem : ∀ P, Q P → P ∈ s := fun P hP => by
      obtain ⟨E, hE, hEP⟩ := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.exists_subset_of_isIrreducible
        (s := s) (A := fun E : MMP.Mori.PrimeDivisor Y => (E.support : Set Y))
        (fun E _ => MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support E)
        (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isIrreducible_support P)
        (by rw [hs]; exact hQ P hP)
      rw [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hEP]
      exact hE
    refine ⟨∑ P ∈ s.filter Q, Finsupp.single P (1 : ℤ),
      coeff_sum_single_eq_zero_or_eq_one _, fun P => ?_, isSNCDivisor_sum_single _ ?_⟩
    · rw [coeff_sum_single]
      by_cases hP : Q P
      · simp [hP, hmem P hP]
      · simp [hP]
    · refine hsnc.of_support_subset ?_
      intro E hE
      rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply] at hE ⊢
      simp only [Finsupp.single_apply] at hE ⊢
      rw [Finset.sum_ite_eq'] at hE ⊢
      split_ifs at hE with h1
      · rw [if_pos (Finset.mem_filter.mp h1).1]
        exact one_ne_zero
      · exact absurd rfl hE

/-- A divisor with simple normal crossings in the sense of `MMP.Mori.IsSNCSubset` is one in the
sense of `MMP.Resolution.IsSNCClosedSubset`. -/
private theorem isSNCClosedSubset_of_isSNCSubset {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {S : Closeds X} (hS : IsSNCSubset sX S) :
    IsSNCClosedSubset sX (S : Set X) := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · exact ⟨(⊥ : Closeds X).isClosed, Or.inl Closeds.coe_bot⟩
  · have h := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC sX hsnc
    rwa [support_sum_single, hs] at h

/-- A member of an snc family with irreducible support is a prime divisor. -/
private theorem exists_primeDivisor_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (i : ι) (hirr : IsIrreducible ((F i).support : Set X)) :
    ∃ P : MMP.Mori.PrimeDivisor X, P.idealSheaf = F i := by
  have hint := isIntegral_subscheme_of_isIrreducible s (F i) (hF.1 i).2.2 hirr
  refine ⟨⟨F i, hint, ?_⟩, rfl⟩
  have hcl := closure_subschemeι_genericPoint (F i)
  refine (hF.1 i).2.1 _ ⟨show closure _ ⊆ _ from hcl.le, fun V hV _ => ?_⟩
  exact show (V : Set X) ⊆ closure _ from hcl ▸ hV

/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (D : MMP.Mori.DivisorWithCoeffs ℤ X) (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    MMP.Mori.DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]
    exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by
      rw [hg]
      exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

/-- A divisor with simple normal crossings in the sense of `IsSNCClosedSubset` is one in the
sense of `MMP.Mori.IsSNCSubset`. -/
private theorem isSNCSubset_of_isSNCClosedSubset {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [NoetherianSpace X] {S : Closeds X}
    (hS : IsSNCClosedSubset sX (S : Set X)) : IsSNCSubset sX S := by
  classical
  obtain ⟨-, h | ⟨-, hfin, hfam⟩⟩ := hS
  · exact Or.inl (Closeds.ext (by rw [h]; rfl))
  · right
    have : Fintype (componentsOf (S : Set X)) := hfin.fintype
    have hP : ∀ W : componentsOf (S : Set X), ∃ P : MMP.Mori.PrimeDivisor X,
        P.idealSheaf = componentsFamily (S : Set X) W := fun W =>
      exists_primeDivisor_of_isSNCFamily hfam W (by
        rw [coe_support_componentsFamily S.isClosed W]; exact W.2.1.1)
    choose P hP using hP
    have hPs : ∀ W, (P W).support = (W : Set X) := fun W => by
      change ((P W).idealSheaf.support : Set X) = _
      rw [hP, coe_support_componentsFamily S.isClosed W]
    refine ⟨Finset.univ.image P, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.iUnion_exists,
          Set.iUnion_iUnion_eq', Set.iUnion_subset_iff]
        intro W
        rw [hPs]
        exact W.2.1.2
      · intro x hx
        obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
        obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
        refine Set.mem_biUnion (x := P ⟨W, hW⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_
        rw [hPs]
        exact hxW
    · refine isSNC_of_isSNCFamily hfam _ fun Q hQ => ?_
      obtain ⟨E, hE, hQE⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hQ)
      have hQ' : Q = E := Finset.mem_singleton.1 (Finsupp.support_single_subset hQE)
      obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hE
      exact ⟨W, by rw [hQ', hP]⟩

/-! ### Strict transforms and exceptional divisors -/

/-- A coefficient of the linear extension of a partial map `φ` on prime divisors is nonzero only
at the image of a prime divisor with nonzero coefficient. -/
private theorem exists_apply_ne_zero_of_mapPrimeDivisors_apply_ne_zero {X Y : Scheme.{u}}
    {R : Type*} [AddCommMonoid R]
    {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {D : DivisorWithCoeffs R X} {P : MMP.Mori.PrimeDivisor Y}
    (h : DivisorWithCoeffs.mapPrimeDivisors φ D P ≠ 0) : ∃ Q, D Q ≠ 0 ∧ φ Q = some P := by
  classical
  by_contra hne
  push Not at hne
  refine h ?_
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  rw [DivisorWithCoeffs.mapPrimeDivisors_single]
  rcases hφ : φ Q with _ | E
  · rfl
  · have hne' : E ≠ P := fun he => hne Q (Finsupp.mem_support_iff.mp hQ) (by rw [hφ, he])
    exact Finsupp.single_eq_of_ne' hne'

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- If `e` is a partial isomorphism representing `f : Y ⟶ X` and `g'` a partial map representing
`e⁻¹`, then `f ∘ g'` is the identity where `g'` is defined. -/
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

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some {X Y : Scheme.{u}}
    [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor
      (MMP.Mori.RationalMap.IsBirational.inverse hf) P = some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp
    (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

private theorem isSeparated_toTerminal_of_isSeparated {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- A component `P` of the strict transform `g⁻¹_* D` under a birational morphism of varieties
lies over a component `Q` of `D`: `g(η_P) = η_Q`. -/
private theorem exists_map_genericPoint_eq_of_birationalInverseTransform_ne_zero
    {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsVariety k sX) {g : Y ⟶ X} (hY : MMP.Mori.IsVariety k (g ≫ sX))
    (hg : IsBirationalMorphism g) {R : Type*} [AddCommMonoid R] {D : DivisorWithCoeffs R X}
    {P : MMP.Mori.PrimeDivisor Y} (h : MMP.Flips.birationalInverseTransform g hg D P ≠ 0) :
    ∃ Q, D Q ≠ 0 ∧ g P.genericPoint = Q.genericPoint := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.toIsSeparated
  have : IsSeparated (g ≫ sX) := hY.toIsSeparated
  have := isSeparated_toTerminal_of_isSeparated sX
  have := isSeparated_toTerminal_of_isSeparated (g ≫ sX)
  obtain ⟨Q, hQ, hQP⟩ := exists_apply_ne_zero_of_mapPrimeDivisors_apply_ne_zero
    (φ := MMP.Mori.RationalMap.transformPrimeDivisor
      (MMP.Mori.RationalMap.IsBirational.inverse hg)) h
  exact ⟨Q, hQ, genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hg hQP⟩

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd (WithBot.coe_injective h) (by simp)
    | coe d =>
      induction c using ENat.recTopCoe with
      | top => exact absurd (WithBot.coe_injective h) (by simp)
      | coe c =>
        have h' : d + c = n := by exact_mod_cast h
        rw [show ((d : ℕ∞) : WithBot ℕ∞) + 2 = ((d + 2 : ℕ) : WithBot ℕ∞) by norm_cast]
        norm_cast
        omega

/-- A variety has finite dimension. -/
private theorem exists_topologicalKrullDim_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have : IsIntegral X := hX.toIsIntegral
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  have h2 : topologicalKrullDim X ≠ ⊥ := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have : Nonempty (IrreducibleCloseds X) := ⟨IrreducibleCloseds.closureSingleton x⟩
    unfold topologicalKrullDim
    rw [Ne, Order.krullDim_eq_bot_iff]
    exact not_isEmpty_of_nonempty _
  generalize topologicalKrullDim X = d at h1 h2
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl h2
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd rfl h1
    | coe n => exact ⟨n, rfl⟩

/-- A prime divisor `P` of `Y` exceptional over `X` has its generic point in `Ex(f)`: over the
biregular locus of `f` the generic point of `P` goes to a point of coheight one. -/
private theorem genericPoint_mem_exceptionalSet {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) {Y : Scheme.{u}} {f : Y ⟶ X} {P : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Flips.IsExceptionalPrimeDivisor sX f P) :
    P.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set Y) := by
  obtain ⟨hY, hf, hp, hexc⟩ := h
  set D := MMP.Flips.ProperDivisorOver.mk ⟨Y, f, hY, hf, P⟩ hp
  have h2 : 2 ≤ Order.coheight (f P.genericPoint) := by
    unfold MMP.Flips.ProperDivisorOver.IsExceptional at hexc
    rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint,
      hn] at hexc
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (f P.genericPoint)
    rw [hn] at h
    exact (withBot_add_two_le_iff h).mp hexc
  by_contra hmem
  have hV : f P.genericPoint ∈ biregularLocus f := by
    by_contra hV
    exact hmem (mem_exceptionalSet.mpr hV)
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hV, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-! ### Birational morphisms -/

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open subset of the
target is birational. -/
private theorem isBirationalMorphism_of_isIso_morphismRestrict {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) (U : Y.Opens)
    (hU : (U : Set Y).Nonempty) [IsIso (f ∣_ U)] : IsBirationalMorphism f := by
  obtain ⟨y, hy⟩ := hU
  have hV : ((f ⁻¹ᵁ U : X.Opens) : Set X).Nonempty := ⟨_, ((inv (f ∣_ U)) ⟨y, hy⟩).2⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f (f ⁻¹ᵁ U) U hV ⟨y, hy⟩ le_rfl ?_
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private theorem isBirationalMorphism_comp {V X' X : Scheme.{u}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : IsBirationalMorphism g) (hμ : IsBirationalMorphism μ) :
    IsBirationalMorphism (g ≫ μ) := by
  have : Nonempty V := (IrreducibleSpace.isIrreducible_univ V).nonempty.to_subtype.map Subtype.val
  have : Nonempty X' :=
    (IrreducibleSpace.isIrreducible_univ X').nonempty.to_subtype.map Subtype.val
  obtain ⟨Wg, hWgne, hWg⟩ := IsBirationalMorphism.exists_isOpenImmersion hg
  obtain ⟨Wμ, hWμne, hWμ⟩ := IsBirationalMorphism.exists_isOpenImmersion hμ
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (Wg.ι ≫ g).isOpenEmbedding.isOpen_range Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  have h1 : IsOpenImmersion (U.ι ≫ g) := by
    rw [← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rw [hfac]
    exact h1
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  have hU : IsOpenImmersion (U.ι ≫ g ≫ μ) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    infer_instance
  let V' : X.Opens := (U.ι ≫ g ≫ μ).opensRange
  have hle : U ≤ (g ≫ μ) ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (g ≫ μ) U V' ⟨_, hwU⟩
    ⟨_, ⟨⟨w.1, hwU⟩, rfl⟩⟩ hle ?_
  have e : (g ≫ μ).resLE V' U hle = (U.ι ≫ g ≫ μ).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- A proper birational morphism onto a normal variety is biregular at the generic point. -/
private theorem genericPoint_mem_biregularLocus {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : MMP.Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) :
    genericPoint X ∈ biregularLocus f := by
  haveI : IsNormal X := hX.2
  haveI := hX.1
  haveI := hY
  have h := two_le_closedsCodimension_compl_biregularLocus sX f hf
  by_contra hη
  have h2 := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h) (genericPoint X) hη
  have h0 : Order.coheight (genericPoint X) = 0 := Order.coheight_eq_zero.mpr fun y _ =>
    (Scheme.le_iff_specializes).mpr ((genericPoint_spec X).specializes (Set.mem_univ y))
  rw [h0] at h2
  exact absurd h2 (by decide)

/-! ### Projectivity -/

/-- **A projective morphism in the sense of EGA onto a scheme H-projective over a field is
H-projective**, the target carrying an ample invertible sheaf. -/
private theorem isProjectiveMorphism_of_isProjective_of_isProjectiveMorphism {k : Type u}
    [Field k] {Y Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (hsZ : IsProjectiveMorphism sZ)
    (f : Y ⟶ Z) (hf : IsProjective f) : IsProjectiveMorphism f := by
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of k))
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sZ _
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective _
      (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.1 hsZ).1)
  haveI := hL
  exact isProjectiveMorphism_of_isProjective f L hLa hf

/-! ### Graphs -/

/-- **A separated morphism split by an open immersion over a nonempty open is an isomorphism
there.** Let `f : Γ ⟶ X` be separated with `Γ` irreducible, and `j : O ⟶ Γ` an open immersion
from a nonempty open `O ⊆ X` with `j ≫ f = O ↪ X`. Then `f` is an isomorphism over `O`, with
inverse `j`: every morphism `g` out of `Γ` is `j ≫ g` on `f⁻¹(O)`. -/
private theorem isIso_morphismRestrict_of_comp_eq_ι {Γ X : Scheme.{u}} [IrreducibleSpace Γ]
    (f : Γ ⟶ X) [IsSeparated f] (O : X.Opens) (hO : (O : Set X).Nonempty)
    (j : O.toScheme ⟶ Γ) [IsOpenImmersion j] (hj : j ≫ f = O.ι) :
    IsIso (f ∣_ O) ∧ ∀ {Z : Scheme.{u}} (g : Γ ⟶ Z), (f ⁻¹ᵁ O).ι ≫ g = (f ∣_ O) ≫ j ≫ g := by
  have hrange : Set.range j ⊆ Set.range (f ⁻¹ᵁ O).ι := by
    rintro _ ⟨o, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (j o) ∈ O
    rw [← Scheme.Hom.comp_apply, hj]
    exact o.2
  set j₀ := IsOpenImmersion.lift (f ⁻¹ᵁ O).ι j hrange with hj₀def
  have hj₀ : j₀ ≫ (f ⁻¹ᵁ O).ι = j := IsOpenImmersion.lift_fac _ _ _
  have hsec : j₀ ≫ f ∣_ O = 𝟙 _ := by
    rw [← cancel_mono O.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hj₀, hj,
      Category.id_comp]
  haveI : IsOpenImmersion (j₀ ≫ (f ⁻¹ᵁ O).ι) := by
    rw [hj₀]
    infer_instance
  haveI : IsOpenImmersion j₀ := IsOpenImmersion.of_comp j₀ (f ⁻¹ᵁ O).ι
  haveI : IsClosedImmersion (j₀ ≫ f ∣_ O) := by
    rw [hsec]
    infer_instance
  haveI : IsClosedImmersion j₀ := IsClosedImmersion.of_comp j₀ (f ∣_ O)
  have hsurj : Function.Surjective j₀ := by
    have hpre : _root_.IsPreconnected (Set.univ : Set (f ⁻¹ᵁ O).toScheme) := by
      have hirr : IsPreirreducible ((f ⁻¹ᵁ O : Γ.Opens) : Set Γ) :=
        (IrreducibleSpace.isIrreducible_univ Γ).isPreirreducible.open_subset (f ⁻¹ᵁ O).isOpen
          (Set.subset_univ _)
      exact (Subtype.preconnectedSpace hirr.isPreconnected).isPreconnected_univ
    obtain ⟨o, ho⟩ := hO
    have hcl := hpre.subset_isClopen (s := Set.univ)
      ⟨j₀.isClosedEmbedding.isClosed_range, j₀.isOpenEmbedding.isOpen_range⟩
      ⟨j₀ ⟨o, ho⟩, Set.mem_univ _, ⟨o, ho⟩, rfl⟩
    exact fun x => hcl (Set.mem_univ x)
  haveI : IsIso j₀ := (isIso_iff_isOpenImmersion_and_surjective j₀).2 ⟨inferInstance, ⟨hsurj⟩⟩
  haveI : IsIso (f ∣_ O) := by
    have : IsIso (j₀ ≫ f ∣_ O) := by
      rw [hsec]
      infer_instance
    exact IsIso.of_isIso_comp_left j₀ (f ∣_ O)
  refine ⟨inferInstance, fun g => ?_⟩
  have h2 : f ∣_ O ≫ j₀ = 𝟙 _ := by
    rw [← cancel_epi j₀, ← Category.assoc, hsec, Category.id_comp, Category.comp_id]
  rw [← hj₀, Category.assoc, reassoc_of% h2]

/-- The pointwise form of `(f⁻¹ O).ι ≫ g = (f ∣_ O) ≫ κ`. -/
private theorem apply_eq_of_ι_comp_eq {Γ X Z : Scheme.{u}} (f : Γ ⟶ X) (O : X.Opens)
    (g : Γ ⟶ Z) (κ : O.toScheme ⟶ Z) (H : (f ⁻¹ᵁ O).ι ≫ g = (f ∣_ O) ≫ κ) {γ : Γ}
    (hγ : f γ ∈ O) : g γ = κ ⟨f γ, hγ⟩ := by
  let x : (f ⁻¹ᵁ O).toScheme := ⟨γ, hγ⟩
  have h1 : ((f ⁻¹ᵁ O).ι ≫ g) x = ((f ∣_ O) ≫ κ) x := by rw [H]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
  refine h1.trans (congrArg κ (Subtype.ext ?_))
  change O.ι ((f ∣_ O) x) = f ((f ⁻¹ᵁ O).ι x)
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

/-- **The closure of the graph of a birational map.** Let `φ : X ⤏ X'` be a birational map of
projective varieties over `k`, an isomorphism `φ.source ≅ φ.target`. The closure `Γ` of its graph
in `X' ×_k X` is a variety with projective projections `p₁ : Γ ⟶ X` and `p₂ : Γ ⟶ X'`, an
isomorphism over `φ.source` and `φ.target` respectively, and `p₂ = φ ∘ p₁` there. -/
private theorem exists_graph {k : Type u} [Field k] {X X' : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k)) (hXv : MMP.Mori.IsVariety k sX)
    (hX'v : MMP.Mori.IsVariety k sX') (hXp : IsProjectiveMorphism sX)
    (hX'p : IsProjectiveMorphism sX') (φ : X.PartialIso X') (hφ : φ.IsOver sX sX') :
    ∃ (Γ : Scheme.{u}) (p₁ : Γ ⟶ X) (p₂ : Γ ⟶ X'), MMP.Mori.IsVariety k (p₁ ≫ sX) ∧
      p₂ ≫ sX' = p₁ ≫ sX ∧ IsProjectiveMorphism p₁ ∧ IsProjectiveMorphism p₂ ∧
      IsIso (p₁ ∣_ φ.source) ∧ IsIso (p₂ ∣_ φ.target) ∧
      (p₁ ⁻¹ᵁ φ.source).ι ≫ p₂ = (p₁ ∣_ φ.source) ≫ φ.iso.hom ≫ φ.target.ι ∧
      (p₂ ⁻¹ᵁ φ.target).ι ≫ p₁ = (p₂ ∣_ φ.target) ≫ φ.iso.inv ≫ φ.source.ι := by
  haveI := hXv
  haveI := hX'v
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType sX
  set O : X.Opens := φ.source
  set O' : X'.Opens := φ.target
  have hOne : (O : Set X).Nonempty := φ.dense_source.nonempty
  have hO'ne : (O' : Set X').Nonempty := φ.dense_target.nonempty
  haveI : Nonempty O := hOne.to_subtype
  have hcond : (φ.iso.hom ≫ O'.ι) ≫ sX' = O.ι ≫ sX := by
    rw [Category.assoc]
    exact hφ
  let s : O.toScheme ⟶ Limits.pullback sX' sX := Limits.pullback.lift _ O.ι hcond
  haveI : IsImmersion s := by
    have : IsImmersion (s ≫ Limits.pullback.snd sX' sX) := by
      rw [Limits.pullback.lift_snd]; infer_instance
    exact IsImmersion.of_comp s (Limits.pullback.snd _ _)
  haveI : NoetherianSpace O := NoetherianSpace.set (O : Set X)
  haveI : QuasiCompact s := quasiCompact_of_noetherianSpace_source s
  haveI : IsOpenImmersion s.toImage := isOpenImmersion_toImage s (.inl inferInstance)
  haveI : IsIntegral s.image :=
    (Scheme.Hom.isVariety_image k s (Limits.pullback.snd sX' sX ≫ sX)).toIsIntegral
  let p₁ : s.image ⟶ X := s.imageι ≫ Limits.pullback.snd sX' sX
  let p₂ : s.image ⟶ X' := s.imageι ≫ Limits.pullback.fst sX' sX
  have hj₁ : s.toImage ≫ p₁ = O.ι := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, Limits.pullback.lift_snd]
  have hj₂ : s.toImage ≫ p₂ = φ.iso.hom ≫ O'.ι := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, Limits.pullback.lift_fst]
  have hj'₂ : (φ.iso.inv ≫ s.toImage) ≫ p₂ = O'.ι := by
    rw [Category.assoc, hj₂, Iso.inv_hom_id_assoc]
  obtain ⟨hp₁O, hp₁g⟩ := isIso_morphismRestrict_of_comp_eq_ι p₁ O hOne s.toImage hj₁
  obtain ⟨hp₂O', hp₂g⟩ := isIso_morphismRestrict_of_comp_eq_ι p₂ O' hO'ne _ hj'₂
  refine ⟨s.image, p₁, p₂, ?_, ?_, ?_, ?_, hp₁O, hp₂O', by rw [hp₁g p₂, hj₂], ?_⟩
  · have := Scheme.Hom.isVariety_image k s (Limits.pullback.snd sX' sX ≫ sX)
    rwa [← Category.assoc] at this
  · simp only [p₁, p₂, Category.assoc, Limits.pullback.condition]
  · exact (MMP.isProjectiveMorphism_of_isClosedImmersion _).comp
      (hX'p.baseChange sX)
  · change IsProjectiveMorphism (s.imageι ≫ Limits.pullback.fst sX' sX)
    rw [← Limits.pullbackSymmetry_hom_comp_snd]
    exact (MMP.isProjectiveMorphism_of_isClosedImmersion _).comp
      ((MMP.isProjectiveMorphism_of_isClosedImmersion _).comp
        (hXp.baseChange sX'))
  · rw [hp₂g p₁, Category.assoc, hj₁]

/-- If `p₂ = φ ∘ p₁` over `φ.source` and `p₁ = φ⁻¹ ∘ p₂` over `φ.target`, then the inverse images
of corresponding opens `U ↔ U'` under `p₁` and `p₂` agree. -/
private theorem preimage_eq_preimage_of_partialIso {Γ X X' : Scheme.{u}} {p₁ : Γ ⟶ X}
    {p₂ : Γ ⟶ X'} {φ : X.PartialIso X'} {U : X.Opens} {U' : X'.Opens} (hU : U ≤ φ.source)
    (hU' : U' ≤ φ.target)
    (hUU' : φ.source.ι ⁻¹ᵁ U = φ.iso.hom ⁻¹ᵁ (φ.target.ι ⁻¹ᵁ U'))
    (h₁₂ : (p₁ ⁻¹ᵁ φ.source).ι ≫ p₂ = (p₁ ∣_ φ.source) ≫ φ.iso.hom ≫ φ.target.ι)
    (h₂₁ : (p₂ ⁻¹ᵁ φ.target).ι ≫ p₁ = (p₂ ∣_ φ.target) ≫ φ.iso.inv ≫ φ.source.ι) :
    p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U' := by
  ext γ
  refine ⟨fun hγ => ?_, fun hγ => ?_⟩
  · have hγO : p₁ γ ∈ φ.source := hU hγ
    have hx : (⟨p₁ γ, hγO⟩ : φ.source.toScheme) ∈ φ.source.ι ⁻¹ᵁ U := hγ
    rw [hUU'] at hx
    change p₂ γ ∈ U'
    rw [apply_eq_of_ι_comp_eq p₁ _ p₂ _ h₁₂ hγO]
    exact hx
  · have hγO' : p₂ γ ∈ φ.target := hU' hγ
    let y' : φ.target.toScheme := ⟨p₂ γ, hγO'⟩
    change p₁ γ ∈ U
    rw [apply_eq_of_ι_comp_eq p₂ _ p₁ _ h₂₁ hγO']
    have hx : φ.iso.inv y' ∈ φ.iso.hom ⁻¹ᵁ (φ.target.ι ⁻¹ᵁ U') := by
      change φ.target.ι (φ.iso.hom (φ.iso.inv y')) ∈ U'
      rw [Scheme.inv_hom_apply]
      exact hγ
    rw [← hUU'] at hx
    exact hx

/-- An identity `p₂ = κ ∘ p₁` over an open `O` persists after precomposition with any `F`. -/
private theorem ι_comp_comp_eq_morphismRestrict_comp {Y Γ X Z : Scheme.{u}} (F : Y ⟶ Γ)
    (p₁ : Γ ⟶ X) (p₂ : Γ ⟶ Z) (O : X.Opens) {κ : O.toScheme ⟶ Z}
    (h : (p₁ ⁻¹ᵁ O).ι ≫ p₂ = (p₁ ∣_ O) ≫ κ) :
    ((F ≫ p₁) ⁻¹ᵁ O).ι ≫ F ≫ p₂ = ((F ≫ p₁) ∣_ O) ≫ κ := by
  have e : (F ∣_ (p₁ ⁻¹ᵁ O)) ≫ (p₁ ⁻¹ᵁ O).ι ≫ p₂ = (F ⁻¹ᵁ (p₁ ⁻¹ᵁ O)).ι ≫ F ≫ p₂ :=
    (reassoc_of% (morphismRestrict_ι F (p₁ ⁻¹ᵁ O))) p₂
  rw [h, ← Category.assoc, ← morphismRestrict_comp] at e
  exact e.symm

/-! ### Snc-preserving resolutions over a chart -/

/-- Every point of an snc divisor specializes from a point of the divisor of coheight one, the
generic point of a component through it. -/
private theorem exists_coheight_eq_one_of_isSNCSubset {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {S : Closeds X} (hS : IsSNCSubset sX S) :
    ∀ x ∈ (S : Set X), ∃ e ∈ (S : Set X), Order.coheight e = 1 ∧ e ⤳ x := by
  rcases hS with rfl | ⟨s, hs, -⟩
  · exact fun x hx => absurd hx (Set.notMem_empty x)
  · intro x hx
    rw [← hs] at hx ⊢
    obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hx
    refine ⟨E.genericPoint, Set.mem_iUnion₂.mpr ⟨E, hE, genericPoint_mem_support E⟩,
      E.coheight_genericPoint, ?_⟩
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hxE

/-- **The divisor `D` of components of `T` has the right trace on a chart.** Let `ψ : V ≅ U` be an
isomorphism from an open `V ⊆ Y₁`, and `T ⊆ Y₁` with `T ∩ V = ψ⁻¹ B`, where every point of `B`
specializes from a point of `B` of coheight one. If `SD ⊆ T` is closed and contains every point
of `T` of coheight one, then `SD ∩ V = ψ⁻¹ B` as well. -/
private theorem preimage_ι_eq_preimage_of_coheight_eq_one {Y₁ U : Scheme.{u}} {V : Y₁.Opens}
    (ψ : V.toScheme ⟶ U) [IsIso ψ] {B : Set U}
    (hB : ∀ x ∈ B, ∃ e ∈ B, Order.coheight e = 1 ∧ e ⤳ x) {T SD : Set Y₁}
    (hT : ∀ y : V.toScheme, y.1 ∈ T ↔ ψ y ∈ B) (hSDc : IsClosed SD) (hSDT : SD ⊆ T)
    (hTD : ∀ y : Y₁, Order.coheight y = 1 → y ∈ T → y ∈ SD) :
    V.ι ⁻¹' SD = ψ ⁻¹' B := by
  ext y
  refine ⟨fun hy => (hT y).mp (hSDT hy), fun hy => ?_⟩
  obtain ⟨e, heB, he, hey⟩ := hB _ hy
  have hψz : ψ ((inv ψ) e) = e := by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  have hzy : (inv ψ) e ⤳ y := by
    have h := hey.map (inv ψ).continuous
    rwa [← Scheme.Hom.comp_apply, IsIso.hom_inv_id] at h
  have hzc : Order.coheight (V.ι ((inv ψ) e)) = 1 := by
    rw [Topology.IsOpenEmbedding.coheight_eq _ V.ι.isOpenEmbedding,
      ← Topology.IsOpenEmbedding.coheight_eq _ ψ.isOpenEmbedding, hψz, he]
  have hzT : V.ι ((inv ψ) e) ∈ T := (hT _).mpr (by rwa [hψz])
  exact (hzy.map V.ι.continuous).mem_closed hSDc (hTD _ hzc hzT)

/-- The union of the supports of a finite set of prime divisors is closed. -/
private theorem isClosed_sup_support {Y : Scheme.{u}} (D : Finset (MMP.Mori.PrimeDivisor Y)) :
    IsClosed (D.sup fun E => (E.idealSheaf.support : Set Y)) := by
  rw [Finset.sup_set_eq_biUnion]
  exact isClosed_biUnion_finset fun E _ => E.idealSheaf.support.isClosed

/-- The prime divisors contained in `T` have their union of supports inside `T`. -/
private theorem sup_support_subset_of_finite {Y : Scheme.{u}} {T : Set Y}
    (hT : {P : MMP.Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ T}.Finite) :
    (hT.toFinset.sup fun E => (E.idealSheaf.support : Set Y)) ⊆ T := by
  rw [Finset.sup_set_eq_biUnion]
  intro y hy
  obtain ⟨E, hE, hyE⟩ := Set.mem_iUnion₂.mp hy
  rw [Set.Finite.mem_toFinset] at hE
  exact hE hyE

/-- Every point of coheight one of a closed `T` lies on a prime divisor contained in `T`. -/
private theorem mem_sup_support_of_coheight_eq_one {Y : Scheme.{u}} {T : Set Y}
    (hTc : IsClosed T) (hT : {P : MMP.Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ T}.Finite)
    {y : Y} (hy : Order.coheight y = 1) (hyT : y ∈ T) :
    y ∈ hT.toFinset.sup fun E => (E.idealSheaf.support : Set Y) := by
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy
  have hQ : (Q.support : Set Y) = closure {y} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  rw [Finset.sup_set_eq_biUnion]
  refine Set.mem_iUnion₂.mpr ⟨Q, ?_, show y ∈ (Q.support : Set Y) from hQ ▸ subset_closure rfl⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hQ]
  exact closure_minimal (Set.singleton_subset_iff.mpr hyT) hTc

/-- A prime divisor whose generic point lies in a closed set is contained in it. -/
private theorem support_subset_of_genericPoint_mem {Y : Scheme.{u}} (S : Closeds Y)
    {Q : MMP.Mori.PrimeDivisor Y} (hQ : Q.genericPoint ∈ (S : Set Y)) :
    (Q.support : Set Y) ⊆ S := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact closure_minimal (Set.singleton_subset_iff.mpr hQ) S.isClosed

/-- The generic point of a prime divisor off `Ex(g)` maps to a point of coheight one. -/
private theorem coheight_map_genericPoint_of_notMem_exceptionalSet {Y Y₁ : Scheme.{u}}
    (g : Y ⟶ Y₁) {Q : MMP.Mori.PrimeDivisor Y}
    (hQ : Q.genericPoint ∉ (Mori.exceptionalSet g : Set Y)) :
    Order.coheight (g Q.genericPoint) = 1 := by
  have hb : g Q.genericPoint ∈ biregularLocus g := by
    by_contra hb
    exact hQ (mem_exceptionalSet.mpr hb)
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus g hb, Q.coheight_genericPoint]

/-- The pointwise form of `(f⁻¹ U).ι ≫ f = (f ∣_ U) ≫ U.ι`. -/
private theorem ι_apply_morphismRestrict {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (y : (f ⁻¹ᵁ U).toScheme) : U.ι ((f ∣_ U) y) = f y.1 :=
  morphismRestrict_base_coe f U y

/-- If `P₂ = φ ∘ P₁` over `φ.source` and `U ≤ φ.source`, then `P₂ = φ ∘ P₁` pointwise over `U`. -/
private theorem homOfLE_comp_apply_morphismRestrict {Y X X' : Scheme.{u}} {P₁ : Y ⟶ X}
    {P₂ : Y ⟶ X'} {φ : X.PartialIso X'} {U : X.Opens} (hU : U ≤ φ.source)
    (hc : (P₁ ⁻¹ᵁ φ.source).ι ≫ P₂ = (P₁ ∣_ φ.source) ≫ φ.iso.hom ≫ φ.target.ι)
    (y : (P₁ ⁻¹ᵁ U).toScheme) :
    (X.homOfLE hU ≫ φ.iso.hom ≫ φ.target.ι) ((P₁ ∣_ U) y) = P₂ y.1 := by
  have hyO : P₁ y.1 ∈ φ.source := hU (ι_apply_morphismRestrict P₁ U y ▸ ((P₁ ∣_ U) y).2)
  have e : X.homOfLE hU ((P₁ ∣_ U) y) = ⟨P₁ y.1, hyO⟩ := by
    apply Subtype.ext
    change φ.source.ι (X.homOfLE hU ((P₁ ∣_ U) y)) = _
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, ι_apply_morphismRestrict]
  rw [apply_eq_of_ι_comp_eq P₁ _ P₂ _ hc hyO, Scheme.Hom.comp_apply, e]

/-- **The trace of `T` on a chart.** Over `P₁⁻¹ U ≅ U`, a point lies in
`P₁⁻¹ A ∪ P₂⁻¹ A' ∪ Ex(P₁) ∪ Ex(P₂)` exactly when its image lies in `A ∪ φ⁻¹ A'`. -/
private theorem mem_union_exceptionalSet_iff {Y X X' : Scheme.{u}} {P₁ : Y ⟶ X} {P₂ : Y ⟶ X'}
    {φ : X.PartialIso X'} {U : X.Opens} {U' : X'.Opens} (hU : U ≤ φ.source)
    (hP₁U : IsIso (P₁ ∣_ U)) (hP₂U' : IsIso (P₂ ∣_ U')) (hW : P₁ ⁻¹ᵁ U = P₂ ⁻¹ᵁ U')
    (hc : (P₁ ⁻¹ᵁ φ.source).ι ≫ P₂ = (P₁ ∣_ φ.source) ≫ φ.iso.hom ≫ φ.target.ι)
    (A : Closeds X) (A' : Closeds X') (y : (P₁ ⁻¹ᵁ U).toScheme) :
    y.1 ∈ P₁ ⁻¹' (A : Set X) ∪ P₂ ⁻¹' (A' : Set X') ∪ (Mori.exceptionalSet P₁ : Set Y) ∪
        (Mori.exceptionalSet P₂ : Set Y) ↔
      (P₁ ∣_ U) y ∈ ((A.preimage U.ι.continuous ⊔
        A'.preimage (X.homOfLE hU ≫ φ.iso.hom ≫ φ.target.ι).continuous : Closeds U.toScheme) :
          Set U.toScheme) := by
  have hBU : (P₁ ∣_ U) y ∈ ((A.preimage U.ι.continuous ⊔
      A'.preimage (X.homOfLE hU ≫ φ.iso.hom ≫ φ.target.ι).continuous : Closeds U.toScheme) :
        Set U.toScheme) ↔ P₁ y.1 ∈ A ∨ P₂ y.1 ∈ A' := by
    rw [← ι_apply_morphismRestrict P₁ U y, ← homOfLE_comp_apply_morphismRestrict hU hc y]
    exact Iff.rfl
  rw [hBU]
  refine ⟨fun hT => ?_, fun h => Or.inl (Or.inl h)⟩
  rcases hT with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (le_biregularLocus hP₁U y.2) (mem_exceptionalSet.mp h)
  · exact absurd (le_biregularLocus hP₂U' ((SetLike.ext_iff.mp hW y.1).mp y.2))
      (mem_exceptionalSet.mp h)

/-- The generic point of a proper birational model of a normal variety lies neither over the
support of a divisor nor in the exceptional set. -/
private theorem genericPoint_notMem_of_isBirationalMorphism {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (Δ : QDivisor X)
    [IsIntegral Y] (P : Y ⟶ X) [IsProper P] (hY : MMP.Mori.IsVariety k (P ≫ sX))
    (hP : IsBirationalMorphism P) :
    P (genericPoint Y) ∉ (Δ.supp : Set X) ∧
      genericPoint Y ∉ (Mori.exceptionalSet P : Set Y) := by
  haveI : IsIntegral X := hX.1.toIsIntegral
  haveI : IsDominant P := hP.isDominant
  have hη := MMP.Positivity.map_genericPoint_eq_of_isDominant P
  exact ⟨fun h => MMP.Fourfold.genericPoint_notMem_supp Δ (hη ▸ h),
    fun h => mem_exceptionalSet.mp h (hη ▸ genericPoint_mem_biregularLocus hX _ hY hP)⟩

/-! ### Log resolutions -/

/-- **A resolution which is snc along `Ex(g) ∪ g⁻¹(Supp D)` gives a log resolution.** Let
`P : Y₁ ⟶ X` be a proper birational morphism from a variety onto a normal variety `X` with a
boundary `B`, and `D` a finite set of prime divisors of `Y₁` through every point of coheight one
lying over `Supp B` or in `Ex(P)`. If `g : Y ⟶ Y₁` is a resolution with `Ex(g) ∪ g⁻¹(Supp D)` an
snc divisor, then `g ≫ P` is a log resolution of `(X, B)`. -/
private theorem isLogResolution_comp {k : Type u} [Field k] {X Y₁ Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (B : RDivisor X)
    (hB : MMP.Flips.IsBoundary B) (P : Y₁ ⟶ X) [IsProper P] (hP : IsBirationalMorphism P)
    (sY₁ : Y₁ ⟶ Spec (.of k)) (hs : P ≫ sX = sY₁) (hY₁ : MMP.Mori.IsVariety k sY₁)
    (D : Finset (MMP.Mori.PrimeDivisor Y₁))
    (hD : ∀ y : Y₁, Order.coheight y = 1 →
      (P y ∈ (B.supp : Set X) ∨ y ∈ (Mori.exceptionalSet P : Set Y₁)) →
        y ∈ (D.sup fun E => (E.idealSheaf.support : Set Y₁)))
    (g : Y ⟶ Y₁) [IsProper g] (hg : IsResolutionOfVariety sY₁ g)
    (hsnc : IsSNCClosedSubset (g ≫ sY₁)
      ((Mori.exceptionalSet g : Set Y) ∪ g ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set Y₁)))) :
    MMP.Flips.IsLogResolution sX B (g ≫ P) := by
  classical
  subst hs
  obtain ⟨hXv, hXn⟩ := hX
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have hYv : MMP.Mori.IsVariety k ((g ≫ P) ≫ sX) := by simpa using hg.isVariety_source
  have hYsm : IsSmoothScheme ((g ≫ P) ≫ sX) := by simpa using hg.isSmoothScheme
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : IsIntegral Y₁ := hY₁.toIsIntegral
  haveI : LocallyOfFiniteType ((g ≫ P) ≫ sX) := hYv.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation ((g ≫ P) ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := (g ≫ P) ≫ sX)).mpr inferInstance
  haveI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType ((g ≫ P) ≫ sX)
  have hgP : IsBirationalMorphism (g ≫ P) := isBirationalMorphism_comp hg.isBirationalMorphism hP
  set SD : Set Y₁ := D.sup fun E => (E.idealSheaf.support : Set Y₁)
  have hSDc : IsClosed SD := isClosed_sup_support D
  set S : Closeds Y := Mori.exceptionalSet g ⊔ ⟨g ⁻¹' SD, hSDc.preimage g.continuous⟩ with hSdef
  have hSsnc : IsSNCSubset ((g ≫ P) ≫ sX) S :=
    isSNCSubset_of_isSNCClosedSubset (Category.assoc g P sX ▸ hsnc)
  obtain ⟨n₀, hn₀⟩ := exists_topologicalKrullDim_eq hXv
  have key : ∀ Q : MMP.Mori.PrimeDivisor Y,
      (P (g Q.genericPoint) ∈ (B.supp : Set X) ∨
        g Q.genericPoint ∈ (Mori.exceptionalSet P : Set Y₁)) → Q.genericPoint ∈ (S : Set Y) := by
    intro Q hQ
    by_cases hQg : Q.genericPoint ∈ (Mori.exceptionalSet g : Set Y)
    · exact Or.inl hQg
    · exact Or.inr (hD _ (coheight_map_genericPoint_of_notMem_exceptionalSet g hQg) hQ)
  set Z : Closeds Y₁ := (biregularLocus g).compl
  have hπ : IsIso (g ∣_ ⟨(Z : Set Y₁)ᶜ, Z.isClosed.isOpen_compl⟩) := by
    rw [show (⟨(Z : Set Y₁)ᶜ, Z.isClosed.isOpen_compl⟩ : Y₁.Opens) = biregularLocus g from
      TopologicalSpace.Opens.ext (compl_compl _)]
    exact isBiregular_biregularLocus g
  have hQ : ∀ Q : MMP.Mori.PrimeDivisor Y,
      ((MMP.Flips.birationalInverseTransform (g ≫ P) hgP B).coeff Q ≠ 0 ∨
        MMP.Flips.IsExceptionalPrimeDivisor sX (g ≫ P) Q) → (Q.support : Set Y) ⊆ S := by
    rintro Q (h | h)
    · obtain ⟨R, hR, hgR⟩ :=
        exists_map_genericPoint_eq_of_birationalInverseTransform_ne_zero hXv hYv hgP h
      refine support_subset_of_genericPoint_mem S (key Q (Or.inl ?_))
      rw [← Scheme.Hom.comp_apply, hgR]
      exact DivisorWithCoeffs.support_subset_supp hR (genericPoint_mem_support R)
    · have hEx := genericPoint_mem_exceptionalSet hn₀ h
      rcases MMP.Fourfold.SNCWeight.SNCModel.exceptionalSet_comp_subset P g Z hπ
        (B := (Z : Set Y₁) ∪ (Mori.exceptionalSet P : Set Y₁)) Set.subset_union_right
        Set.subset_union_left hEx with h1 | h2
      · exact support_subset_of_genericPoint_mem S (Or.inl (mem_exceptionalSet.mpr h1))
      · exact support_subset_of_genericPoint_mem S (key Q (Or.inr h2))
  obtain ⟨G, hG01, hGiff, hGsnc⟩ := exists_isSNCDivisor_of_isSNCSubset hYsm hSsnc _ hQ
  exact ⟨⟨⟨hXv, hXn⟩, hB⟩, hYv, hYsm, inferInstance, hgP, G, hG01, hGiff, hGsnc⟩

/-- An open of `Y` mapped isomorphically onto an open of `X` smooth over `k` is smooth over `k`. -/
private theorem isSmoothScheme_ι_comp_of_isIso {k : Type u} [Field k] {Y X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (P : Y ⟶ X)
    (hP : P ≫ sX = sY) (U : X.Opens) [IsIso (P ∣_ U)] [Smooth (U.ι ≫ sX)] :
    IsSmoothScheme ((P ⁻¹ᵁ U).ι ≫ sY) := by
  haveI : LocallyOfFinitePresentation ((P ⁻¹ᵁ U).ι ≫ sY) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := _)).mpr inferInstance
  subst hP
  rw [isSmoothScheme_iff, ← reassoc_of% (morphismRestrict_ι P U)]
  infer_instance

/-- **A common log resolution from a common smooth model.** Let `P₁ : Y₁ ⟶ X` and
`P₂ : Y₁ ⟶ X'` be proper birational morphisms from a normal projective variety, with
`P₂ = φ ∘ P₁` over `φ.source`, isomorphisms over `U` and `U'` with `P₁⁻¹ U = P₂⁻¹ U'`. Then the
snc-preserving log resolution of `Y₁` along `P₁⁻¹ Supp Δ ∪ P₂⁻¹ Supp Δ' ∪ Ex(P₁) ∪ Ex(P₂)` gives
log resolutions of `(X, Δ)` and `(X', Δ')`, isomorphisms over `U` and `U'`. -/
private theorem exists_isLogResolution_of_model {k : Type u} [Field k] [CharZero k]
    {X X' Y₁ : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX')
    {Δ : MMP.Mori.QDivisor X} {Δ' : MMP.Mori.QDivisor X'}
    (hΔ : IsBoundary (MMP.Mori.QDivisor.toRDivisor Δ))
    (hΔ' : IsBoundary (MMP.Mori.QDivisor.toRDivisor Δ'))
    {φ : X.PartialIso X'} {U : X.Opens} {U' : X'.Opens} (hU : U ≤ φ.source)
    (hUs : MMP.Mori.IsSmoothScheme (U.ι ≫ sX))
    (hUΔΔ' : MMP.Mori.IsSNCSubset (U.ι ≫ sX) (Δ.supp.preimage U.ι.continuous ⊔
      Δ'.supp.preimage (X.homOfLE hU ≫ φ.iso.hom ≫ φ.target.ι).continuous))
    {sY₁ : Y₁ ⟶ Spec (.of k)} (hY₁n : IsNormalVariety k sY₁) (hsY₁H : IsProjectiveMorphism sY₁)
    {P₁ : Y₁ ⟶ X} {P₂ : Y₁ ⟶ X'}
    (hP₁proj : IsProjectiveMorphism P₁) (hP₂proj : IsProjectiveMorphism P₂)
    (hP₁bir : IsBirationalMorphism P₁) (hP₂bir : IsBirationalMorphism P₂)
    (hP₁s : P₁ ≫ sX = sY₁) (hP₂s : P₂ ≫ sX' = sY₁)
    (hP₁U : IsIso (P₁ ∣_ U)) (hP₂U' : IsIso (P₂ ∣_ U')) (hW : P₁ ⁻¹ᵁ U = P₂ ⁻¹ᵁ U')
    (hc : (P₁ ⁻¹ᵁ φ.source).ι ≫ P₂ = (P₁ ∣_ φ.source) ≫ φ.iso.hom ≫ φ.target.ι) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (q : Y ⟶ X'),
      IsLogResolution sX (MMP.Mori.QDivisor.toRDivisor Δ) p ∧ IsProjectiveMorphism p ∧
      IsLogResolution sX' (MMP.Mori.QDivisor.toRDivisor Δ') q ∧ IsProjectiveMorphism q ∧
      (p ⁻¹ᵁ φ.source).ι ≫ q = (p ∣_ φ.source) ≫ φ.iso.hom ≫ φ.target.ι ∧
      IsIso (p ∣_ U) ∧ IsIso (q ∣_ U') := by
  classical
  haveI : IsProper P₁ := isProper_of_isProjectiveMorphism P₁ hP₁proj
  haveI : IsProper P₂ := isProper_of_isProjectiveMorphism P₂ hP₂proj
  haveI := hX.1
  haveI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType sX
  haveI : NoetherianSpace U := NoetherianSpace.set (U : Set X)
  haveI : QuasiCompact (U.ι ≫ sX) := quasiCompact_of_noetherianSpace_source _
  haveI := hY₁n.1
  haveI : IsIntegral Y₁ := hY₁n.1.toIsIntegral
  haveI : IsNoetherian Y₁ := isNoetherian_of_locallyOfFiniteType sY₁
  haveI : Smooth (U.ι ≫ sX) := Aux.smooth_of_isSmoothScheme' _ hUs
  haveI := hP₁U
  set T : Set Y₁ := P₁ ⁻¹' (Δ.supp : Set X) ∪ P₂ ⁻¹' (Δ'.supp : Set X') ∪
    (Mori.exceptionalSet P₁ : Set Y₁) ∪ (Mori.exceptionalSet P₂ : Set Y₁) with hTdef
  have hTc : IsClosed T :=
    (((Δ.supp.isClosed.preimage P₁.continuous).union
      (Δ'.supp.isClosed.preimage P₂.continuous)).union
      (Mori.exceptionalSet P₁).isClosed).union (Mori.exceptionalSet P₂).isClosed
  have hηT : genericPoint Y₁ ∉ T := by
    have h₁ := genericPoint_notMem_of_isBirationalMorphism hX Δ P₁ (hP₁s ▸ hY₁n.1) hP₁bir
    have h₂ := genericPoint_notMem_of_isBirationalMorphism hX' Δ' P₂ (hP₂s ▸ hY₁n.1) hP₂bir
    rintro (((h | h) | h) | h)
    exacts [h₁.1 h, h₂.1 h, h₁.2 h, h₂.2 h]
  have hDfin := finite_setOf_support_subset hTc fun h' => hηT (h' ▸ Set.mem_univ _)
  have hTD := fun y : Y₁ => mem_sup_support_of_coheight_eq_one (y := y) hTc hDfin
  obtain ⟨Y, g, hgres, -, hgsnc, hgiso⟩ :=
    exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sY₁ hY₁n hDfin.toFinset
  have hgH : IsProjectiveMorphism g :=
    isProjectiveMorphism_of_isProjective_of_isProjectiveMorphism sY₁ hsY₁H g hgres.isProjective
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hgH
  haveI hgV : IsIso (g ∣_ (P₁ ⁻¹ᵁ U)) := by
    refine hgiso _ (isSmoothScheme_ι_comp_of_isIso P₁ hP₁s U) ?_
    rw [preimage_ι_eq_preimage_of_coheight_eq_one (P₁ ∣_ U)
      (exists_coheight_eq_one_of_isSNCSubset hUΔΔ')
      (mem_union_exceptionalSet_iff hU hP₁U hP₂U' hW hc Δ.supp Δ'.supp)
      (isClosed_sup_support _) (sup_support_subset_of_finite hDfin) hTD, ← hP₁s,
      ← reassoc_of% (morphismRestrict_ι P₁ U)]
    exact IsSNCClosedSubset.preimage_of_isIso _ (isSNCClosedSubset_of_isSNCSubset hUΔΔ')
  haveI hgV' : IsIso (g ∣_ (P₂ ⁻¹ᵁ U')) := hW ▸ hgV
  refine ⟨Y, g ≫ P₁, g ≫ P₂, isLogResolution_comp sX hX _ hΔ P₁ hP₁bir sY₁ hP₁s hY₁n.1
      hDfin.toFinset (fun y hy h => hTD y hy ?_) g hgres hgsnc, hgH.comp hP₁proj,
    isLogResolution_comp sX' hX' _ hΔ' P₂ hP₂bir sY₁ hP₂s hY₁n.1 hDfin.toFinset
      (fun y hy h => hTD y hy ?_) g hgres hgsnc, hgH.comp hP₂proj,
    ι_comp_comp_eq_morphismRestrict_comp g P₁ P₂ _ hc, ?_, ?_⟩
  · rw [QDivisor.supp_toRDivisor] at h
    exact h.elim (fun h => Or.inl (Or.inl (Or.inl h))) fun h => Or.inl (Or.inr h)
  · rw [QDivisor.supp_toRDivisor] at h
    exact h.elim (fun h => Or.inl (Or.inl (Or.inr h))) Or.inr
  · rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' hgV hP₁U
  · rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' hgV' hP₂U'

/-- **Common log resolution preserving an snc locus.** Let `φ` be a birational map over `k`
(characteristic zero) between normal projective varieties `X` and `X'` with `ℚ`-boundaries `Δ`,
`Δ'`, and let `U ⊆ φ.source`, smooth over `k`, map isomorphically onto `U' ⊆ φ.target` under
`φ`, with `Supp Δ ∩ U`, `Supp Δ' ∩ U'` and `(Supp Δ ∪ φ⁻¹ Supp Δ') ∩ U` snc. Then there are
projective log resolutions `p : Y ⟶ X` of `(X, Δ)` and `q : Y ⟶ X'` of `(X', Δ')` with
`q = φ ∘ p` on `p⁻¹(φ.source)`, such that `p` is an isomorphism over `U` and `q` is an
isomorphism over `U'`. -/
@[mmp "lem_mmp_common_resolution_strata"]
public theorem exists_isLogResolution_isIso_restrict_of_partialIso {k : Type u} [Field k]
    [CharZero k] {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k))
    (hX : MMP.Mori.IsNormalVariety k sX) (hX' : MMP.Mori.IsNormalVariety k sX')
    (hXp : IsProjectiveMorphism sX) (hX'p : IsProjectiveMorphism sX')
    (Δ : MMP.Mori.QDivisor X) (Δ' : MMP.Mori.QDivisor X')
    (hΔ : IsBoundary (MMP.Mori.QDivisor.toRDivisor Δ))
    (hΔ' : IsBoundary (MMP.Mori.QDivisor.toRDivisor Δ'))
    (φ : X.PartialIso X') (hφ : φ.IsOver sX sX')
    (U : X.Opens) (U' : X'.Opens) (hU : U ≤ φ.source) (hU' : U' ≤ φ.target)
    (hUU' : φ.source.ι ⁻¹ᵁ U = φ.iso.hom ⁻¹ᵁ (φ.target.ι ⁻¹ᵁ U'))
    (hUs : MMP.Mori.IsSmoothScheme (U.ι ≫ sX))
    (hUΔ : MMP.Mori.IsSNCSubset (U.ι ≫ sX) (Δ.supp.preimage U.ι.continuous))
    (hUΔ' : MMP.Mori.IsSNCSubset (U'.ι ≫ sX') (Δ'.supp.preimage U'.ι.continuous))
    (hUΔΔ' : MMP.Mori.IsSNCSubset (U.ι ≫ sX) (Δ.supp.preimage U.ι.continuous ⊔
      Δ'.supp.preimage (X.homOfLE hU ≫ φ.iso.hom ≫ φ.target.ι).continuous)) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (q : Y ⟶ X'),
      IsLogResolution sX (MMP.Mori.QDivisor.toRDivisor Δ) p ∧ IsProjectiveMorphism p ∧
      IsLogResolution sX' (MMP.Mori.QDivisor.toRDivisor Δ') q ∧ IsProjectiveMorphism q ∧
      (p ⁻¹ᵁ φ.source).ι ≫ q = (p ∣_ φ.source) ≫ φ.iso.hom ≫ φ.target.ι ∧
      IsIso (p ∣_ U) ∧ IsIso (q ∣_ U') := by
  classical
  obtain ⟨hXv, hXn⟩ := hX
  obtain ⟨hX'v, hX'n⟩ := hX'
  haveI := hXv
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : IsIntegral X' := hX'v.toIsIntegral
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hXp
  haveI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType sX
  obtain ⟨Γ, p₁, p₂, hΓv, hp₂s, hp₁proj, hp₂proj, hp₁O, hp₂O', hc, hc'⟩ :=
    exists_graph sX sX' hXv hX'v hXp hX'p φ hφ
  haveI : IsIntegral Γ := hΓv.toIsIntegral
  haveI := hp₁O
  haveI := hp₂O'
  have hW : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U' := preimage_eq_preimage_of_partialIso hU hU' hUU' hc hc'
  haveI hp₁U : IsIso (p₁ ∣_ U) := TupleResolutionAux.isIso_restrict_of_le p₁ hU
  haveI hp₂U' : IsIso (p₂ ∣_ U') := TupleResolutionAux.isIso_restrict_of_le p₂ hU'
  haveI : Smooth (U.ι ≫ sX) := Aux.smooth_of_isSmoothScheme' _ hUs
  have hWsm : p₁ ⁻¹ᵁ U ≤ smoothLocus (p₁ ≫ sX) := by
    apply le_smoothLocus
    rw [← reassoc_of% (morphismRestrict_ι p₁ U)]
    infer_instance
  obtain ⟨Y₁, f₁, hY₁v, hf₁proj, hf₁bir, hY₁sm, hf₁iso, -⟩ := exists_isStrongResolution _ hΓv
  haveI := hf₁iso
  haveI hf₁W : IsIso (f₁ ∣_ (p₁ ⁻¹ᵁ U)) := TupleResolutionAux.isIso_restrict_of_le f₁ hWsm
  haveI hf₁W' : IsIso (f₁ ∣_ (p₂ ⁻¹ᵁ U')) := hW ▸ hf₁W
  have hsΓproj : IsProjectiveMorphism (p₁ ≫ sX) := hp₁proj.comp hXp
  have hf₁H : IsProjectiveMorphism f₁ :=
    isProjectiveMorphism_of_isProjective_of_isProjectiveMorphism _ hsΓproj f₁ hf₁proj
  haveI : IsProper f₁ := isProper_of_isProjectiveMorphism f₁ hf₁H
  haveI : IsProper p₁ := isProper_of_isProjectiveMorphism p₁ hp₁proj
  haveI : IsProper p₂ := isProper_of_isProjectiveMorphism p₂ hp₂proj
  haveI := hY₁v
  haveI : IsIntegral Y₁ := hY₁v.toIsIntegral
  have hY₁n : IsNormalVariety k (f₁ ≫ p₁ ≫ sX) :=
    ⟨hY₁v, (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hY₁sm).2⟩
  exact exists_isLogResolution_of_model ⟨hXv, hXn⟩ ⟨hX'v, hX'n⟩ hΔ hΔ' hU hUs hUΔΔ' hY₁n
    (hf₁H.comp hsΓproj) (hf₁H.comp hp₁proj) (hf₁H.comp hp₂proj)
    (isBirationalMorphism_comp hf₁bir
      (isBirationalMorphism_of_isIso_morphismRestrict p₁ _ φ.dense_source.nonempty))
    (isBirationalMorphism_comp hf₁bir
      (isBirationalMorphism_of_isIso_morphismRestrict p₂ _ φ.dense_target.nonempty))
    (Category.assoc _ _ _) (by rw [Category.assoc, hp₂s])
    (by
      rw [morphismRestrict_comp]
      exact IsIso.comp_isIso' hf₁W hp₁U)
    (by
      rw [morphismRestrict_comp]
      exact IsIso.comp_isIso' hf₁W' hp₂U')
    (congrArg (f₁ ⁻¹ᵁ ·) hW) (ι_comp_comp_eq_morphismRestrict_comp f₁ p₁ p₂ _ hc)

end MMP.Flips

end
