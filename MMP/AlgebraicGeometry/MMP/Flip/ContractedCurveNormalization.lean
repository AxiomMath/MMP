module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Contracted curves along flips, relative Picard number one, and standard coefficients

Three auxiliary facts used in the construction and termination of flips.

**Normalizations along a flip.** Let `φ : X ⟶ Z` be a small contraction of a threefold and
`φ⁺ : X⁺ ⟶ Z` a flip of `φ` with birational map `g : X ⤏ X⁺`. Let `S ⊆ X` be a prime divisor with
birational transform `S⁺ = g_* S`. If no flipped curve lies in `S⁺` while some flipping curve of
`φ` lies in `S`, then every morphism `ψ : S^ν ⟶ (S⁺)^ν` of the normalizations that agrees with
`g` on a dense open subset of `S^ν` maps some proper integral curve of `S^ν` to a point.

The normalizations `ν : S^ν ⟶ X` and `ν⁺ : (S⁺)^ν ⟶ X⁺` are finite (a scheme of finite type over a
field is Nagata), so they are closed, surjective onto `S` and `S⁺`, and strictly monotone for the
specialization order. A point of height one over a flipping curve `Γ ⊆ S` lifts to a point
`c ∈ S^ν` of height one, whose closure is a proper curve `C` over a closed point `z ∈ Z`. Since
`S^ν` is reduced and `Z` is separated, `φ⁺ ∘ ν⁺ ∘ ψ = φ ∘ ν`. If `ψ` were not constant on `C`, the
closure of `ν⁺(ψ(c))` would be an irreducible closed subset of `S⁺ ∩ φ⁺⁻¹(z)` of positive
dimension; a maximal irreducible subset of `φ⁺⁻¹(z)` containing it lies in the exceptional set of
`φ⁺`, hence has dimension at most one, so it is that closure: a flipped curve contained in `S⁺`.

**Relative Picard number one.** Let `f : X ⟶ Z` be a projective contraction of normal varieties
with `ρ(X/Z) = 1`, and `H` an `f`-ample `ℚ`-Cartier `ℚ`-divisor. Since `N¹(X/Z)` is
one-dimensional and the class of `H` is nonzero, every `ℚ`-Cartier `ℚ`-divisor `L` is numerically
`f`-equivalent to a multiple `λ H`, and `λ` is rational, being a quotient of two rational
intersection numbers with one contracted curve.

**Standard coefficients.** For a finite family of reals `b i > 0` and `c > 0`, only finitely many
`(m, (m_i)_i)` satisfy `(m - 1) / m + ∑ i, m_i b_i / m ≤ 1 - c`: the inequality forces `m ≤ c⁻¹`
and `m_i ≤ b_i⁻¹`.

## Main results

* `MMP.Flips.IsFlip.exists_properCurve_isContractedBy_normalization`: a morphism of
  normalizations along a flip contracts a proper curve.
* `MMP.Flips.exists_properCurve_isContractedBy_of_relativePicardNumber_eq_one`: if `ρ(X/Z) = 1`
  some proper curve is contracted by `f`.
* `MMP.Flips.exists_intersectionNumber_eq_mul_of_relativePicardNumber_eq_one`: if `ρ(X/Z) = 1`
  there is `λ ∈ ℚ` with `L · C = λ (H · C)` for every proper curve `C` contracted by `f`.
* `MMP.Flips.finite_setOf_standardCoefficient_le`: finiteness of standard coefficients bounded
  away from one.

## Implementation notes

The normalization `S^ν ⟶ X` of a prime divisor is `MMP.Fourfold.primeDivisorNormalization`. That
`ψ` agrees with `g` on a dense open subset is expressed through a representative `g₀` of `g`:
there is a dense open `U ⊆ S^ν` mapped by `ν` into the domain of `g₀` on which `ν⁺ ∘ ψ = g₀ ∘ ν`.
Contracted curves are `MMP.Mori.ProperCurve`s with `MMP.Mori.ProperCurve.IsContractedBy`, and
`L · C` is `MMP.Mori.QDivisor.intersectionNumber` along the closed immersion `C ⟶ X`. Relative
ampleness of a `ℚ`-divisor `H` is `MMP.Flips.IsRelativelyAmple` of its image as an `ℝ`-divisor.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.13.3, 5,
  7.4.4
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori MMP.Fourfold

/-! ### A morphism of normalizations along a flip contracts a curve -/

section NormalizationContractsCurve

/-- A locally quasi-finite morphism does not identify a point with one of its specializations. -/
private lemma eq_of_specializes_of_apply_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    {x y : X} (h : x ⤳ y) (he : f x = f y) : x = y := by
  have := (f.isDiscrete_preimage_singleton (f y)).to_subtype
  have hs : (⟨x, he⟩ : f ⁻¹' {f y}) ⤳ ⟨y, rfl⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp h
  have hmem := hs.mem_open (isOpen_discrete {⟨y, rfl⟩}) rfl
  exact congrArg Subtype.val hmem

/-- A finite morphism does not identify a point with one of its specializations. -/
private lemma eq_of_specializes_of_apply_eq_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] {x y : X} (h : x ⤳ y) (he : f x = f y) : x = y :=
  eq_of_specializes_of_apply_eq f h he

/-- A locally quasi-finite morphism is strictly monotone for the specialization order. -/
private lemma strictMono_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] : StrictMono (f : X → Y) := by
  intro x y hxy
  have h : y ⤳ x := Scheme.le_iff_specializes.mp hxy.le
  refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr (h.map f.continuous)) fun hge => ?_
  have he : f x = f y := ((Scheme.le_iff_specializes.mp hge).antisymm (h.map f.continuous)).eq
  exact hxy.ne (eq_of_specializes_of_apply_eq f h he.symm).symm

/-- Every irreducible subset of `F` lies in a maximal irreducible subset of `F`. -/
private lemma exists_maximal_isIrreducible {X : Type*} [TopologicalSpace X] {F s : Set X}
    (hs : IsIrreducible s) (hsF : s ⊆ F) :
    ∃ m, s ⊆ m ∧ Maximal (fun S : Set X => IsIrreducible S ∧ S ⊆ F) m := by
  have H : ∀ c ⊆ {t : Set X | IsPreirreducible t ∧ t ⊆ F}, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {t : Set X | IsPreirreducible t ∧ t ⊆ F}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hcc _
    refine ⟨⋃₀ c, ⟨?_, Set.sUnion_subset fun t ht => (hc ht).2⟩,
      fun _ hxc => Set.subset_sUnion_of_mem hxc⟩
    intro u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩
    obtain ⟨p, hpc, hyp⟩ := Set.mem_sUnion.1 hy
    obtain ⟨q, hqc, hxq⟩ := Set.mem_sUnion.1 hx
    rcases hcc.total hpc hqc with hpq | hqp
    · obtain ⟨x, hxp, hxuv⟩ := (hc hqc).1 u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
      exact ⟨x, Set.mem_sUnion_of_mem hxp hqc, hxuv⟩
    · obtain ⟨x, hxp, hxuv⟩ := (hc hpc).1 u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
      exact ⟨x, Set.mem_sUnion_of_mem hxp hpc, hxuv⟩
  obtain ⟨m, hsm, hm⟩ := zorn_subset_nonempty _ H s ⟨hs.isPreirreducible, hsF⟩
  exact ⟨m, hsm, ⟨⟨hs.nonempty.mono hsm, hm.prop.1⟩, hm.prop.2⟩,
    fun S hS hmS => hm.2 ⟨hS.1.isPreirreducible, hS.2⟩ hmS⟩

/-- A maximal irreducible subset of a closed set is closed. -/
private lemma isClosed_of_maximal_isIrreducible {X : Type*} [TopologicalSpace X] {F m : Set X}
    (hF : IsClosed F) (hm : Maximal (fun S : Set X => IsIrreducible S ∧ S ⊆ F) m) :
    IsClosed m :=
  closure_subset_iff_isClosed.mp (hm.2 ⟨hm.1.1.closure, closure_minimal hm.1.2 hF⟩ subset_closure)

/-- The normalization of a prime divisor of a scheme locally of finite type over a field, as a
scheme over the divisor, is finite. -/
private lemma isFinite_normalization {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (S : MMP.Mori.PrimeDivisor X) :
    haveI := S.integral
    IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) := by
  haveI := S.integral
  exact normalization_isFinite S.idealSheaf.subscheme (isJapaneseScheme_of_isNagataScheme _
    (isNagataScheme_of_locallyOfFiniteType_over_field k (S.idealSheaf.subschemeι ≫ sX)))

/-- The normalization `ν : S^ν ⟶ X` of a prime divisor is finite. -/
private lemma isFinite_primeDivisorNormalization {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (S : MMP.Mori.PrimeDivisor X) :
    IsFinite (primeDivisorNormalization S) := by
  haveI := isFinite_normalization sX S
  unfold primeDivisorNormalization
  infer_instance

/-- The normalization `ν : S^ν ⟶ X` of a prime divisor maps onto `S`. -/
private lemma exists_primeDivisorNormalization_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (S : MMP.Mori.PrimeDivisor X) {x : X}
    (hx : x ∈ S.support) : ∃ y, primeDivisorNormalization S y = x := by
  haveI := S.integral
  haveI := isFinite_normalization sX S
  set n := Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have hdom : IsDominant n := by
    letI := Stacks.AlgebraicGeometry.Normalization.quasiCompact_fromGenericPointResidueFields
      S.idealSheaf.subscheme (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
    set f := Stacks.AlgebraicGeometry.Normalization.fromGenericPointResidueFields
      S.idealSheaf.subscheme
    have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp f.toNormalization f.fromNormalization
  have hrange : Set.range n = Set.univ := by
    rw [← n.isClosedMap.isClosed_range.closure_eq]
    exact hdom.denseRange.closure_range
  have hx' : x ∈ Set.range S.idealSheaf.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hx
  obtain ⟨a, rfl⟩ := hx'
  obtain ⟨b, hb⟩ : a ∈ Set.range n := hrange ▸ Set.mem_univ a
  exact ⟨b, by simp [primeDivisorNormalization, ← hb, n]⟩

/-- The normalization of a prime divisor is a reduced scheme. -/
private lemma isReduced_primeDivisorNormalizationScheme {X : Scheme.{u}}
    (S : MMP.Mori.PrimeDivisor X) : IsReduced (primeDivisorNormalizationScheme S) := by
  have := S.integral
  have : IsReduced (Stacks.AlgebraicGeometry.Normalization.genericPointResidueSpectrum
      S.idealSheaf.subscheme) := by
    unfold Stacks.AlgebraicGeometry.Normalization.genericPointResidueSpectrum
    have : ∀ i, IsReduced ((sigmaOpenCover (fun η : genericPoints S.idealSheaf.subscheme ↦
        Spec (.of (S.idealSheaf.subscheme.residueField η.1)))).X i) := fun η => by
      change IsReduced (Spec _); infer_instance
    exact IsReduced.of_openCover _ (sigmaOpenCover _)
  let := Stacks.AlgebraicGeometry.Normalization.quasiCompact_fromGenericPointResidueFields
    S.idealSheaf.subscheme (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  unfold primeDivisorNormalizationScheme Stacks.AlgebraicGeometry.Normalization.normalizationScheme
  infer_instance

/-- A finite morphism `ν : T ⟶ X` onto a closed irreducible subset `Γ` of positive dimension in a
finite-dimensional scheme: some point `c ∈ T` of height one has `ν({c}⁻) ⊆ Γ`. -/
private lemma exists_height_eq_one_of_isFinite {T X : Scheme.{u}} (ν : T ⟶ X) [IsFinite ν]
    {Γ : Set X} (hΓc : IsClosed Γ) (hΓirr : IsIrreducible Γ)
    (hΓdim : 0 < topologicalKrullDim Γ) (hdim : topologicalKrullDim X ≠ ⊤)
    (hΓν : Γ ⊆ Set.range ν) :
    ∃ c : T, Order.height c = 1 ∧ ∀ x ∈ closure {c}, ν x ∈ Γ := by
  set γ := hΓirr.genericPoint
  have hγ : closure {γ} = Γ := (hΓirr.isGenericPoint_genericPoint hΓc).def
  have h1 : topologicalKrullDim Γ = (Order.height γ : WithBot ℕ∞) := by
    rw [← topologicalKrullDim_closure_singleton_eq_height γ, hγ]
  have hγtop : Order.height γ ≠ ⊤ := by
    intro htop
    have h2 : topologicalKrullDim Γ ≤ topologicalKrullDim X := topologicalKrullDim_subspace_le X Γ
    rw [h1, htop] at h2
    exact hdim (top_le_iff.mp h2)
  have hγ0 : 0 < Order.height γ := by
    have := hΓdim; rw [h1] at this; exact_mod_cast this
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hγtop
  obtain ⟨p, hplast, hplen⟩ := Order.exists_series_of_height_eq_coe γ hn.symm
  have hn1 : 1 ≤ n := by
    rw [← hn] at hγ0; exact_mod_cast hγ0
  set δ := p ⟨1, by omega⟩
  have hδh : Order.height δ = 1 := by
    simpa using Order.height_eq_index_of_length_eq_height_last (p := p)
      (by rw [hplast, hplen, hn]) ⟨1, by omega⟩
  have hδΓ : δ ∈ Γ := by
    have hδγ : δ ≤ γ := hplast ▸ p.monotone (Fin.le_last _)
    rw [← hγ]; exact specializes_iff_mem_closure.mp (Scheme.le_iff_specializes.mp hδγ)
  obtain ⟨c, hc⟩ := hΓν hδΓ
  have hcle : Order.height c ≤ 1 :=
    hδh ▸ hc ▸ Order.height_le_height_apply_of_strictMono ν (strictMono_of_locallyQuasiFinite ν) c
  have hcge : 1 ≤ Order.height c := by
    obtain ⟨δ', hδ'⟩ := not_isMin_iff.mp (Order.height_ne_zero.mp (by rw [hδh]; exact one_ne_zero))
    have hcl : IsClosed (ν '' closure {c}) := ν.isClosedMap _ isClosed_closure
    have hsub : closure {δ} ⊆ ν '' closure {c} :=
      closure_minimal (Set.singleton_subset_iff.mpr ⟨c, subset_closure rfl, hc⟩) hcl
    obtain ⟨y, hy, hyδ⟩ := hsub (specializes_iff_mem_closure.mp
      (Scheme.le_iff_specializes.mp hδ'.le))
    have hyc : y < c := by
      refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr
        (specializes_iff_mem_closure.mpr hy)) fun hcy => ?_
      have : ν c ≤ ν y :=
        Scheme.le_iff_specializes.mpr ((Scheme.le_iff_specializes.mp hcy).map ν.continuous)
      rw [hc, hyδ] at this
      exact hδ'.not_ge this
    exact le_add_self.trans (Order.height_add_one_le hyc)
  refine ⟨c, le_antisymm hcle hcge, fun x hx => ?_⟩
  exact ((specializes_iff_mem_closure.mpr hx).map ν.continuous).mem_closed hΓc (hc ▸ hδΓ)

/-- For a small contraction `φ⁺ : X⁺ ⟶ Z` of a threefold and a closed point `z ∈ Z`, a point
`t ∈ φ⁺⁻¹(z)` with a proper specialization `t'` has closure a maximal irreducible subset of the
fibre `φ⁺⁻¹(z)`. -/
private lemma maximal_closure_singleton_of_lt {k : Type u} [Field k] {X' Z : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {φp : X' ⟶ Z}
    (hsmall : IsSmall k sZ sX' φp) (hdimX' : topologicalKrullDim X' = 3) {z : Z}
    {t t' : X'} (htt'lt : t' < t) (htz : φp t = z) (hz : IsClosed ({z} : Set Z)) :
    Maximal (fun S : Set X' => IsIrreducible S ∧ S ⊆ {y | φp y = z}) (closure {t}) := by
  haveI hvX' : AlgebraicGeometry.IsVariety k sX' := hsmall.isVariety_source
  have htt' : t ⤳ t' := Scheme.le_iff_specializes.mp htt'lt.le
  have hF'c : IsClosed {y : X' | φp y = z} := hz.preimage φp.continuous
  have htF : closure {t} ⊆ {y : X' | φp y = z} :=
    closure_minimal (Set.singleton_subset_iff.mpr htz) hF'c
  obtain ⟨m, htm, hm⟩ := exists_maximal_isIrreducible isIrreducible_singleton.closure htF
  have hmc := isClosed_of_maximal_isIrreducible hF'c hm
  set q := hm.1.1.genericPoint
  have hq : closure {q} = m := (hm.1.1.isGenericPoint_genericPoint hmc).def
  have htq : t ∈ closure {q} := hq ▸ htm (subset_closure rfl)
  have ht'm : t' ∈ m := htm (specializes_iff_mem_closure.mp htt')
  obtain ⟨V, W, hV, -, hle, hiso⟩ := hsmall.exists_isIso
  -- the generic point `q` of `m` lies in the exceptional set `V`: off `V` the map `φ⁺` is
  -- injective, so `m` would be a closed point
  have hqV : q ∈ (V : Set X') := by
    by_contra hqV
    haveI : JacobsonSpace X' := LocallyOfFiniteType.jacobsonSpace sX'
    have hloc : IsLocallyClosed (m ∩ (V : Set X')ᶜ) :=
      hmc.isLocallyClosed.inter V.isClosed.isOpen_compl.isLocallyClosed
    obtain ⟨q', ⟨hq'm, hq'V⟩, hq'c⟩ :=
      nonempty_inter_closedPoints (show (m ∩ (V : Set X')ᶜ).Nonempty from
        ⟨q, by rw [← hq]; exact subset_closure rfl, hqV⟩) hloc
    set r := φp.resLE W.compl V.compl hle
    have hrinj : Function.Injective r := r.isOpenEmbedding.injective
    have hr : ∀ a, Scheme.Opens.ι W.compl (r a) = φp (Scheme.Opens.ι V.compl a) := fun a => by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
    have hqq' : q' = q := by
      have hqV' : q ∈ V.compl := hqV
      have hq'V' : q' ∈ V.compl := hq'V
      have hφ : φp q' = φp q := by rw [hm.1.2 hq'm, hm.1.2 (hq ▸ subset_closure rfl)]
      exact congrArg Subtype.val <| hrinj <| (Scheme.Opens.ι W.compl).isOpenEmbedding.injective
        ((hr ⟨q', hq'V'⟩).trans (hφ.trans (hr ⟨q, hqV'⟩).symm))
    have hm1 : m = {q} := by
      rw [← hq, ← hqq']; exact hq'c.closure_eq
    rw [hm1] at htm ht'm
    exact htt'lt.ne' ((htm (subset_closure rfl)).trans ht'm.symm)
  -- hence `dim m ≤ 1`, so `m = {t}⁻`
  have hqt : q = t := by
    by_contra hqt
    have htqlt : t < q := by
      refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr
        (specializes_iff_mem_closure.mpr htq)) fun h => hqt ?_
      exact ((specializes_iff_mem_closure.mpr htq).antisymm
        (Scheme.le_iff_specializes.mp h)).eq
    have hcoh : 2 ≤ Order.coheight q := (le_closedsCodimension_iff_le_coheight.mp hV) q hqV
    have hsum := topologicalKrullDim_closure_singleton_add_coheight sX' q
    rw [topologicalKrullDim_closure_singleton_eq_height, hdimX'] at hsum
    have hsum' : Order.height q + Order.coheight q = 3 :=
      WithBot.coe_injective (by push_cast; exact hsum)
    have hqh : 2 ≤ Order.height q := by
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ Order.height t + 1 := by
          gcongr; exact le_add_self.trans (Order.height_add_one_le htt'lt)
        _ ≤ Order.height q := Order.height_add_one_le htqlt
    have := add_le_add hqh hcoh
    rw [hsum'] at this
    exact absurd this (by decide)
  rwa [← hqt, hq]

/-- A morphism `ψ` of reduced schemes over `X` and `X'` that agrees on a dense open subset with a
partial map `g₀ : X ⇀ X'` over a separated `Z` lies over `Z`. -/
private lemma comp_eq_of_agree {X X' Z T T' : Scheme.{u}} [IsReduced X] [IsReduced T]
    [Z.IsSeparated] {φ : X ⟶ Z} {φp : X' ⟶ Z} {g₀ : X.PartialMap X'}
    (h : (g₀.compHom φp).equiv φ.toPartialMap) (ν : T ⟶ X) (νp : T' ⟶ X') (ψ : T ⟶ T')
    (U : T.Opens) (hUd : Dense (U : Set T)) (hU : U ≤ ν ⁻¹ᵁ g₀.domain)
    (hUeq : U.ι ≫ ψ ≫ νp = ν.resLE g₀.domain U hU ≫ g₀.hom) :
    ψ ≫ νp ≫ φp = ν ≫ φ := by
  have hD : g₀.hom ≫ φp = g₀.domain.ι ≫ φ := by
    obtain ⟨W, hW, hWl, hWr, hWe⟩ := h
    have hWl' : W ≤ g₀.domain := hWl
    haveI : IsDominant (X.homOfLE hWl') := Opens.isDominant_homOfLE hW _
    refine ext_of_isDominant (X.homOfLE hWl') ?_
    rw [Scheme.homOfLE_ι_assoc]
    simp only [Scheme.PartialMap.restrict, Scheme.PartialMap.compHom] at hWe
    refine hWe.trans ?_
    simp only [Scheme.Hom.toPartialMap]
    exact Scheme.homOfLE_ι_assoc ..
  haveI : IsDominant U.ι := Opens.isDominant_ι hUd
  refine ext_of_isDominant U.ι ?_
  rw [reassoc_of% hUeq, hD, Scheme.Hom.resLE_comp_ι_assoc]

/-- Let `φ : X ⟶ Z` be a small contraction of a threefold, `φ⁺ : X⁺ ⟶ Z` a flip of `φ` with
birational map `g`, `S ⊆ X` a prime divisor and `S⁺ = g_* S`. If no flipped curve is contained in
`S⁺` and some flipping curve of `φ` is contained in `S`, then every morphism `ψ : S^ν ⟶ (S⁺)^ν`
agreeing with `g` on a dense open subset contracts some proper integral curve of `S^ν` to a
point. -/
@[mmp "lem_fa4_normalization_morphism_contracts_curve"]
public theorem IsFlip.exists_properCurve_isContractedBy_normalization
    {k : Type u} [Field k] {X Z X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {E : RDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}
    (hflip : IsFlip k sX sZ sX' E φ φp g) (hdim : topologicalKrullDim X = 3)
    {S : Mori.PrimeDivisor X} {Sp : Mori.PrimeDivisor X'}
    (hS : Mori.RationalMap.transformPrimeDivisor g S = some Sp)
    (hflipped : ∀ C : Set X', IsFlippedCurveOf k sX sZ sX' E φ φp g C → ¬ C ⊆ Sp.support)
    (hflipping : ∃ C : Set X, IsFlippingCurve k sX sZ φ C ∧ C ⊆ S.support)
    (ψ : primeDivisorNormalizationScheme S ⟶ primeDivisorNormalizationScheme Sp)
    (hψ : ∃ g₀ : X.PartialMap X', g₀.toRationalMap = g ∧
      ∃ U : (primeDivisorNormalizationScheme S).Opens,
        Dense (U : Set (primeDivisorNormalizationScheme S)) ∧
        ∃ hU : U ≤ primeDivisorNormalization S ⁻¹ᵁ g₀.domain,
          U.ι ≫ ψ ≫ primeDivisorNormalization Sp =
            (primeDivisorNormalization S).resLE g₀.domain U hU ≫ g₀.hom) :
    ∃ C : ProperCurve (primeDivisorNormalization S ≫ sX), C.IsContractedBy ψ := by
  classical
  obtain ⟨Γ, ⟨hvX, hvZ, hφs, hφp, z, hz, hΓmax, hΓdim⟩, hΓS⟩ := hflipping
  haveI := hvX
  haveI := hvZ
  haveI := hφp
  haveI hvX' : AlgebraicGeometry.IsVariety k sX' := hflip.isNormalVariety_flip.1
  haveI : IsProper φp := hflip.isProper
  haveI : Z.IsSeparated :=
    ⟨by rw [show Limits.terminal.from Z = sZ ≫ Limits.terminal.from _ from
      Limits.terminal.hom_ext _ _]; infer_instance⟩
  set ν := primeDivisorNormalization S
  set νp := primeDivisorNormalization Sp
  haveI hνfin : IsFinite ν := isFinite_primeDivisorNormalization sX S
  haveI hνpfin : IsFinite νp := isFinite_primeDivisorNormalization sX' Sp
  haveI := isReduced_primeDivisorNormalizationScheme S
  have hΓc : IsClosed Γ := isClosed_of_maximal_isIrreducible (hz.preimage φ.continuous) hΓmax
  -- Step 1: `ψ` lies over `Z`: `φ⁺ ∘ ν⁺ ∘ ψ = φ ∘ ν`.
  have hover : ψ ≫ νp ≫ φp = ν ≫ φ := by
    obtain ⟨g₀, rfl, U, hUd, hU, hUeq⟩ := hψ
    haveI : IsIntegral X := hvX.toIsIntegral
    have h : (g₀.compHom φp).equiv φ.toPartialMap := by
      rw [← Scheme.PartialMap.toRationalMap_eq_iff]; exact hflip.isModificationOf.2
    exact comp_eq_of_agree h ν νp ψ U hUd hU hUeq
  have hfib : ∀ y, φp (νp (ψ y)) = φ (ν y) := fun y => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hover]
  -- Step 2: a point `c ∈ S^ν` of height one over the flipping curve `Γ`.
  obtain ⟨c, hch, hcΓ⟩ := exists_height_eq_one_of_isFinite ν hΓc hΓmax.1.1 hΓdim
    (by rw [hdim]; decide) fun x hx => exists_primeDivisorNormalization_eq sX S (hΓS hx)
  have hcz : ∀ x ∈ closure {c}, φ (ν x) = z := fun x hx => hΓmax.1.2 (hcΓ x hx)
  -- Step 3: the proper curve `C = {c}⁻`.
  have hdimc : topologicalKrullDim (curveSubschemeAt c) = 1 := by
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change topologicalKrullDim (closure ({c} : Set _)) = 1
    rw [topologicalKrullDim_closure_singleton_eq_height, hch]; rfl
  have hprop : IsProper (curveSubschemeAtι c ≫ ν ≫ sX) := by
    have hg := MMP.Mori.isProper_comp_of_range_subset_singleton sZ
      (curveSubschemeAtι c ≫ ν ≫ φ) hz ?_
    · rwa [Category.assoc, Category.assoc, hφs] at hg
    · rintro _ ⟨a, rfl⟩
      have ha : curveSubschemeAtι c a ∈ closure {c} := by
        have := Set.mem_range_self (f := curveSubschemeAtι c) a
        rwa [Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
      change (curveSubschemeAtι c ≫ ν ≫ φ) a = z
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact hcz _ ha
  refine ⟨⟨c, ⟨hdimc, hprop⟩⟩, fun x hx => ?_⟩
  change x ∈ closure {c} at hx
  change ψ x = ψ c
  by_contra hne
  -- Step 4: otherwise `{ν⁺(ψ(c))}⁻` is a flipped curve in `S⁺`.
  have hww' : ψ c ⤳ ψ x := (specializes_iff_mem_closure.mpr hx).map ψ.continuous
  have htt' : νp (ψ c) ⤳ νp (ψ x) := hww'.map νp.continuous
  have htne : νp (ψ c) ≠ νp (ψ x) := fun h => hne
    (eq_of_specializes_of_apply_eq_of_isFinite νp hww' h).symm
  set t := νp (ψ c)
  set t' := νp (ψ x)
  have htz : φp t = z := (hfib c).trans (hcz c (subset_closure rfl))
  have htSp : t ∈ Sp.support := range_primeDivisorNormalization_subset Sp ⟨ψ c, rfl⟩
  have htt'lt : t' < t := by
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr htt') fun h => htne ?_
    exact (htt'.antisymm (Scheme.le_iff_specializes.mp h)).eq
  have hth : 1 ≤ Order.height t := le_add_self.trans (Order.height_add_one_le htt'lt)
  have hdimX' : topologicalKrullDim X' = 3 :=
    hflip.isSmall.dim_eq.trans (hflip.isSmall_source.dim_eq.symm.trans hdim)
  have hm := maximal_closure_singleton_of_lt hflip.isSmall hdimX' htt'lt htz hz
  refine hflipped _ ⟨hflip, hvX', hvZ, hflip.isSmall.comp_eq, hflip.isProper, z, hz, hm, ?_⟩ ?_
  · rw [topologicalKrullDim_closure_singleton_eq_height]
    exact_mod_cast lt_of_lt_of_le zero_lt_one hth
  · exact closure_minimal (Set.singleton_subset_iff.mpr htSp) Sp.idealSheaf.support.isClosed

end NormalizationContractsCurve

/-! ### Proportionality of intersection numbers in relative Picard number one -/

section RelativePicardNumberOne

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- On an integral normal scheme, every Cartier Weil divisor `D` has a Cartier divisor whose
degree on every proper curve is `deg_C 𝒪_X(D)`. -/
private theorem exists_cartierDivisor_degree_eq [IsIntegral X] (D : Divisor X)
    (hD : D.IsCartier) : ∃ E : X.CartierDivisor, ∀ C : ProperCurve sX,
      (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
        (D.degreeOn k sX C.ι C.dim_le hD : ℝ) := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  refine ⟨E, fun C => ?_⟩
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  exact_mod_cast (degreeOn_eq_of_iso k sX C.ι C.dim_le e).symm

/-- On an integral normal scheme, every `ℚ`-Cartier `ℚ`-divisor `L` has an `ℝ`-Cartier divisor
with the same intersection numbers with every proper curve. -/
private theorem exists_kCartierDivisor_intersectionNumber_eq [IsIntegral X] (L : QDivisor X)
    (hL : L.IsQCartier) : ∃ δ : KCartierDivisor ℝ X, ∀ C : ProperCurve sX,
      (C.cycle ℝ).intersectionNumber δ = (L.intersectionNumber k sX C.ι C.dim_le hL : ℝ) := by
  set hF := QDivisor.isCartierDivisor_cartierIndex_smul hL
  obtain ⟨E, hE⟩ := exists_cartierDivisor_degree_eq sX hF.toDivisor hF.isCartier_toDivisor
  refine ⟨((L.cartierIndex hL : ℝ))⁻¹ • KCartierDivisor.ofCartier ℝ E, fun C => ?_⟩
  simp only [OneCycle.intersectionNumber, map_smul, LinearMap.smul_apply, smul_eq_mul] at hE ⊢
  rw [hE, QDivisor.intersectionNumber]
  push_cast
  ring

/-- A rational multiple of a Cartier divisor is `ℚ`-Cartier. -/
private theorem isQCartier_smul_toQDivisor {D : Divisor X} (hD : D.IsCartier) (q : ℚ) :
    (q • Divisor.toQDivisor D).IsQCartier := by
  refine ⟨q.den, by exact_mod_cast q.den_ne_zero, q.num • D, ?_, hD.zsmul _⟩
  refine Finsupp.ext fun P => ?_
  change ((q.num * D P : ℤ) : ℚ) = (q.den : ℤ) * (q * (D P : ℚ))
  have := Rat.mul_den_eq_num q
  push_cast
  rw [← this]
  ring

variable {sX}

/-- `(∑ⱼ qⱼ Lⱼ) · C = ∑ⱼ qⱼ deg_C 𝒪_X(Lⱼ)` for Cartier divisors `Lⱼ` and rational `qⱼ`. -/
private theorem intersectionNumber_sum_smul {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {m : ℕ} (q : Fin m → ℚ) (L : Fin m → Divisor X)
    (hL : ∀ j, (L j).IsCartier) (s : Finset (Fin m)) :
    ∃ h : (∑ j ∈ s, q j • Divisor.toQDivisor (L j)).IsQCartier,
      (∑ j ∈ s, q j • Divisor.toQDivisor (L j)).intersectionNumber k sX i hdim h =
        ∑ j ∈ s, q j * (L j).degreeOn k sX i hdim (hL j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using QDivisor.isQCartier_zero, ?_⟩
    simp only [Finset.sum_empty]
    rw [MMP.Fourfold.intersectionNumber_congr sX i hdim _ (QDivisor.isQCartier_toQDivisor
      Divisor.isCartier_zero) (by simp), QDivisor.intersectionNumber_toQDivisor k sX i hdim _
      Divisor.isCartier_zero, Divisor.degreeOn_zero']
    simp
  | insert a s ha ih =>
    obtain ⟨h, ih⟩ := ih
    have ha' := isQCartier_smul_toQDivisor (hL a) (q a)
    have hs := ha'.add h
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨hs, ?_⟩
    rw [QDivisor.intersectionNumber_add' k sX i hdim _ _ ha' h hs, ih,
      MMP.Fourfold.intersectionNumber_smul sX i hdim _ (QDivisor.isQCartier_toQDivisor (hL a))
        (q a) ha',
      QDivisor.intersectionNumber_toQDivisor k sX i hdim _ (hL a)]

/-- **Independence of the presentation.** If the `ℚ`-Cartier `ℚ`-divisor `H` equals
`∑ⱼ rⱼ Lⱼ` as an `ℝ`-divisor, with `Lⱼ` Cartier and `rⱼ ∈ ℝ`, then
`H · C = ∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)`. -/
private theorem intersectionNumber_eq_sum_of_toRDivisor_eq {C : Scheme.{u}} (i : C ⟶ X)
    [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) (H : QDivisor X) (hH : H.IsQCartier)
    {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (h : QDivisor.toRDivisor H = ∑ j, r j • Divisor.toRDivisor (L j)) :
    (H.intersectionNumber k sX i hdim hH : ℝ) =
      ∑ j, r j * (L j).degreeOn k sX i hdim (hL j) := by
  -- test the difference against every `ℚ`-linear functional `π : ℝ → ℚ`
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℚ]
  intro π
  have hcast : ∀ x : ℚ, π (x : ℝ) = x * π 1 := fun x => by
    rw [show (x : ℝ) = x • (1 : ℝ) by rw [Rat.smul_def, mul_one], map_smul, smul_eq_mul]
  have hzs : ∀ (x : ℝ) (n : ℤ), π (x * n) = n * π x := fun x n => by
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  have key : π 1 • H = ∑ j, π (r j) • Divisor.toQDivisor (L j) := by
    refine Finsupp.ext fun P => ?_
    have hP := congrArg (fun G : RDivisor X => G P) h
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul] at hP ⊢
    change ((H P : ℚ) : ℝ) = ∑ j, r j * ((L j P : ℤ) : ℝ) at hP
    change π 1 * H P = ∑ j, π (r j) * ((L j P : ℤ) : ℚ)
    have := congrArg π hP
    rw [hcast, map_sum] at this
    simp only [hzs] at this
    rw [mul_comm, this]
    simp [mul_comm]
  obtain ⟨hs, hsum⟩ := intersectionNumber_sum_smul (sX := sX) i hdim (fun j => π (r j)) L hL
    Finset.univ
  have h1 := MMP.Fourfold.intersectionNumber_smul sX i hdim H hH (π 1)
    (by rw [key]; exact hs)
  rw [MMP.Fourfold.intersectionNumber_congr sX i hdim _ hs key, hsum] at h1
  rw [map_sub, map_sum, hcast]
  simp only [hzs]
  rw [mul_comm, ← h1, sub_eq_zero]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- An `f`-ample Cartier divisor has positive degree on every proper curve contracted by `f`. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier [CompactSpace X] {Z : Scheme.{u}}
    (f : X ⟶ Z) {D : Divisor X} (hD : IsRelativelyAmpleCartier f D) (hDc : D.IsCartier)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 < D.degreeOn k sX C.ι C.dim_le hDc := by
  obtain ⟨hD', hamp⟩ := hD
  haveI := hD'.isInvertibleModule_divisorialSheaf
  have hrel : MMP.Mori.IsRelativelyAmple f D.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hrel C hC

/-- An `f`-ample `ℚ`-Cartier `ℚ`-divisor has positive intersection number with every proper curve
contracted by `f`. -/
private theorem intersectionNumber_pos_of_isRelativelyAmple [CompactSpace X] {Z : Scheme.{u}}
    (f : X ⟶ Z) {H : QDivisor X} (hH : H.IsQCartier)
    (hHa : IsRelativelyAmple f (QDivisor.toRDivisor H)) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) :
    0 < H.intersectionNumber k sX C.ι C.dim_le hH := by
  obtain ⟨m, r, L, hm, hr, hL, hHL⟩ := hHa
  have hLc : ∀ j, (L j).IsCartier := fun j => (hL j).1
  have h := intersectionNumber_eq_sum_of_toRDivisor_eq (sX := sX) C.ι C.dim_le H hH r L hLc hHL
  have hpos : (0 : ℝ) < ∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hLc j) := by
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    refine Finset.sum_pos (fun j _ => mul_pos (hr j) ?_) Finset.univ_nonempty
    exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier f (hL j) (hLc j) C hC
  rw [← h] at hpos
  exact_mod_cast hpos

/-- If `N¹(X/Z)` is one-dimensional, some proper curve is contracted by `f`. -/
theorem exists_properCurve_isContractedBy_of_finrank_eq_one {Z : Scheme.{u}} (f : X ⟶ Z)
    (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1) :
    ∃ C : ProperCurve sX, C.IsContractedBy f := by
  haveI := Module.finite_of_finrank_eq_succ hfin
  obtain ⟨v, hv⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).mp (by rw [hfin]; exact one_pos)
  obtain ⟨δ, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [Ne, Submodule.Quotient.mk_eq_zero, mem_relativeNumericallyTrivialDivisors] at hv
  push Not at hv
  obtain ⟨C, hC, -⟩ := hv
  exact ⟨C, hC⟩

/-- `ρ(X/Z) = 1` says that `N¹(X/Z)` has dimension one. -/
private theorem finrank_eq_one_of_relativePicardNumber_eq_one {Z : Scheme.{u}} {f : X ⟶ Z}
    (hρ : relativePicardNumber sX f = 1) :
    Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1 :=
  Module.finrank_eq_of_rank_eq (by rw [Cardinal.toENat_eq_one.mp hρ]; rfl)

/-- If `ρ(X/Z) = 1`, some proper curve is contracted by `f`. -/
theorem exists_properCurve_isContractedBy_of_relativePicardNumber_eq_one {Z : Scheme.{u}}
    (f : X ⟶ Z) (hρ : relativePicardNumber sX f = 1) :
    ∃ C : ProperCurve sX, C.IsContractedBy f :=
  exists_properCurve_isContractedBy_of_finrank_eq_one f
    (finrank_eq_one_of_relativePicardNumber_eq_one hρ)

/-- **Numerical proportionality in a one-dimensional `N¹(X/Z)`.** If `N¹(X/Z)` is
one-dimensional and `δH` is not numerically trivial on some contracted curve, then every
`ℝ`-Cartier divisor `δL` is numerically `f`-equivalent to a multiple `c • δH`. -/
private theorem exists_intersectionNumber_eq_mul_of_finrank_eq_one {Z : Scheme.{u}} (f : X ⟶ Z)
    (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1)
    (δH δL : KCartierDivisor ℝ X) {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy f)
    (h₀ : (C₀.cycle ℝ).intersectionNumber δH ≠ 0) :
    ∃ c : ℝ, ∀ C : ProperCurve sX, C.IsContractedBy f →
      (C.cycle ℝ).intersectionNumber δL = c * (C.cycle ℝ).intersectionNumber δH := by
  have hne : (Submodule.Quotient.mk δH : RelativeNumericalDivisorClasses sX f) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero, mem_relativeNumericallyTrivialDivisors]
    exact fun h => h₀ (h C₀ hC₀)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hfin (Submodule.Quotient.mk δL)
  have hmem : δL - c • δH ∈ relativeNumericallyTrivialDivisors sX f := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      hc, sub_self]
  refine ⟨c, fun C hC => ?_⟩
  have := (mem_relativeNumericallyTrivialDivisors sX f).mp hmem C hC
  simp only [OneCycle.intersectionNumber, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul] at this ⊢
  linarith

end RelativePicardNumberOne

/-- **Proportionality in relative Picard number one.** Let `f : X ⟶ Z` be a projective
contraction of normal varieties with `ρ(X/Z) = 1` and `H` an `f`-ample `ℚ`-Cartier `ℚ`-divisor.
Then for every `ℚ`-Cartier `ℚ`-divisor `L` there is `λ ∈ ℚ` with `L · C = λ (H · C)` for every
proper curve `C` contracted by `f`. -/
@[mmp "lem_fa5_rho_one_proportional"]
public theorem exists_intersectionNumber_eq_mul_of_relativePicardNumber_eq_one
    {k : Type u} [Field k] {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    (hX : IsNormalVariety k sX) (hZ : IsNormalVariety k sZ) (f : X ⟶ Z)
    (hf : IsContraction k sZ sX f) (hfp : IsProjectiveMorphism f)
    (hρ : relativePicardNumber sX f = 1)
    (H : QDivisor X) (hH : H.IsQCartier) (hHa : IsRelativelyAmple f (QDivisor.toRDivisor H))
    (L : QDivisor X) (hL : L.IsQCartier) :
    ∃ l : ℚ, ∀ C : ProperCurve sX, C.IsContractedBy f →
      L.intersectionNumber k sX C.ι C.dim_le hL =
        l * H.intersectionNumber k sX C.ι C.dim_le hH := by
  haveI : IsIntegral X := hX.1.toIsIntegral
  have hfin := finrank_eq_one_of_relativePicardNumber_eq_one hρ
  obtain ⟨C₀, hC₀⟩ := exists_properCurve_isContractedBy_of_finrank_eq_one f hfin
  have hH₀ := (intersectionNumber_pos_of_isRelativelyAmple f hH hHa C₀ hC₀).ne'
  obtain ⟨δH, hδH⟩ := exists_kCartierDivisor_intersectionNumber_eq sX H hH
  obtain ⟨δL, hδL⟩ := exists_kCartierDivisor_intersectionNumber_eq sX L hL
  obtain ⟨c, hc⟩ := exists_intersectionNumber_eq_mul_of_finrank_eq_one f hfin δH δL hC₀
    (by rw [hδH]; exact_mod_cast hH₀)
  -- the real factor `c` is the rational number `(L · C₀) / (H · C₀)`
  refine ⟨L.intersectionNumber k sX C₀.ι C₀.dim_le hL /
    H.intersectionNumber k sX C₀.ι C₀.dim_le hH, fun C hC => ?_⟩
  have h₀ := hc C₀ hC₀
  have h := hc C hC
  rw [hδL, hδH] at h₀ h
  refine Rat.cast_injective (α := ℝ) ?_
  push_cast
  rw [h, h₀, mul_div_cancel_right₀ _ (by exact_mod_cast hH₀)]

/-! ### Finiteness of standard coefficients bounded away from one -/

/-- A natural number `n` with `n * a ≤ 1` for some `a > 0` is at most `⌈a⁻¹⌉₊`. -/
private lemma le_ceil_inv_of_mul_le_one {n : ℕ} {a : ℝ} (ha : 0 < a) (h : n * a ≤ 1) :
    n ≤ ⌈a⁻¹⌉₊ :=
  Nat.cast_le.mp <| ((le_div_iff₀ ha).mpr (by simpa using h)).trans (by simpa using Nat.le_ceil _)

/-- Clearing the denominator `m`: the standard-coefficient inequality
`(m - 1) / m + ∑ i, m_i b_i / m ≤ 1 - c` is `c m + ∑ i, m_i b_i ≤ 1`. -/
private lemma mul_add_sum_le_one {I : Type*} [Fintype I] {b : I → ℝ} {c : ℝ} {m : ℕ+}
    {v : I → ℕ} (h : ((m : ℝ) - 1) / m + ∑ i, (v i : ℝ) * b i / m ≤ 1 - c) :
    c * m + ∑ i, (v i : ℝ) * b i ≤ 1 := by
  rw [← Finset.sum_div, ← add_div, div_le_iff₀ (by positivity)] at h
  linarith

/-- For a finite index type `I`, positive reals `b i` and `c > 0`, there are only finitely many
`(m, (m_i)_i) ∈ ℕ+ × (I → ℕ)` with `(m - 1) / m + ∑ i, m_i * b_i / m ≤ 1 - c`. -/
@[mmp "lem_fa7_standard_coefficients_finite"]
public theorem finite_setOf_standardCoefficient_le {I : Type*} [Fintype I] (b : I → ℝ)
    (hb : ∀ i, 0 < b i) {c : ℝ} (hc : 0 < c) :
    {p : ℕ+ × (I → ℕ) |
      ((p.1 : ℝ) - 1) / p.1 + ∑ i, (p.2 i : ℝ) * b i / p.1 ≤ 1 - c}.Finite := by
  refine ((Set.finite_Iic (⟨⌈c⁻¹⌉₊ + 1, by omega⟩ : ℕ+)).prod
    (Set.Finite.pi (t := fun i => Set.Iic ⌈(b i)⁻¹⌉₊) fun i => Set.finite_Iic _)).subset ?_
  rintro ⟨m, v⟩ hp
  have key : c * m + ∑ i, (v i : ℝ) * b i ≤ 1 := mul_add_sum_le_one hp
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ (v i : ℝ) * b i := fun i _ => by
    have := (hb i).le; positivity
  refine ⟨?_, fun i _ => le_ceil_inv_of_mul_le_one (hb i) ?_⟩
  · exact Nat.le_succ_of_le <| le_ceil_inv_of_mul_le_one hc <| by
      nlinarith [Finset.sum_nonneg hnn]
  · have : 0 ≤ c * m := by positivity
    exact le_trans (Finset.single_le_sum hnn (Finset.mem_univ i)) (by linarith)

end MMP.Flips
