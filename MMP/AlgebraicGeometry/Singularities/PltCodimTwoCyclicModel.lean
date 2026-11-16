module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.IndexOneCover
public import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
public import MMP.AlgebraicGeometry.Morphisms.Etale.HenselizationColimit
import MMP.AlgebraicGeometry.Singularities.Surface.LogTerminalReducedBoundary
import MMP.AlgebraicGeometry.Singularities.Surface.CyclicQuotientFormalModel
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolution
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.Surface.WeightedDualGraph
import MMP.AlgebraicGeometry.Intersection.Surface.BlowupGenusDropAdjunction
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.MMP.Abundance.NumericalDimensionOnePencil
import MMP.AlgebraicGeometry.Resolution.Principalization.SimultaneousLogResolution
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.NormalBoundarySurfaceModel
import MMP.AlgebraicGeometry.Singularities.CyclicQuotientClassGroup
import MMP.RingTheory.Henselian.CompletionDescent

/-!
# The cyclic surface model along a normal plt boundary

Let `X` be a normal variety over an algebraically closed field `k` of characteristic zero, `S` a
normal prime divisor and `B` an effective `ℚ`-divisor with all coefficients `≤ 1` and no component
`S`. Let `P ∈ S` be a point of codimension one in `S` near which `K_X + S + B` is `ℚ`-Cartier and
`(X, S + B)` is plt. Then the completed strict henselization of `𝒪_{X,P}`, together with the ideal
of `S`, is the cyclic quotient pair `(K[[u, v]]^{μ_m}, image of (u = 0))`, `μ_m` acting by
`ζ · (u, v) = (ζu, ζ^q v)` with `gcd(q, m) = 1`, where `K` is the residue field of the strict
henselization; and `mD` is Cartier at `P` for every Weil divisor `D` on `X`.

The proof runs as follows. On the open `V ∋ P` where the pair is plt it has a projective log
resolution, so it is log terminal. The surface model of the completed strict local
ring at `P` is a surface germ `(Y, y)` with a smooth curve `C` over `S`, and the pull-back
`T = C + B_Y` of `S + B` is log terminal near `y`. On the minimal resolution of `(Y, y)` the log
discrepancy vector of `(Y, y; C)` dominates that of `(Y, y; T)`, which is positive, so
`(Y, y; C)` is of type (3). Its completed local ring is the cyclic invariant ring
`κ^sep[[u, v]]^{μ_m}`, carrying `C` to the image of `(u = 0)`. The divisor class group of that
ring is killed by `m`, and faithfully flat descent of freeness makes `mD` Cartier at `P`. The
model, found for one strict henselization, transports to every other.

## Main results

* `MMP.Flips.exists_ringEquiv_cyclicInvariants_of_isAt_isPltPair`: at a point of codimension two
  on a normal plt boundary, the completed strict local pair is a cyclic quotient pair, and `m • D`
  is Cartier there.
* `MMP.Flips.IsGermResolution.exists_finset_isGermExceptionalCurve`: a resolution of a surface
  germ has finitely many exceptional curves.
* `MMP.Flips.IsGermResolution.exists_isExceptionalCurveEnumeration`: they admit an enumeration
  `Fin n → PrimeDivisor Y`, as the FA 3 classification theorems take it.

## Implementation notes

The source asks the coefficients of `B` to be `< 1`; the argument uses only that `S + B` is a
boundary, so coefficients `≤ 1` are allowed. This is the form that applies to a globally plt pair
`(X, S + B)`, which may have components of coefficient one away from `S`. Likewise only the
`ℚ`-Cartierness of `K_X + S + B` on a neighbourhood of `P` is asked for; it is in fact implied by
plt-ness at `P`, which includes it on the plt neighbourhood, and the proof uses only the latter.

The completed strict local ring at `P` is the `𝔪`-adic completion of a strict henselization `H`
of `𝒪_{X,P}` with respect to a separable closure `κ(P) ⊆ κ^sep`
(`IsLocalRing.IsHenselization (𝒪_{X,P}) κ^sep H`). The integers `m` and `q` are chosen before
`κ^sep` and `H`, and the model is asserted for every such choice. The isomorphism of pairs is a
ring isomorphism `φ : κ^sep[[u, v]]^{μ_m} ≃+* Ĥ`, `k`-linear for the constants of `κ^sep[[u, v]]`
(with `k → κ(P) → κ^sep`), which carries the ideal of invariants in `(u)` onto `I_{S,P} Ĥ`. The
invariants in the prime `(u)` form the ideal of the reduced image of `(u = 0)`, since
`κ^sep[[u, v]]` is integral over its invariant ring.

Positivity of the log discrepancy vector of `(Y, y; C)` is proved numerically. With `M` the
intersection matrix of the exceptional curves, the difference `x = a(C) - a(T)` satisfies
`Mᵀx = -β`, where `β_j = (f⁻¹_*(T - C) · E_j) ≥ 0`. Since `M` is negative definite with
nonnegative off-diagonal entries, this forces `x ≥ 0`. The rationality of the germ and the
`ℚ`-Cartierness of `K_Y + C` are therefore not needed.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace MMP.Flips

open MMP.Mori

/-! ### Transport of cyclic models -/

section Transport

open AdicCompletion

/-- Coefficientwise application of `σ` commutes with the action of `μ_m`, `ζ` acting on the
target through `σ(ζ)`. -/
private theorem map_rescale_cyclicWeights {K K' : Type*} [Field K] [Field K'] (σ : K ≃+* K')
    (m : ℕ) (q : ℤ) (ζ : rootsOfUnity m K) (f : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.map (σ : K →+* K') (MvPowerSeries.rescale (cyclicWeights K m q ζ) f) =
      MvPowerSeries.rescale (cyclicWeights K' m q (restrictRootsOfUnity σ m ζ))
        (MvPowerSeries.map (σ : K →+* K') f) := by
  ext n
  simp only [MvPowerSeries.coeff_map, MvPowerSeries.coeff_rescale, map_mul, map_finsuppProd,
    map_pow]
  congr 1
  refine Finsupp.prod_congr fun i _ => ?_
  fin_cases i <;> simp [cyclicWeights, map_zpow₀]

private theorem map_mem_cyclicInvariants {K K' : Type*} [Field K] [Field K'] (σ : K ≃+* K')
    (m : ℕ) (q : ℤ) {f : MvPowerSeries (Fin 2) K} (hf : f ∈ cyclicInvariants K m q) :
    MvPowerSeries.map (σ : K →+* K') f ∈ cyclicInvariants K' m q := by
  intro ζ
  obtain ⟨ξ, rfl⟩ : ∃ ξ, restrictRootsOfUnity σ m ξ = ζ :=
    ⟨restrictRootsOfUnity σ.symm m ζ, by ext; simp⟩
  change MvPowerSeries.rescale _ _ = _
  rw [← map_rescale_cyclicWeights]
  exact congrArg _ (hf ξ)

/-- A field isomorphism `σ : K ≃ K'` induces `K[[x, y]]^{μ_m} ≃ K'[[x, y]]^{μ_m}`,
coefficientwise. -/
private noncomputable def cyclicInvariantsMapEquiv {K K' : Type*} [Field K] [Field K']
    (σ : K ≃+* K') (m : ℕ) (q : ℤ) : cyclicInvariants K m q ≃+* cyclicInvariants K' m q :=
  RingEquiv.ofRingHom
    (((MvPowerSeries.map (σ : K →+* K')).comp (cyclicInvariants K m q).subtype).codRestrict _
      fun f => map_mem_cyclicInvariants σ m q f.2)
    (((MvPowerSeries.map (σ.symm : K' →+* K)).comp
      (cyclicInvariants K' m q).subtype).codRestrict _
      fun f => map_mem_cyclicInvariants σ.symm m q f.2)
    (by ext f n; simp [MvPowerSeries.coeff_map])
    (by ext f n; simp [MvPowerSeries.coeff_map])

private theorem coe_cyclicInvariantsMapEquiv {K K' : Type*} [Field K] [Field K']
    (σ : K ≃+* K') (m : ℕ) (q : ℤ) (f : cyclicInvariants K m q) :
    ((cyclicInvariantsMapEquiv σ m q f : cyclicInvariants K' m q) :
      MvPowerSeries (Fin 2) K') = MvPowerSeries.map (σ : K →+* K') f := rfl

private theorem coe_cyclicInvariantsMapEquiv_symm {K K' : Type*} [Field K] [Field K']
    (σ : K ≃+* K') (m : ℕ) (q : ℤ) (f : cyclicInvariants K' m q) :
    (((cyclicInvariantsMapEquiv σ m q).symm f : cyclicInvariants K m q) :
      MvPowerSeries (Fin 2) K) = MvPowerSeries.map (σ.symm : K' →+* K) f := rfl

private theorem map_mem_span_X_zero {K K' : Type*} [Field K] [Field K'] (σ : K →+* K')
    {f : MvPowerSeries (Fin 2) K} (hf : f ∈ Ideal.span {MvPowerSeries.X 0}) :
    MvPowerSeries.map σ f ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K')} := by
  rw [Ideal.mem_span_singleton] at hf ⊢
  obtain ⟨g, rfl⟩ := hf
  exact ⟨MvPowerSeries.map σ g, by rw [map_mul, MvPowerSeries.map_X]⟩

private theorem map_ringEquiv_eq_comap {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) : Ideal.map e I = Ideal.comap e.symm I :=
  Ideal.map_comap_of_equiv e

private theorem map_ringEquiv_trans {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (e₁ : R ≃+* S) (e₂ : S ≃+* T) (I : Ideal R) :
    Ideal.map (e₁.trans e₂) I = Ideal.map e₂ (Ideal.map e₁ I) :=
  (Ideal.map_map (e₁ : R →+* S) (e₂ : S →+* T)).symm

private theorem map_ringEquiv_symm_map {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) : Ideal.map e.symm (Ideal.map e I) = I :=
  Ideal.map_of_equiv e

private theorem map_ringEquiv_map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (e : S ≃+* T) (f : R →+* S) (I : Ideal R) :
    Ideal.map e (Ideal.map f I) = Ideal.map ((e : S →+* T).comp f) I := by
  rw [← Ideal.map_map]
  rfl

/-- `cyclicInvariantsMapEquiv σ` carries the invariants in `(x)` onto the invariants in `(x)`. -/
private theorem map_cyclicInvariantsMapEquiv_comap_span {K K' : Type*} [Field K] [Field K']
    (σ : K ≃+* K') (m : ℕ) (q : ℤ) :
    ((Ideal.span {MvPowerSeries.X 0}).comap (cyclicInvariants K m q).subtype).map
        (cyclicInvariantsMapEquiv σ m q) =
      (Ideal.span {MvPowerSeries.X 0}).comap (cyclicInvariants K' m q).subtype := by
  rw [map_ringEquiv_eq_comap]
  ext f
  simp only [Ideal.mem_comap, Subring.coe_subtype]
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · have := map_mem_span_X_zero (σ : K →+* K') hf
    have hσσ : ∀ g : MvPowerSeries (Fin 2) K',
        MvPowerSeries.map (σ : K →+* K') (MvPowerSeries.map (σ.symm : K' →+* K) g) = g := by
      intro g; ext n; simp [MvPowerSeries.coeff_map]
    rwa [coe_cyclicInvariantsMapEquiv_symm, hσσ] at this
  · rw [coe_cyclicInvariantsMapEquiv_symm]
    exact map_mem_span_X_zero _ hf

private theorem factorPow_evalₐ {R : Type*} [CommRing R] (I : Ideal R) {a b : ℕ} (hle : a ≤ b)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (evalₐ I b x) = evalₐ I a x := by
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [evalₐ_mk, evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hle f

private theorem pow_le_comap_pow {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S)
    {I : Ideal R} {J : Ideal S} (hIJ : I.map ψ ≤ J) (n : ℕ) : I ^ n ≤ (J ^ n).comap ψ := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono hIJ n

private theorem adicCompletionMap_compat {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S)
    {I : Ideal R} {J : Ideal S} (hIJ : I.map ψ ≤ J) {a b : ℕ} (hle : a ≤ b) :
    (Ideal.Quotient.factorPow J hle).comp ((Ideal.quotientMap (J ^ b) ψ
      (pow_le_comap_pow ψ hIJ b)).comp (evalₐ I b : AdicCompletion I R →+* R ⧸ I ^ b)) =
      (Ideal.quotientMap (J ^ a) ψ (pow_le_comap_pow ψ hIJ a)).comp
        (evalₐ I a : AdicCompletion I R →+* R ⧸ I ^ a) := by
  ext x
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I b x)
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe,
    RingHom.coe_coe, ← factorPow_evalₐ I hle, ← hy]
  simp only [Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

/-- The map of adic completions induced by a ring map `ψ` with `ψ(I) ⊆ J`. -/
private noncomputable def adicCompletionMap {R S : Type*} [CommRing R] [CommRing S]
    (ψ : R →+* S) {I : Ideal R} {J : Ideal S} (hIJ : I.map ψ ≤ J) :
    AdicCompletion I R →+* AdicCompletion J S :=
  liftRingHom J (fun n => (Ideal.quotientMap (J ^ n) ψ (pow_le_comap_pow ψ hIJ n)).comp
      (evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) (adicCompletionMap_compat ψ hIJ)

private theorem evalₐ_adicCompletionMap {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S)
    {I : Ideal R} {J : Ideal S} (hIJ : I.map ψ ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (adicCompletionMap ψ hIJ x) =
      Ideal.quotientMap (J ^ n) ψ (pow_le_comap_pow ψ hIJ n) (evalₐ I n x) :=
  evalₐ_liftRingHom J _ (adicCompletionMap_compat ψ hIJ) n x

private theorem adicCompletionMap_of {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S)
    {I : Ideal R} {J : Ideal S} (hIJ : I.map ψ ≤ J) (x : R) :
    adicCompletionMap ψ hIJ (of I R x) = of J S (ψ x) := by
  refine ext_evalₐ fun n => ?_
  rw [evalₐ_adicCompletionMap, evalₐ_of, evalₐ_of, Ideal.quotientMap_mk]

private theorem adicCompletionMap_comp_apply {R S : Type*} [CommRing R] [CommRing S]
    (ψ : R →+* S) (χ : S →+* R) (hχ : ∀ x, χ (ψ x) = x)
    {I : Ideal R} {J : Ideal S} (hIJ : I.map ψ ≤ J) (hJI : J.map χ ≤ I)
    (x : AdicCompletion I R) :
    adicCompletionMap χ hJI (adicCompletionMap ψ hIJ x) = x := by
  refine ext_evalₐ fun n => ?_
  rw [evalₐ_adicCompletionMap, evalₐ_adicCompletionMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  rw [← hy, Ideal.quotientMap_mk, Ideal.quotientMap_mk, hχ]

/-- The isomorphism of adic completions induced by a ring isomorphism `ψ` with `ψ(I) = J`. -/
private noncomputable def adicCompletionCongr {R S : Type*} [CommRing R] [CommRing S]
    (ψ : R ≃+* S) {I : Ideal R} {J : Ideal S} (hIJ : I.map (ψ : R →+* S) = J) :
    AdicCompletion I R ≃+* AdicCompletion J S where
  __ := adicCompletionMap (ψ : R →+* S) hIJ.le
  invFun := adicCompletionMap (ψ.symm : S →+* R) (hIJ ▸ (Ideal.map_of_equiv ψ).le)
  left_inv := adicCompletionMap_comp_apply _ _ ψ.symm_apply_apply _ _
  right_inv := adicCompletionMap_comp_apply _ _ ψ.apply_symm_apply _ _

private theorem adicCompletionCongr_of {R S : Type*} [CommRing R] [CommRing S] (ψ : R ≃+* S)
    {I : Ideal R} {J : Ideal S} (hIJ : I.map (ψ : R →+* S) = J) (x : R) :
    adicCompletionCongr ψ hIJ (of I R x) = of J S (ψ x) :=
  adicCompletionMap_of _ hIJ.le x

/-- **Strict henselizations are unique.** Two henselizations of a local ring `A` with respect to
isomorphic extensions `κ ≅ κ'` of its residue field are isomorphic `A`-algebras. -/
private theorem nonempty_algEquiv_of_isHenselization {A : Type u} [CommRing A] [IsLocalRing A]
    {κ κ' : Type u} [Field κ] [Field κ'] [Algebra (ResidueField A) κ] [Algebra (ResidueField A) κ']
    (σ : κ ≃+* κ')
    (hσ : ∀ x, σ (algebraMap (ResidueField A) κ x) = algebraMap (ResidueField A) κ' x)
    (H H' : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [CommRing H'] [IsLocalRing H']
    [Algebra A H'] [hH : IsHenselization A κ H] [hH' : IsHenselization A κ' H'] :
    Nonempty (H ≃ₐ[A] H') := by
  obtain ⟨e, he⟩ := hH.exists_residueFieldEquiv
  obtain ⟨e', he'⟩ := hH'.exists_residueFieldEquiv
  haveI := hH'.henselian
  haveI := hH.henselian
  let φ : ResidueField H →+* ResidueField H' :=
    ((e' : κ' →+* ResidueField H').comp (σ : κ →+* κ')).comp (e.symm : ResidueField H →+* κ)
  let φ' : ResidueField H' →+* ResidueField H :=
    ((e : κ →+* ResidueField H).comp (σ.symm : κ' →+* κ)).comp (e'.symm : ResidueField H' →+* κ')
  have hφ : φ.comp ((residue H).comp (algebraMap A H)) = (residue H').comp (algebraMap A H') := by
    ext x
    simp only [φ, RingHom.comp_apply, RingEquiv.coe_toRingHom, ← he, RingEquiv.symm_apply_apply,
      hσ, he']
  have hφ' : φ'.comp ((residue H').comp (algebraMap A H')) = (residue H).comp (algebraMap A H) := by
    ext x
    simp only [φ', RingHom.comp_apply, RingEquiv.coe_toRingHom, ← he', RingEquiv.symm_apply_apply,
      ← hσ, he]
  let f := HenselianLocalRing.indEtaleAlgHomOfResidue hH.ind_etale φ hφ
  let g := HenselianLocalRing.indEtaleAlgHomOfResidue hH'.ind_etale φ' hφ'
  have hf := HenselianLocalRing.isLocalHom_indEtaleAlgHomOfResidue hH.ind_etale φ hφ
  have hg := HenselianLocalRing.isLocalHom_indEtaleAlgHomOfResidue hH'.ind_etale φ' hφ'
  have rf := HenselianLocalRing.comp_residue_indEtaleAlgHomOfResidue hH.ind_etale φ hφ
  have rg := HenselianLocalRing.comp_residue_indEtaleAlgHomOfResidue hH'.ind_etale φ' hφ'
  have hgf : g.comp f = AlgHom.id A H := by
    have h1 := HenselianLocalRing.indEtaleAlgHomOfResidue_unique hH.ind_etale (RingHom.id _) rfl
      (g.comp f) ⟨fun a ha => hf.map_nonunit a (hg.map_nonunit _ ha)⟩ (by
        change (residue H).comp ((g : H' →+* H).comp (f : H →+* H')) = _
        rw [← RingHom.comp_assoc, rg, RingHom.comp_assoc, rf, ← RingHom.comp_assoc]
        congr 1
        ext x
        simp [φ, φ'])
    have h2 := HenselianLocalRing.indEtaleAlgHomOfResidue_unique hH.ind_etale (RingHom.id _) rfl
      (AlgHom.id A H) ⟨fun a ha => ha⟩ (by ext; rfl)
    rw [h1, h2]
  have hfg : f.comp g = AlgHom.id A H' := by
    have h1 := HenselianLocalRing.indEtaleAlgHomOfResidue_unique hH'.ind_etale (RingHom.id _) rfl
      (f.comp g) ⟨fun a ha => hg.map_nonunit a (hf.map_nonunit _ ha)⟩ (by
        change (residue H').comp ((f : H →+* H').comp (g : H' →+* H)) = _
        rw [← RingHom.comp_assoc, rf, RingHom.comp_assoc, rg, ← RingHom.comp_assoc]
        congr 1
        ext x
        simp [φ, φ'])
    have h2 := HenselianLocalRing.indEtaleAlgHomOfResidue_unique hH'.ind_etale (RingHom.id _) rfl
      (AlgHom.id A H') ⟨fun a ha => ha⟩ (by ext; rfl)
    rw [h1, h2]
  exact ⟨AlgEquiv.ofAlgHom f g hfg hgf⟩

/-- The completed strict local pair `(Ĥ, I Ĥ)` of `(A, I)` is the cyclic quotient pair
`(κ[[u, v]]^{μ_m}, image of (u = 0))`, by a ring isomorphism which is `k`-linear on constants. -/
private def IsCyclicModel (k : Type u) [Field k] {A : Type u} [CommRing A] [IsLocalRing A]
    [Algebra k A] (I : Ideal A) (m : ℕ) (q : ℤ) (κ : Type u) [Field κ]
    [Algebra (ResidueField A) κ] (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] :
    Prop :=
  ∃ φ : cyclicInvariants κ m q ≃+* AdicCompletion (maximalIdeal H) H,
    (∀ c : k, ((φ.symm (algebraMap H (AdicCompletion (maximalIdeal H) H)
        (algebraMap A H (algebraMap k A c))) : cyclicInvariants κ m q) :
          MvPowerSeries (Fin 2) κ) =
      MvPowerSeries.C (algebraMap (ResidueField A) κ (residue A (algebraMap k A c)))) ∧
    Ideal.map φ ((Ideal.span {MvPowerSeries.X 0}).comap (cyclicInvariants κ m q).subtype) =
      (I.map (algebraMap A H)).map (algebraMap H (AdicCompletion (maximalIdeal H) H))

/-- A cyclic model for one strict henselization is a cyclic model for every other one. -/
private theorem IsCyclicModel.transport {k : Type u} [Field k] {A : Type u} [CommRing A]
    [IsLocalRing A] [Algebra k A] {I : Ideal A} {m : ℕ} {q : ℤ}
    {κ κ' : Type u} [Field κ] [Field κ'] [Algebra (ResidueField A) κ]
    [Algebra (ResidueField A) κ'] [IsSepClosure (ResidueField A) κ]
    [IsSepClosure (ResidueField A) κ']
    {H H' : Type u} [CommRing H] [IsLocalRing H] [Algebra A H] [CommRing H'] [IsLocalRing H']
    [Algebra A H'] [IsHenselization A κ H] [IsHenselization A κ' H']
    (h : IsCyclicModel k I m q κ H) : IsCyclicModel k I m q κ' H' := by
  obtain ⟨φ, hc, hI⟩ := h
  let σa := IsSepClosure.equiv (ResidueField A) κ κ'
  let σ : κ ≃+* κ' := σa.toRingEquiv
  have hσ : ∀ x, σ (algebraMap (ResidueField A) κ x) = algebraMap (ResidueField A) κ' x :=
    σa.commutes
  obtain ⟨ψa⟩ := nonempty_algEquiv_of_isHenselization σ hσ H H'
  let ψ : H ≃+* H' := ψa.toRingEquiv
  have hψ : ∀ a : A, ψ (algebraMap A H a) = algebraMap A H' a := ψa.commutes
  let Ψ := adicCompletionCongr ψ (IsLocalRing.map_ringEquiv_maximalIdeal ψ)
  have hΨ : ∀ x : H, Ψ (algebraMap H _ x) = algebraMap H' _ (ψ x) := fun x =>
    adicCompletionCongr_of ψ _ x
  refine ⟨(cyclicInvariantsMapEquiv σ m q).symm.trans (φ.trans Ψ), fun c => ?_, ?_⟩
  · have h1 : Ψ.symm (algebraMap H' (AdicCompletion (maximalIdeal H') H')
        (algebraMap A H' (algebraMap k A c))) =
        algebraMap H _ (algebraMap A H (algebraMap k A c)) := by
      rw [RingEquiv.symm_apply_eq, hΨ, hψ]
    simp only [RingEquiv.symm_trans_apply, RingEquiv.symm_symm, h1]
    rw [coe_cyclicInvariantsMapEquiv, hc, MvPowerSeries.map_C]
    exact congrArg _ (hσ _)
  · rw [← map_cyclicInvariantsMapEquiv_comap_span σ m q, map_ringEquiv_trans,
      map_ringEquiv_symm_map, map_ringEquiv_trans, hI, Ideal.map_map, map_ringEquiv_map,
      Ideal.map_map]
    congr 1
    ext a
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, hΨ, hψ]

/-- A cyclic model of the completion of an algebraic local ring `O` of a surface, transported along
an isomorphism `Ô ≅ Ĥ` over `A`, is a cyclic model of `(A, I)`. -/
private theorem isCyclicModel_of_ringEquiv {k : Type u} [Field k] {A : Type u} [CommRing A]
    [IsLocalRing A] [Algebra k A] {I : Ideal A} {m : ℕ} {q : ℤ} {κ : Type u} [Field κ]
    [Algebra (ResidueField A) κ] {H : Type u} [CommRing H] [IsLocalRing H] [Algebra A H]
    {O : Type u} [CommRing O] [IsLocalRing O] [Algebra κ O] (φ₀ : A →+* O)
    (hφ₀ : ∀ c : k, φ₀ (algebraMap k A c) =
      algebraMap κ O (algebraMap (ResidueField A) κ (residue A (algebraMap k A c))))
    (e : AdicCompletion (maximalIdeal O) O ≃+* AdicCompletion (maximalIdeal H) H)
    (he : ∀ a : A, e (algebraMap O _ (φ₀ a)) = algebraMap H _ (algebraMap A H a))
    {IC : Ideal O} (hIC : (IC.map (algebraMap O (AdicCompletion (maximalIdeal O) O))).map e =
      (I.map (algebraMap A H)).map (algebraMap H (AdicCompletion (maximalIdeal H) H)))
    (φ : cyclicInvariants κ m q ≃+* AdicCompletion (maximalIdeal O) O)
    (hc : ∀ c : κ, ((φ.symm (algebraMap O (AdicCompletion (maximalIdeal O) O)
      (algebraMap κ O c)) : cyclicInvariants κ m q) : MvPowerSeries (Fin 2) κ) =
        MvPowerSeries.C c)
    (hφI : Ideal.map φ ((Ideal.span {MvPowerSeries.X 0}).comap (cyclicInvariants κ m q).subtype)
      = IC.map (algebraMap O (AdicCompletion (maximalIdeal O) O))) :
    IsCyclicModel k I m q κ H := by
  refine ⟨φ.trans e, fun c => ?_, ?_⟩
  · have h1 : e.symm (algebraMap H (AdicCompletion (maximalIdeal H) H)
        (algebraMap A H (algebraMap k A c))) =
        algebraMap O _ (algebraMap κ O
          (algebraMap (ResidueField A) κ (residue A (algebraMap k A c)))) := by
      rw [RingEquiv.symm_apply_eq, ← hφ₀, he]
    rw [RingEquiv.symm_trans_apply, h1, hc]
  · rw [map_ringEquiv_trans, hφI, hIC]

private theorem X_dvd_iff_rescale_eq_zero {K : Type u} [Field K] (i : Fin 2)
    (φ : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.X i ∣ φ ↔ MvPowerSeries.rescale (Function.update 1 i 0) φ = 0 := by
  rw [MvPowerSeries.X_dvd_iff]
  refine ⟨fun h => ?_, fun h e he => ?_⟩
  · ext e
    rw [MvPowerSeries.coeff_rescale, _root_.map_zero]
    by_cases he : e i = 0
    · rw [h e he, mul_zero]
    · rw [Finsupp.prod, Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.mpr he)
        (by simp [he]), zero_mul]
  · have hp : e.prod (fun j n => (Function.update (1 : Fin 2 → K) i 0) j ^ n) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      have : j ≠ i := fun hji => (Finsupp.mem_support_iff.mp hj) (hji ▸ he)
      simp [this]
    have := congrArg (MvPowerSeries.coeff e) h
    rwa [MvPowerSeries.coeff_rescale, _root_.map_zero, hp, one_mul] at this

private theorem prime_X {K : Type u} [Field K] (i : Fin 2) :
    Prime (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) := by
  refine ⟨fun h => by simpa using congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h,
    fun hu => ?_, fun a b hab => ?_⟩
  · simpa using MvPowerSeries.isUnit_iff_constantCoeff.mp hu
  · simp only [X_dvd_iff_rescale_eq_zero, map_mul] at hab ⊢
    exact mul_eq_zero.mp hab

private theorem radical_span_X {K : Type u} [Field K] (i : Fin 2) :
    (Ideal.span {MvPowerSeries.X i} : Ideal (MvPowerSeries (Fin 2) K)).radical =
      Ideal.span {MvPowerSeries.X i} :=
  ((Ideal.span_singleton_prime (prime_X i).ne_zero).mpr (prime_X i)).radical

private theorem comap_ΓSpecIso_vanishingIdeal (R : CommRingCat.{u})
    (Z : TopologicalSpace.Closeds (Spec R)) :
    Ideal.comap (Scheme.ΓSpecIso R).inv.hom
      ((Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨⊤, isAffineOpen_top (Spec R)⟩) =
      PrimeSpectrum.vanishingIdeal (R := R) (Z : Set (Spec R)) := by
  ext x
  refine Iff.trans ?_ (PrimeSpectrum.mem_vanishingIdeal _ _).symm
  rw [Ideal.mem_comap, Scheme.IdealSheafData.vanishingIdeal_ideal,
    PrimeSpectrum.mem_vanishingIdeal]
  simp only [Set.mem_preimage]
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  refine ⟨fun h (p : Spec R) hp => ?_, fun h p hp => h _ hp⟩
  have hp' : Spec.map (Scheme.ΓSpecIso R).inv (Spec.map (Scheme.ΓSpecIso R).hom p) = p := by
    rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
    rfl
  have hmem : Spec.map (Scheme.ΓSpecIso R).inv (Spec.map (Scheme.ΓSpecIso R).hom p) ∈
      (Z : Set (Spec R)) := by rwa [hp']
  have := h (Spec.map (Scheme.ΓSpecIso R).hom p) hmem
  change (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom x) ∈ p.asIdeal at this
  simpa using this

private theorem vanishingIdeal_image_comap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (S : Set (PrimeSpectrum B)) :
    PrimeSpectrum.vanishingIdeal (PrimeSpectrum.comap f '' S) =
      Ideal.comap f (PrimeSpectrum.vanishingIdeal S) := by
  ext a
  simp only [PrimeSpectrum.mem_vanishingIdeal, Set.forall_mem_image, Ideal.mem_comap]
  rfl

private theorem comap_vanishingIdeal_cyclicQuotientImage {K : Type u} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) (g : MvPowerSeries (Fin 2) K) :
    Ideal.comap (Scheme.ΓSpecIso (.of (cyclicInvariants K m q))).inv.hom
        ((Scheme.IdealSheafData.vanishingIdeal (cyclicQuotientImage h g)).ideal
          ⟨⊤, isAffineOpen_top _⟩) =
      Ideal.comap (cyclicInvariants K m q).subtype (Ideal.span {g}).radical := by
  rw [comap_ΓSpecIso_vanishingIdeal]
  exact (PrimeSpectrum.vanishingIdeal_closure (R := cyclicInvariants K m q) _).trans <|
    (vanishingIdeal_image_comap (cyclicInvariants K m q).subtype _).trans <| by
      rw [← PrimeSpectrum.zeroLocus_span, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]

end Transport

/-! ### Stalks and constants -/

section Stalks

/-- A morphism `j : Y ⟶ X` over `Spec κ ⟶ Spec k` carries the constants `k → 𝒪_{X,P}` to the
constants `κ → 𝒪_{Y,y}` on stalks, for `j(y) ⤳ P`. -/
private theorem stalkSpecializes_stalkMap_algebraMap {k κ : Type u} [Field k] [Field κ]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of κ)) (j : Y ⟶ X)
    (ψ : k →+* κ) (h : j ≫ sX = sY ≫ Spec.map (CommRingCat.ofHom ψ)) {y : Y} {P : X}
    (hjy : j.base y ⤳ P) (c : k) :
    (X.presheaf.stalkSpecializes hjy ≫ j.stalkMap y).hom
        ((stalkAlgebra sX P).algebraMap c) = (stalkAlgebra sY y).algebraMap (ψ c) := by
  change (X.presheaf.stalkSpecializes hjy ≫ j.stalkMap y).hom
      (((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ P (TopologicalSpace.Opens.mem_top _)).hom c) =
    ((Scheme.ΓSpecIso (.of κ)).inv ≫ sY.appTop ≫
      Y.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top _)).hom (ψ c)
  rw [← CommRingCat.comp_apply]
  simp only [Category.assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
  have h2 := congrArg (fun f => ((Scheme.ΓSpecIso (.of k)).inv ≫ f.app ⊤ ≫
    Y.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top _)).hom c) h
  simp only [Scheme.Hom.comp_app, Category.assoc] at h2
  have h3 : ((Spec.map (CommRingCat.ofHom ψ)).appTop).hom
      ((Scheme.ΓSpecIso (.of k)).inv.hom c) = (Scheme.ΓSpecIso (.of κ)).inv.hom (ψ c) :=
    (congrArg (fun g => g.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))).symm
  refine h2.trans ?_
  change (Y.presheaf.germ ⊤ y _).hom ((sY.app _).hom (((Spec.map (CommRingCat.ofHom ψ)).appTop).hom
    ((Scheme.ΓSpecIso (.of k)).inv.hom c))) = _
  rw [h3]
  rfl

/-- On an affine open `W`, the ideal of a prime divisor `S` meeting `W` is the prime of its
generic point. -/
private theorem idealSheaf_ideal_eq_primeIdealOf {X : Scheme.{u}}
    (S : AlgebraicGeometry.PrimeDivisor X)
    {W : X.Opens} (hW : IsAffineOpen W) (hη : S.genericPoint ∈ W) :
    S.idealSheaf.ideal ⟨W, hW⟩ = (hW.primeIdealOf ⟨S.genericPoint, hη⟩).asIdeal := by
  have : IsReduced S.idealSheaf.subscheme := by
    haveI := S.integral
    infer_instance
  rw [← MMP.Positivity.vanishingIdeal_support_of_isReduced S.idealSheaf,
    Scheme.IdealSheafData.vanishingIdeal_ideal]
  set η' := hW.primeIdealOf ⟨S.genericPoint, hη⟩
  have hη' : hW.fromSpec η' = S.genericPoint := hW.fromSpec_primeIdealOf _
  ext f
  rw [PrimeSpectrum.mem_vanishingIdeal]
  refine ⟨fun h => h η' ?_, fun hf p hp => ?_⟩
  · change hW.fromSpec η' ∈ (S.idealSheaf.support : Set X)
    rw [hη']
    change S.genericPoint ∈ S.support
    rw [S.support_eq_closure]
    exact subset_closure rfl
  · change hW.fromSpec p ∈ S.support at hp
    rw [S.support_eq_closure] at hp
    have hsp : S.genericPoint ⤳ hW.fromSpec p := specializes_iff_mem_closure.mpr hp
    rw [← hη'] at hsp
    exact (PrimeSpectrum.le_iff_specializes η' p).mpr
      (hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hsp) hf

private theorem ker_stalkSpecializes_residue_eq_map {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V)
    {x P : X} (hxP : x ⤳ P) (hPV : P ∈ V) :
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P, hPV⟩
    RingHom.ker (X.presheaf.stalkSpecializes hxP ≫ X.residue x).hom =
      (hV.primeIdealOf ⟨x, hxP.mem_open V.isOpen hPV⟩).asIdeal.map
        (algebraMap Γ(X, V) (X.presheaf.stalk P)) := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P, hPV⟩
  have hxV : x ∈ V := hxP.mem_open V.isOpen hPV
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have hP := hV.isLocalization_stalk ⟨P, hPV⟩
  have hx := hV.isLocalization_stalk ⟨x, hxV⟩
  set q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  set φ := (X.presheaf.stalkSpecializes hxP ≫ X.residue x).hom
  have hψ : ∀ b : Γ(X, V), φ (algebraMap _ _ b) =
      residue (X.presheaf.stalk x) (algebraMap Γ(X, V) (X.presheaf.stalk x) b) := by
    intro b
    change (X.presheaf.germ V P hPV ≫ X.presheaf.stalkSpecializes hxP ≫ X.residue x).hom b = _
    rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
    rfl
  have hker : ∀ b : Γ(X, V), φ (algebraMap _ _ b) = 0 ↔ b ∈ q := by
    intro b
    rw [hψ]
    exact (residue_eq_zero_iff _).trans
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x) q b)
  apply le_antisymm
  · intro a ha
    obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq
      (hV.primeIdealOf ⟨P, hPV⟩).asIdeal.primeCompl a
    have h1 : φ (algebraMap _ _ b) = 0 := by
      rw [← IsLocalization.mk'_spec (X.presheaf.stalk P) b s, map_mul, RingHom.mem_ker.mp ha,
        zero_mul]
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((hker b).mp h1))
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact (hker b).mpr hb

/-- The stalk at `P` of the ideal of a prime divisor `S` through `P` is the kernel of
`𝒪_{X,P} → κ(η_S)`. -/
private theorem stalk_idealSheaf_eq_ker {X : Scheme.{u}} (S : AlgebraicGeometry.PrimeDivisor X)
    {P : X}
    (hPS : S.genericPoint ⤳ P) :
    IdealSheafData.stalk S.idealSheaf P =
      RingHom.ker (X.presheaf.stalkSpecializes hPS ≫ X.residue S.genericPoint).hom := by
  obtain ⟨W, hW, hPW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show P ∈ (⊤ : X.Opens) from trivial)
  have hη : S.genericPoint ∈ W := hPS.mem_open W.isOpen hPW
  rw [IdealSheafData.stalk_eq_map_germ S.idealSheaf P ⟨W, hW⟩ hPW,
    idealSheaf_ideal_eq_primeIdealOf S hW hη, ker_stalkSpecializes_residue_eq_map hW hPS hPW]
  rfl

/-- The local ring of a scheme locally of finite type over `k` is essentially of finite type
over `k`. -/
private theorem essFiniteType_stalk {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (P : X) :
    letI := stalkAlgebra sX P
    Algebra.EssFiniteType k (X.presheaf.stalk P) := by
  letI := stalkAlgebra sX P
  obtain ⟨V, hV, hPV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show P ∈ (⊤ : X.Opens) from trivial)
  letI : Algebra k Γ(X, V) := sectionAlgebra sX V
  letI : Algebra Γ(X, V) (X.presheaf.stalk P) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P, hPV⟩
  have : Algebra.FiniteType k Γ(X, V) := finiteType_sectionAlgebra sX hV
  have : IsScalarTower k Γ(X, V) (X.presheaf.stalk P) :=
    isScalarTower_section_stalk sX V ⟨P, hPV⟩
  have := hV.isLocalization_stalk ⟨P, hPV⟩
  have : Algebra.EssFiniteType Γ(X, V) (X.presheaf.stalk P) :=
    Algebra.EssFiniteType.of_isLocalization _ (hV.primeIdealOf ⟨P, hPV⟩).asIdeal.primeCompl
  exact Algebra.EssFiniteType.comp k Γ(X, V) (X.presheaf.stalk P)

end Stalks

/-- Every local ring has a strict henselization with respect to any separable closure of its
residue field. -/
private theorem exists_isHenselization (A : Type u) [CommRing A] [IsLocalRing A] (κ : Type u)
    [Field κ] [Algebra (ResidueField A) κ] [IsSepClosure (ResidueField A) κ] :
    ∃ (H : Type u) (_ : CommRing H) (_ : IsLocalRing H) (_ : Algebra A H),
      IsHenselization A κ H := by
  obtain ⟨Rh, _, _, _, _, -, hind, -, hbij⟩ := IsLocalRing.exists_henselization A
  obtain ⟨Rsh, _, _, _, _, _, _, hhen, -, hind', -, e, he⟩ :=
    IsLocalRing.exists_strictHenselization A Rh hind hbij.2 κ
  exact ⟨Rsh, _, _, _, IsHenselization.of_ind_etale.{u, u, u} hhen hind' ⟨e, he⟩⟩

/-! ### Comparing log discrepancy vectors -/

/-- **A negative definite weighted graph is an M-matrix**: if `∑_k x_k M(Γ)_{kj} ≤ 0` for every
`j`, then `x ≥ 0`. Write `x = y + z` with `y = min(x, 0)`, `z = max(x, 0)`; the off-diagonal
entries of `M(Γ)` are nonnegative and `y_j z_j = 0`, so `yᵀ M y ≥ yᵀ M x ≥ 0`, and negative
definiteness forces `y = 0`. -/
private theorem nonneg_of_sum_mul_matrix_nonpos {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} (hΓ : Γ.IsNegDef) {x : V → ℚ}
    (hx : ∀ j, ∑ k, x k * (Γ.matrix k j : ℚ) ≤ 0) (j : V) : 0 ≤ x j := by
  set y : V → ℚ := fun k => min (x k) 0 with hy
  set z : V → ℚ := fun k => max (x k) 0 with hz
  have hxyz : ∀ k, x k = y k + z k := fun k => by simp [hy, hz, min_add_max]
  have hyz : ∀ k, y k * z k = 0 := fun k => by
    rcases le_total (x k) 0 with h | h
    · simp [hy, hz, h]
    · simp [hy, hz, h]
  have hM : ∀ k l, k ≠ l → 0 ≤ (Γ.matrix k l : ℚ) := fun k l h => by
    simp [WeightedGraph.matrix, h]
  have h1 : 0 ≤ ∑ l, y l * ∑ k, x k * (Γ.matrix k l : ℚ) :=
    Finset.sum_nonneg fun l _ => mul_nonneg_of_nonpos_of_nonpos (min_le_right _ _) (hx l)
  have h2 : ∑ l, y l * ∑ k, z k * (Γ.matrix k l : ℚ) ≤ 0 := by
    refine Finset.sum_nonpos fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_nonpos fun k _ => ?_
    by_cases hkl : k = l
    · subst hkl
      have e : y k * (z k * (Γ.matrix k k : ℚ)) = (y k * z k) * Γ.matrix k k := by ring
      rw [e, hyz k, zero_mul]
    · exact mul_nonpos_of_nonpos_of_nonneg (min_le_right _ _)
        (mul_nonneg (le_max_right (x k) 0) (hM k l hkl))
  have h3 : 0 ≤ ∑ l, y l * ∑ k, y k * (Γ.matrix k l : ℚ) := by
    have : ∑ l, y l * ∑ k, x k * (Γ.matrix k l : ℚ) =
        ∑ l, y l * ∑ k, y k * (Γ.matrix k l : ℚ) + ∑ l, y l * ∑ k, z k * (Γ.matrix k l : ℚ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hxyz k]
      ring
    linarith
  by_contra hneg
  have hy0 : y ≠ 0 := fun h => by
    have := congrFun h j
    simp [hy] at this
    linarith [not_le.mp hneg]
  have hpos := hΓ.dotProduct_mulVec_pos hy0
  have hsymm : ∀ k l, (Γ.matrix k l : ℚ) = Γ.matrix l k := fun k l => by
    rw [← Matrix.transpose_apply Γ.matrix l k, Γ.matrix_isSymm.eq]
  simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.neg_apply, Matrix.map_apply] at hpos
  have : ∑ l, y l * ∑ k, -(Γ.matrix l k : ℚ) * y k =
      -∑ l, y l * ∑ k, y k * (Γ.matrix k l : ℚ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsymm]
    ring
  linarith

/-- **Log discrepancy vectors decrease as the boundary grows** (graph form). If two weighted graphs
with the same matrix and genera have boundary degrees `β ≤ β'`, the log discrepancy vector of the
first dominates that of the second, provided the matrix is negative definite: the difference
`x = a - a'` has `∑_k x_k M_{kj} = β_j - β'_j ≤ 0`. -/
private theorem le_of_isLogDiscrepancyVector_of_boundary_le {V : Type*} [Fintype V]
    [DecidableEq V] {Γ Γ' : WeightedGraph V} (hneg : Γ.IsNegDef) (hM : Γ.matrix = Γ'.matrix)
    (hp : ∀ j, Γ.genus j = Γ'.genus j) (hβ : ∀ j, Γ.boundary j ≤ Γ'.boundary j)
    {a a' : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha' : Γ'.IsLogDiscrepancyVector a')
    (j : V) : a' j ≤ a j := by
  have hew : ∀ j k, j ≠ k → Γ.edgeWeight j k = Γ'.edgeWeight j k := fun j k h => by
    have := congrFun (congrFun hM j) k
    simpa [WeightedGraph.matrix, h] using this
  have hc : ∀ l, Γ'.c l = Γ.c l - (Γ'.boundary l - Γ.boundary l) := fun l => by
    have hs : ∑ k ∈ Finset.univ.erase l, (Γ'.edgeWeight l k : ℚ) =
        ∑ k ∈ Finset.univ.erase l, (Γ.edgeWeight l k : ℚ) :=
      Finset.sum_congr rfl fun k hk => by rw [hew l k (Finset.ne_of_mem_erase hk).symm]
    simp only [WeightedGraph.c, hp, hs]
    ring
  have hx : ∀ l, ∑ k, (a k - a' k) * (Γ.matrix k l : ℚ) ≤ 0 := fun l => by
    have h1 := ha l
    have h2 := ha' l
    rw [← hM] at h2
    simp only [sub_mul, Finset.sum_sub_distrib, h1, h2, hc]
    linarith [hβ l]
  linarith [nonneg_of_sum_mul_matrix_nonpos hneg hx j]

/-- A negative definite weighted graph has positive determinant. -/
private theorem det_pos_of_isNegDef {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} (hneg : Γ.IsNegDef) : 0 < Γ.det := by
  have h := hneg.delta_pos Finset.univ
  rw [← WeightedGraph.det_restrict, WeightedGraph.det, ← Matrix.det_submatrix_equiv_self
    (Equiv.subtypeUnivEquiv Finset.mem_univ).symm] at h
  convert h using 1
  rw [WeightedGraph.det]
  congr 1
  ext x y
  simp only [WeightedGraph.matrix, Matrix.neg_apply, Matrix.of_apply, Matrix.submatrix_apply,
    Equiv.subtypeUnivEquiv_symm_apply, Subtype.ext_iff]
  rfl

/-! ### Canonical divisors of normal varieties -/

section CanonicalDivisorExistence

open MMP.Fourfold Opposite TopologicalSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-! ### The divisorial sheaf on an open subscheme -/

section DivisorialRestrict

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem genericPoint_specializes_of_mem {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_genericPoint_of_mem {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_stalkSpecializes_apply {Y : Scheme.{u}} {x y z : Y}
    (h : x ⤳ y) (h' : y ⤳ z) (h'' : x ⤳ z) (s : Y.presheaf.stalk z) :
    (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.stalkSpecializes h').hom s) =
      (Y.presheaf.stalkSpecializes h'').hom s :=
  TopCat.Presheaf.stalkSpecializes_comp_apply _ h h' s

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes_of_mem Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (genericPoint_specializes_of_mem Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint_of_mem Z)).hom h
  rwa [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes_of_mem E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes_of_mem E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (genericPoint_specializes_of_mem E.component)).hom
            s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The irreducible component `Set.univ` of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rw [componentGenericPoint_eq_genericPoint]; exact h⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint_of_mem Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint_of_mem Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint_of_mem Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes_of_mem _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint_of_mem _)).hom (e.symm _)))) = _
  rw [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint_of_mem Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF]
    rw [evFF_restrictRF U V ψ _ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxe⟩
    rwa [U.ι.isOpenEmbedding.injective hxe] at hx
  refine ⟨fun h P hP => ?_,
    fun h E' hE' => (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))⟩
  have hPU : P.genericPoint ∈ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
    rw [← hx]
    exact x.2
  obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
  exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))

private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict U.ι ⟶ Divisor.divisorialSheaf (D.restrictOpen U) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF U V.unop (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff U D V.unop _).2
              (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (D.restrictOpen U) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero U V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add U V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul U V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom U D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (U.ι ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · exact Subtype.ext (restrictRF_injective U V (congrArg Subtype.val h))
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- The divisorial sheaf of the restriction `D|_U` of a divisor to an open subscheme is the
restriction `𝒪_X(D)|_U` of its divisorial sheaf. -/
private theorem nonempty_divisorialSheaf_restrictOpen_iso (D : Divisor X) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] :
    Nonempty (Divisor.divisorialSheaf (D.restrictOpen U) ≅ D.divisorialSheaf.restrict U.ι) :=
  ⟨(@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom U D)).symm⟩

/-- Relative differential forms restrict along an open immersion: for `ψ : Z ⟶ Y` an open
immersion and `p' = ψ ≫ p`, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm`, which contains the generic point, the canonical sheaf is `𝒪_T(K_T)` for a divisor
`K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  have : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS with hT
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  have : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  have : IsDominant T.ι := Opens.isDominant_ι (T.isOpen.dense ⟨_, (Classical.arbitrary T).2⟩)
  have hTv : IsNormalVariety K (T.ι ≫ sS) := hS.restrictOpen T
  have : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  have : QuasiCompact (T.ι ≫ sS) := hTv.1.toQuasiCompact
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T.ι ≫ sS)
  have hsm : MMP.Mori.IsSmoothScheme (T.ι ≫ sS) := by
    rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq, Scheme.Opens.ι_preimage_self]
  have hdimT : topologicalKrullDim T = n :=
    (topologicalKrullDim_opens_eq hS T).trans hn
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (T.ι ≫ sS) hsm hdimT
  classical
  let KS : MMP.Mori.Divisor S := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap T.ι) KT
  have hKS : KS.restrictOpen T = KT := by
    ext W
    rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective T.ι) KT W
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictOpen_iso KS T
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) (T'.ι ≫ T.ι ≫ sS) rfl n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

end CanonicalDivisorExistence

/-! ### Surface germs with a smooth boundary curve -/

/-- A resolution of a surface germ has finitely many exceptional curves: some finset contains
exactly the exceptional prime divisors. -/
public theorem IsGermResolution.exists_finset_isGermExceptionalCurve {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] (hf : IsGermResolution sX P f) :
    ∃ S : Finset (MMP.Mori.PrimeDivisor Y), ∀ C, C ∈ S ↔ IsGermExceptionalCurve f P C := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsNoetherian Y := {}
  obtain ⟨Z, hZf, hZc, hZirr, hZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (hf.isSurfaceGerm.2.2.1.preimage f.continuous)
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

/-- The exceptional curves of a resolution of a surface germ admit an enumeration
`E : Fin n → PrimeDivisor Y`. -/
public theorem IsGermResolution.exists_isExceptionalCurveEnumeration {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] (hf : IsGermResolution sX P f) :
    ∃ (n : ℕ) (E : Fin n → MMP.Mori.PrimeDivisor Y), IsExceptionalCurveEnumeration f P E := by
  classical
  obtain ⟨S, hS⟩ := hf.exists_finset_isGermExceptionalCurve
  exact ⟨S.card, fun j => (S.equivFin.symm j).1,
    ⟨fun a b hab => S.equivFin.symm.injective (Subtype.ext hab),
      fun j => (hS _).1 (S.equivFin.symm j).2,
      fun C hC => ⟨S.equivFin ⟨C, (hS C).2 hC⟩, by simp⟩⟩⟩

/-- A point strictly generizing the generic point of a prime divisor is the generic point. -/
theorem eq_genericPoint_of_genericPoint_lt {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (Q : Mori.PrimeDivisor Y) {w : Y} (hlt : Q.genericPoint < w) :
    w = genericPoint Y := by
  have h1 := Q.coheight_genericPoint
  have h0 : Order.coheight w = 0 := by
    have hfin : Order.coheight w < ⊤ :=
      (Order.coheight_anti hlt.le).trans_lt (by rw [h1]; exact ENat.one_lt_top)
    have := Order.coheight_strictAnti hlt hfin
    rw [h1] at this
    exact ENat.lt_one_iff_eq_zero.mp this
  have hle : w ≤ genericPoint Y := Scheme.le_iff_specializes.mpr (genericPoint_specializes w)
  exact ((genericPoint_specializes w).antisymm
    (Scheme.le_iff_specializes.mp (Order.coheight_eq_zero.mp h0 hle))).eq.symm

/-- If `j : Y ⟶ X` maps the generic point of `Y` to that of `X`, only finitely many prime divisors
`Q` of the Noetherian scheme `Y` have `j(η_Q) = η_Γ`, for a prime divisor `Γ` of `X`: each such
`Q` is an irreducible component of `j⁻¹(Γ)`. A strictly larger irreducible closed subset of
`j⁻¹(Γ)` through `Q` would have the generic point of `Y` as its generic point, which `j` sends to
`η_X ∉ Γ`. -/
private theorem finite_setOf_map_genericPoint_eq {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [CompactSpace Y] (j : Y ⟶ X)
    (hj : j.base (genericPoint Y) = genericPoint X) (Γ : Mori.PrimeDivisor X) :
    {Q : Mori.PrimeDivisor Y | j.base Q.genericPoint = Γ.genericPoint}.Finite := by
  classical
  have : IsNoetherian Y := {}
  have hZc : IsClosed (j.base ⁻¹' (Γ.support : Set X)) :=
    Γ.idealSheaf.support.isClosed.preimage j.continuous
  obtain ⟨Z, hZf, hZc', hZirr, hZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZc
  have hmemΓ : Γ.genericPoint ∈ (Γ.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have key : ∀ Q : Mori.PrimeDivisor Y, j.base Q.genericPoint = Γ.genericPoint →
      (Q.support : Set Y) ∈ Z := by
    intro Q hQ
    have hQsub : (Q.support : Set Y) ⊆ ⋃₀ (hZf.toFinset : Set (Set Y)) := by
      rw [hZf.coe_toFinset, ← hZ, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact closure_minimal (Set.singleton_subset_iff.mpr (by
        show j.base Q.genericPoint ∈ (Γ.support : Set X); rw [hQ]; exact hmemΓ)) hZc
    have hQirr : IsIrreducible (Q.support : Set Y) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
    obtain ⟨W, hW, hQW⟩ := (isIrreducible_iff_sUnion_isClosed.1 hQirr) hZf.toFinset
      (fun W hW => hZc' W (hZf.mem_toFinset.1 hW)) hQsub
    have hW' := hZf.mem_toFinset.1 hW
    have hWZ : W ⊆ j.base ⁻¹' (Γ.support : Set X) := by
      rw [hZ]; exact Set.subset_sUnion_of_mem hW'
    set w := (hZirr W hW').genericPoint
    have hwW : closure {w} = W := (hZirr W hW').closure_genericPoint (hZc' W hW')
    have hwQ : w ⤳ Q.genericPoint := by
      rw [specializes_iff_mem_closure, hwW]
      exact hQW (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
    by_cases hweq : w = Q.genericPoint
    · have : (Q.support : Set Y) = W := by
        rw [← hwW, hweq, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact this ▸ hW'
    exfalso
    have hlt : Q.genericPoint < w := by
      refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hwQ) fun h => hweq ?_
      exact ((Scheme.le_iff_specializes.mp h).antisymm hwQ).eq.symm
    have hwgen := eq_genericPoint_of_genericPoint_lt Q hlt
    have hwmem : j.base w ∈ (Γ.support : Set X) := hWZ (by rw [← hwW]; exact subset_closure rfl)
    rw [hwgen, hj, AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← specializes_iff_mem_closure] at hwmem
    have hΓgen : Γ.genericPoint = genericPoint X :=
      (hwmem.antisymm (genericPoint_specializes _)).eq
    have h1' := Γ.coheight_genericPoint
    rw [hΓgen, Order.coheight_eq_zero.mpr (fun b _ => Scheme.le_iff_specializes.mpr
      (genericPoint_specializes b))] at h1'
    exact absurd h1' (by decide)
  refine Set.Finite.of_finite_image (hZf.subset ?_) fun Q _ Q' _ h =>
    AlgebraicGeometry.PrimeDivisor.eq_of_support_eq h
  rintro _ ⟨Q, hQ, rfl⟩
  exact key Q hQ

/-- **Pull-back of a `ℚ`-divisor along a map preserving generic points.** For `j : Y ⟶ X` sending
`η_Y` to `η_X`, with `Y` Noetherian, every `ℚ`-divisor `Δ` of `X` has a pull-back `T` on `Y`:
its coefficient along a prime divisor `Q` is `Δ_Γ` if `j(η_Q) = η_Γ`, and `0` if `j(η_Q)` is the
generic point of no prime divisor of `X`. Only finitely many `Q` lie over each `Γ`
(`finite_setOf_map_genericPoint_eq`). -/
private theorem exists_coeff_eq_of_map_genericPoint {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] (j : Y ⟶ X)
    (hj : j.base (genericPoint Y) = genericPoint X) (Δ : QDivisor X) :
    ∃ T : QDivisor Y,
      (∀ (Q : Mori.PrimeDivisor Y) (Γ : Mori.PrimeDivisor X),
        j.base Q.genericPoint = Γ.genericPoint → T Q = Δ Γ) ∧
      ∀ Q : Mori.PrimeDivisor Y, (∀ Γ : Mori.PrimeDivisor X,
        j.base Q.genericPoint ≠ Γ.genericPoint) → T Q = 0 := by
  classical
  let F : Finset (Mori.PrimeDivisor Y) := Δ.support.biUnion fun Γ =>
    (finite_setOf_map_genericPoint_eq j hj Γ).toFinset
  let c : Mori.PrimeDivisor Y → ℚ := fun Q =>
    ∑ Γ ∈ Δ.support, if j.base Q.genericPoint = Γ.genericPoint then Δ Γ else 0
  refine ⟨Finsupp.onFinset F c ?_, fun Q Γ hQΓ => ?_, fun Q hQ => ?_⟩
  · intro Q hQ
    obtain ⟨Γ, hΓ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
    have : j.base Q.genericPoint = Γ.genericPoint := by_contra fun h => hne (if_neg h)
    exact Finset.mem_biUnion.mpr ⟨Γ, hΓ, (Set.Finite.mem_toFinset _).mpr this⟩
  · rw [Finsupp.onFinset_apply]
    change ∑ Γ' ∈ Δ.support, _ = _
    rw [Finset.sum_eq_single Γ (fun Γ' _ hne => if_neg fun h : j.base Q.genericPoint =
        Γ'.genericPoint =>
        hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h.symm.trans hQΓ)))
      (fun hΓ => by rw [if_pos hQΓ]; exact Finsupp.notMem_support_iff.mp hΓ), if_pos hQΓ]
  · rw [Finsupp.onFinset_apply]
    exact Finset.sum_eq_zero fun Γ _ => if_neg (hQ Γ)

/-- **A smooth boundary curve below a log terminal boundary gives type (3)** (FA 3.3.1, Fig. 3
(3)). Let `(Y, y; T)` be a surface germ with boundary over an algebraically closed field, log
terminal near `y`, and `C` a component of `T` with coefficient one which is regular at `y`. Then
`(Y, y; C)` is of type (3). On the minimal resolution, either there is no exceptional curve and
`C` is regular at `y`, or the log discrepancy vector of `(Y, y; C)` dominates that of
`(Y, y; T)` (the boundary degrees only grow, `T - C` being effective), which is positive by log
terminality, so `MMP.Flips.IsMinimalGermResolution.isFig3Type3_of_pos` applies. -/
private theorem isFig3Type3_single_of_isLogTerminal {K : Type u} [Field K] [IsAlgClosed K]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of K)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [LocallyOfFiniteType sY] {y : Y} (hy : IsSurfaceGerm sY y)
    (C : Mori.PrimeDivisor Y) (hCy : y ∈ C.support)
    (hCreg : IsRegularLocalRing
      (Y.presheaf.stalk y ⧸ AlgebraicGeometry.IdealSheafData.stalk C.idealSheaf y))
    {T : QDivisor Y} (hT : IsSurfaceGermWithBoundary sY y T) (hTC : T C = 1)
    {KY : Divisor Y} (hK : KY.IsCanonicalDivisor sY 2)
    (hlt : HoldsOnGerm {y} fun U : Y.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@TopologicalSpace.NoetherianSpace.isCompact _ _
          (haveI : AlgebraicGeometry.IsNoetherian Y := {}; inferInstance) _)
      IsLogTerminal (U.ι ≫ sY) 2 (DivisorWithCoeffs.restrictOpen U KY)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor T))) :
    IsFig3Type3 sY y (Finsupp.single C 1) := by
  classical
  have hsupp : (Finsupp.single C (1 : ℚ)).support = {C} :=
    Finsupp.support_single_ne_zero _ one_ne_zero
  have hC1 : IsSurfaceGermWithBoundary sY y (Finsupp.single C 1) := by
    refine ⟨hy, fun C' hC' => ?_, fun C' => ?_⟩
    · rw [hsupp, Finset.mem_singleton] at hC'
      subst hC'
      exact hCy
    · by_cases h : C' = C
      · subst h; simp
      · simp [Finsupp.single_apply, Ne.symm h]
  have hred : IsReducedBoundary (Finsupp.single C (1 : ℚ)) := by
    intro C' hC'
    rw [hsupp, Finset.mem_singleton] at hC'
    subst hC'
    simp
  obtain ⟨Ymin, f, _, _, _, hf⟩ := exists_isMinimalGermResolution sY hy
  obtain ⟨n, E, hE⟩ := hf.1.exists_isExceptionalCurveEnumeration
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨hC1, Ymin, f, inferInstance, inferInstance, inferInstance, 0, E, hf, hE,
      Or.inl ⟨rfl, C, hsupp, hCreg⟩⟩
  refine hf.isFig3Type3_of_pos hC1 hred (Finsupp.single_ne_zero.mpr one_ne_zero) hE hn
    fun a ha j => ?_
  set D : QDivisor Y := T - Finsupp.single C 1 with hDdef
  have hDC : ∀ C', D C' = T C' - (Finsupp.single C (1 : ℚ)) C' := fun C' => rfl
  have hD : IsSurfaceGermWithBoundary sY y D := by
    refine ⟨hy, fun C' hC' => ?_, fun C' => ?_⟩
    · rw [Finsupp.mem_support_iff, hDC] at hC'
      by_cases h : C' = C
      · subst h
        simp [hTC] at hC'
      · rw [Finsupp.single_apply, if_neg (Ne.symm h), sub_zero] at hC'
        exact hT.2.1 C' (Finsupp.mem_support_iff.mpr hC')
    · rw [hDC]
      by_cases h : C' = C
      · subst h
        simp [hTC]
      · rw [Finsupp.single_apply, if_neg (Ne.symm h), sub_zero]
        exact hT.2.2 C'
  obtain ⟨ΓC, hΓC⟩ := hf.1.exists_isWeightedDualGraph hC1 hE
  obtain ⟨ΓT, hΓT⟩ := hf.1.exists_isWeightedDualGraph hT hE
  obtain ⟨ΓD, hΓD⟩ := hf.1.exists_isWeightedDualGraph hD hE
  have hw : ∀ j, ΓC.weight j = ΓT.weight j := fun j => by
    have := (hΓC.weight j).unique (hΓT.weight j)
    exact_mod_cast neg_injective this
  have hew : ∀ j l, ΓC.edgeWeight j l = ΓT.edgeWeight j l := fun j l => by
    rcases eq_or_ne j l with rfl | h
    · rw [ΓC.edgeWeight_self, ΓT.edgeWeight_self]
    · exact_mod_cast (hΓC.edgeWeight j l h).unique (hΓT.edgeWeight j l h)
  have hM : ΓC.matrix = ΓT.matrix := by
    ext j l
    simp [WeightedGraph.matrix, hw, hew]
  have hp : ∀ j, ΓC.genus j = ΓT.genus j := fun j => by
    have := (hΓC.genus j).unique (hΓT.genus j)
    exact_mod_cast this
  have hβ : ∀ j, ΓC.boundary j ≤ ΓT.boundary j := fun j => by
    have hTD : T = Finsupp.single C 1 + D := by rw [hDdef]; abel
    have h := isIntersectionNumber_add (hΓC.boundary j) (hΓD.boundary j)
    rw [← map_add, ← hTD] at h
    have heq := h.unique (hΓT.boundary j)
    linarith [ΓD.boundary_nonneg j]
  obtain ⟨a', ha', -⟩ := ΓT.existsUnique_isLogDiscrepancyVector
    (det_pos_of_isNegDef hΓT.isNegDef).ne'
  have ha'pos := ((hΓT.isGermLogDiscrepancyVector_iff a').2 ha').pos_of_isLogTerminal hf hK hlt j
  have := le_of_isLogDiscrepancyVector_of_boundary_le hΓC.isNegDef hM hp hβ
    ((hΓC.isGermLogDiscrepancyVector_iff a).1 ha) ha' j
  linarith

section PltLogTerminal

variable {k : Type u} [Field k] {V : Scheme.{u}} {sV : V ⟶ Spec (.of k)}

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + c = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_add, top_add]
      rw [this] at h
      exact ENat.top_ne_natCast n (WithBot.coe_injective h)
    | coe d =>
      induction c using ENat.recTopCoe with
      | top =>
        exfalso
        have : ((d : ℕ∞) : WithBot ℕ∞) + ((⊤ : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_add, add_top]
        rw [this] at h
        exact ENat.top_ne_natCast n (WithBot.coe_injective h)
      | coe c =>
        have h' : d + c = n := by exact_mod_cast h
        have e1 : (((d : ℕ∞) : WithBot ℕ∞) + 2 ≤ (n : WithBot ℕ∞)) ↔ d + 2 ≤ n := by
          rw [show ((d : ℕ∞) : WithBot ℕ∞) + 2 = (((d + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) from rfl,
            show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, WithBot.coe_le_coe,
            Nat.cast_le]
        rw [e1]
        constructor
        · intro h2
          exact_mod_cast (show 2 ≤ c by omega)
        · intro h2
          have : 2 ≤ c := by exact_mod_cast h2
          omega

/-- An exceptional divisor over `V` in the sense of FA (its center has dimension at most
`dim V - 2`) is exceptional in the sense of Kollár–Mori. Both say that `f(η_E)` has coheight at
least two. -/
private theorem ProperDivisorOver.isExceptional_toDivisorOver [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] (hV : IsNormalVariety k sV) {n : ℕ}
    (hn : topologicalKrullDim V = n) (D : ProperDivisorOver k sV) (hD : D.IsExceptional) :
    D.toDivisorOver.IsExceptional := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : LocallyOfFiniteType sV := hV.1.toLocallyOfFiniteType
  haveI : IsSeparated sV := hV.1.toIsSeparated
  haveI : IsSeparated (V ↘ ⊤_ Scheme) := by
    rw [show (V ↘ ⊤_ Scheme) = sV ≫ Limits.terminal.from (Spec (.of k)) from
      Subsingleton.elim _ _]
    infer_instance
  have h2 : 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
    unfold ProperDivisorOver.IsExceptional at hD
    rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint,
      hn] at hD
    have h := topologicalKrullDim_closure_singleton_add_coheight sV (D.f D.E.genericPoint)
    rw [hn] at h
    exact (withBot_add_two_le_iff h).mp hD
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hc : TopologicalSpace.Closeds.closure
      (D.toDivisorOver.f '' (D.toDivisorOver.E.idealSheaf.support : Set D.toDivisorOver.Y)) =
      ⟨(D.toDivisorOver.center : Set V), D.toDivisorOver.center.isClosed⟩ :=
    TopologicalSpace.Closeds.ext <| by
      rw [TopologicalSpace.Closeds.coe_closure]; exact D.toDivisorOver.coe_center.symm
  rw [hc, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]
  exact h2

open scoped WithZero in
/-- A discrepancy `a(F, D_X)` is computed on a divisor `(Y, f, E)` over `V` with `ord_E = F`, and
`1 + a` is the log discrepancy of that divisor in the sense of
`MMP.Intersection.IsLogDiscrepancy`. -/
private theorem exists_isLogDiscrepancy_of_isDiscrepancy [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] [LocallyOfFiniteType sV] {n : ℕ} {K : Divisor V}
    {D_X : RDivisor V} {F : Valuation V.functionField ℤᵐ⁰} {a : ℝ}
    (h : MMP.Flips.IsDiscrepancy sV n K D_X F a) :
    ∃ E : ProperDivisorOver k sV, E.valuation = F ∧
      MMP.Intersection.IsLogDiscrepancy sV n D_X E.toDivisorOver (1 + a) := by
  obtain ⟨hK, -, -, E, ω, m, r, L, hEF, rfl, hX, -, hω0, hLc, hL, L', hLpb, rfl⟩ := h
  refine ⟨E, hEF, hX, E.isProper, ω, hω0, ⟨_, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, m, r, L,
    L', hLc, fun Γ => ?_, hLpb, by ring⟩
  have := congrArg (fun G : RDivisor V => G.coeff Γ) hL
  simp only [coeff_sum_smul_toRDivisor] at this
  rw [← this, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm]

/-- **A plt pair with a log resolution is log terminal** (FA 2.13.1). If `(V, Δ)` is plt in the
sense of Kollár–Mori (`discrep(V, Δ) > -1`) and `f` is a log resolution of `(V, Δ)`, then every
exceptional prime divisor of `f` has discrepancy `> -1`, so `(V, Δ)` is log terminal with witness
`f`. -/
private theorem isLogTerminal_of_isPltPair [PerfectField k] [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [LocallyOfFiniteType sV] {n : ℕ}
    {K : Divisor V} {Δ : QDivisor V} (h : IsPltPair sV n K Δ)
    (hKΔ : IsCartierCombination (Divisor.toRDivisor K + QDivisor.toRDivisor Δ))
    {W : Scheme.{u}} {f : W ⟶ V} (hf : Flips.IsLogResolution sV (QDivisor.toRDivisor Δ) f) :
    IsLogTerminal sV n K (QDivisor.toRDivisor Δ) := by
  refine ⟨hf.1, h.1.2.1, hKΔ, W, f, hf, fun hY hb hp E hE b hb' => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hb'
  let D : ProperDivisorOver k sV := ProperDivisorOver.mk ⟨W, f, hY, hb, E⟩ hp
  have hDexc := ProperDivisorOver.isExceptional_toDivisorOver h.1.1 h.1.2.1.1 D hE
  obtain ⟨q, hq⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy h.1.isPair h.1.2.1 D.toDivisorOver
  obtain ⟨E₁, hE₁, hlog₁⟩ := exists_isLogDiscrepancy_of_isDiscrepancy ha
  have hlogD := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hq hp
  have h1 : 1 + a = 1 + (q : ℝ) :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog₁ hlogD hE₁
  have hle := discrep_le hDexc hq
  have hlt : ((-1 : ℝ) : EReal) < ((q : ℝ) : EReal) := by
    have := h.2.trans_le hle
    rwa [show ((-1 : ℝ) : EReal) = -1 by norm_num]
  have : (-1 : ℝ) < (q : ℝ) := EReal.coe_lt_coe_iff.mp hlt
  linarith

end PltLogTerminal

/-- A `ℚ`-Cartier `ℚ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_toRDivisor {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : QDivisor X} (h : D.IsQCartier) :
    IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, r, L, hL, rfl⟩ := (QDivisor.isCartierCombination_iff_isQCartier D).mpr h
  refine ⟨m, fun j => (r j : ℝ), L, hL, ?_⟩
  refine DivisorWithCoeffs.ext' fun E => ?_
  rw [QDivisor.coeff_toRDivisor]
  simp only [DivisorWithCoeffs.coeff, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Rat.cast_sum, Rat.cast_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [DivisorWithCoeffs.mapCoeffs]

/-- **Log terminality near a plt point.** Let `(X, Δ)` be a pair over a field of characteristic
zero with `Δ` a boundary, plt at `P`. Then there is an open `V ∋ P` on which `(V, Δ|_V)` is log
terminal: take for `V` the open on which `(X, Δ)` is plt; it is a normal variety, so it has a log
resolution, and `K_V + Δ|_V` is `ℚ`-Cartier, `(V, Δ|_V)` being a pair. -/
private theorem exists_isLogTerminal_of_isAt {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hΔ : ∀ E, 0 ≤ Δ E ∧ Δ E ≤ 1) {P : X}
    (hplt : IsAt sX (fun sU n K Δ => IsPltPair sU n K Δ) n K Δ P) :
    ∃ V : X.Opens, P ∈ V ∧ ∀ [Nonempty V] [CompactSpace V],
      IsLogTerminal (V.ι ≫ sX) n (K.restrictOpen V) (QDivisor.toRDivisor (Δ.restrictOpen V)) := by
  obtain ⟨V, hPV, hne, hpltV⟩ := hplt
  refine ⟨V, hPV rfl, ?_⟩
  intros
  have hlogvar : IsLogVariety k (V.ι ≫ sX) (QDivisor.toRDivisor (Δ.restrictOpen V)) :=
    ⟨hpltV.1.1, fun E => by
      rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_restrictOpen]
      exact ⟨by exact_mod_cast (hΔ _).1, by exact_mod_cast (hΔ _).2⟩⟩
  obtain ⟨W, f, hf, -⟩ := MMP.Flips.exists_isLogResolution_isProjectiveMorphism (V.ι ≫ sX)
    hlogvar.isNormalVariety _ hlogvar.isBoundary
  have hKΔ : IsCartierCombination
      (Divisor.toRDivisor (K.restrictOpen V) + QDivisor.toRDivisor (Δ.restrictOpen V)) := by
    have := isCartierCombination_toRDivisor hpltV.1.2.2
    rwa [map_add, QDivisor.toRDivisor_toQDivisor] at this
  exact isLogTerminal_of_isPltPair hpltV hKΔ hf

/-- `ht 𝔭 + dim R/𝔭 ≤ dim R` for a prime `𝔭`. -/
private theorem height_add_ringKrullDim_quotient_le {R : Type*} [CommRing R] (I : Ideal R)
    [I.IsPrime] : (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I) ≤ ringKrullDim R := by
  let p : PrimeSpectrum R := ⟨I, inferInstance⟩
  have : Nonempty (PrimeSpectrum R) := ⟨p⟩
  have hz : PrimeSpectrum.zeroLocus (I : Set R) = Set.Ici p := Set.ext fun _ => Iff.rfl
  rw [ringKrullDim_quotient, hz, ← Order.coheight_eq_krullDim_Ici,
    show I.height = Order.height p from PrimeSpectrum.height_eq_orderHeight p, ← WithBot.coe_add]
  change _ ≤ Order.krullDim (PrimeSpectrum R)
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  exact WithBot.coe_le_coe.mpr
    (le_iSup (fun x : PrimeSpectrum R => Order.height x + Order.coheight x) p)

/-- A prime `I` of a local ring, strictly below the maximal ideal, with `1 + dim A/I ≤ 2`, has
`dim A/I = 1`. -/
private theorem ringKrullDim_quotient_eq_one_of_ne {A : Type*} [CommRing A] [IsLocalRing A]
    (I : Ideal A) [I.IsPrime] (h : I ≠ maximalIdeal A)
    (hle : (1 : WithBot ℕ∞) + ringKrullDim (A ⧸ I) ≤ 2) : ringKrullDim (A ⧸ I) = 1 := by
  have hlt : I < maximalIdeal A := lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) h
  have hge : 1 ≤ ringKrullDim (A ⧸ I) := by
    rw [ringKrullDim_quotient, Order.one_le_krullDim_iff]
    exact ⟨⟨⟨I, inferInstance⟩, show I ≤ I from le_rfl⟩,
      ⟨⟨maximalIdeal A, inferInstance⟩, show I ≤ maximalIdeal A from hlt.le⟩, hlt⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ∞, ringKrullDim (A ⧸ I) = d := by
    induction h : ringKrullDim (A ⧸ I) using WithBot.recBotCoe with
    | bot =>
      rw [h] at hge
      exact absurd hge (by decide)
    | coe d => exact ⟨d, rfl⟩
  rw [hd] at hle hge ⊢
  have h1 : (1 : ℕ∞) + d ≤ 2 := WithBot.coe_le_coe.mp (by simpa using hle)
  have h2 : (1 : ℕ∞) ≤ d := WithBot.coe_le_coe.mp (by simpa using hge)
  have : d = 1 := by
    induction d using ENat.recTopCoe with
    | top => simp at h1
    | coe d =>
      have h1' : 1 + d ≤ 2 := by exact_mod_cast h1
      have h2' : 1 ≤ d := by exact_mod_cast h2
      exact_mod_cast (show d = 1 by omega)
  rw [this]
  rfl

/-- At a point `P` of a prime divisor `S` with `dim 𝒪_{X,P} = 2`, the local ring `𝒪_{X,P}/I_S` of
`S` at `P` has dimension one: `I_S` has height one, so `dim 𝒪_{X,P}/I_S ≤ 2 - 1`, and `I_S` is not
the maximal ideal, which has height two. -/
private theorem ringKrullDim_quotient_ker_eq_one {X : Scheme.{u}} [IsLocallyNoetherian X]
    (S : Mori.PrimeDivisor X) {P : X} (hPS : S.genericPoint ⤳ P)
    (hP : ringKrullDim (X.presheaf.stalk P) = 2) :
    ringKrullDim (X.presheaf.stalk P ⧸
      RingHom.ker (X.presheaf.stalkSpecializes hPS ≫ X.residue S.genericPoint).hom) = 1 := by
  rw [← stalk_idealSheaf_eq_ker S hPS]
  haveI : (AlgebraicGeometry.IdealSheafData.stalk S.idealSheaf P).IsPrime := by
    rw [stalk_idealSheaf_eq_ker S hPS]
    exact RingHom.ker_isPrime _
  have hht := MMP.Flips.ResolutionInputs.height_stalk_eq_one_of_isPureCodimOne S.idealSheaf
    (MMP.Resolution.isPureCodimOne_support_primeDivisor S) (x := P)
  set I := AlgebraicGeometry.IdealSheafData.stalk S.idealSheaf P
  have hle := height_add_ringKrullDim_quotient_le I
  rw [hht, hP] at hle
  have hIm : I ≠ maximalIdeal (X.presheaf.stalk P) := by
    intro h
    have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := X.presheaf.stalk P)
    rw [← h, hht, hP] at h2
    exact absurd h2 (by decide)
  exact ringKrullDim_quotient_eq_one_of_ne I hIm (by exact_mod_cast hle)

/-- **The pull-back of a boundary, cut down to a germ.** Let `j : Y ⟶ X` send `η_Y` to `η_X`, with
`Y` Noetherian, and let `Δ` be a boundary on `X` (coefficients in `[0, 1]`). For `y ∈ Y` with
`j(y)` in an open `V`, there is a `ℚ`-divisor `T₀` on `Y`, all of whose components pass through
`y`, with coefficients in `[0, 1]`, and an open `U₀ ∋ y` inside `j⁻¹(V)`, such that `T₀` is the
flat pull-back of `Δ` along components through `y` and `T₀|_{U₀}` is the flat pull-back of `Δ|_V`.
Take the pull-back `T` of `Δ`, keep its components through `y`, and remove from `j⁻¹(V)` the
(finitely many, closed) components of `T` missing `y`. -/
private theorem exists_germ_pullback_boundary {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [CompactSpace Y] (j : Y ⟶ X)
    (hj : j.base (genericPoint Y) = genericPoint X) {Δ : QDivisor X}
    (hΔ : ∀ E, 0 ≤ Δ E ∧ Δ E ≤ 1) {y : Y} {V : X.Opens} (hyV : j.base y ∈ V) :
    ∃ (T₀ : QDivisor Y) (U₀ : Y.Opens), y ∈ U₀ ∧ U₀ ≤ j ⁻¹ᵁ V ∧
      (∀ Q ∈ T₀.support, y ∈ Q.support) ∧ (∀ Q, 0 ≤ T₀ Q ∧ T₀ Q ≤ 1) ∧
      (∀ Q Γ, y ∈ Q.support → j.base Q.genericPoint = Γ.genericPoint → T₀ Q = Δ Γ) ∧
      (∀ (Q₀ : Mori.PrimeDivisor U₀) (Γ' : Mori.PrimeDivisor V),
        j.base (U₀.ι.base Q₀.genericPoint) = V.ι.base Γ'.genericPoint →
          ((QDivisor.toRDivisor T₀).restrictOpen U₀).coeff Q₀ =
            (QDivisor.toRDivisor (Δ.restrictOpen V)).coeff Γ') ∧
      ∀ Q₀ : Mori.PrimeDivisor U₀, (∀ Γ' : Mori.PrimeDivisor V,
        j.base (U₀.ι.base Q₀.genericPoint) ≠ V.ι.base Γ'.genericPoint) →
          ((QDivisor.toRDivisor T₀).restrictOpen U₀).coeff Q₀ = 0 := by
  classical
  obtain ⟨T, hT1, hT2⟩ := exists_coeff_eq_of_map_genericPoint j hj Δ
  set T₀ : QDivisor Y := Finsupp.filter (fun Q => y ∈ Q.support) T with hT₀def
  set Bad : Finset (Mori.PrimeDivisor Y) := Finset.filter (fun Q => y ∉ Q.support) T.support
  have hBadc : IsClosed (⋃ Q ∈ Bad, (Q.support : Set Y)) :=
    isClosed_biUnion_finset fun Q _ => Q.idealSheaf.support.isClosed
  set U₀ : Y.Opens := j ⁻¹ᵁ V ⊓ ⟨_, hBadc.isOpen_compl⟩ with hU₀def
  have hyU₀ : y ∈ U₀ := by
    refine ⟨hyV, ?_⟩
    show y ∉ ⋃ Q ∈ Bad, (Q.support : Set Y)
    simp only [Set.mem_iUnion, not_exists]
    exact fun Q hQ hyQ => (Finset.mem_filter.mp hQ).2 hyQ
  have hT₀eq : ∀ Q : Mori.PrimeDivisor Y, Q.genericPoint ∈ U₀ → T₀ Q = T Q := fun Q hQ => by
    rw [hT₀def, Finsupp.filter_apply]
    split_ifs with hy
    · rfl
    · by_contra hne
      have hQBad : Q ∈ Bad :=
        Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (Ne.symm hne), hy⟩
      refine hQ.2 (Set.mem_biUnion hQBad ?_)
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  have hgenU₀ : ∀ Q₀ : Mori.PrimeDivisor U₀,
      Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U₀.ι Q₀) =
        U₀.ι.base Q₀.genericPoint :=
    fun Q₀ => OpenWeilRestriction.genericPoint_primeDivisorMap _ _
  have hgenV : ∀ Γ' : Mori.PrimeDivisor V,
      Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap V.ι Γ') =
        V.ι.base Γ'.genericPoint :=
    fun Γ' => OpenWeilRestriction.genericPoint_primeDivisorMap _ _
  have hQU : ∀ Q₀ : Mori.PrimeDivisor U₀,
      Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U₀.ι Q₀) ∈ U₀ :=
    fun Q₀ => by rw [hgenU₀]; exact Q₀.genericPoint.2
  refine ⟨T₀, U₀, hyU₀, inf_le_left, fun Q hQ => ?_, fun Q => ?_, fun Q Γ hyQ hQΓ => ?_,
    fun Q₀ Γ' h => ?_, fun Q₀ h => ?_⟩
  · rw [hT₀def, Finsupp.support_filter, Finset.mem_filter] at hQ
    exact hQ.2
  · rw [hT₀def, Finsupp.filter_apply]
    split_ifs
    · by_cases h : ∃ Γ : Mori.PrimeDivisor X, j.base Q.genericPoint = Γ.genericPoint
      · obtain ⟨Γ, hΓ⟩ := h
        rw [hT1 Q Γ hΓ]
        exact hΔ Γ
      · push Not at h
        rw [hT2 Q h]
        norm_num
    · norm_num
  · rw [hT₀def, Finsupp.filter_apply, if_pos hyQ, hT1 Q Γ hQΓ]
  · rw [DivisorWithCoeffs.coeff_restrictOpen, QDivisor.coeff_toRDivisor,
      QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_restrictOpen]
    congr 1
    refine (hT₀eq _ (hQU Q₀)).trans (hT1 _ _ ?_)
    rw [hgenU₀, hgenV]
    exact h
  · rw [DivisorWithCoeffs.coeff_restrictOpen, QDivisor.coeff_toRDivisor]
    rw [show DivisorWithCoeffs.coeff T₀ (OpenWeilRestriction.primeDivisorMap U₀.ι Q₀) =
      T₀ (OpenWeilRestriction.primeDivisorMap U₀.ι Q₀) from rfl, hT₀eq _ (hQU Q₀)]
    by_cases hΓ : ∃ Γ : Mori.PrimeDivisor X,
        j.base (Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U₀.ι Q₀)) =
          Γ.genericPoint
    · obtain ⟨Γ, hΓ⟩ := hΓ
      exfalso
      have hΓV : Γ.genericPoint ∈ Set.range V.ι.base := by
        rw [V.range_ι, ← hΓ]
        exact (hQU Q₀).1
      obtain ⟨Γ', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff V.ι Γ).2 hΓV
      refine h Γ' ?_
      rw [← hgenU₀, ← hgenV]
      exact hΓ
    · push Not at hΓ
      rw [hT2 _ hΓ]
      simp

/-- **From a type (3) surface model to a cyclic model.** Let `j : Y ⟶ X` be a surface model of
`(X, S)` at `P`: a morphism over `Spec κ^sep ⟶ Spec k`, a point `y` over `P`, a prime divisor `C`
of `Y` through `y` and an isomorphism `𝒪̂_{Y,y} ≅ Ĥ` over `𝒪_{X,P}` carrying `I_C` onto `I_S Ĥ`.
If `(Y, y; C)` is of type (3), the cyclic quotient model of `(𝒪̂_{Y,y}, I_C)` transports to one
of `(Ĥ, I_S Ĥ)`. -/
private theorem isCyclicModel_of_isFig3Type3 {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (S : Mori.PrimeDivisor X) (P : X) (hPS : S.genericPoint ⤳ P)
    (κsep : Type u) [Field κsep] [IsAlgClosed κsep] [CharZero κsep]
    [Algebra (ResidueField (X.presheaf.stalk P)) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk P) H]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of κsep)) (j : Y ⟶ X) (y : Y) (C : Mori.PrimeDivisor Y)
    (hCy : C.genericPoint ⤳ y) (hjy : j.base y ⤳ P)
    (hjcompat : j ≫ sX = sY ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap (ResidueField (X.presheaf.stalk P)) κsep).comp
        (letI := stalkAlgebra sX P; algebraMap k (ResidueField (X.presheaf.stalk P))))))
    (e : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) ≃+*
      AdicCompletion (maximalIdeal H) H)
    (he : ∀ a, e (algebraMap _ _ ((X.presheaf.stalkSpecializes hjy ≫ j.stalkMap y).hom a)) =
      algebraMap H (AdicCompletion (maximalIdeal H) H) (algebraMap _ H a))
    (hIdeal : ((RingHom.ker (Y.presheaf.stalkSpecializes hCy ≫ Y.residue C.genericPoint).hom).map
        (algebraMap _
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))).map e =
      ((RingHom.ker (X.presheaf.stalkSpecializes hPS ≫ X.residue S.genericPoint).hom).map
        (algebraMap _ H)).map (algebraMap H (AdicCompletion (maximalIdeal H) H)))
    (h3 : IsFig3Type3 sY y (Finsupp.single C 1)) :
    letI := stalkAlgebra sX P
    ∃ m : ℕ, 1 ≤ m ∧ ∃ q : ℤ, Int.gcd q m = 1 ∧
      IsCyclicModel k (AlgebraicGeometry.IdealSheafData.stalk S.idealSheaf P) m q κsep H := by
  letI := stalkAlgebra sX P
  letI := stalkAlgebra sY y
  have hsupp : (Finsupp.single C (1 : ℚ)).support = {C} :=
    Finsupp.support_single_ne_zero _ one_ne_zero
  have hred : IsReducedBoundary (Finsupp.single C (1 : ℚ)) := by
    intro C' hC'
    rw [hsupp, Finset.mem_singleton] at hC'
    subst hC'
    simp
  obtain ⟨m, q, h, φ, hc, hI⟩ := exists_ringEquiv_cyclicInvariants_of_isFig3Type3_or_isFig3Type9
    sY y _ hred _ (Or.inl ⟨h3, rfl⟩)
  rw [comap_vanishingIdeal_cyclicQuotientImage, radical_span_X] at hI
  have hinf : (⨅ C' ∈ (Finsupp.single C (1 : ℚ)).support, C'.idealSheaf) = C.idealSheaf := by
    rw [hsupp]
    simp
  rw [hinf, stalk_idealSheaf_eq_ker C hCy] at hI
  refine ⟨m, h.one_le, q, h.gcd_eq_one, ?_⟩
  rw [stalk_idealSheaf_eq_ker S hPS]
  refine isCyclicModel_of_ringEquiv (X.presheaf.stalkSpecializes hjy ≫ j.stalkMap y).hom
    (fun c => ?_) e he hIdeal φ hc hI
  have := stalkSpecializes_stalkMap_algebraMap sX sY j _ hjcompat hjy c
  refine this.trans ?_
  simp only [RingHom.coe_comp, Function.comp_apply]
  rfl

/-- For one strict henselization `H` of `𝒪_{X,P}`, the completed strict local pair at `P` is a
cyclic quotient pair. -/
private theorem exists_isCyclicModel {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) {n : ℕ} {KX : Divisor X}
    (S : Mori.PrimeDivisor X) (hS : IsNormalVariety k (S.idealSheaf.subschemeι ≫ sX))
    (B : QDivisor X) (hB : 0 ≤ B) (hB_le : ∀ E : Mori.PrimeDivisor X, B.coeff E ≤ 1)
    (hBS : B.coeff S = 0)
    (P : X) (hPS : P ∈ S.support) (hP : ringKrullDim (X.presheaf.stalk P) = 2)
    (hplt : IsAt sX (fun sU n K Δ => IsPltPair sU n K Δ) n KX (Finsupp.single S 1 + B) P)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk P)) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk P)) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk P) H]
    [IsHenselization (X.presheaf.stalk P) κsep H] :
    letI := stalkAlgebra sX P
    ∃ m : ℕ, 1 ≤ m ∧ ∃ q : ℤ, Int.gcd q m = 1 ∧
      IsCyclicModel k (AlgebraicGeometry.IdealSheafData.stalk S.idealSheaf P) m q κsep H := by
  letI := stalkAlgebra sX P
  haveI : CharZero (ResidueField (X.presheaf.stalk P)) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  haveI : CharZero κsep :=
    charZero_of_injective_algebraMap (algebraMap (ResidueField (X.presheaf.stalk P)) κsep).injective
  haveI : IsSepClosed κsep := IsSepClosure.sep_closed (ResidueField (X.presheaf.stalk P))
  have hPS' : S.genericPoint ⤳ P := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hPS
  obtain ⟨Y, sY, j, y, C, hCy, hjy, hgerm, hjP, hCs, hjC, hjflat, hjfu, hjcompat, e, he, hIdeal,
    htrans⟩ := exists_surfaceModel_of_codimension_two k X sX hX S hS.2 P hPS'
      (ringKrullDim_quotient_ker_eq_one S hPS' hP) κsep H
  have h3 : IsFig3Type3 sY y (Finsupp.single C 1) := by
    have hYv := hgerm.1
    haveI : IsIntegral Y := hYv.1.toIsIntegral
    haveI : IsNormal Y := hYv.2
    haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : CompactSpace Y :=
      haveI := hYv.1.toQuasiCompact
      QuasiCompact.compactSpace_of_compactSpace sY
    have hCmem : y ∈ C.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
      exact hCy
    have hCreg : IsRegularLocalRing
        (Y.presheaf.stalk y ⧸ AlgebraicGeometry.IdealSheafData.stalk C.idealSheaf y) :=
      MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_stalk sY C.idealSheaf
        ((MMP.Mori.isSmoothScheme_iff _).mpr hCs) hCmem
    obtain ⟨KY, hKY⟩ : ∃ KY : Divisor Y, KY.IsCanonicalDivisor sY 2 :=
      exists_isCanonicalDivisor sY hYv (n := 2) (by exact_mod_cast hgerm.2.1)
    obtain ⟨T, hT, hTC, hlt⟩ : ∃ T : QDivisor Y, IsSurfaceGermWithBoundary sY y T ∧ T C = 1 ∧
        HoldsOnGerm {y} fun U : Y.Opens => ∀ [Nonempty U],
          haveI : CompactSpace U := isCompact_iff_compactSpace.mp
            (@TopologicalSpace.NoetherianSpace.isCompact _ _
              (haveI : AlgebraicGeometry.IsNoetherian Y := {}; inferInstance) _)
          IsLogTerminal (U.ι ≫ sY) 2 (DivisorWithCoeffs.restrictOpen U KY)
            (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor T)) := by
      classical
      set Δ : QDivisor X := Finsupp.single S 1 + B with hΔdef
      have hΔS : Δ S = 1 := by simp [hΔdef, show B S = 0 from hBS]
      have hΔb : ∀ E, 0 ≤ Δ E ∧ Δ E ≤ 1 := fun E => by
        by_cases h : E = S
        · subst h
          rw [hΔS]
          norm_num
        · simp only [hΔdef, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm h),
            zero_add]
          exact ⟨hB E, hB_le E⟩
      haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
      obtain ⟨V, hPV, hltV⟩ := exists_isLogTerminal_of_isAt hΔb hplt
      have hjgen : j.base (genericPoint Y) = genericPoint X := by
        obtain ⟨y', hy', hjy'⟩ := Flat.generalizingMap j
          (genericPoint_specializes (j.base (genericPoint Y)))
        rw [← hjy', ((genericPoint_specializes y').antisymm hy').eq]
      obtain ⟨T₀, U₀, hyU₀, hU₀V, hT₀s, hT₀b, hT₀Δ, hB1, hB2⟩ :=
        exists_germ_pullback_boundary j hjgen hΔb (V := V) (by rw [hjP]; exact hPV)
      refine ⟨T₀, ⟨hgerm, hT₀s, hT₀b⟩, by rw [hT₀Δ C S hCmem hjC, hΔS],
        U₀, Set.singleton_subset_iff.mpr hyU₀, ?_⟩
      intro
      haveI : Nonempty V := ⟨⟨P, hPV⟩⟩
      haveI : CompactSpace X := haveI := hX.1.toQuasiCompact
        QuasiCompact.compactSpace_of_compactSpace sX
      haveI : AlgebraicGeometry.IsNoetherian X := {}
      haveI : CompactSpace V := isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact _)
      haveI : AlgebraicGeometry.IsNoetherian Y := {}
      haveI : Nonempty (j ⁻¹ᵁ V) := ⟨⟨y, hU₀V hyU₀⟩⟩
      haveI : CompactSpace (j ⁻¹ᵁ V) := isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact _)
      haveI : CompactSpace U₀ := isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact _)
      exact (htrans V hPV).2.2 U₀ hyU₀ hU₀V n (KX.restrictOpen V)
        (QDivisor.toRDivisor (Δ.restrictOpen V)) (KY.restrictOpen U₀)
        ((QDivisor.toRDivisor T₀).restrictOpen U₀) hB1 hB2 (hKY.restrictOpen hYv U₀) hltV
    exact isFig3Type3_single_of_isLogTerminal hgerm C hCmem hCreg hT hTC hKY hlt
  exact isCyclicModel_of_isFig3Type3 sX S P hPS' κsep H sY j y C hCy hjy hjcompat e he hIdeal h3

/-- If the completed strict local ring at `P` is the cyclic invariant ring of order `m`, the
`m`-th reflexive power of every finite reflexive `𝒪_{X,P}`-module of rank one is free. -/
private theorem nonempty_linearEquiv_reflexivePower_stalk {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (P : X) (m : ℕ) (hm : 1 ≤ m) (q : ℤ)
    (hq : Int.gcd q m = 1)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk P)) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk P)) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk P) H]
    [IsHenselization (X.presheaf.stalk P) κsep H]
    (φ : cyclicInvariants κsep m q ≃+* AdicCompletion (maximalIdeal H) H)
    (N : ModuleCat.{u} (X.presheaf.stalk P)) [Module.Finite (X.presheaf.stalk P) N]
    [Module.IsReflexive (X.presheaf.stalk P) N] (hN : Module.rank (X.presheaf.stalk P) N = 1) :
    Nonempty (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePower N m
      ≃ₗ[X.presheaf.stalk P] X.presheaf.stalk P) := by
  letI := stalkAlgebra sX P
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : Algebra.EssFiniteType k (X.presheaf.stalk P) := essFiniteType_stalk sX P
  set R := AdicCompletion (maximalIdeal H) H
  have hRdom : IsDomain R := by
    have : IsDomain (cyclicInvariants κsep m q) := NoZeroDivisors.to_isDomain _
    exact Function.Injective.isDomain (φ.symm : R →+* cyclicInvariants κsep m q)
      φ.symm.injective
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk P) R) := by
    have : IsNoetherianRing H :=
      IsLocalRing.isNoetherianRing_of_isHenselization (A := X.presheaf.stalk P) (B := H) κsep
    have h1 : Function.Injective (algebraMap (X.presheaf.stalk P) H) := by
      haveI := (inferInstance : IsHenselization (X.presheaf.stalk P) κsep H).faithfullyFlat
      exact FaithfulSMul.algebraMap_injective _ H
    have h2 : Function.Injective (algebraMap H R) :=
      AdicCompletion.of_injective (maximalIdeal H) H
    rw [IsScalarTower.algebraMap_eq (X.presheaf.stalk P) H]
    exact h2.comp h1
  haveI : FaithfulSMul (X.presheaf.stalk P) (FractionRing R) := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq (X.presheaf.stalk P) R (FractionRing R)]
    exact (IsFractionRing.injective R (FractionRing R)).comp hinj
  letI : Algebra (FractionRing (X.presheaf.stalk P)) (FractionRing R) :=
    FractionRing.liftAlgebra _ _
  haveI : IsScalarTower (X.presheaf.stalk P) (FractionRing (X.presheaf.stalk P))
      (FractionRing R) := FractionRing.isScalarTower_liftAlgebra _ _
  obtain ⟨_, ⟨hRN, -, hRic⟩, -, hmod, -⟩ :=
    MMP.isIntegrallyClosed_adicCompletion_strictHenselization_and_descent k
      (X.presheaf.stalk P) κsep H (FractionRing (X.presheaf.stalk P)) (FractionRing R)
  obtain ⟨⟨hrefl', hrank'⟩, -⟩ := hmod N hN
  have hset : IsCyclicQuotientSetting κsep m q := by
    haveI : CharZero κsep := charZero_of_injective_ringHom
      (((algebraMap (ResidueField (X.presheaf.stalk P)) κsep).comp
        ((residue (X.presheaf.stalk P)).comp (algebraMap k (X.presheaf.stalk P))))).injective
    haveI : IsSepClosed κsep := IsSepClosure.sep_closed (ResidueField (X.presheaf.stalk P))
    exact ⟨inferInstance, inferInstance, hm, hq⟩
  have hCl : ∀ c : weilDivisorClassGroup (Spec (CommRingCat.of R)), m • c = 0 :=
    nsmul_eq_zero_weilDivisorClassGroup_of_ringEquiv hset φ
  haveI : IsNormal (Spec (CommRingCat.of R)) := isNormal_spec (CommRingCat.of R)
  obtain ⟨e⟩ := MMP.Flips.nonempty_linearEquiv_reflexivePower_of_nsmul_eq_zero
    (R := CommRingCat.of R) hCl (ModuleCat.of _ (TensorProduct (X.presheaf.stalk P) R N)) hrank'
  haveI := Module.Free.of_equiv e.symm
  obtain ⟨⟨e₁⟩, hfree'⟩ := MMP.nonempty_baseChange_reflexivePower_equiv_and_free_of_free k
    (X.presheaf.stalk P) κsep H (FractionRing (X.presheaf.stalk P)) (FractionRing R)
    (ModuleCat.of (CommRingCat.of (X.presheaf.stalk P)) N) hN m
  haveI hfree := hfree' inferInstance
  haveI : Module.Finite (X.presheaf.stalk P)
      (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePower
        (ModuleCat.of (CommRingCat.of (X.presheaf.stalk P)) N) m) :=
    Stacks.AlgebraicGeometry.ModuleReflexivePower.finite_reflexivePower _ m
  have hr : Module.finrank (X.presheaf.stalk P)
      (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePower
        (ModuleCat.of (CommRingCat.of (X.presheaf.stalk P)) N) m) = 1 := by
    rw [← Module.finrank_baseChange (R := R) (S := X.presheaf.stalk P),
      (e₁.trans e).finrank_eq]
    exact Module.finrank_self R
  exact ⟨LinearEquiv.ofFinrankEq _ _ (hr.trans (Module.finrank_self _).symm)⟩

private theorem nsmul_eq_zero_weilDivisorClassGroup_stalk {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (P : X) (m : ℕ) (hm : 1 ≤ m) (q : ℤ)
    (hq : Int.gcd q m = 1)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk P)) κsep]
    [IsSepClosure (ResidueField (X.presheaf.stalk P)) κsep]
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk P) H]
    [IsHenselization (X.presheaf.stalk P) κsep H]
    (φ : cyclicInvariants κsep m q ≃+* AdicCompletion (maximalIdeal H) H) :
    ∀ c : weilDivisorClassGroup (Spec (X.presheaf.stalk P)), m • c = 0 := by
  have : IsNormal (Spec (X.presheaf.stalk P)) := isNormal_spec (X.presheaf.stalk P)
  exact MMP.Flips.nsmul_eq_zero_of_nonempty_linearEquiv_reflexivePower fun N _ _ hN =>
    nonempty_linearEquiv_reflexivePower_stalk sX hX P m hm q hq κsep H φ N hN

@[expose] public section

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k))

/-- **The cyclic surface model along a normal plt boundary.** Let `X` be a normal variety over an
algebraically closed field `k` of characteristic zero, of dimension `n`, with canonical divisor
`K_X`, `S` a prime divisor which is a normal variety, and `B` an effective `ℚ`-divisor with all
coefficients `≤ 1` and `coeff_S B = 0`. Let `P ∈ S` be a point with `dim 𝒪_{X,P} = 2`, near
which `K_X + S + B` is `ℚ`-Cartier and `(X, S + B)` is plt. Then there are `m ≥ 1` and `q` with
`gcd(q, m) = 1` such that `mD` is Cartier at `P` for every Weil divisor `D` on `X`, and such that
for every strict henselization `H` of `𝒪_{X,P}`, with residue field `κ^sep`, there is a ring
isomorphism `φ : κ^sep[[u, v]]^{μ_m} ≃+* Ĥ` onto the `𝔪_H`-adic completion of `H`
(`μ_m` acting by `ζ · (u, v) = (ζu, ζ^q v)`, `MMP.Flips.cyclicInvariants`) which is `k`-linear on
constants and carries the ideal of invariants vanishing on `u = 0` onto `I_{S,P} Ĥ`. -/
@[mmp "lem_mmp_normal_plt_codimension_two_cyclic_model"]
public theorem exists_ringEquiv_cyclicInvariants_of_isAt_isPltPair
    (hX : IsNormalVariety k sX) {n : ℕ} {KX : Divisor X} (hK : KX.IsCanonicalDivisor sX n)
    (S : Mori.PrimeDivisor X) (hS : IsNormalVariety k (S.idealSheaf.subschemeι ≫ sX))
    (B : QDivisor X) (hB : 0 ≤ B) (hB_le : ∀ E : Mori.PrimeDivisor X, B.coeff E ≤ 1)
    (hBS : B.coeff S = 0)
    (P : X) (hQ : ∃ U : X.Opens, P ∈ U ∧ (Divisor.toQDivisor (KX.restrictOpen U) +
      DivisorWithCoeffs.restrictOpen U (Finsupp.single S 1 + B)).IsQCartier)
    (hPS : P ∈ S.support) (hP : ringKrullDim (X.presheaf.stalk P) = 2)
    (hplt : IsAt sX (fun sU n K Δ => IsPltPair sU n K Δ) n KX (Finsupp.single S 1 + B) P) :
    letI := stalkAlgebra sX P
    ∃ m : ℕ, 1 ≤ m ∧ ∃ q : ℤ, Int.gcd q m = 1 ∧
      (∀ D : Divisor X, IsCartierAt (m • D) P) ∧
      ∀ (κsep : Type u) [Field κsep] [Algebra (ResidueField (X.presheaf.stalk P)) κsep]
        [IsSepClosure (ResidueField (X.presheaf.stalk P)) κsep]
        (H : Type u) [CommRing H] [IsLocalRing H] [Algebra (X.presheaf.stalk P) H]
        [IsLocalRing.IsHenselization (X.presheaf.stalk P) κsep H],
        ∃ φ : cyclicInvariants κsep m q ≃+* AdicCompletion (maximalIdeal H) H,
          (∀ c : k, ((φ.symm (algebraMap H (AdicCompletion (maximalIdeal H) H)
              (algebraMap (X.presheaf.stalk P) H (algebraMap k (X.presheaf.stalk P) c))) :
                cyclicInvariants κsep m q) : MvPowerSeries (Fin 2) κsep) =
            MvPowerSeries.C (algebraMap (ResidueField (X.presheaf.stalk P)) κsep
              (residue (X.presheaf.stalk P) (algebraMap k (X.presheaf.stalk P) c)))) ∧
          Ideal.map φ ((Ideal.span {MvPowerSeries.X 0}).comap
              (cyclicInvariants κsep m q).subtype) =
            ((AlgebraicGeometry.IdealSheafData.stalk S.idealSheaf P).map
              (algebraMap (X.presheaf.stalk P) H)).map
              (algebraMap H (AdicCompletion (maximalIdeal H) H)) := by
  letI := stalkAlgebra sX P
  obtain ⟨H₀, _, _, _, _⟩ := exists_isHenselization (X.presheaf.stalk P)
    (SeparableClosure (ResidueField (X.presheaf.stalk P)))
  obtain ⟨m, hm, q, hq, hmodel⟩ := exists_isCyclicModel sX hX S hS B hB hB_le hBS P hPS hP
    hplt (SeparableClosure (ResidueField (X.presheaf.stalk P))) H₀
  refine ⟨m, hm, q, hq, isCartierAt_smul_of_nsmul_eq_zero_weilDivisorClassGroup_stalk P m
    (nsmul_eq_zero_weilDivisorClassGroup_stalk sX hX P m hm q hq _ H₀ hmodel.choose),
    fun κsep _ _ _ H _ _ _ _ => hmodel.transport⟩

end

end MMP.Flips
